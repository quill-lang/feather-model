import feather_logic.basic
import order.extension.well

universe u

namespace feather_model

open_locale classical

/-- The type of variables in our model. -/
def V : Type u := ulift ℕ

/--
A term in our model.

* `var v` is the term representing the variable `v`.
* `ty α` is the Lean type `α`.
* `obj α x` is a Lean object of type `α` and value `x : α`.
* `apply f x` is the term representing function application of `f` on `x`.
-/
inductive mterm : Type (u + 1)
| var : V.{u} → mterm
| ty : Type u → mterm
| obj : Π (α : Type u), α → mterm
| apply : mterm → mterm → mterm

namespace mterm

def bound : Π (e : mterm), finset V
| (var v) := {v}
| (ty α) := ∅
| (obj α x) := ∅
| (apply f x) := bound f ∪ bound x

-- A convenient instance to use instead of explicitly calling `bound` all the time.
instance mterm_has_mem : has_mem V mterm := ⟨λ v e, v ∈ bound e⟩

def subst (v : V) (e : mterm) : Π (f : mterm), mterm
| (var w) := if v = w then e else var w
| (ty α) := ty α
| (obj α x) := obj α x
| (apply f x) := apply (subst f) (subst x)

def has_type : Π (e f : mterm), Prop
| (obj α x) (ty β) := α = β
| _ _ := false

end mterm

open mterm

section interpretation

/-! Given a context, which here means a  `finset (V × mterm)`, we produce the set of all
*interpretations* of that context: substitutions of Lean objects for these variables
that satisfy the given context. -/

/--
We establish a relation on judgments `V × mterm`.
If `v` occurs bound in a term `f`, then `(v, e)` must precede `(w, f)`.

On a plain context `finset (V × mterm)`, if the transitive closure of this relation forms a
strict partial order, we can sort the judgments and provide a set of interpretations for it by
iteratively substituting along this order.
-/
def immediately_precedes (a b : V × mterm) : Prop := a.1 ∈ b.2

/-- A list of substitutions to perform to yield a interpretation of a collection of variables. -/
@[reducible] def interpretation := list (V × mterm)

/-- Given an interpretation, evaluate this term. -/
def interpretation.interpret (I : interpretation) (e : mterm) : mterm :=
list.foldl (λ (f : mterm) (i : V × mterm), subst i.1 i.2 f) e I

/-- A collection of assumptions `V × mterm` is *sortable* if they can be ordered in such a way
where each variable occurs only in substitutions later in the order. -/
def interpretation.sortable (C : finset (V × mterm)) : Prop :=
well_founded (λ a b : C, immediately_precedes a.val b.val)

/-- Assuming a context is sortable, produce a linear order for it. -/
noncomputable def interpretation.sort_order (C : finset (V × mterm))
  (h : interpretation.sortable C) : linear_order C :=
well_founded.well_order_extension h

/-- Assuming that a context is sortable, sort it. The precise sort chosen is arbitrary. -/
noncomputable def interpretation.sort (C : finset (V × mterm)) (h : interpretation.sortable C) :
  list (V × mterm) :=
(finset.sort (interpretation.sort_order C h).le C.attach).map subtype.val

/-- Substitutes the term `e` for the variable `v`. If the context contains an assumption `v : α`,
it is removed. -/
def interpretation.subst (v : V) (e : mterm) (I : list (V × mterm)) : list (V × mterm) :=
(I.filter (λ x : V × mterm, x.1 = v)).map (prod.map id (subst v e))

lemma interpretation.subst_length (v : V) (e : mterm) (I : interpretation) :
  (interpretation.subst v e I).length ≤ I.length :=
begin
  unfold interpretation.subst,
  rw list.length_map,
  exact list.length_filter_le _ _,
end

/-- The set of interpretations of a typing judgment `e : type`. -/
def interpretations (v : V) : Π (type : mterm), set interpretation
| (ty α) := ⋃ (x : α), {[⟨v, mterm.obj α x⟩]}
| _ := ∅

def interpretations' : Π (C : list (V × mterm)), set interpretation
| [] := {[]}
| (x :: xs) := ⋃ (I ∈ interpretations x.1 x.2),
    have (interpretation.subst x.1 x.2 xs).length < (x :: xs).length,
    from lt_of_le_of_lt (interpretation.subst_length x.1 x.2 xs) (lt_add_one _),
    (λ J, I ++ J) '' interpretations' (interpretation.subst x.1 x.2 xs)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩] }

def plain_context.interpretations (C : plain_context mterm V) : set interpretation :=
if h : interpretation.sortable C.Γ then interpretations' (interpretation.sort _ h) else ∅

def rir_context.interpretations (C : rir_context mterm V) : set interpretation :=
if h : interpretation.sortable (C.Γ ∪ C.Ξ)
then interpretations' (interpretation.sort _ h) else ∅

def runtime_context.interpretations (C : runtime_context mterm V) : set interpretation :=
if h : interpretation.sortable (C.Γ ∪ C.Θ.to_finset ∪ C.Ξ)
then interpretations' (interpretation.sort _ h) else ∅

end interpretation

def runtime_judgments (J : runtime_judgment mterm V) : Prop :=
∀ (I : interpretation), I ∈ J.ctx.interpretations → (I.interpret J.e).has_type (I.interpret J.type)

def rir_judgments (J : rir_judgment mterm V) : Prop :=
∀ (I : interpretation), I ∈ J.ctx.interpretations → (I.interpret J.e).has_type (I.interpret J.type)

def defeq (C : plain_context mterm V) (x y α : mterm) : Prop :=
∀ (I : interpretation), I ∈ C.interpretations →
  I.interpret x = I.interpret y ∧ (I.interpret x).has_type (I.interpret α)

def sort : sort_name → mterm.{u}
| (sort_name.type n) := ty pempty
| sort_name.prop := ty (ulift Prop)
| sort_name.region := ty punit

def representable (C : finset (V × mterm)) (e : mterm) : mterm.{u} :=
mterm.obj (ulift Prop) ⟨false⟩

instance : term_struct mterm := {
  V := V,
  var := var,
  bound := bound,
  subst := subst,
  runtime_judgments := runtime_judgments,
  rir_judgments := rir_judgments,
  defeq := defeq,
  sort := sort,
  representable := representable,
}

end feather_model
