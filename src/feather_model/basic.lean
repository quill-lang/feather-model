import feather_logic.basic
import order.extension.well

universe u

/-!
In this file, we construct the type of feather terms in our model,
given the previous level of the model.
-/

namespace feather_model

open_locale classical

/--
A term in our model, parametrised by the type of terms in the previous level of the model.

* `var v` is the term representing the variable `v`.
* `prev e` is a term `e` from the previous level of the model.
* `univ` represents all of `Type u`.
* `ty α` is the Lean type `α`.
* `obj α x` is a Lean object of type `α` and value `x : α`.
* `apply f x` is the term representing function application of `f` on `x`.

If we are in level `u` of the model, `ty` represents feather objects of type `Type u`, and `obj`
represents feather objects of type which lies in `Type u`. Notably, `var` is a variable of feather
objects of type `Type u` or of type which lies in `Type u`. If smaller universes are needed, wrap
them in `prev`.

Some "error states" representing invalid situations are encoded as `ty pempty`.
-/
inductive mterm (T : Type u) : Type (u + 1)
| var : V → mterm
| prev : T → mterm
| univ : mterm
| ty : Type u → mterm
| obj : Π (α : Type u), α → mterm
| apply : mterm → mterm → mterm

/-- Provides the `has_type` function, which determines if a given term has a given type.
This is just used for bookkeeping between levels of the model. -/
class type_data (α : Type*) :=
(has_type : α → α → Prop)
(is_type : α → Prop)

variables {T : Type u} [term_struct T]

namespace mterm

def bound : Π (e : mterm T), finset V
| (var v) := {v}
| (prev e) := term_struct.bound e
| univ := ∅
| (ty α) := ∅
| (obj α x) := ∅
| (apply f x) := bound f ∪ bound x

-- A convenient instance to use instead of explicitly calling `bound` all the time.
instance mterm_has_mem : has_mem V (mterm T) := ⟨λ v e, v ∈ bound e⟩

def subst (v : V) : Π (e : mterm T) (f : mterm T), mterm T
| e (var w) := if v = w then e else var w
| (prev e) (prev f) := prev (term_struct.subst v e f)
| _ (prev f) := ty pempty
| e univ := univ
| e (ty α) := ty α
| e (obj α x) := obj α x
| e (apply f x) := apply (subst e f) (subst e x)

def has_type [type_data T] : Π (e f : mterm T), Prop
| (prev x) (prev α) := type_data.has_type x α
| (ty α) univ := true
| (obj α x) (ty β) := α = β
| _ _ := false

def is_type [type_data T] : Π (e : mterm T), Prop
| (prev α) := type_data.is_type α
| (ty α) := true
| _ := false

instance mterm.type_data [type_data T] : type_data (mterm T) := ⟨has_type, is_type⟩

end mterm

open mterm

section interpretation

/-! Given a context, which here means a  `finset (V × mterm T)`, we produce the set of all
*interpretations* of that context: substitutions of Lean objects for these variables
that satisfy the given context. -/

/--
We establish a relation on judgments `V × mterm T`.
If `v` occurs bound in a term `f`, then `(v, e)` must precede `(w, f)`.

On a plain context `finset (V × mterm T)`, if the transitive closure of this relation forms a
strict partial order, we can sort the judgments and provide a set of interpretations for it by
iteratively substituting along this order.
-/
def immediately_precedes (a b : V × mterm T) : Prop := a.1 ∈ b.2

/-- A list of substitutions to perform to yield a interpretation of a collection of variables. -/
@[reducible] def interpretation (T : Type u) := list (V × mterm T)

/-- Given an interpretation, evaluate this term. -/
def interpretation.interpret (I : interpretation T) (e : mterm T) : mterm T :=
list.foldl (λ (f : mterm T) (i : V × mterm T), subst i.1 i.2 f) e I

/-- A collection of assumptions `V × mterm T` is *sortable* if they can be ordered in such a way
where each variable occurs only in substitutions later in the order. -/
def interpretation.sortable (C : finset (V × mterm T)) : Prop :=
well_founded (λ a b : C, immediately_precedes a.val b.val)

/-- Assuming a context is sortable, produce a linear order for it. -/
noncomputable def interpretation.sort_order (C : finset (V × mterm T))
  (h : interpretation.sortable C) : linear_order C :=
well_founded.well_order_extension h

/-- Assuming that a context is sortable, sort it. The precise sort chosen is arbitrary. -/
noncomputable def interpretation.sort (C : finset (V × mterm T)) (h : interpretation.sortable C) :
  list (V × mterm T) :=
(finset.sort (interpretation.sort_order C h).le C.attach).map subtype.val

/-- Substitutes the term `e` for the variable `v`. If the context contains an assumption `v : α`,
it is removed. -/
def interpretation.subst (v : V) (e : mterm T) (I : list (V × mterm T)) : list (V × mterm T) :=
(I.filter (λ x : V × mterm T, x.1 = v)).map (prod.map id (subst v e))

lemma interpretation.subst_length (v : V) (e : mterm T) (I : interpretation T) :
  (interpretation.subst v e I).length ≤ I.length :=
begin
  unfold interpretation.subst,
  rw list.length_map,
  exact list.length_filter_le _ _,
end

/-- The set of interpretations of a typing judgment `e : type`. -/
def interpretations (v : V) : Π (type : mterm T), set (interpretation T)
| (ty α) := ⋃ (x : α), {[⟨v, mterm.obj α x⟩]}
| _ := ∅

def interpretations' : Π (C : list (V × mterm T)), set (interpretation T)
| [] := {[]}
| (x :: xs) := ⋃ (I ∈ interpretations x.1 x.2),
    have (interpretation.subst x.1 x.2 xs).length < (x :: xs).length,
    from lt_of_le_of_lt (interpretation.subst_length x.1 x.2 xs) (lt_add_one _),
    (λ J, I ++ J) '' interpretations' (interpretation.subst x.1 x.2 xs)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩] }

def rir_context.interpretations (C : rir_context (mterm T)) : set (interpretation T) :=
if h : interpretation.sortable (C.Γ ∪ C.Ξ)
then interpretations' (interpretation.sort _ h) else ∅

def runtime_context.interpretations (C : runtime_context (mterm T)) : set (interpretation T) :=
if h : interpretation.sortable (C.Γ ∪ C.Θ.to_finset ∪ C.Ξ)
then interpretations' (interpretation.sort _ h) else ∅

end interpretation

def is_type [type_data T] (C : rir_context (mterm T)) (α : mterm T) : Prop :=
∀ (I : interpretation T), I ∈ C.interpretations → mterm.is_type (I.interpret α)

inductive runtime_ok [type_data T] : runtime_context (mterm T) → Prop
| empty : runtime_ok ⟨∅, ∅, ∅⟩
| Γ (C : runtime_context (mterm T)) (v : V) (α : mterm T) :
  runtime_ok C → is_type C.rir α → runtime_ok (C + ⟨{(v, α)}, ∅, ∅⟩)
| Θ (C : runtime_context (mterm T)) (v : V) (α : mterm T) :
  runtime_ok C → is_type C.rir α → runtime_ok (C + ⟨∅, {(v, α)}, ∅⟩)
| Ξ (C : runtime_context (mterm T)) (v : V) (α : mterm T) :
  runtime_ok C → is_type C.rir α → runtime_ok (C + ⟨∅, ∅, {(v, α)}⟩)

inductive rir_ok [type_data T] : rir_context (mterm T) → Prop
| empty : rir_ok ⟨∅, ∅⟩
| Γ (C : rir_context (mterm T)) (v : V) (α : mterm T) :
  rir_ok C → is_type C α → rir_ok (C ∪ ⟨{(v, α)}, ∅⟩)
| Ξ (C : rir_context (mterm T)) (v : V) (α : mterm T) :
  rir_ok C → is_type C α → rir_ok (C ∪ ⟨∅, {(v, α)}⟩)

-- TODO: Add the assertion that we use the relevant resources in `Θ` only once, and that relevant
-- things are representable.
structure runtime_judgments [type_data T] (J : runtime_judgment (mterm T)) : Prop :=
(ok : runtime_ok J.ctx)
(interpret : ∀ (I : interpretation T), I ∈ J.ctx.interpretations →
  (I.interpret J.e).has_type (I.interpret J.type))

structure rir_judgments [type_data T] (J : rir_judgment (mterm T)) : Prop :=
(ok : rir_ok J.ctx)
(interpret : ∀ (I : interpretation T), I ∈ J.ctx.interpretations →
  (I.interpret J.e).has_type (I.interpret J.type))

def defeq [type_data T] (C : rir_context (mterm T)) (x y α : mterm T) : Prop :=
∀ (I : interpretation T), I ∈ C.interpretations →
  I.interpret x = I.interpret y ∧ (I.interpret x).has_type (I.interpret α)

def sort : sort_name → mterm T
| (sort_name.type n) := ty pempty
| sort_name.prop := ty (ulift Prop)
| sort_name.region := ty punit

def representable (C : finset (V × mterm T)) (e : mterm T) : mterm T :=
mterm.obj (ulift Prop) ⟨false⟩

instance [type_data T] : term_struct (mterm T) := {
  var := var,
  bound := bound,
  subst := subst,
  is_type := is_type,
  runtime_ok := runtime_ok,
  rir_ok := rir_ok,
  runtime_judgments := runtime_judgments,
  rir_judgments := rir_judgments,
  defeq := defeq,
  sort := sort,
  representable := representable,
}

end feather_model
