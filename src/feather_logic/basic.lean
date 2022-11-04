import data.finpfun

/-!
# Feather logic

This file defines feather's core logic. Models of feather's kernel are constructed by instantiating
various typeclasses.
-/

universe u

namespace feather_model

/--
A runtime typing context.

* `Γ` is the intuitionistic typing context, which is a set that contains elements of the form
  `x : α`, which can be copied freely.
* `Θ` is the affine typing context, a multiset that contains similar elements, but which cannot
  be copied.
* `Ξ` is the affine knowledge context, which is a set that contains information about elements
  of the affine typing context, in a copyable way.
-/
structure runtime_context (E : Type (u + 1)) (V : Type u) :=
(Γ : finset (V × E))
(Θ : multiset (V × E))
(Ξ : finset (V × E))

instance {E : Type (u + 1)} {V : Type u} [decidable_eq E] [decidable_eq V] : has_add (runtime_context E V) :=
⟨λ C D, ⟨C.Γ ∪ D.Γ, C.Θ + D.Θ, C.Ξ ∪ D.Ξ⟩⟩

/-- The judgment `Γ | Θ | Ξ ⊢ e : type`. -/
structure runtime_judgment (E : Type (u + 1)) (V : Type u) :=
(ctx : runtime_context E V)
(e : E)
(type : E)

/--
A runtime-irrelevant typing context.

* `Γ` is the intuitionistic typing context, which is a set that contains elements of the form
  `x : α`, which can be copied freely.
* `Ξ` is the affine knowledge context, which is a set that contains information about elements
  of the affine typing context of a runtime context, in a copyable way.
-/
structure rir_context (E : Type (u + 1)) (V : Type u) :=
(Γ : finset (V × E))
(Ξ : finset (V × E))

instance {E : Type (u + 1)} {V : Type u} [decidable_eq E] [decidable_eq V] : has_union (rir_context E V) :=
⟨λ C D, ⟨C.Γ ∪ D.Γ, C.Ξ ∪ D.Ξ⟩⟩

/-- A typing context that contains no information about resource ownership. -/
structure plain_context (E : Type (u + 1)) (V : Type u) :=
(Γ : finset (V × E))

instance {E : Type (u + 1)} {V : Type u} [decidable_eq E] [decidable_eq V] : has_union (plain_context E V) :=
⟨λ C D, ⟨C.Γ ∪ D.Γ⟩⟩

/-- Returns the runtime-irrelevant portion of a runtime context. -/
def runtime_context.rir {E : Type (u + 1)} {V : Type u} (C : runtime_context E V) : rir_context E V := ⟨C.Γ, C.Ξ⟩

/-- Returns the intuitionistic portion of a runtime context. -/
def runtime_context.plain {E : Type (u + 1)} {V : Type u} (C : runtime_context E V) : plain_context E V :=
⟨C.Γ⟩

/-- Returns the intuitionistic portion of a runtime-irrelevant context. -/
def rir_context.plain {E : Type (u + 1)} {V : Type u} (C : rir_context E V) : plain_context E V :=
⟨C.Γ⟩

/-- Collapses a runtime-irrelevant context's knowledge context into the intuitionistic context. -/
def rir_context.collapse {E : Type (u + 1)} {V : Type u} [decidable_eq E] [decidable_eq V] (C : rir_context E V) : rir_context E V :=
⟨C.Γ ∪ C.Ξ, ∅⟩

/-- The runtime-irrelevant judgment `Γ | Ξ ⊢ e : type`. -/
structure rir_judgment (E : Type (u + 1)) (V : Type u) :=
(ctx : rir_context E V)
(e : E)
(type : E)

/-- The name of a sort in feather's type system.

The sorts `type n` are indexed by the natural numbers.
There are additional sorts of propositions and regions. -/
inductive sort_name
| type : ℕ → sort_name
| prop : sort_name
| region : sort_name

/--
Types associated with feather terms `E`.

`V` is a type of *variables*. This type should be (constructively) infinite.

`var` creates the term representing a single variable `v : V`. `bound` is the finite set
of bound variables in a term. `subst` is the substitution operation: `subst v e` is a
function that substitutes each occurence of `v` for `e` in a given term.

`runtime_judgments` is a set of runtime judgments `Γ | Θ | Ξ ⊢ x : α` that hold in this
particular model of feather. Similarly, `rir_judgments` is a set of runtime-irrelevant
judgments `Γ | Ξ ⊢ x : α`. These sets will be constrained later by various closure properties.

`defeq` is an equivalence relation on feather terms, given an ambient runtime-irrelevant
context `Γ | Ξ`, called *definitional equality*. In particular, `defeq C x y α` is the
proposition that `x` and `y` are definitionally equivalent and have type `α`.

`sort` gives the sorts in the type hierarchy. In particular, this gives `prop` and `region`.

`representable` gives a term that encodes the representability of a particular term,
considered as a type of feather terms, given a context of variables to bind.
-/
class term_struct (E : Type (u + 1)) :=
(V : Type u)
(var : V → E)
(bound : E → finset V)
(subst : V → E → E → E)
(runtime_judgments : runtime_judgment E V → Prop)
(rir_judgments : rir_judgment E V → Prop)
(defeq : plain_context E V → E → E → E → Prop)
(sort : sort_name → E)
(representable : finset (V × E) → E → E)

export term_struct (V var bound subst sort representable)

def type {E : Type (u + 1)} [term_struct E] (u : ℕ) : E := sort (sort_name.type u)
def prop {E : Type (u + 1)} [term_struct E] : E := sort sort_name.prop
def region {E : Type (u + 1)} [term_struct E] : E := sort sort_name.region

/-! We define notation for these common types of judgment. -/

notation C ` ⊢ᵣ `:26 x:26 ` : `:26 α:26 := term_struct.runtime_judgments (runtime_judgment.mk C x α)
notation C ` ⊢ `:26 x:26 ` : `:26 α:26 := term_struct.rir_judgments (rir_judgment.mk C x α)
notation C ` ⊢ `:26 x:26 ` ≡ `:26 y:26 ` : `:26 α:26 := term_struct.defeq C x y α

-- A convenient instance to use instead of explicitly calling `bound` all the time.
instance term_has_mem (E : Type (u + 1)) [term_struct E] : has_mem (V E) E :=
⟨λ v e, v ∈ (bound e : finset (V E))⟩

/-- Substitutes the term `e` for the variable `v`. If the context contains an assumption `v : α`,
it is removed. -/
def runtime_context.subst {E : Type (u + 1)} [term_struct E] [decidable_eq E] [decidable_eq (V E)]
  (v : V E) (e : E) (C : runtime_context E (V E)) : runtime_context E (V E) :=
⟨(C.Γ.filter (λ x : V E × E, x.1 = v)).image (prod.map id (subst v e)),
 (C.Θ.filter (λ x : V E × E, x.1 = v)).map (prod.map id (subst v e)),
 (C.Ξ.filter (λ x : V E × E, x.1 = v)).image (prod.map id (subst v e))⟩

/-- Substitutes the term `e` for the variable `v`. If the context contains an assumption `v : α`,
it is removed. -/
def rir_context.subst {E : Type (u + 1)} [term_struct E] [decidable_eq E] [decidable_eq (V E)]
  (v : V E) (e : E) (C : rir_context E (V E)) : rir_context E (V E) :=
⟨(C.Γ.filter (λ x : V E × E, x.1 = v)).image (prod.map id (subst v e)),
 (C.Ξ.filter (λ x : V E × E, x.1 = v)).image (prod.map id (subst v e))⟩

/-- Substitutes the term `e` for the variable `v`. If the context contains an assumption `v : α`,
it is removed. -/
def plain_context.subst {E : Type (u + 1)} [term_struct E] [decidable_eq E] [decidable_eq (V E)]
  (v : V E) (e : E) (C : plain_context E (V E)) : plain_context E (V E) :=
⟨(C.Γ.filter (λ x : V E × E, x.1 = v)).image (prod.map id (subst v e))⟩

/--
A type of feather terms that is lawful. Many of these laws are inspired by the
[HoTT book](https://homotopytypetheory.org/book/).

This structure encapsulates the basic information about feather terms: definitional equality,
substitution, sorts, knowledge rules, variable instantiation, and representability.

* Given any context, definitional equality is an equivalence relation. Note that for the reflexive
  case, we are allowed to use information in `Ξ` to determine the type of a term.
  Note that runtime terms have no definitional equality properties, even reflexivity.
  This equivalence is respected by typing and representability.
* `representable` has the `α`-equivalence property.
* If we can derive `x : α`, and *separately* we can derive `y : β` given `v : α`, then we can
  derive the substituted version `y[x/v] : β[x/v]`. The property holds for runtime-relevant and
  runtime-irrelevant judgments, as well as definitional equality.
* The *weakening property* holds: we can insert arbitrary extra hypotheses in any judgment.
* We can eliminate assumptions from `Ξ` if the corresponding entry in `Θ` exists.
* We can instantiate variables in `Γ` in a runtime-irrelevant context.
* We can instantiate variables in `Θ` in a runtime context.
* The sorts `type u` have type `type (u + 1)`, and `prop`, `region` have type `type 0`.
* Runtime-irrelevant judgments that are representable can be made runtime-relevant.
* The bound variables for created terms behave in the obvious ways under substitution.
-/
class term (E : Type (u + 1)) [decidable_eq E] [term_struct E] [decidable_eq (V E)] :=
(defeq_reflexive {C : rir_context E (V E)} {x α : E} : C ⊢ x : α → C.plain ⊢ x ≡ x : α)
(defeq_symmetric {C : plain_context E (V E)} {x y α : E} : C ⊢ x ≡ y : α → C ⊢ y ≡ x : α)
(defeq_transitive {C : plain_context E (V E)} {x y z α : E} :
  C ⊢ x ≡ y : α → C ⊢ y ≡ z : α → C ⊢ x ≡ z : α)
(runtime_congr {C : runtime_context E (V E)} {x α β γ : E} :
  C ⊢ᵣ x : α → C.plain ⊢ α ≡ β : γ → C ⊢ᵣ x : β)
(rir_congr {C : rir_context E (V E)} {x α β γ : E} :
  C ⊢ x : α → C.plain ⊢ α ≡ β : γ → C ⊢ x : β)
(defeq_congr {C : plain_context E (V E)} {x y α β γ : E} :
  C ⊢ x ≡ y : α → C ⊢ α ≡ β : γ → C ⊢ x ≡ y : β)
(representable_congr {C : plain_context E (V E)} {α β γ : E} {K : finset (V E × E)} :
  C ⊢ α ≡ β : γ → C ⊢ representable K α ≡ representable K β : prop)
(representable_congr_type {C : plain_context E (V E)} {v : V E} {α β γ δ : E} {K : finset (V E × E)} :
  C ⊢ α ≡ β : γ → C ⊢ representable (K ∪ {(v, α)}) δ ≡ representable (K ∪ {(v, β)}) δ : prop)
(representable_alpha {C : plain_context E(V E)} {v w : V E} {α β : E} {K : finset (V E × E)} :
  C ⊢ representable (K ∪ {(v, α)}) β ≡ representable (K ∪ {(w, α)}) (subst v (var w) β) : prop)
(subst_runtime {C D : runtime_context E (V E)} {v : V E} {x y α β : E} :
  C ⊢ᵣ x : α → ⟨C.Γ, ∅, C.Ξ⟩ + D + ⟨∅, {(v, α)}, ∅⟩ ⊢ᵣ y : β →
  C + D.subst v x ⊢ᵣ subst v x y : subst v x β)
(subst_rir {C D : rir_context E (V E)} {v : V E} {x y α β : E} :
  C ⊢ x : α → C ∪ D ∪ ⟨{(v, α)}, ∅⟩ ⊢ y : β →
  C ∪ D.subst v x ⊢ subst v x y : subst v x β)
(subst_defeq {C : rir_context E (V E)} {D : plain_context E (V E)} {v : V E} {x y z α β : E} :
  C ⊢ x : α → C.plain ∪ D ∪ ⟨{(v, α)}⟩ ⊢ y ≡ z : β →
  C.plain ∪ D.subst v x ⊢ subst v x y ≡ subst v x z : subst v x β)
(subst_congr {C D : rir_context E (V E)} {v : V E} {x y z α β : E} :
  C.plain ⊢ x ≡ y : α → C ∪ D ∪ ⟨{(v, α)}, ∅⟩ ⊢ z : β →
  C.plain ∪ D.plain.subst v x ⊢ subst v x z ≡ subst v y z : subst v x β)
(runtime_judgments_weak {C D : runtime_context E (V E)} {x α : E} : C ⊢ᵣ x : α → C + D ⊢ᵣ x : α)
(rir_judgments_weak {C D : rir_context E (V E)} {x α : E} : C ⊢ x : α → C ∪ D ⊢ x : α)
(defeq_weak {C D : plain_context E (V E)} {x y α : E} : C ⊢ x ≡ y : α → C ∪ D ⊢ x ≡ y : α)
(Ξ_elim {C : runtime_context E (V E)} {Θ' : multiset (V E × E)} {x α : E} :
  C + ⟨∅, Θ', Θ'.to_finset⟩ ⊢ᵣ x : α → C + ⟨∅, Θ', ∅⟩ ⊢ᵣ x : α)
(Γ_var {C : rir_context E (V E)} {v : V E} {α : E} : (v, α) ∈ C.Γ → C ⊢ var v : α)
(Θ_var {C : runtime_context E (V E)} {v : V E} {α : E} : (v, α) ∈ C.Θ → C ⊢ᵣ var v : α)
(type_type {C : rir_context E (V E)} {u : ℕ} : C ⊢ type u : type (u + 1))
(prop_type {C : rir_context E (V E)} : C ⊢ prop : type 0)
(region_type {C : rir_context E (V E)} : C ⊢ region : type 0)
(to_runtime {C : rir_context E (V E)} {x α h : E} :
  C ⊢ x : α → C ⊢ h : representable ⊥ α → ⟨C.Γ, ∅, C.Ξ⟩ ⊢ᵣ x : α)
(bound_var (v : V E) : (bound (var v : E) : finset (V E)) = {v})
(bound_sort {s : sort_name} : (bound (sort s) : finset (V E)) = ∅)
(bound_representable {α : E} {K : finset (V E × E)} :
  bound (representable K α) = bound α \ K.image prod.fst)
(subst_unbound {e f : E} {v : V E} : v ∉ e → subst v f e = e)
(subst_bound {e f : E} {v : V E} : v ∈ e → bound (subst v f e) = (bound e).erase v ∪ bound f)

end feather_model
