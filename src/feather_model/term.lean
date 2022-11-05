import feather_model.basic

universe u

open_locale classical

/-!
In this file, we prove that the model, as defined in `feather_model.basic`,
produces a lawful type of terms, assuming the same is true for the lower level.
-/

namespace feather_model

variables {T : Type u} [term_struct T] [type_data T] [term T]

lemma empty_runtime_ok : runtime_ok (⟨∅, ∅, ∅⟩ : runtime_context (mterm T)) :=
runtime_ok.empty

lemma empty_rir_ok : rir_ok (⟨∅, ∅⟩ : rir_context (mterm T)) :=
rir_ok.empty

lemma runtime_ok_Γ (C : runtime_context (mterm T)) {v : V} {α : mterm T} :
  runtime_ok C → is_type C.rir α → runtime_ok (C + ⟨{(v, α)}, ∅, ∅⟩) :=
runtime_ok.Γ C v α

lemma runtime_ok_Θ (C : runtime_context (mterm T)) {v : V} {α : mterm T} :
  runtime_ok C → is_type C.rir α → runtime_ok (C + ⟨∅, {(v, α)}, ∅⟩) :=
runtime_ok.Θ C v α

lemma runtime_ok_Ξ (C : runtime_context (mterm T)) {v : V} {α : mterm T} :
  runtime_ok C → is_type C.rir α → runtime_ok (C + ⟨∅, ∅, {(v, α)}⟩) :=
runtime_ok.Ξ C v α

lemma rir_ok_Γ (C : rir_context (mterm T)) {v : V} {α : mterm T} :
  rir_ok C → is_type C α → rir_ok (C ∪ ⟨{(v, α)}, ∅⟩) :=
rir_ok.Γ C v α

lemma rir_ok_Ξ (C : rir_context (mterm T)) {v : V} {α : mterm T} :
  rir_ok C → is_type C α → rir_ok (C ∪ ⟨∅, {(v, α)}⟩) :=
rir_ok.Ξ C v α

lemma defeq_reflexive (C : rir_context (mterm T)) {x α : mterm T} :
  C ⊢ x : α → C ⊢ x ≡ x : α :=
begin
  intros h I hI,
  exact ⟨rfl, h.interpret I hI⟩,
end

lemma defeq_symmetric (C : rir_context (mterm T)) {x y α : mterm T} :
  C ⊢ x ≡ y : α → C ⊢ y ≡ x : α :=
begin
  intros h I hI,
  obtain ⟨h₁, h₂⟩ := h I hI,
  rw h₁ at h₂ ⊢,
  exact ⟨rfl, h₂⟩,
end

lemma defeq_transitive (C : rir_context (mterm T)) {x y z α : mterm T} :
  C ⊢ x ≡ y : α → C ⊢ y ≡ z : α → C ⊢ x ≡ z : α :=
begin
  intros hxy hyz I hI,
  obtain ⟨h₁, h₂⟩ := hxy I hI,
  obtain ⟨h₃, h₄⟩ := hyz I hI,
  rw [h₁, h₃] at h₂ ⊢,
  exact ⟨rfl, h₂⟩,
end

/-
instance : term (mterm T) := {
  empty_runtime_ok := empty_runtime_ok,
  empty_rir_ok := empty_rir_ok,
  runtime_ok_Γ := runtime_ok_Γ,
  runtime_ok_Θ := runtime_ok_Θ,
  runtime_ok_Ξ := runtime_ok_Ξ,
  rir_ok_Γ := rir_ok_Γ,
  rir_ok_Ξ := rir_ok_Ξ,
  defeq_reflexive := defeq_reflexive,
  defeq_symmetric := defeq_symmetric,
  defeq_transitive := defeq_transitive,
}
-/

end feather_model
