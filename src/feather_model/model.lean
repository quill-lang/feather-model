import feather_model.basic

open_locale classical

open feather_model

@[reducible] def 𝕋 := mterm (finset V)

/-- To establish a base case for the model, we create the "empty" model level. -/
instance : term_struct (finset V) := {
  var := λ v, {v},
  bound := id,
  subst := λ v e f, if v ∈ f then f.erase v ∪ e else f,
  is_type := λ _ _, true,
  runtime_ok := λ _, true,
  rir_ok := λ _, true,
  runtime_judgments := λ _, true,
  rir_judgments := λ _, true,
  defeq := λ _ _ _ _, true,
  sort := λ _, ∅,
  representable := λ s f, f,
}

instance : type_data (finset V) := ⟨λ _ _, true, λ _, true⟩

instance : term (finset V) :=
begin
  refine_struct { .. };
  intros; try { trivial },
  { unfold subst,
    rw if_neg,
    assumption, },
  { unfold subst,
    rw if_pos,
    refl,
    assumption, },
end

example : term_struct 𝕋 := infer_instance
