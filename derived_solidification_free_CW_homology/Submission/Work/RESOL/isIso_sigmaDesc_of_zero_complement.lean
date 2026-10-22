import Mathlib

namespace Work.RESOL

open CategoryTheory CategoryTheory.Limits

/-- Naturality of the coproduct inclusions in the index: for an equality `a = b` of indices the
transport `eqToHom (congrArg F e) : F a ⟶ F b` followed by the inclusion of the summand `F b`
is the inclusion of the summand `F a`. -/
lemma sigma_ι_eqToHom_comp {C : Type*} [Category C] {β : Type*} (F : β → C)
    [HasCoproduct F] {a b : β} (e : a = b) :
    eqToHom (congrArg F e) ≫ Sigma.ι F b = Sigma.ι F a := by
  cases e
  simp

/-- If `f : ι → κ` is an injective map of index types and all the summands `Y j` for `j` outside
the image of `f` are zero objects, then the canonical "coproduct inclusion"
`∐ i, Y (f i) ⟶ ∐ j, Y j` is an isomorphism. -/
theorem isIso_sigmaDesc_of_zero_complement {C : Type*} [CategoryTheory.Category C]
    {ι κ : Type*} {Y : κ → C} [CategoryTheory.Limits.HasCoproduct Y] (f : ι → κ)
    (hf : Function.Injective f) [CategoryTheory.Limits.HasCoproduct (fun i => Y (f i))]
    (hY : ∀ j, (∀ i, f i ≠ j) → CategoryTheory.Limits.IsZero (Y j)) :
    CategoryTheory.IsIso (CategoryTheory.Limits.Sigma.desc
      (fun i => CategoryTheory.Limits.Sigma.ι Y (f i)) :
      (∐ fun i => Y (f i)) ⟶ ∐ Y) := by
  classical
  -- The candidate inverse: send the summand `Y j` to the summand `Y (f i)` where `f i = j` when
  -- `j` lies in the image of `f`, and to the zero object `Y j` otherwise.
  let g : (j : κ) → (Y j ⟶ ∐ fun i => Y (f i)) := fun j =>
    if h : ∃ i, f i = j then
      eqToHom (congrArg Y (Classical.choose_spec h).symm) ≫
        Sigma.ι (fun i => Y (f i)) (Classical.choose h)
    else
      (hY j (fun i hi => h ⟨i, hi⟩)).to_ (∐ fun i => Y (f i))
  -- On the image the map `g` is the corresponding coproduct inclusion.
  have hgi : ∀ i, g (f i) = Sigma.ι (fun i => Y (f i)) i := by
    intro i
    have h : ∃ i', f i' = f i := ⟨i, rfl⟩
    have hstep : g (f i) = eqToHom (congrArg Y (Classical.choose_spec h).symm) ≫
        Sigma.ι (fun i => Y (f i)) (Classical.choose h) := by
      dsimp only [g]
      exact dite_eq_left h
    rw [hstep]
    -- The chosen preimage of `f i` is `i` by injectivity.
    have e : i = Classical.choose h := (hf (Classical.choose_spec h)).symm
    have hcongr : congrArg Y (Classical.choose_spec h).symm
        = congrArg (fun i => Y (f i)) e := Subsingleton.elim _ _
    rw [hcongr]
    exact sigma_ι_eqToHom_comp (fun i => Y (f i)) e
  refine IsIso.mk ⟨Sigma.desc g, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.comp_id, Sigma.ι_comp_desc]
    exact hgi i
  · apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.comp_id]
    by_cases hj : ∃ i, f i = j
    · -- `j` in the image of `f`: both sides are the inclusion of the summand `Y j`.
      have hstep : g j = eqToHom (congrArg Y (Classical.choose_spec hj).symm) ≫
          Sigma.ι (fun i => Y (f i)) (Classical.choose hj) := by
        dsimp only [g]
        exact dite_eq_left hj
      rw [hstep, Category.assoc, Sigma.ι_comp_desc]
      exact sigma_ι_eqToHom_comp Y (Classical.choose_spec hj).symm
    · -- `j` outside the image of `f`: both sides are morphisms out of the zero object `Y j`.
      have hstep : g j = (hY j (fun i hi => hj ⟨i, hi⟩)).to_ (∐ fun i => Y (f i)) := by
        dsimp only [g]
        exact dite_eq_right hj
      rw [hstep]
      exact (hY j (fun i hi => hj ⟨i, hi⟩)).eq_of_src _ _

end Work.RESOL
