import Mathlib

namespace Work.WilE7.DimAPI

/-- Let `E, X` be finite dimensional real normed spaces, `W ⊆ X` a submodule, `C : X →L[ℝ] W` a
continuous linear retraction onto `W` (`C` fixes `W` pointwise), and `T : E →L[ℝ] X` an injective
continuous linear map whose image lies in `W`.  If `finrank ℝ E = finrank ℝ W`, then
`C ∘ T : E → W` is bijective.

Indeed `C ∘ T` is the corestriction of `T` to `W` (`C` fixes `W`), which is injective, and an
injective linear map between finite dimensional spaces of equal dimension is bijective. -/
theorem bij_comp_projection {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (W : Submodule ℝ X) (C : X →L[ℝ] W) (hC : ∀ x : W, C ↑x = x)
    (T : E →L[ℝ] X) (hT : ∀ v, T v ∈ W) (hTinj : Function.Injective T)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ W) :
    Function.Bijective (C.comp T) := by
  -- `W` is finite dimensional, being a submodule of the finite dimensional space `X`.
  have : FiniteDimensional ℝ W := Submodule.finiteDimensional_of_le le_top
  -- The corestriction of `T` to `W`.
  let Tl : E →ₗ[ℝ] W :=
    { toFun := fun v => ⟨T v, hT v⟩
      map_add' := by intro a b; ext; simp
      map_smul' := by intro c a; ext; simp }
  -- `C ∘ T` is exactly this corestriction, because `C` fixes `W` pointwise.
  have hfun : (C.comp T : E → W) = Tl := by
    ext v
    exact congrArg Subtype.val (hC ⟨T v, hT v⟩)
  -- The corestriction is injective since `T` is.
  have hinj : Function.Injective Tl := by
    intro a b h
    exact hTinj (congrArg Subtype.val h)
  -- Injective linear self-map of finite dimensional spaces of equal dimension is surjective.
  have hsurj : Function.Surjective Tl :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  rw [hfun]
  exact ⟨hinj, hsurj⟩

end Work.WilE7.DimAPI
