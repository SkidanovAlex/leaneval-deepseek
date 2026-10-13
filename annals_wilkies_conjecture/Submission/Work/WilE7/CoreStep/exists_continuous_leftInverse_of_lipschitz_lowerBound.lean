import Mathlib

namespace Work.WilE7.CoreStep

theorem exists_continuous_leftInverse_of_lipschitz_lowerBound
    {E : Type*} [NormedAddCommGroup E]
    {F : Type*} [NormedAddCommGroup F]
    (f : E → F) (W : Set E) (C : NNReal)
    (h : ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ C * ‖f x - f y‖) :
    ∃ r : F → E, ContinuousOn r (f '' W) ∧ ∀ v ∈ W, r (f v) = v := by
  classical
  -- The lower bound forces `f` to be injective on `W`.
  have hinj : Set.InjOn f W := by
    intro x hx y hy hxy
    have h1 := h x hx y hy
    rw [hxy, sub_self, norm_zero, mul_zero] at h1
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _)))
  -- The left inverse, defined on the image by choice and set to `0` elsewhere.
  let g : F → E := fun y =>
    if hy : y ∈ f '' W then Classical.choose ((Set.mem_image f W y).mp hy) else 0
  have hg_spec : ∀ y (hy : y ∈ f '' W), g y ∈ W ∧ f (g y) = y := by
    intro y hy
    have key : g y = Classical.choose ((Set.mem_image f W y).mp hy) := by
      simp only [g]
      exact dite_eq_left hy
    rw [key]
    exact Classical.choose_spec ((Set.mem_image f W y).mp hy)
  refine ⟨g, ?_, ?_⟩
  · -- On the image, `g` is `C`-Lipschitz, hence continuous.
    have hlip : LipschitzOnWith C g (f '' W) := by
      intro y hy z hz
      obtain ⟨hyW, hyf⟩ := hg_spec y hy
      obtain ⟨hzW, hzf⟩ := hg_spec z hz
      have key := h (g y) hyW (g z) hzW
      rw [hyf, hzf] at key
      simp only [edist_dist, dist_eq_norm]
      have key' : ENNReal.ofReal ‖g y - g z‖ ≤ ENNReal.ofReal ((C : ℝ) * ‖y - z‖) :=
        ENNReal.ofReal_le_ofReal key
      rwa [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal] at key'
    exact hlip.continuousOn
  · -- And it is a left inverse on `W`.
    intro v hv
    obtain ⟨h1, h2⟩ := hg_spec (f v) (Set.mem_image_of_mem f hv)
    exact hinj h1 hv h2

end Work.WilE7.CoreStep
