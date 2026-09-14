import Mathlib.Topology.MetricSpace.Lipschitz

namespace Commons.Analysis.Convolution

/-- The "reverse Minkowski" style potential function
`f x = sSup_{y ∈ S} (c y - |x - y| / s)` is `1/s`-Lipschitz, provided `S` is nonempty and
`c` is bounded above on `S`. -/
theorem lipschitzWith_sSup_sub_abs_div (c : ℝ → ℝ) (S : Set ℝ) (s : ℝ) (hs : 0 < s)
    (hne : S.Nonempty) (hbd : BddAbove (c '' S)) :
    LipschitzWith ⟨s⁻¹, inv_nonneg.mpr hs.le⟩
      (fun x : ℝ => sSup ((fun y : ℝ => c y - |x - y| / s) '' S)) := by
  -- For every `x`, the set over which we take the supremum is bounded above.
  have hbdd : ∀ x : ℝ, BddAbove ((fun y : ℝ => c y - |x - y| / s) '' S) := by
    intro x
    obtain ⟨B, hB⟩ := hbd
    refine ⟨B, ?_⟩
    rintro _ ⟨y, hyS, rfl⟩
    have h1 : c y - |x - y| / s ≤ c y := by
      have : 0 ≤ |x - y| / s := div_nonneg (abs_nonneg _) hs.le
      linarith
    exact le_trans h1 (hB ⟨y, hyS, rfl⟩)
  apply LipschitzWith.of_le_add_mul (⟨s⁻¹, inv_nonneg.mpr hs.le⟩ : NNReal)
  intro x z
  -- Key one-sided estimate: `f x ≤ f z + s⁻¹ * |x - z|`.
  have key : sSup ((fun y : ℝ => c y - |x - y| / s) '' S) ≤
      sSup ((fun y : ℝ => c y - |z - y| / s) '' S) + s⁻¹ * |x - z| := by
    apply csSup_le (hne.image _)
    rintro _ ⟨y, hyS, rfl⟩
    have hy : c y - |z - y| / s ∈ ((fun y : ℝ => c y - |z - y| / s) '' S) := ⟨y, hyS, rfl⟩
    have h2 : c y - |z - y| / s ≤ sSup ((fun y : ℝ => c y - |z - y| / s) '' S) :=
      le_csSup (hbdd z) hy
    have htri : |z - y| ≤ |x - z| + |x - y| := by
      have h := abs_sub_le z x y
      rwa [abs_sub_comm z x] at h
    have h3 : c y - |x - y| / s ≤ c y - |z - y| / s + s⁻¹ * |x - z| := by
      have hs1 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
      have hmul := mul_le_mul_of_nonneg_right htri hs1
      rw [add_mul] at hmul
      rw [div_eq_mul_inv, div_eq_mul_inv]
      rw [mul_comm s⁻¹ |x - z|]
      linarith [hmul]
    linarith [h2, h3]
  rw [Real.dist_eq]
  exact key

end Commons.Analysis.Convolution