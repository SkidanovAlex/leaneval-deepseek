import Submission.Work.OddRadon.RadonProfileInjective
import Submission.Work.OddRadon.RadonXiReduction

/-!
# The inverse spherical Radon transform on rotation-invariant even data

`radonProfile_inv` restated directly in terms of `sphericalRadon`: the even profile `γ` is
recovered from the values of `𝓡 (γ ∘ (· 0))` at the paper's normals `ξ(α)`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **The inverse spherical Radon transform on rotation-invariant even data.**
For `d = 2n+1` (`n ≥ 1`) and an even `γ`, continuous on `ℝ` and of class `C¹` on `[-1,1]`,

  `γ u = radonInverse n (c ↦ 𝓡 (γ ∘ (· 0)) (ξ (arccos c))) u`   for `u ∈ (0,1)`,

where `ξ(α) = radonXi (2n+1) α` is the paper's normal. -/
theorem sphericalRadon_inv_rotationInvariant (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ}
    (hγc : Continuous γ) (hγ : ContDiffOn ℝ 1 γ (Set.Icc (-1) 1))
    (heven : ∀ t, γ (-t) = γ t) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    γ u = radonInverse n
      (fun c => sphericalRadon (2 * n + 1) (fun w => γ (w 0))
        (radonXi (2 * n + 1) (Real.arccos c))) u := by
  have h3 : 3 ≤ 2 * n + 1 := by omega
  have hEq : Set.EqOn
      (fun c : ℝ => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) *
        sphericalRadon (2 * n + 1) (fun w => γ (w 0))
          (radonXi (2 * n + 1) (Real.arccos c)))
      (fun c : ℝ => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) *
        radonProfile (2 * n + 1) γ c) (Set.Ioo 0 1) := by
    intro c hc
    change (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) *
        sphericalRadon (2 * n + 1) (fun w => γ (w 0)) (radonXi (2 * n + 1) (Real.arccos c))
      = (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * radonProfile (2 * n + 1) γ c
    have hmem : Real.arccos c ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨Real.arccos_nonneg c, Real.arccos_le_pi_div_two.mpr hc.1.le⟩
    rw [sphericalRadon_radonXi (2 * n + 1) h3 hγc hmem,
      Real.cos_arccos (by linarith [hc.1]) hc.2.le]
  unfold radonInverse
  rw [abelInvert_congr_of_eqOn hu.1 hu.2
    (abelReduceIter_congr_open isOpen_Ioo (n - 1) ((n : ℝ) - 3 / 2) hEq)]
  exact radonProfile_inv n hn hγ heven hu

end Work.OddRadon
