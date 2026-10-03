import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup
import Submission.Work.PertCrux.phi_norm_le_of_far
import Submission.Work.Pert.Ksub2.tau0_phi_band_norm_le

/-!
# `Work.Pert.Ksub2.phi_norm_le_of_far_re_le`

The Fatou coordinate `φ = φ₀` of a §4.1-datum is **bounded near `∞` in the whole half-plane
`Re u ≤ B`**, for an arbitrary real `B`:

  for every `c > 0` there is `R > 0` with `‖d.φ u‖ ≤ c` for all `u` with `Re u ≤ B`, `‖u‖ ≥ R`.

This is the general-`B` form of `Work.Pert.Ksub2.phi_norm_le_of_far_re_le_one` (the case
`B = 1`).  The reduction to the sectorial statement `Work.PertCrux.phi_norm_le_of_far` is
elementary: any `u` with `Re u ≤ B` that lies *outside* Shishikura's repelling sector
`QLeft ξ₀ = {π/3 < |arg (u + ξ₀)|}` satisfies `2 Re (u + ξ₀) ≥ ‖u + ξ₀‖` (`Work.Parab.QLeft_iff`,
i.e. `|arg| ≤ π/3`), which forces `u.re ∈ [-ξ₀, B]` and `|u.im| ≤ 2 (B + ξ₀)`, hence
`‖u‖ ≤ max ξ₀ B + 2 (B + ξ₀)`
(`norm_le_max_of_not_mem_QLeft_re_le` below, the generalisation of
`Work.Pert.Ksub2.norm_le_max_of_not_mem_QLeft` to an arbitrary half-plane `Re ≤ B`).  That bound
is *independent of `u`*, so for `‖u‖` beyond it every admissible `u` lies in the sector, where
`φ → 0` by the asymptotic expansion field `ParabData.φ_asymp`.

No continuity or compactness argument is needed: the sectorial estimate
`Work.PertCrux.phi_norm_le_of_far` is uniform on `{u ∈ QLeft ξ₀ | ‖u‖ ≥ R₁}`.
-/

namespace Work.Pert.Ksub2

open MandelDim

/-- **The half-plane `{Re u ≤ B}` is bounded off the repelling sector.**  If `u` has `Re u ≤ B`
and lies outside Shishikura's sector `QLeft ξ`, then `2 Re (u + ξ) ≥ ‖u + ξ‖`, which forces
`-ξ ≤ Re u` and `|Im u| ≤ 2 (B + ξ)`, whence `‖u‖ ≤ max ξ B + 2 (B + ξ)`.

(When `B + ξ < 0` this case cannot occur at all — the pointwise contradiction is turned into the
claim by `linarith`.  This is why no separate hypothesis on `B` is needed.) -/
lemma norm_le_max_of_not_mem_QLeft_re_le {ξ B : ℝ} {u : ℂ} (hre : u.re ≤ B)
    (hQ : u ∉ MandelDim.QLeft ξ) : ‖u‖ ≤ max ξ B + 2 * (B + ξ) := by
  have h2 : ‖u + (ξ : ℂ)‖ ≤ 2 * (u + (ξ : ℂ)).re := by
    have hlt : ¬ (2 * (u + (ξ : ℂ)).re < ‖u + (ξ : ℂ)‖) :=
      fun h => hQ ((Work.Parab.QLeft_iff ξ u).mpr h)
    exact not_lt.mp hlt
  have hzre : 0 ≤ (u + (ξ : ℂ)).re := by
    have := norm_nonneg (u + (ξ : ℂ)); linarith
  have hzre' : 0 ≤ u.re + ξ := by
    rw [Complex.add_re, Complex.ofReal_re] at hzre; exact hzre
  by_cases hBs : 0 ≤ B + ξ
  · have hsum : (u + (ξ : ℂ)).re ≤ B + ξ := by
      rw [Complex.add_re, Complex.ofReal_re]; linarith
    have hsq : u.im ^ 2 ≤ 3 * (B + ξ) ^ 2 := by
      have h2sq : ‖u + (ξ : ℂ)‖ ^ 2 ≤ (2 * (u + (ξ : ℂ)).re) ^ 2 :=
        by nlinarith [h2, norm_nonneg (u + (ξ : ℂ))]
      have h1 : ‖u + (ξ : ℂ)‖ ^ 2 = (u + (ξ : ℂ)).re ^ 2 + (u + (ξ : ℂ)).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have h3 : (u + (ξ : ℂ)).im = u.im := by simp
      have h4 : (u + (ξ : ℂ)).re = u.re + ξ := by simp
      rw [h1, h3, h4] at h2sq
      have h5 : (u.re + ξ) ^ 2 ≤ (B + ξ) ^ 2 := by nlinarith [hsum, hzre']
      nlinarith [h2sq, h5]
    have him : |u.im| ≤ 2 * (B + ξ) := by
      have h2' : u.im ^ 2 ≤ (2 * (B + ξ)) ^ 2 := by nlinarith [hsq, hBs]
      rw [sq_le_sq] at h2'
      rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (B + ξ))] at h2'
    have hreabs : |u.re| ≤ max ξ B := by
      rw [abs_le]
      constructor
      · have h : ξ ≤ max ξ B := le_max_left _ _
        linarith
      · exact le_trans hre (le_max_right _ _)
    calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ ≤ max ξ B + 2 * (B + ξ) := by linarith
  · -- `B + ξ < 0` contradicts `-ξ ≤ Re u ≤ B`
    have hBs' : B + ξ < 0 := not_le.mp hBs
    linarith

/-- **`φ` is uniformly small far out in the half-plane `Re ≤ B`.**  Since the complement of the
repelling sector inside `{Re ≤ B}` is bounded by `max ξ₀ B + 2 (B + ξ₀)`, the sectorial estimate
`Work.PertCrux.phi_norm_le_of_far` applies to everything with `‖u‖` beyond that bound. -/
theorem phi_norm_le_of_far_re_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {c B : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : ℂ, u.re ≤ B → R ≤ ‖u‖ → ‖d.φ u‖ ≤ c := by
  obtain ⟨R₀, hR₀pos, hfar⟩ := Work.PertCrux.phi_norm_le_of_far d hc
  refine ⟨max R₀ (max (max d.ξ₀ B + 2 * (B + d.ξ₀) + 1) 1), ?_, ?_⟩
  · exact lt_of_lt_of_le hR₀pos (le_max_left _ _)
  · intro u hre hRu
    by_cases hQ : u ∈ MandelDim.QLeft d.ξ₀
    · -- inside the repelling sector: the sectorial estimate applies
      exact hfar u hQ (le_trans (le_max_left _ _) hRu)
    · -- off the sector the point is bounded, hence cannot be that far out
      have hb : ‖u‖ ≤ max d.ξ₀ B + 2 * (B + d.ξ₀) :=
        norm_le_max_of_not_mem_QLeft_re_le hre hQ
      have h2 : max d.ξ₀ B + 2 * (B + d.ξ₀) + 1 ≤ ‖u‖ :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hRu)
      linarith

end Work.Pert.Ksub2
