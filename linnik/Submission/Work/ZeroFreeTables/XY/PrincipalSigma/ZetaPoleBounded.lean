/-
# `Work.ZeroFreeTables.XY.PrincipalSigma.ZetaPoleBounded`

The logarithmic derivative of `ζ`, with the contribution of the pole `s = 1` subtracted, is
bounded together with its first two derivatives on the rectangle `{1 < Re s ≤ 4, |Im s| ≤ 5}`.

Writing `zetaPhi s = (s-1)ζ(s)` for the entire extension of `(s-1)ζ(s)` across `s = 1` (see
`ZetaPhiDefs`), the logarithmic derivative of `ζ` splits as

  `logDeriv ζ = logDeriv zetaPhi - 1/(s-1)`   (for `Re s > 1`),

so the pole-subtracted quantities of the statement are exactly

  `logDeriv zetaPhi`,  `(logDeriv zetaPhi)'`,  `(logDeriv zetaPhi)''`.

The function `zetaPhi` is analytic and nonzero on an open neighbourhood of the compact rectangle
`zetaRect = {1 ≤ Re s ≤ 4, |Im s| ≤ 5}`, hence `logDeriv zetaPhi` and its first two derivatives
are continuous there, and therefore bounded (applying `ContinuousOn`-compactness and taking real
parts).  Transporting this bound back along the pole-splitting identity gives the result.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.PrincipalSigma.ZetaPhiDefs

open Complex Set Filter
open scoped Topology

namespace Work.ZeroFreeTables.XY.PrincipalSigma

noncomputable section

/-! ## The iterated derivatives of `t ↦ (t-1)⁻¹` -/

/-- The first derivative of `t ↦ (t-1)⁻¹`. -/
lemma itDeriv1_inv_sub (s : ℂ) :
    iteratedDeriv 1 (fun t : ℂ => (t - 1)⁻¹) s = -(1 / (s - 1) ^ 2) := by
  rw [iteratedDeriv_inv_sub_one]
  have hcoef : ((-1:ℂ)^1 * ((Nat.factorial 1 : ℕ):ℂ)) = -1 := by norm_num
  rw [hcoef]
  rw [show (-1 : ℤ) - ((1:ℕ):ℤ) = -(2:ℤ) by norm_num, zpow_neg, div_eq_mul_inv]
  simp

/-- The second derivative of `t ↦ (t-1)⁻¹`. -/
lemma itDeriv2_inv_sub (s : ℂ) :
    iteratedDeriv 2 (fun t : ℂ => (t - 1)⁻¹) s = 2 / (s - 1) ^ 3 := by
  rw [iteratedDeriv_inv_sub_one]
  have hcoef : ((-1:ℂ)^2 * ((Nat.factorial 2 : ℕ):ℂ)) = 2 := by norm_num
  rw [hcoef]
  rw [show (-1 : ℤ) - ((2:ℕ):ℤ) = -(3:ℤ) by norm_num, zpow_neg, div_eq_mul_inv]
  simp

/-- `t ↦ (t-1)⁻¹` is `C^n` at every point with `Re s > 1`. -/
lemma contDiffAt_inv_sub_one (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    ContDiffAt ℂ n (fun t : ℂ => (t - 1)⁻¹) s := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  exact ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs1)).contDiffAt

/-! ## Splitting the pole off the logarithmic derivative of `ζ` -/

/-- Order zero: `logDeriv ζ s + 1/(s-1) = logDeriv zetaPhi s`. -/
lemma logDeriv_pole_id0 (s : ℂ) (hs : 1 < s.re) :
    logDeriv riemannZeta s + 1 / (s - 1) = logDeriv zetaPhi s := by
  rw [logDeriv_riemannZeta_eq s hs]
  ring

/-- `logDeriv ζ` agrees with `logDeriv zetaPhi - 1/(s-1)` near any point with `Re s > 1`. -/
lemma logDeriv_zetaPhi_eventually (s : ℂ) (hs : 1 < s.re) :
    logDeriv riemannZeta =ᶠ[𝓝 s] (logDeriv zetaPhi - fun t : ℂ => (t - 1)⁻¹) := by
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with t ht
  rw [logDeriv_riemannZeta_eq t ht, one_div]
  simp only [Pi.sub_apply]

/-- Order one: `(logDeriv ζ)'(s) - 1/(s-1)² = (logDeriv zetaPhi)'(s)`. -/
lemma logDeriv_pole_id1 (s : ℂ) (hs : 1 < s.re) :
    iteratedDeriv 1 (logDeriv riemannZeta) s - 1 / (s - 1) ^ 2
      = iteratedDeriv 1 (logDeriv zetaPhi) s := by
  have h1 := (logDeriv_zetaPhi_eventually s hs).iteratedDeriv 1
  rw [h1.self_of_nhds]
  rw [iteratedDeriv_sub (f := logDeriv zetaPhi) (g := fun t : ℂ => (t - 1)⁻¹) (x := s)
        (by exact (analyticAt_logDeriv_zetaPhi s hs).contDiffAt) (contDiffAt_inv_sub_one s hs 1)]
  rw [itDeriv1_inv_sub]
  ring

/-- Order two: `(logDeriv ζ)''(s) + 2/(s-1)³ = (logDeriv zetaPhi)''(s)`. -/
lemma logDeriv_pole_id2 (s : ℂ) (hs : 1 < s.re) :
    iteratedDeriv 2 (logDeriv riemannZeta) s + 2 / (s - 1) ^ 3
      = iteratedDeriv 2 (logDeriv zetaPhi) s := by
  have h1 := (logDeriv_zetaPhi_eventually s hs).iteratedDeriv 2
  rw [h1.self_of_nhds]
  rw [iteratedDeriv_sub (f := logDeriv zetaPhi) (g := fun t : ℂ => (t - 1)⁻¹) (x := s)
        (by exact (analyticAt_logDeriv_zetaPhi s hs).contDiffAt) (contDiffAt_inv_sub_one s hs 2)]
  rw [itDeriv2_inv_sub]
  ring

/-! ## Boundedness of the logarithmic derivative of `zetaPhi` on the rectangle -/

/-- The real parts of `logDeriv zetaPhi` and its first two derivatives are bounded on the
compact rectangle `zetaRect = {1 ≤ Re s ≤ 4, |Im s| ≤ 5}`. -/
theorem zetaPhiLogDerivBounded :
    ∃ M : ℝ, 0 < M ∧ ∀ s ∈ zetaRect,
      |(logDeriv zetaPhi s).re| ≤ M
      ∧ |(iteratedDeriv 1 (logDeriv zetaPhi) s).re| ≤ M
      ∧ |(iteratedDeriv 2 (logDeriv zetaPhi) s).re| ≤ M := by
  have h0 : ContinuousOn (fun s => (logDeriv zetaPhi s).re) zetaRect :=
    Complex.continuous_re.comp_continuousOn
      (analyticOnNhd_logDeriv_zetaPhi.continuousOn.mono zetaRect_subset_good)
  have h1 : ContinuousOn (fun s => (iteratedDeriv 1 (logDeriv zetaPhi) s).re) zetaRect := by
    have hc : ContinuousOn (iteratedDeriv 1 (logDeriv zetaPhi)) zetaRect := by
      have h := (analyticOnNhd_logDeriv_zetaPhi.deriv).continuousOn.mono zetaRect_subset_good
      simpa only [iteratedDeriv_one] using h
    exact Complex.continuous_re.comp_continuousOn hc
  have h2 : ContinuousOn (fun s => (iteratedDeriv 2 (logDeriv zetaPhi) s).re) zetaRect := by
    have hc : ContinuousOn (iteratedDeriv 2 (logDeriv zetaPhi)) zetaRect := by
      have heq : iteratedDeriv 2 (logDeriv zetaPhi) = deriv (deriv (logDeriv zetaPhi)) := by
        rw [show (2:ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
      rw [heq]
      exact (analyticOnNhd_logDeriv_zetaPhi.deriv.deriv).continuousOn.mono zetaRect_subset_good
    exact Complex.continuous_re.comp_continuousOn hc
  obtain ⟨C0, hC0⟩ := isCompact_zetaRect.exists_bound_of_continuousOn h0
  obtain ⟨C1, hC1⟩ := isCompact_zetaRect.exists_bound_of_continuousOn h1
  obtain ⟨C2, hC2⟩ := isCompact_zetaRect.exists_bound_of_continuousOn h2
  refine ⟨max (max |C0| |C1|) |C2| + 1, by positivity, ?_⟩
  intro s hs
  have hb0 : |(logDeriv zetaPhi s).re| ≤ C0 := by simpa using hC0 s hs
  have hb1 : |(iteratedDeriv 1 (logDeriv zetaPhi) s).re| ≤ C1 := by simpa using hC1 s hs
  have hb2 : |(iteratedDeriv 2 (logDeriv zetaPhi) s).re| ≤ C2 := by simpa using hC2 s hs
  have e0 : C0 ≤ max (max |C0| |C1|) |C2| + 1 := by
    have a : C0 ≤ |C0| := le_abs_self C0
    have b : |C0| ≤ max (max |C0| |C1|) |C2| := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have e1 : C1 ≤ max (max |C0| |C1|) |C2| + 1 := by
    have a : C1 ≤ |C1| := le_abs_self C1
    have b : |C1| ≤ max (max |C0| |C1|) |C2| := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have e2 : C2 ≤ max (max |C0| |C1|) |C2| + 1 := by
    have a : C2 ≤ |C2| := le_abs_self C2
    have b : |C2| ≤ max (max |C0| |C1|) |C2| := le_max_right _ _
    linarith
  exact ⟨le_trans hb0 e0, le_trans hb1 e1, le_trans hb2 e2⟩

/-! ## The target -/

theorem ZetaPoleBounded :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 4 → |s.im| ≤ 5 →
      |(logDeriv riemannZeta s + 1 / (s - 1)).re| ≤ M
      ∧ |(iteratedDeriv 1 (logDeriv riemannZeta) s - 1 / (s - 1) ^ 2).re| ≤ M
      ∧ |(iteratedDeriv 2 (logDeriv riemannZeta) s + 2 / (s - 1) ^ 3).re| ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := zetaPhiLogDerivBounded
  refine ⟨M, hMpos, ?_⟩
  intro s h1 h2 h3
  have hsr : s ∈ zetaRect := ⟨le_of_lt h1, h2, h3⟩
  obtain ⟨hb0, hb1, hb2⟩ := hM s hsr
  refine ⟨?_, ?_, ?_⟩
  · rw [logDeriv_pole_id0 s h1]; exact hb0
  · rw [logDeriv_pole_id1 s h1]; exact hb1
  · rw [logDeriv_pole_id2 s h1]; exact hb2

end

end Work.ZeroFreeTables.XY.PrincipalSigma
