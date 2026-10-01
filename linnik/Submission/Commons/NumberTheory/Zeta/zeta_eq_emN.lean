import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN_re_gt_one
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_analyticOn
import Submission.Commons.NumberTheory.Zeta.isPreconnected_re_gt_sdiff

open Complex Filter Set Finset
open scoped Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- The domain `{z | 0 < z.re ∧ z ≠ 1}` on which both sides of the identity are analytic. -/
private def zetaDomain : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}

/-- `s ↦ c ^ (-s)` is analytic for a constant base `c` in the slit plane. -/
private lemma analyticOnNhd_cpow_const_neg (U : Set ℂ) {c : ℂ} (hc : c ∈ Complex.slitPlane) :
    AnalyticOnNhd ℂ (fun s : ℂ => c ^ (-s)) U := by
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => c) U := analyticOnNhd_const
  have hlin : AnalyticOnNhd ℂ (fun s : ℂ => -s) U :=
    (analyticOnNhd_id (s := U)).neg
  exact AnalyticOnNhd.cpow hconst hlin (fun _ _ => hc)

/-- Each summand `n^{-s}` of the finite Euler–Maclaurin sum is analytic. -/
private lemma analyticOnNhd_powNeg_term (U : Set ℂ) {n : ℕ} (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (fun s : ℂ => (((n : ℕ) : ℂ) ^ (-s))) U := by
  have hslit : ((n : ℕ) : ℂ) ∈ Complex.slitPlane :=
    Complex.natCast_mem_slitPlane.2 (by omega)
  simpa using analyticOnNhd_cpow_const_neg U hslit

/-- The finite Euler–Maclaurin sum `∑_{n=1}^N n^{-s}` is analytic. -/
private lemma analyticOnNhd_partial_sum (U : Set ℂ) : ∀ N : ℕ,
    AnalyticOnNhd ℂ (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) U := by
  intro N
  induction N with
  | zero =>
      simpa using (analyticOnNhd_const (v := (0 : ℂ)) (s := U))
  | succ N ih =>
      have hsplit : ∀ s : ℂ,
          (∑ n ∈ Finset.Icc 1 (N + 1), (((n : ℕ) : ℂ) ^ (-s))) =
            (∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
              ((((N + 1 : ℕ) : ℂ) ^ (-s))) := by
        intro s
        rw [Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega : 1 ≤ N + 1)]
      have hfun : (fun s : ℂ => ∑ n ∈ Finset.Icc 1 (N + 1), (((n : ℕ) : ℂ) ^ (-s))) =
          (fun s : ℂ => (∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
            ((((N + 1 : ℕ) : ℂ) ^ (-s)))) := by
        funext s
        exact hsplit s
      rw [hfun]
      exact ih.add (analyticOnNhd_powNeg_term U (by omega : 1 ≤ N + 1))

/-- `s ↦ c ^ (1 - s)` is analytic for a constant base `c` in the slit plane. -/
private lemma analyticOnNhd_cpow_const_shift (U : Set ℂ) {c : ℂ} (hc : c ∈ Complex.slitPlane) :
    AnalyticOnNhd ℂ (fun s : ℂ => c ^ (1 - s)) U := by
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => c) U := analyticOnNhd_const
  have hlin : AnalyticOnNhd ℂ (fun s : ℂ => 1 - s) U :=
    (analyticOnNhd_const (v := (1 : ℂ)) (s := U)).sub (analyticOnNhd_id (s := U))
  exact AnalyticOnNhd.cpow hconst hlin (fun _ _ => hc)

/-- `s ↦ N^(1-s) / (s - 1)` is analytic on sets avoiding `s = 1`. -/
private lemma analyticOnNhd_mid_term (U : Set ℂ) {N : ℕ} (hN : 1 ≤ N)
    (hne : ∀ s ∈ U, s ≠ 1) :
    AnalyticOnNhd ℂ (fun s : ℂ => (((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) U := by
  have hslit : ((N : ℕ) : ℂ) ∈ Complex.slitPlane :=
    Complex.natCast_mem_slitPlane.2 (by omega)
  have hnum : AnalyticOnNhd ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (1 - s)) U :=
    analyticOnNhd_cpow_const_shift U hslit
  have hden : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) U :=
    (analyticOnNhd_id (s := U)).sub (analyticOnNhd_const (v := (1 : ℂ)) (s := U))
  refine AnalyticOnNhd.div hnum hden ?_
  intro s hs
  exact sub_ne_zero.mpr (hne s hs)


/-- The Euler–Maclaurin decomposition of the Riemann zeta function on the whole half-plane
`0 < re s` (excluding the pole at `s = 1`), obtained by analytic continuation from the case
`1 < re s` (`zeta_eq_emN_re_gt_one`). -/
theorem zeta_eq_emN {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
      ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) +
      (∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))) := by
  let P : ℂ → ℂ := fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))
  let M : ℂ → ℂ := fun s : ℂ => (((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)
  let T : ℂ → ℂ := fun s : ℂ =>
    ∑' m : ℕ,
      ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
        (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))
  -- analyticity of the three pieces on `zetaDomain`
  have hP : AnalyticOnNhd ℂ P zetaDomain := analyticOnNhd_partial_sum zetaDomain N
  have hM : AnalyticOnNhd ℂ M zetaDomain := analyticOnNhd_mid_term zetaDomain hN (by
    intro s hs
    exact hs.2)
  have hT : AnalyticOnNhd ℂ T zetaDomain := by
    simpa [T, zetaDomain] using emTerm_tsum_analyticOn N hN
  -- analyticity of the whole right hand side
  have hg : AnalyticOnNhd ℂ (P + M + T) zetaDomain := (hP.add hM).add hT
  -- analyticity of ζ on `zetaDomain`
  have hf : AnalyticOnNhd ℂ riemannZeta zetaDomain := by
    intro z hz
    have hz' : z ≠ 1 := by simpa [zetaDomain] using hz.2
    exact analyticOn_riemannZeta z (by simpa using hz')
  -- preconnectedness of `zetaDomain`
  have hpre : IsPreconnected zetaDomain := by
    simpa [zetaDomain] using isPreconnected_re_gt_sdiff (θ := 0) (by norm_num : (0 : ℝ) < 1)
  -- equality on the half-plane `1 < re`, a neighborhood of `2`
  have hEqW : ∀ z : ℂ, 1 < z.re → riemannZeta z = (P + M + T) z := by
    intro z hz
    simpa [P, M, T] using zeta_eq_emN_re_gt_one (s := z) hz N hN
  have hz0 : (2 : ℂ) ∈ zetaDomain := by
    simp [zetaDomain]
  have hWmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    exact (isOpen_lt (f := fun _ : ℂ => (1 : ℝ)) (g := fun z : ℂ => z.re)
      continuous_const Complex.continuous_re).mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})
  have hev : riemannZeta =ᶠ[𝓝 (2 : ℂ)] (P + M + T) := by
    change ∀ᶠ z in 𝓝 (2 : ℂ), riemannZeta z = (P + M + T) z
    filter_upwards [hWmem] with z hz
    exact hEqW z hz
  -- identity theorem
  have heqOn : Set.EqOn riemannZeta (P + M + T) zetaDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hpre hz0 hev
  have hsD : s ∈ zetaDomain := by
    simpa [zetaDomain] using ⟨hs0, hs1⟩
  have hfin : riemannZeta s = (P + M + T) s := heqOn hsD
  simpa [P, M, T] using hfin

end Commons.NumberTheory.Zeta
