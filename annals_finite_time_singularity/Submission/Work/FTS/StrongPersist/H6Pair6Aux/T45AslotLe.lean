import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_slice_tendsto
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.gRHS_tendsto
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.SliceDPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

open Work.FTS.EllipticEst

/-
Pointwise form of the single-slice `∂_θ²`-Poincaré estimate in the open-trace class.

Write `L = D_θ = sin(2θ)∂_θ`, `LopIter i u = L^i u`, `thEta θ = sin(2θ)^{-η}`,
`thGam α θ = sin(2θ)^{-γ}` (`η = eta = 99/100`, `γ = gam α = 1 + α/10`),
`sliceV u = deriv (deriv u)`, and
`sliceD K α u θ = (u θ)²·thEta θ + (u' θ)²·thEta θ + (u'' θ)²·thEta θ
    + ∑_{1 ≤ m ≤ K} (L^m u'' θ)²·thGam α θ`
(`Work.FTS.EllSol.VopAux.sliceD`, defined in
`Submission/Work/FTS/EllSol/VopAux/SliceDDefs.lean`, which is the module to import; it also
contains `sd_LopIter_expand_open`, `sd_LopIter_sin_sq_bound`, `sd_LopIter_cos_bound`,
`sd_two_sub_gam_le_thEta`, `sd_four_sub_gam_le_thEta`, `sd_four_sub_gam_le_thGam`,
`sd_sum_sq_mul_le`, `sd_choose_sq_sum_le` and the `sliceD` summand lemmas
`sd_self_sq_le_sliceD`, `sd_deriv_sq_le_sliceD`, `sd_sliceV_sq_le_sliceD`,
`sd_LopIter_sliceV_sq_le_sliceD`).

Claim.  For `u` of class `C^∞` on the OPEN interval `(0, π/2)` (nothing is assumed outside) and
every `1 ≤ i ≤ K`, the pointwise bound

  `(L^i u θ)²·thGam α θ ≤ C·sliceD K α u θ`

holds at every interior angle `θ ∈ (0, π/2)`, with a constant `C` depending only on `K` (uniform
in `α ∈ (0,1]` and in `u`).

ROUTE (strong induction on `i`, valid because the expansion below reduces `i` to `i-1`).
* `i = 1`: `L u θ = sin(2θ)·u' θ`, so `(L u θ)²thGam α θ = (u' θ)²·sin(2θ)^{2-γ}`; on `Iθ` one has
  `sin(2θ) ≤ 1` and `-η ≤ 2-γ` (as `γ ≤ 11/10`), so by `sin_two_rpow_le_rpow`
  `sin(2θ)^{2-γ} ≤ thEta θ`, and `(u' θ)²thEta θ` is a summand of `sliceD` (`sd_deriv_sq_le_sliceD`).
* `i = n+2 ≥ 2`: expand (`sd_LopIter_expand_open`, whose only hypothesis is the `∀ n` open-interval
  smoothness; note `θ ∈ Ioo 0 (π/2)` is its `θ ∈ sdU`)
  `L^{n+2}u θ = ∑_{a ≤ n} C(n,a)·(L^a sin²(2·) θ)·(L^{n-a}u'' θ)
             + ∑_{a ≤ n} C(n,a)·(L^a (2cos 2·) θ)·(L^{n+1-a}u θ)`.
  Bound `(A+B)²·thGam ≤ 2A²thGam + 2B²thGam` and bound each sum by Cauchy–Schwarz with `thGam ≥ 0`
  (`sd_sum_sq_mul_le` + `sd_choose_sq_sum_le`, giving `∑_a C(n,a)² ≤ (n+1)4^n`).
  In the first sum, `|L^a sin²(2·) θ| ≤ D·sin²(2θ)` for `a ≤ K` (`sd_LopIter_sin_sq_bound`), and
  `sin(2θ)^4·thGam α θ ≤ thEta θ` resp. `≤ thGam α θ` (`sd_four_sub_gam_le_thEta`,
  `sd_four_sub_gam_le_thGam`): the terms with `n-a = 0` are dominated by the `(u'')²thEta` summand
  of `sliceD` (`sd_sliceV_sq_le_sliceD`), those with `1 ≤ n-a ≤ K` by
  `sd_LopIter_sliceV_sq_le_sliceD`.
  In the second sum, `|L^a(2cos 2·) θ| ≤ E` for `a ≤ K` (`sd_LopIter_cos_bound`), and the index
  `1 ≤ n+1-a ≤ n+1 = i-1 < i` lets the strong induction hypothesis apply with `B^{i-1} ≤ B^i`.
  Collecting the constants into `B^i` exactly as in the pre-existing (sorry-free, neigh-
  bourhood-smooth-class) proof `sfb_LopIter_expand_succ` + `key` inside
  `Submission/Work/FTS/EllipticEst/ThetaU/slice_f_bound_open.lean` — the `sfF1`/`sfF2` summands
  there are the two sums above verbatim — yields the claim for `i = n+2 ≤ K`, with
  `B := 2 + π/2 + 34·(K+1)²·D²·4^K` (any sufficiently large `B ≥ 1` works).
-/
theorem SliceDPointwise (K : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      ∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          ≤ C * Work.FTS.EllSol.VopAux.sliceD K α u θ := by
  -- the two `O(1)` bounds on the iterates of `sin²(2·)` and of `2 cos(2·)`
  obtain ⟨D, hD1, hDss⟩ := sd_LopIter_sin_sq_bound K
  obtain ⟨E, hEpos, hE⟩ := sd_LopIter_cos_bound K
  set F : ℝ := max D E with hFdef
  have hF1 : 1 ≤ F := le_trans hD1 (le_max_left D E)
  have hF0 : 0 ≤ F := le_trans zero_le_one hF1
  have hFD : D ≤ F := le_max_left D E
  have hFE : E ≤ F := le_max_right D E
  -- the two uniform bounds, with the single constant `F`
  have hDssF : ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
        ≤ F * (Real.sin (2 * θ)) ^ 2 :=
    fun a ha θ hθ =>
      le_trans (hDss a ha θ hθ) (mul_le_mul_of_nonneg_right hFD (sq_nonneg _))
  have hEF : ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ| ≤ F :=
    fun a ha θ hθ => le_trans (hE a ha θ hθ) hFE
  -- the constant of the induction, an upper bound for the one-step growth
  set B : ℝ := 2 + 34 * ((K : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ K with hBdef
  have hBextra : 0 ≤ 34 * ((K : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ K :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg F))
      (pow_nonneg (by norm_num) K)
  have hB1 : 1 ≤ B := by rw [hBdef]; linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hBstep : ∀ n ≤ K, 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n ≤ B := by
    intro n hn
    have h1 : ((n : ℝ) + 1) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by
      have hn' : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hn
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
    have h2 : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hn
    calc 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n
        ≤ 34 * ((K : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ K := by gcongr
      _ ≤ B := by rw [hBdef]; linarith
  refine ⟨B ^ K, pow_pos (lt_of_lt_of_le zero_lt_one hB1) K, ?_⟩
  intro α u hα0 hα1 hu i hi θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hP0θ : 0 ≤ sliceD K α u θ := sliceD_nonneg K α u hθI
  have hg0 : 0 ≤ thGam α θ := thGam_nonneg hθI
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθI
  have hs4le : ((Real.sin (2 * θ)) ^ 2) ^ 2 ≤ 1 := by
    have h := sd_sin_sq_le_one hθI
    have h0 : 0 ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    calc ((Real.sin (2 * θ)) ^ 2) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 1 := by norm_num
  -- the strong induction on the number of `L`-derivatives
  have key : ∀ m ≤ K, 1 ≤ m →
      (LopIter m u θ) ^ 2 * thGam α θ ≤ B ^ m * sliceD K α u θ := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih hmK hm1
    rcases eq_or_lt_of_le hm1 with hEq | hLt
    · -- `m = 1`: `(L u)² sin(2θ)^{-γ} = (u')² sin(2θ)^{2-γ} ≤ (u')² sin(2θ)^{-η} ≤ sliceD`
      have hm1' : m = 1 := hEq.symm
      subst hm1'
      have hLval : LopIter 1 u θ = Real.sin (2 * θ) * deriv u θ := by
        simp only [LopIter_succ, LopIter_zero, Work.Spaces.Lop]
      rw [hLval]
      have hrpow : (Real.sin (2 * θ)) ^ 2 * thGam α θ
          = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
        sd_sin_sq_mul_thGam hθI hα0 hα1
      have h2le := sd_two_sub_gam_le_thEta hα1 hθI
      have hdv := sd_deriv_sq_le_sliceD K α u hθI
      have hcomb : (Real.sin (2 * θ) * deriv u θ) ^ 2 * thGam α θ
          = (deriv u θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 * thGam α θ) := by ring
      rw [hcomb, hrpow]
      calc (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          ≤ (deriv u θ) ^ 2 * thEta θ := mul_le_mul_of_nonneg_left h2le (sq_nonneg _)
        _ ≤ sliceD K α u θ := hdv
        _ ≤ B ^ 1 * sliceD K α u θ := by
            rw [pow_one]
            exact le_mul_of_one_le_left hP0θ hB1
    · -- `m ≥ 2`: the expansion of `L^{n+2}u`
      have hm2 : 2 ≤ m := hLt
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
      have hnK : n ≤ K := by omega
      have hexp := sd_LopIter_expand_open n u hu hθ
      have hIH : ∀ j, 1 ≤ j → j ≤ n + 1 →
          (LopIter j u θ) ^ 2 * thGam α θ ≤ B ^ (n + 1) * sliceD K α u θ := by
        intro j hj1 hjK
        have hlt : j < n + 2 := by omega
        have hjK' : j ≤ K := by omega
        calc (LopIter j u θ) ^ 2 * thGam α θ ≤ B ^ j * sliceD K α u θ :=
              ih j hlt hjK' hj1
          _ ≤ B ^ (n + 1) * sliceD K α u θ :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hjK) hP0θ
      -- the `u''`-terms of the expansion
      have hterm1 : ∀ a ∈ Finset.range (n + 1),
          ((n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
            ≤ ((n.choose a : ℝ)) ^ 2 * (F ^ 2 * sliceD K α u θ) := by
        intro a ha
        have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have haK : a ≤ K := by omega
        have hsq : (LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
            ≤ F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by
          rw [← sq_abs]
          calc |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ| ^ 2
              ≤ (F * (Real.sin (2 * θ)) ^ 2) ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) (hDssF a haK θ hθI) 2
            _ = F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by ring
        rcases lt_or_eq_of_le ha' with hlt | heq
        · have hm1 : 1 ≤ n - a := by omega
          have hmK : n - a ≤ K := by omega
          have hmv := sd_LopIter_sliceV_sq_le_sliceD K α u
            (Finset.mem_Icc.mpr ⟨hm1, hmK⟩) hθI
          have hX : 0 ≤ (LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ :=
            mul_nonneg (sq_nonneg _) hg0
          have hcomb : ((n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
              = ((n.choose a : ℝ)) ^ 2
                * ((LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                  * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) := by ring
          rw [hcomb]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc (LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
              ≤ F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2
                * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ) :=
                mul_le_mul_of_nonneg_right hsq hX
            _ = F ^ 2 * (((Real.sin (2 * θ)) ^ 2) ^ 2
                  * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) := by ring
            _ ≤ F ^ 2 * (1 * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs4le hX) (sq_nonneg F)
            _ = F ^ 2 * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ) := by ring
            _ ≤ F ^ 2 * sliceD K α u θ := mul_le_mul_of_nonneg_left hmv (sq_nonneg F)
        · subst a
          rw [Nat.sub_self, LopIter_zero, Nat.choose_self, Nat.cast_one, one_pow, one_mul]
          have hsqn : (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
              ≤ F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by
            rw [← sq_abs]
            calc |LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ| ^ 2
                ≤ (F * (Real.sin (2 * θ)) ^ 2) ^ 2 :=
                  pow_le_pow_left₀ (abs_nonneg _) (hDssF n hnK θ hθI) 2
              _ = F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by ring
          have hrpow : ((Real.sin (2 * θ)) ^ 2) ^ 2 * thGam α θ
              = (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
            have h4a : ((Real.sin (2 * θ)) ^ 2) ^ 2 = (Real.sin (2 * θ)) ^ 4 := by ring
            rw [h4a, show thGam α θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from rfl]
            exact sd_pow_mul_rpow (sin_two_nonneg hθI) (by norm_num) (sd_gam_ne hα0)
              (by intro hc; exact sd_four_sub_gam_ne hα1 (sub_eq_zero.mpr hc))
          have hcomb : (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ * sliceV u θ) ^ 2
              * thGam α θ
              = (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                * ((sliceV u θ) ^ 2 * thGam α θ) := by ring
          have hmain : (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ * sliceV u θ) ^ 2
              * thGam α θ ≤ F ^ 2 * sliceD K α u θ := by
            rw [hcomb]
            have h4le := sd_four_sub_gam_le_thEta hα1 hθI
            have hvle := sd_sliceV_sq_le_sliceD K α u hθI
            calc (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                  * ((sliceV u θ) ^ 2 * thGam α θ)
                ≤ F ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2
                  * ((sliceV u θ) ^ 2 * thGam α θ) :=
                  mul_le_mul_of_nonneg_right hsqn (mul_nonneg (sq_nonneg _) hg0)
              _ = F ^ 2 * ((sliceV u θ) ^ 2
                    * (((Real.sin (2 * θ)) ^ 2) ^ 2 * thGam α θ)) := by ring
              _ = F ^ 2 * ((sliceV u θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) := by rw [hrpow]
              _ ≤ F ^ 2 * ((sliceV u θ) ^ 2 * thEta θ) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4le (sq_nonneg _))
                    (sq_nonneg F)
              _ ≤ F ^ 2 * sliceD K α u θ := mul_le_mul_of_nonneg_left hvle (sq_nonneg F)
          simpa using hmain
      -- the `u`-terms of the expansion
      have hterm2 : ∀ a ∈ Finset.range (n + 1),
          ((n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ
            ≤ ((n.choose a : ℝ)) ^ 2 * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)) := by
        intro a ha
        have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rcases Nat.eq_zero_or_pos a with h0a | hpos
        · subst a
          rw [Nat.choose_zero_right, Nat.cast_one, one_pow, Nat.sub_zero, one_mul]
          have hccval : LopIter 0 (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              = 2 * Real.cos (2 * θ) := by simp only [LopIter_zero]
          rw [hccval]
          have hc2 : (2 * Real.cos (2 * θ)) ^ 2 ≤ F ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hEF 0 (Nat.zero_le K) θ hθI) 2
          have hIHn := hIH (n + 1) (by omega) le_rfl
          have hcomb : (2 * Real.cos (2 * θ) * LopIter (n + 1) u θ) ^ 2 * thGam α θ
              = (2 * Real.cos (2 * θ)) ^ 2 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ) := by
            ring
          rw [hcomb]
          calc (2 * Real.cos (2 * θ)) ^ 2 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ)
              ≤ F ^ 2 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ) :=
                mul_le_mul_of_nonneg_right hc2 (mul_nonneg (sq_nonneg _) hg0)
            _ ≤ F ^ 2 * (B ^ (n + 1) * sliceD K α u θ) :=
                mul_le_mul_of_nonneg_left hIHn (sq_nonneg F)
            _ = 1 * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)) := by ring
        · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
          have hbK : b + 1 ≤ K := by omega
          have hcsq : (LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
              ≤ F ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hEF (b + 1) hbK θ hθI) 2
          have hj1 : 1 ≤ n + 1 - (b + 1) := by omega
          have hjK : n + 1 - (b + 1) ≤ n + 1 := by omega
          have hIHj := hIH (n + 1 - (b + 1)) hj1 hjK
          have hX : 0 ≤ (LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ :=
            mul_nonneg (sq_nonneg _) hg0
          have hcomb : ((n.choose (b + 1) : ℝ)
              * LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ
              = ((n.choose (b + 1) : ℝ)) ^ 2
                * ((LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
                  * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ)) := by ring
          rw [hcomb]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc (LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
                * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ)
              ≤ F ^ 2 * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ) :=
                mul_le_mul_of_nonneg_right hcsq hX
            _ ≤ F ^ 2 * (B ^ (n + 1) * sliceD K α u θ) :=
                mul_le_mul_of_nonneg_left hIHj (sq_nonneg F)
      -- Cauchy–Schwarz for the first sum
      have hS1sq : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
            * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
            * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
          ≤ ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ := by
        have hcs := sd_sum_sq_mul_le (Finset.range (n + 1))
          (fun a => (n.choose a : ℝ) * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
            * LopIter (n - a) (sliceV u) θ) hg0
        have hcs' : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                ((n.choose a : ℝ) * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                  * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ := by
          simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hcs
        calc (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                ((n.choose a : ℝ) * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                  * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ := hcs'
          _ ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                (((n.choose a : ℝ)) ^ 2 * (F ^ 2 * sliceD K α u θ)) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm1)
                (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
          _ = ((n : ℝ) + 1) * (F ^ 2 * sliceD K α u θ)
                * (∑ a ∈ Finset.range (n + 1), ((n.choose a : ℝ)) ^ 2) := by
              rw [← Finset.sum_mul]
              ring_nf
          _ ≤ ((n : ℝ) + 1) * (F ^ 2 * sliceD K α u θ)
                * (((n : ℝ) + 1) * (4 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left (sd_choose_sq_sum_le n)
                (mul_nonneg (by positivity) (mul_nonneg (sq_nonneg F) hP0θ))
          _ = ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ := by ring_nf
      -- Cauchy–Schwarz for the second sum
      have hS2sq : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
            * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
            * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ
          ≤ ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
              * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)) := by
        have hcs := sd_sum_sq_mul_le (Finset.range (n + 1))
          (fun a => (n.choose a : ℝ) * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
            * LopIter (n + 1 - a) u θ) hg0
        have hcs' : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                ((n.choose a : ℝ) * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                  * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ := by
          simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hcs
        calc (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                ((n.choose a : ℝ) * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                  * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ := hcs'
          _ ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                (((n.choose a : ℝ)) ^ 2 * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ))) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm2)
                (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
          _ = ((n : ℝ) + 1) * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ))
                * (∑ a ∈ Finset.range (n + 1), ((n.choose a : ℝ)) ^ 2) := by
              rw [← Finset.sum_mul]
              ring_nf
          _ ≤ ((n : ℝ) + 1) * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ))
                * (((n : ℝ) + 1) * (4 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left (sd_choose_sq_sum_le n)
                (mul_nonneg (by positivity)
                  (mul_nonneg (sq_nonneg F) (mul_nonneg (pow_nonneg hB0 _) hP0θ)))
          _ = ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
                * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)) := by ring_nf
      -- assembly
      rw [hexp]
      have hsq21 : ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ)
            + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ)) ^ 2
          ≤ 2 * ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2
            + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2) := by
        nlinarith [sq_nonneg ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ)
            - (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ))]
      have hstep : ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ)
            + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ)) ^ 2 * thGam α θ
          ≤ 2 * (((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
            + ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ)) := by
        have h1 := mul_le_mul_of_nonneg_right hsq21 hg0
        have h2 : 2 * ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                * LopIter (n - a) (sliceV u) θ) ^ 2
              + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                * LopIter (n + 1 - a) u θ) ^ 2) * thGam α θ
            = 2 * (((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
              + ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ)) := by ring
        linarith [h1, le_of_eq h2]
      have hbnd : 2 * (((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
            + ((∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
              * LopIter (n + 1 - a) u θ) ^ 2 * thGam α θ))
          ≤ 2 * (((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
            + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
              * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hS1sq hS2sq) (by norm_num)
      have hcore : 2 * (1 + B ^ (n + 1)) ≤ 34 * B ^ (n + 1) := by
        have hBp : 1 ≤ B ^ (n + 1) := one_le_pow₀ hB1
        linarith
      have hfac : 0 ≤ ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ :=
        mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg F))
          (pow_nonneg (by norm_num) n)) hP0θ
      have hfinal1 : 2 * (((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
            + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
              * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)))
          ≤ 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
              * sliceD K α u θ := by
        calc 2 * (((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
              + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
                * (F ^ 2 * (B ^ (n + 1) * sliceD K α u θ)))
            = ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
              * (2 * (1 + B ^ (n + 1))) := by ring_nf
          _ ≤ ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * sliceD K α u θ
              * (34 * B ^ (n + 1)) := mul_le_mul_of_nonneg_left hcore hfac
          _ = 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
              * sliceD K α u θ := by ring_nf
      have hlast : 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
            * sliceD K α u θ ≤ B ^ (n + 2) * sliceD K α u θ := by
        have hfacs : 0 ≤ B ^ (n + 1) * sliceD K α u θ :=
          mul_nonneg (pow_nonneg hB0 _) hP0θ
        have h := mul_le_mul_of_nonneg_right (hBstep n hnK) hfacs
        calc 34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
              * sliceD K α u θ
            = (34 * ((n : ℝ) + 1) ^ 2 * F ^ 2 * (4 : ℝ) ^ n)
              * (B ^ (n + 1) * sliceD K α u θ) := by ring
          _ ≤ B * (B ^ (n + 1) * sliceD K α u θ) := h
          _ = B ^ (n + 2) * sliceD K α u θ := by
              rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
              ring
      exact le_trans hstep (le_trans hbnd (le_trans hfinal1 hlast))
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hiK : i ≤ K := (Finset.mem_Icc.mp hi).2
  calc (LopIter i u θ) ^ 2 * thGam α θ ≤ B ^ i * sliceD K α u θ := key i hiK hi1
    _ ≤ B ^ K * sliceD K α u θ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hiK) hP0θ

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.sliceDerivPointLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

open Work.FTS.EllipticEst

/-- Declare inside `namespace Work.FTS.EllSol.VopAux` so the full name is `Work.FTS.EllSol.VopAux.sliceDerivPointLe`.

Context: `L u θ = sin(2θ)·u'(θ)`, `LopIter i u = (L^[i]) u`, `sliceV u = u''`,
`thEta θ = sin(2θ)^{-η}`, `thGam α θ = sin(2θ)^{-γ}`, `γ = gam α = 1+α/10`,
`sliceW K α w θ = (w θ)²·thEta θ + ∑_{m∈Icc 1 K}(L^m w θ)²·thGam α θ`.

ROUTE. `L (deriv u) = sin(2·) * sliceV u` definitionally, so for `i = j+1`,
`LopIter i (deriv u) = LopIter j (sin(2·) * sliceV u)`; the iterated Leibniz rule on
`sdU = Ioo 0 (π/2)` is `Work.FTS.EllSol.VopAux.sd_LopIter_mul_eqOn` (in `SliceDDefs.lean`,
which also provides `sd_contDiffOn_smoothOrder`, `sd_contDiffOn_deriv`,
`sd_two_sub_gam_le_thEta` (`sin(2θ)^{2-γ} ≤ thEta`, needs `α ≤ 1`),
`sd_four_sub_gam_le_thGam`, `sd_LopIter_sin_sq_bound`, `sd_sum_sq_mul_le`,
`sd_choose_sq_sum_le`), so with `c a = (j.choose a : ℝ)`, `S a = LopIter a sin(2·) θ`,
`Y a = LopIter (j-a) (sliceV u) θ`, `σ = sin(2θ)`, `γ = gam α`:
`LopIter i (deriv u) θ = ∑_{a∈range(j+1)} c a * S a * Y a` (LEFT-associated products).
Then `|c a| ≤ 2^i`, `|S a| ≤ Cs·σ` (hypothesis), and `Y a^2 * σ^(2-γ) ≤ Φ := sliceW K α (sliceV u) θ`:
for `a = j` (`Y = sliceV u`) by `sd_two_sub_gam_le_thEta`; for `a < j` since
`σ^{2-γ} ≤ σ^{-γ} = thGam α θ` (`sin_two_rpow_le_rpow`, `σ ≤ 1` on `Iθ`) and
`LopIter (j-a) (sliceV u) θ²·thGam α θ ≤ sliceW K α (sliceV u) θ` (index in `Icc 1 K`).
Close with `Work.EllipticEst.Blocks.slice_d_alg_core` (`Cc = 2^K`), which gives
`≤ (2^K)²·Cs²·i²·Φ ≤ max 1 ((2^K)²·K²·Cs²)·Φ` using `i ≤ K`, `Φ ≥ 0` (`sliceW_nonneg`). -/
theorem sliceDerivPointLe {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) {K : ℕ} {Cs : ℝ}
    (hCs : 0 ≤ Cs)
    (hSb : ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ|
        ≤ Cs * Real.sin (2 * θ))
    {α : ℝ} (hα1 : α ≤ 1) {i : ℕ} (hi : i ∈ Finset.Icc 1 K) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
      ≤ max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2)
          * Work.FTS.EllSol.VopAux.sliceW K α (Work.FTS.EllipticEst.sliceV u) θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hiK : i ≤ K := (Finset.mem_Icc.mp hi).2
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  subst i
  have hjK : j ≤ K := by omega
  -- `L (deriv u) = sin(2·) · sliceV u` definitionally
  have hiter : LopIter (j + 1) (deriv u)
      = LopIter j ((fun θ : ℝ => Real.sin (2 * θ)) * sliceV u) := by
    simp only [LopIter]
    rw [Function.iterate_succ_apply]
    rfl
  have huso : ContDiffOn ℝ Work.Stability.smoothOrder u sdU := sd_contDiffOn_smoothOrder hu
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ)) sdU := by
    fun_prop
  have hg : ContDiffOn ℝ Work.Stability.smoothOrder (sliceV u) sdU := by
    have h := sd_contDiffOn_deriv (sd_contDiffOn_deriv huso)
    simpa only [sliceV] using h
  -- the iterated Leibniz expansion of `L^{j+1}(deriv u)`
  have hleib : LopIter (j + 1) (deriv u) θ
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ * LopIter (j - a) (sliceV u) θ) := by
    rw [hiter]
    exact sd_LopIter_mul_eqOn hf hg j hθ
  have hΦ : 0 ≤ sliceW K α (sliceV u) θ := sliceW_nonneg K α (sliceV u) hθI
  have hσ : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθI
  have hCc : 0 ≤ (2 : ℝ) ^ K := by positivity
  have hc : ∀ a ∈ Finset.range (j + 1), |(j.choose a : ℝ)| ≤ (2 : ℝ) ^ K := by
    intro a _
    have h1 : j.choose a ≤ 2 ^ j := Nat.choose_le_two_pow j a
    have h2 : 2 ^ j ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hjK
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    calc ((j.choose a : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast le_trans h1 h2
      _ = (2 : ℝ) ^ K := by push_cast; ring
  have hS : ∀ a ∈ Finset.range (j + 1),
      |LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ| ≤ Cs * Real.sin (2 * θ) := by
    intro a ha
    exact hSb a (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hjK) θ hθI
  have hbase : (sliceV u θ) ^ 2 * thEta θ ≤ sliceW K α (sliceV u) θ := by
    rw [sliceW]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun m _ =>
      mul_nonneg (sq_nonneg _) (thGam_nonneg hθI))
  -- the datum slots `Y a²·σ^{2-γ} ≤ Φ`
  have hY : ∀ a ∈ Finset.range (j + 1),
      (LopIter (j - a) (sliceV u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        ≤ sliceW K α (sliceV u) θ := by
    intro a ha
    have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rcases eq_or_lt_of_le haj with h | h
    · -- `a = j`: `Y = sliceV u`, compared through `sd_two_sub_gam_le_thEta`
      subst h
      rw [Nat.sub_self, LopIter_zero]
      have hσγ := sd_two_sub_gam_le_thEta hα1 hθI
      have h2 := mul_le_mul_of_nonneg_left hσγ (sq_nonneg (sliceV u θ))
      linarith [h2, hbase]
    · -- `a < j`: the index `j - a` lies in `Icc 1 K`, so the slot is in `sliceW`
      have hm1 : 1 ≤ j - a := by omega
      have hmK : j - a ≤ K := by omega
      have hσg : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ thGam α θ := by
        have h := sin_two_rpow_le_rpow (a := 2 - Work.Spaces.gam α)
          (b := -(Work.Spaces.gam α)) (by rw [Work.Spaces.gam]; linarith) (by linarith) hθI
        simpa only [thGam] using h
      have hterm : (LopIter (j - a) (sliceV u) θ) ^ 2 * thGam α θ ≤ sliceW K α (sliceV u) θ := by
        have hsingle := Finset.single_le_sum
          (f := fun m => (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
          (fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθI))
          (Finset.mem_Icc.mpr ⟨hm1, hmK⟩)
        rw [sliceW]
        linarith [hsingle, mul_nonneg (sq_nonneg (sliceV u θ)) (thEta_nonneg hθI)]
      have h2 := mul_le_mul_of_nonneg_left hσg (sq_nonneg (LopIter (j - a) (sliceV u) θ))
      linarith [h2, hterm]
  have hcore := Work.EllipticEst.Blocks.slice_d_alg_core (j := j)
      (σ := Real.sin (2 * θ)) (γ := Work.Spaces.gam α)
      (Φ := sliceW K α (sliceV u) θ) (Cc := (2 : ℝ) ^ K) (Cs := Cs)
      hσ hCc hCs hΦ (c := fun a => (j.choose a : ℝ))
      (S := fun a => LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ)
      (Y := fun a => LopIter (j - a) (sliceV u) θ) hc hS hY
  have hnj : ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
    have : j + 1 ≤ K := by omega
    exact_mod_cast this
  have hsq : (((j + 1 : ℕ) : ℝ)) ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hnj 2
  have step1 : ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (((j + 1 : ℕ) : ℝ)) ^ 2
      ≤ ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have step2 : ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2
      ≤ max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    ring
  calc (LopIter (j + 1) (deriv u) θ) ^ 2 * thGam α θ
      = (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ * LopIter (j - a) (sliceV u) θ)) ^ 2
          * thGam α θ := by rw [hleib]
    _ = (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ * LopIter (j - a) (sliceV u) θ) ^ 2
          * thGam α θ := by simp only [mul_assoc]
    _ ≤ ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (((j + 1 : ℕ) : ℝ)) ^ 2
          * (sliceW K α (sliceV u) θ) := hcore
    _ ≤ max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2)
          * sliceW K α (sliceV u) θ :=
        mul_le_mul_of_nonneg_right (le_trans step1 step2) hΦ

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_seven_of_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Honesty.ellWeakPos_seven_of_slots`

The mode series `Ψ = psiSeries α F` is put in the weak hypothesis class
`EllWeakPos α 7 F Ψ` from the slot hypotheses that the surrounding `PhiStar` development
supplies:

* the equation `bslOp α Ψ = F` on the open quadrant (`heq`),
* the source's angular moment `F_* F ≡ 0` on `z > 0` (`hFstar`),
* the weighted summability of the mode coefficients (`hcoef`),
* `C^∞`-smoothness of `Ψ` on the open quadrant (`hsm`),
* the four honesty (`HkMem`) slots (`hF`, `hmemA`, `hmemB`, `hmemMix`).

The only conjuncts *not* among the hypotheses are the two Dirichlet traces of `Ψ`
(`Ψ z 0 = 0`, `Ψ z (π/2) = 0`, for **every** real `z`, not merely `z > 0`) and the vanishing of
the *solution's* moment `F_* Ψ`.  The traces are immediate: every basis function `eFam m` vanishes
at `θ = 0` (`gC (2m+1) 0 = 0`, `gC` odd) and at `θ = π/2` (`cos (π/2) = 0`), so every term of the
series vanishes there and hence so does the series — no summability is needed.  The moment is
`Fstar_psiSeries_eq_zero`, which needs exactly `hcoef` and `hFstar` on `z > 0`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

/-- `eFam m 0 = 0`: the angular basis vanishes at the right endpoint
(`gC (2m+1)` is `odd`, hence zero at the origin). -/
private lemma eFam_zero_theta_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
  simp only [Work.FTS.PhiStar.Gegenbauer.eFam, Real.sin_zero, Real.cos_zero, one_mul]
  exact Work.FTS.PhiStar.Gegenbauer.gC_odd_zero m

/-- `eFam m (π/2) = 0`: the angular basis vanishes at the left endpoint (`cos (π/2) = 0`). -/
private lemma eFam_zero_theta_pi_half (m : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2) = 0 := by
  simp only [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two, zero_mul]

/-- **The convolution trace `Ψ z 0 = 0` of the mode series** (conjunct 3 of `EllWeakPos`).  Every
term of the series vanishes, so the series does, for every real `z` — in particular for `z ≤ 0`,
where no honesty hypothesis is available. -/
theorem psiSeries_zero_theta_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.psiSeries α F z 0 = 0 := by
  simp only [Work.FTS.PhiStar.Series.psiSeries, eFam_zero_theta_zero, mul_zero, tsum_zero]

/-- **The convolution trace `Ψ z (π/2) = 0` of the mode series** (conjunct 4 of `EllWeakPos`). -/
theorem psiSeries_zero_theta_pi_half (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.psiSeries α F z (Real.pi / 2) = 0 := by
  simp only [Work.FTS.PhiStar.Series.psiSeries, eFam_zero_theta_pi_half, mul_zero, tsum_zero]


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.ae_extract_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Extraction of an a.e.-convergent subsequence of the `∂_z`-family (1-D engine)

`Work.FTS.StrongEps.LocUnif.D5.ae_extract_z`: from a sequence `L n` with a uniform Cauchy bound
in weighted `L¹` for the first `z`-derivatives, uniform convergence to `Llim`, and `L²` bounds on
the first derivatives, extract a subsequence along which `∂_z (L n)` converges a.e. to the
(totalised) `z`-derivative of `Llim`.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- Uniform convergence is preserved by passing to a subsequence. -/
theorem tendstoUniformlyOn_subseq {α β : Type*} [UniformSpace β] {F : ℕ → α → β} {f : α → β}
    {s : Set α} {ν : ℕ → ℕ} (hν : StrictMono ν)
    (h : TendstoUniformlyOn F f Filter.atTop s) :
    TendstoUniformlyOn (fun n => F (ν n)) f Filter.atTop s := by
  intro u hu
  exact (hν.tendsto_atTop.eventually (h u hu))

theorem ae_extract_z {a b a₀ b₀ c d M : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a < b)
    (hbb₀ : b < b₀) (hc : 0 < c) (hcd : c < d) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (fun p : ℝ × ℝ => L n p.1 p.2) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hcontdz : ∀ n, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hslice : ∀ n, ∀ θ ∈ Set.Icc c d, ContDiffOn ℝ 1 (fun z => L n z θ) (Set.Ioo a₀ b₀))
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε)
    (h1 : ∀ n, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M) :
    ∃ φ' : ℕ → ℕ, StrictMono φ' ∧
      ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)),
        Filter.Tendsto (fun n => Work.Spaces.pz (L (φ' n)) p.1 p.2) Filter.atTop
          (nhds (Work.Spaces.pz Llim p.1 p.2)) := by
  classical
  have hab' : a ≤ b := le_of_lt hab
  have hcd' : c ≤ d := le_of_lt hcd
  have ha₀b₀ : a₀ ≤ b₀ := le_of_lt (lt_trans ha₀a (lt_trans hab hbb₀))
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top⟩
  -- the clamped family: globally continuous, agreeing with `∂_z (L n)` on the box
  set Wc : ℕ → ℝ × ℝ → ℝ := fun n p =>
    Work.Spaces.pz (L n) (Set.projIcc a₀ b₀ ha₀b₀ p.1) (Set.projIcc c d hcd' p.2) with hWcdef
  have hWccont : ∀ n, Continuous (fun p : ℝ × ℝ => Wc n p) := by
    intro n
    have h1a : Continuous fun p : ℝ × ℝ =>
        ((Set.projIcc a₀ b₀ ha₀b₀ p.1 : Set.Icc a₀ b₀) : ℝ) :=
      continuous_subtype_val.comp
        ((continuous_projIcc (a := a₀) (b := b₀) (h := ha₀b₀)).comp continuous_fst)
    have h1b : Continuous fun p : ℝ × ℝ => ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ) :=
      continuous_subtype_val.comp
        ((continuous_projIcc (a := c) (b := d) (h := hcd')).comp continuous_snd)
    have h1 : Continuous fun p : ℝ × ℝ =>
        (((Set.projIcc a₀ b₀ ha₀b₀ p.1 : Set.Icc a₀ b₀) : ℝ),
         ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) := h1a.prodMk h1b
    have h2 : ∀ p : ℝ × ℝ,
        (((Set.projIcc a₀ b₀ ha₀b₀ p.1 : Set.Icc a₀ b₀) : ℝ),
         ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      fun p => Set.mem_prod.mpr ⟨(Set.projIcc a₀ b₀ ha₀b₀ p.1).2, (Set.projIcc c d hcd' p.2).2⟩
    have h4 : (fun p : ℝ × ℝ => Wc n p) = (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2) ∘
        fun p : ℝ × ℝ =>
          (((Set.projIcc a₀ b₀ ha₀b₀ p.1 : Set.Icc a₀ b₀) : ℝ),
           ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) := by
      funext p
      simp only [Function.comp_apply, hWcdef]
    rw [h4]
    exact (hcontdz n).comp_continuous h1 h2
  have hWceq : ∀ n, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      Wc n p = Work.Spaces.pz (L n) p.1 p.2 := by
    intro n p hp
    simp only [hWcdef, Set.projIcc_of_mem ha₀b₀ (⟨by linarith [hp.1.1, ha₀a],
      by linarith [hp.1.2, hbb₀]⟩ : p.1 ∈ Set.Icc a₀ b₀),
      Set.projIcc_of_mem hcd' hp.2, Subtype.coe_mk]
  have hWcaesm : ∀ n, AEStronglyMeasurable (Wc n) (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    fun n => (hWccont n).aestronglyMeasurable
  have hcauchy' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ x, ENNReal.ofReal |Wc n x - Wc m x| ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
        ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun n m hn hm => ?_⟩
    have h1c : (fun x : ℝ × ℝ => ENNReal.ofReal |Wc n x - Wc m x|)
        =ᵐ[volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)]
        (fun p : ℝ × ℝ => ENNReal.ofReal
          |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|) := by
      refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
      simp only [hWceq n p hp, hWceq m p hp]
    rw [lintegral_congr_ae h1c]
    exact hN n m hn hm
  obtain ⟨φ, hφ, w, hwmeas, hae, hL1⟩ :=
    subseq_tendsto_ae_of_cauchy_L1 (μ := volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      hWcaesm hcauchy'
  have hL1tend : Filter.Tendsto (fun k => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      ENNReal.ofReal |Wc (φ k) p - w p|) Filter.atTop (nhds 0) := by
    rw [tendsto_order]
    refine ⟨fun b hb => absurd hb (not_lt.mpr (zero_le : (0 : ℝ≥0∞) ≤ b)), fun b hb => ?_⟩
    obtain ⟨ε, hεpos, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < b := by
      obtain ⟨q, -, hqpos, hqb⟩ := (ENNReal.lt_iff_exists_real_btwn (a := 0) (b := b)).mp hb
      exact ⟨q, ENNReal.ofReal_pos.mp hqpos, hqb⟩
    obtain ⟨K, hK⟩ := hL1 ε hεpos
    refine Filter.eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
    exact lt_of_le_of_lt (hK k hk) hεb
  have hL1tend' : Filter.Tendsto (fun k => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      ENNReal.ofReal |(fun z θ => Wc (φ k) (z, θ)) p.1 p.2 - (fun z θ => w (z, θ)) p.1 p.2|)
      Filter.atTop (nhds 0) := hL1tend
  obtain ⟨ψ, hψ, hsliceconv⟩ :=
    slice_interval_tendsto_of_L1 (W := fun k z θ => Wc (φ k) (z, θ))
      (w := fun z θ => w (z, θ)) hab' hcd'
      (fun k => (hWccont (φ k)).aemeasurable)
      hwmeas.aemeasurable hL1tend'
  have hsliceconv' : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), ∀ z ∈ Set.Icc a b,
      ∀ z₀ ∈ Set.Icc a b,
      Filter.Tendsto (fun k => ∫ u in z..z₀, Wc (φ (ψ k)) (u, θ)) Filter.atTop
        (nhds (∫ u in z..z₀, w (u, θ))) := by
    filter_upwards [hsliceconv] with θ hθ z hz z₀ hz₀
    exact hθ z hz z₀ hz₀
  have hwint : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)),
      IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume := by
    obtain ⟨K, hK⟩ := hL1 1 one_pos
    have hW2 : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Wc (φ K) p) ^ 2) ≤ ENNReal.ofReal M := by
      have h1c : (fun p : ℝ × ℝ => ENNReal.ofReal ((Wc (φ K) p) ^ 2))
          =ᵐ[volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)]
          (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pz (L (φ K)) p.1 p.2) ^ 2)) := by
        refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
        simp only [hWceq (φ K) p hp]
      rw [lintegral_congr_ae h1c]
      refine le_trans (MeasureTheory.lintegral_mono_set ?_) (h1 (φ K))
      exact Set.prod_mono (Set.Icc_subset_Icc ha₀a.le (le_of_lt hbb₀)) Subset.rfl
    have hdiff : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Wc (φ K) p - w p| ≤ ENNReal.ofReal 1 := hK K le_rfl
    exact ae_integrableOn_slice_of_bounds (W := fun z θ => Wc (φ K) (z, θ))
      (w := fun z θ => w (z, θ)) hab' hcd' hM zero_le_one
      ((hWccont (φ K)).aemeasurable) hwmeas.aemeasurable hW2 hdiff
  have hident := ae_limit_eq_deriv (L := fun k => L (φ (ψ k))) (Llim := Llim)
    (W := fun k => Wc (φ (ψ k))) (w := w) ha₀ ha₀a hab hbb₀ hcd
    (fun k => hcont (φ (ψ k)))
    (fun k θ hθ => hslice (φ (ψ k)) θ hθ)
    (fun k p hp => hWceq (φ (ψ k)) p hp)
    (tendstoUniformlyOn_subseq (hφ.comp hψ) hconv)
    hwmeas hsliceconv' hwint
  refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
  filter_upwards [hae, hident, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)]
    with p hp1 hp2 hpbox
  have hp1' : Filter.Tendsto (fun k => Wc (φ (ψ k)) p) Filter.atTop (nhds (w p)) :=
    hp1.comp (hψ.tendsto_atTop)
  rw [hp2] at hp1'
  refine hp1'.congr' (Filter.Eventually.of_forall fun k => ?_)
  simp only [Function.comp_apply]
  exact hWceq (φ (ψ k)) p hpbox

/-! ## The `θ`-direction engine

The same extraction with the two coordinate boxes exchanged: the `z`-family `pz (L n)` becomes
the `θ`-family `pth (L n)`, the data box `Icc a b ×ˢ Icc c₀ d₀` becomes `Icc c₀ d₀ ×ˢ Icc a b`
and the conclusion box `Icc a b ×ˢ Icc c d` becomes `Icc c d ×ˢ Icc a b`.  The proof is a
transposition of `ae_extract_z` along the measure-preserving involution `Prod.swap` (whose
measure-preservation on the boxes is `Measure.prod_swap`). -/

/-- `Prod.swap` sends the measure of the rectangle `[a,b] × [c,d]` to that of the rectangle
`[c,d] × [a,b]`. -/
lemma map_swap_box (a b c d : ℝ) :
    Measure.map Prod.swap (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      = volume.restrict (Set.Icc c d ×ˢ Set.Icc a b) := by
  have h₁ : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) : Measure (ℝ × ℝ))
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d)) := by
    have h : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) : Measure (ℝ × ℝ))
        = (volume.prod volume).restrict (Set.Icc a b ×ˢ Set.Icc c d) :=
      congrArg (fun (m : Measure (ℝ × ℝ)) => m.restrict (Set.Icc a b ×ˢ Set.Icc c d))
        (Measure.volume_eq_prod ℝ ℝ)
    rw [h, Measure.prod_restrict]
  have h₂ : (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b) : Measure (ℝ × ℝ))
      = (volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Icc a b)) := by
    have h : (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b) : Measure (ℝ × ℝ))
        = (volume.prod volume).restrict (Set.Icc c d ×ˢ Set.Icc a b) :=
      congrArg (fun (m : Measure (ℝ × ℝ)) => m.restrict (Set.Icc c d ×ˢ Set.Icc a b))
        (Measure.volume_eq_prod ℝ ℝ)
    rw [h, Measure.prod_restrict]
  rw [h₁, h₂, Measure.prod_swap]

/-- The `lintegral` over the swapped rectangle, pulled back along `Prod.swap`. -/
lemma lintegral_swap_box {a b c d : ℝ} (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, f p
      = ∫⁻ q in Set.Icc c d ×ˢ Set.Icc a b, f (Prod.swap q) := by
  have hmp : MeasurePreserving Prod.swap
      (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b))
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    ⟨measurable_swap, map_swap_box c d a b⟩
  have hg : (⇑(MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)) = Prod.swap := by
    funext p
    rfl
  have h := hmp.lintegral_map_equiv f MeasurableEquiv.prodComm
  rw [hg] at h
  exact h

theorem ae_extract_theta {a b c c₀ d d₀ M : ℝ} (ha : 0 < a) (hab : a < b)
    (hc₀ : 0 < c₀) (hc₀c : c₀ < c) (hcd : c < d) (hdd₀ : d < d₀) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (fun p : ℝ × ℝ => L n p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hcontth : ∀ n, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (L n) p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hslice : ∀ n, ∀ z ∈ Set.Icc a b, ContDiffOn ℝ 1 (fun θ => L n z θ) (Set.Ioo c₀ d₀))
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pth (L n) p.1 p.2 - Work.Spaces.pth (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε)
    (h1 : ∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c₀ d₀,
        ENNReal.ofReal ((Work.Spaces.pth (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M) :
    ∃ φ' : ℕ → ℕ, StrictMono φ' ∧
      ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)),
        Filter.Tendsto (fun n => Work.Spaces.pth (L (φ' n)) p.1 p.2) Filter.atTop
          (nhds (Work.Spaces.pth Llim p.1 p.2)) := by
  classical
  have hcont' : ∀ n, ContinuousOn (fun p : ℝ × ℝ => L n p.2 p.1)
      (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) := fun n =>
    (hcont n).comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)
  have hcontdz' : ∀ n, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (L n) p.2 p.1)
      (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) := fun n =>
    (hcontth n).comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)
  have hslice' : ∀ n, ∀ y ∈ Set.Icc a b, ContDiffOn ℝ 1 (fun x => L n y x) (Set.Ioo c₀ d₀) :=
    fun n y hy => hslice n y hy
  have hconv' : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.2 p.1) (fun p => Llim p.2 p.1)
      Filter.atTop (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε] with n hn p hp
    exact hn (Prod.swap p) ⟨hp.2, hp.1⟩
  have hcauchy' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc c d ×ˢ Set.Icc a b,
        ENNReal.ofReal
          |Work.Spaces.pth (L n) p.2 p.1 - Work.Spaces.pth (L m) p.2 p.1|
          ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun n m hn hm => ?_⟩
    have hgoal : ∫⁻ q in Set.Icc c d ×ˢ Set.Icc a b,
        (fun p : ℝ × ℝ => ENNReal.ofReal
          |Work.Spaces.pth (L n) p.1 p.2 - Work.Spaces.pth (L m) p.1 p.2|) (Prod.swap q)
        ≤ ENNReal.ofReal ε := by
      rw [← lintegral_swap_box (a := a) (b := b) (c := c) (d := d)
        (f := fun p : ℝ × ℝ => ENNReal.ofReal
          |Work.Spaces.pth (L n) p.1 p.2 - Work.Spaces.pth (L m) p.1 p.2|)]
      exact hN n m hn hm
    exact hgoal
  have h1' : ∀ n, ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
      ENNReal.ofReal ((Work.Spaces.pth (L n) p.2 p.1) ^ 2) ≤ ENNReal.ofReal M := by
    intro n
    have hgoal : ∫⁻ q in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
        (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth (L n) p.1 p.2) ^ 2))
          (Prod.swap q) ≤ ENNReal.ofReal M := by
      rw [← lintegral_swap_box (a := a) (b := b) (c := c₀) (d := d₀)
        (f := fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth (L n) p.1 p.2) ^ 2))]
      exact h1 n
    exact hgoal
  obtain ⟨φ', hφ', hae⟩ :=
    ae_extract_z (L := fun n x y => L n y x) (Llim := fun x y => Llim y x)
      (a := c) (b := d) (a₀ := c₀) (b₀ := d₀) (c := a) (d := b) (M := M)
      hc₀ hc₀c hcd hdd₀ ha hab hM hcont' hcontdz' hslice' hconv' hcauchy' h1'
  refine ⟨φ', hφ', ?_⟩
  have hmp : MeasurePreserving Prod.swap
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b)) :=
    ⟨measurable_swap, map_swap_box a b c d⟩
  rw [MeasureTheory.ae_iff] at hae ⊢
  exact hmp.preimage_null hae

end Work.FTS.StrongEps.LocUnif.D5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.gRHS_abs_le_on_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `sin(2θ)^{-q}·H²` -/
def IbpU (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun θ => (Real.sin (2*θ))^(-q) * (H θ)^2

/-- `sin(2θ)·∂_θH·H·sin(2θ)^{-q}` -/
def IbpA (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.sin (2*θ) * deriv H θ * H θ * (Real.sin (2*θ))^(-q)

/-- `cos(2θ)·sin(2θ)^{-q}·H²` -/
def IbpE (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.cos (2*θ) * (Real.sin (2*θ))^(-q) * (H θ)^2

theorem slice_ibp_base {q : ℝ} {H : ℝ → ℝ}
    (hH : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt H (deriv H θ) θ)
    (hU : MeasureTheory.IntegrableOn (IbpU q H) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn (IbpA q H) Work.Spaces.Iθ)
    (hE : MeasureTheory.IntegrableOn (IbpE q H) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, IbpA q H θ) = (q-1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ) := by
  have hpi : (0:ℝ) < Real.pi/2 := by positivity
  set v' : ℝ → ℝ := fun θ => 2 * IbpA q H θ - 2*(q-1) * IbpE q H θ
  have hderiv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      HasDerivAt (fun θ' => Real.sin (2*θ') * ((Real.sin (2*θ'))^(-q) * (H θ')^2))
        (v' θ) θ := by
    intro θ hθ
    have h1 := hasDerivAt_ibpPrim (q := q) hH θ hθ
    simpa only [v', IbpA, IbpE] using h1
  have hu_nonneg : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), 0 ≤ IbpU q H θ := by
    intro θ hθ
    have hs : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    exact mul_nonneg (Real.rpow_nonneg hs.le _) (sq_nonneg _)
  have hv'_int : MeasureTheory.IntegrableOn v' Work.Spaces.Iθ := by
    rw [show v' = fun θ => 2 * IbpA q H θ - 2*(q-1) * IbpE q H θ from rfl]
    exact hA.const_mul 2 |>.sub (hE.const_mul (2*(q-1)))
  have hlim := tendsto_sin_mul_zero_of_integrable hU hu_nonneg hderiv hv'_int
  have hInt : IntervalIntegrable v' volume (0:ℝ) (Real.pi/2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hv'_int.mono_set Set.Ioc_subset_Icc_self)
  have hFTC : (∫ θ in (0:ℝ)..(Real.pi/2), v' θ) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hInt hlim.1 hlim.2
    simpa using h
  have hconv : ∀ g : ℝ → ℝ,
      (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0:ℝ)..(Real.pi/2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi/2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have h0 : (∫ θ in Work.Spaces.Iθ, v' θ) = 0 := by rw [hconv]; exact hFTC
  have hdecomp : (∫ θ in Work.Spaces.Iθ, v' θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, IbpA q H θ)
        - 2*(q-1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ) := by
    rw [show v' = fun θ => 2 * IbpA q H θ - 2*(q-1) * IbpE q H θ from rfl]
    rw [MeasureTheory.integral_sub (hA.const_mul 2) (hE.const_mul (2*(q-1))),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hdecomp] at h0
  linarith

theorem slice_ibp_mul {q : ℝ} {H : ℝ → ℝ} (c : ℝ)
    (hH : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt H (deriv H θ) θ)
    (hU : MeasureTheory.IntegrableOn (fun θ => IbpU q H θ * c) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn (fun θ => IbpA q H θ * c) Work.Spaces.Iθ)
    (hE : MeasureTheory.IntegrableOn (fun θ => IbpE q H θ * c) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, IbpA q H θ * c) = (q-1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ * c) := by
  by_cases hc : c = 0
  · simp [hc]
  · have key : ∀ f : ℝ → ℝ, MeasureTheory.IntegrableOn (fun θ => f θ * c) Work.Spaces.Iθ →
        MeasureTheory.IntegrableOn f Work.Spaces.Iθ := by
      intro f hf
      have h1 : MeasureTheory.IntegrableOn (fun θ => c⁻¹ * (f θ * c)) Work.Spaces.Iθ :=
        hf.const_mul c⁻¹
      refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
      show c⁻¹ * (f θ * c) = f θ
      rw [mul_comm (f θ) c, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have hU' := key _ hU
    have hA' := key _ hA
    have hE' := key _ hE
    have hbase := slice_ibp_base hH hU' hA' hE'
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const, hbase]
    ring

set_option maxHeartbeats 1000000 in
theorem wip_Dth_ibp {h : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ} {q : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hint0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth h z θ * h z θ * Φ z
        * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => Φ z * (Real.sin (2 * θ)) ^ (-q))
        (Work.Spaces.Dth h) h
      = (q - 1) * (∫ z in Work.Spaces.Iz, Φ z * ∫ θ in Work.Spaces.Iθ,
          Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * h z θ ^ 2) := by
  have hsliceU : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => IbpU q (fun θ' => h z θ') θ * Φ z)
        Work.Spaces.Iθ := by
    have h0 : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * (Real.sin (2*θ))^(-q)))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hint0
    have h0' : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => IbpU q (fun θ' => h z θ') θ * Φ z))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      h0.congr (Eventually.of_forall fun p => by
        simp only [Function.uncurry, IbpU]
        ring)
    have hmeas : (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :
          MeasureTheory.Measure (ℝ × ℝ))
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.Measure.prod_restrict (μ := (volume : MeasureTheory.Measure ℝ))
        (ν := (volume : MeasureTheory.Measure ℝ)) Work.Spaces.Iz Work.Spaces.Iθ).symm
    rw [hmeas] at h0'
    simpa only [MeasureTheory.IntegrableOn, Function.uncurry] using h0'.prod_right_ae
  have hsliceA : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => IbpA q (fun θ' => h z θ') θ * Φ z)
        Work.Spaces.Iθ := by
    have h0 : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.Dth h z θ * h z θ * Φ z
          * (Real.sin (2*θ))^(-q)))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hint1
    have h0' : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => IbpA q (fun θ' => h z θ') θ * Φ z))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      h0.congr (Eventually.of_forall fun p => by
        simp only [Function.uncurry, IbpA, Work.Spaces.Dth, Work.Spaces.pth]
        ring)
    have hmeas : (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :
          MeasureTheory.Measure (ℝ × ℝ))
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.Measure.prod_restrict (μ := (volume : MeasureTheory.Measure ℝ))
        (ν := (volume : MeasureTheory.Measure ℝ)) Work.Spaces.Iz Work.Spaces.Iθ).symm
    rw [hmeas] at h0'
    simpa only [MeasureTheory.IntegrableOn, Function.uncurry] using h0'.prod_right_ae
  have hsliceE : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => IbpE q (fun θ' => h z θ') θ * Φ z)
        Work.Spaces.Iθ := by
    have h0 : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * Real.cos (2*θ)
          * (Real.sin (2*θ))^(-q)))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hint2
    have h0' : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => IbpE q (fun θ' => h z θ') θ * Φ z))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      h0.congr (Eventually.of_forall fun p => by
        simp only [Function.uncurry, IbpE]
        ring)
    have hmeas : (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :
          MeasureTheory.Measure (ℝ × ℝ))
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.Measure.prod_restrict (μ := (volume : MeasureTheory.Measure ℝ))
        (ν := (volume : MeasureTheory.Measure ℝ)) Work.Spaces.Iz Work.Spaces.Iθ).symm
    rw [hmeas] at h0'
    simpa only [MeasureTheory.IntegrableOn, Function.uncurry] using h0'.prod_right_ae
  have hzpos : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), (0:ℝ) < z := by
    have hzeq : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0:ℝ)) := by
      apply MeasureTheory.Measure.restrict_congr_set
      rw [MeasureTheory.ae_eq_set]
      have h1 : Work.Spaces.Iz \ Set.Ioi (0:ℝ) = {(0:ℝ)} := by
        ext x
        simp only [Work.Spaces.Iz, Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩; linarith
        · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
      constructor
      · rw [h1, measure_singleton]
      · rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
        rw [Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]
    rw [hzeq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hkey : (fun z => Φ z * ∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ)
      =ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => Φ z * ((q-1) * ∫ θ in Work.Spaces.Iθ,
        IbpE q (fun θ' => h z θ') θ)) := by
    filter_upwards [hsliceU, hsliceA, hsliceE, hzpos] with z hU hA hE hz
    have hH : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        HasDerivAt (fun θ' => h z θ') (deriv (fun θ' => h z θ') θ) θ := by
      intro θ hθ
      exact (((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hb := slice_ibp_mul (q := q) (H := fun θ' => h z θ') (Φ z) hH hU hA hE
    have e1 : Φ z * (∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ)
        = (∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ * Φ z) := by
      rw [MeasureTheory.integral_mul_const]; ring
    have e2 : Φ z * (∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ)
        = (∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ * Φ z) := by
      rw [MeasureTheory.integral_mul_const]; ring
    rw [show Φ z * ((q-1) * (∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ))
        = (q-1) * (Φ z * (∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ))
        from by ring, e1, e2]
    exact hb
  simp only [Work.Coercivity.wip]
  have hstep1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.Dth h z θ * h z θ * (Φ z * (Real.sin (2*θ))^(-q)))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          IbpA q (fun θ' => h z θ') θ * Φ z := by
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [IbpA, Work.Spaces.Dth, Work.Spaces.pth]
    ring
  rw [hstep1]
  rw [show (fun z => ∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ * Φ z)
      = fun z => Φ z * ∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ
      from funext fun z => by rw [MeasureTheory.integral_mul_const]; ring]
  rw [MeasureTheory.integral_congr_ae hkey]
  rw [show (fun z => Φ z * ((q-1) * ∫ θ in Work.Spaces.Iθ,
          IbpE q (fun θ' => h z θ') θ))
      = fun z => (q-1) * (Φ z * ∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ)
      from funext fun z => by ring,
    MeasureTheory.integral_const_mul]
  rfl

end Work.FTS.StrongPersist.H6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-- The angular factor `(α + sin 2θ)·sin(2θ)^{α/5}` occurring in `Abnd` for `i ≥ 1`. -/
def Xfac (α θ : ℝ) : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- Unfolding of `Abnd` in terms of `Xfac`. -/
theorem Abnd_eq_Xfac (α : ℝ) (i : ℕ) (θ : ℝ) :
    Abnd α i θ = if i = 0 then 1 else Xfac α θ := rfl

/-- `Abnd α i θ` is the pure angular factor as soon as `i ≠ 0`. -/
theorem Abnd_of_ne_zero {α : ℝ} {i : ℕ} (hi : i ≠ 0) (θ : ℝ) :
    Abnd α i θ = Xfac α θ := by
  simp [Abnd_eq_Xfac, hi]

/-- `Abnd α 0 θ = 1`. -/
theorem Abnd_zero (α θ : ℝ) : Abnd α 0 θ = 1 := by
  simp [Abnd_eq_Xfac]

/-- `Xfac` is nonnegative on the angular interval. -/
theorem Xfac_nonneg {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) :
    0 ≤ Xfac α θ :=
  mul_nonneg (by linarith) (Real.rpow_nonneg hθ _)

/-- `WlInf` is nonnegative whenever it is the honest sum of `L^∞`-norms. -/
theorem WlInf_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α l f) :
    0 ≤ Work.Spaces.WlInf α l f := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α l f hmem)
    (Work.Spaces.wlThSum_nonneg α l f hmem)

/-- The Bell numbers of the rows `j ≤ 6` are at most `203`. -/
theorem bell_le_six (j : ℕ) (hj : j ≤ 6) : Work.Spaces.bell j ≤ 203 := by
  interval_cases j <;> decide

/-- The Stirling-weighted sum bound for the rows `j ≤ 6`: if `|z^k ∂_z^k h| ≤ M` for
`k ≤ j` then `|∑_k S(j,k) z^k ∂_z^k h| ≤ 203·M`. -/
theorem abs_sum_scoef_le_six {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {j : ℕ} (hj : j ≤ 6) (hM : 0 ≤ M)
    (hx : ∀ k ≤ j, |z ^ k * Work.Spaces.pzIter k h z θ| ≤ M) :
    |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
        * (z ^ k * Work.Spaces.pzIter k h z θ)| ≤ 203 * M :=
  (Work.Spaces.abs_sum_scoef_mul_le j M (fun k => z ^ k * Work.Spaces.pzIter k h z θ) hx).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le_six j hj) hM)

/-- **The pointwise slot bound in terms of the `𝒲^{6,∞}`-norm.** -/
theorem mixed_le_WlInf (α : ℝ) (hα : 0 < α) (A : ℝ → ℝ → ℝ)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hmem : Work.Spaces.WlInfMem α 6 A) :
    ∀ (j i : ℕ), i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ 203 * Work.Spaces.WlInf α 6 A * Abnd α i θ := by
  intro j i hij z θ hz hθ0 hθ1
  have hz0 : 0 ≤ z := le_of_lt hz
  have hz1 : 0 < z + 1 := by linarith
  have hzI : z ∈ Work.Spaces.Iz := hz0
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hθIoo : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 A := WlInf_nonneg α 6 A hmem
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · -- no angular derivative: `|D_z^j A| ≤ 203·|A|_𝒲`
    have hj6 : j ≤ 6 := by omega
    have hd : ∀ k ≤ j,
        DifferentiableOn ℝ (fun y : ℝ => Work.Spaces.pzIter k A y θ) (Set.Ioi 0) :=
      fun k _ => ((hA.pzIter k).curry_z hθIoo).differentiableOn (by simp)
    have hx : ∀ k ≤ j, |z ^ k * Work.Spaces.pzIter k A z θ| ≤ Work.Spaces.WlInf α 6 A := by
      intro k hk
      have hk6 : k ≤ 6 := by omega
      have h2 : (z + 1) ^ k * |Work.Spaces.pzIter k A z θ| ≤ Work.Spaces.WlInf α 6 A := by
        have h := Work.Spaces.WlInf_z_bound α 6 A hmem k hk6 z θ hzI hθI
        rwa [abs_mul, abs_of_pos (pow_pos hz1 k)] at h
      calc |z ^ k * Work.Spaces.pzIter k A z θ|
          = z ^ k * |Work.Spaces.pzIter k A z θ| := by
            rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 k)]
        _ ≤ (z + 1) ^ k * |Work.Spaces.pzIter k A z θ| :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 (by linarith) k) (abs_nonneg _)
        _ ≤ Work.Spaces.WlInf α 6 A := h2
    have hsum := abs_sum_scoef_le_six (h := A) (z := z) (θ := θ)
      (M := Work.Spaces.WlInf α 6 A) hj6 hWnn hx
    have hexp := Work.FTS.EllipticEst.Cores.DiagEstEllT.DzIter_eq_sum_scoef_diffOn
      (h := A) (θ := θ) (U := Set.Ioi 0) (n := j) isOpen_Ioi hd z hz
    rw [Work.Spaces.mixed_zero_right, hexp]
    refine hsum.trans (le_of_eq ?_)
    rw [Abnd_zero]
    ring
  · -- at least one angular derivative
    have hi1 : 1 ≤ i := hipos
    have hi0 : ¬ i = 0 := by omega
    have hj6 : j ≤ 6 := by omega
    have hd : ∀ k ≤ j,
        DifferentiableOn ℝ
          (fun y : ℝ => Work.Spaces.pzIter k (Work.Spaces.DthIter i A) y θ) (Set.Ioi 0) :=
      fun k _ => (((hA.DthIter i).pzIter k).curry_z hθIoo).differentiableOn (by simp)
    have hXnn : 0 ≤ Xfac α θ := Xfac_nonneg hα hs0
    have hx : ∀ k ≤ j,
        |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i A) z θ|
          ≤ Work.Spaces.WlInf α 6 A * Xfac α θ := by
      intro k hk
      have hki : k + i ≤ 6 := by omega
      have hb := Work.Spaces.pz_Dth_sup_bound α hα 6 A hmem i k hi1 hki z θ hzI hθI
      have hzk : 0 ≤ z ^ k := pow_nonneg hz0 k
      have hz1k : 0 < (z + 1) ^ k := pow_pos hz1 k
      have hq : z ^ k / (z + 1) ^ k ≤ 1 :=
        div_le_one_of_le₀ (pow_le_pow_left₀ hz0 (by linarith) k) (le_of_lt hz1k)
      calc |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i A) z θ|
          = z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i A) z θ| := by
            rw [abs_mul, abs_of_nonneg hzk]
        _ ≤ z ^ k * (Work.Spaces.WlInf α 6 A / (z + 1) ^ k * Xfac α θ) :=
            mul_le_mul_of_nonneg_left hb hzk
        _ = (z ^ k / (z + 1) ^ k) * (Work.Spaces.WlInf α 6 A * Xfac α θ) := by ring
        _ ≤ 1 * (Work.Spaces.WlInf α 6 A * Xfac α θ) :=
            mul_le_mul_of_nonneg_right hq (mul_nonneg hWnn hXnn)
        _ = Work.Spaces.WlInf α 6 A * Xfac α θ := one_mul _
    have hsum := abs_sum_scoef_le_six (h := Work.Spaces.DthIter i A) (z := z) (θ := θ)
      (M := Work.Spaces.WlInf α 6 A * Xfac α θ) hj6 (mul_nonneg hWnn hXnn) hx
    have hexp := Work.FTS.EllipticEst.Cores.DiagEstEllT.DzIter_eq_sum_scoef_diffOn
      (h := Work.Spaces.DthIter i A) (θ := θ) (U := Set.Ioi 0) (n := j) isOpen_Ioi hd z hz
    change |Work.Spaces.DzIter j (Work.Spaces.DthIter i A) z θ|
      ≤ 203 * Work.Spaces.WlInf α 6 A * Abnd α i θ
    rw [hexp]
    refine hsum.trans (le_of_eq ?_)
    rw [Abnd_of_ne_zero hi0]
    ring

theorem T45AslotLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (A : ℝ → ℝ → ℝ) (K : ℝ),
    Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
    Work.Spaces.WlInf α 6 A ≤ K →
    ∀ (j i : ℕ), i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i A z θ|
        ≤ C * K * Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ := by
  refine ⟨203, by norm_num, ?_⟩
  intro α hα A K hA hmem hWK j i hij z θ hz hθ0 hθ1
  have hbase := mixed_le_WlInf α hα.1 A hA hmem j i hij z θ hz hθ0 hθ1
  have hAnn : 0 ≤ Abnd α i θ := Abnd_nonneg hα.1 ⟨le_of_lt hθ0, le_of_lt hθ1⟩ i
  calc |Work.Spaces.mixed j i A z θ|
      ≤ 203 * Work.Spaces.WlInf α 6 A * Abnd α i θ := hbase
    _ ≤ 203 * K * Abnd α i θ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWK (by norm_num)) hAnn

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
