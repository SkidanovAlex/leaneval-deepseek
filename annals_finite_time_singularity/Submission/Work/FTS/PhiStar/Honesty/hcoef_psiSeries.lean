/-
# `Work.FTS.PhiStar.Honesty.hcoef_psiSeries` — the weighted `ℓ¹`-summability of the modal
coefficients of `psiSeries`

For a source `F` which is `C^∞` on the open quadrant and honest at level `0`
(`Work.Spaces.HkMem α 0 F`), the modal coefficients of the series solution
`psiSeries α F = Σ_m acoeff α m F z · e_m(θ)` of `bslOp α Ψ = F` satisfy

  `Σ_m (m+1)·|acoeff α m F z| < ∞`   for every `z > 0`.

This is the `hcoef` input of the level-`0` honesty capstones
(`Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone`,
`Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero`).

## Route

Write `c_m := cmode m F` and `a_m := acoeff α m F = radGreen α m c_m`.  Two ingredients:

* the *sharp modal Green bound* `Work.EllipticEst.ModalSolution.radGreen_abs_le`
  (`m ≥ 1`, `z > 0`, `c` with `∫ c² < ∞`):

    `|a_m(z)| ≤ √(∫_0^∞ c_m²) · z ^ (-1/2) / (α (4m+5) √m)`;

* the *integrated Bessel inequality* `Work.FTS.ClassC.sum_eNorm_cmode_sq_le_HkSq`,
  which says that the total weighted energy of the mode coefficients is dominated by the
  source's `ℋ⁰`-norm,

    `∑_{m ≤ N} eNorm m · ∫_0^∞ (c_m w)² ≤ HkSq α 0 F`,

  and hence, since `w ≥ 1` and `m ≤ eNorm m` (`CmpSupp.eNorm_bounds`), that

    `∑_m eNorm m · ∫_0^∞ c_m² ≤ HkSq α 0 F`.

Since `(m+1)/(4m+5) ≤ 1/4`, the Green bound gives
`(m+1)|a_m(z)| ≤ (4α√z)⁻¹ · ‖c_m‖₂/√m` for `m ≥ 1`; the Cauchy–Schwarz inequality

  `∑_m ‖c_m‖₂/√m ≤ (∑_m eNorm m ‖c_m‖₂²)^{1/2} · (∑_m 1/(m · eNorm m))^{1/2}`

(with the second factor `≤ (∑_m 1/m²)^{1/2} < ∞`) then gives the summability.  The single
`m = 0` term is a finite real number and does not affect summability, which is why no source
moment condition is needed.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.BmodeCoeff
import Submission.Work.EllipticEst.ModalSolution.radGreen_abs_le
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem
import Submission.Work.FTS.ClassC.bessel_z
import Submission.Work.FTS.ClassCHon.CmpSupp.eNorm_bounds
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.FTS.ClassCHon.Hcoef.cmode_L2_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- The radial weight is at least `1` on the open half-line: `(1+t)²/z² ≥ 1`. -/
private lemma one_le_w {t : ℝ} (ht : 0 < t) : 1 ≤ Work.Spaces.w t := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- `z ^ (-1/2) = 1/√z` for `z > 0`. -/
private lemma rpow_neg_half_eq {z : ℝ} (hz : 0 < z) : z ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt z := by
  simp [Real.rpow_neg (le_of_lt hz), Real.sqrt_eq_rpow]

/-- The elementary arithmetic of the modal bound: the factor `(m+1)/(4m+5) ≤ 1/4` converts the
Green bound `√(∫c²)·z^(-1/2)/(α(4m+5)√m)` into `√(∫c²)/(4α√z√m)`. -/
private lemma modal_arith {α u z : ℝ} (hα : 0 < α) (hz : 0 < z) (hu : 0 ≤ u)
    {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * (u * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt m))
      ≤ u / (4 * α * Real.sqrt z * Real.sqrt m) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos (by linarith)
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos_of_pos hz
  have hstep : ((m : ℝ) + 1) * (u * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt m))
      = (((m : ℝ) + 1) / (4 * (m : ℝ) + 5)) * (u / (α * Real.sqrt m * Real.sqrt z)) := by
    rw [rpow_neg_half_eq hz]
    field_simp
  rw [hstep]
  have h2 : ((m : ℝ) + 1) / (4 * (m : ℝ) + 5) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
    linarith
  have h3 : 0 ≤ u / (α * Real.sqrt m * Real.sqrt z) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_right h2 h3) ?_
  rw [one_div]
  field_simp
  linarith

/-! ## The theorem -/

theorem hcoef_psiSeries {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F) :
    ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|) := by
  intro z hz
  -- ## the slice integrability facts required by the integrated Bessel inequality
  have hintc : ∀ t ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ : ℝ => (F t θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    fun t ht => integrableOn_sq_cos_of_HkMem hF ht
  have hints : ∀ t ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ : ℝ => (F t θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    fun t ht => integrableOn_sq_sEta_of_HkMem hF ht
  -- ## the mode energy of a fixed mode is a nonnegative integral
  have hAnn : ∀ m : ℕ, 0 ≤ ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 := by
    intro m
    refine integral_nonneg_of_ae ?_
    filter_upwards with t
    exact sq_nonneg _
  -- ## per-mode integrability of the weighted and unweighted squares of the mode coefficients
  have hWint : ∀ m : ℕ, IntegrableOn
      (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2) (Set.Ioi 0) :=
    fun m => (Work.FTS.ClassCHon.Hcoef.cmode_L2_bound hsm hF m).1
  have hCint : ∀ m : ℕ, IntegrableOn
      (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 0) := by
    intro m
    refine (hWint m).mono' ((Work.EllipticEst.ModalSolution.aesm_cmode hsm m).pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw2 : 1 ≤ (Work.Spaces.w t) ^ 2 := by
      have := one_le_w ht
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Work.FTS.PhiStar.Series.cmode m F t) ^ 2
        = (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
      _ = (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2 := by ring
  have hWint' : ∀ m : ℕ, IntegrableOn
      (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0) := fun m =>
    (hWint m).congr_fun (fun t _ => by ring) measurableSet_Ioi
  -- ## the integrated Bessel inequality, with the two weights compared
  have hMaster : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1),
        Work.EllipticEst.ModalSolution.eNorm m *
          (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
      ≤ Work.Spaces.HkSq α 0 F := by
    intro N
    refine le_trans (Finset.sum_le_sum ?_)
      (Work.FTS.ClassC.sum_eNorm_cmode_sq_le_HkSq α F N hsm hF hintc hints)
    intro m _
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m))
    refine setIntegral_mono_on (hCint m) (hWint' m) measurableSet_Ioi ?_
    intro t ht
    have hw2 : 1 ≤ (Work.Spaces.w t) ^ 2 := by
      have := one_le_w ht
      nlinarith
    calc (Work.FTS.PhiStar.Series.cmode m F t) ^ 2
        = (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
  -- ## `HkSq α 0 F` is nonnegative
  have hHkSq_nn : 0 ≤ Work.Spaces.HkSq α 0 F := by
    refine integral_nonneg_of_ae ?_
    filter_upwards with t
    refine integral_nonneg_of_ae ?_
    filter_upwards with θ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α F t θ]
    exact sq_nonneg _
  -- ## summability of the `eNorm`-weighted mode energy
  have hSumE : Summable (fun m : ℕ => Work.EllipticEst.ModalSolution.eNorm m *
      (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)) := by
    refine summable_of_sum_range_le
      (f := fun m : ℕ => Work.EllipticEst.ModalSolution.eNorm m *
        (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2))
      (c := Work.Spaces.HkSq α 0 F) (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos n)) (hAnn n)
    · rcases n with _ | k
      · rw [Finset.range_zero, Finset.sum_empty]
        exact hHkSq_nn
      · simpa using hMaster k
  -- ## shift to `m = n + 1`, so that `1 ≤ m` throughout
  set En : ℕ → ℝ := fun n => Work.EllipticEst.ModalSolution.eNorm (n + 1) with hEndef
  set U : ℕ → ℝ := fun n =>
    Real.sqrt (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode (n + 1) F t) ^ 2) with hUdef
  have hUn : ∀ n : ℕ, U n = Real.sqrt (∫ t in Set.Ioi 0,
      (Work.FTS.PhiStar.Series.cmode (n + 1) F t) ^ 2) := fun n => congrFun hUdef n
  have hEn : ∀ n : ℕ, En n = Work.EllipticEst.ModalSolution.eNorm (n + 1) :=
    fun n => congrFun hEndef n
  have hUnn : ∀ n : ℕ, 0 ≤ U n := by
    intro n
    rw [hUn n]
    exact Real.sqrt_nonneg _
  have hEpos : ∀ n : ℕ, 0 < En n := by
    intro n
    rw [hEn n]
    exact Work.EllipticEst.ModalSolution.eNorm_pos (n + 1)
  have hEge : ∀ n : ℕ, (n : ℝ) + 1 ≤ En n := by
    intro n
    have h := (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds (n + 1)).2
    rw [hEn n]
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hUsq : ∀ n : ℕ, (U n) ^ 2 = ∫ t in Set.Ioi 0,
      (Work.FTS.PhiStar.Series.cmode (n + 1) F t) ^ 2 := by
    intro n
    rw [hUn n]
    exact Real.sq_sqrt (hAnn (n + 1))
  -- ## the shifted `eNorm`-weighted energy is summable
  have hAsum : Summable (fun n : ℕ => En n * (U n) ^ 2) := by
    refine ((summable_nat_add_iff (f := fun m : ℕ => Work.EllipticEst.ModalSolution.eNorm m *
      (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)) 1).mpr hSumE).congr
      (fun n => ?_)
    rw [hEn n, hUsq n]
  -- ## the `1/(m·eNorm m)`-weighted sum is summable
  have hBsum : Summable (fun n : ℕ =>
      (1 / (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1))) ^ 2) := by
    have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have h1 := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).mpr h0
      simpa only [Nat.cast_add, Nat.cast_one] using h1
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
    · positivity
    · have hEnn : 0 < En n := hEpos n
      have hs : Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1)
          = Real.sqrt (En n * ((n : ℝ) + 1)) :=
        (Real.sqrt_mul (le_of_lt hEnn) _).symm
      have hsq : (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1)) ^ 2
          = En n * ((n : ℝ) + 1) := by
        rw [hs, Real.sq_sqrt (by positivity)]
      have hle : ((n : ℝ) + 1) ^ 2 ≤ En n * ((n : ℝ) + 1) := by
        nlinarith [hEge n]
      rw [div_pow, one_pow, hsq]
      exact one_div_le_one_div_of_le (by positivity) hle
  -- ## the two factors whose product is `U n/√(n+1)`
  have ha2 : Summable (fun n : ℕ => (Real.sqrt (En n) * U n) ^ 2) := by
    refine hAsum.congr (fun n => ?_)
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hEpos n)), hUsq n]
  have hAB : Summable (fun n : ℕ => (1 / 2) * (Real.sqrt (En n) * U n) ^ 2
      + (1 / 2) * (1 / (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1))) ^ 2) :=
    (ha2.mul_left (1 / 2)).add (hBsum.mul_left (1 / 2))
  -- ## Cauchy–Schwarz over the modes
  have hCSsum : Summable (fun n : ℕ => U n / Real.sqrt ((n : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hAB
    · positivity
    · have hEnpos : 0 < Real.sqrt (En n) := Real.sqrt_pos_of_pos (hEpos n)
      have hid : (Real.sqrt (En n) * U n) * (1 / (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1)))
          = U n / Real.sqrt ((n : ℝ) + 1) := by
        rw [mul_one_div, mul_div_mul_left _ _ (ne_of_gt hEnpos)]
      rw [← hid]
      have hAM := two_mul_le_add_sq (Real.sqrt (En n) * U n)
        (1 / (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1)))
      linarith
  -- ## the modal bound for the shifted family
  have hkey : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α (n + 1) F z|) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => (1 / (4 * α * Real.sqrt z)) * (U n / Real.sqrt ((n : ℝ) + 1)))
      (hCSsum.mul_left (1 / (4 * α * Real.sqrt z))) (fun n => ?_)
    have hgreen := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα (by linarith) (n + 1)
      (Nat.le_add_left 1 n)
      (c := fun t => Work.FTS.PhiStar.Series.cmode (n + 1) F t) (hCint (n + 1)) hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : |Work.FTS.PhiStar.Series.acoeff α (n + 1) F z| ≤ U n * z ^ (-(1 / 2) : ℝ)
        / (α * (4 * (((n + 1 : ℕ) : ℝ)) + 5) * Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
      have hg := hgreen
      rw [← hUn n] at hg
      simpa only [Work.FTS.PhiStar.Series.acoeff] using hg
    calc ((((n + 1 : ℕ) : ℝ)) + 1) * |Work.FTS.PhiStar.Series.acoeff α (n + 1) F z|
        ≤ ((((n + 1 : ℕ) : ℝ)) + 1) * (U n * z ^ (-(1 / 2) : ℝ)
            / (α * (4 * (((n + 1 : ℕ) : ℝ)) + 5)
              * Real.sqrt (((n + 1 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ U n / (4 * α * Real.sqrt z * Real.sqrt (((n + 1 : ℕ) : ℝ))) :=
          modal_arith hα hz (hUnn n) (Nat.le_add_left 1 n)
      _ = (1 / (4 * α * Real.sqrt z)) * (U n / Real.sqrt ((n : ℝ) + 1)) := by
          push_cast
          ring
  exact (summable_nat_add_iff (f := fun m : ℕ =>
    ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|) 1).mp hkey

end Work.FTS.PhiStar.Honesty
