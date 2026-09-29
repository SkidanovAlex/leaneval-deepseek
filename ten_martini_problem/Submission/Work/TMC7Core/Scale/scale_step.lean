import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Lyap.subadditive_integral_log_frob
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMC7Core.Scale.frob_tmC_le
import Submission.Work.TMC7Core.Scale.volume_fract_shift
import Submission.Work.TMC7Core.Scale.avalanche_weak

set_option maxHeartbeats 8000000

namespace Work.TMC7Core.Scale

open MeasureTheory Filter Topology Set
open Classical
open Work.TMC7Core
open Work.TMC7Core.Lyap
open LeanEval.Analysis.TenMartini

noncomputable section

/-! ## Auxiliary: `iterC` is periodic with period `1`, hence invariant under integer shifts -/

theorem iterC_int_periodic (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) (k : ℤ) :
    iterC α lam E n (x + (k : ℝ)) = iterC α lam E n x := by
  have hper : Function.Periodic (fun y : ℝ => iterC α lam E n y) 1 := fun y => iterC_periodic α lam E n y
  have h := hper.zsmul k
  simp only [zsmul_eq_mul, mul_one] at h
  exact h x

/-- `log ‖A_M(x)‖_F = M * uAvg M x` for `M ≥ 1`. -/
theorem log_frob_eq_mul_uAvg (α lam : ℝ) (E : ℂ) {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    Real.log (frob (iterC α lam E M x)) = (M : ℝ) * uAvg α lam E M x := by
  rw [uAvg]
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  field_simp

/-- `uAvg` is nonnegative for `M ≥ 1`. -/
theorem uAvg_nonneg' (α lam : ℝ) (E : ℂ) {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    0 ≤ uAvg α lam E M x := by
  rw [uAvg]
  apply div_nonneg
  · exact Real.log_nonneg (by
      have := Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam E M x)
      linarith [Real.one_lt_sqrt_two])
  · positivity

/-- `log ‖A_M(x)‖_F ≥ 0`. -/
theorem log_frob_iterC_nonneg' (α lam : ℝ) (E : ℂ) (M : ℕ) (x : ℝ) :
    0 ≤ Real.log (frob (iterC α lam E M x)) := by
  apply Real.log_nonneg
  have := Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam E M x)
  linarith [Real.one_lt_sqrt_two]

/-! ## The blocks of the scale chain -/

/-- The `j`-th block of the scale chain: `A_j = A_N(x + j N α)`. -/
def block (α lam : ℝ) (E : ℂ) (N : ℕ) (x : ℝ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  iterC α lam E N (x + (j : ℝ) * ((N : ℝ) * α))

/-- `matProd` of `m` blocks of length `N` is the iterate of length `m * N`. -/
theorem matProd_block (α lam : ℝ) (E : ℂ) (N m : ℕ) (x : ℝ) :
    matProd (block α lam E N x) m = iterC α lam E (m * N) x := by
  induction m with
  | zero => simp [matProd_zero, iterC_zero]
  | succ m ih =>
    rw [matProd_succ, ih, block]
    have h1 : x + ((m : ℕ) : ℝ) * ((N : ℝ) * α) = x + ((m * N : ℕ) : ℝ) * α := by
      push_cast; ring
    rw [h1, ← iterC_add]
    congr 1
    ring

/-- The product of two consecutive blocks is the `2N`-iterate at the shifted phase. -/
theorem block_mul (α lam : ℝ) (E : ℂ) (N j : ℕ) (x : ℝ) :
    block α lam E N x (j + 1) * block α lam E N x j = iterC α lam E (2 * N) (x + (j : ℝ) * ((N : ℝ) * α)) := by
  rw [block, block]
  have h1 : x + ((j + 1 : ℕ) : ℝ) * ((N : ℝ) * α) = (x + (j : ℝ) * ((N : ℝ) * α)) + (N : ℝ) * α := by
    push_cast; ring
  rw [h1, ← iterC_add]
  congr 1
  ring

/-- `uAvg` is invariant under integer shifts. -/
theorem uAvg_int_shift (α lam : ℝ) (E : ℂ) (M : ℕ) (y : ℝ) (k : ℤ) :
    uAvg α lam E M (y + (k : ℝ)) = uAvg α lam E M y := by
  simp only [uAvg, iterC_int_periodic α lam E M y k]

/-- `matProd` depends only on the first `m` terms. -/
theorem matProd_congr {A B : ℕ → Matrix (Fin 2) (Fin 2) ℂ} {m : ℕ} (h : ∀ j < m, A j = B j) :
    matProd A m = matProd B m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [matProd_succ, matProd_succ, h m (by omega), ih (fun j hj => h j (by omega))]

/-- `uAvg` at the fractional part. -/
theorem uAvg_fract (α lam : ℝ) (E : ℂ) (M : ℕ) (z : ℝ) :
    uAvg α lam E M z = uAvg α lam E M (Int.fract z) := by
  conv_lhs => rw [← Int.fract_add_floor z]
  exact uAvg_int_shift α lam E M (Int.fract z) ⌊z⌋

/-! ## The integrated quantity of the scale chain -/

/-- The pointwise quantity whose integral, divided by `m * N`, is the left-hand side of
`scale_step`: `log‖A_{mN}(x)‖ + Σ_{j=1}^{m-2} log‖A_j‖ - Σ_{j=0}^{m-2} log‖A_{j+1}A_j‖`. -/
def Ffun (α lam : ℝ) (E : ℂ) (N m : ℕ) (x : ℝ) : ℝ :=
  Real.log (frob (iterC α lam E (m * N) x))
    + ∑ j ∈ Finset.Icc 1 (m - 2), Real.log (frob (block α lam E N x j))
    - ∑ j ∈ Finset.range (m - 1),
        Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j))

/-- Integral of one block term. -/
theorem integral_block (α lam : ℝ) (E : ℂ) {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    (∫ x in (0:ℝ)..1, Real.log (frob (block α lam E N x j))) = (N:ℝ) * lyapAvg α lam E N := by
  have hNne : ((N:ℝ)) ≠ 0 := by positivity
  have hsh := log_frob_integral_shift α lam E N ((j:ℝ) * ((N:ℝ) * α))
  simp only [block] at hsh ⊢
  rw [hsh, lyapAvg, mul_div_cancel₀ _ hNne]

/-- Integral of one pair term. -/
theorem integral_pair (α lam : ℝ) (E : ℂ) {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    (∫ x in (0:ℝ)..1, Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j)))
      = (((2 * N : ℕ)) : ℝ) * lyapAvg α lam E (2 * N) := by
  have h2Nne : ((((2 * N : ℕ)) : ℝ)) ≠ 0 := by positivity
  have heq : (fun x : ℝ => Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j)))
      = fun x : ℝ => Real.log (frob (iterC α lam E (2 * N) (x + (j:ℝ) * ((N:ℝ) * α)))) := by
    funext x; rw [block_mul]
  rw [heq, log_frob_integral_shift α lam E (2 * N) ((j:ℝ) * ((N:ℝ) * α)), lyapAvg,
    mul_div_cancel₀ _ h2Nne]

/-- **Integral identity.**  Averaging `Ffun` over a period gives
`m N L_{mN} + (m-2) N L_N - 2(m-1) N L_{2N}`. -/
theorem integral_Ffun (α lam : ℝ) (E : ℂ) (N m : ℕ) (hN : 1 ≤ N) (hm : 2 ≤ m) :
    (∫ x in (0:ℝ)..1, Ffun α lam E N m x)
      = ((m : ℝ) * N) * lyapAvg α lam E (m * N) + (((m : ℝ) - 2) * N) * lyapAvg α lam E N
        - (2 * ((m : ℝ) - 1) * N) * lyapAvg α lam E (2 * N) := by
  have hmNne : (((m * N : ℕ)) : ℝ) ≠ 0 := by
    have : 1 ≤ m * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    positivity
  have hci : ∀ j ∈ Finset.Icc 1 (m - 2),
      IntervalIntegrable (fun x : ℝ => Real.log (frob (block α lam E N x j))) volume (0:ℝ) 1 := by
    intro j _
    exact ((continuous_log_frob_iterC α lam E N).comp
      (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hcp : ∀ j ∈ Finset.range (m - 1),
      IntervalIntegrable (fun x : ℝ => Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j)))
        volume (0:ℝ) 1 := by
    intro j _
    have heq : (fun x : ℝ => Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j)))
        = fun x : ℝ => Real.log (frob (iterC α lam E (2 * N) (x + (j:ℝ) * ((N:ℝ) * α)))) := by
      funext x; rw [block_mul]
    rw [heq]
    exact ((continuous_log_frob_iterC α lam E (2 * N)).comp
      (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hAi : IntervalIntegrable (fun x : ℝ => Real.log (frob (iterC α lam E (m * N) x)))
      volume (0:ℝ) 1 := (continuous_log_frob_iterC α lam E (m * N)).intervalIntegrable _ _
  have hG1i : IntervalIntegrable
      (fun x : ℝ => ∑ j ∈ Finset.Icc 1 (m - 2), Real.log (frob (block α lam E N x j)))
      volume (0:ℝ) 1 := by
    have hfun : (∑ j ∈ Finset.Icc 1 (m - 2), fun x : ℝ => Real.log (frob (block α lam E N x j)))
        = fun x : ℝ => ∑ j ∈ Finset.Icc 1 (m - 2), Real.log (frob (block α lam E N x j)) := by
      funext x; rw [Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum (Finset.Icc 1 (m - 2)) hci
  have hG2i : IntervalIntegrable
      (fun x : ℝ => ∑ j ∈ Finset.range (m - 1),
        Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j)))
      volume (0:ℝ) 1 := by
    have hfun : (∑ j ∈ Finset.range (m - 1),
          fun x : ℝ => Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j)))
        = fun x : ℝ => ∑ j ∈ Finset.range (m - 1),
            Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j)) := by
      funext x; rw [Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum (Finset.range (m - 1)) hcp
  simp only [Ffun]
  rw [intervalIntegral.integral_sub (hAi.add hG1i) hG2i, intervalIntegral.integral_add hAi hG1i]
  rw [intervalIntegral.integral_finsetSum (s := Finset.Icc 1 (m - 2))
        (f := fun j x => Real.log (frob (block α lam E N x j))) hci]
  rw [intervalIntegral.integral_finsetSum (s := Finset.range (m - 1))
        (f := fun j x => Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j))) hcp]
  have h1 : (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E (m * N) x)))
      = (((m * N : ℕ)) : ℝ) * lyapAvg α lam E (m * N) := by
    rw [lyapAvg, mul_div_cancel₀ _ hmNne]
  rw [h1]
  have h2 : ∀ j ∈ Finset.Icc 1 (m - 2),
      (∫ x in (0:ℝ)..1, Real.log (frob (block α lam E N x j))) = (N:ℝ) * lyapAvg α lam E N :=
    fun j _ => integral_block α lam E hN j
  have h3 : ∀ j ∈ Finset.range (m - 1),
      (∫ x in (0:ℝ)..1, Real.log (frob (block α lam E N x (j + 1) * block α lam E N x j)))
        = (((2 * N : ℕ)) : ℝ) * lyapAvg α lam E (2 * N) :=
    fun j _ => integral_pair α lam E hN j
  rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl h3]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_range]
  have hcard1 : ((Finset.Icc 1 (m - 2)).card) = m - 2 := by simp
  rw [hcard1]
  have hcast : (((m - 2 : ℕ)) : ℝ) = (m:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]; norm_num
  have hcast1 : (((m - 1 : ℕ)) : ℝ) = (m:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
  have hmNcast : (((m * N : ℕ)) : ℝ) = (m:ℝ) * (N:ℝ) := by push_cast; ring
  have h2Ncast : ((((2 * N : ℕ)) : ℝ)) = 2 * (N:ℝ) := by push_cast; ring
  simp only [nsmul_eq_mul, hcast, hcast1, hmNcast, h2Ncast]
  ring

/-! ## Generic measure-theoretic helpers -/

/-- The integral over `[0,1]` of the indicator of a measurable set equals the measure of its
trace on `(0,1]`. -/
theorem integral_indicator_eq (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ x in (0:ℝ)..1, s.indicator (fun _ => (1:ℝ)) x) = (volume (s ∩ Set.Ioc (0:ℝ) 1)).toReal := by
  classical
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [← MeasureTheory.integral_indicator (s := Set.Ioc (0:ℝ) 1) measurableSet_Ioc]
  have hcomp : (Set.Ioc (0:ℝ) 1).indicator (s.indicator (fun _ => (1:ℝ)))
      = (s ∩ Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) := by
    funext x
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    by_cases h1 : x ∈ s <;> by_cases h2 : x ∈ Set.Ioc (0:ℝ) 1 <;> simp [h1, h2, Set.mem_inter_iff]
  rw [hcomp]
  exact MeasureTheory.integral_indicator_one (hs.inter measurableSet_Ioc)

/-- The indicator of a measurable set is interval integrable. -/
theorem intervalIntegrable_indicator (s : Set ℝ) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator (fun _ => (1:ℝ))) volume (0:ℝ) 1 := by
  classical
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ ?_ 1 ?_
  · rw [Real.volume_uIoc]; norm_num
  · exact (measurable_const.indicator hs).aestronglyMeasurable
  · filter_upwards with x
    rw [Set.indicator_apply, Real.norm_eq_abs]
    by_cases h : x ∈ s <;> simp [h]

/-- The "bad set" of the scale chain is measurable. -/
theorem measurableSet_bad (B₁ B₂ : Set ℝ) (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂)
    (m N : ℕ) (α : ℝ) :
    MeasurableSet {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧
      ((∃ j ∈ Finset.range m, Int.fract (x + (j:ℝ) * ((N:ℝ)*α)) ∈ B₁) ∨
       (∃ j ∈ Finset.range (m-1), Int.fract (x + (j:ℝ) * ((N:ℝ)*α)) ∈ B₂))} := by
  classical
  have h1 : {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧
      ((∃ j ∈ Finset.range m, Int.fract (x + (j:ℝ) * ((N:ℝ)*α)) ∈ B₁) ∨
       (∃ j ∈ Finset.range (m-1), Int.fract (x + (j:ℝ) * ((N:ℝ)*α)) ∈ B₂))}
      = (Set.Icc (0:ℝ) 1) ∩
        ((⋃ j ∈ Finset.range m, {x : ℝ | Int.fract (x + (j:ℝ) * ((N:ℝ)*α)) ∈ B₁}) ∪
         (⋃ j ∈ Finset.range (m-1), {x : ℝ | Int.fract (x + (j:ℝ) * ((N:ℝ)*α)) ∈ B₂})) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, exists_prop, Set.mem_union]
  rw [h1]
  refine measurableSet_Icc.inter (MeasurableSet.union ?_ ?_)
  · exact MeasurableSet.biUnion (Finset.countable_toSet _) (fun j _ =>
      h₁.preimage ((measurable_fract.comp (measurable_id.add measurable_const))))
  · exact MeasurableSet.biUnion (Finset.countable_toSet _) (fun j _ =>
      h₂.preimage ((measurable_fract.comp (measurable_id.add measurable_const))))

/-- **Avila–Jitomirskaya, [BJ] Lemma 6 (one scale step).** -/
theorem scale_step (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ) (hLDT : HasLDTOn lam K c C) (hC₀ : HasLEBound lam K C₀) (hc1 : c ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100) (E : ℝ) (hE : E ∈ K) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs a) q) (hqC : C * (κ ^ 2)⁻¹ ≤ (q : ℝ)) (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) (N : ℕ) (hN : C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N : ℝ)) (hL : 100 * κ < lyap α lam (E : ℂ)) (h2N : (9 / 10) * lyapAvg α lam (E : ℂ) N < lyapAvg α lam (E : ℂ) (2 * N)) (m : ℕ) (hm : 3 ≤ m) (hmq : (m : ℝ) < Real.exp (c * κ * (q : ℝ) / 2)) : |lyapAvg α lam (E : ℂ) (m * N) + (1 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N - (2 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N)| < (12 * C₀ + 1000) * Real.exp (-(c * κ * (q : ℝ) / 4)) := by
  -- ============ 0. elementary setup ============
  have hc : 0 < c := hLDT.1
  have hC : 1 ≤ C := hLDT.2.1
  have hLDTa := hLDT.2.2
  have hC0 : 0 < C₀ := hC₀.1
  have hLEB := hC₀.2
  have hκ1' : κ ≤ 1 := by linarith
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hκ2le : κ^2 ≤ (1/100:ℝ)^2 := pow_le_pow_left₀ hκ.le hκ1 2
  have hκinv : (10:ℝ)^4 ≤ (κ^2)⁻¹ := by
    have hpos : (0:ℝ) < κ^2 := by positivity
    rw [le_inv_comm₀ (by norm_num : (0:ℝ) < (10:ℝ)^4) hpos]
    have h10 : (((10:ℝ)^4))⁻¹ = (1/100:ℝ)^2 := by norm_num
    rw [h10]
    exact hκ2le
  have hκinv100 : (100:ℝ) ≤ κ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 100) hκ]
    linarith
  have hNk : (κ^2)⁻¹ * (q:ℝ) ≤ (N:ℝ) := by
    have h1 : C * (κ^2)⁻¹ * (q:ℝ) = C * ((κ^2)⁻¹ * (q:ℝ)) := by ring
    rw [h1] at hN
    have h2 : (1:ℝ) * ((κ^2)⁻¹ * (q:ℝ)) ≤ C * ((κ^2)⁻¹ * (q:ℝ)) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    linarith
  have hN1 : 1 ≤ N := by
    have h2 : (1:ℝ) ≤ (κ^2)⁻¹ * (q:ℝ) := by
      have h3 := mul_le_mul hκinv hq1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (κ^2)⁻¹)
      nlinarith [h3]
    have : (1:ℝ) ≤ (N:ℝ) := le_trans h2 hNk
    exact_mod_cast this
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hLN : 100 * κ < lyapAvg α lam (E:ℂ) N := lt_of_lt_of_le hL (lyap_le_lyapAvg α lam (E:ℂ) hN1)
  have hm2 : 2 ≤ m := by omega
  have hmN1 : 1 ≤ m * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hmNpos : (0:ℝ) < ((m*N:ℕ):ℝ) := by positivity
  -- ============ 1. notation ============
  set LN := lyapAvg α lam (E:ℂ) N with hLNdef
  set L2N := lyapAvg α lam (E:ℂ) (2*N) with hL2Ndef
  set LmN := lyapAvg α lam (E:ℂ) (m*N) with hLmNdef
  set μ := Real.exp ((N:ℝ) * (LN - κ)) with hμdef
  have hμpos : 0 < μ := Real.exp_pos _
  have hsqμpos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμpos
  have hlogμ : Real.log μ = (N:ℝ) * (LN - κ) := Real.log_exp _
  -- ============ 2. the exponent scales ============
  have hNLN : (9900:ℝ) ≤ (N:ℝ) * (LN - κ) := by
    have hLNk : 99 * κ ≤ LN - κ := by linarith
    have h1 : (κ^2)⁻¹ * (q:ℝ) * (99*κ) ≤ (N:ℝ) * (LN - κ) :=
      mul_le_mul hNk hLNk (by positivity) (by positivity)
    have hk : (κ^2)⁻¹ * κ = κ⁻¹ := by
      have hne : κ ≠ 0 := ne_of_gt hκ
      field_simp
    have h2 : (9900:ℝ) ≤ (κ^2)⁻¹ * (q:ℝ) * (99*κ) := by
      have heq : (κ^2)⁻¹ * (q:ℝ) * (99*κ) = 99 * (q:ℝ) * ((κ^2)⁻¹ * κ) := by ring
      rw [heq, hk]
      nlinarith [hκinv100, hq1]
    linarith
  have hμbig : (10:ℝ)^6 ≤ μ := by
    rw [hμdef]
    refine (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < (10:ℝ)^6)).mp ?_
    have hlog6 : Real.log ((10:ℝ)^6) ≤ 9900 := by
      have h9 : Real.log 10 ≤ 9 := by
        linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 10 by norm_num)]
      have hpow : Real.log ((10:ℝ)^6) = 6 * Real.log 10 := by
        rw [Real.log_pow]; push_cast; ring
      rw [hpow]; linarith
    linarith [hlog6, hNLN]
  have hμsq : (1000:ℝ) ≤ Real.sqrt μ := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hμpos)]
    nlinarith [hμbig]
  -- ============ 3. the bad sets ============
  set B₁ : Set ℝ := {y : ℝ | y ∈ Set.Icc (0:ℝ) 1 ∧ κ < |uAvg α lam (E:ℂ) N y - LN|} with hB1def
  set B₂ : Set ℝ := {y : ℝ | y ∈ Set.Icc (0:ℝ) 1 ∧ κ < |uAvg α lam (E:ℂ) (2*N) y - L2N|} with hB2def
  have hB₁sub : B₁ ⊆ Set.Icc (0:ℝ) 1 := fun y hy => hy.1
  have hB₂sub : B₂ ⊆ Set.Icc (0:ℝ) 1 := fun y hy => hy.1
  have huN_cont : Continuous (fun y : ℝ => uAvg α lam (E:ℂ) N y) := by
    simp only [uAvg]
    exact (continuous_log_frob_iterC α lam (E:ℂ) N).div_const _
  have hu2N_cont : Continuous (fun y : ℝ => uAvg α lam (E:ℂ) (2*N) y) := by
    simp only [uAvg]
    exact (continuous_log_frob_iterC α lam (E:ℂ) (2*N)).div_const _
  have hB₁meas : MeasurableSet B₁ := by
    rw [hB1def]
    exact measurableSet_Icc.inter (isOpen_Ioi.preimage ((huN_cont.sub continuous_const).abs)).measurableSet
  have hB₂meas : MeasurableSet B₂ := by
    rw [hB2def]
    exact measurableSet_Icc.inter (isOpen_Ioi.preimage ((hu2N_cont.sub continuous_const).abs)).measurableSet
  have hvolB₁ : volume B₁ ≤ ENNReal.ofReal (Real.exp (-(c * κ * (q:ℝ)))) :=
    hLDTa E hE α a q N κ hq hκ hκ1' hcop hα hqC hN
  have hvolB₂ : volume B₂ ≤ ENNReal.ofReal (Real.exp (-(c * κ * (q:ℝ)))) := by
    refine hLDTa E hE α a q (2*N) κ hq hκ hκ1' hcop hα hqC ?_
    have : ((N:ℕ):ℝ) ≤ ((2*N:ℕ):ℝ) := by push_cast; linarith
    linarith
  set Bad : Set ℝ := {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧
      ((∃ j ∈ Finset.range m, Int.fract (x + (j:ℝ) * ((N:ℝ) * α)) ∈ B₁) ∨
       (∃ j ∈ Finset.range (m - 1), Int.fract (x + (j:ℝ) * ((N:ℝ) * α)) ∈ B₂))} with hBaddef
  have hBadsub : Bad ⊆ Set.Icc (0:ℝ) 1 := fun x hx => hx.1
  have hBadvol : volume Bad ≤ ENNReal.ofReal (2 * (m:ℝ) * Real.exp (-(c * κ * (q:ℝ)))) := by
    set S : ℕ → Set ℝ := fun j => {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧
        Int.fract (x + (j:ℝ) * ((N:ℝ)*α)) ∈ B₁} with hSdef
    set T : ℕ → Set ℝ := fun j => {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧
        Int.fract (x + (j:ℝ) * ((N:ℝ)*α)) ∈ B₂} with hTdef
    have hvolS : ∀ j, volume (S j) ≤ volume B₁ := by
      intro j
      exact volume_fract_shift B₁ hB₁meas hB₁sub _
    have hvolT : ∀ j, volume (T j) ≤ volume B₂ := by
      intro j
      exact volume_fract_shift B₂ hB₂meas hB₂sub _
    have hsub : Bad ⊆ (⋃ j ∈ Finset.range m, S j) ∪ (⋃ j ∈ Finset.range (m-1), T j) := by
      intro x hx
      obtain ⟨hxI, hx'⟩ := hx
      rcases hx' with ⟨j, hj, hjar⟩ | ⟨j, hj, hjar⟩
      · exact Or.inl (Set.mem_biUnion hj ⟨hxI, hjar⟩)
      · exact Or.inr (Set.mem_biUnion hj ⟨hxI, hjar⟩)
    have hsumS : (∑ j ∈ Finset.range m, volume (S j)) ≤ (m : ENNReal) * volume B₁ := by
      calc (∑ j ∈ Finset.range m, volume (S j)) ≤ ∑ j ∈ Finset.range m, volume B₁ :=
            Finset.sum_le_sum (fun j _ => hvolS j)
        _ = (m : ENNReal) * volume B₁ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsumT : (∑ j ∈ Finset.range (m-1), volume (T j)) ≤ ((m-1:ℕ) : ENNReal) * volume B₂ := by
      calc (∑ j ∈ Finset.range (m-1), volume (T j)) ≤ ∑ j ∈ Finset.range (m-1), volume B₂ :=
            Finset.sum_le_sum (fun j _ => hvolT j)
        _ = ((m-1:ℕ) : ENNReal) * volume B₂ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hstep1 : volume Bad ≤ (∑ j ∈ Finset.range m, volume (S j)) + (∑ j ∈ Finset.range (m-1), volume (T j)) := by
      calc volume Bad ≤ volume ((⋃ j ∈ Finset.range m, S j) ∪ (⋃ j ∈ Finset.range (m-1), T j)) :=
            measure_mono hsub
        _ ≤ volume (⋃ j ∈ Finset.range m, S j) + volume (⋃ j ∈ Finset.range (m-1), T j) :=
            measure_union_le _ _
        _ ≤ (∑ j ∈ Finset.range m, volume (S j)) + (∑ j ∈ Finset.range (m-1), volume (T j)) :=
            add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)
    have hE0 : 0 ≤ Real.exp (-(c * κ * (q:ℝ))) := le_of_lt (Real.exp_pos _)
    have hstep2 : (m : ENNReal) * volume B₁ + ((m-1:ℕ) : ENNReal) * volume B₂
        ≤ (m : ENNReal) * ENNReal.ofReal (Real.exp (-(c * κ * (q:ℝ))))
          + ((m-1:ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (-(c * κ * (q:ℝ)))) :=
      add_le_add (mul_le_mul_right hvolB₁ _) (mul_le_mul_right hvolB₂ _)
    have hstep3 : (m : ENNReal) * ENNReal.ofReal (Real.exp (-(c * κ * (q:ℝ))))
          + ((m-1:ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (-(c * κ * (q:ℝ))))
        = ENNReal.ofReal ((2 * (m:ℝ) - 1) * Real.exp (-(c * κ * (q:ℝ)))) := by
      rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_natCast (m-1),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (m:ℝ)),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (((m-1:ℕ)):ℝ))]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
      ring
    have hstep4 : ENNReal.ofReal ((2 * (m:ℝ) - 1) * Real.exp (-(c * κ * (q:ℝ))))
        ≤ ENNReal.ofReal (2 * (m:ℝ) * Real.exp (-(c * κ * (q:ℝ)))) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hE0]
    exact le_trans (le_trans (le_trans hstep1 (add_le_add hsumS hsumT)) hstep2)
      (le_trans hstep3.le hstep4)
  have hBadvolR : (volume Bad).toReal ≤ 2 * (m:ℝ) * Real.exp (-(c * κ * (q:ℝ))) := by
    rw [← ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2 * (m:ℝ) * Real.exp (-(c * κ * (q:ℝ))))]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hBadvol
  -- ============ 4. the pointwise estimates ============
  -- good-set property at scale N
  have hgoodN : ∀ x ∈ Set.Icc (0:ℝ) 1, x ∉ Bad → ∀ j ∈ Finset.range m,
      |uAvg α lam (E:ℂ) N (x + (j:ℝ) * ((N:ℝ) * α)) - LN| ≤ κ := by
    intro x hxI hxB j hj
    have hfract : Int.fract (x + (j:ℝ) * ((N:ℝ) * α)) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩
    have hnot : Int.fract (x + (j:ℝ) * ((N:ℝ) * α)) ∉ B₁ := by
      intro hmem
      exact hxB ⟨hxI, Or.inl ⟨j, hj, hmem⟩⟩
    rw [hB1def] at hnot
    simp only [Set.mem_setOf_eq, not_and] at hnot
    have h2 := hnot hfract
    rw [uAvg_fract α lam (E:ℂ) N (x + (j:ℝ) * ((N:ℝ) * α))]
    exact not_lt.mp h2
  have hgood2N : ∀ x ∈ Set.Icc (0:ℝ) 1, x ∉ Bad → ∀ j ∈ Finset.range (m-1),
      |uAvg α lam (E:ℂ) (2*N) (x + (j:ℝ) * ((N:ℝ) * α)) - L2N| ≤ κ := by
    intro x hxI hxB j hj
    have hfract : Int.fract (x + (j:ℝ) * ((N:ℝ) * α)) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩
    have hnot : Int.fract (x + (j:ℝ) * ((N:ℝ) * α)) ∉ B₂ := by
      intro hmem
      exact hxB ⟨hxI, Or.inr ⟨j, hj, hmem⟩⟩
    rw [hB2def] at hnot
    simp only [Set.mem_setOf_eq, not_and] at hnot
    have h2 := hnot hfract
    rw [uAvg_fract α lam (E:ℂ) (2*N) (x + (j:ℝ) * ((N:ℝ) * α))]
    exact not_lt.mp h2
  -- the pointwise (avalanche) estimate on the good set
  have hF_good : ∀ x ∈ Set.Icc (0:ℝ) 1, x ∉ Bad →
      |Ffun α lam (E:ℂ) N m x| ≤ 1000 * (m:ℝ) / Real.sqrt μ := by
    intro x hxI hxB
    have hm0 : 0 < m := by omega
    set A : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun j => block α lam (E:ℂ) N x (j % m) with hAdef
    have hAeq : ∀ j < m, A j = block α lam (E:ℂ) N x j := by
      intro j hj
      rw [hAdef]
      simp only
      rw [Nat.mod_eq_of_lt hj]
    have hdet : ∀ j, (A j).det = 1 := by
      intro j
      rw [hAdef]
      exact det_iterC α lam (E:ℂ) N _
    have hnorm : ∀ j, μ ≤ frob (A j) := by
      intro j
      have hj : j % m ∈ Finset.range m := Finset.mem_range.mpr (Nat.mod_lt j hm0)
      have hg := hgoodN x hxI hxB (j % m) hj
      rw [abs_le] at hg
      have hlog : Real.log (frob (A j))
          = (N:ℝ) * uAvg α lam (E:ℂ) N (x + ((j % m : ℕ):ℝ) * ((N:ℝ) * α)) := by
        rw [hAdef]
        simp only [block]
        rw [log_frob_eq_mul_uAvg α lam (E:ℂ) hN1]
      have hfrpos : 0 < frob (A j) := frob_iterC_pos α lam (E:ℂ) N _
      have h3 : (N:ℝ) * (LN - κ) ≤ Real.log (frob (A j)) := by
        rw [hlog]
        have hg' : LN - κ ≤ uAvg α lam (E:ℂ) N (x + ((j % m : ℕ):ℝ) * ((N:ℝ) * α)) := by
          linarith [hg.1]
        exact mul_le_mul_of_nonneg_left hg' (le_of_lt hNpos)
      rw [hμdef]
      exact (Real.le_log_iff_exp_le hfrpos).mp h3
    have hpair : ∀ j, j + 1 < m →
        Real.log (frob (A (j + 1))) + Real.log (frob (A j)) - Real.log (frob (A (j + 1) * A j))
          ≤ Real.log μ / 2 := by
      intro j hj
      have hjm : j < m := by omega
      have hj1m : j + 1 < m := hj
      have h1 : A (j+1) = block α lam (E:ℂ) N x (j+1) := hAeq (j+1) hj1m
      have h2 : A j = block α lam (E:ℂ) N x j := hAeq j hjm
      have hg1 : |uAvg α lam (E:ℂ) N (x + ((j+1:ℕ):ℝ) * ((N:ℝ) * α)) - LN| ≤ κ :=
        hgoodN x hxI hxB (j+1) (Finset.mem_range.mpr hj1m)
      have hg0 : |uAvg α lam (E:ℂ) N (x + (j:ℝ) * ((N:ℝ) * α)) - LN| ≤ κ :=
        hgoodN x hxI hxB j (Finset.mem_range.mpr hjm)
      have hg2 : |uAvg α lam (E:ℂ) (2*N) (x + (j:ℝ) * ((N:ℝ) * α)) - L2N| ≤ κ :=
        hgood2N x hxI hxB j (Finset.mem_range.mpr (by omega))
      rw [abs_le] at hg1 hg0 hg2
      have hp1 : Real.log (frob (A (j+1)))
          = (N:ℝ) * uAvg α lam (E:ℂ) N (x + ((j+1:ℕ):ℝ) * ((N:ℝ) * α)) := by
        rw [h1]
        simp only [block]
        rw [log_frob_eq_mul_uAvg α lam (E:ℂ) hN1]
      have hp0 : Real.log (frob (A j))
          = (N:ℝ) * uAvg α lam (E:ℂ) N (x + (j:ℝ) * ((N:ℝ) * α)) := by
        rw [h2]
        simp only [block]
        rw [log_frob_eq_mul_uAvg α lam (E:ℂ) hN1]
      have hp2 : Real.log (frob (A (j + 1) * A j))
          = (((2*N:ℕ)):ℝ) * uAvg α lam (E:ℂ) (2*N) (x + (j:ℝ) * ((N:ℝ) * α)) := by
        rw [h1, h2, block_mul]
        rw [log_frob_eq_mul_uAvg α lam (E:ℂ) (by omega : 1 ≤ 2*N)]
      have h2Nc : ((((2*N:ℕ)):ℝ)) = 2 * (N:ℝ) := by push_cast; ring
      have hb1 : Real.log (frob (A (j+1))) ≤ (N:ℝ) * (LN + κ) := by
        rw [hp1]; nlinarith [hg1.2, hNpos]
      have hb0 : Real.log (frob (A j)) ≤ (N:ℝ) * (LN + κ) := by
        rw [hp0]; nlinarith [hg0.2, hNpos]
      have hb2 : 2 * (N:ℝ) * (L2N - κ) ≤ Real.log (frob (A (j+1) * A j)) := by
        rw [hp2, h2Nc]; nlinarith [hg2.1, hNpos]
      have hkey2 : 2 * (LN + 2*κ - L2N) < (LN - κ)/2 := by linarith [h2N, hLN, hκ]
      have hkey3 : (N:ℝ) * (LN + κ) + (N:ℝ) * (LN + κ) - 2 * ((N:ℝ) * (L2N - κ))
          < (N:ℝ) * (LN - κ) / 2 := by
        have := mul_lt_mul_of_pos_left hkey2 hNpos
        nlinarith [this]
      rw [hlogμ]
      linarith [hb1, hb0, hb2, hkey3]
    have hav := avalanche_weak A m μ hdet hm2 hμbig hnorm hpair
    have hmat : matProd A m = iterC α lam (E:ℂ) (m * N) x := by
      have h1 : matProd A m = matProd (block α lam (E:ℂ) N x) m := matProd_congr (fun j hj => hAeq j hj)
      rw [h1, matProd_block]
    have hs1 : (∑ j ∈ Finset.Icc 1 (m - 2), Real.log (frob (A j)))
        = ∑ j ∈ Finset.Icc 1 (m - 2), Real.log (frob (block α lam (E:ℂ) N x j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hAeq j (by have := (Finset.mem_Icc.mp hj).2; omega)]
    have hs2 : (∑ j ∈ Finset.range (m - 1), Real.log (frob (A (j + 1) * A j)))
        = ∑ j ∈ Finset.range (m - 1),
            Real.log (frob (block α lam (E:ℂ) N x (j + 1) * block α lam (E:ℂ) N x j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < m - 1 := Finset.mem_range.mp hj
      rw [hAeq (j+1) (by omega), hAeq j (by omega)]
    rw [hmat, hs1, hs2] at hav
    simpa only [Ffun] using hav
  -- the crude bound, valid everywhere
  have hF_crude : ∀ x : ℝ, |Ffun α lam (E:ℂ) N m x| ≤ 2 * (m:ℝ) * (N:ℝ) * C₀ := by
    intro x
    have hmNcast : (((m * N : ℕ)) : ℝ) = (m:ℝ) * (N:ℝ) := by push_cast; ring
    have hcard1 : ((Finset.Icc 1 (m - 2)).card) = m - 2 := by simp
    have hcard2 : ((Finset.range (m - 1)).card) = m - 1 := Finset.card_range _
    have hA1 : Real.log (frob (iterC α lam (E:ℂ) (m * N) x)) ≤ (m:ℝ) * (N:ℝ) * C₀ := by
      rw [log_frob_eq_mul_uAvg α lam (E:ℂ) hmN1 x, hmNcast]
      have := hLEB E hE α (m*N) x
      have h0 : (0:ℝ) ≤ (m:ℝ) * (N:ℝ) := by positivity
      nlinarith [this, hC0, h0]
    have hA1' : 0 ≤ Real.log (frob (iterC α lam (E:ℂ) (m * N) x)) :=
      log_frob_iterC_nonneg' α lam (E:ℂ) (m * N) x
    have hB1 : (∑ j ∈ Finset.Icc 1 (m - 2), Real.log (frob (block α lam (E:ℂ) N x j)))
        ≤ ((m:ℝ) - 2) * (N:ℝ) * C₀ := by
      calc (∑ j ∈ Finset.Icc 1 (m - 2), Real.log (frob (block α lam (E:ℂ) N x j)))
          ≤ ∑ j ∈ Finset.Icc 1 (m - 2), ((N:ℝ) * C₀) := by
            apply Finset.sum_le_sum
            intro j hj
            simp only [block]
            rw [log_frob_eq_mul_uAvg α lam (E:ℂ) hN1]
            have := hLEB E hE α N (x + (j:ℝ) * ((N:ℝ) * α))
            nlinarith [this, hNpos, hC0]
        _ = ((m:ℝ) - 2) * (N:ℝ) * C₀ := by
            rw [Finset.sum_const, hcard1, nsmul_eq_mul]
            have hc : (((m - 2 : ℕ)) : ℝ) = (m:ℝ) - 2 := by
              rw [Nat.cast_sub (by omega : 2 ≤ m)]; norm_num
            rw [hc]; ring
    have hB1' : 0 ≤ (∑ j ∈ Finset.Icc 1 (m - 2), Real.log (frob (block α lam (E:ℂ) N x j))) :=
      Finset.sum_nonneg (fun j _ => log_frob_iterC_nonneg' α lam (E:ℂ) N _)
    have hB2 : (∑ j ∈ Finset.range (m - 1),
          Real.log (frob (block α lam (E:ℂ) N x (j + 1) * block α lam (E:ℂ) N x j)))
        ≤ ((m:ℝ) - 1) * (2 * (N:ℝ)) * C₀ := by
      have h2Nc : ((((2*N:ℕ)):ℝ)) = 2 * (N:ℝ) := by push_cast; ring
      calc (∑ j ∈ Finset.range (m - 1),
            Real.log (frob (block α lam (E:ℂ) N x (j + 1) * block α lam (E:ℂ) N x j)))
          ≤ ∑ j ∈ Finset.range (m - 1), (2 * (N:ℝ) * C₀) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [block_mul]
            rw [log_frob_eq_mul_uAvg α lam (E:ℂ) (by omega : 1 ≤ 2*N)]
            rw [h2Nc]
            have := hLEB E hE α (2*N) (x + (j:ℝ) * ((N:ℝ) * α))
            nlinarith [this, hNpos, hC0]
        _ = ((m:ℝ) - 1) * (2 * (N:ℝ)) * C₀ := by
            rw [Finset.sum_const, hcard2, nsmul_eq_mul]
            have hc : (((m - 1 : ℕ)) : ℝ) = (m:ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
            rw [hc]; ring
    have hB2' : 0 ≤ (∑ j ∈ Finset.range (m - 1),
          Real.log (frob (block α lam (E:ℂ) N x (j + 1) * block α lam (E:ℂ) N x j))) := by
      apply Finset.sum_nonneg
      intro j hj
      rw [block_mul]
      exact log_frob_iterC_nonneg' α lam (E:ℂ) (2*N) _
    rw [Ffun, abs_le]
    constructor
    · nlinarith [hA1', hB1', hA1, hB1, hB2, hC0, hNpos, hN1, hm]
    · nlinarith [hA1', hB1', hA1, hB1, hB2, hC0, hNpos, hN1, hm]
  -- ============ 5. the integral bound ============
  have hcrude : 0 ≤ 2 * (m:ℝ) * (N:ℝ) * C₀ := by positivity
  have hFint : (∫ x in (0:ℝ)..1, Ffun α lam (E:ℂ) N m x)
      = ((m:ℝ) * N) * LmN + (((m:ℝ) - 2) * N) * LN - (2 * ((m:ℝ) - 1) * N) * L2N := by
    have h := integral_Ffun α lam (E:ℂ) N m hN1 hm2
    rw [← hLNdef, ← hL2Ndef, ← hLmNdef] at h
    exact h
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1, |Ffun α lam (E:ℂ) N m x|
      ≤ 1000 * (m:ℝ) / Real.sqrt μ + (2 * (m:ℝ) * (N:ℝ) * C₀) * (Bad.indicator (fun _ => (1:ℝ)) x) := by
    intro x hxI
    by_cases hxB : x ∈ Bad
    · rw [Set.indicator_of_mem hxB]
      have h0 : 0 ≤ 1000 * (m:ℝ) / Real.sqrt μ := by positivity
      linarith [hF_crude x]
    · rw [Set.indicator_of_notMem hxB, mul_zero, add_zero]
      exact hF_good x hxI hxB
  have hcont : Continuous (fun x : ℝ => Ffun α lam (E:ℂ) N m x) := by
    simp only [Ffun]
    refine Continuous.sub (Continuous.add ?_ ?_) ?_
    · exact continuous_log_frob_iterC α lam (E:ℂ) (m*N)
    · apply continuous_finset_sum
      intro j hj
      simp only [block]
      exact (continuous_log_frob_iterC α lam (E:ℂ) N).comp (continuous_id.add continuous_const)
    · apply continuous_finset_sum
      intro j hj
      have heq : (fun x : ℝ => Real.log (frob (block α lam (E:ℂ) N x (j + 1) * block α lam (E:ℂ) N x j)))
          = fun x : ℝ => Real.log (frob (iterC α lam (E:ℂ) (2*N) (x + (j:ℝ) * ((N:ℝ) * α)))) := by
        funext x; rw [block_mul]
      rw [heq]
      exact (continuous_log_frob_iterC α lam (E:ℂ) (2*N)).comp (continuous_id.add continuous_const)
  have hcont1 : IntervalIntegrable (fun x : ℝ => |Ffun α lam (E:ℂ) N m x|) volume (0:ℝ) 1 :=
    hcont.abs.intervalIntegrable _ _
  have hind_meas : MeasurableSet Bad := measurableSet_bad B₁ B₂ hB₁meas hB₂meas m N α
  have hind_int : IntervalIntegrable (Bad.indicator (fun _ => (1:ℝ))) volume (0:ℝ) 1 :=
    intervalIntegrable_indicator Bad hind_meas
  have hindval : (∫ x in (0:ℝ)..1, Bad.indicator (fun _ => (1:ℝ)) x)
      = (volume (Bad ∩ Set.Ioc (0:ℝ) 1)).toReal := integral_indicator_eq Bad hind_meas
  have hfin : volume Bad ≠ ⊤ := by
    have hle : volume Bad ≤ volume (Set.Icc (0:ℝ) 1) := measure_mono hBadsub
    rw [Real.volume_Icc] at hle
    exact ne_top_of_le_ne_top (by simp) hle
  have hleBad : (volume (Bad ∩ Set.Ioc (0:ℝ) 1)).toReal ≤ (volume Bad).toReal :=
    ENNReal.toReal_mono hfin (measure_mono Set.inter_subset_left)
  have hbound : (∫ x in (0:ℝ)..1, Bad.indicator (fun _ => (1:ℝ)) x)
      ≤ 2 * (m:ℝ) * Real.exp (-(c * κ * (q:ℝ))) := by
    rw [hindval]
    exact le_trans hleBad hBadvolR
  have hIntBound : (∫ x in (0:ℝ)..1, |Ffun α lam (E:ℂ) N m x|)
      ≤ 1000 * (m:ℝ) / Real.sqrt μ
        + (2 * (m:ℝ) * (N:ℝ) * C₀) * (2 * (m:ℝ) * Real.exp (-(c * κ * (q:ℝ)))) := by
    have hint2 : IntervalIntegrable (fun x : ℝ => 1000 * (m:ℝ) / Real.sqrt μ
        + (2 * (m:ℝ) * (N:ℝ) * C₀) * Bad.indicator (fun _ => (1:ℝ)) x) volume (0:ℝ) 1 :=
      intervalIntegrable_const.add (hind_int.const_mul _)
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hcont1 hint2 hpt
    have hsplit : (∫ x in (0:ℝ)..1, (1000 * (m:ℝ) / Real.sqrt μ
        + (2 * (m:ℝ) * (N:ℝ) * C₀) * Bad.indicator (fun _ => (1:ℝ)) x))
        = 1000 * (m:ℝ) / Real.sqrt μ + (2 * (m:ℝ) * (N:ℝ) * C₀)
          * (∫ x in (0:ℝ)..1, Bad.indicator (fun _ => (1:ℝ)) x) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const (hind_int.const_mul _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      norm_num
    rw [hsplit] at hmono
    nlinarith [hmono, hbound, hcrude]
  -- ============ 6. final arithmetic ============
  have hmnpos : (0:ℝ) < (m:ℝ) * (N:ℝ) := by positivity
  have halg : (((m:ℝ) * N) * LmN + (((m:ℝ) - 2) * N) * LN - (2 * ((m:ℝ) - 1) * N) * L2N)
      / ((m:ℝ) * (N:ℝ)) = LmN + (1 - 2/(m:ℝ)) * LN - (2 - 2/(m:ℝ)) * L2N := by
    have hmne : (m:ℝ) ≠ 0 := by positivity
    have hNne : (N:ℝ) ≠ 0 := by positivity
    field_simp
  have hmain : |LmN + (1 - 2 / (m:ℝ)) * LN - (2 - 2 / (m:ℝ)) * L2N|
      ≤ (∫ x in (0:ℝ)..1, |Ffun α lam (E:ℂ) N m x|) / ((m:ℝ) * (N:ℝ)) := by
    have h1 : |(((m:ℝ) * N) * LmN + (((m:ℝ) - 2) * N) * LN - (2 * ((m:ℝ) - 1) * N) * L2N)
        / ((m:ℝ) * (N:ℝ))| ≤ (∫ x in (0:ℝ)..1, |Ffun α lam (E:ℂ) N m x|) / ((m:ℝ) * (N:ℝ)) := by
      rw [abs_div, abs_of_pos hmnpos]
      apply div_le_div_of_nonneg_right _ (le_of_lt hmnpos)
      rw [← hFint]
      exact intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ) ≤ 1)
    rwa [halg] at h1
  have hexpE : 0 < Real.exp (-(c * κ * (q:ℝ) / 4)) := Real.exp_pos _
  have hμhalf : 1000 / ((N:ℝ) * Real.sqrt μ) < 1000 * Real.exp (-(c * κ * (q:ℝ) / 4)) := by
    have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    have hsqe : (Real.exp ((N:ℝ) * (LN - κ) / 2))^2 = μ := by
      rw [sq, ← Real.exp_add, hμdef]
      congr 1
      ring
    have hle : Real.exp ((N:ℝ) * (LN - κ) / 2) ≤ Real.sqrt μ := Real.le_sqrt_of_sq_le hsqe.le
    have hposE : 0 < Real.exp ((N:ℝ) * (LN - κ) / 2) := Real.exp_pos _
    have hinv : 1 / Real.sqrt μ ≤ Real.exp (-((N:ℝ) * (LN - κ) / 2)) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le hposE hle
    have hkey : c * κ * (q:ℝ) / 4 < (N:ℝ) * (LN - κ) / 2 := by
      have h1 : (9900:ℝ) * (q:ℝ) ≤ (N:ℝ) * (LN - κ) := by
        have hLNk : 99 * κ ≤ LN - κ := by linarith
        have hmul := mul_le_mul hNk hLNk (by positivity) (by positivity)
        have hk : (κ^2)⁻¹ * κ = κ⁻¹ := by
          have hne : κ ≠ 0 := ne_of_gt hκ
          field_simp
        have heq : (κ^2)⁻¹ * (q:ℝ) * (99*κ) = 99 * (q:ℝ) * κ⁻¹ := by
          rw [show (κ^2)⁻¹ * (q:ℝ) * (99*κ) = 99 * (q:ℝ) * ((κ^2)⁻¹ * κ) by ring, hk]
        have hge : (9900:ℝ) * (q:ℝ) ≤ 99 * (q:ℝ) * κ⁻¹ := by nlinarith [hκinv100, hq1]
        linarith [hmul, heq, hge]
      have hckq : c * κ * (q:ℝ) ≤ (q:ℝ) / 100 := by
        have h1 : c * κ ≤ 1 * (1/100) :=
          mul_le_mul hc1 hκ1 (le_of_lt hκ) (by norm_num)
        calc c * κ * (q:ℝ) ≤ (1 * (1/100)) * (q:ℝ) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = (q:ℝ) / 100 := by ring
      nlinarith [h1, hckq, hq1]
    have hexplt : Real.exp (-((N:ℝ) * (LN - κ) / 2)) < Real.exp (-(c * κ * (q:ℝ) / 4)) :=
      Real.exp_lt_exp.mpr (by linarith [hkey])
    have hsmall : 1 / ((N:ℝ) * Real.sqrt μ) < Real.exp (-(c * κ * (q:ℝ) / 4)) := by
      have hne : (N:ℝ) ≠ 0 := by positivity
      have hsne : Real.sqrt μ ≠ 0 := ne_of_gt hsqμpos
      have h1 : 1 / ((N:ℝ) * Real.sqrt μ) = (1/(N:ℝ)) * (1/Real.sqrt μ) := by
        field_simp
      rw [h1]
      have h2 : 1/(N:ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hN1'
      calc (1/(N:ℝ)) * (1/Real.sqrt μ) ≤ 1 * Real.exp (-((N:ℝ) * (LN - κ) / 2)) := by
            apply mul_le_mul h2 hinv (by positivity) (by norm_num)
        _ = Real.exp (-((N:ℝ) * (LN - κ) / 2)) := by ring
        _ < Real.exp (-(c * κ * (q:ℝ) / 4)) := hexplt
    calc 1000 / ((N:ℝ) * Real.sqrt μ) = 1000 * (1 / ((N:ℝ) * Real.sqrt μ)) := by ring
      _ < 1000 * Real.exp (-(c * κ * (q:ℝ) / 4)) :=
          mul_lt_mul_of_pos_left hsmall (by norm_num)
  have hmterm : 4 * (m:ℝ) * C₀ * Real.exp (-(c * κ * (q:ℝ)))
      ≤ 4 * C₀ * Real.exp (-(c * κ * (q:ℝ) / 4)) := by
    have hmexp : (m:ℝ) * Real.exp (-(c * κ * (q:ℝ))) < Real.exp (-(c * κ * (q:ℝ) / 2)) := by
      have h1 : Real.exp (c * κ * (q:ℝ) / 2) * Real.exp (-(c * κ * (q:ℝ)))
          = Real.exp (-(c * κ * (q:ℝ) / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← h1]
      exact mul_lt_mul_of_pos_right hmq (Real.exp_pos _)
    have hexpmono : Real.exp (-(c * κ * (q:ℝ) / 2)) ≤ Real.exp (-(c * κ * (q:ℝ) / 4)) := by
      apply Real.exp_le_exp.mpr
      have hq0 : (0:ℝ) ≤ c * κ * (q:ℝ) := by positivity
      linarith
    have hC0' : (0:ℝ) ≤ C₀ := le_of_lt hC0
    calc 4 * (m:ℝ) * C₀ * Real.exp (-(c * κ * (q:ℝ)))
        = 4 * C₀ * ((m:ℝ) * Real.exp (-(c * κ * (q:ℝ)))) := by ring
      _ ≤ 4 * C₀ * Real.exp (-(c * κ * (q:ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left (le_of_lt hmexp) (by positivity)
      _ ≤ 4 * C₀ * Real.exp (-(c * κ * (q:ℝ) / 4)) := by
          apply mul_le_mul_of_nonneg_left hexpmono (by positivity)
  have hfinal : |LmN + (1 - 2 / (m:ℝ)) * LN - (2 - 2 / (m:ℝ)) * L2N|
      < (12 * C₀ + 1000) * Real.exp (-(c * κ * (q:ℝ) / 4)) := by
    have h1 : (∫ x in (0:ℝ)..1, |Ffun α lam (E:ℂ) N m x|) / ((m:ℝ) * (N:ℝ))
        ≤ (1000 * (m:ℝ) / Real.sqrt μ
            + (2 * (m:ℝ) * (N:ℝ) * C₀) * (2 * (m:ℝ) * Real.exp (-(c * κ * (q:ℝ)))))
          / ((m:ℝ) * (N:ℝ)) :=
      div_le_div_of_nonneg_right hIntBound (le_of_lt hmnpos)
    have h2 : (1000 * (m:ℝ) / Real.sqrt μ
          + (2 * (m:ℝ) * (N:ℝ) * C₀) * (2 * (m:ℝ) * Real.exp (-(c * κ * (q:ℝ)))))
          / ((m:ℝ) * (N:ℝ))
        = 1000 / ((N:ℝ) * Real.sqrt μ)
          + 4 * (m:ℝ) * C₀ * Real.exp (-(c * κ * (q:ℝ))) := by
      have hmne : (m:ℝ) ≠ 0 := by positivity
      have hNne : (N:ℝ) ≠ 0 := by positivity
      have hsne : Real.sqrt μ ≠ 0 := ne_of_gt hsqμpos
      field_simp
      ring
    have h3 : 1000 / ((N:ℝ) * Real.sqrt μ) + 4 * (m:ℝ) * C₀ * Real.exp (-(c * κ * (q:ℝ)))
        < (12 * C₀ + 1000) * Real.exp (-(c * κ * (q:ℝ) / 4)) := by
      nlinarith [hμhalf, hmterm, le_of_lt hC0, hexpE]
    rw [h2] at h1
    linarith [hmain, h1, h3]
  exact hfinal


end

end Work.TMC7Core.Scale
