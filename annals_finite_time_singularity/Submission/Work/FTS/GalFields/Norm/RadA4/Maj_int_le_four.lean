/-
# `GalFields/Norm/RadA4/Maj_int_le_four` — the integral of the order-`4` majorant

`E1Norm.Maj_int_le` bounds the integral of the pointwise majorant `E1Parts.Maj α f j K` of the
`j`-th `D_z`-iterate of `radA α f` for `j ≤ n ≤ 3`:

  `∫_0^∞ Maj α f j K ≤ (2·((8K)²·16·107·CQ) + 200·CC·Kb)·|f|²_{ℋⁿ}`.

The present file is the order-`4` counterpart, needed by `RadA4.radA_sum_le_four`: the `ℋ⁴`-slot
is the top slot of the data (`CoerAdm α f` supplies `ℋ⁵`-membership), so the majorant has to be
integrated one order higher.  Exactly as in `Own.lean`'s `radA_sum_le_four`, the only changes are

* `Maj`'s `D_z`-sum now runs to `j = 4`, so the weighted square of `D_z^4 (L₁₂ f)` has to be
  integrable: this is `L₁₂`-Hardy (`c = 0`) plus `D_z^c (L₁₂ f) = −Qang f (c−1)` for `1 ≤ c ≤ 4`
  (`E1Parts.DzdIter_L12f_eq_neg_Qang`) together with the hypothesis `hQ` at `i = c − 1 ≤ n`;
* the profile slot `ampB` is now needed up to order `4` (`hB` bounds the slot sum over
  `Finset.range 5`), which `E2pkg.dzdIter_coeff_bound` already supplies at `j ≤ 4`;
* the numerical constants move `8 → 16` (the `2^j` factor) and `16 → 25` (the `(j+1)²` factor).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Radial
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadABnd
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm.RadA4

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Maj_int_le_four {CQ CC Kb K : ℝ} (hCQ : 0 ≤ CQ) (hCC : 0 < CC) (hKb : 0 < Kb) (hK : 0 ≤ K)
    (hQ : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem β m g → ∀ i : ℕ, i ≤ m →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ CQ * Work.Spaces.HkSq β m g)
    (hC0 : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 → Work.FTS.Nonlin.CoerAdm β g →
      Work.Spaces.HkMem β m g → (Work.Coercivity.C0 g) ^ 2 ≤ CC * Work.Spaces.HkSq β m g)
    (hB : ∀ (β : ℝ), 0 < β → β ≤ 1 → (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB β) z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ Kb)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 4) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hmem : Work.Spaces.HkMem α n f) (j : ℕ) (hj : j ≤ n) :
    (∫ z in Work.Spaces.Iz, Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z)
      ≤ (2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hj4 : j ≤ 4 := by omega
  have hNf : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  -- ## integrability of the `D_z`-iterates of `L₁₂ f`, up to order `4`
  have hLint : ∀ c : ℕ, c ≤ j → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
    intro c hcj
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · subst h0
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.L12f_DzdIter_sq_w_sq_integrable α hα hα1 hf 0
        (by norm_num)
    · have hc4 : c ≤ 4 := by omega
      have hid := Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_L12f_eq_neg_Qang α hα hα1 hf
        c hpos hc4
      have hQioi : MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang f (c - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          (Set.Ioi (0 : ℝ)) :=
        ((hQ α n f hα hα1 hsm hmem (c - 1) (by omega)).1).congr_set_ae
          (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
      have h1 : MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
        hQioi.congr_fun (fun z hz => by
          show (Work.Elliptic.Qang f (c - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
            = (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2
          rw [hid z hz]
          ring) measurableSet_Ioi
      exact h1.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  have hBint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 j (by omega)
  have hsum_int : MeasureTheory.IntegrableOn
      (fun z => ∑ c ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum _ (fun c hc => hLint c
      (by have := Finset.mem_range.mp hc; omega))
  -- ## the per-order bound for the `L₁₂`-iterates
  have hHardy := (Work.FTS.CoercivityFix.Transfer.E1Norm.hardy_L12f hQ α hα hα1 n hf hmem).2
  have hLc : ∀ c : ℕ, c ≤ j → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * CQ * Work.Spaces.HkSq α n f := by
    intro c hc
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · subst h0
      simpa only [Work.Elliptic.DzdIter_zero, mul_pow] using hHardy
    · have hc4 : c ≤ 4 := by omega
      have hcongr : ∀ z ∈ Set.Ioi (0 : ℝ),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2
            = (Work.Elliptic.Qang f (c - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        intro z hz
        have h1 := Work.FTS.CoercivityFix.Transfer.E1Parts.dzdIter_L_as_if α hα hα1 hf
          (c := c) hc4 z hz
        rw [h1, if_neg (show ¬ (c = 0) by omega)]
        ring
      have hIoi : (∫ z in Set.Ioi (0 : ℝ),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 107 * CQ * Work.Spaces.HkSq α n f := by
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
        have h2 := (hQ α n f hα hα1 hsm hmem (c - 1) (by omega)).2
        rw [MeasureTheory.setIntegral_congr_set (s := Work.Spaces.Iz) (t := Set.Ioi (0 : ℝ))
          (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm] at h2
        exact le_trans h2 (by nlinarith [hCQ, hNf])
      rw [MeasureTheory.setIntegral_congr_set (s := Work.Spaces.Iz) (t := Set.Ioi (0 : ℝ))
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm]
      exact hIoi
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ c ∈ Finset.range (j + 1),
      (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ((j : ℝ) + 1) * (107 * CQ * Work.Spaces.HkSq α n f) := by
    rw [MeasureTheory.integral_finsetSum _ (fun c hc => hLint c
      (by have := Finset.mem_range.mp hc; omega))]
    have h1 : (∑ c ∈ Finset.range (j + 1), (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _c ∈ Finset.range (j + 1), (107 * CQ * Work.Spaces.HkSq α n f) :=
      Finset.sum_le_sum (fun c hc => hLc c (by have := Finset.mem_range.mp hc; omega))
    refine le_trans h1 (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  -- ## the `C₀`-piece
  have hB_le : (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) ≤ Kb := by
    refine le_trans ?_ (hB α hα hα1)
    have hsum_int' : MeasureTheory.IntegrableOn (fun z => ∑ j' ∈ Finset.range 5,
        (Work.Elliptic.DzdIter j' (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
      MeasureTheory.integrable_finsetSum _ (fun c hc =>
        (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 c (by
          have := Finset.mem_range.mp hc; omega))
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _))) hsum_int' ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
    exact Finset.single_le_sum (f := fun j' => (Work.Elliptic.DzdIter j'
      (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.mem_range.mpr (by omega))
  -- ## the split of `Maj` and the numerical assembly
  have hsplit : (∫ z in Work.Spaces.Iz, Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z)
      = 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (∫ z in Work.Spaces.Iz, ∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
    rw [show (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z) = fun z =>
        2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) *
            ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
        from funext (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj_eq α f j K z)]
    rw [MeasureTheory.integral_add (hsum_int.const_mul _) (hBint.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hc_bd : 1 / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc2 : (Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2 ≤ 100 * Work.Coercivity.C0 f ^ 2 := by
    rw [div_pow]
    have h1 : (1 : ℝ) / Work.Spaces.c α ^ 2 ≤ 100 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc (Work.Coercivity.C0 f) ^ 2 / Work.Spaces.c α ^ 2
        = (Work.Coercivity.C0 f) ^ 2 * (1 / Work.Spaces.c α ^ 2) := by ring
      _ ≤ (Work.Coercivity.C0 f) ^ 2 * 100 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = 100 * Work.Coercivity.C0 f ^ 2 := by ring
  have hK16 : (K * 2 ^ j) ^ 2 ≤ (K * 16) ^ 2 := by
    have h2j : (2 : ℝ) ^ j ≤ 16 := by
      have h : (2 : ℝ) ^ j ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h; exact h
    exact pow_le_pow_left₀ (mul_nonneg hK (by positivity)) (by nlinarith [h2j, hK]) 2
  have hj5 : (j : ℝ) + 1 ≤ 5 := by
    have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
    linarith
  have hA_bd : 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
        * (((j : ℝ) + 1) * (107 * CQ * Work.Spaces.HkSq α n f))
      ≤ 2 * ((K * 16) ^ 2 * 25 * 107 * CQ) * Work.Spaces.HkSq α n f := by
    have hjn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hsq : (((j : ℝ) + 1) ^ 2) ≤ 25 := by nlinarith [hj5, hjn]
    have hprod : ((K * 2 ^ j) ^ 2) * (((j : ℝ) + 1) ^ 2) ≤ ((K * 16) ^ 2) * 25 :=
      mul_le_mul hK16 hsq (sq_nonneg _) (by positivity)
    have hc2nn : (0 : ℝ) ≤ 2 * 107 * CQ * Work.Spaces.HkSq α n f := by positivity
    calc 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
          * (((j : ℝ) + 1) * (107 * CQ * Work.Spaces.HkSq α n f))
        = (2 * 107 * CQ * Work.Spaces.HkSq α n f)
            * (((K * 2 ^ j) ^ 2) * (((j : ℝ) + 1) ^ 2)) := by ring
      _ ≤ (2 * 107 * CQ * Work.Spaces.HkSq α n f) * (((K * 16) ^ 2) * 25) :=
          mul_le_mul_of_nonneg_left hprod hc2nn
      _ = 2 * ((K * 16) ^ 2 * 25 * 107 * CQ) * Work.Spaces.HkSq α n f := by ring
  have hB_bd : 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) * Kb
      ≤ 200 * CC * Kb * Work.Spaces.HkSq α n f := by
    have h0 : (Work.Coercivity.C0 f) ^ 2 ≤ CC * Work.Spaces.HkSq α n f := hC0 α n f hα hα1 hf hmem
    calc 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) * Kb
        ≤ 2 * (100 * Work.Coercivity.C0 f ^ 2) * Kb := by
          have := mul_le_mul_of_nonneg_right hc2 hKb.le
          linarith
      _ = 200 * (Work.Coercivity.C0 f) ^ 2 * Kb := by ring
      _ ≤ 200 * (CC * Work.Spaces.HkSq α n f) * Kb :=
          mul_le_mul_of_nonneg_right (by linarith) hKb.le
      _ = 200 * CC * Kb * Work.Spaces.HkSq α n f := by ring
  have hAstep : 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (∫ z in Work.Spaces.Iz,
        ∑ c ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
        * (((j : ℝ) + 1) * (107 * CQ * Work.Spaces.HkSq α n f)) :=
    mul_le_mul_of_nonneg_left hsum_le (by positivity)
  have hBstep : 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) * (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) * Kb :=
    mul_le_mul_of_nonneg_left hB_le (by positivity)
  have hXY : 2 * ((K * 16) ^ 2 * 25 * 107 * CQ) * Work.Spaces.HkSq α n f
        + 200 * CC * Kb * Work.Spaces.HkSq α n f
      = (2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f := by ring
  linarith [hsplit, hAstep, hA_bd, hBstep, hB_bd, hXY]

end Work.FTS.GalFields.Norm.RadA4
