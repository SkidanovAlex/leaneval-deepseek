/-
# `E1Norm/Radial` — the quantitative radial bound for the transfer defect's radial profile

The transfer defect is `E1 α f = (D_θ Γ) · radA α f` (`Transfer/Profiles.lean`), a product of an
angular profile and the *radial* profile

  `radA α f z = -(ampA α z)·L₁₂ f(z) + (ampB α z/c(α))·C₀ f`,
  `ampA α z = 2z/(c(α)(1+z)²)`, `ampB α z = 2z²/(1+z)³`, `C₀ f = L₁₂(Transport f)(0)`.

This file proves the radial half of the norm bound of `Transfer.E1_norm`: for `0 < α ≤ 1`,
`n ≤ 3` and `f ∈ CoerAdm α`,

  `∫_0^∞ ∑_{j≤n} (D_z^j (radA α f)(z))² w(z)² dz ≤ C·(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`

with a constant `C` that does **not** depend on `α`, `n` or `f`.

The proof has three steps, each of which is a separate named result:

* `Maj_int_le` — the pointwise majorant `E1Parts.Maj α f j K` of the `j`-th integrand
  (`E1Parts.RadA_Efun_eq`, `E1Parts.Efun_le_Maj`) has an integral bounded by
  `(2·((8K)²·16·107·CQ) + 200·CC·Kb)·|f|²_{ℋⁿ}`.  Its `L₁₂`-part is bounded by the four
  hypotheses at the top (the Hardy inequality for `L₁₂ f` itself, `Coercivity.L12f_w_hardy`,
  and the angular-moment bounds `Qang` for the higher `D_z`-iterates,
  `E1Parts.dzdIter_L_as_if` + `hQ`), and its `C₀`-part by `hC0` and the explicit profile bound
  `hB`;
* `hardy_L12f` — the `c = 0` instance of the first family, i.e. the Hardy inequality
  `∫ (L₁₂ f · w)² ≤ 107·∫ (Qang f 0)² w²` composed with `hQ`;
* the assembly, which sums `Maj_int_le` over `j ≤ n` and adds the integrability of the
  single integrands (`E1Parts.RadA`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadABnd
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAId
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadA
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.HardyOne
import Submission.Work.Coercivity.L12f_w_hardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The restricted measures of `(0,∞)` and `[0,∞)` agree: they differ by the null point `0`. -/
theorem restrict_Ioi_eq_restrict_Iz :
    MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) = MeasureTheory.volume.restrict Work.Spaces.Iz := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))

/-! ## The `c = 0` piece: the Hardy inequality for `L₁₂ f` -/

/-- **The Hardy bound for the `L₁₂`-profile.**  For `f ∈ CoerAdm α` and `HkMem α n f`,

  `∫ (L₁₂ f · w)² ≤ 107·CQ·|f|²_{ℋⁿ}`,

where `CQ` bounds the weighted angular moments `∫ (Qang g i)²w²` at level `n` (`hQ`). -/
theorem hardy_L12f {CQ : ℝ}
    (hQ : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem β m g → ∀ i : ℕ, i ≤ m →
      MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ CQ * Work.Spaces.HkSq β m g)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hmem : Work.Spaces.HkMem α n f) :
    MeasureTheory.IntegrableOn (fun z => (Work.Coercivity.L12f f z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Coercivity.L12f f z * Work.Spaces.w z) ^ 2)
        ≤ 107 * CQ * Work.Spaces.HkSq α n f := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hH : Work.Coercivity.HardyHyp f :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.hardyHyp_of_coerAdm_le_one α hα hα1 hf
  have h0 := hQ α n f hα hα1 hsm hmem 0 (Nat.zero_le n)
  have hQang : Work.Elliptic.Qang f 0 = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ := by
    funext z
    simp only [Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [Work.Elliptic.Ktheta_eq_K]
  have hgint : MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    simpa only [hQang] using h0.1
  obtain ⟨hint, hbd⟩ := Work.Coercivity.L12f_w_hardy f hH hgint
  refine ⟨hint, ?_⟩
  have h2 : (∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ CQ * Work.Spaces.HkSq α n f := by
    simpa only [hQang] using h0.2
  linarith

/-! ## The integral of the majorant, for one order `j` -/

/-- **The single-order majorant bound.**  For `j ≤ n ≤ 3`,

  `∫_0^∞ Maj α f j K ≤ (2·((8K)²·16·107·CQ) + 200·CC·Kb)·|f|²_{ℋⁿ}`,

where `Maj` is the pointwise majorant of the `j`-th `D_z`-iterate of `radA α f` supplied by
`E1Parts.Efun_le_Maj`. -/
theorem Maj_int_le {CQ CC Kb K : ℝ} (hCQ : 0 ≤ CQ) (hCC : 0 < CC) (hKb : 0 < Kb) (hK : 0 ≤ K)
    (hQ : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem β m g → ∀ i : ℕ, i ≤ m →
      MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ CQ * Work.Spaces.HkSq β m g)
    (hC0 : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 → Work.FTS.Nonlin.CoerAdm β g →
      Work.Spaces.HkMem β m g → (Work.Coercivity.C0 g) ^ 2 ≤ CC * Work.Spaces.HkSq β m g)
    (hB : ∀ (β : ℝ), 0 < β → β ≤ 1 → (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 4,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB β) z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ Kb)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hmem : Work.Spaces.HkMem α n f) (j : ℕ) (hj : j ≤ n) :
    (∫ z in Work.Spaces.Iz, Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z)
      ≤ (2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hj3 : j ≤ 3 := by omega
  have hNf : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hLint : ∀ c ≤ 3, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := fun c hc =>
    Work.FTS.CoercivityFix.Transfer.E1Parts.L12f_DzdIter_sq_w_sq_integrable α hα hα1 hf c hc
  have hBint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 j (by omega)
  have hsum_int : MeasureTheory.IntegrableOn
      (fun z => ∑ c ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum _ (fun c hc => hLint c (by have := Finset.mem_range.mp hc; omega))
  -- ## the per-order bound for the `L₁₂`-iterates
  have hHardy := (hardy_L12f hQ α hα hα1 n hf hmem).2
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
        have h1 := Work.FTS.CoercivityFix.Transfer.E1Parts.dzdIter_L_as_if α hα hα1 hf (c := c) hc4 z hz
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
    rw [MeasureTheory.integral_finsetSum _ (fun c hc => hLint c (by have := Finset.mem_range.mp hc; omega))]
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
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ Kb := by
    refine le_trans ?_ (hB α hα hα1)
    have hsum_int' : MeasureTheory.IntegrableOn (fun z => ∑ j' ∈ Finset.range 4,
        (Work.Elliptic.DzdIter j' (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz :=
      MeasureTheory.integrable_finsetSum _ (fun c hc =>
        (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 c (by
          have := Finset.mem_range.mp hc; omega))
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _))) hsum_int' ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
    exact Finset.single_le_sum (f := fun j' => (Work.Elliptic.DzdIter j'
      (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_range.mpr (by omega))
  -- ## the split of `Maj` and the numerical assembly
  have hsplit : (∫ z in Work.Spaces.Iz, Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z)
      = 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (∫ z in Work.Spaces.Iz, ∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [show (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z) = fun z =>
        2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (∑ c ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) *
            ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
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
  have hK8 : (K * 2 ^ j) ^ 2 ≤ (K * 8) ^ 2 := by
    have h2j : (2 : ℝ) ^ j ≤ 8 := by
      have h : (2 : ℝ) ^ j ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h; exact h
    exact pow_le_pow_left₀ (mul_nonneg hK (by positivity)) (by nlinarith [h2j, hK]) 2
  have hj1 : (j : ℝ) + 1 ≤ 4 := by
    have : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
    linarith
  have hA_bd : 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (((j : ℝ) + 1) * (107 * CQ * Work.Spaces.HkSq α n f))
      ≤ 2 * ((K * 8) ^ 2 * 16 * 107 * CQ) * Work.Spaces.HkSq α n f := by
    have hsq : (((j : ℝ) + 1) ^ 2) ≤ 16 := by nlinarith
    have hprod : ((K * 2 ^ j) ^ 2) * (((j : ℝ) + 1) ^ 2) ≤ ((K * 8) ^ 2) * 16 :=
      mul_le_mul hK8 hsq (sq_nonneg _) (by positivity)
    have hc2nn : (0 : ℝ) ≤ 2 * 107 * CQ * Work.Spaces.HkSq α n f := by positivity
    calc 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (((j : ℝ) + 1) * (107 * CQ * Work.Spaces.HkSq α n f))
        = (2 * 107 * CQ * Work.Spaces.HkSq α n f) * (((K * 2 ^ j) ^ 2) * (((j : ℝ) + 1) ^ 2)) := by ring
      _ ≤ (2 * 107 * CQ * Work.Spaces.HkSq α n f) * (((K * 8) ^ 2) * 16) :=
          mul_le_mul_of_nonneg_left hprod hc2nn
      _ = 2 * ((K * 8) ^ 2 * 16 * 107 * CQ) * Work.Spaces.HkSq α n f := by ring
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
  have hAstep : 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (∫ z in Work.Spaces.Iz, ∑ c ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) * (((j : ℝ) + 1) * (107 * CQ * Work.Spaces.HkSq α n f)) :=
    mul_le_mul_of_nonneg_left hsum_le (by positivity)
  have hBstep : 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) * (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) * Kb :=
    mul_le_mul_of_nonneg_left hB_le (by positivity)
  have hXY : 2 * ((K * 8) ^ 2 * 16 * 107 * CQ) * Work.Spaces.HkSq α n f
        + 200 * CC * Kb * Work.Spaces.HkSq α n f
      = (2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f := by ring
  linarith [hsplit, hAstep, hA_bd, hBstep, hB_bd, hXY]

/-! ## The radial bound for `radA α f` -/

/-- **The quantitative radial bound.**  For `0 < α ≤ 1`, `n ≤ 3` and `f ∈ CoerAdm α`,

  `∫_0^∞ ∑_{j≤n} (D_z^j (radA α f)(z))² w(z)² dz ≤ C·(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`,

the integrand being honestly integrable on `[0,∞)`. -/
theorem radA_sum_le {CQ CC Kb K : ℝ} (hCQ : 0 ≤ CQ) (hCC : 0 < CC) (hKb : 0 < Kb) (hK : 0 ≤ K)
    (hQ : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem β m g → ∀ i : ℕ, i ≤ m →
      MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ CQ * Work.Spaces.HkSq β m g)
    (hC0 : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 → Work.FTS.Nonlin.CoerAdm β g →
      Work.Spaces.HkMem β m g → (Work.Coercivity.C0 g) ^ 2 ≤ CC * Work.Spaces.HkSq β m g)
    (hB : ∀ (β : ℝ), 0 < β → β ≤ 1 → (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 4,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB β) z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ Kb)
    (hA : ∀ (β : ℝ), 0 < β → β ≤ 1 → ∀ b ≤ 4, ∀ z ∈ Set.Ioi 0,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA β) z| ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → n ≤ 3 →
      Work.FTS.Nonlin.CoerAdm α f → Work.Spaces.HkMem α n f →
      MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  refine ⟨4 * (2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) + 1,
    by have : 0 ≤ 2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb := by positivity
       linarith, ?_⟩
  intro α n f hα hα1 hn hf hmem
  have hKbd := hA α hα hα1
  have hmeas : MeasureTheory.volume.restrict (Set.Ioi 0) = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    restrict_Ioi_eq_restrict_Iz
  -- ## the pointwise majorant, a.e. on `Iz`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ j ∈ Finset.range (n + 1), Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z := by
    have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ∑ j ∈ Finset.range (n + 1), Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hj3 : j ≤ 3 := by have := Finset.mem_range.mp hj; omega
        rw [Work.FTS.CoercivityFix.Transfer.E1Parts.RadA_Efun_eq α hα hα1 f hf hj3 z hz]
        exact Work.FTS.CoercivityFix.Transfer.E1Parts.Efun_le_Maj α hα hα1 f hf hj3 hK hKbd z hz)
    rw [hmeas] at h1
    exact h1
  -- ## integrability of the majorant
  have hMint : ∀ j : ℕ, j ≤ 3 → MeasureTheory.IntegrableOn
      (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z) Work.Spaces.Iz := by
    intro j hj3
    have hAint : MeasureTheory.IntegrableOn (fun z => 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) *
        (∑ c ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)) Work.Spaces.Iz :=
      (MeasureTheory.integrable_finsetSum _ (fun c hc =>
        Work.FTS.CoercivityFix.Transfer.E1Parts.L12f_DzdIter_sq_w_sq_integrable α hα hα1 hf c
          (by have := Finset.mem_range.mp hc; omega))).const_mul _
    have hBint : MeasureTheory.IntegrableOn (fun z => 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) *
        ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2)) Work.Spaces.Iz :=
      ((Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 j (by omega)).const_mul _
    have hfun : (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z)
        = fun z => 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) *
            (∑ c ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) *
            ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) :=
      funext (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj_eq α f j K z)
    rw [hfun]
    exact hAint.add hBint
  have hRint : MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
      Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum _ (fun j hj => hMint j (by
      have := Finset.mem_range.mp hj; omega))
  have hLint : MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum _ (fun j hj =>
      Work.FTS.CoercivityFix.Transfer.E1Parts.RadA α hα hα1 f hf j (by
        have := Finset.mem_range.mp hj; omega))
  refine ⟨hLint, ?_⟩
  have hle : (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z =>
      Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))) hRint hae
  have hsum2 : (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
      Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z)
      ≤ ∑ _j ∈ Finset.range (n + 1),
          ((2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f) := by
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => hMint j (by
      have := Finset.mem_range.mp hj; omega))]
    exact Finset.sum_le_sum (fun j hj => Maj_int_le hCQ hCC hKb hK hQ hC0 hB α hα hα1 n hn hf hmem j
      (by have := Finset.mem_range.mp hj; omega))
  have hcard : (∑ _j ∈ Finset.range (n + 1),
        ((2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f))
      = ((n : ℝ) + 1) * ((2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb)
          * Work.Spaces.HkSq α n f) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hCnn : 0 ≤ (2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f := by
    have := Work.Spaces.HkSq_nonneg α n f
    positivity
  have hn4 : ((n : ℝ) + 1) ≤ 4 := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  have hkey : 4 * ((2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f)
      ≤ (4 * (2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) + 1)
        * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hC0nn : 0 ≤ 2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb := by positivity
    have hNd : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) := Work.Spaces.HkSq_nonneg α n _
    have hNf : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
    nlinarith [hNd, hNf, hC0nn]
  calc (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z := hle
    _ ≤ ∑ _j ∈ Finset.range (n + 1),
          ((2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f) := hsum2
    _ = ((n : ℝ) + 1) * ((2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f) := hcard
    _ ≤ 4 * ((2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f) :=
        mul_le_mul_of_nonneg_right hn4 hCnn
    _ = 4 * (2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f := by ring
    _ ≤ (4 * (2 * ((K * 8) ^ 2 * 16 * 107 * CQ) + 200 * CC * Kb) + 1)
        * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
        simpa only [mul_assoc] using hkey

end Work.FTS.CoercivityFix.Transfer.E1Norm
