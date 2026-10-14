import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.dthU_Gam
-- ===== merged: Submission.Work.FTS.FinalClock.PhiZopBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Set Filter

namespace Work.FTS.FinalClock

/-! ## `Zop` on a negated or shifted function -/

/-- `Zop` commutes with pointwise negation: this is `deriv_const_sub` with the constant `0`,
since `-h z = 0 - h z`. -/
lemma Zop_neg_fun (h : ℝ → ℝ) :
    Work.Spaces.Zop (fun z => - h z) = fun z => - Work.Spaces.Zop h z := by
  have h' : (fun z : ℝ => - h z) = fun z => (0 : ℝ) - h z := by
    funext z
    ring
  rw [h']
  funext z
  simp only [Work.Spaces.Zop]
  rw [deriv_const_sub]
  ring

/-- `Zop` of a constant minus a function is minus `Zop` of the function. -/
lemma Zop_const_sub_fun (c : ℝ) (h : ℝ → ℝ) :
    Work.Spaces.Zop (fun z => c - h z) = fun z => - Work.Spaces.Zop h z := by
  funext z
  simp only [Work.Spaces.Zop]
  rw [deriv_const_sub]
  ring

/-- The same at the level of the iterates, for order `≥ 1` (the order `0` iterate is the
function itself, for which the identity fails). -/
lemma Zop_iter_const_sub_fun (c : ℝ) (h : ℝ → ℝ) (b : ℕ) (hb : 1 ≤ b) :
    Work.Spaces.Zop^[b] (fun z => c - h z) = fun z => - Work.Spaces.Zop^[b] h z := by
  induction b with
  | zero => exact absurd hb (by omega)
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0]
        simpa using Zop_const_sub_fun c h
      · have ihk : Work.Spaces.Zop^[k] (fun z => c - h z)
            = fun z => - Work.Spaces.Zop^[k] h z := ih hkpos
        calc Work.Spaces.Zop^[k + 1] (fun z => c - h z)
            = Work.Spaces.Zop (Work.Spaces.Zop^[k] (fun z => c - h z)) :=
                Function.iterate_succ_apply' _ k _
          _ = Work.Spaces.Zop (fun z => - Work.Spaces.Zop^[k] h z) := by rw [ihk]
          _ = fun z => - Work.Spaces.Zop (Work.Spaces.Zop^[k] h) z := Zop_neg_fun _
          _ = fun z => - Work.Spaces.Zop^[k + 1] h z := by
                rw [Function.iterate_succ_apply' Work.Spaces.Zop k h]

/-! ## The relation between the iterates of `3/(1+z)` and of `z/(1+z)` -/

/-- For order `b ≥ 1` and `z > -1` (where `1/(1+z) = 1 - z/(1+z)`), the `b`-th `Zop`-iterate
of `3/(1+z)` is `-3` times the `b`-th iterate of `z/(1+z)`. -/
lemma Zop_iter_three_div_eq (b : ℕ) (hb : 1 ≤ b) {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z
      = -3 * Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z := by
  have hconst : (fun z : ℝ => 3 / (1 + z)) = fun z => 3 * (1 / (1 + z)) := by
    funext z
    rw [div_eq_mul_inv, one_div]
  have hcongr : Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z
      = Work.Spaces.Zop^[b] (fun z : ℝ => 1 - z / (1 + z)) z :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi
      (fun w hw => by
        have hw1 : (1 : ℝ) + w ≠ 0 := by
          have := Set.mem_Ioi.mp hw
          linarith
        field_simp
        ring)
      hz
  have hstep := Zop_iter_const_sub_fun (1 : ℝ) (fun z : ℝ => z / (1 + z)) b hb
  have hcm : Work.Spaces.Zop^[b] (fun z : ℝ => 3 * (1 / (1 + z))) z
      = 3 * Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z := by
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
  calc Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z
      = Work.Spaces.Zop^[b] (fun z : ℝ => 3 * (1 / (1 + z))) z := by rw [hconst]
    _ = 3 * Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z := hcm
    _ = 3 * Work.Spaces.Zop^[b] (fun z : ℝ => 1 - z / (1 + z)) z := by rw [hcongr]
    _ = 3 * (- Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z) := by rw [hstep]
    _ = -3 * Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z := by ring

/-! ## The bound -/

theorem PhiZopBound : ∀ (b : ℕ) (hb : b ≤ 4) (z : ℝ), 0 ≤ z →
    |Work.Spaces.Zop^[b] (fun z => 3 / (1 + z)) z| ≤ 100 := by
  intro b hb z hz
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    have h1 : (0 : ℝ) < 1 + z := by linarith
    have h2 : 3 / (1 + z) ≤ 3 := by
      rw [div_le_iff₀ h1]
      linarith
    have h3 : 0 ≤ 3 / (1 + z) := by positivity
    rw [Function.iterate_zero_apply, abs_of_nonneg h3]
    linarith
  · rw [Zop_iter_three_div_eq b hbpos (by linarith)]
    have hbnd : |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z| ≤ 1 := by
      rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b
        (fun z : ℝ => z / (1 + z))]
      exact Work.FTS.NonlinRows.NRow10aux.phiSelf_DzdIter_bound b hb z hz
    rw [abs_mul, show |(-3 : ℝ)| = 3 by norm_num]
    nlinarith [abs_nonneg (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z)]

end Work.FTS.FinalClock
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.fk_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.N4Fields

set_option autoImplicit false

theorem fk_field {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.RegQ α 4 g → Work.Construction.L12 g 0 = 0 → Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧ Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z) ≤ C * Work.FTS.Nonlin.Xn α g := by
  -- the two universal constants: `∫_θ K(θ)²` and `∫_θ sin(2θ)^{-η}`
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  refine ⟨Real.sqrt (5 * AK * Cθ) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (5 * AK * Cθ)
    linarith
  intro α hαIoc g hreg _
  obtain ⟨hαpos, hαα₂⟩ := Set.mem_Ioc.mp hαIoc
  have hα1 : α ≤ 1 := le_trans hαα₂ hα₂1
  obtain ⟨hsm, hmem, -⟩ := hreg
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang g 0 z with hudef
  -- ## the a.e. identity `D_z^i (FK g) = Qang g i` for `i ≤ 4`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang g i z := by
    filter_upwards [DzdIter_Qang_ae hsm hmem, MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 4 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 5))]
  -- ## the per-slot integrability and bound
  have hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi
    exact (Qang_sq_w_sq_integral hαpos hα1 hsm hmem hi).1.congr (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 4 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ AK * Work.Spaces.HkSq α 4 g := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (Qang_sq_w_sq_integral hαpos hα1 hsm hmem hi).2
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 5 * (AK * Work.Spaces.HkSq α 4 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int]
    calc ∑ i ∈ Finset.range 5, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, (AK * Work.Spaces.HkSq α 4 g) :=
          Finset.sum_le_sum fun i hi => hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * (AK * Work.Spaces.HkSq α 4 g) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the `ℋ⁴`-energy and the norm bound
  have hHkSq : Work.Spaces.HkSq α 4 (fun z θ => u z) = (∫ z in Work.Spaces.Iz,
        ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 4 (fun z θ => u z) ≤ (5 * AK * Cθ) * Work.Spaces.HkSq α 4 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => u z)
      ≤ Real.sqrt (5 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
    have h5 : 0 ≤ 5 * AK * Cθ := by nlinarith
    calc Work.FTS.Nonlin.Xn α (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((5 * AK * Cθ) * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (5 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
          rw [Real.sqrt_mul h5]
          rfl
  -- ## membership in `ℋ⁴`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 4 (fun z θ => u z) := by
    constructor
    · intro z hz
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun (f := fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## `FK g` is the radial function `u`
  have hfun : (fun z (_ : ℝ) => Work.Construction.FK g z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHkMem
  · rw [hfun]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

end Work.FTS.Nonlinear.N4Fields
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.N4Fields

set_option maxHeartbeats 1600000

/-! ## `SmoothInt` is stronger than `SmoothQuad`

`SmoothInt f` is `C^⊤` (analytic order) on the open strip `(-1,∞) × (0,π/2)` plus a
`z`-smoothness conjunct; `SmoothQuad f` is `C^∞` (genuine smooth order
`Work.Stability.smoothOrder = ∞ ≤ ⊤`) on the same strip, so the projection is immediate. -/


/-! ## The mixed-derivative pointwise bound, with `SmoothQuad` in place of pointwise smoothness

This is `Work.FTS.Nonlinear.N4Fields.wang_mixed_bound` with its hypothesis
`∀ θ, ContDiffAt ℝ ⊤ a θ` replaced by `SmoothQuad (fun _ θ => a θ)`: that hypothesis is used
only to produce `SmoothQuad (fun _ θ => a θ)` (see `hfq` below), which is exactly the data the
`θ`-Leibniz expansion `sqm_pz_DthIter_mul_le_4` consumes. -/


/-! ## The field lemma -/


end Work.FTS.Nonlinear.N4Fields
end
