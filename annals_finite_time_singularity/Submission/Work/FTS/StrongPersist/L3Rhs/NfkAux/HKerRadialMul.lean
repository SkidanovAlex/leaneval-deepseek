/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial multiplication `r ↦ r · h`, `h(z) = z/(1+z)²`, in `ℋ⁴`

`Work.FTS.StrongPersist.L3Rhs.NfkAux.HKerRadialMul`: multiplication of a radial
`ℋ⁴`-datum by the fixed profile `hKer z = z/(1+z)²` preserves `ℋ⁴`, with a constant that is
*independent of `α`*, and keeps every `D_z`-iterate up to order `4` continuous on `(0,∞)`.

The mathematical content is the multiplier lemma of §7 of the paper: since `hKer` is smooth
on `[0,∞)` with **bounded** iterated `D_z = z∂_z`-derivatives, the Leibniz rule
`D_z^i (hKer · r) = Σ_b C(i,b) (D_z^b hKer)(D_z^{i-b} r)` and the binomial Cauchy–Schwarz
estimate `Work.FTS.StrongPersist.L3Aux.zmul_pt` give the pointwise domination

  `HkIntegrand α 4 (hKer·r) z θ ≤ zmulConst 4·(1+K)²·HkIntegrand α 4 r z θ`

on the closed quadrant (`K` the uniform bound on the `D_z`-iterates of `hKer`).  Because the
two weights `w`, `Wt α` are the *same* on both sides, the constant is universal in `α`; the
domination is then integrated (`Work.FTS.LocData.HkMem_of_majorant` for the honesty and two
monotone integral comparisons for `HkSq`).

The remaining conjunct — continuity of the iterates `D_z^b (r·h)` — follows from the block
continuity of the uncurried product on the open quadrant
(`Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn`), the product being `C⁴`
there because `r` is `C⁴` on `(0,∞)` and `hKer` is analytic on `(-1,∞)`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## A pointwise domination transfers to `HkSq` -/

/-- A pointwise domination of the `ℋᵏ`-integrand on the closed quadrant, with the integrand of
`f` integrable, transfers to `HkSq` (both sides being iterated integrals). -/
private theorem hkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkSq α k g ≤ C * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α k f z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
        ((hmf.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ))
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (hmf.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

/-! ## The profile `h(z) = z/(1+z)²` -/

/-- `hKer = (1/2)·(2z/(1+z)²)`. -/
private theorem hKer_eq_half_two_z_div :
    Work.Spaces.hKer = fun z => (1 / 2 : ℝ) * (2 * z / (1 + z) ^ 2) := by
  funext w
  rw [Work.Spaces.hKer_apply]
  ring

/-- `hKer` is `C⁴` on `(0,∞)`. -/
private theorem hKer_contDiffOn_four : ContDiffOn ℝ 4 Work.Spaces.hKer (Set.Ioi 0) := by
  rw [hKer_eq_half_two_z_div]
  have h : ContDiffOn ℝ 4 (fun z : ℝ => (1 / 2 : ℝ) * (2 * z / (1 + z) ^ 2))
      (Set.Ioi 0) := by
    refine ((contDiffOn_const.mul Work.FTS.StrongPersist.L3Aux.contDiffOn_two_z_div).mono
      ?_).of_le le_top
    intro z hz
    have hz' : (-1 : ℝ) < z := by have := Set.mem_Ioi.mp hz; linarith
    exact Set.mem_Ioi.mpr hz'
  exact h

/-- **The `D_z`-iterates of `hKer` are bounded on `(0,∞)` by `24000`.**  This is the profile
bound `Work.FTS.StrongPersist.L3Aux.zslot_supBound` for `2z/(1+z)²`, divided by the factor
`2` (`Zop_iter_const_mul`). -/
private theorem zop_hKer_bound :
    ∀ b ≤ 4, ∀ z : ℝ, 0 < z → |Work.Spaces.Zop^[b] Work.Spaces.hKer z| ≤ 24000 := by
  intro b hb z hz
  rw [hKer_eq_half_two_z_div,
    Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul b (1 / 2 : ℝ)
      (fun z => 2 * z / (1 + z) ^ 2),
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b
      (fun z => 2 * z / (1 + z) ^ 2)]
  have h1 := Work.FTS.StrongPersist.L3Aux.zslot_supBound b hb z (le_of_lt hz) (π / 4)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rw [Work.Elliptic.DzIter_rad] at h1
  linarith

/-! ## Continuity of the iterates of `r · h` -/

/-- **Every `D_z`-iterate of `r·hKer` (of order `≤ 4`) is continuous on `(0,∞)`**, for `r` of
class `C⁴` on `(0,∞)`: the uncurried product is `C⁴` on the open quadrant, so all its mixed
blocks are continuous there (`blocksCont_of_contDiffOn`), and the `θ`-slices of the pure
`D_z`-blocks give the one-dimensional statement at `θ = π/4`. -/
private theorem dzdIter_mul_hKer_continuousOn {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ 4 r (Set.Ioi 0)) :
    ∀ b ≤ 4, ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b (fun z : ℝ => r z * Work.Spaces.hKer z) z)
      (Set.Ioi 0) := by
  intro b hb
  have h1 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => r p.1) Work.Construction.Qd :=
    hr.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have h2 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Spaces.hKer p.1) Work.Construction.Qd :=
    hKer_contDiffOn_four.comp contDiffOn_fst
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hFsm : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ : ℝ => r z * Work.Spaces.hKer z)) Work.Construction.Qd :=
    h1.mul h2
  have hBc := Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn hFsm
  have h0b : 0 + b ≤ 4 := by simpa using hb
  have hb0 : ContinuousOn
      (Function.uncurry (Work.Spaces.DzIter b (fun z θ : ℝ => r z * Work.Spaces.hKer z)))
      Work.Construction.Qd := by
    have h := hBc 0 b h0b
    rwa [Work.Spaces.mixed_zero_right] at h
  have hcomp : ContinuousOn
      (fun z : ℝ => Work.Spaces.DzIter b (fun z θ : ℝ => r z * Work.Spaces.hKer z) z (π / 4))
      (Set.Ioi 0) := by
    have hmap : ContinuousOn (fun z : ℝ => ((z, π / 4) : ℝ × ℝ)) (Set.Ioi 0) :=
      continuousOn_id.prodMk continuousOn_const
    have hmem : ∀ z ∈ Set.Ioi (0 : ℝ), ((z, π / 4) : ℝ × ℝ) ∈ Work.Construction.Qd :=
      fun z hz => ⟨hz, ⟨by positivity, by linarith [Real.pi_pos]⟩⟩
    refine (hb0.comp hmap hmem).congr (fun z _ => ?_)
    rfl
  refine hcomp.congr (fun z _ => ?_)
  exact (Work.Elliptic.DzIter_rad (fun z => r z * Work.Spaces.hKer z) b z (π / 4)).symm

/-! ## The main statement -/

theorem HKerRadialMul : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ r : ℝ → ℝ,
    ContDiffOn ℝ 4 r (Set.Ioi 0) →
    Work.Spaces.HkMem α 4 (fun z _ => r z) →
    (∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b (fun z : ℝ => r z * Work.Spaces.hKer z) z)
      (Set.Ioi 0)) ∧
    Work.Spaces.HkMem α 4 (fun z _ => r z * Work.Spaces.hKer z) ∧
    Work.Spaces.HkSq α 4 (fun z _ => r z * Work.Spaces.hKer z)
      ≤ K * Work.Spaces.HkSq α 4 (fun z _ => r z) := by
  refine ⟨Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2,
    mul_pos (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 4) (by norm_num), ?_⟩
  intro α hα hα1 r hr hrmem
  -- the two shapes of the product
  have hfun : (fun z θ : ℝ => Work.Spaces.hKer z * r z)
      = fun z (_ : ℝ) => r z * Work.Spaces.hKer z := by
    funext z θ
    exact mul_comm _ _
  have hCnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2 :=
    (mul_pos (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 4) (by norm_num)).le
  -- the pointwise domination on the open quadrant
  have hpt_open : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
      Work.Spaces.HkIntegrand α 4 (fun z θ : ℝ => Work.Spaces.hKer z * r z) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
          * Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
    intro z hz θ
    refine Work.FTS.StrongPersist.L3Aux.zmul_pt α 4 Work.Spaces.hKer (fun z (_ : ℝ) => r z)
      (by norm_num) (fun b hb => zop_hKer_bound b hb z hz) ?_ ?_
    · intro i hi
      exact Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i Work.Spaces.hKer
        (fun z (_ : ℝ) => r z) isOpen_Ioi
        (hKer_contDiffOn_four.of_le (Nat.cast_le.mpr hi))
        (hr.of_le (Nat.cast_le.mpr hi)) z hz
    · intro j i hi hij
      exact Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i Work.Spaces.hKer
        (fun z (_ : ℝ) => r z) isOpen_Ioi
        (hKer_contDiffOn_four.of_le (Nat.cast_le.mpr (by omega : j ≤ 4)))
        (by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
          rw [Work.Elliptic.DthIter_rad_succ]
          exact contDiffOn_const) z hz
  -- and on the closed quadrant
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ : ℝ => Work.Spaces.hKer z * r z) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
          * Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      rw [Work.FTS.LocData.HkIntegrand_zero_fst]
      exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α 4 _ 0 θ)
    · exact hpt_open z hzpos θ
  -- continuity of the integrand of the product on the open quadrant
  have hFsm : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.hKer z * r z)) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0 :=
      hr.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    have h2 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Spaces.hKer p.1)
        Work.FTS.EllipticEst.Q0 :=
      hKer_contDiffOn_four.comp contDiffOn_fst
        (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    exact h2.mul h1
  have hBc := Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn hFsm
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (fun z θ : ℝ => Work.Spaces.hKer z * r z) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont hBc α
  -- honesty of the product
  have hmemProd : Work.Spaces.HkMem α 4 (fun z θ : ℝ => Work.Spaces.hKer z * r z) := by
    refine Work.FTS.LocData.HkMem_of_majorant α 4 hcont ?_ ?_ hpt
    · intro z hz
      exact (hrmem.1 z hz).const_mul _
    · have h2 := (hrmem.2).const_mul
          (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
      have heq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
              * Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ)
          = fun z : ℝ =>
              (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2)
                * ∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [heq]
      exact h2
  -- the `HkSq` estimate
  have hsq := hkSq_le_of_integrand_le α 4
    (Work.FTS.StrongPersist.L3Aux.zmulConst 4 * (1 + 24000) ^ 2) hrmem hpt
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    exact dzdIter_mul_hKer_continuousOn hr b hb
  · rw [← hfun]
    exact hmemProd
  · rw [← hfun]
    exact hsq

end Work.FTS.StrongPersist.L3Rhs.NfkAux
