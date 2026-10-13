/-
# `Work.FTS.StrongPersist.N6_fkH` — the `fkH` clause of `N6Norm`

The angular moment `FK g z = ∫_θ K(θ)·g(z,θ) dθ` is the radial function `Qang g 0`.  This
module proves that for a datum `g` of the **open-quadrant** class `Work.FTS.VocabO.HQo α 6 g`
(`SmoothOpen g` + honest `HkMem α 6 g`) with `L₁₂(g)(0) = 0`, the radial function
`z ↦ FK g z` lies in `ℋ⁶` and

  `|FK g|_{ℋ⁶} ≤ Xi · α^{-Cpow} · |g|_{ℋ⁶}`

with a constant independent of `α ∈ (0, α₂]` and of `g`.  This is the field `N6Norm.fkH` of
`Submission/Work/FTS/StrongPersist/Defs.lean`.

The argument is the level-four analogue `Work.FTS.OpenPkg.fkH_field` with `4 → 6`: a function of
`z` alone has no angular derivatives, so only the pure `D_z`-summands of
`HkIntegrand α 6 (fun z _ => FK g z)` survive (`Work.FTS.H2.HkIntegrand_rad'`,
`Work.Elliptic.HkSq_rad`, both stated for arbitrary `k`), and each of them is the angular
moment `D_z^i (FK g) = Qang g i` (exactly for `i ≤ 5`, almost everywhere for `i = 6`).  Cauchy
Schwarz in `θ` bounds every summand by `(∫_θ K²)·HkSq α 6 g`.  The zero-mode hypothesis
`L₁₂(g)(0) = 0` is not needed for this estimate (unlike the `l12H` clause, no Hardy inequality
is used).

The two level-six analytic inputs are separated out as `QangSq6Full` (the weighted `L²`-bound
for the angular moments, `i ≤ 6`) and `QangAe6` (the a.e. identification of the `D_z`-iterates
of `Qang g 0` with the angular moments, `i ≤ 6`); `N6_fkH_of` below is the whole argument
conditional on them, and `N6_fkH` is the unconditional statement.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.ClauseFields
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.StrongPersist.QangAe6
import Submission.Work.FTS.StrongPersist.QangDiff6
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The angular moment of the construction is the zeroth angular moment of the elliptic
chapter**: `FK g z = Qang g 0 z`.  (The two definitions differ only in the order of the factors
and in the name of the angular kernel, `Work.Spaces.K` vs `Work.Elliptic.Ktheta`, which are
equal.) -/
theorem FK_eq_Qang (g : ℝ → ℝ → ℝ) :
    (fun z (_ : ℝ) => Work.Construction.FK g z)
      = fun z (_ : ℝ) => Work.Elliptic.Qang g 0 z := by
  funext z θ
  simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
  rw [← Work.Elliptic.Ktheta_eq_K]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- **The `ℋ⁶`-bound for the angular moment `FK g` from the two level-six inputs.**

* `hSq` is the weighted `L²`-bound for the angular moments `Qang g i`, `i ≤ 6` (proved in
  `Submission/Work/FTS/StrongPersist/QangSq6Full.lean` as `QangSq6Full`);
* `hAe` is the a.e. identification `D_z^i (Qang g 0) = Qang g i` for `i ≤ 6` (proved in
  `Submission/Work/FTS/StrongPersist/QangAe6.lean` as `QangAe6`). -/
theorem N6_fkH_of
    (hSq : ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 6 g → ∀ i : ℕ, i ≤ 6 →
        MeasureTheory.IntegrableOn
            (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
          (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
            ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g)
    (hAe : ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 6 g →
      ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 7,
        Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z
          = Work.Elliptic.Qang g i z) :
    ∃ Xi Cpow α₂ : ℝ, 0 < Xi ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 6 g →
      Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 6 (fun z _ => Work.Construction.FK g z) ∧
      Work.FTS.StrongPersist.Xn6 α (fun z _ => Work.Construction.FK g z)
        ≤ Xi * α ^ (-Cpow) * Work.FTS.StrongPersist.Xn6 α g := by
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
  refine ⟨Real.sqrt (7 * AK * Cθ) + 1, 0, 1, ?_, le_refl 0, one_pos, ?_⟩
  · have h := Real.sqrt_nonneg (7 * AK * Cθ)
    linarith
  intro α hα g hg _
  obtain ⟨hsm, hmem⟩ := hg
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang g 0 z with hudef
  -- ## the a.e. identity `D_z^i (Qang g 0) = Qang g i` on `Iz`, `i ≤ 6`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 7,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang g i z := by
    filter_upwards [hAe α g hsm hmem, MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 7))]
  -- ## the per-slot integrability and bound
  have hInt : ∀ i : ℕ, i ≤ 6 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => (hSq α g hsm hmem i hi).1.congr (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 6 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ AK * Work.Spaces.HkSq α 6 g := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (hSq α g hsm hmem i hi).2
  have hsum_int : ∀ i ∈ Finset.range 7, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 7,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 7 * (AK * Work.Spaces.HkSq α 6 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 7) hsum_int]
    calc ∑ i ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 7, (AK * Work.Spaces.HkSq α 6 g) :=
          Finset.sum_le_sum fun i hi =>
            hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 7 * (AK * Work.Spaces.HkSq α 6 g) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the `ℋ⁶`-energy of the radial function and the norm bound
  have hHkSq : Work.Spaces.HkSq α 6 (fun z θ => u z) = (∫ z in Work.Spaces.Iz,
        ∑ i ∈ Finset.range 7,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 6 (fun z θ => u z)
      ≤ (7 * AK * Cθ) * Work.Spaces.HkSq α 6 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.FTS.StrongPersist.Xn6 α g := Real.sqrt_nonneg _
  have hXn : Work.FTS.StrongPersist.Xn6 α (fun z θ => u z)
      ≤ Real.sqrt (7 * AK * Cθ) * Work.FTS.StrongPersist.Xn6 α g := by
    have h7 : 0 ≤ 7 * AK * Cθ := by nlinarith
    calc Work.FTS.StrongPersist.Xn6 α (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((7 * AK * Cθ) * Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (7 * AK * Cθ) * Work.FTS.StrongPersist.Xn6 α g := by
          rw [Real.sqrt_mul h7]
          rfl
  -- ## membership in `ℋ⁶`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 6 (fun z θ => u z) := by
    constructor
    · intro z _
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 6 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 7) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun
          (f := fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 7,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 6 u z hθ)]
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
    rw [neg_zero, Real.rpow_zero, mul_one]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

/-- **The `fkH` clause of `N6Norm`**: the angular moment `FK g` of an honest `ℋ⁶`-datum with
vanishing zero mode is an `ℋ⁶`-function, controlled by the `ℋ⁶`-norm of the datum with a
constant independent of `α ∈ (0, α₂]` and of `g`.  (The witness has `Cpow = 0`.) -/
theorem N6_fkH : ∃ Xi Cpow α₂ : ℝ, 0 < Xi ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 6 g →
      Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 6 (fun z _ => Work.Construction.FK g z) ∧
      Work.FTS.StrongPersist.Xn6 α (fun z _ => Work.Construction.FK g z)
        ≤ Xi * α ^ (-Cpow) * Work.FTS.StrongPersist.Xn6 α g :=
  N6_fkH_of
    (fun α g hO hmem => QangSq6Full hO hmem)
    (fun α g hO hmem => QangAe6 hO hmem)

end Work.FTS.StrongPersist
