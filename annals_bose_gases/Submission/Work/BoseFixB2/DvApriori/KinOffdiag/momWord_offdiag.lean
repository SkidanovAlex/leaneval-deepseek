import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.DvApriori.boxState_fibre_eq
import Submission.Work.BoseFixB2.DvApriori.exists_diff_slot
import Submission.Work.BoseFixB2.DvApriori.gapWord_fibre_offdiag
import Submission.Work.BoseFixB2.DvApriori.integrable_momBil_fibre
import Submission.Work.BoseFixB2.DvApriori.momForm_polar_diff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.KinOffdiag.momWord_offdiag`

The **off-diagonal vanishing of the large-momentum kinetic word on the slot-`j` fibre of two
joint sector projections**: for sectors `S ≠ T` that *both* contain the slot `j`,

`∫_{abox n ℓ} 1_{Λ(0)}(x_j)·[momWord ℓ d εT b 0 (fibre_j (E_SΦ + E_TΦ) x)
    − momWord ℓ d εT b 0 (fibre_j (E_SΦ − E_TΦ) x)] dx = 0`.

This file is a *self-contained* proof: the three auxiliary analytic lemmas (continuity of the
`p`-mode along a fibre, the slot-mean vanishing of a `kinFT` over the cube, and the vanishing of
the localised state of a sector that omits the slot `j`) and the `p`-wise vanishing of the box
integral are all proved here rather than imported.

## The proof

1. `momWord = c·momForm` (`c = b·εT·(dℓ)⁻²`) with
   `momForm ℓ d 0 (f+g) − momForm ℓ d 0 (f−g) = 4 momBil ℓ d f g` (`momForm_polar_diff`), and the
   fibre is linear in the state: the integrand polarises into `4c·momBil` of the two fibres.
2. `momBil` is the `p`-integral of `momProj ℓ d p·⟪kinFT (θ₀Q₀f) p, kinFT (θ₀Q₀g) p⟫_ℝ`, so the
   box integral becomes an iterated `(x,p)`-integral; Fubini applies with the integrability
   `integrable_momBil_fibre`, multiplied by the bounded measurable factor `θ₀(x_j)`.
3. For every frequency `p` the `x`-integral vanishes: since `S ≠ T` differ in a slot `i ≠ j`
   (`exists_diff_slot`), the `T`-side state is independent of the slot-`i` variable
   (`Sector.constIn_jointProj`) while the `S`-side state has vanishing slot-`i` mean
   (`integral_fibre_jointProj_eq_zero`).  Peeling the slot `i` out of the box integral
   (`abox_integral_peel`) and using that `⟪·, v⟫` is continuous linear
   (`ContinuousLinearMap.integral_comp_comm`), the inner integral collapses to
   `⟪∫_y (slot-i fibre of the S-amplitude), v⟫`, whose first entry is `0` by the slot-`i`
   mean vanishing of the amplitude.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseFixB2.DvApriori.KinOffdiag

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. Elementary fibre algebra -/

/-- The slot-`j` fibre of a smooth state is a smooth one-body state. -/
theorem contDiff_fibre' {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (x : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n j Ψ x) :=
  hΨ.comp (contDiff_update (⊤ : ℕ∞) x j)

/-- `z ↦ Function.update x j z` is continuous (the other slots are frozen). -/
theorem continuous_update_const {n : ℕ} (j : Fin n) (x : Submission.BoseGases.X n) :
    Continuous fun z : EuclideanSpace ℝ (Fin 3) => Function.update x j z := by
  have h2 : Continuous fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      Function.update p.1 j p.2 := continuous_update j
  exact h2.comp (continuous_const.prodMk continuous_id)

/-- The anchored-box indicator is bounded by one. -/
theorem abs_indU_le_one (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseKinLoc.indU ℓ 0 z| ≤ 1 := by
  rw [Work.BoseKinLoc.indU]
  by_cases h : z ∈ Work.BoseKinLoc.lamBox ℓ 0
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

/-- **The `p`-mode of an anchored localised state is the restricted integral**: for a real
one-body function `g`, `kinFT (θ₀·g) p = ∫_{acube ℓ} e^{-i⟪p,z⟫} g(z) dz`. -/
theorem kinFT_indU_mul_eq {ℓ : ℝ} (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
        ((g z : ℝ) : ℂ)) p
      = ∫ z in Submission.BoseGases.acube ℓ,
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((g z : ℝ) : ℂ) := by
  classical
  rw [Submission.BoseGases.kinFT]
  have hfun : (fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
          ((((Work.BoseKinLoc.indU ℓ 0 y : ℝ)) : ℂ) * ((g y : ℝ) : ℂ)))
      = (Submission.BoseGases.acube ℓ).indicator
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((g z : ℝ) : ℂ)) := by
    funext y
    rw [Work.BoseKinLoc.indU, Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube]
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; simp
  rw [hfun, MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]

/-! ## 2. The localised state of a sector missing the slot `j` vanishes -/

/-- **`boxState ℓ 0 (fibre_j (E_SΦ) x) = 0` when `j ∉ S`**: the slot-`j` operator of the sector
`E_S` is `P_j`, so `Q_j E_S = 0` and the mean-free part of the fibre vanishes identically. -/
theorem boxState_fibre_eq_zero_of_notMem {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {S : Finset ℕ} (hjS : (j : ℕ) ∉ S) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.Kinetic.boxState ℓ 0
      (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x) = 0 := by
  have haQ : Submission.BoseGases.aQ ℓ j (Work.BoseFixB2.jointProj ℓ S Φ) = 0 := by
    have h := Work.BoseFixB2.Sector.aP_jointProj_eq_self (ℓ := ℓ) hℓ j.isLt hjS hΦ
    funext y
    simp [Submission.BoseGases.aQ, h]
  have hQ : Work.BoseKinLoc.Qfree ℓ 0
      (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x) = 0 := by
    rw [Work.BoseFixB2.DvApriori.boxState_Qfree_fibre j x, haQ]
    rfl
  funext z
  simp only [Work.BoseKinLoc.Kinetic.boxState, Pi.zero_apply]
  rw [congrFun hQ z]
  simp

/-- **`ConstIn` transfers to slot-`j` fibres**: if `Ψ` does not depend on the slot `i` and
`i ≠ j`, then the slot-`j` fibre of `Ψ` does not change under an update of the slot-`i`
variable. -/
theorem fibre_update_eq_of_constIn {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
      Ψ (Function.update x i z) = Ψ x)
    (x : Submission.BoseGases.X n) (y : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.fibre n j Ψ (Function.update x i y) = Work.BoseKinLoc.fibre n j Ψ x := by
  funext z
  simp only [Work.BoseKinLoc.fibre]
  rw [Function.update_comm hij y z x]
  exact hΨ (Function.update x j z) y

/-- The same invariance at the level of the localised box state. -/
theorem boxState_fibre_update_eq_of_constIn {ℓ : ℝ} {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
      Ψ (Function.update x i z) = Ψ x)
    (x : Submission.BoseGases.X n) (y : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j Ψ (Function.update x i y))
      = Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) := by
  rw [fibre_update_eq_of_constIn hij hΨ x y]

/-! ## 3. Continuity of the `p`-mode along a fibre -/

/-- **The `p`-mode of the localised state of a slot-`j` fibre is continuous in the
configuration.** -/
theorem continuous_kinFT_boxState_fibre {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j Ψ x)) p) := by
  set m : Submission.BoseGases.X n → ℝ :=
    fun x => (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, Ψ (Function.update x j z) with hm
  have hmc : Continuous m := by
    rw [hm]
    refine Continuous.mul continuous_const ?_
    refine continuous_parametric_integral_of_continuous (f := fun (x : Submission.BoseGases.X n)
      (z : EuclideanSpace ℝ (Fin 3)) => Ψ (Function.update x j z)) ?_
      (Submission.BoseGases.acube_compact hℓ)
    exact hΨ.comp (continuous_fst.update j continuous_snd)
  have hpt : ∀ x : Submission.BoseGases.X n,
      Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p
        = ∫ z in Submission.BoseGases.acube ℓ,
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              ((Ψ (Function.update x j z) - m x : ℝ) : ℂ) := by
    intro x
    rw [show Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)
        = fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
            ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z : ℝ) : ℂ)
        from rfl]
    rw [kinFT_indU_mul_eq (ℓ := ℓ)
      (g := Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)) p]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) ?_
    intro z _
    congr 1
    simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BSKinetic.bsMean,
      Work.BoseKinLoc.fibre, smul_zero, zero_add, hm]
  refine (continuous_parametric_integral_of_continuous (f := fun (x : Submission.BoseGases.X n)
      (z : EuclideanSpace ℝ (Fin 3)) => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((Ψ (Function.update x j z) - m x : ℝ) : ℂ)) ?_
      (Submission.BoseGases.acube_compact hℓ)).congr (fun x => (hpt x).symm)
  have hsub : Continuous fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      (Ψ (Function.update q.1 j q.2) - m q.1 : ℝ) :=
    (hΨ.comp (continuous_fst.update j continuous_snd)).sub (hmc.comp continuous_fst)
  have hinner : Continuous fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      (inner ℝ p q.2 : ℝ) :=
    continuous_inner.comp (continuous_const.prodMk continuous_snd)
  have hexp : Continuous fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.comp hinner)).neg)
  exact hexp.mul (Complex.continuous_ofReal.comp hsub)

/-! ## 4. The slot-mean vanishing of a `kinFT` over the cube -/

/-- **The `y`-average of the slot-`i`-updated amplitude vanishes** when the state has zero
slot-`i` mean: exchanging the `y`- and `z`-integrations reduces it to
`∫_y Ψ(update (update x i y) j z) dy = ∫_y Ψ(update (update x j z) i y) dy = 0`. -/
theorem integral_kinFT_indU_fibre_slot_mean_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (hmean : ∀ w : Submission.BoseGases.X n,
      (∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update w i y)) = 0)
    (x : Submission.BoseGases.X n) (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.kinFT (fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
        ((Work.BoseKinLoc.fibre n j Ψ (Function.update x i y) z : ℝ) : ℂ)) p) = 0 := by
  set f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ := fun y z =>
    Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
      ((Ψ (Function.update (Function.update x i y) j z) : ℝ) : ℂ) with hf
  -- the amplitudes, written as their defining integrals
  have hrew : ∀ y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT (fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
        ((Work.BoseKinLoc.fibre n j Ψ (Function.update x i y) z : ℝ) : ℂ)) p
        = ∫ z in Submission.BoseGases.acube ℓ, f y z := by
    intro y
    rw [kinFT_indU_mul_eq (ℓ := ℓ) (g := Work.BoseKinLoc.fibre n j Ψ (Function.update x i y)) p]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) ?_
    intro z _
    rfl
  -- joint integrability over the product of the two cubes
  have hjoint : Continuous (Function.uncurry f) := by
    have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) := by
      have hi : Continuous fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          (inner ℝ p q.2 : ℝ) :=
        continuous_inner.comp (continuous_const.prodMk continuous_snd)
      exact Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp hi)).neg)
    have hupd2 : Continuous fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        (Function.update (Function.update x i q.1) j q.2 : Submission.BoseGases.X n) := by
      have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          (Function.update x i q.1 : Submission.BoseGases.X n) :=
        continuous_const.update i continuous_fst
      exact h1.update j continuous_snd
    have h2 : Continuous fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ((Ψ (Function.update (Function.update x i q.1) j q.2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hΨ.comp hupd2)
    exact h1.mul h2
  have hint : Integrable (Function.uncurry f)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact
      ((Submission.BoseGases.acube_compact hℓ).prod (Submission.BoseGases.acube_compact hℓ))
      hjoint.continuousOn
  -- the `z`-sections vanish
  have hzero : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube ℓ, f y z) = 0 := by
    intro z
    have h1 : (∫ y in Submission.BoseGases.acube ℓ, f y z)
        = Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            ∫ y in Submission.BoseGases.acube ℓ,
              ((Ψ (Function.update (Function.update x i y) j z) : ℝ) : ℂ) := by
      rw [hf]
      exact MeasureTheory.integral_const_mul _ _
    rw [h1]
    have h2 : (∫ y in Submission.BoseGases.acube ℓ,
          ((Ψ (Function.update (Function.update x i y) j z) : ℝ) : ℂ))
        = ((∫ y in Submission.BoseGases.acube ℓ,
            Ψ (Function.update (Function.update x i y) j z) : ℝ) : ℂ) := by
      refine (Complex.ofRealCLM.integral_comp_comm (φ := fun y : EuclideanSpace ℝ (Fin 3) =>
        Ψ (Function.update (Function.update x i y) j z)) ?_).trans ?_
      · refine ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ) ?_
        exact (hΨ.comp ((continuous_const.update i continuous_id).update j
          continuous_const)).continuousOn
      · rfl
    rw [h2]
    have h3 : (∫ y in Submission.BoseGases.acube ℓ,
          Ψ (Function.update (Function.update x i y) j z))
        = ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update (Function.update x j z) i y) := by
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) ?_
      intro y _
      beta_reduce
      rw [Function.update_comm hij y z x]
    rw [h3, hmean (Function.update x j z)]
    simp
  rw [show (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.kinFT (fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
          ((Work.BoseKinLoc.fibre n j Ψ (Function.update x i y) z : ℝ) : ℂ)) p)
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, f y z
      from MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun y _ => hrew y)]
  rw [MeasureTheory.integral_integral_swap hint]
  rw [show (∫ z in Submission.BoseGases.acube ℓ,
        ∫ y in Submission.BoseGases.acube ℓ, f y z)
      = ∫ z in Submission.BoseGases.acube ℓ, (0 : ℂ)
      from MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun z _ => hzero z)]
  simp

/-! ## 5. The `p`-wise vanishing of the box integral -/

/-- **The box integral of the `θ₀`-weighted pairing of two `kinFT` amplitudes vanishes** when the
two states are separated in the slot `i` (`i ≠ j`): the `S`-side has vanishing slot-`i` mean and
the `T`-side is independent of the slot-`i` variable. -/
theorem integral_indU_kinFT_fibre_eq_zero {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (i : Fin n) (hij : i ≠ j) (hiS : (i : ℕ) ∈ S) (hiT : (i : ℕ) ∉ T) :
    ∀ p : EuclideanSpace ℝ (Fin 3),
      (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))) = 0 := by
  intro p
  by_cases hjS : (j : ℕ) ∈ S
  · by_cases hjT : (j : ℕ) ∈ T
    · -- ================== main case: `j ∈ S` and `j ∈ T` ==================
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fin.pos j))
      have hSc : Continuous (Work.BoseFixB2.jointProj ℓ S Φ) :=
        (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ).continuous
      have hTc : Continuous (Work.BoseFixB2.jointProj ℓ T Φ) :=
        (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ).continuous
      -- the slot-`i` mean of the `S`-side vanishes
      have hmeans : ∀ w : Submission.BoseGases.X (m + 1),
          (∫ y in Submission.BoseGases.acube ℓ,
            (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update w i y)) = 0 :=
        fun w => Work.BoseFixB2.DvApriori.integral_fibre_jointProj_eq_zero hℓ i hiS hΦ.continuous w
      -- the `T`-side is independent of the slot `i`
      have hConstT : ∀ (w : Submission.BoseGases.X (m + 1)) (z : EuclideanSpace ℝ (Fin 3)),
          (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update w i z)
            = (Work.BoseFixB2.jointProj ℓ T Φ) w :=
        fun w z => Work.BoseFixB2.Sector.constIn_jointProj hℓ i.isLt hiT hΦ.continuous w z
      set F : Submission.BoseGases.X (m + 1) → ℝ := fun x =>
        (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p)) with hF
      -- Step 1: the indicator `1_{Λ(0)}(x_j)` equals one on the box
      have hind : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x j) * F x)
          = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, F x := by
        refine MeasureTheory.setIntegral_congr_fun
          (Submission.BoseGases.abox_measurable (m + 1) ℓ) ?_
        intro x hx
        beta_reduce
        have hmem : x j ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
          rw [Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube]
          exact (Submission.BoseGases.mem_abox_iff (m + 1) ℓ x).mp hx j
        rw [Work.BoseKinLoc.indU, Set.indicator_of_mem hmem (fun _ => (1 : ℝ)), one_mul]
      rw [show (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p)))
          = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) * F x
        from rfl, hind]
      -- Step 2: integrability of `F` on the box and the peel at the slot `i`
      have hAS : Continuous (fun x : Submission.BoseGases.X (m + 1) =>
          Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p) :=
        continuous_kinFT_boxState_fibre hℓ j hSc p
      have hAT : Continuous (fun x : Submission.BoseGases.X (m + 1) =>
          Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p) :=
        continuous_kinFT_boxState_fibre hℓ j hTc p
      have hcont : Continuous F := by
        rw [hF]
        exact hAS.inner hAT
      have hIntF : IntegrableOn F (Submission.BoseGases.abox (m + 1) ℓ) volume :=
        hcont.continuousOn.integrableOn_compact (Submission.BoseGases.abox_compact (m + 1) hℓ)
      rw [Submission.BoseGases.abox_integral_peel (n := m) i F hIntF]
      -- Step 3: the inner integral vanishes for every `r`
      have hper : ∀ r : Submission.BoseGases.X m,
          (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
            F (Submission.BoseGases.kcInsN m i (y, r))) = 0 := by
        intro r
        set X0 : Submission.BoseGases.X (m + 1) := Submission.BoseGases.kcInsN m i (0, r) with hX0
        have hupd : ∀ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.kcInsN m i (y, r) = Function.update X0 i y := by
          intro y
          rw [hX0]
          exact Submission.BoseGases.kcInsN_update_zero i y r
        -- the `T`-side is constant in `y`
        have hTside : ∀ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ)
                (Function.update X0 i y))) p
              = Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ) X0)) p := by
          intro y
          rw [boxState_fibre_update_eq_of_constIn hij hConstT X0 y]
        -- the `S`-side, rewritten to the localised form
        have hSind : ∀ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                (Function.update X0 i y))) p
              = Submission.BoseGases.kinFT (fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
                  (((Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                    (Function.update X0 i y) z : ℝ)) : ℂ)) p := by
          intro y
          rw [Work.BoseFixB2.DvApriori.boxState_fibre_eq hℓ j hjS hΦ]
        -- the slot-`i` mean of the `S`-side kills the `y`-integral
        have hzeroA : (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                (Function.update X0 i y))) p) = 0 := by
          rw [show (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                    (Function.update X0 i y))) p)
              = ∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
                  Submission.BoseGases.kinFT (fun z =>
                    ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
                    (((Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                      (Function.update X0 i y) z : ℝ)) : ℂ)) p
            from MeasureTheory.setIntegral_congr_fun
              (Submission.BoseGases.acube_measurable ℓ) (fun y _ => hSind y)]
          exact integral_kinFT_indU_fibre_slot_mean_eq_zero hℓ hij hSc hmeans X0 p
        -- integrability of the `y ↦ S`-side amplitude on the cube
        have hIntA : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                (Function.update X0 i y))) p)
            (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
          refine ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ) ?_
          have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                  (Function.update X0 i y))) p) :=
            (continuous_kinFT_boxState_fibre hℓ j hSc p).comp
              (continuous_update_const i X0)
          exact h1.continuousOn
        -- the pointwise reduction of the integrand
        have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
            F (Submission.BoseGases.kcInsN m i (y, r))
              = inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ) X0)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                    (Function.update X0 i y))) p) := by
          intro y
          simp only [hF]
          rw [hupd y, hTside y]
          exact real_inner_comm _ _
        -- the contraction of the `y`-integral against the (constant) `T`-amplitude
        have hCLM : (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ) X0)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                    (Function.update X0 i y))) p))
            = inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ) X0)) p)
              (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ S Φ)
                    (Function.update X0 i y))) p) := by
          simpa only [innerSL_apply_apply] using ContinuousLinearMap.integral_comp_comm
            (innerSL ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre (m + 1) j (Work.BoseFixB2.jointProj ℓ T Φ) X0)) p)) hIntA
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt), hCLM, hzeroA]
        simp
      rw [funext hper, MeasureTheory.integral_zero]
    · -- ================== degenerate case: `j ∉ T` ==================
      have hzero : (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
            (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))) = 0 := by
        funext x
        rw [boxState_fibre_eq_zero_of_notMem hℓ j hjT hΦ.continuous x,
          show Submission.BoseGases.kinFT (0 : EuclideanSpace ℝ (Fin 3) → ℂ) p = 0 by
            simp [Submission.BoseGases.kinFT]]
        simp
      rw [hzero]
      simp
  · -- ================== degenerate case: `j ∉ S` ==================
    have hzero : (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
          (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))) = 0 := by
      funext x
      rw [boxState_fibre_eq_zero_of_notMem hℓ j hjS hΦ.continuous x,
        show Submission.BoseGases.kinFT (0 : EuclideanSpace ℝ (Fin 3) → ℂ) p = 0 by
          simp [Submission.BoseGases.kinFT]]
      simp
    rw [hzero]
    simp

/-! ## 6. The off-diagonal vanishing -/

theorem momWord_offdiag {ℓ d εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (Work.BoseKinLoc.momWord ℓ d εT b 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.momWord ℓ d εT b 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  classical
  set A : Submission.BoseGases.X n → ℝ := Work.BoseFixB2.jointProj ℓ S Φ with hA
  set B : Submission.BoseGases.X n → ℝ := Work.BoseFixB2.jointProj ℓ T Φ with hB
  have hAc : ContDiff ℝ (⊤ : ℕ∞) A := by
    rw [hA]; exact Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ
  have hBc : ContDiff ℝ (⊤ : ℕ∞) B := by
    rw [hB]; exact Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ
  obtain ⟨i, hij, hmem⟩ := Work.BoseFixB2.DvApriori.exists_diff_slot j hS hT hjS hjT hST
  set c : ℝ := b * εT * (d * ℓ) ^ (-2 : ℤ) with hc
  -- ### the pointwise polarisation
  have hpt : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j (A + B) x)
         - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j (A - B) x))
      = (c * 4) * (Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseFixB2.DvApriori.momBil ℓ d (Work.BoseKinLoc.fibre n j A x)
            (Work.BoseKinLoc.fibre n j B x)) := by
    intro x
    have hsum : Work.BoseKinLoc.fibre n j (A + B) x
        = fun z => Work.BoseKinLoc.fibre n j A x z + Work.BoseKinLoc.fibre n j B x z := by
      funext z; simp only [Work.BoseKinLoc.fibre, Pi.add_apply]
    have hsub : Work.BoseKinLoc.fibre n j (A - B) x
        = fun z => Work.BoseKinLoc.fibre n j A x z - Work.BoseKinLoc.fibre n j B x z := by
      funext z; simp only [Work.BoseKinLoc.fibre, Pi.sub_apply]
    have hmw : Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j (A + B) x)
          - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j (A - B) x)
        = c * (Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n j (A + B) x)
            - Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n j (A - B) x)) := by
      simp only [Work.BoseKinLoc.momWord, hc]; ring
    rw [hmw, hsum, hsub,
      Work.BoseFixB2.DvApriori.momForm_polar_diff hℓ (contDiff_fibre' j hAc x)
        (contDiff_fibre' j hBc x)]
    ring
  -- ### step 1: pointwise polarisation inside the box integral
  have hstep1 :
      (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j (A + B) x)
         - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j (A - B) x)))
      = (c * 4) * (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseFixB2.DvApriori.momBil ℓ d (Work.BoseKinLoc.fibre n j A x)
            (Work.BoseKinLoc.fibre n j B x)) := by
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => hpt x)]
    rw [MeasureTheory.integral_const_mul]
  -- ### the `(x,p)`-integrand
  set K : Submission.BoseGases.X n → EuclideanSpace ℝ (Fin 3) → ℝ := fun x p =>
      Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
        (Work.BoseKinLoc.momProj ℓ d p *
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j A x)) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j B x)) p))) with hK
  -- ### step 2: unfold `momBil` into the `p`-integral
  have hstep2 : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseFixB2.DvApriori.momBil ℓ d (Work.BoseKinLoc.fibre n j A x)
            (Work.BoseKinLoc.fibre n j B x))
      = ∫ x in Submission.BoseGases.abox n ℓ, ∫ p : EuclideanSpace ℝ (Fin 3), K x p := by
    have hpt2 : ∀ x : Submission.BoseGases.X n,
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseFixB2.DvApriori.momBil ℓ d (Work.BoseKinLoc.fibre n j A x)
            (Work.BoseKinLoc.fibre n j B x)
        = ∫ p : EuclideanSpace ℝ (Fin 3), K x p := by
      intro x
      unfold Work.BoseFixB2.DvApriori.momBil
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => hpt2 x)]
  -- ### step 3: Fubini
  set V : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) → ℝ := fun q =>
      Work.BoseKinLoc.momProj ℓ d q.2 *
        (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j A q.1)) q.2)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j B q.1)) q.2)) with hV
  have hInt1 : MeasureTheory.Integrable V
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h := (Work.BoseFixB2.DvApriori.integrable_momBil_fibre (ℓ := ℓ) (d := d) hℓ
      (n := n) j hΦ hS hT).swap
    simpa only [Function.uncurry_def, Function.comp_def, Prod.fst_swap, Prod.snd_swap, hA, hB, hV]
      using h
  have hInt2 : MeasureTheory.Integrable
      (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
        ((2 * Real.pi) ^ 3)⁻¹ * V q)
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
    hInt1.const_mul _
  have hindMeas : AEStronglyMeasurable
      (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.indU ℓ 0 (q.1 j))
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h2 : Measurable fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) => q.1 j :=
      (measurable_pi_apply j).comp measurable_fst
    have hset : MeasurableSet {q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) |
        q.1 j ∈ Submission.BoseGases.acube ℓ} :=
      (Submission.BoseGases.acube_measurable ℓ).preimage h2
    have hmeas : Measurable fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.indU ℓ 0 (q.1 j) := by
      rw [Work.BoseKinLoc.indU, Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube]
      exact Measurable.indicator measurable_const hset
    exact hmeas.aestronglyMeasurable
  have hindBound : ∀ᵐ q ∂(((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)).prod
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
      ‖Work.BoseKinLoc.indU ℓ 0 (q.1 j)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs]; exact abs_indU_le_one ℓ (q.1 j))
  have hIntK : MeasureTheory.Integrable (Function.uncurry K)
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h := hInt2.bdd_mul hindMeas hindBound
    simpa only [Function.uncurry_def, hK] using h
  have hstep3 : (∫ x in Submission.BoseGases.abox n ℓ,
        ∫ p : EuclideanSpace ℝ (Fin 3), K x p)
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          ∫ x in Submission.BoseGases.abox n ℓ, K x p :=
    MeasureTheory.integral_integral_swap hIntK
  -- ### step 4: the inner integral vanishes
  have hJ : ∀ p : EuclideanSpace ℝ (Fin 3),
      (∫ x in Submission.BoseGases.abox n ℓ, K x p) = 0 := by
    intro p
    rcases hmem with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
    · have hp := integral_indU_kinFT_fibre_eq_zero (ℓ := ℓ) (d := d) hℓ (n := n) j hΦ
        (S := S) (T := T) i hij hiS hiT p
      have hsplit : ∀ x : Submission.BoseGases.X n, K x p =
          ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseKinLoc.momProj ℓ d p) *
            (Work.BoseKinLoc.indU ℓ 0 (x j) *
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j A x)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j B x)) p)) := by
        intro x; simp only [hK]; ring
      rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
        (fun x _ => hsplit x), MeasureTheory.integral_const_mul]
      rw [show (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j A x)) p)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j B x)) p)) = 0 from by
          simpa only [hA, hB] using hp]
      rw [mul_zero]
    · have hp := integral_indU_kinFT_fibre_eq_zero (ℓ := ℓ) (d := d) hℓ (n := n) j hΦ
        (S := T) (T := S) i hij hiT hiS p
      have hsplit : ∀ x : Submission.BoseGases.X n, K x p =
          ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseKinLoc.momProj ℓ d p) *
            (Work.BoseKinLoc.indU ℓ 0 (x j) *
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j B x)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j A x)) p)) := by
        intro x
        simp only [hK]
        rw [real_inner_comm]
        ring
      rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
        (fun x _ => hsplit x), MeasureTheory.integral_const_mul]
      rw [show (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j B x)) p)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j A x)) p)) = 0 from by
          simpa only [hA, hB] using hp]
      rw [mul_zero]
  -- ### assembly
  have hzero : (∫ p : EuclideanSpace ℝ (Fin 3),
      ∫ x in Submission.BoseGases.abox n ℓ, K x p) = 0 := by
    rw [funext hJ, MeasureTheory.integral_zero]
  rw [hstep1, hstep2, hstep3, hzero, mul_zero]

end Work.BoseFixB2.DvApriori.KinOffdiag
