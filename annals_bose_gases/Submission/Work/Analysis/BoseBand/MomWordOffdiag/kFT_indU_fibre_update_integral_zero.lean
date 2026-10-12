import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.BoseBand.MomWordOffdiag.kFT_indU_fibre_update_integral_zero`

**The mean-zero hypothesis in a slot kills the windowed slot-`j` fibre in the Fourier variable.**

For a continuous state `A` on the `n`-body configuration space whose slot-`i` fibre has vanishing
mean over the centred cube `acube ℓ` (`hmeani`), the `p`-Fourier transform of the windowed slot-`j`
fibre of `A`, integrated over the slot-`i` variable `y ∈ acube ℓ`, vanishes.  Since `i ≠ j`, the
two updates commute, so the integrand is

    `(2π)`-Fourier of `z ↦ 1_{Λ(0)}(z)·A(x[j ↦ z][i ↦ y])`

and Fubini in `(y, z)` over the two copies of the cube turns the `y`-integral into the slot-`i`
mean of `A` at the configuration `x[j ↦ z]`, which is `0` by `hmeani`.

## Contents

* `lamBox_zero_eq_acube`, `indU_eq_one_of_mem_acube`, `indU_eq_zero_of_not_mem_acube` — the
  anchored box `Λ(0)` is the centred cube `acube ℓ`, on which the box indicator is `1`;
* `kFTkernel` — the joint `(z, y)`-kernel (the integrand of the double integral);
* `fibre_update_comm` — the commutation of the two `Function.update`s (`i ≠ j`);
* `swap_setIntegral_cube` — Fubini for the two cube integrals;
* the theorem itself.
-/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Analysis.BoseBand.MomWordOffdiag

/-! ## 1. The anchored box `Λ(0) = acube ℓ` -/

/-- The anchored moving box is the centred cube. -/
private lemma lamBox_zero_eq_acube (ℓ : ℝ) :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext z
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- The box indicator is `1` on the centred cube. -/
private lemma indU_eq_one_of_mem_acube {ℓ : ℝ} {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ Submission.BoseGases.acube ℓ) : Work.BoseKinLoc.indU ℓ 0 z = 1 := by
  rw [Work.BoseKinLoc.indU, lamBox_zero_eq_acube, Set.indicator_of_mem hz]

/-- The box indicator is `0` off the centred cube. -/
private lemma indU_eq_zero_of_not_mem_acube {ℓ : ℝ} {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∉ Submission.BoseGases.acube ℓ) : Work.BoseKinLoc.indU ℓ 0 z = 0 := by
  rw [Work.BoseKinLoc.indU, lamBox_zero_eq_acube, Set.indicator_of_notMem hz]

/-! ## 2. The joint kernel and the commutation of the two slot updates -/

/-- The joint `(z, y)`-integrand: the Fourier phase at `z` times the windowed slot-`j` fibre of
`A` at the configuration `x[j ↦ z][i ↦ y]`. -/
private noncomputable def kFTkernel (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (j i : Fin n)
    (A : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (z y : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
    (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
      ((A (Function.update (Function.update x j z) i y) : ℝ) : ℂ))

/-- **The two slot updates commute** (`i ≠ j`): the slot-`j` fibre of the slot-`i` update of `A`
at `x` is the slot-`i` update of the slot-`j` update of `A` at `x`. -/
private lemma fibre_update_comm {n : ℕ} {j i : Fin n} (hij : i ≠ j)
    {A : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n)
    (y z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.fibre n j A (Function.update x i y) z
      = A (Function.update (Function.update x j z) i y) := by
  simp only [Work.BoseKinLoc.fibre]
  rw [Function.update_comm hij y z x]

/-! ## 3. Fubini for the two cube integrals -/

/-- **Fubini over the cube.**  For an integrable kernel `g` on the product of the two copies of
the centred cube, the two iterated integrals agree. -/
private lemma swap_setIntegral_cube {ℓ : ℝ}
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => g q.1 q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)))) :
    (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, g z y)
      = ∫ z in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ, g z y := by
  have h1 := MeasureTheory.integral_prod_symm
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ))
    (ν := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ))
    (f := fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => g q.1 q.2) hg
  have h2 := MeasureTheory.integral_prod
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ))
    (ν := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ))
    (f := fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => g q.1 q.2) hg
  exact h1.symm.trans h2

/-! ## 4. The theorem -/

theorem kFT_indU_fibre_update_integral_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {j i : Fin n}
    (hij : i ≠ j) {A : Submission.BoseGases.X n → ℝ} (hA : Continuous A)
    (hmeani : ∀ x : Submission.BoseGases.X n,
      ∫ y in Submission.BoseGases.acube ℓ, A (Function.update x i y) = 0)
    (x : Submission.BoseGases.X n) (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
          ((Work.BoseKinLoc.fibre n j A (Function.update x i y) z : ℝ) : ℂ)) p) = 0 := by
  classical
  -- ### Step 1: the inner Fourier transform is a `z`-integral over the cube
  have hstep1 : ∀ y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
          ((Work.BoseKinLoc.fibre n j A (Function.update x i y) z : ℝ) : ℂ)) p
        = ∫ z in Submission.BoseGases.acube ℓ, kFTkernel ℓ p j i A x z y := by
    intro y
    calc Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
            ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
              ((Work.BoseKinLoc.fibre n j A (Function.update x i y) z : ℝ) : ℂ)) p
        = ∫ z : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
              ((Work.BoseKinLoc.fibre n j A (Function.update x i y) z : ℝ) : ℂ)) := by
          rw [Submission.BoseGases.kinFT]
      _ = ∫ z : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
              ((A (Function.update (Function.update x j z) i y) : ℝ) : ℂ)) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          dsimp only
          rw [fibre_update_comm hij x y z]
      _ = ∫ z in Submission.BoseGases.acube ℓ,
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
                ((A (Function.update (Function.update x j z) i y) : ℝ) : ℂ)) :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
            (s := Submission.BoseGases.acube ℓ)
            (f := fun z : EuclideanSpace ℝ (Fin 3) =>
              Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
                (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
                  ((A (Function.update (Function.update x j z) i y) : ℝ) : ℂ)))
            (fun z hz => by
              rw [indU_eq_zero_of_not_mem_acube hz]
              simp)).symm
      _ = ∫ z in Submission.BoseGases.acube ℓ, kFTkernel ℓ p j i A x z y :=
          MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
            (fun z _ => by simp only [kFTkernel])
  -- ### Step 2: the inner `z`-integral is zero for every `z`
  have hinner : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube ℓ, kFTkernel ℓ p j i A x z y) = 0 := by
    intro z
    have hreal : (∫ y in Submission.BoseGases.acube ℓ,
          ((A (Function.update (Function.update x j z) i y) : ℝ) : ℂ))
        = ((∫ y in Submission.BoseGases.acube ℓ,
            A (Function.update (Function.update x j z) i y) : ℝ) : ℂ) :=
      integral_ofReal
    calc (∫ y in Submission.BoseGases.acube ℓ, kFTkernel ℓ p j i A x z y)
        = (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ))) *
            ∫ y in Submission.BoseGases.acube ℓ,
              ((A (Function.update (Function.update x j z) i y) : ℝ) : ℂ) := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
            (fun y _ => ?_)
          simp only [kFTkernel]
          ring
      _ = (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ))) *
            ((∫ y in Submission.BoseGases.acube ℓ,
              A (Function.update (Function.update x j z) i y) : ℝ) : ℂ) := by
          rw [hreal]
      _ = 0 := by
          rw [hmeani (Function.update x j z)]
          simp
  -- ### Step 3: integrability of the joint kernel on the product of the two cubes
  have hInt : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        kFTkernel ℓ p j i A x q.1 q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))) := by
    have hcont1 : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Function.update (Function.update x j q.1) i q.2) := by
      fun_prop
    have hHcont : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p q.1 : ℂ))) *
          ((A (Function.update (Function.update x j q.1) i q.2) : ℝ) : ℂ)) := by
      fun_prop
    have hHIntOn : MeasureTheory.IntegrableOn
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ p q.1 : ℂ))) *
            ((A (Function.update (Function.update x j q.1) i q.2) : ℝ) : ℂ))
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hHcont.continuousOn).integrableOn_compact
        ((Submission.BoseGases.acube_compact hℓ).prod (Submission.BoseGases.acube_compact hℓ))
    have hFIntOn : MeasureTheory.IntegrableOn
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          kFTkernel ℓ p j i A x q.1 q.2)
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      hHIntOn.congr_fun (fun q hq => by
        rw [Set.mem_prod] at hq
        simp only [kFTkernel]
        rw [indU_eq_one_of_mem_acube hq.1]
        simp)
        ((Submission.BoseGases.acube_measurable ℓ).prod (Submission.BoseGases.acube_measurable ℓ))
    rw [Measure.prod_restrict]
    exact hFIntOn
  -- ### Assembly: Fubini, then the vanishing of the inner integral for every `z`
  have hb : (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
            ((Work.BoseKinLoc.fibre n j A (Function.update x i y) z : ℝ) : ℂ)) p)
      = ∫ y in Submission.BoseGases.acube ℓ,
          ∫ z in Submission.BoseGases.acube ℓ, kFTkernel ℓ p j i A x z y :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y _ => hstep1 y)
  rw [hb, swap_setIntegral_cube (g := fun z y => kFTkernel ℓ p j i A x z y) hInt]
  have hzero : (fun z : EuclideanSpace ℝ (Fin 3) =>
        ∫ y in Submission.BoseGases.acube ℓ, kFTkernel ℓ p j i A x z y)
      = fun _ => (0 : ℂ) := funext hinner
  rw [hzero]
  simp

end Work.Analysis.BoseBand.MomWordOffdiag
