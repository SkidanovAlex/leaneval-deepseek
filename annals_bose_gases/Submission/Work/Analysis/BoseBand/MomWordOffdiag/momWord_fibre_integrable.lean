import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.Analysis.BoseBand.MomWordOffdiag.integrable_momProj_inner_fibre_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.BoseBand.MomWordOffdiag.momWord_fibre_integrable`

**The polarised large-momentum fibre integrand of two smooth `n`-body profiles is jointly
integrable on the box × frequency space.**

The object of the statement is

    `q ↦ 1_{Λ(0)}(q.1_j) · (2π)⁻³ · 1_{(d²ℓ)⁻¹<‖q.2‖} · ⟨𝓕(1_{Λ(0)}Q_0(ψ^A_{q.1}))(q.2),
                                                                  𝓕(1_{Λ(0)}Q_0(ψ^B_{q.1}))(q.2)⟩`

with `ψ^A_x = fibre n j A x` (and likewise for `B`), integrated against
`vol|_{abox n ℓ} ⊗ vol` on `X n × ℝ³`.  This is the two-variable (`(x,p)` instead of only `p`)
form of the polarised large-momentum word of FS `eq:DefT`'s third piece, and it is the
integrability that lets the `p`-integral of `momWord`'s polarisation be interchanged with the
box integral (Fubini) and that justifies writing the off-diagonal fibre brackets as ordinary
Bochner integrals.

## Proof

The integrand is the pointwise product of

* the bounded box indicator `1_{Λ(0)}(x_j)` and the constant `(2π)⁻³` — constants in `p`,
  bounded by `(2π)⁻³` in modulus;
* the high-momentum cut-off `momProj ℓ d p ∈ {0,1}` — a function of `p` alone;
* the real inner product of the two `p`-Fourier transforms.

`p`-integrability for a *fixed* configuration `x ∈ abox n ℓ`, together with a bound uniform over
the box, is `integrable_momProj_inner_fibre_bound` (the `L²`-decay of the two transforms, i.e.
Cauchy–Schwarz plus Plancherel for the compactly supported box states).  Joint measurability in
`(x,p)` is `measurable_kinFT_boxState_fibre` (the Fourier kernel/box-state family is jointly
measurable, no integrability needed) together with the (trivial) measurability of the two
constant factors.  The two-variable integrability criterion `MeasureTheory.integrable_prod_iff`
— `vol|_{abox}` is a *finite* measure and `x ↦ ∫_p ‖integrand‖` is bounded on the box — then
gives the claim.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.Analysis.BoseBand.MomWordOffdiag

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the two bounded factors -/

/-- The box indicator is bounded by one. -/
private lemma abs_indU_zero_le_one (ℓ : ℝ) (z : E3) :
    |Work.BoseKinLoc.indU ℓ 0 z| ≤ 1 := by
  rw [Work.BoseKinLoc.indU]
  by_cases h : z ∈ Work.BoseKinLoc.lamBox ℓ 0
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

/-- The product of the box indicator with the normalisation `(2π)⁻³` is bounded by `(2π)⁻³`. -/
private lemma abs_indU_mul_inv_le (ℓ : ℝ) (z : E3) :
    |Work.BoseKinLoc.indU ℓ 0 z * ((2 * Real.pi) ^ 3)⁻¹| ≤ ((2 * Real.pi) ^ 3)⁻¹ := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹)]
  exact mul_le_of_le_one_left (by positivity) (abs_indU_zero_le_one ℓ z)

/-- Norm of a real scalar multiple. -/
private lemma norm_const_mul_real (c y : ℝ) : ‖c * y‖ = |c| * ‖y‖ := by
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]

/-! ## Joint measurability of the two constant factors -/

/-- The box indicator `indU ℓ 0 (q.1 j)` is measurable on `X n × ℝ³`. -/
private lemma measurable_indU_fst_zero (ℓ : ℝ) {n : ℕ} (j : Fin n) :
    Measurable (fun q : Submission.BoseGases.X n × E3 =>
      Work.BoseKinLoc.indU ℓ 0 (q.1 j)) := by
  have hset : MeasurableSet (Work.BoseKinLoc.lamBox ℓ 0) := by
    have h : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
      ext z
      simp only [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox, smul_zero, sub_zero,
        Submission.BoseGases.mem_acube_iff, Set.mem_ofPred_eq]
    rw [h]; exact Submission.BoseGases.acube_measurable ℓ
  have h1 : Measurable (Work.BoseKinLoc.indU ℓ 0) :=
    measurable_const.indicator hset
  exact h1.comp (by fun_prop : Measurable (fun q : Submission.BoseGases.X n × E3 => q.1 j))

/-- The anchored box indicator `indU ℓ 0` is measurable. -/
private lemma measurable_indU_zero_fun (ℓ : ℝ) :
    Measurable (fun z : E3 => Work.BoseKinLoc.indU ℓ 0 z) := by
  have hset : MeasurableSet (Work.BoseKinLoc.lamBox ℓ 0) := by
    have h : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
      ext z
      simp only [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox, smul_zero, sub_zero,
        Submission.BoseGases.mem_acube_iff, Set.mem_ofPred_eq]
    rw [h]; exact Submission.BoseGases.acube_measurable ℓ
  exact measurable_const.indicator hset

/-- **Joint measurability of `(x,p) ↦ 𝓕(1_{Λ(0)}·Q_0(ψ_x))(p)`** for the slot-`j` fibre
`ψ_x = fibre n j A x` of a continuous `n`-body profile `A`.  `kinFT` is the Bochner integral of
the jointly measurable kernel `(p,z) ↦ e^{-i⟪p,z⟫}·1_{Λ(0)}(z)·Q_0(ψ_x)(z)`; no integrability is
needed (`StronglyMeasurable.integral_prod_right` is unconditional), and `x ↦ bsMean ℓ 0 (ψ_x)`
is a parametric integral of the jointly continuous family `(x,z) ↦ A(x_{j←z})`. -/
private lemma measurable_kinFT_boxState_fibre_aux {ℓ : ℝ} {n : ℕ} (j : Fin n)
    {A : Submission.BoseGases.X n → ℝ} (hA : Continuous A) :
    Measurable (fun q : Submission.BoseGases.X n × E3 =>
      Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j A q.1)) q.2) := by
  classical
  -- the fibre family `(x,z) ↦ A (x_{j←z})`
  have hfib : StronglyMeasurable (fun a : Submission.BoseGases.X n × E3 =>
      A (Function.update a.1 j a.2)) :=
    (hA.comp (continuous_update j)).stronglyMeasurable
  -- the box mean of the fibre, as a parametric integral
  have hmean : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.fibre n j A x)) := by
    have hI : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ∫ z, A (Function.update x j z)
          ∂(volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right
        (ν := (volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ))
        (f := fun (x : Submission.BoseGases.X n) (z : E3) => A (Function.update x j z))
        hfib
    have heq : (fun x : Submission.BoseGases.X n =>
        Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.fibre n j A x))
        = fun x : Submission.BoseGases.X n =>
            (ℓ ^ 3)⁻¹ * ∫ z, A (Function.update x j z)
              ∂(volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ) := by
      funext x
      simp only [Work.BSKinetic.bsMean, Work.BoseKinLoc.fibre, smul_zero, zero_add]
    rw [heq]
    exact hI.const_mul _
  -- the box state, jointly strongly measurable
  have hB : StronglyMeasurable (fun a : (Submission.BoseGases.X n × E3) × E3 =>
      Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j A a.1.1) a.2) := by
    have h1 : StronglyMeasurable (fun a : (Submission.BoseGases.X n × E3) × E3 =>
        A (Function.update a.1.1 j a.2)) :=
      hfib.comp_measurable (Measurable.prodMk measurable_fst.fst measurable_snd)
    have h2 : StronglyMeasurable (fun a : (Submission.BoseGases.X n × E3) × E3 =>
        Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.fibre n j A a.1.1)) :=
      hmean.comp_measurable measurable_fst.fst
    have hq : StronglyMeasurable (fun a : (Submission.BoseGases.X n × E3) × E3 =>
        ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j A a.1.1) a.2 : ℝ) : ℂ)) := by
      refine Complex.continuous_ofReal.comp_stronglyMeasurable ?_
      have heq : (fun a : (Submission.BoseGases.X n × E3) × E3 =>
          Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j A a.1.1) a.2)
          = fun a => A (Function.update a.1.1 j a.2)
              - Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.fibre n j A a.1.1) := by
        funext a; rfl
      rw [heq]; exact h1.sub h2
    have hind : StronglyMeasurable (fun a : (Submission.BoseGases.X n × E3) × E3 =>
        ((Work.BoseKinLoc.indU ℓ 0 a.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp_stronglyMeasurable
        (((measurable_indU_zero_fun ℓ).comp measurable_snd).stronglyMeasurable)
    exact hind.mul hq
  -- the Fourier transform is a parametric integral against the jointly measurable kernel
  change Measurable (fun q : Submission.BoseGases.X n × E3 => ∫ z : E3,
    Complex.exp (-(Complex.I * (inner ℝ q.2 z : ℂ))) *
      Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j A q.1) z)
  refine (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := (volume : MeasureTheory.Measure E3))
    (f := fun (q : Submission.BoseGases.X n × E3) (z : E3) =>
      Complex.exp (-(Complex.I * (inner ℝ q.2 z : ℂ))) *
        Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j A q.1) z) ?_).measurable
  have hker : StronglyMeasurable (fun a : (Submission.BoseGases.X n × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ a.1.2 a.2 : ℂ)))) :=
    (by fun_prop : Continuous fun a : (Submission.BoseGases.X n × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ a.1.2 a.2 : ℂ)))).stronglyMeasurable
  exact hker.mul hB

/-- The spectral cut-off `momProj ℓ d q.2` is measurable on `X n × ℝ³`. -/
private lemma measurable_momProj_snd (ℓ d : ℝ) {n : ℕ} :
    Measurable (fun q : Submission.BoseGases.X n × E3 =>
      Work.BoseKinLoc.momProj ℓ d q.2) := by
  have h1 : Measurable (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p) := by
    have heq : (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p)
        = fun p => if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0 := by
      funext p; rfl
    rw [heq]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
      measurable_const measurable_const
  exact h1.comp measurable_snd

/-! ## The integrability of the rearranged integrand -/

/-- The integrand with its constants grouped in front: `(1_{Λ(0)}(x_j)·(2π)⁻³) · (momProj·⟨·,·⟩)`.
This is the form to which the per-fibre integrability bound applies directly. -/
private lemma integrable_grouped {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {A B : Submission.BoseGases.X n → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    MeasureTheory.Integrable
      (fun q : Submission.BoseGases.X n × E3 =>
        (Work.BoseKinLoc.indU ℓ 0 (q.1 j) * ((2 * Real.pi) ^ 3)⁻¹) *
          (Work.BoseKinLoc.momProj ℓ d q.2 *
            inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j A q.1)) q.2)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j B q.1)) q.2)))
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) := by
  classical
  -- the per-fibre integrability and uniform bound
  obtain ⟨K, hK0, hK⟩ :=
    integrable_momProj_inner_fibre_bound (ℓ := ℓ) (d := d) hℓ j hA hB
  -- joint measurability of the integrand
  have hAmeas := measurable_kinFT_boxState_fibre_aux (ℓ := ℓ) j hA.continuous
  have hBmeas := measurable_kinFT_boxState_fibre_aux (ℓ := ℓ) j hB.continuous
  have hUmeas := measurable_indU_fst_zero ℓ j
  have hPmeas := measurable_momProj_snd ℓ d (n := n)
  have hmeasF : Measurable (fun q : Submission.BoseGases.X n × E3 =>
        (Work.BoseKinLoc.indU ℓ 0 (q.1 j) * ((2 * Real.pi) ^ 3)⁻¹) *
          (Work.BoseKinLoc.momProj ℓ d q.2 *
            inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j A q.1)) q.2)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j B q.1)) q.2))) :=
    (hUmeas.mul (measurable_const : Measurable fun _ : Submission.BoseGases.X n × E3 =>
        ((2 * Real.pi) ^ 3)⁻¹)).mul (hPmeas.mul (hAmeas.inner hBmeas))
  refine (MeasureTheory.integrable_prod_iff hmeasF.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · -- almost every configuration: the `p`-section is integrable
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    filter_upwards with x hx
    exact (hK x hx).1.const_mul _
  · -- the `x`-integral of the norm is integrable: it is bounded by a constant
    refine MeasureTheory.Integrable.mono' (g := fun _ : Submission.BoseGases.X n =>
      ((2 * Real.pi) ^ 3)⁻¹ * K) ?_ ?_ ?_
    · exact MeasureTheory.integrableOn_const (C := ((2 * Real.pi) ^ 3)⁻¹ * K)
        (Submission.BoseGases.abox_lt_top n ℓ hℓ.le).ne
    · exact hmeasF.norm.aestronglyMeasurable.integral_prod_right'
    · rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
      filter_upwards with x hx
      have hb : (∫ p : E3, ‖Work.BoseKinLoc.momProj ℓ d p *
            inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j A x)) p)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j B x)) p)‖) ≤ K := (hK x hx).2
      have hcx : |Work.BoseKinLoc.indU ℓ 0 (x j) * ((2 * Real.pi) ^ 3)⁻¹|
          ≤ ((2 * Real.pi) ^ 3)⁻¹ := abs_indU_mul_inv_le ℓ (x j)
      have hnn : 0 ≤ (∫ p : E3, ‖Work.BoseKinLoc.momProj ℓ d p *
            inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j A x)) p)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j B x)) p)‖) :=
        integral_nonneg (fun p => norm_nonneg _)
      have hbig : (∫ p : E3, ‖(Work.BoseKinLoc.indU ℓ 0 (x j) * ((2 * Real.pi) ^ 3)⁻¹) *
            (Work.BoseKinLoc.momProj ℓ d p *
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j A x)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j B x)) p))‖)
          ≤ ((2 * Real.pi) ^ 3)⁻¹ * K := by
        calc (∫ p : E3, ‖(Work.BoseKinLoc.indU ℓ 0 (x j) * ((2 * Real.pi) ^ 3)⁻¹) *
              (Work.BoseKinLoc.momProj ℓ d p *
                inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                    (Work.BoseKinLoc.fibre n j A x)) p)
                  (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                    (Work.BoseKinLoc.fibre n j B x)) p))‖)
            = ∫ p : E3, |Work.BoseKinLoc.indU ℓ 0 (x j) * ((2 * Real.pi) ^ 3)⁻¹| *
                ‖Work.BoseKinLoc.momProj ℓ d p *
                  inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                      (Work.BoseKinLoc.fibre n j A x)) p)
                    (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                      (Work.BoseKinLoc.fibre n j B x)) p)‖ :=
              MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall (fun p => norm_const_mul_real _ _))
          _ = |Work.BoseKinLoc.indU ℓ 0 (x j) * ((2 * Real.pi) ^ 3)⁻¹| *
                (∫ p : E3, ‖Work.BoseKinLoc.momProj ℓ d p *
                  inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                      (Work.BoseKinLoc.fibre n j A x)) p)
                    (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                      (Work.BoseKinLoc.fibre n j B x)) p)‖) :=
              MeasureTheory.integral_const_mul _ _
          _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * K := mul_le_mul hcx hb hnn (by positivity)
      have houter : 0 ≤ (∫ p : E3, ‖(Work.BoseKinLoc.indU ℓ 0 (x j) * ((2 * Real.pi) ^ 3)⁻¹) *
            (Work.BoseKinLoc.momProj ℓ d p *
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j A x)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j B x)) p))‖) :=
        integral_nonneg (fun p => norm_nonneg _)
      rwa [Real.norm_of_nonneg houter]

/-! ## The target -/

theorem momWord_fibre_integrable {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {A B : Submission.BoseGases.X n → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    MeasureTheory.Integrable
      (fun q : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.indU ℓ 0 (q.1 j) * ((2 * Real.pi) ^ 3)⁻¹ *
          Work.BoseKinLoc.momProj ℓ d q.2 *
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j A q.1)) q.2)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j B q.1)) q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  refine (integrable_grouped (ℓ := ℓ) (d := d) hℓ j hA hB).congr
    (Filter.Eventually.of_forall (fun q => ?_))
  simp only [mul_assoc]

end Work.Analysis.BoseBand.MomWordOffdiag
