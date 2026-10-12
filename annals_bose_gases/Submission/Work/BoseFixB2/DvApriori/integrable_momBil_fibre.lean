import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.DvApriori.MomBilDefs
import Submission.Work.BoseKinLoc.Kinetic.continuous_Qfree_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.integrable_momBil_fibre`

The polarised large-momentum integrand along the fibre of a joint sector projection is
integrable on the product `d p ⊗ 1_{abox}(x) dx`.

The integrand is

`F (p, x) = momProj ℓ d p · ⟨kinFT (1_{Λ}(ψ^S_x − m_ψ)) p, kinFT (1_{Λ}(ψ^T_x − m_ψ)) p⟩`,

where `ψ^S_x = fibre n j (jointProj ℓ S Φ) x` and `Λ = Λ(0) = acube ℓ`.

**Why this is integrable.** `momProj` is the indicator of the *unbounded* region
`‖p‖ > (d²ℓ)⁻¹`, so a bound on the integrand alone cannot work; the saving is the `L²`
decay of the Fourier transform.  For every `x` the box state
`1_{Λ}(ψ_x − m)` is a bounded function supported in the compact cube `acube ℓ`, hence in
`L¹ ∩ L²`, and Plancherel (`kinFT_sq_of_memLp`) gives

`(2π)⁻³ ∫_p ‖kinFT (boxState ψ_x) p‖² = ∫_x ‖boxState ψ_x x‖² < ∞`.

Since `‖⟨u,v⟩‖ ≤ ‖u‖‖v‖ ≤ (‖u‖² + ‖v‖²)/2` and `0 ≤ momProj ≤ 1`, the `p`-section is
integrable with `∫_p ‖F (p,x)‖ ≤ (1/2)(K_S + K_T)`, and for `x ∈ abox n ℓ` the box states
are uniformly bounded (`Φ` is continuous, `abox n ℓ` compact, `Λ(0) = acube ℓ` inside it),
so `K_S, K_T` are independent of `x`.  Fubini
(`MeasureTheory.integrable_prod_iff'`) finishes.

## Contents

* `norm_mul_inner_le` — the pointwise bound `‖m·⟨z,w⟩‖ ≤ (1/2)m(‖z‖² + ‖w‖²)` for `m ≥ 0`;
* `integrable_prod_of_ae_section_bound` — the Fubini assembly (a.e. `p`-sections
  integrable with an a.e. uniform bound on their `L¹` norms, over a finite measure);
* `fibre_integrable` — Plancherel/L²: every `p`-section of a *single* factor is integrable;
* `fibre_bound` — the uniform-in-`x ∈ abox` bound on the `p`-integral of a single factor;
* `integrable_momBil_fibre` — the target.

The proof is self-contained: measurability of the integrand (`meas_boxState_kinFT`), the
Plancherel/L² integrability of each `p`-section (`fibre_integrable`), the uniform-in-`x`
bound on the box `L²` mass (`fibre_bound`, via `continuous_Qfree_L2`), and the Fubini
assembly (`integrable_prod_of_ae_section_bound`).
-/

noncomputable section

open scoped Real
open MeasureTheory

namespace Work.BoseFixB2.DvApriori

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The pointwise polarisation bound.**  For `m ≥ 0` and `z w : ℂ`,
`‖m·⟨z,w⟩_ℝ‖ ≤ (1/2)·m·(‖z‖² + ‖w‖²)` — the inner product is dominated by
`‖z‖‖w‖ ≤ (‖z‖² + ‖w‖²)/2`, and `m ≥ 0` passes through the norm. -/
private lemma norm_mul_inner_le (m : ℝ) (hm : 0 ≤ m) (z w : ℂ) :
    ‖m * (inner ℝ z w)‖ ≤ (1 / 2) * (m * ‖z‖ ^ 2 + m * ‖w‖ ^ 2) := by
  have h1 : ‖m * (inner ℝ z w)‖ = m * ‖inner ℝ z w‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm, Real.norm_eq_abs]
  have h2 : ‖inner ℝ z w‖ ≤ ‖z‖ * ‖w‖ := norm_inner_le_norm z w
  have h3 : ‖z‖ * ‖w‖ ≤ (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
  have h4 : m * (‖z‖ * ‖w‖) ≤ (1 / 2) * (m * ‖z‖ ^ 2 + m * ‖w‖ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left h3 hm
    nlinarith [h]
  rw [h1]
  exact (mul_le_mul_of_nonneg_left h2 hm).trans h4

/-- The `p`-convention Fourier kernel is jointly measurable. -/
private lemma measurable_fkern :
    Measurable (fun p : E3 × E3 => Complex.exp (-(Complex.I * ↑(inner ℝ p.1 p.2)))) :=
  Complex.continuous_exp.measurable.comp
    (continuous_neg.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_inner))).measurable

/-- **Measurability of the `p`-convention Fourier transform of a strongly measurable
family**, with the frequency as the first coordinate of the parameter.  Unconditional: the
Bochner integral exists for every function, and `StronglyMeasurable.integral_prod_right'`
supplies the measurability of the integral. -/
private lemma stronglyMeasurable_kinFT_fst {β : Type*} [MeasurableSpace β]
    {G : E3 × β → E3 → ℂ}
    (hG : StronglyMeasurable (fun a : (E3 × β) × E3 => G a.1 a.2)) :
    StronglyMeasurable (fun w : E3 × β => Submission.BoseGases.kinFT (G w) w.1) := by
  have hfun : (fun w : E3 × β => Submission.BoseGases.kinFT (G w) w.1)
      = fun w : E3 × β => ∫ z : E3,
          Complex.exp (-(Complex.I * ↑(inner ℝ w.1 z))) * G w z := by
    funext w; rfl
  rw [hfun]
  refine MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3))
    (f := fun w : (E3 × β) × E3 =>
      Complex.exp (-(Complex.I * ↑(inner ℝ w.1.1 w.2))) * G w.1 w.2) ?_
  exact (measurable_fkern.comp
    (Measurable.prodMk measurable_fst.fst measurable_snd)).stronglyMeasurable.mul hG

/-- **Measurability of `(p,x) ↦ kinFT (boxState ℓ 0 (fibre n j Ψ x)) p`.**  The `x`-dependence
sits in the box indicator `1_{Λ(0)}` (independent of `x`), in the fibre
`z ↦ Ψ (update x j z)` (jointly continuous in `(x,z)`), and in the box mean
`ℓ⁻³ ∫_{acube ℓ} Ψ (update x j ·)` (a parametric integral of a jointly measurable function);
the `p`-dependence is the Fourier integral against the jointly measurable kernel
`exp(-i⟪p,z⟫)`.  No integrability is needed. -/
private lemma meas_boxState_kinFT {ℓ : ℝ} {n : ℕ} (j : Fin n)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) :
    Measurable (fun q : E3 × Submission.BoseGases.X n =>
      Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j Ψ q.2)) q.1) := by
  have hfib : StronglyMeasurable (fun a : Submission.BoseGases.X n × E3 =>
      Ψ (Function.update a.1 j a.2)) := (hΨ.comp (continuous_update j)).stronglyMeasurable
  -- the box mean
  have hmean : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)) := by
    have hI := MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun w : Submission.BoseGases.X n × E3 => Ψ (Function.update w.1 j w.2)) hfib
    have heq : (fun x : Submission.BoseGases.X n =>
        Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x))
        = fun x : Submission.BoseGases.X n =>
            (ℓ ^ 3)⁻¹ * ∫ z, Ψ (Function.update x j z)
              ∂(volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) := by
      funext x
      simp only [Work.BSKinetic.bsMean, Work.BoseKinLoc.fibre, smul_zero, zero_add]
    rw [heq]
    exact hI.const_mul _
  -- the localised mean-free box state
  have hB : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
      Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j Ψ a.1.2) a.2) := by
    have h1 : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
        Ψ (Function.update a.1.2 j a.2)) :=
      hfib.comp_measurable (Measurable.prodMk measurable_fst.snd measurable_snd)
    have h2 : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
        Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.fibre n j Ψ a.1.2)) :=
      hmean.comp_measurable (measurable_fst.snd)
    have hq : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
        ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ a.1.2) a.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp_stronglyMeasurable (h1.sub h2)
    classical
    have hset : MeasurableSet {a : (E3 × Submission.BoseGases.X n) × E3 |
        a.2 - ℓ • (0 : E3) ∈ Submission.BoseGases.acube ℓ} :=
      (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)
    have hind : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
        Work.BoseKinLoc.indU ℓ 0 a.2) := by
      have heq : (fun a : (E3 × Submission.BoseGases.X n) × E3 => Work.BoseKinLoc.indU ℓ 0 a.2)
          = fun a => if a.2 - ℓ • (0 : E3) ∈ Submission.BoseGases.acube ℓ
              then (1 : ℝ) else 0 := by
        funext a; rfl
      rw [heq]
      exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
    have hindC : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
        ((Work.BoseKinLoc.indU ℓ 0 a.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp_stronglyMeasurable hind
    exact hindC.mul hq
  exact (stronglyMeasurable_kinFT_fst hB).measurable

/-- **Fubini assembly.**  If `H : E3 × β → ℝ` is measurable, its `p`-sections
`p ↦ H (p,x)` are a.e. integrable, and their `L¹` norms are a.e. bounded by a constant `C`
over a finite measure `ν`, then `H` is integrable for `volume.prod ν`.

The a.e. quantifier is over the *second* variable, which is why the inner (`p`-)integration
is the one that must converge — this is exactly the order needed for the `L²`-in-`p`
(Plancherel) bound. -/
private lemma integrable_prod_of_ae_section_bound {β : Type*} [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] (hν : ν Set.univ ≠ ⊤) {H : E3 × β → ℝ} (hmeas : Measurable H)
    (hint : ∀ᵐ x ∂ν, Integrable (fun p => H (p, x)) volume)
    {C : ℝ} (hC : ∀ᵐ x ∂ν, ∫ p, ‖H (p, x)‖ ∂volume ≤ C) :
    Integrable H (volume.prod ν) := by
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hν⟩
  rw [MeasureTheory.integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨hint, ?_⟩
  have hS : StronglyMeasurable (fun x : β => ∫ p, ‖H (p, x)‖ ∂volume) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure E3))
      (f := fun q : β × E3 => ‖H (q.2, q.1)‖)
      (((hmeas.comp measurable_swap).norm).stronglyMeasurable)
  refine Integrable.of_bound hS.aestronglyMeasurable C ?_
  filter_upwards [hC] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => norm_nonneg _))]
  exact hx

/-- **Plancherel/L²: the `p`-section of a single factor is integrable.**  The box state
`1_{Λ}(ψ_x − m)` lies in `L¹ ∩ L²` (`boxState_memLp`), so its `p`-convention Fourier
transform is in `L²(‖·‖²)` (`kinFT_sq_of_memLp`), and `momProj ≤ 1` is a bounded multiplier. -/
private lemma fibre_integrable {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (x : Submission.BoseGases.X n) :
    Integrable (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p‖ ^ 2) volume := by
  have hfib : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n j Ψ x) :=
    hΨ.comp (contDiff_update (⊤ : ℕ∞) x j)
  obtain ⟨h1, h2⟩ :=
    Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ 0 hfib
  obtain ⟨hint, _⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
    (F := Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)) h1 h2
  refine hint.bdd_mul (c := 1) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    unfold Work.BoseKinLoc.momProj
    exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
      measurable_const measurable_const
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p)]
    exact Work.BoseKinLoc.Kinetic.momProj_le_one ℓ d p

/-- **The uniform-in-`x` bound on the `p`-integral of one factor.**  By Plancherel the
`p`-integral is at most `(2π)³ ∫_{acube ℓ} (Q_u ψ_x)²`, and the latter is *continuous* in `x`
(`continuous_Qfree_L2`, applied to the jointly continuous fibre family
`(x,z) ↦ Ψ (update x j z)`), hence bounded on the compact `abox n ℓ`. -/
private lemma fibre_bound {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ,
      ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p‖ ^ 2 ≤ K := by
  have hK : Continuous (fun p : Submission.BoseGases.X n × E3 =>
      Ψ (Function.update p.1 j p.2)) :=
    hΨ.continuous.comp (continuous_update j)
  have hcont : Continuous (fun x : Submission.BoseGases.X n =>
      ∫ z in Submission.BoseGases.acube ℓ,
        (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z) ^ 2) :=
    Work.BoseKinLoc.Kinetic.continuous_Qfree_L2 (ℓ := ℓ) hℓ hK
  obtain ⟨C, hC⟩ :=
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨(2 * Real.pi) ^ 3 * max C 0, by positivity, ?_⟩
  intro x hx
  have hbox : (∫ z in Submission.BoseGases.acube ℓ,
      (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z) ^ 2) ≤ max C 0 := by
    have hnn : 0 ≤ ∫ z in Submission.BoseGases.acube ℓ,
        (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z) ^ 2 :=
      integral_nonneg (fun z => sq_nonneg _)
    have hx' := hC x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at hx'
    exact le_trans hx' (le_max_left _ _)
  have hfib : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n j Ψ x) :=
    hΨ.comp (contDiff_update (⊤ : ℕ∞) x j)
  obtain ⟨h1, h2⟩ :=
    Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ 0 hfib
  obtain ⟨hint, hplanch⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
    (F := Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)) h1 h2
  have hmom := fibre_integrable (d := d) hℓ j hΨ x
  have hneg : (0 : ℝ) ≤ (2 * Real.pi) ^ 3 := by positivity
  have hne : (2 * Real.pi) ^ 3 ≠ 0 := by positivity
  calc ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p‖ ^ 2
      ≤ ∫ p : E3, ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p‖ ^ 2 :=
        integral_mono hmom hint
          (fun p => mul_le_of_le_one_left (sq_nonneg _)
            (Work.BoseKinLoc.Kinetic.momProj_le_one ℓ d p))
    _ = (2 * Real.pi) ^ 3 * ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z) ^ 2 := by
        have h3 := hplanch
        rw [Work.BoseKinLoc.Kinetic.integral_boxState_normSq,
          Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube] at h3
        rw [← h3, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ ≤ (2 * Real.pi) ^ 3 * max C 0 := mul_le_mul_of_nonneg_left hbox hneg

theorem integrable_momBil_fibre {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n) :
    MeasureTheory.Integrable (Function.uncurry (fun p (x : Submission.BoseGases.X n) =>
      Work.BoseKinLoc.momProj ℓ d p *
        (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))))
      (MeasureTheory.volume.prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := by
  -- the two projected states
  let PS : Submission.BoseGases.X n → ℝ := Work.BoseFixB2.jointProj ℓ S Φ
  let PT : Submission.BoseGases.X n → ℝ := Work.BoseFixB2.jointProj ℓ T Φ
  -- the integrand
  let F : E3 × Submission.BoseGases.X n → ℝ := fun q =>
    Work.BoseKinLoc.momProj ℓ d q.1 *
      (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j PS q.2)) q.1)
        (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j PT q.2)) q.1))
  change MeasureTheory.Integrable F (MeasureTheory.volume.prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
  have hPScd : ContDiff ℝ (⊤ : ℕ∞) PS :=
    Work.BoseFixB2.Sector.jointProj_contDiff (n := n) hℓ S hΦ
  have hPTcd : ContDiff ℝ (⊤ : ℕ∞) PT :=
    Work.BoseFixB2.Sector.jointProj_contDiff (n := n) hℓ T hΦ
  -- measurability of the two Fourier factors
  have hmeasS : Measurable (fun q : E3 × Submission.BoseGases.X n =>
      Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j PS q.2)) q.1) :=
    meas_boxState_kinFT (ℓ := ℓ) j hPScd.continuous
  have hmeasT : Measurable (fun q : E3 × Submission.BoseGases.X n =>
      Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j PT q.2)) q.1) :=
    meas_boxState_kinFT (ℓ := ℓ) j hPTcd.continuous
  -- measurability of the integrand
  have hFmeas : Measurable F := by
    have hmom : Measurable
        (fun q : E3 × Submission.BoseGases.X n => Work.BoseKinLoc.momProj ℓ d q.1) := by
      have h : Measurable (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p) := by
        have heq : (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p)
            = fun p : E3 => if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0 := by
          funext p; rfl
        rw [heq]
        exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
          measurable_const measurable_const
      exact h.comp measurable_fst
    have hpair : Measurable (fun q : E3 × Submission.BoseGases.X n =>
        (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j PS q.2)) q.1,
         Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j PT q.2)) q.1)) :=
      hmeasS.prodMk hmeasT
    have hinner : Measurable (fun q : E3 × Submission.BoseGases.X n =>
        inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j PS q.2)) q.1)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j PT q.2)) q.1)) :=
      continuous_inner.measurable.comp hpair
    exact hmom.mul hinner
  -- the two uniform bounds
  obtain ⟨KS, hKS0, hKS⟩ := fibre_bound (ℓ := ℓ) (d := d) hℓ j hPScd
  obtain ⟨KT, hKT0, hKT⟩ := fibre_bound (ℓ := ℓ) (d := d) hℓ j hPTcd
  -- integrability of each single-factor `p`-integrand
  have hIntA : ∀ x : Submission.BoseGases.X n, Integrable (fun p : E3 =>
      Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j PS x)) p‖ ^ 2) volume :=
    fun x => fibre_integrable (ℓ := ℓ) (d := d) hℓ j hPScd x
  have hIntB : ∀ x : Submission.BoseGases.X n, Integrable (fun p : E3 =>
      Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j PT x)) p‖ ^ 2) volume :=
    fun x => fibre_integrable (ℓ := ℓ) (d := d) hℓ j hPTcd x
  -- the dominating function at a fixed `x`
  have hgInt : ∀ x : Submission.BoseGases.X n, Integrable (fun p : E3 =>
      (1 / 2) * (Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j PS x)) p‖ ^ 2
        + Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j PT x)) p‖ ^ 2)) volume :=
    fun x => ((hIntA x).add (hIntB x)).const_mul (1 / 2)
  -- the pointwise polarisation bound at a fixed `x`
  have hle : ∀ (x : Submission.BoseGases.X n) (p : E3), ‖F (p, x)‖ ≤
      (1 / 2) * (Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j PS x)) p‖ ^ 2
        + Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j PT x)) p‖ ^ 2) :=
    fun x p => norm_mul_inner_le _ (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p) _ _
  -- each `p`-section is integrable
  have hSecInt : ∀ x : Submission.BoseGases.X n, Integrable (fun p : E3 => F (p, x)) volume := by
    intro x
    exact Integrable.mono' (hgInt x)
      (hFmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hle x p))
  -- the uniform bound for `x ∈ abox`
  have hBound : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      ∫ p : E3, ‖F (p, x)‖ ∂volume ≤ (1 / 2) * (KS + KT) := by
    intro x hx
    have key : (∫ p : E3, ‖F (p, x)‖ ∂volume) ≤
        (1 / 2) * ((∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j PS x)) p‖ ^ 2 ∂volume)
          + (∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j PT x)) p‖ ^ 2 ∂volume)) := by
      calc (∫ p : E3, ‖F (p, x)‖ ∂volume)
          ≤ ∫ p : E3, (1 / 2) * (Work.BoseKinLoc.momProj ℓ d p *
              ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j PS x)) p‖ ^ 2
            + Work.BoseKinLoc.momProj ℓ d p *
              ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j PT x)) p‖ ^ 2) ∂volume :=
            integral_mono (hSecInt x).norm (hgInt x) (hle x)
        _ = (1 / 2) * ((∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
              ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j PS x)) p‖ ^ 2 ∂volume)
            + (∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
              ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j PT x)) p‖ ^ 2 ∂volume)) := by
            rw [integral_const_mul, integral_add (hIntA x) (hIntB x)]
    have h1 := hKS x hx
    have h2 := hKT x hx
    linarith [key, h1, h2]
  -- the measure is finite
  have hνfin : ((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ)) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (Submission.BoseGases.abox_compact n hℓ).measure_lt_top.ne
  have hCae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ)),
      ∫ p : E3, ‖F (p, x)‖ ∂volume ≤ (1 / 2) * (KS + KT) := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    exact Filter.Eventually.of_forall (fun x hx => hBound x hx)
  exact integrable_prod_of_ae_section_bound hνfin hFmeas
    (Filter.Eventually.of_forall hSecInt) hCae

end Work.BoseFixB2.DvApriori
