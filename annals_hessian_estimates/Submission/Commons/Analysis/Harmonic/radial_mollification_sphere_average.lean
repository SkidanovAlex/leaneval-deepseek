import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.MeasureTheory.polar_integral
import Submission.Commons.Analysis.MeasureTheory.polar_integral_prod

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal

namespace Commons.Analysis.Harmonic

/-- Integrability is preserved by the polar-coordinate homeomorphism:
if `F : V → ℝ` is integrable then so is `(θ, r) ↦ F (r • θ)` with respect to the product
of the spherical surface measure and the radial measure `volumeIoiPow (finrank - 1)`. -/
private theorem integrable_polar_comp {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    [Nontrivial V] {F : V → ℝ} (hF : Integrable F volume) :
    Integrable (fun p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ) => F (p.2.1 • (p.1 : V)))
      ((MeasureTheory.volume.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
  let hh : ({0}ᶜ : Set V) ≃ₜ (Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ)) :=
    homeomorphUnitSphereProd V
  have hmp : MeasurePreserving hh
      (volume.comap (Subtype.val : ({0}ᶜ : Set V) → V))
      ((volume.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
    simpa [hh] using
      (Measure.measurePreserving_homeomorphUnitSphereProd (μ := (volume : Measure V)) (E := V))
  rw [← (hmp.integrable_comp_emb hh.measurableEmbedding
    (g := fun p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ) => F (p.2.1 • (p.1 : V))))]
  have hgh : ∀ z : ({0}ᶜ : Set V),
      F (((hh z).2 : Set.Ioi (0 : ℝ)).1 • (((hh z).1 : Metric.sphere (0 : V) 1) : V)) = F (z : V) := by
    intro z
    congr 1
    calc ((hh z).2 : Set.Ioi (0 : ℝ)).1 • ((hh z).1 : V)
        = ((hh.symm (hh z) : ({0}ᶜ : Set V)) : V) := by
          rw [homeomorphUnitSphereProd_symm_apply_coe]
      _ = (z : V) := by congr 1; exact hh.left_inv z
  have hgval : Integrable (fun z : ({0}ᶜ : Set V) => F (z : V))
      (volume.comap (Subtype.val : ({0}ᶜ : Set V) → V)) := by
    have hFo : IntegrableOn F ({0}ᶜ : Set V) volume := by
      dsimp [MeasureTheory.IntegrableOn]
      rw [restrict_compl_singleton (0 : V)]
      exact hF
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : V)).compl).mp hFo
  exact hgval.congr (ae_of_all _ (fun z => (hgh z).symm))

/-- Integrability of `y ↦ f (x + y) * ψ y`: `f` is only assumed continuous on the unit ball,
while `ψ` is continuous with `tsupport ψ ⊆ closedBall 0 R` and `closedBall x R` lies inside
the unit ball. -/
private theorem integrable_mul_of_continuousOn {n : ℕ} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContinuousOn f (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψcont : Continuous ψ)
    (hψsupp : tsupport ψ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : Metric.closedBall x R ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => f (x + y) * ψ y) := by
  let K : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R
  have hKc : IsCompact K := isCompact_closedBall 0 R
  have hKm : MeasurableSet K := isClosed_closedBall.measurableSet
  have hcont : ContinuousOn (fun y : EuclideanSpace ℝ (Fin n) => f (x + y) * ψ y) K := by
    refine ContinuousOn.mul ?_ hψcont.continuousOn
    intro y hy
    have hyK : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := hy
    have hyb : x + y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      apply hx
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hyK
    exact (((hf.continuousAt (Metric.isOpen_ball.mem_nhds hyb)).comp
      ((continuous_id.continuousAt).const_add x))).continuousWithinAt
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  have hAE : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) => f (x + y) * ψ y)
      (volume.restrict K) := hcont.aestronglyMeasurable_of_isCompact hKc hKm
  have hIntOn : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => f (x + y) * ψ y) K volume :=
    IntegrableOn.of_bound hKc.measure_lt_top hAE C
      (by filter_upwards [self_mem_ae_restrict hKm] with y hy; exact hC y hy)
  have hsupp : Function.support (fun y : EuclideanSpace ℝ (Fin n) => f (x + y) * ψ y) ⊆ K := by
    intro y hy
    exact hψsupp (subset_tsupport ψ (by
      rw [Function.mem_support] at hy ⊢
      exact fun h => hy (by rw [h, mul_zero])))
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

theorem radial_mollification_sphere_average {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContinuousOn f (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hMVP : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ r : ℝ, 0 < r →
      Metric.closedBall x r ⊆ Metric.ball 0 1 →
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          f (x + r • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere) =
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1 : ℝ) ∂MeasureTheory.volume.toSphere) * f x)
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψcont : Continuous ψ)
    (hψsupp : tsupport ψ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
    {φ : ℝ → ℝ} (hφcont : Continuous φ) (hφsupp : tsupport φ ⊆ Set.Icc 0 R)
    (hψrad : ∀ (r : ℝ) (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1), 0 < r →
      ψ (r • (θ : EuclideanSpace ℝ (Fin n))) = φ r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : Metric.closedBall x R ⊆ Metric.ball 0 1) :
    (∫ y, f (x + y) * ψ y) = (∫ y, ψ y) * f x := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hx_ball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    hx (by rw [Metric.mem_closedBall, dist_self]; exact hR.le)
  have hφ_zero : ∀ r : ℝ, R < r → φ r = 0 := by
    intro r hr
    by_contra hne
    have hmem : r ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hne)
    exact absurd (hφsupp hmem).2 (not_le.mpr hr)
  -- integrability of the polar composite
  have hGint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => f (x + y) * ψ y) volume :=
    integrable_mul_of_continuousOn hf hψcont hψsupp hx
  have hGcomp_int : Integrable
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ) =>
        f (x + p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n))) *
          ψ (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n))))
      ((MeasureTheory.volume.toSphere).prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) :=
    integrable_polar_comp hGint
  -- Step 1: polar decomposition of the left-hand side
  have keyG : (∫ y, f (x + y) * ψ y)
      = ∫ r : Set.Ioi (0 : ℝ),
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + r.1 • (θ : EuclideanSpace ℝ (Fin n))) *
              ψ (r.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) := by
    rw [Commons.Analysis.MeasureTheory.polar_integral_prod (EuclideanSpace ℝ (Fin n))
      (fun y => f (x + y) * ψ y)]
    exact MeasureTheory.integral_prod_symm _ hGcomp_int
  -- Step 2: evaluate `ψ` on `r • θ`
  have keyG2 : (∫ r : Set.Ioi (0 : ℝ),
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + r.1 • (θ : EuclideanSpace ℝ (Fin n))) *
              ψ (r.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)))
      = ∫ r : Set.Ioi (0 : ℝ),
          ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              f (x + r.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)) * φ r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with r
    have hfun : (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          f (x + r.1 • (θ : EuclideanSpace ℝ (Fin n))) * ψ (r.1 • (θ : EuclideanSpace ℝ (Fin n))))
        = (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
            f (x + r.1 • (θ : EuclideanSpace ℝ (Fin n))) * φ r.1) := by
      funext θ
      rw [hψrad r.1 θ r.2]
    rw [hfun, MeasureTheory.integral_mul_const]
  -- Step 3: apply the mean value property a.e. on `(0, ∞)`
  have keyG3 : (∫ r : Set.Ioi (0 : ℝ),
          ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              f (x + r.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)) * φ r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)))
      = ∫ r : Set.Ioi (0 : ℝ),
          ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              (1 : ℝ) ∂MeasureTheory.volume.toSphere) * f x) * φ r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with r
    by_cases hrR : r.1 ≤ R
    · rw [hMVP x hx_ball r.1 r.2
        (subset_trans (Metric.closedBall_subset_closedBall hrR) hx)]
    · simp [hφ_zero r.1 (lt_of_not_ge hrR)]
  -- Step 4: factor out the constant
  have keyG4 : (∫ r : Set.Ioi (0 : ℝ),
          ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              (1 : ℝ) ∂MeasureTheory.volume.toSphere) * f x) * φ r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)))
      = ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              (1 : ℝ) ∂MeasureTheory.volume.toSphere) * f x) *
          (∫ r : Set.Ioi (0 : ℝ), φ r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
    rw [MeasureTheory.integral_const_mul]
  -- the right-hand side
  have keyψ : (∫ y, ψ y)
      = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            (1 : ℝ) ∂MeasureTheory.volume.toSphere) *
          (∫ r : Set.Ioi (0 : ℝ), φ r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
    rw [Commons.Analysis.MeasureTheory.polar_integral_prod (EuclideanSpace ℝ (Fin n)) ψ]
    have hfun : (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ) =>
          ψ (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n)))) = (fun p => φ p.2.1) := by
      funext p
      exact hψrad p.2.1 p.1 p.2.2
    rw [hfun]
    rw [← MeasureTheory.integral_prod_mul
      (μ := (MeasureTheory.volume.toSphere))
      (ν := (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)))
      (f := fun _ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => (1 : ℝ))
      (g := fun r : Set.Ioi (0 : ℝ) => φ r.1)]
    simp
  have hfinal : (∫ y, f (x + y) * ψ y)
      = ((∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              (1 : ℝ) ∂MeasureTheory.volume.toSphere) * f x) *
          (∫ r : Set.Ioi (0 : ℝ), φ r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
    rw [keyG, keyG2, keyG3, keyG4]
  rw [hfinal, keyψ]
  ring

end Commons.Analysis.Harmonic