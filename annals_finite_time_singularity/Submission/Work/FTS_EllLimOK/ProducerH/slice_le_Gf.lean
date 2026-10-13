import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos_defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The auxiliary integrand of the slice estimate

Everything below is infrastructure for `slice_le_Gf`.  The integrand

  `slgH α z U θ v = sin(2θ)^{-η} · v^β · U(z v, θ)²`

is the (curried) integrand of the product integral over `Iθ × (0,1)` whose two iterated forms
are compared by Tonelli/Fubini in the main proof. -/

/-- The product integrand `σ θ · v^β · U(z v, θ)²` of the slice estimate. -/
noncomputable def slgH (α z : ℝ) (U : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun θ v => Work.FTS.EllipticEst.AngSecond.sig θ * (v ^ (beta α) * (U (z * v) θ) ^ 2)

/-- The angular weight `θ ↦ sin(2θ)^{-η}` is continuous on the open interval `(0,π/2)`. -/
theorem slg_sig_continuousOn :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (π/2)) := by
  unfold Work.FTS.EllipticEst.AngSecond.sig
  refine ContinuousOn.rpow_const
    (Real.continuous_sin.comp_continuousOn
      (continuous_const.mul continuous_id).continuousOn) ?_
  intro θ hθ
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])))

/-- Continuity on an open box upgrades to a.e. strong measurability for the product of the two
one-dimensional Lebesgue measures restricted to the closed/half-open boxes.  (The closed box and
the open box differ by a null set.) -/
theorem slg_aesm_prod_box {g : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hg : ContinuousOn g (Set.Ioo a b ×ˢ Set.Ioo c d)) :
    AEStronglyMeasurable g
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Ioc c d))) := by
  have h1 : Set.Icc a b =ᵐ[volume] Set.Ioo a b := MeasureTheory.Ioo_ae_eq_Icc.symm
  have h2 : Set.Ioc c d =ᵐ[volume] Set.Ioo c d := MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hprod : (Set.Icc a b ×ˢ Set.Ioc c d : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioo a b ×ˢ Set.Ioo c d) := MeasureTheory.Measure.set_prod_ae_eq h1 h2
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Ioo a b ×ˢ Set.Ioo c d)) :=
    hg.aestronglyMeasurable (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

/-- The `U`-slot `U' = Uprime α Φ` is continuous on the open quadrant as soon as `Φ` is `C^∞`
there: `U' = (-3Φ - α z ∂_zΦ)/sin(2θ)` is a quotient of two continuous functions whose
denominator does not vanish. -/
theorem slg_Uprime_continuousOn {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Φ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StreamBdryIface.Uprime α Φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hnum : ContinuousOn
      (fun p : ℝ × ℝ => -3 * Φ p.1 p.2 - α * p.1 * Work.Spaces.pz Φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.sub ?_ ?_
    · exact (continuousOn_const.mul hsm.continuousOn)
    · exact (continuousOn_const.mul continuousOn_fst).mul hsm.pz.continuousOn
  have hden : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp_continuousOn
      ((continuous_const.mul continuous_snd).continuousOn))
  refine hnum.div hden ?_
  intro p hp
  have hp2 : p.2 ∈ Set.Ioo (0:ℝ) (π/2) := hp.2
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp2.1])
    (by linarith [hp2.2, Real.pi_pos]))

/-- The product integrand `slgH α z U` is continuous on the open box `(0,π/2) × (0,1)` whenever
`U` is continuous on the open quadrant and `z > 0` (so that `(zv, θ)` stays in the quadrant). -/
theorem slg_slgH_continuousOn {α : ℝ} {U : ℝ → ℝ → ℝ}
    (hU : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) Work.FTS.EllipticEst.Q0)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun p : ℝ × ℝ => slgH α z U p.1 p.2)
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) := by
  have hsig : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.1)
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) :=
    slg_sig_continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hvp : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ (beta α))
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) :=
    ContinuousOn.rpow_const continuous_snd.continuousOn
      (fun p hp => Or.inl (ne_of_gt hp.2.1))
  have hUp : ContinuousOn (fun p : ℝ × ℝ => U (z * p.2) p.1)
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) :=
    hU.comp ((continuous_const.mul continuous_snd).prodMk continuous_fst).continuousOn
      (fun p hp => ⟨mul_pos hz hp.2.1, hp.1.1, hp.1.2⟩)
  exact hsig.mul (hvp.mul (hUp.pow 2))

/-- **The `ℋ⁰`-slice of `Φ/cos θ` is dominated by `Gf`.**  Let `α > 0`, `Φ` smooth on the open
quadrant (`SmoothOpen Φ`), `U' = Uprime α Φ` bounded by `M ≥ 0` on the quadrant, and suppose the
pointwise Cauchy–Schwarz bound `(Φ z θ/cos θ)² ≤ (4/(3α))∫₀¹ v^β U'(zv,θ)² dv` holds on the open
quadrant (`hpt`; it is the conclusion of `psiP_pointwise_cs`).  Then for every `z > 0`

  `∫_θ HkIntegrand α 0 (Φ/cos θ) z θ ≤ (4/(3α)) · Gf α U' z`,

where `Gf α U' z = w(z)² ∫₀¹ v^β M₁(zv) dv` and `M₁(z) = ∫_θ U'(z,θ)² sin(2θ)^{-η}`.

Route: at level `0` the integrand is `w(z)² · ((Φ z θ/cos θ)² · σ θ)` with `σ = sin(2θ)^{-η}`
(`HkIntegrand_eq_w2_sig`), so it suffices to bound
`∫_θ (Φ/cos θ)²σ ≤ (4/(3α))∫_θ (∫₀¹ v^β U'(zv,θ)²dv) σ dθ` (monotonicity of the `θ`-integral and
`hpt` a.e. on `Iθ`), and then to interchange the two integrals (`Fubini` on the *finite* measure
spaces `Iθ × (0,1)`, e.g. `Work.FTS.H2.swap_iterated_integral_of_nonneg`, whose four hypotheses
are: nonnegativity, joint a.e. strong measurability (uses `SmoothOpen Φ`: `U'` is continuous on
the open quadrant, and `θ ↦ σ θ` is Borel), a.e. `v`-integrability (dominated by
`M²v^βσ`), and `θ`-integrability of the partially integrated function (dominated by
`M²σθ/(β+1)`, `σ ∈ L¹(Iθ)`)) giving `∫_θ∫_v = ∫_v∫_θ = ∫₀¹ v^β M₁(zv) dv`. -/
theorem slice_le_Gf {α : ℝ} (hα : 0 < α) {Φ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hbnd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.FTS.StreamBdryIface.Uprime α Φ z θ| ≤ M)
    (hpt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      (Φ z θ / Real.cos θ) ^ 2
        ≤ (4 / (3 * α)) * ∫ v in (0 : ℝ)..1,
            v ^ (Work.FTS_EllLimOK.ProducerH.beta α)
              * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ) ^ 2) :
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
        ≤ (4 / (3 * α))
            * Work.FTS_EllLimOK.ProducerH.Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z := by
  intro z hz
  -- `U'` is continuous on the open quadrant, hence so is the product integrand.
  have hUc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StreamBdryIface.Uprime α Φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := slg_Uprime_continuousOn hsm
  have hcont_h : ContinuousOn
      (fun p : ℝ × ℝ => slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2)
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) := slg_slgH_continuousOn hUc hz
  have haesm_h : AEStronglyMeasurable
      (fun p : ℝ × ℝ => slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2)
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    slg_aesm_prod_box hcont_h
  -- `σ` and `v ↦ v^β` are integrable on the two (finite) measure spaces.
  have hsigI : Integrable (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have hp1 : (-1:ℝ) < -(Work.Spaces.eta) := by norm_num [Work.Spaces.eta]
    have hp2 : -(Work.Spaces.eta) ≤ 0 := by norm_num [Work.Spaces.eta]
    exact (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hp1 hp2).1
  have hvI : Integrable (fun v : ℝ => v ^ (beta α)) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have hb : (-1:ℝ) < beta α := by
      rw [beta]; have : (0:ℝ) < 3/α := div_pos (by norm_num) hα; linarith
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' hb)
  have hdom_int : Integrable
      (fun p : ℝ × ℝ => M^2 * (Work.FTS.EllipticEst.AngSecond.sig p.1 * p.2 ^ (beta α)))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    (hsigI.mul_prod hvI).const_mul (M^2)
  -- a.e. facts on the product: the angle is in the open interval and `v` is positive.
  have haeθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0:ℝ) (π/2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := π/2)] with θ h
    exact fun hmem => h.mpr hmem
  have haev : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), v ∈ Set.Ioo (0:ℝ) 1 := by
    rw [MeasureTheory.ae_restrict_iff' (s := Set.Ioc (0:ℝ) 1) measurableSet_Ioc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := 1)] with v h
    exact fun hmem => h.mpr hmem
  have hae_open : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iθ).prod
      (volume.restrict (Set.Ioc (0:ℝ) 1))),
      p.1 ∈ Set.Ioo (0:ℝ) (π/2) ∧ p.2 ∈ Set.Ioo (0:ℝ) 1 := by
    refine (Measure.ae_prod_iff_ae_ae (μ := volume.restrict Work.Spaces.Iθ)
      (ν := volume.restrict (Set.Ioc (0:ℝ) 1))
      (p := fun z : ℝ × ℝ => z.1 ∈ Set.Ioo (0:ℝ) (π/2) ∧ z.2 ∈ Set.Ioo (0:ℝ) 1) ?_).mpr ?_
    · exact measurableSet_Ioo.prod measurableSet_Ioo
    · filter_upwards [haeθ] with θ hθ
      filter_upwards [haev] with v hv
      exact ⟨hθ, hv⟩
  -- the pointwise domination on the product
  have hdom_ae : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iθ).prod
      (volume.restrict (Set.Ioc (0:ℝ) 1))),
      ‖slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2‖
        ≤ M^2 * (Work.FTS.EllipticEst.AngSecond.sig p.1 * p.2 ^ (beta α)) := by
    filter_upwards [hae_open] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hzv : 0 < z * p.2 := mul_pos hz hp2.1
    have hb : |Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1| ≤ M :=
      hbnd (z * p.2) p.1 ⟨hzv, hp1.1, hp1.2⟩
    have hsq : (Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1)^2 ≤ M^2 := by
      nlinarith [abs_nonneg (Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1),
        sq_abs (Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1), hM]
    have hsnn : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig p.1 :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hp1.1, le_of_lt hp1.2⟩
    have hvnn : 0 ≤ p.2 ^ (beta α) := Real.rpow_nonneg (le_of_lt hp2.1) _
    have hnn : 0 ≤ slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2 := by
      simp only [slgH]
      exact mul_nonneg hsnn (mul_nonneg hvnn (sq_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2
        = Work.FTS.EllipticEst.AngSecond.sig p.1 * (p.2 ^ (beta α)
            * (Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1)^2) := by simp only [slgH]
      _ ≤ Work.FTS.EllipticEst.AngSecond.sig p.1 * (p.2 ^ (beta α) * M^2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hvnn) hsnn
      _ = M^2 * (Work.FTS.EllipticEst.AngSecond.sig p.1 * p.2 ^ (beta α)) := by ring
  -- integrability of the product integrand
  have hInt : Integrable
      (fun p : ℝ × ℝ => slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2)
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    Integrable.mono' hdom_int haesm_h hdom_ae
  -- Tonelli/Fubini on the product of the two *finite* measure spaces
  have hFub := integral_integral_swap (μ := volume.restrict Work.Spaces.Iθ)
    (ν := volume.restrict (Set.Ioc (0:ℝ) 1))
    (f := slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ)) hInt
  -- the angular slice is `v^β · M₁(zv)`
  have hθcongr : ∀ v : ℝ,
      (∫ θ, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
          ∂(volume.restrict Work.Spaces.Iθ))
        = v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v) := by
    intro v
    have hcongr : (∫ θ, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
        ∂(volume.restrict Work.Spaces.Iθ))
        = ∫ θ, v ^ (beta α)
            * ((Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2
              * Work.FTS.EllipticEst.AngSecond.sig θ)
            ∂(volume.restrict Work.Spaces.Iθ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [slgH]
      ring
    rw [hcongr, MeasureTheory.integral_const_mul]
    rfl
  -- monotonicity of the angular integral against the pointwise bound `hpt`
  have hnn_f : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun θ => (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
  have hjeq : ∀ θ : ℝ,
      (∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
        = Work.FTS.EllipticEst.AngSecond.sig θ
          * (∫ v in (0:ℝ)..1,
              v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2) := by
    intro θ
    rw [show (∫ v in (0:ℝ)..1,
          v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2)
        = ∫ v, v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) from
        intervalIntegral.integral_of_le (by norm_num)]
    exact MeasureTheory.integral_const_mul _ _
  have hle : (fun θ => (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (4/(3*α)) * ∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    filter_upwards [haeθ] with θ hθ
    have hp := hpt z θ ⟨hz, hθ.1, hθ.2⟩
    have hsnn := Work.FTS.EllipticEst.AngSecond.sig_nonneg
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [hjeq θ]
    calc (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ ((4/(3*α)) * (∫ v in (0:ℝ)..1,
            v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2))
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_le_mul_of_nonneg_right hp hsnn
      _ = (4/(3*α)) * (Work.FTS.EllipticEst.AngSecond.sig θ
            * (∫ v in (0:ℝ)..1,
              v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2)) := by ring
  have hj_int : Integrable
      (fun θ => ∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
        ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) (volume.restrict Work.Spaces.Iθ) :=
    hInt.integral_prod_left
  have hmono := MeasureTheory.integral_mono_of_nonneg hnn_f (hj_int.const_mul (4/(3*α))) hle
  -- level `0`: `HkIntegrand α 0 U z θ = w(z)² (U z θ)² σ θ` on `Iθ`
  have hstepA : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
      = (Work.Spaces.w z)^2 * ∫ θ in Work.Spaces.Iθ,
          (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    simp only [Work.Spaces.Iθ]
    have hcongr : ∀ θ ∈ Set.Icc (0:ℝ) (π/2),
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ
          = (Work.Spaces.w z)^2 * ((Φ z θ / Real.cos θ)^2
              * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      intro θ hθ
      simpa using HkIntegrand_eq_w2_sig α (fun z θ => Φ z θ / Real.cos θ) hθ
    rw [setIntegral_congr_fun measurableSet_Icc hcongr]
    exact MeasureTheory.integral_const_mul _ _
  -- the swapped iterated integral is the inner `v`-integral of `Gf`
  have hswapmain : (∫ θ in Work.Spaces.Iθ,
        ∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
      = ∫ v in (0:ℝ)..1,
          v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v) := by
    rw [hFub]
    rw [show (∫ v, ∫ θ, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
            ∂(volume.restrict Work.Spaces.Iθ) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
        = ∫ v, v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v)
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun v => hθcongr v))]
    exact (intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)).symm
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
      = (Work.Spaces.w z)^2 * ∫ θ in Work.Spaces.Iθ,
          (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ := hstepA
    _ ≤ (Work.Spaces.w z)^2 * ∫ θ in Work.Spaces.Iθ,
          (4/(3*α)) * ∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
    _ = (Work.Spaces.w z)^2 * ((4/(3*α)) * ∫ v in (0:ℝ)..1,
          v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v)) := by
        rw [MeasureTheory.integral_const_mul, hswapmain]
    _ = (4 / (3 * α)) * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z := by
        simp only [Gf]
        ring

end Work.FTS_EllLimOK.ProducerH
