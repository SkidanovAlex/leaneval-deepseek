import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.ShellMean
import Submission.Work.SmallBoxBridge.Kernel.absCosIntervalLower
import Submission.Work.SmallBoxBridge.Kernel.aemeasurableProfileOfRadial
import Submission.Work.SmallBoxBridge.Kernel.lintegralPolarR3
import Submission.Work.SmallBoxBridge.Kernel.volumeCosInnerZeroNull
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `radialCosIntegrable`

If `p ↦ F ‖p‖ * cos ⟪p, z⟫` is Lebesgue-integrable on `ℝ³`, then so is `p ↦ F ‖p‖`.

The point is that the angular average of `|cos ⟪p, z⟫|` over any sphere is bounded below by
`1/2`: in polar coordinates

  `∫_p F ‖p‖ |cos ⟪p, z⟫| = ∫_{S²}∫_0^∞ r² F(r) |cos (r ⟪e, z⟫)| dr dσ(e)`

and `∫_{S²} |cos (r ⟪e, z⟫)| dσ = 2π ∫_{-1}^1 |cos (r ‖z‖ t)| dt ≥ 2π` by the one
dimensional bound `absCosIntervalLower`.  Since `∫_{S²} dσ = 4π`, this gives
`∫ |F ‖p‖| ≤ 2 ∫ |F ‖p‖ cos ⟪p, z⟫|`.

We prove the inequality on lower integrals (`lintegral`) for an arbitrary radial `Φ`, which
then yields `HasFiniteIntegral` for `F ‖·‖`; `AEStronglyMeasurable` is obtained from the
hypothesis by dividing by `cos ⟪·, z⟫`, which vanishes only on a null set (a countable union
of hyperplanes).
-/

noncomputable section

open MeasureTheory

namespace Work.SmallBoxBridge.Kernel

abbrev radE : Type := EuclideanSpace ℝ (Fin 3)
abbrev radSph : Type := Metric.sphere (0 : radE) 1
abbrev radRp : Type := Set.Ioi (0 : ℝ)
noncomputable abbrev radSigma : Measure radSph := (volume : Measure radE).toSphere
noncomputable abbrev radRho : Measure radRp := Measure.volumeIoiPow 2
noncomputable abbrev radE0 : radE := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-! ### A.e. lifting of an a.e. equality through the second coordinate -/

theorem ae_comp_snd_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {f g : β → ENNReal} (h : f =ᵐ[ν] g) :
    (fun z : α × β => f z.2) =ᵐ[μ.prod ν] (fun z => g z.2) := by
  have hT : ν {r : β | ¬ f r = g r} = 0 := by rw [← MeasureTheory.ae_iff]; exact h
  change ∀ᵐ (z : α × β) ∂(μ.prod ν), f z.2 = g z.2
  rw [MeasureTheory.ae_iff]
  set T' : Set β := toMeasurable ν {r : β | ¬ f r = g r} with hT'def
  have hT'm : ν T' = 0 := by rw [hT'def, measure_toMeasurable, hT]
  have hTm : MeasurableSet ((Prod.snd ⁻¹' T') : Set (α × β)) :=
    (measurableSet_toMeasurable ν {r : β | ¬ f r = g r}).preimage measurable_snd
  apply measure_mono_null (t := (Prod.snd ⁻¹' T' : Set (α × β)))
  · intro z hz
    have : z.2 ∈ T' := by rw [hT'def]; exact subset_toMeasurable ν _ hz
    exact this
  · rw [Measure.prod_apply hTm]
    have hset : ∀ x : α, ((fun r => (x, r)) ⁻¹' ((Prod.snd ⁻¹' T') : Set (α × β))) = T' := by
      intro x; ext r; simp
    simp only [hset, hT'm, lintegral_zero]

/-! ### The one-sphere average of `|cos|` -/

theorem sphere_cos_lintegral_ge (s : ℝ) :
    ENNReal.ofReal (2 * Real.pi) ≤
      ∫⁻ (u : radSph), ENNReal.ofReal |Real.cos (s * (u : radE) 0)| ∂radSigma := by
  rw [Submission.BoseGases.shell_proj_lintegral (h := fun t => |Real.cos (s * t)|) (by fun_prop)]
  have hint : Integrable (fun t : ℝ => |Real.cos (s * t)|)
      (volume.restrict (Set.Icc (-1:ℝ) 1)) :=
    ((by fun_prop : Continuous fun t : ℝ => |Real.cos (s * t)|)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hof : (∫⁻ t in Set.Icc (-1:ℝ) 1, ENNReal.ofReal |Real.cos (s * t)|)
      = ENNReal.ofReal (∫ t in Set.Icc (-1:ℝ) 1, |Real.cos (s * t)|) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => abs_nonneg _)).symm
  rw [hof]
  have h1 : (1:ℝ) ≤ ∫ t in Set.Icc (-1:ℝ) 1, |Real.cos (s * t)| := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have hs' : 0 < -s := by linarith
      have h := absCosIntervalLower (-s) 1 hs' (by norm_num)
      refine le_trans h (le_of_eq ?_)
      apply intervalIntegral.integral_congr
      intro x hx
      simp only
      rw [show (-s) * x = -(s * x) by ring, Real.cos_neg]
    · subst hs; norm_num
    · exact absCosIntervalLower s 1 hs (by norm_num)
  calc ENNReal.ofReal (2 * Real.pi)
      = ENNReal.ofReal (2 * Real.pi) * 1 := (mul_one _).symm
    _ = ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal 1 := by rw [ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (2 * Real.pi) *
          ENNReal.ofReal (∫ t in Set.Icc (-1:ℝ) 1, |Real.cos (s * t)|) := by gcongr

/-! ### The core inequality along the axis -/

set_option maxHeartbeats 800000 in
theorem radial_cos_lintegral_le_axis (Φ : radE → ENNReal) (c : ℝ)
    (hΦ : AEStronglyMeasurable Φ (volume : Measure radE))
    (hrad : ∀ p q : radE, ‖p‖ = ‖q‖ → Φ p = Φ q) :
    ∫⁻ (p : radE), Φ p ≤ 2 * ∫⁻ (p : radE), Φ p * ENNReal.ofReal |Real.cos (c * p 0)| := by
  let A : radRp → ENNReal := fun r => Φ ((r : ℝ) • radE0)
  have hA : AEMeasurable A radRho := aemeasurableProfileOfRadial Φ hΦ hrad
  obtain ⟨Ã, hÃmeas, hÃeq⟩ := hA
  have hpt : ∀ b : radSph × radRp, Φ ((b.2 : ℝ) • (b.1 : radE)) = A b.2 := by
    intro b
    change Φ ((b.2 : ℝ) • (b.1 : radE)) = Φ ((b.2 : ℝ) • radE0)
    apply hrad
    have hb1 : ‖(b.1 : radE)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm, dist_zero_right] using b.1.2
    have he0 : ‖(radE0 : radE)‖ = 1 := Submission.BoseGases.shellE0_norm
    have hL : ‖(b.2 : ℝ) • (b.1 : radE)‖ = (b.2 : ℝ) := by
      rw [norm_smul, hb1, mul_one, Real.norm_eq_abs, abs_of_pos b.2.2]
    have hR : ‖(b.2 : ℝ) • (radE0 : radE)‖ = (b.2 : ℝ) := by
      rw [norm_smul, he0, mul_one, Real.norm_eq_abs, abs_of_pos b.2.2]
    rw [hL, hR]
  have hLHS : ∫⁻ (p : radE), Φ p = radSigma Set.univ * ∫⁻ (r : radRp), A r ∂radRho := by
    rw [lintegralPolarR3 Φ]
    rw [show (∫⁻ (b : radSph × radRp), Φ ((b.2:ℝ)•(b.1:radE)) ∂(radSigma.prod radRho))
        = ∫⁻ (b : radSph × radRp), A b.2 ∂(radSigma.prod radRho) from by
          apply lintegral_congr; intro b; exact hpt b]
    rw [show (∫⁻ (b : radSph × radRp), A b.2 ∂(radSigma.prod radRho))
        = ∫⁻ (b : radSph × radRp), Ã b.2 ∂(radSigma.prod radRho) from
          lintegral_congr_ae (ae_comp_snd_of_ae (μ := radSigma) (ν := radRho) hÃeq)]
    rw [show (∫⁻ (b : radSph × radRp), Ã b.2 ∂(radSigma.prod radRho))
        = (∫⁻ (u : radSph), (1:ENNReal) ∂radSigma) * (∫⁻ (r : radRp), Ã r ∂radRho) from by
          rw [← lintegral_prod_mul (μ := radSigma) (ν := radRho) (f := fun _ : radSph => (1:ENNReal))
                (g := Ã) aemeasurable_const hÃmeas.aemeasurable]
          apply lintegral_congr; intro z; simp]
    rw [lintegral_const, one_mul]
    congr 1
    exact (lintegral_congr_ae hÃeq).symm
  have hRHS : (∫⁻ (p : radE), Φ p * ENNReal.ofReal |Real.cos (c * p 0)|)
      = ∫⁻ (b : radSph × radRp),
          A b.2 * ENNReal.ofReal |Real.cos (c * b.2 * (b.1 : radE) 0)| ∂(radSigma.prod radRho) := by
    rw [lintegralPolarR3 (fun p => Φ p * ENNReal.ofReal |Real.cos (c * p 0)|)]
    apply lintegral_congr; intro b
    rw [hpt b]
    congr 1; congr 1; congr 1
    simp only [PiLp.smul_apply]; ring_nf
  have hRHS2 : (∫⁻ (b : radSph × radRp),
          A b.2 * ENNReal.ofReal |Real.cos (c * b.2 * (b.1 : radE) 0)| ∂(radSigma.prod radRho))
      = ∫⁻ (r : radRp), ∫⁻ (u : radSph),
          Ã r * ENNReal.ofReal |Real.cos (c * r * (u : radE) 0)| ∂radSigma ∂radRho := by
    have hAe : (fun b : radSph × radRp =>
          A b.2 * ENNReal.ofReal |Real.cos (c * b.2 * (b.1 : radE) 0)|)
        =ᵐ[radSigma.prod radRho] (fun b =>
          Ã b.2 * ENNReal.ofReal |Real.cos (c * b.2 * (b.1 : radE) 0)|) := by
      filter_upwards [ae_comp_snd_of_ae (μ := radSigma) (ν := radRho) hÃeq] with b hb
      rw [hb]
    rw [lintegral_congr_ae hAe]
    set F : radSph × radRp → ENNReal :=
      fun b => Ã b.2 * ENNReal.ofReal |Real.cos (c * b.2 * (b.1 : radE) 0)| with hF
    set g : radRp × radSph → ENNReal :=
      fun z => Ã z.1 * ENNReal.ofReal |Real.cos (c * z.1 * (z.2 : radE) 0)| with hg
    have hswap : (∫⁻ (b : radSph × radRp), F b ∂(radSigma.prod radRho))
        = ∫⁻ (z : radRp × radSph), F z.swap ∂(radRho.prod radSigma) :=
      (MeasureTheory.lintegral_prod_swap F).symm
    rw [hswap]
    have hge : (fun z : radRp × radSph => F z.swap) = g := by
      funext z; simp [F, g, Prod.swap]
    rw [hge]
    have hgm : AEMeasurable g (radRho.prod radSigma) := by
      have h1 : AEMeasurable (fun z : radRp × radSph => Ã z.1) (radRho.prod radSigma) :=
        hÃmeas.aemeasurable.comp_fst
      have h2 : AEMeasurable
          (fun z : radRp × radSph => ENNReal.ofReal |Real.cos (c * z.1 * (z.2:radE) 0)|)
          (radRho.prod radSigma) := by
        apply Measurable.aemeasurable
        apply ENNReal.measurable_ofReal.comp
        apply Measurable.abs
        apply Real.measurable_cos.comp
        fun_prop
      exact h1.mul h2
    rw [lintegral_prod (μ := radRho) (ν := radSigma) (f := g) hgm]
  have hbound : ENNReal.ofReal (2 * Real.pi) * (∫⁻ (r : radRp), A r ∂radRho)
      ≤ ∫⁻ (r : radRp), ∫⁻ (u : radSph),
          Ã r * ENNReal.ofReal |Real.cos (c * r * (u : radE) 0)| ∂radSigma ∂radRho := by
    have hinner : ∀ r : radRp, (∫⁻ (u : radSph),
          Ã r * ENNReal.ofReal |Real.cos (c * r * (u:radE) 0)| ∂radSigma)
        = Ã r * (∫⁻ (u : radSph),
            ENNReal.ofReal |Real.cos (c * r * (u:radE) 0)| ∂radSigma) := by
      intro r
      have hm : Measurable
          (fun u : radSph => ENNReal.ofReal |Real.cos ((c * (r:ℝ)) * (u:radE) 0)|) := by
        apply ENNReal.measurable_ofReal.comp; apply Measurable.abs
        apply Real.measurable_cos.comp; fun_prop
      exact lintegral_const_mul (Ã r) hm
    simp_rw [hinner]
    have h1 : (∫⁻ (r : radRp), Ã r * ENNReal.ofReal (2 * Real.pi) ∂radRho)
        ≤ ∫⁻ (r : radRp), Ã r * (∫⁻ (u : radSph),
            ENNReal.ofReal |Real.cos (c * r * (u:radE) 0)| ∂radSigma) ∂radRho := by
      apply lintegral_mono; intro r
      exact mul_le_mul_of_nonneg_left (sphere_cos_lintegral_ge (c * (r : ℝ))) bot_le
    have h2 : (∫⁻ (r : radRp), Ã r * ENNReal.ofReal (2 * Real.pi) ∂radRho)
        = ENNReal.ofReal (2 * Real.pi) * (∫⁻ (r : radRp), A r ∂radRho) := by
      rw [lintegral_mul_const (ENNReal.ofReal (2 * Real.pi)) hÃmeas, mul_comm]
      congr 1
      exact (lintegral_congr_ae hÃeq).symm
    rw [← h2]
    exact h1
  have hsig : radSigma Set.univ ≤ 2 * ENNReal.ofReal (2 * Real.pi) := by
    rw [Submission.BoseGases.shell_toSphere_total_enn]
    rw [show (4:ℝ) * Real.pi = 2 * (2 * Real.pi) by ring,
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [ENNReal.ofReal_ofNat]
  have hfinal : ENNReal.ofReal (2*Real.pi) * (∫⁻ (r : radRp), A r ∂radRho)
      ≤ ∫⁻ (p : radE), Φ p * ENNReal.ofReal |Real.cos (c * p 0)| := by
    rw [hRHS, hRHS2]; exact hbound
  calc ∫⁻ (p : radE), Φ p
      = radSigma Set.univ * (∫⁻ (r : radRp), A r ∂radRho) := hLHS
    _ ≤ (2 * ENNReal.ofReal (2*Real.pi)) * (∫⁻ (r : radRp), A r ∂radRho) :=
        mul_le_mul_of_nonneg_right hsig bot_le
    _ = 2 * (ENNReal.ofReal (2*Real.pi) * (∫⁻ (r : radRp), A r ∂radRho)) := by rw [mul_assoc]
    _ ≤ 2 * (∫⁻ (p : radE), Φ p * ENNReal.ofReal |Real.cos (c * p 0)|) :=
        mul_le_mul_of_nonneg_left hfinal bot_le

/-! ### Reduction of a general direction `z` to the axis -/

set_option maxHeartbeats 800000 in
theorem radial_cos_lintegral_le (Φ : radE → ENNReal) (z : radE)
    (hΦ : AEStronglyMeasurable Φ (volume : Measure radE))
    (hrad : ∀ p q : radE, ‖p‖ = ‖q‖ → Φ p = Φ q) :
    ∫⁻ (p : radE), Φ p ≤ 2 * ∫⁻ (p : radE), Φ p * ENNReal.ofReal |Real.cos (inner ℝ p z)| := by
  rcases eq_or_ne z 0 with rfl | hz
  · have h := radial_cos_lintegral_le_axis Φ 0 hΦ hrad
    simpa [inner_zero_right, Real.cos_zero, ENNReal.ofReal_one, mul_one] using h
  · have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    -- a linear isometry sending the unit vector `‖z‖⁻¹ • z` to the first basis vector
    have hnorm : ‖(‖z‖⁻¹ : ℝ) • z‖ = ‖(radE0 : radE)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ hzn]
      exact (Submission.BoseGases.shellE0_norm).symm
    obtain ⟨U, hU⟩ :=
      Submission.BoseGases.exists_linearIsometry_of_norm_eq
        (x := (‖z‖⁻¹ : ℝ) • z) (y := (radE0 : radE)) hnorm
    have hpt : ∀ p : radE, inner ℝ p z = ‖z‖ * (U p) 0 := by
      intro p
      have h1 : inner ℝ (U p) (U ((‖z‖⁻¹ : ℝ) • z)) = inner ℝ p ((‖z‖⁻¹ : ℝ) • z) :=
        U.inner_map_map p _
      rw [hU, inner_smul_right] at h1
      have h2 : inner ℝ (U p) (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = (U p) 0 := by
        rw [EuclideanSpace.inner_single_right]; simp
      rw [h2] at h1
      rw [h1, ← mul_assoc, mul_inv_cancel₀ hzn, one_mul]
    have hmp : MeasurePreserving U (volume : Measure radE) volume :=
      LinearIsometryEquiv.measurePreserving U
    have hemb : MeasurableEmbedding (U : radE → radE) :=
      (LinearIsometryEquiv.toHomeomorph U).measurableEmbedding
    have hkey := hmp.lintegral_comp_emb hemb
      (fun q : radE => Φ q * ENNReal.ofReal |Real.cos (‖z‖ * q 0)|)
    have hswap : (∫⁻ (p : radE), Φ p * ENNReal.ofReal |Real.cos (‖z‖ * (U p) 0)|)
        = ∫⁻ (q : radE), Φ q * ENNReal.ofReal |Real.cos (‖z‖ * q 0)| := by
      rw [← hkey]
      apply lintegral_congr; intro p
      change Φ p * ENNReal.ofReal |Real.cos (‖z‖ * (U p) 0)|
          = Φ (U p) * ENNReal.ofReal |Real.cos (‖z‖ * (U p) 0)|
      rw [hrad (U p) p (U.norm_map p)]
    have hpt2 : (∫⁻ (p : radE), Φ p * ENNReal.ofReal |Real.cos (inner ℝ p z)|)
        = ∫⁻ (p : radE), Φ p * ENNReal.ofReal |Real.cos (‖z‖ * (U p) 0)| := by
      apply lintegral_congr; intro p; rw [hpt p]
    rw [hpt2, hswap]
    exact radial_cos_lintegral_le_axis Φ ‖z‖ hΦ hrad

/-! ### The final statement -/

theorem radialCosIntegrable (F : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖ * Real.cos (inner ℝ p z)) →
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖) := by
  intro h
  have haesm : AEStronglyMeasurable (fun p : radE => F ‖p‖) (volume : Measure radE) := by
    classical
    rcases eq_or_ne z 0 with rfl | hz
    · simpa [inner_zero_right, Real.cos_zero, mul_one] using h.1
    · have hne : ∀ᵐ p ∂(volume : Measure radE), Real.cos (inner ℝ p z) ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simpa using volumeCosInnerZeroNull z hz
      obtain ⟨G, hG, hGeq⟩ := h.1
      refine ⟨fun p => if Real.cos (inner ℝ p z) = 0 then 0 else G p / Real.cos (inner ℝ p z),
        ?_, ?_⟩
      · apply Measurable.stronglyMeasurable
        have hc : Measurable (fun p : radE => Real.cos (inner ℝ p z)) := by
          apply Real.measurable_cos.comp
          fun_prop
        exact Measurable.ite (measurableSet_eq_fun hc measurable_const) measurable_const
          (hG.measurable.div hc)
      · filter_upwards [hGeq, hne] with p hGp hcn
        rw [if_neg hcn, ← hGp]
        field_simp
  refine ⟨haesm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [show (∫⁻ (p : radE), ‖F ‖p‖‖ₑ ∂(volume : Measure radE))
      = ∫⁻ (p : radE), ENNReal.ofReal |F ‖p‖| ∂volume from by
        apply lintegral_congr; intro p; rw [Real.enorm_eq_ofReal_abs]]
  have hΦ : AEStronglyMeasurable (fun p : radE => ENNReal.ofReal |F ‖p‖|)
      (volume : Measure radE) :=
    (ENNReal.continuous_ofReal.comp continuous_abs).comp_aestronglyMeasurable haesm
  have hrad : ∀ p q : radE, ‖p‖ = ‖q‖ →
      ENNReal.ofReal |F ‖p‖| = ENNReal.ofReal |F ‖q‖| := by
    intro p q hpq; rw [hpq]
  have hk := radial_cos_lintegral_le (fun p : radE => ENNReal.ofReal |F ‖p‖|) z hΦ hrad
  refine lt_of_le_of_lt hk ?_
  have heq : (∫⁻ (p : radE),
        ENNReal.ofReal |F ‖p‖| * ENNReal.ofReal |Real.cos (inner ℝ p z)|)
      = ∫⁻ (p : radE), ‖F ‖p‖ * Real.cos (inner ℝ p z)‖ₑ := by
    apply lintegral_congr; intro p
    rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  rw [heq]
  exact ENNReal.mul_lt_top (by norm_num) h.2

end Work.SmallBoxBridge.Kernel
