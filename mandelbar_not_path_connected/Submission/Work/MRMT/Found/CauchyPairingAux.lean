/-
Work.MRMT.Found — auxiliary facts about the Cauchy transform pairing.

* `Work.MRMT.Found.isDzDeriv_congr_ae`: the distributional `∂`-relation is insensitive to
  changing the representing function almost everywhere;
* `Work.MRMT.Found.integral_cauchyTransform_mul_eq`: the Fubini identity
  `∫ z, C g z * ψ z = cauchyConst * ∫ ζ, g ζ * (∫ z, ψ z / (ζ - z))` for `g ∈ L¹(ℂ)` and
  `ψ` smooth with compact support (the interchange of the two integrals is licensed by
  `Work.MRMT.Cauchy.integrable_prod_mul_div_sub`).
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Cauchy.integrable_prod_mul_div_sub
import Submission.Work.MRMT.Found.memLp_cauchyTransform_dz
import Submission.Work.MRMT.Sobolev.mollification_pairing_tendsto
import Submission.Work.MRMT.Beltrami.CauchyDzAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal Convolution

/-- The distributional `∂`-relation only depends on the second function up to a.e. equality. -/
theorem isDzDeriv_congr_ae {f g g' : ℂ → ℂ} (h : Work.MRMT.IsDzDeriv f g)
    (hgg' : g =ᵐ[(volume : Measure ℂ)] g') : Work.MRMT.IsDzDeriv f g' := by
  refine ⟨h.1, h.2.1.congr hgg', fun φ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2.2 φ
  refine ⟨h1, h2.congr (hgg'.mono (fun z hz => by simp only [Pi.mul_apply]; rw [hz])), ?_⟩
  rw [h3]
  congr 1
  exact integral_congr_ae (hgg'.mono (fun z hz => by simp only [Pi.mul_apply]; rw [hz]))

/-- **Fubini identity for the Cauchy-transform pairing.**
For `g ∈ L¹(ℂ)` and `ψ` smooth with compact support,
`∫ z, C g z * ψ z = cauchyConst * ∫ ζ, g ζ * (∫ z, ψ z / (ζ - z))`. -/
theorem integral_cauchyTransform_mul_eq (g ψ : ℂ → ℂ) (hg : Integrable g (volume : Measure ℂ))
    (hψc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψs : HasCompactSupport ψ) :
    ∫ z, Work.MRMT.cauchyTransform g z * ψ z
      = Work.MRMT.cauchyConst * ∫ ζ, g ζ * (∫ z, ψ z / (ζ - z)) := by
  have hInt := Work.MRMT.Cauchy.integrable_prod_mul_div_sub g hg ψ hψc hψs
  calc ∫ z, Work.MRMT.cauchyTransform g z * ψ z
      = Work.MRMT.cauchyConst * ∫ z, (∫ ζ, g ζ / (ζ - z)) * ψ z := by
          rw [← integral_const_mul]
          congr 1
          funext z
          rw [Work.MRMT.cauchyTransform]; ring
      _ = Work.MRMT.cauchyConst * ∫ z, ∫ ζ, g ζ * ψ z / (ζ - z) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          show (∫ ζ, g ζ / (ζ - z)) * ψ z = ∫ ζ, g ζ * ψ z / (ζ - z)
          rw [show (fun ζ : ℂ => g ζ * ψ z / (ζ - z)) = fun ζ => ψ z * (g ζ / (ζ - z)) from by
            funext ζ; ring]
          rw [integral_const_mul]; ring
      _ = Work.MRMT.cauchyConst * ∫ p : ℂ × ℂ, g p.1 * ψ p.2 / (p.1 - p.2) := by
          congr 1
          exact (integral_prod_symm _ hInt).symm
      _ = Work.MRMT.cauchyConst * ∫ ζ, ∫ z, g ζ * ψ z / (ζ - z) := by
          congr 1
          exact integral_prod _ hInt
      _ = Work.MRMT.cauchyConst * ∫ ζ, g ζ * (∫ z, ψ z / (ζ - z)) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
          show (∫ z, g ζ * ψ z / (ζ - z)) = g ζ * ∫ z, ψ z / (ζ - z)
          rw [show (fun z : ℂ => g ζ * ψ z / (ζ - z)) = fun z => g ζ * (ψ z / (ζ - z)) from by
            funext z; ring]
          rw [integral_const_mul]

/-- `C (∂φ)` is square integrable for every test function `φ`. -/
theorem memLp_cauchyTransform_dz_test (φ : 𝓓(⊤, ℂ)) :
    MemLp (Work.MRMT.cauchyTransform (fun z => Work.MRMT.dz (φ : ℂ → ℂ) z)) 2
      (volume : Measure ℂ) :=
  memLp_cauchyTransform_dz (φ.contDiff.of_le (by simp)) φ.hasCompactSupport

/-- `∂φ` of a test function `φ` is `C^∞`. -/
theorem contDiff_dz_testFunction (φ : 𝓓(⊤, ℂ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Work.MRMT.dz (φ : ℂ → ℂ) z) := by
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z) := by
    have hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uncurry (fun _ : ℂ => (φ : ℂ → ℂ))) :=
      φ.contDiff.comp contDiff_snd
    exact hm.fderiv contDiff_id (by simp)
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z 1) :=
    hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z Complex.I) := hfd.clm_apply contDiff_const
  have hIc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    (contDiff_const (c := Complex.I)).mul hI
  have hmain := (h1.sub hIc).div_const 2
  simpa only [Work.MRMT.dz] using hmain

/-- The Fubini integrand `(ζ, z) ↦ g ζ * ψ z / (ζ - z)` is integrable for `g ∈ L¹(ℂ)` and
`ψ` *continuous* with compact support (the hypothesis `ContDiff ℝ ⊤` of
`Work.MRMT.Cauchy.integrable_prod_mul_div_sub` is not needed). -/
theorem integrable_prod_mul_div_sub_of_continuous (ω : ℂ → ℂ)
    (hω : MeasureTheory.Integrable ω MeasureTheory.volume)
    (ψ : ℂ → ℂ) (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun p : ℂ × ℂ => ω p.1 * ψ p.2 / (p.1 - p.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hAE : AEStronglyMeasurable (fun p : ℂ × ℂ => ω p.1 * ψ p.2 / (p.1 - p.2))
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => ω p.1) (volume.prod volume) :=
      hω.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEStronglyMeasurable (fun p : ℂ × ℂ => ψ p.2) (volume.prod volume) :=
      Measurable.aestronglyMeasurable (hψc.measurable.comp measurable_snd)
    have h3 : AEStronglyMeasurable (fun p : ℂ × ℂ => p.1 - p.2) (volume.prod volume) :=
      Measurable.aestronglyMeasurable (measurable_fst.sub measurable_snd)
    exact AEStronglyMeasurable.div₀ (h1.mul h2) h3
  refine ⟨hAE, ?_⟩
  obtain ⟨M₀, hM₀⟩ := hψs.isCompact.exists_bound_of_continuousOn hψc.continuousOn
  let M : ℝ := max M₀ 0
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMbd : ∀ z, ‖ψ z‖ ≤ M := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · exact le_trans (hM₀ z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact hMnn
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0:ℂ)).mp hψs.isCompact.isBounded
  let R : ℝ := max r 1
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right r 1)
  have hsupp : ∀ z, z ∉ Metric.ball (0:ℂ) R → ψ z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hzt
    exact hz (Metric.ball_subset_ball (le_max_left r 1) (hr hzt))
  have hinner : ∀ ζ : ℂ, ∫⁻ z, ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)
      ≤ ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R) := by
    intro ζ
    have hpt : (fun z : ℂ => ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖))
        ≤ (fun z : ℂ => ENNReal.ofReal M *
            (Metric.ball (0:ℂ) R).indicator (fun z => ENNReal.ofReal (‖ζ - z‖⁻¹)) z) := by
      intro z
      change ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)
        ≤ ENNReal.ofReal M *
            (Metric.ball (0:ℂ) R).indicator (fun z => ENNReal.ofReal (‖ζ - z‖⁻¹)) z
      by_cases hz : z ∈ Metric.ball (0:ℂ) R
      · rw [Set.indicator_of_mem hz]
        calc ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)
            ≤ ENNReal.ofReal (M / ‖ζ - z‖) :=
              ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hMbd z) (norm_nonneg _))
          _ = ENNReal.ofReal M * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
              rw [div_eq_mul_inv, ENNReal.ofReal_mul hMnn]
      · rw [Set.indicator_of_notMem hz, mul_zero]
        simp [hsupp z hz]
    calc ∫⁻ z, ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)
        ≤ ∫⁻ z, ENNReal.ofReal M *
            (Metric.ball (0:ℂ) R).indicator (fun z => ENNReal.ofReal (‖ζ - z‖⁻¹)) z :=
          lintegral_mono hpt
      _ = ENNReal.ofReal M *
            ∫⁻ z, (Metric.ball (0:ℂ) R).indicator (fun z => ENNReal.ofReal (‖ζ - z‖⁻¹)) z :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal M *
            ∫⁻ z in Metric.ball (0:ℂ) R, ENNReal.ofReal (‖ζ - z‖⁻¹) := by
          rw [MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet]
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R) := by
          gcongr
          exact Work.MRMT.Cauchy.lintegral_ofReal_norm_inv_sub_ball_aux R hR ζ
  have hbound : ∫⁻ p : ℂ × ℂ, ‖ω p.1 * ψ p.2 / (p.1 - p.2)‖ₑ ∂(volume.prod volume)
      ≤ (∫⁻ ζ, ‖ω ζ‖ₑ ∂volume) * (ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R)) := by
    calc ∫⁻ p : ℂ × ℂ, ‖ω p.1 * ψ p.2 / (p.1 - p.2)‖ₑ ∂(volume.prod volume)
        = ∫⁻ ζ, ∫⁻ z, ENNReal.ofReal (‖ω ζ‖ * ‖ψ z‖ / ‖ζ - z‖) ∂volume ∂volume := by
          rw [MeasureTheory.lintegral_prod _ hAE.enorm]
          apply lintegral_congr; intro ζ
          apply lintegral_congr; intro z
          rw [← ofReal_norm, norm_div, norm_mul]
      _ = ∫⁻ ζ, ‖ω ζ‖ₑ * ∫⁻ z, ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖) ∂volume ∂volume := by
          apply lintegral_congr; intro ζ
          have he : (fun z : ℂ => ENNReal.ofReal (‖ω ζ‖ * ‖ψ z‖ / ‖ζ - z‖))
              = (fun z : ℂ => ‖ω ζ‖ₑ * ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)) := by
            funext z
            rw [div_eq_mul_inv, mul_assoc, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
            rfl
          rw [he, MeasureTheory.lintegral_const_mul' (‖ω ζ‖ₑ)
                (fun z : ℂ => ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖)) (enorm_ne_top (x := ω ζ))]
      _ ≤ ∫⁻ ζ, ‖ω ζ‖ₑ * (ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R)) ∂volume := by
          apply lintegral_mono; intro ζ
          change ‖ω ζ‖ₑ * (∫⁻ z, ENNReal.ofReal (‖ψ z‖ / ‖ζ - z‖))
            ≤ ‖ω ζ‖ₑ * (ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R))
          gcongr
          exact hinner ζ
      _ = (∫⁻ ζ, ‖ω ζ‖ₑ ∂volume) * (ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * R)) :=
          MeasureTheory.lintegral_mul_const'' _ hω.aestronglyMeasurable.enorm
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hω.hasFiniteIntegral
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))


/-- **Fubini identity for the Cauchy-transform pairing, continuous version.** -/
theorem integral_cauchyTransform_mul_eq_of_continuous (g ψ : ℂ → ℂ)
    (hg : Integrable g (volume : Measure ℂ)) (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    ∫ z, Work.MRMT.cauchyTransform g z * ψ z
      = Work.MRMT.cauchyConst * ∫ ζ, g ζ * (∫ z, ψ z / (ζ - z)) := by
  have hInt := integrable_prod_mul_div_sub_of_continuous g hg ψ hψc hψs
  calc ∫ z, Work.MRMT.cauchyTransform g z * ψ z
      = Work.MRMT.cauchyConst * ∫ z, (∫ ζ, g ζ / (ζ - z)) * ψ z := by
          rw [← integral_const_mul]
          congr 1
          funext z
          rw [Work.MRMT.cauchyTransform]; ring
      _ = Work.MRMT.cauchyConst * ∫ z, ∫ ζ, g ζ * ψ z / (ζ - z) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          show (∫ ζ, g ζ / (ζ - z)) * ψ z = ∫ ζ, g ζ * ψ z / (ζ - z)
          rw [show (fun ζ : ℂ => g ζ * ψ z / (ζ - z)) = fun ζ => ψ z * (g ζ / (ζ - z)) from by
            funext ζ; ring]
          rw [integral_const_mul]; ring
      _ = Work.MRMT.cauchyConst * ∫ p : ℂ × ℂ, g p.1 * ψ p.2 / (p.1 - p.2) := by
          congr 1
          exact (integral_prod_symm _ hInt).symm
      _ = Work.MRMT.cauchyConst * ∫ ζ, ∫ z, g ζ * ψ z / (ζ - z) := by
          congr 1
          exact integral_prod _ hInt
      _ = Work.MRMT.cauchyConst * ∫ ζ, g ζ * (∫ z, ψ z / (ζ - z)) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
          show (∫ z, g ζ * ψ z / (ζ - z)) = g ζ * ∫ z, ψ z / (ζ - z)
          rw [show (fun z : ℂ => g ζ * ψ z / (ζ - z)) = fun z => g ζ * (ψ z / (ζ - z)) from by
            funext z; ring]
          rw [integral_const_mul]

/-- The Cauchy transform is **anti**-self-adjoint for the bilinear pairing `(g, ψ) ↦ ∫ g ψ`:
`∫ z, C g z * ψ z = -∫ ζ, g ζ * C ψ ζ`.  (The kernel `1/(ζ - z)` is antisymmetric, so the two
double integrals differ by a sign.) -/
theorem integral_cauchyTransform_mul_eq_neg (g ψ : ℂ → ℂ) (hg : Integrable g (volume : Measure ℂ))
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    ∫ z, Work.MRMT.cauchyTransform g z * ψ z = -∫ ζ, g ζ * Work.MRMT.cauchyTransform ψ ζ := by
  have hc : Work.MRMT.cauchyConst ≠ 0 := by
    rw [Work.MRMT.cauchyConst]
    simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hΘ : ∀ ζ : ℂ, (∫ z, ψ z / (ζ - z)) = -Work.MRMT.cauchyConst⁻¹ * Work.MRMT.cauchyTransform ψ ζ := by
    intro ζ
    have h1 : (∫ z, ψ z / (ζ - z)) = ∫ z, -(ψ z / (z - ζ)) :=
      integral_congr_ae (Eventually.of_forall fun z => by
        show ψ z / (ζ - z) = -(ψ z / (z - ζ))
        rw [← div_neg, neg_sub])
    rw [h1, integral_neg, Work.MRMT.cauchyTransform]
    rw [show -Work.MRMT.cauchyConst⁻¹ * (Work.MRMT.cauchyConst * ∫ z, ψ z / (z - ζ))
        = -((Work.MRMT.cauchyConst⁻¹ * Work.MRMT.cauchyConst) * ∫ z, ψ z / (z - ζ)) by ring,
      inv_mul_cancel₀ hc, one_mul]
  rw [integral_cauchyTransform_mul_eq_of_continuous g ψ hg hψc hψs]
  rw [show (∫ ζ, g ζ * ∫ z, ψ z / (ζ - z)) = ∫ ζ, g ζ * (-Work.MRMT.cauchyConst⁻¹ * Work.MRMT.cauchyTransform ψ ζ) from
    integral_congr_ae (Eventually.of_forall fun ζ => by
      show g ζ * (∫ z, ψ z / (ζ - z)) = g ζ * (-Work.MRMT.cauchyConst⁻¹ * Work.MRMT.cauchyTransform ψ ζ)
      rw [hΘ ζ])]
  rw [show (fun ζ : ℂ => g ζ * (-Work.MRMT.cauchyConst⁻¹ * Work.MRMT.cauchyTransform ψ ζ))
      = fun ζ => -Work.MRMT.cauchyConst⁻¹ * (g ζ * Work.MRMT.cauchyTransform ψ ζ) from by
    funext ζ; ring]
  rw [integral_const_mul]
  rw [show Work.MRMT.cauchyConst * (-Work.MRMT.cauchyConst⁻¹ * ∫ ζ, g ζ * Work.MRMT.cauchyTransform ψ ζ)
      = -∫ ζ, g ζ * Work.MRMT.cauchyTransform ψ ζ by
    rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hc, neg_one_mul]]

/-- The C-side `L²`-continuity of the pairing `g ↦ ∫ C g · ψ`. -/
theorem norm_integral_cauchyTransform_sub_pairing_le {ψ : ℂ → ℂ}
    (hψc : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∫ z, ψ z = 0)
    {g₁ g₂ : ℂ → ℂ}
    (h₁ : MeasureTheory.MemLp g₁ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (h₂ : MeasureTheory.MemLp g₂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hc₁ : HasCompactSupport g₁) (hc₂ : HasCompactSupport g₂) :
    ‖(∫ z, Work.MRMT.cauchyTransform g₁ z * ψ z)
        - ∫ z, Work.MRMT.cauchyTransform g₂ z * ψ z‖
      ≤ ‖h₁.toLp g₁ - h₂.toLp g₂‖ *
          (∫ z, ‖Work.MRMT.cauchyTransform ψ z‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hg₁ : Integrable g₁ (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    Work.MRMT.Sobolev.integrable_of_memLp_two_hasCompactSupport h₁ hc₁
  have hg₂ : Integrable g₂ (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    Work.MRMT.Sobolev.integrable_of_memLp_two_hasCompactSupport h₂ hc₂
  have hCψmem : MeasureTheory.MemLp (Work.MRMT.cauchyTransform ψ) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    Work.MRMT.Found.memLp_cauchyTransform_of_zero_mean hψc.continuous hψs hψ0
  have hadj₁ := integral_cauchyTransform_mul_eq_neg g₁ ψ hg₁ hψc.continuous hψs
  have hadj₂ := integral_cauchyTransform_mul_eq_neg g₂ ψ hg₂ hψc.continuous hψs
  have hI₁ : Integrable (fun ζ => g₁ ζ * Work.MRMT.cauchyTransform ψ ζ)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := h₁.integrable_mul hCψmem
  have hI₂ : Integrable (fun ζ => g₂ ζ * Work.MRMT.cauchyTransform ψ ζ)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := h₂.integrable_mul hCψmem
  have hkey : (∫ ζ, ‖g₁ ζ - g₂ ζ‖ ^ 2) = ‖h₁.toLp g₁ - h₂.toLp g₂‖ ^ 2 := by
    rw [← MeasureTheory.MemLp.toLp_sub h₁ h₂,
      ← Work.MRMT.Beltrami.integral_norm_sq_eq_toLp_norm_sq (g₁ - g₂) (h₁.sub h₂)]
    simp only [Pi.sub_apply]
  have hsub : MeasureTheory.MemLp (fun ζ => g₁ ζ - g₂ ζ) (ENNReal.ofReal 2)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
    have h' : MeasureTheory.MemLp (fun ζ => g₁ ζ - g₂ ζ) 2
        (MeasureTheory.volume : MeasureTheory.Measure ℂ) := h₁.sub h₂
    simpa using h'
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (f := fun ζ => g₁ ζ - g₂ ζ) (g := Work.MRMT.cauchyTransform ψ)
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    hsub (by simpa using hCψmem)
  calc ‖(∫ z, Work.MRMT.cauchyTransform g₁ z * ψ z)
        - ∫ z, Work.MRMT.cauchyTransform g₂ z * ψ z‖
      = ‖∫ ζ, (g₁ ζ - g₂ ζ) * Work.MRMT.cauchyTransform ψ ζ‖ := by
        rw [hadj₁, hadj₂, neg_sub_neg, ← neg_sub, norm_neg, ← integral_sub hI₁ hI₂]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun ζ => by ring)
    _ ≤ ∫ ζ, ‖(g₁ ζ - g₂ ζ) * Work.MRMT.cauchyTransform ψ ζ‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ ζ, ‖g₁ ζ - g₂ ζ‖ * ‖Work.MRMT.cauchyTransform ψ ζ‖ :=
        integral_congr_ae (Eventually.of_forall fun ζ => norm_mul _ _)
    _ ≤ (∫ ζ, ‖g₁ ζ - g₂ ζ‖ ^ 2) ^ (1 / 2 : ℝ)
          * (∫ ζ, ‖Work.MRMT.cauchyTransform ψ ζ‖ ^ 2) ^ (1 / 2 : ℝ) := by
        simpa only [Real.rpow_two] using hholder
    _ = ‖h₁.toLp g₁ - h₂.toLp g₂‖ * (∫ ζ, ‖Work.MRMT.cauchyTransform ψ ζ‖ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow, hkey, Real.sqrt_sq (norm_nonneg _)]


end Work.MRMT.Found
