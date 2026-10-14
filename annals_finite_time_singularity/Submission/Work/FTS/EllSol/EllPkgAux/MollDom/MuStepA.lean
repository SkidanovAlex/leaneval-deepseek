import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## Step A — the pointwise Jensen bound in `ℝ≥0∞` -/

/-- **Step A.**  Under the domination hypothesis, for a.e. `z ∈ Iz` and all `θ ∈ Iθ`,

  `ofReal ((F z θ)² σ(θ)) ≤ 3 σ̂(θ) · QHat δ ε X z θ`.

From `hdom` (giving `|F z θ| ≤ ∫_t k δ z t · (MmPsi θ t)`), monotonicity of squaring, the
inequality `ofReal (∫ f) ≤ ∫⁻ ofReal f`, the `ℝ≥0∞`-Cauchy–Schwarz in `t` against the unit-mass
kernel `k δ z ·`, and finally `∫_s KJ ε θ s (X(e^t,s))² ≥ (MmPsi θ t)²/3` (`KJ_pointwise`). -/
theorem mu_pointwise {F X : ℝ → ℝ → ℝ} {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hdom : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ θ ∈ Iθ,
      |F z θ| ≤ ∫ t : ℝ, sKer δ (Real.log z - t) *
        (∫ s in Iθ, KJ ε θ s * |X (Real.exp t) s|))
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ)
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    ∀ᵐ z ∂(volume.restrict Iz), ∀ θ ∈ Iθ,
      ENNReal.ofReal ((F z θ) ^ 2 * σθ θ) ≤ 3 * muSigHat θ * muQHat δ ε X z θ := by
  rw [mu_Ioi]
  filter_upwards [hdom] with z hz θ hθ
  have hJnn : ∀ t : ℝ, 0 ≤ MmPsi ε X θ t := fun t =>
    integral_nonneg (fun s => mul_nonneg (KJ_nonneg hε θ s) (abs_nonneg _))
  have hFabs : |F z θ| ≤ ∫ t : ℝ, sKer δ (Real.log z - t) * MmPsi ε X θ t := hz θ hθ
  -- (1) square the pointwise domination
  have step1 : ENNReal.ofReal ((F z θ) ^ 2)
      ≤ (ENNReal.ofReal (∫ t : ℝ, sKer δ (Real.log z - t) * MmPsi ε X θ t)) ^ 2 := by
    rw [← sq_abs (F z θ), ENNReal.ofReal_pow (abs_nonneg (F z θ)) 2]
    exact mu_sq_le_sq (ENNReal.ofReal_le_ofReal hFabs)
  -- (2) `ofReal` of the integral is at most the lintegral
  have step2 : ENNReal.ofReal (∫ t : ℝ, sKer δ (Real.log z - t) * MmPsi ε X θ t)
      ≤ ∫⁻ t, muKHat δ z t * ENNReal.ofReal (MmPsi ε X θ t) := by
    have h1 := mu_ofReal_integral_le_lintegral (μ := volume)
      (f := fun t : ℝ => sKer δ (Real.log z - t) * MmPsi ε X θ t)
      (Eventually.of_forall (fun t => mul_nonneg (sKer_nonneg hδ _) (hJnn t)))
    refine h1.trans (le_of_eq ?_)
    exact lintegral_congr (fun t => by rw [muKHat_def, ENNReal.ofReal_mul (sKer_nonneg hδ _)])
  -- (3) Cauchy–Schwarz in `t` against the unit-mass kernel
  have step3 : (∫⁻ t, muKHat δ z t * ENNReal.ofReal (MmPsi ε X θ t)) ^ 2
      ≤ (∫⁻ t, muKHat δ z t)
        * (∫⁻ t, muKHat δ z t * (ENNReal.ofReal (MmPsi ε X θ t)) ^ 2) :=
    mu_ofReal_cs
      ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).measurable.comp
        (measurable_const.sub measurable_id)).aemeasurable
      (MmPsi_aesm hXmeas ε θ).aemeasurable
      (fun t => sKer_nonneg hδ _) (fun t => hJnn t)
  -- (4) the mass
  have step4 : ∫⁻ t, muKHat δ z t = 1 := mu_kHat_lintegral_one δ hδ z
  -- (5) the inner Jensen bound
  have step5 : ∀ t : ℝ, (ENNReal.ofReal (MmPsi ε X θ t)) ^ 2
      ≤ 3 * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s) := by
    intro t
    have hX2 : IntegrableOn (fun s : ℝ => (X (Real.exp t) s) ^ 2) Iθ :=
      integrableOn_sq_of_integrableOn (hXhon (Real.exp t) (Real.exp_pos t))
    have hcont : Continuous (fun s : ℝ => KJ ε θ s) := mu_continuous_KJ_slice ε θ
    have hInt' : IntegrableOn (fun s : ℝ => KJ ε θ s * (X (Real.exp t) s) ^ 2) Iθ := by
      have hCnn : (0 : ℝ) ≤ 3 * (ε * sMass)⁻¹ :=
        mul_nonneg (by norm_num) (inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le))
      refine Integrable.mono' (hX2.const_mul (3 * (ε * sMass)⁻¹)) ?_ ?_
      · exact hcont.aestronglyMeasurable.mul hX2.1
      · filter_upwards with s
        simpa only [Real.norm_of_nonneg (mul_nonneg (KJ_nonneg hε θ s) (sq_nonneg _)),
          Real.norm_of_nonneg (mul_nonneg hCnn (sq_nonneg _))] using
          mul_le_mul_of_nonneg_right (KJ_le hε θ s) (sq_nonneg _)
    have hconv : ENNReal.ofReal (∫ s in Iθ, KJ ε θ s * (X (Real.exp t) s) ^ 2)
        = ∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s :=
      mu_ofReal_integral_eq_lintegral_KJ ε θ t hε hInt'
    have habs : IntegrableOn (fun s : ℝ => |X (Real.exp t) s| ^ 2 * σθ s) Iθ :=
      (hXhon (Real.exp t) (Real.exp_pos t)).congr
        (Eventually.of_forall (fun s => by simp only [sq_abs]))
    have h5 := KJ_pointwise (g := fun s => |X (Real.exp t) s|) hε habs hθ
    have h5' : (MmPsi ε X θ t) ^ 2 ≤ 3 * (∫ s in Iθ, KJ ε θ s * (X (Real.exp t) s) ^ 2) := by
      simpa only [sq_abs, MmPsi] using h5
    calc (ENNReal.ofReal (MmPsi ε X θ t)) ^ 2
        = ENNReal.ofReal ((MmPsi ε X θ t) ^ 2) := (ENNReal.ofReal_pow (hJnn t) 2).symm
      _ ≤ ENNReal.ofReal (3 * (∫ s in Iθ, KJ ε θ s * (X (Real.exp t) s) ^ 2)) :=
          ENNReal.ofReal_le_ofReal h5'
      _ = 3 * ENNReal.ofReal (∫ s in Iθ, KJ ε θ s * (X (Real.exp t) s) ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
          simp
      _ = 3 * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s) := by rw [hconv]
  -- assembly
  have hchain : ENNReal.ofReal ((F z θ) ^ 2)
      ≤ 3 * (∫⁻ t, muKHat δ z t * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)) := by
    refine step1.trans ?_
    refine (mu_sq_le_sq step2).trans ?_
    refine step3.trans ?_
    rw [step4]
    refine (le_of_eq (one_mul _)).trans ?_
    refine (lintegral_mono (fun t => mul_le_mul' le_rfl (step5 t))).trans ?_
    rw [show (∫⁻ t, muKHat δ z t
          * (3 * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)))
        = ∫⁻ t, 3 * (muKHat δ z t
            * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)) from
      lintegral_congr (fun t => by ring)]
    exact le_of_eq (MeasureTheory.lintegral_const_mul' _ _ mu_three_ne_top)
  calc ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)
      = ENNReal.ofReal ((F z θ) ^ 2) * muSigHat θ := by
        rw [muSigHat_def]
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ (3 * (∫⁻ t, muKHat δ z t * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)))
          * muSigHat θ := mul_le_mul' hchain le_rfl
    _ = 3 * muSigHat θ * (∫⁻ t, muKHat δ z t * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)) := by
        ring
    _ = 3 * muSigHat θ * muQHat δ ε X z θ := by simp only [muQHat]

/-! ## The angular Schur bound -/

/-- The angular Schur bound of `thWeightCmp`, in `ℝ≥0∞`, a.e. on `Iθ`. -/
theorem mu_BHat_le {ε K₁ : ℝ} (hε : 0 < ε) (hK₁nn : 0 ≤ K₁)
    (hSchur : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ θ in Iθ, σθ θ * KJ ε θ u) ≤ K₁ * σθ u) :
    ∀ᵐ s ∂(volume.restrict Iθ), muBHat ε s ≤ ENNReal.ofReal K₁ * muSigHat s := by
  have hσint : Integrable (fun θ : ℝ => σθ θ) (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  filter_upwards [KJ_schur_ae (K₁ := K₁) (ε := ε) hSchur] with s hs
  have hInt : IntegrableOn (fun θ : ℝ => σθ θ * KJ ε θ s) Iθ := by
    have hCnn : (0 : ℝ) ≤ 3 * (ε * sMass)⁻¹ :=
      mul_nonneg (by norm_num) (inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le))
    refine integrable_of_le
      (hσint.aestronglyMeasurable.mul
        ((Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).measurable.comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ) (KJ_nonneg hε θ s)))
      (hσint.const_mul (3 * (ε * sMass)⁻¹))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg hCnn (Work.FTS.EllipticEst.thEta_nonneg hθ)))
      (ae_le_of_forall_mem_Ioo (fun θ hθ => by
        rw [mul_comm (σθ θ) (KJ ε θ s)]
        exact mul_le_mul_of_nonneg_right (KJ_le hε θ s)
          (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)))
  have hconv : muBHat ε s = ∫⁻ θ in Iθ, ENNReal.ofReal (σθ θ * KJ ε θ s) := by
    change (∫⁻ θ in Iθ, muSigHat θ * muJHat ε θ s)
      = ∫⁻ θ in Iθ, ENNReal.ofReal (σθ θ * KJ ε θ s)
    exact lintegral_congr (fun θ => muSigHat_mul_muJHat ε θ s hε)
  have h2 : (∫⁻ θ in Iθ, ENNReal.ofReal (σθ θ * KJ ε θ s))
      = ENNReal.ofReal (∫ θ in Iθ, σθ θ * KJ ε θ s) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ)
          (KJ_nonneg hε θ s)))).symm
  calc muBHat ε s = ∫⁻ θ in Iθ, ENNReal.ofReal (σθ θ * KJ ε θ s) := hconv
    _ = ENNReal.ofReal (∫ θ in Iθ, σθ θ * KJ ε θ s) := h2
    _ ≤ ENNReal.ofReal (K₁ * σθ s) := ENNReal.ofReal_le_ofReal hs
    _ = ENNReal.ofReal K₁ * muSigHat s := (mu_ofReal_mul_muSigHat K₁ hK₁nn s).symm

/-! ## The `(θ, (t,s))`-Tonelli step with the angular Schur bound -/

/-- The four-factor integrand of the Tonelli step: `σ̂(θ) k(z,t) Ĵ(ε,θ,s) X̂(t,s)`. -/
def muJX (X : ℝ → ℝ → ℝ) (δ ε z θ : ℝ) : ℝ → ℝ → ℝ≥0∞ :=
  fun t s => muSigHat θ * muKHat δ z t * muJHat ε θ s * muXsHat X t s

lemma muJX_def (X : ℝ → ℝ → ℝ) (δ ε z θ t s : ℝ) :
    muJX X δ ε z θ t s = muSigHat θ * muKHat δ z t * muJHat ε θ s * muXsHat X t s :=
  rfl

/-- A.e. measurability of the three-variable integrand `muJX`. -/
lemma mu_aemeasurable_muJX3 {X : ℝ → ℝ → ℝ} {δ ε : ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) (z : ℝ) :
    AEMeasurable (fun q : ℝ × (ℝ × ℝ) => muJX X δ ε z q.1 q.2.1 q.2.2)
      ((volume.restrict Iθ).prod (volume.prod (volume.restrict Iθ))) := by
  rw [show (fun q : ℝ × (ℝ × ℝ) => muJX X δ ε z q.1 q.2.1 q.2.2)
      = fun q : ℝ × (ℝ × ℝ) =>
          muSigHat q.1 * muKHat δ z q.2.1 * muJHat ε q.1 q.2.2
            * muXsHat X q.2.1 q.2.2 from by funext q; rw [muJX_def]]
  have a1 : AEMeasurable (fun q : ℝ × (ℝ × ℝ) => muSigHat q.1)
      ((volume.restrict Iθ).prod (volume.prod (volume.restrict Iθ))) :=
    mu_aemeasurable_sigHat.comp_fst
  have a2 : AEMeasurable (fun q : ℝ × (ℝ × ℝ) => muKHat δ z q.2.1)
      ((volume.restrict Iθ).prod (volume.prod (volume.restrict Iθ))) :=
    ((mu_measurable_kHat δ z).comp measurable_snd.fst).aemeasurable
  have a3 : AEMeasurable (fun q : ℝ × (ℝ × ℝ) => muJHat ε q.1 q.2.2)
      ((volume.restrict Iθ).prod (volume.prod (volume.restrict Iθ))) :=
    ((mu_measurable_KJhat ε).comp (measurable_fst.prodMk measurable_snd.snd)).aemeasurable
  have a4 : AEMeasurable (fun q : ℝ × (ℝ × ℝ) => muXsHat X q.2.1 q.2.2)
      ((volume.restrict Iθ).prod (volume.prod (volume.restrict Iθ))) :=
    (mu_aemeasurable_XsHat hXmeas).comp_snd
  exact ((a1.mul a2).mul a3).mul a4

/-- A.e. measurability of the two-variable integrand `muJX` at fixed `θ`. -/
lemma mu_aemeasurable_muJX2 {X : ℝ → ℝ → ℝ} {δ ε z θ : ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    AEMeasurable (fun p : ℝ × ℝ => muJX X δ ε z θ p.1 p.2)
      (volume.prod (volume.restrict Iθ)) := by
  rw [show (fun p : ℝ × ℝ => muJX X δ ε z θ p.1 p.2)
      = fun p : ℝ × ℝ =>
          muSigHat θ * muKHat δ z p.1 * muJHat ε θ p.2 * muXsHat X p.1 p.2
        from by funext p; rw [muJX_def]]
  have a1 : AEMeasurable (fun p : ℝ × ℝ => muSigHat θ * muKHat δ z p.1)
      (volume.prod (volume.restrict Iθ)) :=
    (measurable_const.mul ((mu_measurable_kHat δ z).comp measurable_fst)).aemeasurable
  have a2 : AEMeasurable (fun p : ℝ × ℝ => muJHat ε θ p.2)
      (volume.prod (volume.restrict Iθ)) :=
    ((mu_measurable_KJhat ε).comp (measurable_const.prodMk measurable_snd)).aemeasurable
  have a3 : AEMeasurable (fun p : ℝ × ℝ => muXsHat X p.1 p.2)
      (volume.prod (volume.restrict Iθ)) := mu_aemeasurable_XsHat hXmeas
  exact (a1.mul a2).mul a3

/-- Unfolding `muQHat` and pulling the constants inside. -/
theorem mu_schurSwap_unfold {X : ℝ → ℝ → ℝ} {δ ε : ℝ} (z : ℝ) :
    (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)
      = ∫⁻ θ in Iθ, ∫⁻ t, ∫⁻ s in Iθ, muJX X δ ε z θ t s := by
  refine lintegral_congr (μ := volume.restrict Iθ)
    (f := fun θ : ℝ => muSigHat θ * muQHat δ ε X z θ)
    (g := fun θ : ℝ => ∫⁻ t, ∫⁻ s in Iθ, muJX X δ ε z θ t s)
    (fun θ => ?_)
  refine (congrArg (fun u : ℝ≥0∞ => muSigHat θ * u)
    (muQHat_def δ ε X z θ)).trans ?_
  refine (MeasureTheory.lintegral_const_mul' (muSigHat θ)
    (fun t : ℝ => muKHat δ z t * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s))
    ENNReal.ofReal_ne_top).symm.trans ?_
  refine lintegral_congr (μ := volume)
    (f := fun t : ℝ => muSigHat θ * (muKHat δ z t
      * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)))
    (g := fun t : ℝ => ∫⁻ s in Iθ, muJX X δ ε z θ t s)
    (fun t => ?_)
  refine (mul_assoc (muSigHat θ) (muKHat δ z t)
    (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)).symm.trans ?_
  refine (MeasureTheory.lintegral_const_mul' (muSigHat θ * muKHat δ z t)
    (fun s : ℝ => muJHat ε θ s * muXsHat X t s)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).symm.trans ?_
  exact lintegral_congr (μ := volume.restrict Iθ)
    (f := fun s : ℝ => (muSigHat θ * muKHat δ z t) * (muJHat ε θ s * muXsHat X t s))
    (g := fun s : ℝ => muJX X δ ε z θ t s)
    (fun s => by rw [muJX_def]; ring)

/-- **Tonelli I**: pack the `(t,s)`-pair into a single product-measure integral. -/
theorem mu_ton_pair {X : ℝ → ℝ → ℝ} {δ ε z θ : ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    (∫⁻ t, ∫⁻ s in Iθ, muJX X δ ε z θ t s)
      = ∫⁻ q : ℝ × ℝ, muJX X δ ε z θ q.1 q.2 ∂(volume.prod (volume.restrict Iθ)) :=
  MeasureTheory.lintegral_lintegral (μ := volume) (ν := volume.restrict Iθ)
    (f := muJX X δ ε z θ)
    (mu_aemeasurable_muJX2 (X := X) (δ := δ) (ε := ε) (z := z) (θ := θ) hXmeas)

/-- **Tonelli II**: swap the outer `θ`-integral with the product integral. -/
theorem mu_ton_swap {X : ℝ → ℝ → ℝ} {δ ε z : ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    (∫⁻ θ in Iθ, (∫⁻ q : ℝ × ℝ, muJX X δ ε z θ q.1 q.2
        ∂(volume.prod (volume.restrict Iθ))))
      = ∫⁻ q : ℝ × ℝ, (∫⁻ θ in Iθ, muJX X δ ε z θ q.1 q.2)
          ∂(volume.prod (volume.restrict Iθ)) :=
  MeasureTheory.lintegral_lintegral_swap (μ := volume.restrict Iθ)
    (ν := volume.prod (volume.restrict Iθ))
    (f := fun θ (q : ℝ × ℝ) => muJX X δ ε z θ q.1 q.2)
    (show AEMeasurable (fun p : ℝ × (ℝ × ℝ) => muJX X δ ε z p.1 p.2.1 p.2.2)
        ((volume.restrict Iθ).prod (volume.prod (volume.restrict Iθ))) from
      mu_aemeasurable_muJX3 (X := X) (δ := δ) (ε := ε) hXmeas z)

/-- **Tonelli III**: unpack the product integral back into the `(t,s)`-iteration. -/
theorem mu_ton_split {X : ℝ → ℝ → ℝ} {δ ε z : ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    (∫⁻ q : ℝ × ℝ, (∫⁻ θ in Iθ, muJX X δ ε z θ q.1 q.2)
        ∂(volume.prod (volume.restrict Iθ)))
      = ∫⁻ t, ∫⁻ s in Iθ, ∫⁻ θ in Iθ, muJX X δ ε z θ t s :=
  MeasureTheory.lintegral_prod (μ := volume) (ν := volume.restrict Iθ)
    (f := fun q : ℝ × ℝ => ∫⁻ θ in Iθ, muJX X δ ε z θ q.1 q.2)
    (AEMeasurable.lintegral_prod_left' (μ := volume.restrict Iθ)
      (ν := volume.prod (volume.restrict Iθ))
      (f := fun p : ℝ × (ℝ × ℝ) => muJX X δ ε z p.1 p.2.1 p.2.2)
      (mu_aemeasurable_muJX3 (X := X) (δ := δ) (ε := ε) hXmeas z))

/-- **Tonelli IV**: pull the `t`-constants out of the inner `θ`-integral, leaving `muBHat`. -/
theorem mu_ton_const {X : ℝ → ℝ → ℝ} {δ ε z : ℝ} :
    (∫⁻ t, ∫⁻ s in Iθ, ∫⁻ θ in Iθ, muJX X δ ε z θ t s)
      = ∫⁻ t, ∫⁻ s in Iθ, muKHat δ z t * muXsHat X t s * muBHat ε s := by
  refine lintegral_congr (fun t => ?_)
  refine lintegral_congr (fun s => ?_)
  rw [muBHat_def]
  calc (∫⁻ θ in Iθ, muJX X δ ε z θ t s)
      = ∫⁻ θ in Iθ, (muKHat δ z t * muXsHat X t s) * (muSigHat θ * muJHat ε θ s) :=
        lintegral_congr (fun θ => by rw [muJX_def]; ring)
    _ = (muKHat δ z t * muXsHat X t s) * ∫⁻ θ in Iθ, muSigHat θ * muJHat ε θ s :=
        MeasureTheory.lintegral_const_mul' (muKHat δ z t * muXsHat X t s)
          (fun θ : ℝ => muSigHat θ * muJHat ε θ s)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- **The Tonelli step of the Schur bound.**  The `θ`-integral of the two-kernel pairing equals
the `(t,s)`-iterated integral in which the angular kernel has been summed against `σ̂`. -/
theorem mu_schurSwap_swap {X : ℝ → ℝ → ℝ} {δ ε : ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)))
    (z : ℝ) :
    (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)
      = ∫⁻ t, ∫⁻ s in Iθ, muKHat δ z t * muXsHat X t s * muBHat ε s := by
  calc (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)
      = ∫⁻ θ in Iθ, ∫⁻ t, ∫⁻ s in Iθ, muJX X δ ε z θ t s :=
        mu_schurSwap_unfold (X := X) (δ := δ) (ε := ε) z
    _ = ∫⁻ θ in Iθ, (∫⁻ q : ℝ × ℝ, muJX X δ ε z θ q.1 q.2
          ∂(volume.prod (volume.restrict Iθ))) :=
        lintegral_congr (μ := volume.restrict Iθ)
          (f := fun θ : ℝ => ∫⁻ t, ∫⁻ s in Iθ, muJX X δ ε z θ t s)
          (g := fun θ : ℝ => ∫⁻ q : ℝ × ℝ, muJX X δ ε z θ q.1 q.2
              ∂(volume.prod (volume.restrict Iθ)))
          (fun θ => mu_ton_pair (X := X) (δ := δ) (ε := ε) (z := z) (θ := θ) hXmeas)
    _ = ∫⁻ q : ℝ × ℝ, (∫⁻ θ in Iθ, muJX X δ ε z θ q.1 q.2)
          ∂(volume.prod (volume.restrict Iθ)) := mu_ton_swap (X := X) (δ := δ) (ε := ε) hXmeas
    _ = ∫⁻ t, ∫⁻ s in Iθ, ∫⁻ θ in Iθ, muJX X δ ε z θ t s :=
        mu_ton_split (X := X) (δ := δ) (ε := ε) hXmeas
    _ = ∫⁻ t, ∫⁻ s in Iθ, muKHat δ z t * muXsHat X t s * muBHat ε s :=
        mu_ton_const (X := X) (δ := δ) (ε := ε) (z := z)

/-- **The Schur step.**  For every `z` the `θ`-integral of `σ̂ · QHat` is at most `ofReal K₁` times
the `(t,s)`-iterated integral in which the angular kernel has already been summed against `σ̂`. -/
theorem mu_schurSwap {X : ℝ → ℝ → ℝ} {δ ε K₁ : ℝ} (hε : 0 < ε) (hK₁nn : 0 ≤ K₁)
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)))
    (hSchur : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ θ in Iθ, σθ θ * KJ ε θ u) ≤ K₁ * σθ u)
    (z : ℝ) :
    (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)
      ≤ ENNReal.ofReal K₁ * ∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by
  rw [mu_schurSwap_swap (X := X) (δ := δ) (ε := ε) hXmeas z]
  calc (∫⁻ t, ∫⁻ s in Iθ, muKHat δ z t * muXsHat X t s * muBHat ε s)
      ≤ ∫⁻ t, ∫⁻ s in Iθ, muKHat δ z t * muXsHat X t s
          * (ENNReal.ofReal K₁ * muSigHat s) := by
        refine lintegral_mono (fun t => ?_)
        refine lintegral_mono_ae ?_
        filter_upwards [mu_BHat_le (ε := ε) (K₁ := K₁) hε hK₁nn hSchur] with s hs
        exact mul_le_mul' le_rfl hs
    _ = ENNReal.ofReal K₁ * ∫⁻ t, muKHat δ z t
          * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by
        have hinner : ∀ t : ℝ,
            (∫⁻ s in Iθ, muKHat δ z t * muXsHat X t s * (ENNReal.ofReal K₁ * muSigHat s))
              = ENNReal.ofReal K₁ * (muKHat δ z t
                  * ∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by
          intro t
          calc (∫⁻ s in Iθ, muKHat δ z t * muXsHat X t s
                * (ENNReal.ofReal K₁ * muSigHat s))
              = ∫⁻ s in Iθ, (muKHat δ z t * ENNReal.ofReal K₁)
                  * (muXsHat X t s * muSigHat s) :=
                lintegral_congr (fun s => by ring)
            _ = (muKHat δ z t * ENNReal.ofReal K₁)
                  * ∫⁻ s in Iθ, muXsHat X t s * muSigHat s :=
                MeasureTheory.lintegral_const_mul' _ _
                  (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
            _ = ENNReal.ofReal K₁ * (muKHat δ z t
                  * ∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by ring
        calc (∫⁻ t, ∫⁻ s in Iθ, muKHat δ z t * muXsHat X t s
              * (ENNReal.ofReal K₁ * muSigHat s))
            = ∫⁻ t, ENNReal.ofReal K₁ * (muKHat δ z t
                * ∫⁻ s in Iθ, muXsHat X t s * muSigHat s) :=
              lintegral_congr hinner
          _ = ENNReal.ofReal K₁ * ∫⁻ t, muKHat δ z t
                * (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) := by
              rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal K₁)
                (fun t : ℝ => muKHat δ z t * ∫⁻ s in Iθ, muXsHat X t s * muSigHat s)
                ENNReal.ofReal_ne_top]

end Work.FTS.EllSol.EllPkgAux.MollDom
