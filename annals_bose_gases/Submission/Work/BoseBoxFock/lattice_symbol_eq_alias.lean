import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.LatSym.exists_aliasPsi
import Submission.Work.BoseBoxFock.LatSym.integral_conj_mul_symOp
import Submission.Work.BoseBoxFock.LatSym.integral_mul_lap3_eq_of_quad
import Submission.Work.BoseBoxFock.LatSym.poisson_scaled_general
import Submission.Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped Real BigOperators

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `‖(r : ℂ)‖ = |r|`. -/
lemma norm_coe_real (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  change ‖Complex.ofRealLI r‖ = |r|
  rw [LinearIsometry.norm_map, Real.norm_eq_abs]

/-- The `n`-th iterated derivative of a complexified real function has the same norm. -/
lemma norm_iteratedFDeriv_ofReal {σ : E3 → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (n : ℕ) (p : E3) :
    ‖iteratedFDeriv ℝ n (fun q : E3 => (σ q : ℂ)) p‖ = ‖iteratedFDeriv ℝ n σ p‖ := by
  have h : (fun q : E3 => (σ q : ℂ)) = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ σ := rfl
  rw [h]
  exact LinearIsometry.norm_iteratedFDeriv_comp_left (x := p) (n := (n : WithTop ℕ∞)) (f := σ)
    (i := n) Complex.ofRealLI (hσ.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) le_rfl

/-- The complexified symbol is smooth. -/
lemma contDiff_ofReal_comp {σ : E3 → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 => (σ q : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hσ

/-- A continuous function whose topological support lies in `closedBall 0 r` has compact support. -/
lemma hasCompactSupport_of_tsupport_subset {g : E3 → ℂ} {r : ℝ}
    (h : tsupport g ⊆ Metric.closedBall 0 r) : HasCompactSupport g :=
  (isCompact_closedBall (0 : E3) r).of_isClosed_subset (isClosed_tsupport g) h

/-- The autocorrelation of a smooth compactly supported `g` is smooth. -/
lemma autocorr_contDiff' {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ContDiff ℝ (⊤ : ℕ∞) (autocorr g) := Green.autocorr_contDiff hg hgc

lemma autocorr_hasCompactSupport' {g : E3 → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (autocorr g) := Green.hasCompactSupport_autocorr hgc

/-- Iterated directional derivatives of a smooth function are smooth. -/
lemma contDiff_dIter' {f : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List E3) :
    ContDiff ℝ (⊤ : ℕ∞) (dIter f L) := by
  induction L with
  | nil => simpa using hf
  | cons v L ih =>
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 => fderiv ℝ (dIter f L) p v) :=
      (ih.fderiv_right (by simp)).clm_apply contDiff_const
    simpa only [dIter_cons] using h

/-- `lap3 f` is continuous for smooth `f`. -/
lemma continuous_lap3' {f : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (lap3 f) := by
  have h : lap3 f = fun p : E3 => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      dIter f (lap3List a b c) p := rfl
  rw [h]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_finsetSum _ fun c _ => (contDiff_dIter' hf _).continuous

/-- `x ^ (-n) = (x^n)⁻¹` for `0 ≤ x`. -/
lemma rpow_neg_nat' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : x ^ (-(n:ℝ)) = (x ^ n)⁻¹ := by
  rw [Real.rpow_neg hx]
  congr 1
  exact Real.rpow_natCast x n

/-- Conjugation commutes with the Bochner integral. -/
lemma integral_conj_eq (f : E3 → ℂ) (hf : MeasureTheory.Integrable f) :
    (∫ p : E3, (starRingEnd ℂ) (f p)) = (starRingEnd ℂ) (∫ p : E3, f p) := by
  have h := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) hf
  rw [show (fun p : E3 => (starRingEnd ℂ) (f p)) = (Complex.conjCLE : ℂ → ℂ) ∘ f from rfl]
  rw [show (starRingEnd ℂ) (∫ p : E3, f p) = (Complex.conjCLE : ℂ → ℂ) (∫ p : E3, f p)
      from rfl]
  exact h


/-- **Decay of the aliasing samples.**  For `‖η‖ ≥ 2ℓ` the Fourier sample of the
symbol-weighted spectral density is bounded by `1728 · ‖D⁶σ‖₁ · ‖autocorr g‖₁ · ‖η‖⁻⁶`.

The two potentials `Ψ_±` of `LatSym.exists_aliasPsi` turn the `Δ³` on the symbol into the `Δ³` on
the potentials (via `LatSym.integral_mul_lap3_eq_of_quad`), which is what produces the `‖η‖⁻⁶`
decay and makes the aliasing series summable. -/
theorem aliasSample_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {σ : E3 → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hσg : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    (hσ6 : MeasureTheory.Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖))
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    {η : E3} (hη : 2 * ℓ ≤ ‖η‖) :
    ‖(∫ p : E3, (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))‖
      ≤ 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) *
          (∫ u : E3, ‖autocorr g u‖) * ‖η‖ ^ (-6 : ℝ) := by
  classical
  have hℓη : ℓ < ‖η‖ := by linarith
  have hηpos : 0 < ‖η‖ := by linarith
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset hgs
  obtain ⟨Ψ₁, hΨ₁cd, hΨ₁lap, hΨ₁bd, hΨ₁dec⟩ := (LatSym.exists_aliasPsi hℓ hg hgs hℓη).1
  obtain ⟨Ψ₂, hΨ₂cd, hΨ₂lap, hΨ₂bd, hΨ₂dec⟩ := (LatSym.exists_aliasPsi hℓ hg hgs hℓη).2
  set M : ℝ := ∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖ with hM
  set A₁ : ℝ := ∫ u : E3, ‖autocorr g u‖ with hA₁
  have hMnn : 0 ≤ M := by rw [hM]; exact integral_nonneg fun p => norm_nonneg _
  have hAnn : 0 ≤ A₁ := by rw [hA₁]; exact integral_nonneg fun u => norm_nonneg _
  have hsplit : ∀ p : E3, ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ)
      = (Submission.BoseGases.kinFT (autocorr g) p
          + (starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) / 2 := by
    intro p
    have h1 : ‖Submission.BoseGases.kinFT g p‖ ^ 2
        = (Submission.BoseGases.kinFT (autocorr g) p).re := by
      rw [aliasFt hg hgc p]
      congr 1
      simp only [Submission.BoseGases.kinFT]
      exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
    rw [h1, Complex.add_conj]
    push_cast
    ring
  obtain ⟨A, hA⟩ := hσg
  have hσg' : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2 := ⟨A, hA⟩
  have hA0 : 0 ≤ A := by
    simpa using le_trans (abs_nonneg (σ 0)) (hA 0)
  obtain ⟨CK, hCK0, hCK⟩ :=
    SqrtKin.kinFT_decay_gen (autocorr_contDiff' hg hgc) (autocorr_hasCompactSupport' hgc) 6
  have hKcont : Continuous (Submission.BoseGases.kinFT (autocorr g)) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable (autocorr_integrable hg hgc)
  have hPhase : Continuous (fun p : E3 => Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))) :=
    Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_id)))))
  have hPhase' : Continuous (fun p : E3 => Complex.exp (Complex.I * (inner ℝ η p : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_id))))
  have hexp_norm : ∀ p : E3, ‖Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))‖ = 1 := by
    intro p
    rw [Complex.norm_exp]
    have : (-(Complex.I * (inner ℝ η p : ℂ))).re = 0 := by simp
    rw [this, Real.exp_zero]
  have hσA : ∀ p : E3, ‖(σ p : ℂ)‖ ≤ A * (1 + ‖p‖) ^ 2 := by
    intro p
    rw [norm_coe_real]
    exact hA p
  have hIntK : Integrable (fun p : E3 => A * CK / (1 + ‖p‖) ^ 4) := by
    have hfin : (Module.finrank ℝ E3 : ℝ) < 4 := by
      rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num
    have h := (integrable_one_add_norm (E := E3) (μ := volume) hfin).const_mul (A * CK)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    show A * CK * (1 + ‖p‖) ^ (-(4 : ℝ)) = A * CK / (1 + ‖p‖) ^ 4
    rw [show (1 + ‖p‖) ^ (-(4 : ℝ)) = ((1 + ‖p‖) ^ 4)⁻¹ from by
      rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖p‖)]
      congr 1
      exact Real.rpow_natCast (1 + ‖p‖) 4, div_eq_mul_inv]
  have hInt₁ : Integrable (fun p : E3 => (σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
      Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))) := by
    refine hIntK.mono' (((Complex.continuous_ofReal.comp hσ.continuous).mul hKcont).mul
      hPhase).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    show ‖(σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
          Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))‖ ≤ A * CK / (1 + ‖p‖) ^ 4
    rw [norm_mul, norm_mul, hexp_norm p, mul_one]
    calc ‖(σ p : ℂ)‖ * ‖Submission.BoseGases.kinFT (autocorr g) p‖
        ≤ (A * (1 + ‖p‖) ^ 2) * (CK / (1 + ‖p‖) ^ 6) :=
          mul_le_mul (hσA p) (hCK p) (norm_nonneg _) (mul_nonneg hA0 (by positivity))
      _ = A * CK / (1 + ‖p‖) ^ 4 := by field_simp
  have hInt₂ : Integrable (fun p : E3 => (σ p : ℂ) *
      ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
      Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))) := by
    refine hIntK.mono' (((Complex.continuous_ofReal.comp hσ.continuous).mul
      (Complex.continuous_conj.comp hKcont)).mul
      hPhase).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    show ‖(σ p : ℂ) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
          Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))‖ ≤ A * CK / (1 + ‖p‖) ^ 4
    have h3 : ‖(starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)‖ ≤ CK / (1 + ‖p‖) ^ 6 := by
      rw [Complex.norm_conj]; exact hCK p
    rw [norm_mul, norm_mul, hexp_norm p, mul_one]
    calc ‖(σ p : ℂ)‖ * ‖(starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)‖
        ≤ (A * (1 + ‖p‖) ^ 2) * (CK / (1 + ‖p‖) ^ 6) :=
          mul_le_mul (hσA p) h3 (norm_nonneg _) (mul_nonneg hA0 (by positivity))
      _ = A * CK / (1 + ‖p‖) ^ 4 := by field_simp
  have hdecomp : (∫ p : E3, (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
      = ((∫ p : E3, (σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
            Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
          + (∫ p : E3, (σ p : ℂ) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
            Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))) / 2 := by
    rw [show (∫ p : E3, (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
        = ∫ p : E3, ((σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))
            + (σ p : ℂ) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))) / 2 from
      integral_congr_ae (Filter.Eventually.of_forall fun p => by
        simp only [hsplit p]
        ring)]
    rw [integral_div, integral_add hInt₁ hInt₂]
  have hT₁ : (∫ p : E3, (σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
        Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
      = -(∫ p : E3, lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₁ p) := by
    have hpt : ∀ p : E3, (σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
        Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))) = (σ p : ℂ) * (-(lap3 Ψ₁ p)) := by
      intro p
      rw [hΨ₁lap p]
      ring
    rw [show (∫ p : E3, (σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
          Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
        = ∫ p : E3, (σ p : ℂ) * (-(lap3 Ψ₁ p)) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [show (∫ p : E3, (σ p : ℂ) * (-(lap3 Ψ₁ p))) = -(∫ p : E3, (σ p : ℂ) * lap3 Ψ₁ p) from by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)]
    rw [LatSym.integral_mul_lap3_eq_of_quad hσ hσg' hσ6 hΨ₁cd hΨ₁dec]
  have hT₂ : (∫ p : E3, (σ p : ℂ) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
        Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
      = -(starRingEnd ℂ) (∫ p : E3, lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₂ p) := by
    have hpt : ∀ p : E3, (σ p : ℂ) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
        Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))
          = (σ p : ℂ) * (-(starRingEnd ℂ (lap3 Ψ₂ p))) := by
      intro p
      have hconjE : (starRingEnd ℂ) (Complex.exp (Complex.I * (inner ℝ η p : ℂ)))
          = Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))) := by
        rw [← Complex.exp_conj]
        congr 1
        simp
      have hcL : (starRingEnd ℂ) (lap3 Ψ₂ p)
          = -(starRingEnd ℂ (Submission.BoseGases.kinFT (autocorr g) p)) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))) := by
        rw [hΨ₂lap p, map_mul, map_neg, hconjE]
      rw [hcL]
      ring
    rw [show (∫ p : E3, (σ p : ℂ) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
          Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
        = ∫ p : E3, (σ p : ℂ) * (-(starRingEnd ℂ (lap3 Ψ₂ p))) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [show (∫ p : E3, (σ p : ℂ) * (-(starRingEnd ℂ (lap3 Ψ₂ p))))
        = -(∫ p : E3, (σ p : ℂ) * (starRingEnd ℂ (lap3 Ψ₂ p))) from by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)]
    have hlap2 : lap3 Ψ₂ = fun p : E3 =>
        -(Submission.BoseGases.kinFT (autocorr g) p) * Complex.exp (Complex.I * (inner ℝ η p : ℂ)) :=
      funext hΨ₂lap
    have hcont2 : Continuous (fun p : E3 => (σ p : ℂ) * lap3 Ψ₂ p) := by
      rw [hlap2]
      exact (Complex.continuous_ofReal.comp hσ.continuous).mul
        (hKcont.neg.mul hPhase')
    have hint : Integrable (fun p : E3 => (σ p : ℂ) * lap3 Ψ₂ p) := by
      refine hIntK.mono' hcont2.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
      show ‖(σ p : ℂ) * lap3 Ψ₂ p‖ ≤ A * CK / (1 + ‖p‖) ^ 4
      rw [norm_mul, hlap2]
      rw [norm_mul, norm_neg, Complex.norm_exp]
      have hre : (Complex.I * (inner ℝ η p : ℂ)).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one]
      calc ‖(σ p : ℂ)‖ * ‖Submission.BoseGases.kinFT (autocorr g) p‖
          ≤ (A * (1 + ‖p‖) ^ 2) * (CK / (1 + ‖p‖) ^ 6) :=
            mul_le_mul (hσA p) (hCK p) (norm_nonneg _) (mul_nonneg hA0 (by positivity))
        _ = A * CK / (1 + ‖p‖) ^ 4 := by field_simp
    have hconj : (∫ p : E3, (σ p : ℂ) * (starRingEnd ℂ (lap3 Ψ₂ p)))
        = (starRingEnd ℂ) (∫ p : E3, (σ p : ℂ) * lap3 Ψ₂ p) := by
      rw [show (∫ p : E3, (σ p : ℂ) * (starRingEnd ℂ (lap3 Ψ₂ p)))
          = ∫ p : E3, (starRingEnd ℂ) ((σ p : ℂ) * lap3 Ψ₂ p) from
        integral_congr_ae (Filter.Eventually.of_forall fun p => by
          simp only [map_mul, Complex.conj_ofReal])]
      exact integral_conj_eq (fun p : E3 => (σ p : ℂ) * lap3 Ψ₂ p) hint
    rw [hconj, LatSym.integral_mul_lap3_eq_of_quad hσ hσg' hσ6 hΨ₂cd hΨ₂dec]
  have hlap3pt : ∀ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖ ≤ 27 * ‖iteratedFDeriv ℝ 6 σ p‖ := by
    intro p
    rw [← norm_iteratedFDeriv_ofReal hσ 6 p]
    exact norm_lap3_apply_le _ (contDiff_ofReal_comp hσ) p
  have hlap3m : Integrable (fun p : E3 => ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖) :=
    (hσ6.const_mul 27).mono' (continuous_lap3' (contDiff_ofReal_comp hσ)).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simpa using hlap3pt p)
  have hlap3int : (∫ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖) ≤ 27 * M := by
    rw [hM]
    calc (∫ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖)
        ≤ ∫ p : E3, 27 * ‖iteratedFDeriv ℝ 6 σ p‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
            (hσ6.const_mul 27) (Filter.Eventually.of_forall fun p => ?_)
          simpa using hlap3pt p
      _ = 27 * ∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖ := integral_const_mul 27 _
  have hmaj : Integrable (fun p : E3 =>
      ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖ * (A₁ / (‖η‖ - ℓ) ^ 6)) :=
    hlap3m.mul_const _
  have hbd₁ : ‖∫ p : E3, lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₁ p‖ ≤ 27 * M * (A₁ / (‖η‖ - ℓ) ^ 6) := by
    calc ‖∫ p : E3, lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₁ p‖
        ≤ ∫ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₁ p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖ * (A₁ / (‖η‖ - ℓ) ^ 6) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _) hmaj
            (Filter.Eventually.of_forall fun p => ?_)
          simpa only [norm_mul] using
            mul_le_mul_of_nonneg_left (hΨ₁bd p) (norm_nonneg _)
      _ = (∫ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖) * (A₁ / (‖η‖ - ℓ) ^ 6) :=
          integral_mul_const _ _
      _ ≤ 27 * M * (A₁ / (‖η‖ - ℓ) ^ 6) :=
          mul_le_mul_of_nonneg_right hlap3int (div_nonneg hAnn (by positivity))
  have hbd₂ : ‖∫ p : E3, lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₂ p‖ ≤ 27 * M * (A₁ / (‖η‖ - ℓ) ^ 6) := by
    calc ‖∫ p : E3, lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₂ p‖
        ≤ ∫ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₂ p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖ * (A₁ / (‖η‖ - ℓ) ^ 6) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _) hmaj
            (Filter.Eventually.of_forall fun p => ?_)
          simpa only [norm_mul] using
            mul_le_mul_of_nonneg_left (hΨ₂bd p) (norm_nonneg _)
      _ = (∫ p : E3, ‖lap3 (fun q : E3 => (σ q : ℂ)) p‖) * (A₁ / (‖η‖ - ℓ) ^ 6) :=
          integral_mul_const _ _
      _ ≤ 27 * M * (A₁ / (‖η‖ - ℓ) ^ 6) :=
          mul_le_mul_of_nonneg_right hlap3int (div_nonneg hAnn (by positivity))
  have hmain : ‖(∫ p : E3, (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))‖ ≤ 27 * M * (A₁ / (‖η‖ - ℓ) ^ 6) := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    calc ‖(∫ p : E3, (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))‖
        = ‖((∫ p : E3, (σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
            + (∫ p : E3, (σ p : ℂ) *
                ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))) / 2‖ := by rw [hdecomp]
      _ ≤ (‖∫ p : E3, (σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))‖
            + ‖∫ p : E3, (σ p : ℂ) *
                ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))‖) / 2 := by
          rw [norm_div, h2, div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 2)]
          linarith [norm_add_le
            (∫ p : E3, (σ p : ℂ) * (Submission.BoseGases.kinFT (autocorr g) p) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
            (∫ p : E3, (σ p : ℂ) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT (autocorr g) p)) *
              Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))]
      _ = (‖∫ p : E3, lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₁ p‖
            + ‖∫ p : E3, lap3 (fun q : E3 => (σ q : ℂ)) p * Ψ₂ p‖) / 2 := by
          rw [hT₁, hT₂, norm_neg, norm_neg, Complex.norm_conj]
      _ ≤ 27 * M * (A₁ / (‖η‖ - ℓ) ^ 6) := by linarith [hbd₁, hbd₂]
  have hrpow6 : ‖η‖ ^ (-6 : ℝ) = (‖η‖ ^ 6)⁻¹ := by
    rw [Real.rpow_neg hηpos.le]
    congr 1
    exact Real.rpow_natCast ‖η‖ 6
  have h64 : ((‖η‖ - ℓ) ^ 6)⁻¹ ≤ 64 * ‖η‖ ^ (-6 : ℝ) := by
    rw [hrpow6]
    have hpos : (0:ℝ) < ‖η‖ - ℓ := by linarith
    have h1 : ‖η‖ / 2 ≤ ‖η‖ - ℓ := by linarith
    have h2 : (‖η‖ / 2) ^ 6 ≤ (‖η‖ - ℓ) ^ 6 := pow_le_pow_left₀ (by positivity) h1 6
    have h3 : (‖η‖ / 2) ^ 6 = ‖η‖ ^ 6 / 64 := by rw [div_pow]; norm_num
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h2, h3]
  calc ‖(∫ p : E3, (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))‖
      ≤ 27 * M * (A₁ / (‖η‖ - ℓ) ^ 6) := hmain
    _ = 27 * M * A₁ * ((‖η‖ - ℓ) ^ 6)⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ 27 * M * A₁ * (64 * ‖η‖ ^ (-6 : ℝ)) :=
        mul_le_mul_of_nonneg_left h64 (by positivity)
    _ = 1728 * M * A₁ * ‖η‖ ^ (-6 : ℝ) := by norm_num; ring

/-! ## The momentum-side symbol `f p = σ p * ‖kinFT g p‖²` -/

/-- The momentum-side symbol of the aliasing identity. -/
noncomputable def specDens (σ : E3 → ℝ) (g : E3 → ℂ) : E3 → ℂ :=
  fun p => ((σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ)

@[simp] lemma specDens_apply' (σ : E3 → ℝ) (g : E3 → ℂ) (p : E3) :
    specDens σ g p = ((σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) := rfl

lemma specDens_exp_eq' (σ : E3 → ℝ) (g : E3 → ℂ) (η : E3) :
    (fun p : E3 => specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))))
      = fun p : E3 => (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ η p : ℂ))) := by
  funext p
  simp only [specDens, Complex.ofReal_mul]

lemma specDens_exp_eq_pos (σ : E3 → ℝ) (g : E3 → ℂ) (η : E3) :
    (fun p : E3 => specDens σ g p * Complex.exp (Complex.I * (inner ℝ η p : ℂ)))
      = fun p : E3 => (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ η p : ℂ)) := by
  funext p
  simp only [specDens, Complex.ofReal_mul]

lemma re_ofReal_mul_exp_neg_I (r θ : ℝ) :
    ((r : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ)))).re = r * Real.cos θ := by
  have h1 : Complex.exp (-(Complex.I * (θ : ℂ))) = Complex.exp (((-θ : ℝ)) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [h1, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg]
  ring

lemma re_ofReal_mul_exp_I (r θ : ℝ) :
    ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re = r * Real.cos θ := by
  have h1 : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp ((θ : ℝ) * Complex.I) := by
    congr 1
    ring
  rw [h1, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The symbol is integrable and decays like `‖p‖⁻⁴`. -/
lemma specDens_integrable {σ : E3 → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hσg : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    MeasureTheory.Integrable (specDens σ g) := by
  obtain ⟨A, hA⟩ := hσg
  have hA0 : 0 ≤ A := by simpa using le_trans (abs_nonneg (σ 0)) (hA 0)
  obtain ⟨CK, hCK0, hCK⟩ := SqrtKin.kinFT_decay_gen hg hgc 6
  have hfin : (Module.finrank ℝ E3 : ℝ) < 10 := by
    rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num
  have hmaj : Integrable (fun p : E3 => A * CK ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹) := by
    refine ((integrable_one_add_norm (E := E3) (μ := volume) hfin).const_mul
      (A * CK ^ 2)).congr (Filter.Eventually.of_forall fun p => ?_)
    show A * CK ^ 2 * (1 + ‖p‖) ^ (-(10:ℝ)) = A * CK ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹
    rw [show (1 + ‖p‖) ^ (-(10:ℝ)) = ((1 + ‖p‖) ^ 10)⁻¹ from by
      rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖p‖)]
      congr 1
      exact Real.rpow_natCast (1 + ‖p‖) 10]
  have hcont : Continuous (specDens σ g) :=
    Complex.continuous_ofReal.comp (hσ.continuous.mul
      ((Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
        (hg.continuous.integrable_of_hasCompactSupport hgc)).norm.pow 2))
  refine hmaj.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [specDens_apply', norm_coe_real]
  have hp : (0:ℝ) < 1 + ‖p‖ := by positivity
  have h4 : |σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2|
      ≤ (A * (1 + ‖p‖) ^ 2) * (CK / (1 + ‖p‖) ^ 6) ^ 2 := by
    have hs : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g p‖ ^ 2 := sq_nonneg _
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul (hA p) (pow_le_pow_left₀ (norm_nonneg _) (hCK p) 2) hs
      (mul_nonneg hA0 (by positivity))
  calc |σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2|
      ≤ (A * (1 + ‖p‖) ^ 2) * (CK / (1 + ‖p‖) ^ 6) ^ 2 := h4
    _ = A * CK ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹ := by field_simp; try ring

/-- **Summability of the Fourier samples of the symbol.** -/
lemma specDens_summable {ℓ : ℝ} (hℓ : 0 < ℓ) {σ : E3 → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hσg : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    (hσ6 : MeasureTheory.Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖))
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    Summable (fun m : Fin 3 → ℤ => ∫ p : E3, specDens σ g p *
      Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))) := by
  classical
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset hgs
  obtain ⟨A, hA⟩ := hσg
  obtain ⟨CK, hCK0, hCK⟩ := SqrtKin.kinFT_decay_gen hg hgc 6
  have hint : MeasureTheory.Integrable (specDens σ g) := specDens_integrable hσ ⟨A, hA⟩ hg hgc
  have hInt0 : 0 ≤ ∫ p : E3, ‖specDens σ g p‖ := integral_nonneg fun p => norm_nonneg _
  have hM0 : 0 ≤ ∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖ := integral_nonneg fun p => norm_nonneg _
  have hA₀0 : 0 ≤ ∫ u : E3, ‖autocorr g u‖ := integral_nonneg fun u => norm_nonneg _
  have hdec := fun (η : E3) (hη : 2 * ℓ ≤ ‖η‖) =>
    aliasSample_norm_le (ℓ := ℓ) hℓ hσ ⟨A, hA⟩ hσ6 hg hgs hη
  -- the comparison function
  refine Summable.of_norm_bounded
    ((summable_one_add_norm_latVec_pow_inv (N := 6) (by norm_num)).mul_left
      (1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
        (64 / ℓ ^ 6) + 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖)))
    (fun m => ?_)
  by_cases hm : 2 ≤ ‖latVec m‖
  · -- the large-`m` case: the decay estimate
    have hη : 2 * ℓ ≤ ‖ℓ • latVec m‖ := by
      rw [norm_smul, Real.norm_of_nonneg hℓ.le]
      have := mul_le_mul_of_nonneg_left hm hℓ.le
      linarith
    have h1 := hdec (ℓ • latVec m) hη
    rw [← specDens_exp_eq'] at h1
    -- rewrite `(ℓ ‖m‖)^{-6}` and compare with `(1 + ‖m‖)^{-6}`
    have h2 : ‖ℓ • latVec m‖ ^ (-6 : ℝ) = (1 / ℓ ^ 6) * (‖latVec m‖ ^ 6)⁻¹ := by
      rw [norm_smul, Real.norm_of_nonneg hℓ.le, Real.mul_rpow hℓ.le (norm_nonneg _),
        show ℓ ^ (-6 : ℝ) = ((ℓ ^ 6)⁻¹) from by
          rw [Real.rpow_neg hℓ.le]; congr 1; exact Real.rpow_natCast ℓ 6,
        show ‖latVec m‖ ^ (-6 : ℝ) = ((‖latVec m‖ ^ 6)⁻¹) from by
          rw [Real.rpow_neg (norm_nonneg _)]; congr 1; exact Real.rpow_natCast _ 6,
        one_div]
    have h3 : (‖latVec m‖ ^ 6)⁻¹ ≤ 64 * ((1 + ‖latVec m‖) ^ 6)⁻¹ := by
      have hpos1 : (0:ℝ) < ‖latVec m‖ ^ 6 := by positivity
      have hpos2 : (0:ℝ) < (1 + ‖latVec m‖) ^ 6 := by positivity
      have h5 : (1 + ‖latVec m‖) ^ 6 ≤ 64 * ‖latVec m‖ ^ 6 := by
        have h4 : (1 + ‖latVec m‖) ^ 6 ≤ (2 * ‖latVec m‖) ^ 6 :=
          pow_le_pow_left₀ (by positivity) (by linarith [hm]) 6
        calc (1 + ‖latVec m‖) ^ 6 ≤ (2 * ‖latVec m‖) ^ 6 := h4
          _ = 64 * ‖latVec m‖ ^ 6 := by ring
      rw [← div_eq_mul_inv (64), inv_eq_one_div (‖latVec m‖ ^ 6),
        div_le_div_iff₀ hpos1 hpos2]
      linarith [h5]
    calc ‖∫ p : E3, specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))‖
        ≤ 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
            ‖ℓ • latVec m‖ ^ (-6 : ℝ) := h1
      _ = 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
            ((1 / ℓ ^ 6) * (‖latVec m‖ ^ 6)⁻¹) := by rw [h2]
      _ ≤ 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
            ((1 / ℓ ^ 6) * (64 * ((1 + ‖latVec m‖) ^ 6)⁻¹)) := by
          have h1ℓ : (0:ℝ) ≤ 1 / ℓ ^ 6 := div_nonneg (by norm_num) (by positivity)
          have hc : (0:ℝ) ≤ 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) *
              (∫ u : E3, ‖autocorr g u‖) := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 h1ℓ) hc
      _ ≤ (1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
            (64 / ℓ ^ 6) + 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖)) *
            ((1 + ‖latVec m‖) ^ 6)⁻¹ := by
          have hC0 : 0 ≤ 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) *
              (∫ u : E3, ‖autocorr g u‖) := by positivity
          have h8 : 0 ≤ ((1 + ‖latVec m‖) ^ 6)⁻¹ := by positivity
          have h9 : 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
              (1 / ℓ ^ 6) * 64 ≤ 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) *
              (∫ u : E3, ‖autocorr g u‖) * (64 / ℓ ^ 6) + 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖) := by
            have : 0 ≤ 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖) := by positivity
            have h10 : 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) *
                (∫ u : E3, ‖autocorr g u‖) * (1 / ℓ ^ 6) * 64
                = 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) *
                  (∫ u : E3, ‖autocorr g u‖) * (64 / ℓ ^ 6) := by
              rw [div_eq_mul_one_div]; ring
            linarith
          calc 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
                ((1 / ℓ ^ 6) * (64 * ((1 + ‖latVec m‖) ^ 6)⁻¹))
              = (1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
                  (1 / ℓ ^ 6) * 64) * ((1 + ‖latVec m‖) ^ 6)⁻¹ := by ring
            _ ≤ (1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
                  (64 / ℓ ^ 6) + 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖)) *
                  ((1 + ‖latVec m‖) ^ 6)⁻¹ := mul_le_mul_of_nonneg_right h9 h8
  · -- the small-`m` case
    push_neg at hm
    have h1 : ‖∫ p : E3, specDens σ g p *
        Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))‖
        ≤ ∫ p : E3, ‖specDens σ g p‖ := by
      calc ‖∫ p : E3, specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))‖
          ≤ ∫ p : E3, ‖specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ p : E3, ‖specDens σ g p‖ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            show ‖specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))‖
              = ‖specDens σ g p‖
            rw [norm_mul, Complex.norm_exp]
            have : (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ))).re = 0 := by simp
            rw [this, Real.exp_zero, mul_one]
    have h3 : (1 + ‖latVec m‖) ^ 6 < 3 ^ 6 := by
      have hlt : 1 + ‖latVec m‖ < 3 := by linarith [hm, norm_nonneg (latVec m)]
      exact pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    have h4 : (∫ p : E3, ‖specDens σ g p‖) ≤ 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖) *
        ((1 + ‖latVec m‖) ^ 6)⁻¹ := by
      have hle : (1:ℝ) ≤ 3 ^ 6 * ((1 + ‖latVec m‖) ^ 6)⁻¹ := by
        rw [le_mul_inv_iff₀ (by positivity : (0:ℝ) < (1 + ‖latVec m‖) ^ 6)]
        simpa using le_of_lt h3
      calc ∫ p : E3, ‖specDens σ g p‖ = (∫ p : E3, ‖specDens σ g p‖) * 1 := by ring
        _ ≤ (∫ p : E3, ‖specDens σ g p‖) * (3 ^ 6 * ((1 + ‖latVec m‖) ^ 6)⁻¹) :=
              mul_le_mul_of_nonneg_left hle hInt0
        _ = 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖) * ((1 + ‖latVec m‖) ^ 6)⁻¹ := by ring
    calc ‖∫ p : E3, specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))‖
        ≤ ∫ p : E3, ‖specDens σ g p‖ := h1
      _ ≤ 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖) * ((1 + ‖latVec m‖) ^ 6)⁻¹ := h4
      _ ≤ (1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
            (64 / ℓ ^ 6) + 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖)) *
            ((1 + ‖latVec m‖) ^ 6)⁻¹ := by
          have h8 : 0 ≤ ((1 + ‖latVec m‖) ^ 6)⁻¹ := by positivity
          have h10 : 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖)
              ≤ 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (∫ u : E3, ‖autocorr g u‖) *
                (64 / ℓ ^ 6) + 3 ^ 6 * (∫ p : E3, ‖specDens σ g p‖) := by
            have : 0 ≤ 1728 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) *
                (∫ u : E3, ‖autocorr g u‖) * (64 / ℓ ^ 6) := by positivity
            linarith
          exact mul_le_mul_of_nonneg_right h10 h8


/-- The symbol `p ↦ σ p ‖kinFT g p‖²` is continuous. -/
lemma specDens_continuous {σ : E3 → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    Continuous (specDens σ g) :=
  Complex.continuous_ofReal.comp (hσ.continuous.mul
    ((Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
      (hg.continuous.integrable_of_hasCompactSupport hgc)).norm.pow 2))

/-- **The symbol decays like `‖p‖⁻⁴`.**  `|σ p| ≤ A (1+‖p‖)²` and
`‖kinFT g p‖ ≤ CK (1+‖p‖)⁻⁶` give `(1+‖p‖)⁴ ‖specDens σ g p‖ ≤ A CK²`. -/
lemma specDens_decay {σ : E3 → ℝ}
    (hσg : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ p : E3, (1 + ‖p‖) ^ 4 * ‖specDens σ g p‖ ≤ C := by
  obtain ⟨A, hA⟩ := hσg
  obtain ⟨CK, hCK0, hCK⟩ := SqrtKin.kinFT_decay_gen hg hgc 6
  have hA0 : 0 ≤ A := by simpa using le_trans (abs_nonneg (σ 0)) (hA 0)
  refine ⟨A * CK ^ 2, fun p => ?_⟩
  have hp : (1 : ℝ) ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
  have hp0 : (1 + ‖p‖ : ℝ) ≠ 0 := by positivity
  have h1 : ‖specDens σ g p‖ = |σ p| * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
    rw [specDens_apply', norm_coe_real, abs_mul]
    have hy : |‖Submission.BoseGases.kinFT g p‖ ^ 2| = ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    rw [hy]
  have h2 : ‖Submission.BoseGases.kinFT g p‖ ^ 2 ≤ (CK / (1 + ‖p‖) ^ 6) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hCK p) 2
  have h3 : (0 : ℝ) ≤ A * (1 + ‖p‖) ^ 2 := mul_nonneg hA0 (by positivity)
  calc (1 + ‖p‖) ^ 4 * ‖specDens σ g p‖
      = (1 + ‖p‖) ^ 4 * (|σ p| * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by rw [h1]
    _ ≤ (1 + ‖p‖) ^ 4 * ((A * (1 + ‖p‖) ^ 2) * (CK / (1 + ‖p‖) ^ 6) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hA p) h2 (by positivity) h3) (by positivity)
    _ = A * CK ^ 2 * ((1 + ‖p‖) ^ 6)⁻¹ := by field_simp [hp0]; try ring
    _ ≤ A * CK ^ 2 := by
        have h6 : (1 : ℝ) ≤ (1 + ‖p‖) ^ 6 := one_le_pow₀ hp
        have h7 : ((1 + ‖p‖) ^ 6)⁻¹ ≤ 1 := by
          have h8 := (inv_le_inv₀ (show (0:ℝ) < (1 + ‖p‖) ^ 6 by positivity)
            (show (0:ℝ) < (1:ℝ) by norm_num)).mpr h6
          rwa [inv_one] at h8
        calc A * CK ^ 2 * ((1 + ‖p‖) ^ 6)⁻¹ ≤ A * CK ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left h7 (mul_nonneg hA0 (sq_nonneg CK))
          _ = A * CK ^ 2 := mul_one _

/-- **Summability of the symbol on the momentum lattice** `(2π/ℓ)ℤ³`.  The sampled symbol
decreases like `(1+‖m‖)⁻⁴`, which is summable in three dimensions. -/
lemma specDens_summable_lattice {ℓ : ℝ} (hℓ : 0 < ℓ) {σ : E3 → ℝ}
    (hσg : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    Summable (fun n : Fin 3 → ℤ => specDens σ g (Work.BoseBoxFock.kmomInt ℓ n)) := by
  obtain ⟨C, hC⟩ := specDens_decay hσg hg hgc
  have ha : 0 < 2 * Real.pi / ℓ := div_pos (by positivity) hℓ
  refine Summable.of_norm_bounded
    ((summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl).mul_left
      ((max 1 (2 * Real.pi / ℓ)⁻¹) ^ 4 * C)) (fun n => ?_)
  have h1 := LatSym.decay_comp_smul (f := specDens σ g) ha hC (Work.BoseBoxFock.latVec n)
  rw [LatSym.smul_latVec_eq_kmomInt] at h1
  have hy : (0 : ℝ) < (1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4 := by positivity
  calc ‖specDens σ g (Work.BoseBoxFock.kmomInt ℓ n)‖
      = ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4)⁻¹ *
          ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4 *
            ‖specDens σ g (Work.BoseBoxFock.kmomInt ℓ n)‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hy), one_mul]
    _ ≤ ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4)⁻¹ *
          ((max 1 (2 * Real.pi / ℓ)⁻¹) ^ 4 * C) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (max 1 (2 * Real.pi / ℓ)⁻¹) ^ 4 * C *
          ((1 + ‖Work.BoseBoxFock.latVec n‖) ^ 4)⁻¹ := by ring

/-- `latVec 0 = 0`. -/
lemma latVec_zero_eq : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [Work.BoseBoxFock.latVec]

/-- The real part of the integral of the symbol is the continuum integral of
`p ↦ σ p ‖kinFT g p‖²`. -/
lemma specDens_integral_re {σ : E3 → ℝ} {g : E3 → ℂ}
    (hint : MeasureTheory.Integrable (specDens σ g)) :
    (∫ p : E3, specDens σ g p).re
      = ∫ p : E3, σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
  rw [show (∫ p : E3, specDens σ g p).re
      = Complex.reCLM (∫ p : E3, specDens σ g p) from rfl]
  rw [← Complex.reCLM.integral_comp_comm hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show Complex.reCLM (specDens σ g p) = σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2
  rw [Complex.reCLM_apply, specDens_apply', Complex.ofReal_re]


/-- **The real part of a Fourier sample of the symbol**, in position space. -/
lemma specDens_sample_re {ℓ : ℝ} (hℓ : 0 < ℓ) {σ : E3 → ℝ} (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hσg : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (m : Fin 3 → ℤ) :
    (∫ p : E3, specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))).re
      = ((2 * Real.pi) ^ 3) *
        (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re := by
  obtain ⟨A, hA⟩ := hσg
  have hσg' : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2 := ⟨A, hA⟩
  have hint : MeasureTheory.Integrable (specDens σ g) := specDens_integrable hσ hσg' hg hgc
  have hPh : Continuous (fun p : E3 => Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))) :=
    Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_id)))))
  have hPh' : Continuous (fun p : E3 => Complex.exp (Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_id))))
  have hint1 : MeasureTheory.Integrable (fun p : E3 =>
      specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))) := by
    refine hint.mul_bdd (c := 1) hPh.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Complex.norm_exp]
    have : (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ))).re = 0 := by simp
    rw [this, Real.exp_zero]
  have hint2 : MeasureTheory.Integrable (fun p : E3 =>
      specDens σ g p * Complex.exp (Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ))) := by
    refine hint.mul_bdd (c := 1) hPh'.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Complex.norm_exp]
    have : (Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  -- the common value of both sides
  have hreal1 : (∫ p : E3,
        specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))).re
      = ∫ p : E3, σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.cos (inner ℝ (ℓ • latVec m) p) := by
    rw [show (∫ p : E3,
          specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))).re
        = Complex.reCLM (∫ p : E3,
          specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))) from rfl]
    rw [← Complex.reCLM.integral_comp_comm hint1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show (specDens σ g p * Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))).re = _
    rw [specDens_apply', re_ofReal_mul_exp_neg_I]
  have hreal2 : ((2 * Real.pi) ^ 3) *
        (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re
      = ∫ p : E3, σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.cos (inner ℝ (ℓ • latVec m) p) := by
    have hS4 := LatSym.integral_conj_mul_symOp hg hgc hσ hσg' (ℓ • latVec m)
    rw [hS4, ← specDens_exp_eq_pos]
    rw [show ((((2 * Real.pi) ^ 3 : ℝ)) : ℂ)⁻¹ = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) from by
      push_cast; ring]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ← mul_assoc]
    have hc : (2 * Real.pi) ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ = 1 := by
      rw [mul_inv_cancel₀]; positivity
    rw [hc, one_mul]
    rw [show (∫ p : E3,
          specDens σ g p * Complex.exp (Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ))).re
        = Complex.reCLM (∫ p : E3,
          specDens σ g p * Complex.exp (Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ))) from rfl]
    rw [← Complex.reCLM.integral_comp_comm hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show (specDens σ g p * Complex.exp (Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ))).re = _
    rw [specDens_apply', re_ofReal_mul_exp_I]
  rw [hreal1, hreal2]

theorem lattice_symbol_eq_alias {ℓ : ℝ} (hℓ : 0 < ℓ) {σ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (hσg : ∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    (hσ6 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖iteratedFDeriv ℝ 6 σ p‖))
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomInt ℓ n) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        + ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (g x) *
              Work.BoseBoxFock.symOp σ g (x + ℓ • Work.BoseBoxFock.latVec m)).re) := by
  classical
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset hgs
  obtain ⟨A, hA⟩ := hσg
  have hσg' : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2 := ⟨A, hA⟩
  have hint : MeasureTheory.Integrable (specDens σ g) := specDens_integrable hσ hσg' hg hgc
  have hcont : Continuous (specDens σ g) := specDens_continuous hσ hg hgc
  have hdec : ∃ C : ℝ, ∀ p : E3, (1 + ‖p‖) ^ 4 * ‖specDens σ g p‖ ≤ C :=
    specDens_decay hσg' hg hgc
  have hsum : Summable (fun m : Fin 3 → ℤ => ∫ p : E3, specDens σ g p *
      Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))) :=
    specDens_summable hℓ hσ hσg' hσ6 hg hgs
  have hsumN : Summable (fun n : Fin 3 → ℤ => specDens σ g (kmomInt ℓ n)) :=
    specDens_summable_lattice hℓ hσg' hg hgc
  -- Poisson summation for the symbol
  have hpois := LatSym.poisson_scaled_general hℓ hcont hdec hsum
  -- the real part of the left-hand side of the Poisson identity
  have hLre : (∑' n : Fin 3 → ℤ, specDens σ g (kmomInt ℓ n)).re
      = ∑' n : Fin 3 → ℤ,
          σ (kmomInt ℓ n) * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
    rw [Complex.re_tsum hsumN]
    exact tsum_congr (fun n => by rw [specDens_apply', Complex.ofReal_re])
  -- the real part of the right-hand side of the Poisson identity
  have hSre : (∑' m : Fin 3 → ℤ, ∫ p : E3, specDens σ g p *
        Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))).re
      = (2 * Real.pi) ^ 3 * ∑' m : Fin 3 → ℤ,
          (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re := by
    rw [Complex.re_tsum hsum]
    rw [show (∑' m : Fin 3 → ℤ, (∫ p : E3, specDens σ g p *
          Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))).re)
        = ∑' m : Fin 3 → ℤ, (2 * Real.pi) ^ 3 *
            (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re from
      tsum_congr (fun m => specDens_sample_re hℓ hσ hσg' hg hgc m)]
    rw [tsum_mul_left]
  -- the real part of the Poisson identity
  have hpois' : (∑' n : Fin 3 → ℤ, specDens σ g (kmomInt ℓ n)).re
      = ((ℓ / (2 * Real.pi)) ^ 3) * (∑' m : Fin 3 → ℤ, ∫ p : E3, specDens σ g p *
          Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))).re := by
    have h := congrArg Complex.re hpois
    have hcast : ((↑ℓ / (2 * ↑Real.pi)) ^ 3 : ℂ) = (((ℓ / (2 * Real.pi)) ^ 3 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at h
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
    exact h
  -- summability of the position-space samples
  have hsumA : Summable (fun m : Fin 3 → ℤ =>
      (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re) := by
    have h1 : Summable (fun m : Fin 3 → ℤ =>
        (∫ p : E3, specDens σ g p *
          Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec m) p : ℂ)))).re) :=
      Summable.of_norm_bounded hsum.norm (fun m => by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _)
    have h2 : Summable (fun m : Fin 3 → ℤ => (2 * Real.pi) ^ 3 *
        (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re) :=
      h1.congr (fun m => specDens_sample_re hℓ hσ hσg' hg hgc m)
    refine (h2.mul_left ((2 * Real.pi) ^ 3)⁻¹).congr (fun m => ?_)
    show ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Real.pi) ^ 3 * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0), one_mul]
  -- the `m = 0` term is the continuum integral
  have hA0 : (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec 0)).re
      = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : E3, σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    have h1 := specDens_sample_re hℓ hσ hσg' hg hgc 0
    have h2 : (∫ p : E3, specDens σ g p *
          Complex.exp (-(Complex.I * (inner ℝ (ℓ • latVec (0 : Fin 3 → ℤ)) p : ℂ))))
        = ∫ p : E3, specDens σ g p := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      show specDens σ g p *
          Complex.exp (-(Complex.I * (inner ℝ (ℓ • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ)) p : ℂ)))
        = specDens σ g p
      have hz : (inner ℝ (ℓ • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ)) p : ℂ) = 0 := by
        rw [latVec_zero_eq, smul_zero, inner_zero_left]
        norm_num
      rw [hz, mul_zero, neg_zero, Complex.exp_zero, mul_one]
    rw [h2, specDens_integral_re hint] at h1
    rw [h1, ← mul_assoc,
      inv_mul_cancel₀ (by positivity : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0), one_mul]
  -- the chain: Poisson, then the identification of every sample with a position-space pairing
  have hchain : (ℓ ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ,
        σ (kmomInt ℓ n) * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      = ∑' m : Fin 3 → ℤ,
          (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re := by
    rw [← hLre, hpois', hSre]
    have hcoe : (ℓ ^ 3)⁻¹ * ((ℓ / (2 * Real.pi)) ^ 3) * ((2 * Real.pi) ^ 3) = 1 := by
      field_simp
      try ring
    rw [← mul_assoc, ← mul_assoc, hcoe, one_mul]
  calc (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (Work.BoseBoxFock.kmomInt ℓ n) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = (ℓ ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ,
          σ (Work.BoseBoxFock.kmomInt ℓ n) *
            ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun n => by ring)
    _ = ∑' m : Fin 3 → ℤ,
          (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re := hchain
    _ = (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec 0)).re
          + ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
              (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re) :=
        hsumA.tsum_eq_add_tsum_ite 0
    _ = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3,
          σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        + ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re) := by
        rw [hA0]

end

end Work.BoseBoxFock
