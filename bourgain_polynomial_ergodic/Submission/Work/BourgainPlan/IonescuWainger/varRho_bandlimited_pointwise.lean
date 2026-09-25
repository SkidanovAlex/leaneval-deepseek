import Mathlib
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs
import Submission.Work.BourgainPlan.Maximal.varRhoSplitting
import Submission.Work.BourgainPlan.IonescuWainger.exists_pairing_attaining_sqrt_sum_sq

/-!
# The pointwise reproducing inequality for the `2`-variation of a band-limited family

This file proves `varRho_bandlimited_pointwise`: for a family `h : ℕ → ℝ → ℂ` of integrable,
continuous, `[-1/2,1/2]`-band-limited functions and a reproducing kernel `K` of the Nyquist band,

`V²_{n ≥ κ}(h_n(x)) ≤ ∫⁻ y, V²_{n ≥ κ}(h_n(y)) · ‖K (x - y)‖ₑ`   for every `x : ℝ`,

where `V² = varRhoFrom 2 κ` is the `2`-variation seminorm in the index tail `{n : κ ≤ n}`.

This is the pointwise step of the lattice sampling principle for the `2`-variation
(`Work.BourgainPlan.IonescuWainger.exists_lattice_varRhoFrom_le_integral_varRhoFrom`): integrating
the inequality over `x ∈ ℝ` against the counting measure of `ℤ` and summing the lattice weights
`Σ_m ‖K (m - x)‖ ≤ C` produces the sampling inequality.

The proof is the variational version of the classical band-limited reconstruction: fix a chain
`κ ≤ t 0 ≤ … ≤ t J ≤ hi`; the reproducing identity `g x = ∫ y, g y * K (x - y)` holds for every
difference `h (t (j+1)) - h (t j)` (the difference of two band-limited integrable functions is again
band-limited and integrable, and both are continuous).  Choosing, by finite-dimensional `ℓ²` duality
(`exists_pairing_attaining_sqrt_sum_sq`), the vector `c : Fin J → ℂ` with `Σ ‖c j‖² ≤ 1` that attains
the `ℓ²`-norm of the increment vector at `x`, the linear combination `Σ_j c_j (h_{t(j+1)} - h_{t j})`
is written — by `integral_sub` and `integral_finset_sum` — as the single integral
`∫ y, (Σ_j c_j (h_{t(j+1)} y - h_{t j} y)) * K (x - y)`, and `norm_integral_le_integral_norm`
together with Cauchy–Schwarz in `ℂ^J` bounds its norm by `∫ y, (Σ_j ‖…‖²)^{1/2} ‖K (x-y)‖`.  Since
`(Σ_j ‖…‖²)^{1/2}` is exactly `chainLp 2 J` for the same chain, taking the supremum over chains (and
over `hi`) gives the statement.  The passage to `ℝ≥0∞` uses
`integral_eq_lintegral_of_nonneg_ae` and `ENNReal.ofReal_toReal_le`, so no integrability of the
variation itself is needed.
-/

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

/-- **The `ℓ²`-length of a chain over `Fin J`.**  `chainLp 2 J a t = (Σ_{j<J} ‖·‖²)^{1/2}` with the
sum indexed by `Fin J` — the form in which the finite-dimensional `ℓ²` duality
(`exists_pairing_attaining_sqrt_sum_sq`) and Cauchy–Schwarz apply. -/
private lemma chainLp_two_eq_fin {E : Type*} [SeminormedAddCommGroup E] (J : ℕ) (a : ℕ → E)
    (t : ℕ → ℕ) :
    Work.BourgainPlan.Maximal.chainLp 2 J a t
      = (∑ i : Fin J, ‖a (t ((i : ℕ) + 1)) - a (t (i : ℕ))‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  rw [Work.BourgainPlan.Maximal.chainLp]
  rw [Fin.sum_univ_eq_sum_range (fun j => ‖a (t (j + 1)) - a (t j)‖ ^ 2) J]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by norm_num [Real.rpow_natCast])

/-- **The reproducing formula for a difference.**  If both `g₁` and `g₂` are reproduced by the kernel
`K` at the point `x` (in particular, for band-limited integrable functions at a continuity point),
then so is their difference: the two convolution integrals are integrable because `K` is bounded. -/
private lemma sub_reproducing (K : ℝ → ℂ) (C0 : ℝ) (hC0 : 0 < C0)
    (hKint : Integrable K) (hKdec : ∀ u : ℝ, ‖K u‖ ≤ C0 / (1 + u ^ 2))
    {g₁ g₂ : ℝ → ℂ} (hint₁ : Integrable g₁) (hint₂ : Integrable g₂)
    (hrep₁ : ∀ x : ℝ, ContinuousAt g₁ x → g₁ x = ∫ y : ℝ, g₁ y * K (x - y))
    (hrep₂ : ∀ x : ℝ, ContinuousAt g₂ x → g₂ x = ∫ y : ℝ, g₂ y * K (x - y))
    {x : ℝ} (hc₁ : ContinuousAt g₁ x) (hc₂ : ContinuousAt g₂ x) :
    g₁ x - g₂ x = ∫ y : ℝ, (g₁ y - g₂ y) * K (x - y) := by
  have hKbdd : ∀ y : ℝ, ‖K (x - y)‖ ≤ C0 := by
    intro y
    refine le_trans (hKdec (x - y)) ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - y), hC0.le]
  have hmeasK : AEStronglyMeasurable (fun y : ℝ => K (x - y)) volume := by
    have h1 : AEMeasurable K (Measure.map (fun y : ℝ => x - y) volume) := by
      rw [Measure.map_sub_left_eq_self]
      exact hKint.aemeasurable
    exact (h1.comp_measurable (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hI₁ : Integrable (fun y : ℝ => g₁ y * K (x - y)) :=
    hint₁.mul_bdd hmeasK (Filter.Eventually.of_forall hKbdd)
  have hI₂ : Integrable (fun y : ℝ => g₂ y * K (x - y)) :=
    hint₂.mul_bdd hmeasK (Filter.Eventually.of_forall hKbdd)
  rw [hrep₁ x hc₁, hrep₂ x hc₂, ← integral_sub hI₁ hI₂]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

/-- **The reproducing formula for a finite linear combination.**  If each `g i` is reproduced by `K`
at `x`, then so is `Σ_i c_i · g_i`, by linearity of the integral (each convolution integral being
integrable because `K` is bounded). -/
private lemma sum_mul_reproducing (K : ℝ → ℂ) (C0 : ℝ) (hC0 : 0 < C0)
    (hKint : Integrable K) (hKdec : ∀ u : ℝ, ‖K u‖ ≤ C0 / (1 + u ^ 2))
    {ι : Type*} [Fintype ι] (g : ι → ℝ → ℂ) (c : ι → ℂ) (x : ℝ)
    (hgint : ∀ i, Integrable (g i))
    (hrep : ∀ i, g i x = ∫ y : ℝ, g i y * K (x - y)) :
    ∑ i, c i * g i x = ∫ y : ℝ, (∑ i, c i * g i y) * K (x - y) := by
  have hKbdd : ∀ y : ℝ, ‖K (x - y)‖ ≤ C0 := by
    intro y
    refine le_trans (hKdec (x - y)) ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - y), hC0.le]
  have hmeasK : AEStronglyMeasurable (fun y : ℝ => K (x - y)) volume := by
    have h1 : AEMeasurable K (Measure.map (fun y : ℝ => x - y) volume) := by
      rw [Measure.map_sub_left_eq_self]
      exact hKint.aemeasurable
    exact (h1.comp_measurable (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hI : ∀ i, Integrable (fun y : ℝ => g i y * K (x - y)) := fun i =>
    (hgint i).mul_bdd hmeasK (Filter.Eventually.of_forall hKbdd)
  have hper : ∀ i, c i * g i x = ∫ y : ℝ, c i * (g i y * K (x - y)) := by
    intro i
    rw [hrep i, integral_const_mul]
  rw [Finset.sum_congr rfl (fun i _ => hper i)]
  rw [← integral_finsetSum Finset.univ
    (fun i (_ : i ∈ Finset.univ) => (hI i).const_mul (c i))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (∑ i, c i * (g i y * K (x - y))) = (∑ i, c i * g i y) * K (x - y)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

-- Route (the reproducing kernel `K` of the Nyquist band, `band_limited_reproducing_kernel`): it
-- suffices to bound `ENNReal.ofReal (chainLp 2 J (fun n => h n x) t)` for every admissible chain
-- `(J, t)` (monotone `t` with `κ ≤ t j ≤ hi`); pick the extremal `c : Fin J → ℂ` with
-- `∑ ‖c j‖ ^ 2 ≤ 1` and `‖∑ j, c j * (h (t (j+1)) x - h (t j) x)‖ = (∑ j, ‖h (t (j+1)) x - h (t j) x‖ ^ 2) ^ (1/2)`
-- (finite-dimensional `ℓ²` duality); apply the reproducing identity to each `h (t m)` and
-- `MeasureTheory.integral_sub` + `MeasureTheory.integral_finset_sum` to write the combination as
-- `∫ y, (∑ j, c j * (h (t (j+1)) y - h (t j) y)) * K (x - y)`; then
-- `enorm_integral_le_lintegral_enorm` and Cauchy–Schwarz in `ℂ^J`.
theorem varRho_bandlimited_pointwise (K : ℝ → ℂ) (C0 : ℝ) (hC0 : 0 < C0)
    (hKint : MeasureTheory.Integrable K)
    (hKdec : ∀ u : ℝ, ‖K u‖ ≤ C0 / (1 + u ^ 2))
    (hrep : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
      ∀ x : ℝ, ContinuousAt g x → g x = ∫ y : ℝ, g y * K (x - y))
    (h : ℕ → ℝ → ℂ) (hint : ∀ n, MeasureTheory.Integrable (h n))
    (hcont : ∀ n, Continuous (h n))
    (hbl : ∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) →
      FourierTransform.fourier (h n) ξ = 0)
    (κ : ℕ) (x : ℝ) :
    Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => h n x)
      ≤ ∫⁻ y : ℝ, Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => h n y) * ‖K (x - y)‖ₑ := by
  -- the reproducing identity for every member of the family
  have hrepn : ∀ (n : ℕ) (x' : ℝ), ContinuousAt (h n) x' →
      h n x' = ∫ y : ℝ, h n y * K (x' - y) :=
    fun n x' _ => hrep (h n) (hint n) (hbl n) x' (hcont n).continuousAt
  -- the kernel is bounded (at the fixed point `x`, uniformly in the integration variable)
  have hKbdd : ∀ y : ℝ, ‖K (x - y)‖ ≤ C0 := by
    intro y
    refine le_trans (hKdec (x - y)) ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - y), hC0.le]
  have hmeasK : AEStronglyMeasurable (fun y : ℝ => K (x - y)) volume := by
    have h1 : AEMeasurable K (Measure.map (fun y : ℝ => x - y) volume) := by
      rw [Measure.map_sub_left_eq_self]
      exact hKint.aemeasurable
    exact (h1.comp_measurable (measurable_const.sub measurable_id)).aestronglyMeasurable
  -- reduce to a single admissible chain, and then to the `Fin J`-indexed `ℓ²`-length
  rw [Work.BourgainPlan.Maximal.varRhoFrom]
  refine iSup_le fun hi => ?_
  refine Work.BourgainPlan.Maximal.varRho_le_of_forall fun J t ht hw => ?_
  -- the increments of the chain, as a function of the point
  let d : ℝ → Fin J → ℂ := fun y i => h (t ((i : ℕ) + 1)) y - h (t (i : ℕ)) y
  -- finite-dimensional `ℓ²` duality: the extremal dual vector at `x`
  obtain ⟨_, c, hcmass, hceq⟩ := exists_pairing_attaining_sqrt_sum_sq (d x)
  have hdint : ∀ i : Fin J, Integrable (fun y : ℝ => d y i) := fun i =>
    (hint (t ((i : ℕ) + 1))).sub (hint (t (i : ℕ)))
  -- the reproducing identity, increment by increment
  have hrepd : ∀ i : Fin J, d x i = ∫ y : ℝ, d y i * K (x - y) := by
    intro i
    exact sub_reproducing K C0 hC0 hKint hKdec
      (hint (t ((i : ℕ) + 1))) (hint (t (i : ℕ)))
      (hrepn (t ((i : ℕ) + 1))) (hrepn (t (i : ℕ)))
      (hcont (t ((i : ℕ) + 1))).continuousAt (hcont (t (i : ℕ))).continuousAt
  -- and for the linear combination
  have hcomb : ∑ i : Fin J, c i * d x i
      = ∫ y : ℝ, (∑ i : Fin J, c i * d y i) * K (x - y) :=
    sum_mul_reproducing K C0 hC0 hKint hKdec (fun i y => d y i) c x hdint hrepd
  -- Cauchy–Schwarz in `ℂ^J`, at every point
  have hcs_y : ∀ y : ℝ, ‖∑ i : Fin J, c i * d y i‖
      ≤ (∑ i : Fin J, ‖d y i‖ ^ 2) ^ ((1 : ℝ) / 2) :=
    fun y => (exists_pairing_attaining_sqrt_sum_sq (d y)).1 c hcmass
  -- `(Σ ‖·‖²)^{1/2}` is the `ℓ²`-length of the chain
  have hchain : ∀ y : ℝ, Work.BourgainPlan.Maximal.chainLp 2 J (fun n => h n y) t
      = (∑ i : Fin J, ‖d y i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro y
    rw [chainLp_two_eq_fin J (fun n => h n y) t]
  -- the single integral bound
  have hnorm_le : ‖∑ i : Fin J, c i * d x i‖
      ≤ ∫ y : ℝ, ‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖ := by
    rw [hcomb]
    calc ‖∫ y : ℝ, (∑ i : Fin J, c i * d y i) * K (x - y)‖
        ≤ ∫ y : ℝ, ‖(∑ i : Fin J, c i * d y i) * K (x - y)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ y : ℝ, ‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖ := by simp_rw [norm_mul]
  have hGcont : Continuous fun y : ℝ => ∑ i : Fin J, c i * d y i := by
    refine continuous_finsetSum Finset.univ fun i _ => ?_
    exact continuous_const.mul ((hcont (t ((i : ℕ) + 1))).sub (hcont (t (i : ℕ))))
  have hψmeas : AEStronglyMeasurable
      (fun y : ℝ => ‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖) volume :=
    (hGcont.norm.aestronglyMeasurable).mul hmeasK.norm
  -- passage to `ℝ≥0∞`
  have hstep2 : ENNReal.ofReal (∫ y : ℝ, ‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖)
      ≤ ∫⁻ y : ℝ, ENNReal.ofReal (‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖) := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => by positivity) hψmeas]
    exact ENNReal.ofReal_toReal_le
  have hstep3 : (∫⁻ y : ℝ, ENNReal.ofReal (‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖))
      ≤ ∫⁻ y : ℝ, (⨆ hi' : ℕ, Work.BourgainPlan.Maximal.varRho 2 κ hi' (fun n => h n y))
          * ‖K (x - y)‖ₑ := by
    refine lintegral_mono fun y => ?_
    have hle : ENNReal.ofReal ‖∑ i : Fin J, c i * d y i‖
        ≤ ⨆ hi' : ℕ, Work.BourgainPlan.Maximal.varRho 2 κ hi' (fun n => h n y) := by
      calc ENNReal.ofReal ‖∑ i : Fin J, c i * d y i‖
          ≤ ENNReal.ofReal ((∑ i : Fin J, ‖d y i‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
            ENNReal.ofReal_le_ofReal (hcs_y y)
        _ = ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp 2 J (fun n => h n y) t) := by
            rw [hchain y]
        _ ≤ Work.BourgainPlan.Maximal.varRho 2 κ hi (fun n => h n y) :=
            Work.BourgainPlan.Maximal.ofReal_chainLp_le_varRho 2 κ hi J (fun n => h n y) t ht hw
        _ ≤ ⨆ hi' : ℕ, Work.BourgainPlan.Maximal.varRho 2 κ hi' (fun n => h n y) :=
            le_iSup (fun hi' : ℕ => Work.BourgainPlan.Maximal.varRho 2 κ hi' (fun n => h n y)) hi
    rw [← ofReal_norm]
    calc ENNReal.ofReal (‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖)
        = ENNReal.ofReal ‖∑ i : Fin J, c i * d y i‖ * ENNReal.ofReal ‖K (x - y)‖ :=
          ENNReal.ofReal_mul (norm_nonneg _)
      _ ≤ (⨆ hi' : ℕ, Work.BourgainPlan.Maximal.varRho 2 κ hi' (fun n => h n y))
            * ENNReal.ofReal ‖K (x - y)‖ := mul_le_mul_left hle _
  calc ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp 2 J (fun n => h n x) t)
      = ENNReal.ofReal ‖∑ i : Fin J, c i * d x i‖ := by rw [hchain x, ← hceq]
    _ ≤ ENNReal.ofReal (∫ y : ℝ, ‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖) :=
        ENNReal.ofReal_le_ofReal hnorm_le
    _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal (‖∑ i : Fin J, c i * d y i‖ * ‖K (x - y)‖) := hstep2
    _ ≤ ∫⁻ y : ℝ, (⨆ hi' : ℕ, Work.BourgainPlan.Maximal.varRho 2 κ hi' (fun n => h n y))
          * ‖K (x - y)‖ₑ := hstep3

end

end Work.BourgainPlan.IonescuWainger
