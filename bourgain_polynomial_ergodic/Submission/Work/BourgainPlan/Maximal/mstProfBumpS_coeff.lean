import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mstHat_bound
import Submission.Work.BourgainPlan.Maximal.mstProfBumpS_coeff_identity
import Submission.Work.BourgainPlan.Maximal.mstHat_sampling_bound
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers
import Submission.Commons.Analysis.Fourier.fourier_transform_min_decay

/-!
# The `ℓ¹` summability of the Fourier coefficients of `star (mstProf P N ·) * mstEta d χ η s`

This is the non-diagonal (profile scale independent of bump level) kernel estimate of MST §4.2
eq. (78): for a bump `η` bounded by `M` and supported in `[-1/2,1/2]` whose level-`0`
fundamental-domain lift `circleLift (mstEta d χ η 0)` is `C²`, there is `K > 0` such that for every
profile scale `N ≥ 1` and every level `s` the coefficient sequence
`m ↦ ∫ ξ, (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)` is summable with total
mass `≤ K` (`mstProfBumpS_coeff` below).

The proof is assembled from three inputs, together with two small facts proved inline:

* `mstProfBumpS_coeff_identity` (companion module): the non-diagonal coefficient identity
  `∫ ξ, (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)
     = ∫_0^1 c_s⁻¹ mstHat η ((m + P(N t))/c_s) dt` with `c_s = mstScale d χ s ≥ 1`;
* `mstHat_bound` (companion module): `‖mstHat η t‖ ≤ M` from `‖η‖ ≤ M`;
* `mstHat_sampling_bound` (companion module): the shifted-lattice sampling bound
  `Σ_m c⁻¹‖mstHat η ((m+σ)/c)‖ ≤ K` uniformly in `c ≥ 1` and `σ : ℝ`;
* `continuous_mstHat` (proved below): continuity of `t ↦ mstHat η t`, which makes the integrands
  interval-integrable so that the finite `m`-sum and the `t`-integral may be exchanged;
* `mstHat_decay_inline` (proved below, as a private copy of `Work.BourgainPlan.Maximal.mstHat_decay`,
  which cannot be imported here because its module and `mstKernel_helpers` both declare the name
  `mstEta_zero_eq`): the quadratic decay `‖mstHat η t‖ ≤ E t⁻²` for `t ≠ 0` from the `C²`-ness of
  the fundamental-domain lift.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal BigOperators

set_option autoImplicit false

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

/-- **Continuity of the bump transform `mstHat η`.**

`mstHat η t = ∫_{−1/2}^{1/2} η u · e^{−2πi t u} du` is continuous in `t`, provided `η` vanishes off
`[−1/2, 1/2]` and the fundamental-domain lift `G := circleLift (mstEta d χ η 0)` of the level-`0`
bump is continuous.

Nothing is assumed about `η` outside `[−1/2, 1/2]`, and no measurability or boundedness is needed:
on the interval over which `mstHat` integrates, `η` agrees with the continuous function `G (−·)`
except possibly at the single point `u = 1/2`, since `G x = η (−x)` for `|x| < 1/2`
(`Work.BourgainPlan.Maximal.circleLift_mstEta_zero_eq`) while for `|u| > 1/2` both `η u` and
`G (−u)` vanish (`hη2` and the definition of `circleLift`).  Hence `mstHat η t` equals
`∫ u in (−1/2)..(1/2), G (−u) · e^{−2πi t u} du` for every `t`
(`intervalIntegral.integral_congr_ae`), and the latter is continuous in `t`
(`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`). -/
theorem continuous_mstHat {d : ℕ} {χ : ℝ} {η : ℝ → ℂ}
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcont : Continuous (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0))) :
    Continuous (fun t : ℝ => mstHat η t) := by
  have hpt : ∀ t : ℝ, mstHat η t = ∫ u in (-(1 / 2) : ℝ)..(1 / 2),
      Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) *
        Complex.exp ((((-(2 * Real.pi * t * u)) : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [mstHat_apply]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (1 / 2 : ℝ) from by
      rw [MeasureTheory.ae_iff]
      have : {u : ℝ | ¬u ≠ (1 / 2 : ℝ)} = {1 / 2} := by ext u; simp
      rw [this]
      exact measure_singleton _] with u hu huIoc
    have huIoc' : u ∈ Set.Ioc (-(1 / 2) : ℝ) (1 / 2) := by
      rw [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at huIoc
      exact huIoc
    have huIoo : u ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2) :=
      ⟨huIoc'.1, lt_of_le_of_ne huIoc'.2 hu⟩
    have hneg : (-u) ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2) := by
      rw [Set.mem_Ioo] at huIoo ⊢
      exact ⟨by linarith [huIoo.2], by linarith [huIoo.1]⟩
    rw [circleLift_mstEta_zero_coe d χ η hneg, neg_neg]
  rw [funext hpt]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t u => Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) *
      Complex.exp ((((-(2 * Real.pi * t * u)) : ℝ) : ℂ) * Complex.I))
    (by fun_prop) (-(1 / 2)) (1 / 2)

/-- **Quadratic decay of the bump transform `mstHat`** (inlined copy of the companion module
`Submission.Work.BourgainPlan.Maximal.mstHat_decay`: it cannot be imported here, since its module and
`mstKernel_helpers` — which the companion coefficient-identity module needs — declare the same name
`mstEta_zero_eq`).

`mstHat η t = ∫_{−1/2}^{1/2} η u e^{−2πi t u} du` decays like `t⁻²` whenever the fundamental-domain
lift `ϑ := circleLift (mstEta d χ η 0)` is `C²`: `m := ϑ ∘ Neg.neg` is then `C²` with compact
support and agrees with `η` on the fundamental interval, so `mstHat η t = 𝓕 m t`, and two
integrations by parts on the `C²` compactly supported `m` give `‖𝓕 m t‖ ≤ (∫‖m''‖)/(2π t)²`
(`Commons.Analysis.Fourier.fourier_transform_min_decay`). -/
private theorem mstHat_decay_inline {d : ℕ} {χ : ℝ} {η : ℝ → ℂ}
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0))) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, t ≠ 0 → ‖mstHat η t‖ ≤ E / t ^ 2 := by
  have hΦeval : ∀ u ∈ Set.Ioo (-(1/2) : ℝ) (1/2),
      Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) u = η (-u) :=
    fun u hu => circleLift_mstEta_zero_coe d χ η hu
  set m : ℝ → ℂ := fun u => Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) with hm
  have hm_apply : ∀ u : ℝ, m u = Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) (-u) :=
    fun u => by rw [hm]
  have hcdm : ContDiff ℝ 2 m := by
    rw [hm]
    simpa only [Function.comp_def] using hcd0.comp contDiff_neg
  have hmIoo : ∀ u ∈ Set.Ioo (-(1/2) : ℝ) (1/2), m u = η u := by
    intro u hu
    rw [hm_apply, hΦeval (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩, neg_neg]
  have hmzero : ∀ u : ℝ, u ∉ Set.Icc (-(1/2) : ℝ) (1/2) → m u = 0 := by
    intro u hu
    rw [hm_apply]
    refine Work.BourgainPlan.Thm52.circleLift_of_notMem ?_
    intro hmem
    rw [Set.mem_Ioc] at hmem
    rw [Set.mem_Icc] at hu
    exact hu ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hcs : HasCompactSupport m := HasCompactSupport.intro isCompact_Icc hmzero
  have hint0 : Integrable m := hcdm.continuous.integrable_of_hasCompactSupport hcs
  have hcont2 : Continuous (deriv (deriv m)) := by
    have h := hcdm.continuous_iteratedDeriv 2 le_rfl
    have hid : iteratedDeriv 2 m = deriv (deriv m) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rwa [hid] at h
  have hint2 : Integrable (deriv (deriv m)) :=
    hcont2.integrable_of_hasCompactSupport hcs.deriv.deriv
  have hdiff1 : Differentiable ℝ m := hcdm.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (deriv m) := by
    have h := hcdm.differentiable_iteratedDeriv' 1
    rwa [iteratedDeriv_one] at h
  have hFourier_eq : ∀ t : ℝ, FourierTransform.fourier m t =
      ∫ x in Set.Ioo (-(1/2) : ℝ) (1/2),
        Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • m x := by
    intro t
    rw [Real.fourier_eq' m t]
    have h1 : ∀ x ∉ Set.Icc (-(1/2) : ℝ) (1/2),
        Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • m x = 0 :=
      fun x hx => by rw [hmzero x hx, smul_zero]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h1,
      MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hmstHat_eq : ∀ t : ℝ, mstHat η t =
      ∫ x in Set.Ioo (-(1/2) : ℝ) (1/2),
        η x * Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [mstHat_apply, intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hpt : ∀ t : ℝ, Set.EqOn
      (fun x : ℝ => η x * Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I))
      (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • m x)
      (Set.Ioo (-(1/2) : ℝ) (1/2)) := by
    intro t x hx
    dsimp only
    rw [hmIoo x hx]
    have hexp : Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) := by
      congr 1
      simp only [Real.inner_apply]
      push_cast
      ring
    rw [hexp, smul_eq_mul]
    ring
  have hmstHat : ∀ t : ℝ, mstHat η t = FourierTransform.fourier m t := by
    intro t
    rw [hmstHat_eq t, hFourier_eq t,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (hpt t)]
  set B : ℝ := ∫ x, ‖deriv (deriv m) x‖ with hB
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun x => norm_nonneg _)
  have hA0 : 0 ≤ ∫ x, ‖m x‖ := integral_nonneg (fun x => norm_nonneg _)
  refine ⟨B / (2 * Real.pi) ^ 2, by positivity, fun t ht => ?_⟩
  rw [hmstHat t]
  have hdec := Commons.Analysis.Fourier.fourier_transform_min_decay m (∫ x, ‖m x‖) B hA0 hB0
    hint0 hint2 hdiff1 hdiff2 le_rfl le_rfl t ht
  have h1 : ‖FourierTransform.fourier m t‖ ≤ B / (2 * Real.pi * |t|) ^ 2 :=
    hdec.trans (min_le_right _ _)
  have h2 : B / (2 * Real.pi * |t|) ^ 2 = (B / (2 * Real.pi) ^ 2) / t ^ 2 := by
    rw [mul_pow, sq_abs, ← div_div]
  rwa [h2] at h1

/-- **The `ℓ¹` summability of the Fourier coefficients of `star (mstProf P N ·) * mstEta d χ η s`,
uniformly in the profile scale `N` and in the bump level `s`.**

For a bump `η` bounded by `M` and supported in `[-1/2,1/2]`, with the level-`0` fundamental-domain
lift `circleLift (mstEta d χ η 0)` of class `C²`, there is `K > 0` such that for every `N ≥ 1` and
every `s : ℕ` the sequence `m ↦ ∫ ξ, (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)`
is summable with total mass at most `K`.

This is the *non-diagonal* (profile scale independent of bump level) form of the kernel estimate of
MST §4.2 eq. (78); the diagonal case is
`Work.BourgainPlan.Maximal.mst_err1_prof_coeff` (a sibling agent is proving it concurrently in
`Submission/Work/BourgainPlan/Maximal/mst_err1_prof_coeff.lean` — you may consult it, but do not
import it unless it is `sorry`-free).

Route (MST §4.2, the `ℓ¹` kernel of the model symbol):

1. `star (mstProf P N ξ) = ∫_0^1 exp (-(2πi · iwRep ξ · P(N s'))) ds'` (definition of `polyProfile`
   as the integral `∫_0^1 e(θ P(N s')) ds'` plus conjugation, `star_polyProfile`).
2. On the fundamental domain the coefficient integral becomes the interval integral
   `∫ x in (-1/2)..(1/2), (∫_0^1 exp (-(2πi x P(N s'))) ds') * η (c_s x) * exp (-(2πi m x)) dx`
   with `c_s = mstScale d χ s = 2^(s(d-χ)) ≥ 1` (`one_le_mstScale`, from `hχ : χ + 1 ≤ d`), and
   Fubini on the rectangle `(-1/2,1/2) × (0,1)` together with the scaling identity
   `∫ x in (-1/2)..(1/2), η (c*x) * exp (-(2πi t x)) = (1/c) * mstHat η (t/c)` gives the
   coefficient identity `mstProfBumpS_coeff_identity`.
3. Sum over `m` with `Σ_m ∫_0^1 = ∫_0^1 Σ_m` (finiteness plus continuity of `mstHat η`, which
   makes the integrands interval-integrable) and apply the sampling bound
   `mstHat_sampling_bound`: `Σ_m (1/c) * ‖mstHat η ((m + σ)/c)‖ ≤ K` uniformly in `c ≥ 1` and in
   the shift `σ : ℝ`, where `‖mstHat η‖ ≤ M` (`mstHat_bound`) and `‖mstHat η t‖ ≤ E/t²`
   (`mstHat_decay`). -/
theorem mstProfBumpS_coeff (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hχ : χ + 1 ≤ (d : ℝ)) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0))) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N s : ℕ), 1 ≤ N →
      Summable (fun m : ℤ => ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖) ≤ K := by
  have hcont : Continuous (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0)) :=
    hcd0.continuous
  obtain ⟨E, hE0, hEdec⟩ := mstHat_decay_inline hcd0
  have hbnd : ∀ t : ℝ, ‖mstHat η t‖ ≤ M := mstHat_bound hM hηbd
  obtain ⟨K, hKpos, hK⟩ := mstHat_sampling_bound hM hE0 hbnd hEdec
  have hmh : Continuous fun t : ℝ => mstHat η t := continuous_mstHat hη2 hcont
  refine ⟨K, hKpos, ?_⟩
  intro N s _
  have hc1 : 1 ≤ mstScale d χ s := one_le_mstScale hχ s
  have hcpos : 0 < mstScale d χ s := mstScale_pos d χ s
  have hcine : ‖((mstScale d χ s : ℝ) : ℂ)⁻¹‖ = (mstScale d χ s)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
  set Q : ℝ → ℝ := fun t => (toRealPoly P).eval ((N : ℝ) * t) with hQ
  have hQcont : Continuous Q := by
    rw [hQ]
    exact (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)
  -- the coefficient identity, in the notation of this proof
  have hid : ∀ m : ℤ,
      (∫ ξ : Circ, (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ) ∂haarT)
        = ∫ t in (0 : ℝ)..1, ((mstScale d χ s : ℝ) : ℂ)⁻¹ *
            mstHat η (((m : ℝ) + Q t) / mstScale d χ s) := by
    intro m
    rw [mstProfBumpS_coeff_identity P hM hχ hηbd hη2 hcont N s m]
  -- the real-valued summand and its continuity
  have hgcont : ∀ m : ℤ, Continuous
      (fun t : ℝ => (mstScale d χ s)⁻¹ * ‖mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖) := by
    intro m
    refine Continuous.mul continuous_const ((hmh.comp ?_).norm)
    exact (continuous_const.add hQcont).div_const _
  -- the finite-sum bound
  have hfin : ∀ F : Finset ℤ,
      ∑ m ∈ F, ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ) ∂haarT‖ ≤ K := by
    intro F
    have hstep : ∀ m : ℤ,
        ‖∫ ξ : Circ, (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ) ∂haarT‖
          ≤ ∫ t in (0 : ℝ)..1,
              (mstScale d χ s)⁻¹ * ‖mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖ := by
      intro m
      rw [hid m]
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun t : ℝ => ((mstScale d χ s : ℝ) : ℂ)⁻¹ *
          mstHat η (((m : ℝ) + Q t) / mstScale d χ s)) (by norm_num)) ?_
      apply le_of_eq
      apply intervalIntegral.integral_congr
      intro t _
      change ‖(((mstScale d χ s : ℝ)) : ℂ)⁻¹ * mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖
        = (mstScale d χ s)⁻¹ * ‖mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖
      rw [norm_mul, hcine]
    calc ∑ m ∈ F, ‖∫ ξ : Circ,
            (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ) ∂haarT‖
        ≤ ∑ m ∈ F, ∫ t in (0 : ℝ)..1,
            (mstScale d χ s)⁻¹ * ‖mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖ :=
          Finset.sum_le_sum (fun m _ => hstep m)
      _ = ∫ t in (0 : ℝ)..1, ∑ m ∈ F,
            (mstScale d χ s)⁻¹ * ‖mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖ :=
          (intervalIntegral.integral_finset_sum (μ := volume) (a := (0 : ℝ)) (b := 1) (s := F)
            (f := fun m t => (mstScale d χ s)⁻¹ *
              ‖mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖)
            (fun m _ => (hgcont m).intervalIntegrable 0 1)).symm
      _ ≤ ∫ t in (0 : ℝ)..1, K := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
          · exact (continuous_finsetSum F (fun m _ => hgcont m)).intervalIntegrable 0 1
          · exact continuous_const.intervalIntegrable 0 1
          · intro t _
            have hs := hK (mstScale d χ s) (Q t) hc1
            calc ∑ m ∈ F, (mstScale d χ s)⁻¹ *
                    ‖mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖
                ≤ ∑' m : ℤ, (mstScale d χ s)⁻¹ *
                    ‖mstHat η (((m : ℝ) + Q t) / mstScale d χ s)‖ :=
                  Summable.sum_le_tsum F (fun m _ => by positivity) hs.1
              _ ≤ K := hs.2
      _ = K := by simp
  exact ⟨summable_of_sum_le (fun m => norm_nonneg _) hfin,
    Real.tsum_le_of_sum_le (fun m => norm_nonneg _) hfin⟩

end

end Work.BourgainPlan.Maximal
