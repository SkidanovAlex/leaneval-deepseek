import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.plancherel_circle_enorm_sq_Ioc
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le
import Submission.Work.BourgainPlan.Oscillation.Lacunary.dilProfDefs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.profFamM_sub_eq_integral_cutFamM
import Submission.Work.BourgainPlan.Oscillation.Lacunary.oscZ_le_of_integral_oscZ
import Submission.Work.BourgainPlan.Oscillation.Lacunary.norm_le_of_summable_lacScale_dilations
import Submission.Work.BourgainPlan.Oscillation.Lacunary.oscZ_profFam_H2_le
import Submission.Work.BourgainPlan.Oscillation.Lacunary.profFam_add_eq
import Submission.Work.BourgainPlan.Oscillation.Lacunary.aemeasurable_cutFamM

/-!
# The dilation-profile reduction of the `oscZ` cut estimate

**The statement.**  Suppose that for every level `t ≥ 0` the *sharp cut* family

`i ↦ x ↦ ∫_{θ ∈ (0,1]} r θ · 1_{θ ≤ t / ⌊ρ^i⌋} · P(θ) · e(-2πi x θ) dθ`,  `P = Σ_{n ∈ T} f n e(nθ)`,

satisfies Bourgain's `ℓ²` block-oscillation bound with constant `(C₁ cap)²` (`hcut`).  Then the same
bound, with the *profile* `H` in place of the cut and with the constant
`(C cap (M+A))²`, holds for every profile that decomposes as

`H = H₁ + H₂`,  `H₁ u = -∫_{t ∈ (0,1]} Hd t · 1_{u ≤ t} dt`,  `‖Hd‖ ≤ M` on `(0,1]`,

with `H₂` square-summable along the lacunary dilations `⌊ρ^i⌋ θ` with total mass `≤ A²`
(`θ ∈ (0,1]`).

**The argument.**  `H₁` is the superposition, over the level `t ∈ (0,1]` and with weight `Hd t`, of
the sharp cuts `1_{u ≤ t}`; hence, by Fubini, the `H₁`-family is the `t`-integral of the cut
families, and the oscillation of a family that is an integral of families is bounded by the integral
of the oscillations (`M²` coming from `‖Hd‖ ≤ M` and from the Cauchy–Schwarz step on the
probability measure `(0,1]`):

  `oscZ(A_{H₁}) ≤ M² ∫_t oscZ(cut_t) dt ≤ (C₁ cap M)² ∫⁻‖f‖²`,

using the hypothesis for every `t`.  The `H₂` part is a square-function bound: the multipliers
`θ ↦ r θ H₂(⌊ρ^i⌋θ)` have pointwise `ℓ²`-mass `≤ (cap A)²`, so Plancherel gives
`oscZ(A_{H₂}) ≤ 8 (cap A)² ∫⁻‖f‖²`.  Adding (`oscZ_add_le`) and comparing constants gives the
claim with `C = max (2C₁) 6`.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The Stieltjes integral of a density bounded by `M` on `(0,1]` is bounded by `M`: the interval
`(0,1]` has length `1`, so the trivial estimate `‖∫_0^1 φ‖ ≤ ∫_0^1 ‖φ‖ ≤ M` suffices. -/
private lemma norm_stieltjes_integral_le (Hd : ℝ → ℂ) (M : ℝ)
    (hHdb : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Hd t‖ ≤ M) (u : ℝ) :
    ‖∫ t in (0:ℝ)..1, Hd t * (if u ≤ t then (1:ℂ) else 0)‖ ≤ M := by
  have hb : ∀ x ∈ Set.uIoc (0:ℝ) 1, ‖Hd x * (if u ≤ x then (1:ℂ) else 0)‖ ≤ M := by
    intro x hx
    rw [Set.uIoc, min_eq_left (by norm_num : (0:ℝ) ≤ 1),
      max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hif : ‖(if u ≤ x then (1:ℂ) else 0)‖ ≤ 1 := by split <;> simp
    have hdx : ‖Hd x‖ ≤ M := hHdb x hx
    calc ‖Hd x * (if u ≤ x then (1:ℂ) else 0)‖
        = ‖Hd x‖ * ‖(if u ≤ x then (1:ℂ) else 0)‖ := norm_mul _ _
      _ ≤ M * 1 := mul_le_mul hdx hif (norm_nonneg _) (le_trans (norm_nonneg _) hdx)
      _ = M := mul_one _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [sub_zero, abs_one, mul_one] at h

theorem dilation_profile_oscZ (ρ : ℝ) (hρ : 1 < ρ) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hcut : ∀ (t : ℝ), 0 ≤ t → ∀ (r : ℝ → ℂ), Measurable r → ∀ (cap : ℝ), 0 ≤ cap →
      (∀ θ, ‖r θ‖ ≤ cap) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (f : ℤ → ℂ) (T : Finset ℤ), (∀ n, n ∉ T → f n = 0) →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            ∫ θ in (0:ℝ)..1,
              (r θ * (if θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)
                then (1:ℂ) else 0)) *
              (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
              Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
          ≤ ENNReal.ofReal ((C₁ * cap) ^ 2) *
              ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H H₁ H₂ Hd : ℝ → ℂ), Measurable H → Measurable H₁ → Measurable H₂ → Measurable Hd →
      ∀ (A M : ℝ), 0 ≤ A → 0 ≤ M →
        (∀ u : ℝ, H u = H₁ u + H₂ u) →
        (∀ u : ℝ, 0 < u → H₁ u = -∫ t in (0:ℝ)..1, Hd t * (if u ≤ t then (1:ℂ) else 0)) →
        (∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Hd t‖ ≤ M) →
        (∀ θ ∈ Set.Ioc (0:ℝ) 1,
          Summable (fun i : ℕ => ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2) ∧
          ∑' i : ℕ, ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤ A ^ 2) →
        ∀ (r : ℝ → ℂ), Measurable r → ∀ (cap : ℝ), 0 ≤ cap → (∀ θ, ‖r θ‖ ≤ cap) →
        ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        ∀ (f : ℤ → ℂ) (T : Finset ℤ), (∀ n, n ∉ T → f n = 0) →
          Work.BourgainPlan.Oscillation.oscZ (fun i x =>
              ∫ θ in (0:ℝ)..1,
                (r θ * H ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) *
                (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
                Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
            ≤ ENNReal.ofReal ((C * cap * (M + A)) ^ 2) *
                ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  classical
  refine ⟨max (2 * C₁) 6, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro H H₁ H₂ Hd hHm hH₁m hH₂m hHdm A M hA hM hHsplit hH₁rep hHdb hH₂sum r hr cap hcap hrb
    J k hk f T hf
  change Work.BourgainPlan.Oscillation.oscZ (profFam H r f T ρ) J k
      ≤ ENNReal.ofReal ((max (2 * C₁) 6 * cap * (M + A)) ^ 2) *
        ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
  -- bounds on the two profile parts
  have hH₁b : ∀ u : ℝ, 0 < u → ‖H₁ u‖ ≤ M := by
    intro u hu
    rw [hH₁rep u hu, norm_neg]
    exact norm_stieltjes_integral_le Hd M hHdb u
  have hH₂b : ∀ u : ℝ, 0 < u → ‖H₂ u‖ ≤ A :=
    norm_le_of_summable_lacScale_dilations ρ hρ A hA H₂ hH₂sum
  -- the pointwise splitting of the family
  have hfam_add : ∀ i x, profFam H r f T ρ i x
      = profFam H₁ r f T ρ i x + profFam H₂ r f T ρ i x :=
    fun i x => profFam_add_eq ρ r hr cap hcap hrb H H₁ H₂ hHsplit hH₁m hH₂m M A hM hA
      hH₁b hH₂b f T i x
  have hdec := Work.BourgainPlan.Oscillation.oscZ_add_le (profFam H r f T ρ)
    (profFam H₁ r f T ρ) (profFam H₂ r f T ρ) hfam_add J k
  -- the `H₁` part: Fubini + the integrated cut bound
  let G : ℝ → ℕ → ℤ → ℂ := fun t i x => cutFamM t r f T ρ i x
  have hsub : ∀ (j i : ℕ) (x : ℤ),
      profFamM H₁ r f T ρ i x - profFamM H₁ r f T ρ (k j) x
        = -∫ t, Hd t * (G t i x - G t (k j) x) ∂mu01 := by
    intro j i x
    exact profFamM_sub_eq_integral_cutFamM ρ hρ cap M hcap hM Hd H₁ r f T hHdm hr hrb hH₁rep
      hHdb i (k j) x
  have hHdae : ∀ᵐ t ∂mu01, ‖Hd t‖ ≤ M := ae_restrict_of_forall_mem measurableSet_Ioc hHdb
  have hGm : ∀ i : ℕ, AEMeasurable (fun p : ℝ × ℤ => G p.1 i p.2)
      (mu01.prod MeasureTheory.Measure.count) :=
    fun i => (aemeasurable_cutFamM ρ r hr f T i).aemeasurable
  have hslice : ∀ x : ℤ, Measurable (fun t : ℝ => (t, x)) :=
    fun x => measurable_id.prod measurable_const
  have hGx : ∀ (i : ℕ) (x : ℤ), AEMeasurable (fun t : ℝ => G t i x) mu01 :=
    fun i x => ((aemeasurable_cutFamM ρ r hr f T i).comp (hslice x)).aemeasurable
  have hsup := oscZ_le_of_integral_oscZ J k hk M hM Hd hHdae (profFamM H₁ r f T ρ) G hsub hGm hGx
  have hprof_eq : (profFamM H₁ r f T ρ) = (profFam H₁ r f T ρ) :=
    funext fun i => funext fun x => (profFam_eq_profFamM H₁ r f T ρ i x).symm
  rw [hprof_eq] at hsup
  have hcutint : ∫⁻ t, Work.BourgainPlan.Oscillation.oscZ (G t) J k ∂mu01
      ≤ ENNReal.ofReal ((C₁ * cap) ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
    have hpt : ∀ᵐ t ∂mu01, Work.BourgainPlan.Oscillation.oscZ (G t) J k
        ≤ ENNReal.ofReal ((C₁ * cap) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
      ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
        have ht0 : 0 ≤ t := le_of_lt ht.1
        have hfam : G t = (fun i x => cutFam r f T
            (fun i => t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)) i x) :=
          funext fun i => funext fun x => cutFamM_eq_cutFam t r f T ρ i x
        rw [hfam]
        exact hcut t ht0 r hr cap hcap hrb J k hk f T hf)
    calc ∫⁻ t, Work.BourgainPlan.Oscillation.oscZ (G t) J k ∂mu01
        ≤ ∫⁻ t, ENNReal.ofReal ((C₁ * cap) ^ 2) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) ∂mu01 :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal ((C₁ * cap) ^ 2) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) * mu01 Set.univ :=
          lintegral_const _
      _ = ENNReal.ofReal ((C₁ * cap) ^ 2) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
          rw [measure_univ, mul_one]
  have h1a : Work.BourgainPlan.Oscillation.oscZ (profFam H₁ r f T ρ) J k
      ≤ ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal ((C₁ * cap) ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :=
    le_trans hsup (mul_le_mul_of_nonneg_left hcutint (bot_le))
  have h1 : Work.BourgainPlan.Oscillation.oscZ (profFam H₁ r f T ρ) J k
      ≤ ENNReal.ofReal ((C₁ * cap * M) ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
    have hkey : ENNReal.ofReal (M ^ 2) * ENNReal.ofReal ((C₁ * cap) ^ 2)
        = ENNReal.ofReal ((C₁ * cap * M) ^ 2) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg M)]
      congr 1
      ring
    calc Work.BourgainPlan.Oscillation.oscZ (profFam H₁ r f T ρ) J k
        ≤ ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal ((C₁ * cap) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := h1a
      _ = (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal ((C₁ * cap) ^ 2)) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by ring
      _ = ENNReal.ofReal ((C₁ * cap * M) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by rw [hkey]

  -- the `H₂` part: the square-function bound
  have h2 := oscZ_profFam_H2_le ρ hρ J k hk r hr cap A hcap hA hrb H₂ hH₂m hH₂sum f T hf
  -- assemble
  have hconst : 4 * (C₁ * cap * M) ^ 2 + 32 * (cap * A) ^ 2
      ≤ (max (2 * C₁) 6 * cap * (M + A)) ^ 2 := by
    have hCA : 4 * C₁ ^ 2 ≤ (max (2 * C₁) 6) ^ 2 := by
      have hle : 2 * C₁ ≤ max (2 * C₁) 6 := le_max_left _ _
      nlinarith
    have hC6 : (32:ℝ) ≤ (max (2 * C₁) 6) ^ 2 := by
      have hle : (6:ℝ) ≤ max (2 * C₁) 6 := le_max_right _ _
      nlinarith
    have hcap : 0 ≤ cap ^ 2 := sq_nonneg cap
    have h1 : 4 * (C₁ * cap * M) ^ 2
        ≤ (max (2 * C₁) 6) ^ 2 * cap ^ 2 * M ^ 2 := by
      calc 4 * (C₁ * cap * M) ^ 2 = (4 * C₁ ^ 2) * cap ^ 2 * M ^ 2 := by ring
        _ ≤ (max (2 * C₁) 6) ^ 2 * cap ^ 2 * M ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA hcap) (sq_nonneg M)
    have h2 : 32 * (cap * A) ^ 2 ≤ (max (2 * C₁) 6) ^ 2 * cap ^ 2 * A ^ 2 := by
      calc 32 * (cap * A) ^ 2 = 32 * cap ^ 2 * A ^ 2 := by ring
        _ ≤ (max (2 * C₁) 6) ^ 2 * cap ^ 2 * A ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC6 hcap) (sq_nonneg A)
    have hsum : (max (2 * C₁) 6) ^ 2 * cap ^ 2 * M ^ 2
          + (max (2 * C₁) 6) ^ 2 * cap ^ 2 * A ^ 2
        ≤ (max (2 * C₁) 6 * cap * (M + A)) ^ 2 := by
      have hMA : M ^ 2 + A ^ 2 ≤ (M + A) ^ 2 := by nlinarith
      calc (max (2 * C₁) 6) ^ 2 * cap ^ 2 * M ^ 2 + (max (2 * C₁) 6) ^ 2 * cap ^ 2 * A ^ 2
          = (max (2 * C₁) 6) ^ 2 * cap ^ 2 * (M ^ 2 + A ^ 2) := by ring
        _ ≤ (max (2 * C₁) 6) ^ 2 * cap ^ 2 * (M + A) ^ 2 :=
            mul_le_mul_of_nonneg_left hMA (mul_nonneg (sq_nonneg _) hcap)
        _ = (max (2 * C₁) 6 * cap * (M + A)) ^ 2 := by ring
    linarith [h1, h2, hsum]

  have hfo : (4:ℝ≥0∞) * (ENNReal.ofReal ((C₁ * cap * M) ^ 2) *
        (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count))
      + 4 * (ENNReal.ofReal (8 * (cap * A) ^ 2) *
        (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count))
      = ENNReal.ofReal (4 * (C₁ * cap * M) ^ 2 + 32 * (cap * A) ^ 2) *
        (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
    have h4a : (4:ℝ≥0∞) * ENNReal.ofReal ((C₁ * cap * M) ^ 2)
        = ENNReal.ofReal (4 * (C₁ * cap * M) ^ 2) := by
      rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    have h4b : (4:ℝ≥0∞) * ENNReal.ofReal (8 * (cap * A) ^ 2)
        = ENNReal.ofReal (32 * (cap * A) ^ 2) := by
      rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      congr 1
      ring
    calc (4:ℝ≥0∞) * (ENNReal.ofReal ((C₁ * cap * M) ^ 2) *
          (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count))
        + 4 * (ENNReal.ofReal (8 * (cap * A) ^ 2) *
          (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count))
        = ((4:ℝ≥0∞) * ENNReal.ofReal ((C₁ * cap * M) ^ 2)) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
          + ((4:ℝ≥0∞) * ENNReal.ofReal (8 * (cap * A) ^ 2)) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by ring
      _ = ENNReal.ofReal (4 * (C₁ * cap * M) ^ 2) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
          + ENNReal.ofReal (32 * (cap * A) ^ 2) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
          rw [h4a, h4b]
      _ = (ENNReal.ofReal (4 * (C₁ * cap * M) ^ 2)
            + ENNReal.ofReal (32 * (cap * A) ^ 2)) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by ring
      _ = ENNReal.ofReal (4 * (C₁ * cap * M) ^ 2 + 32 * (cap * A) ^ 2) *
            (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]

  calc Work.BourgainPlan.Oscillation.oscZ (profFam H r f T ρ) J k
      ≤ 4 * Work.BourgainPlan.Oscillation.oscZ (profFam H₁ r f T ρ) J k
        + 4 * Work.BourgainPlan.Oscillation.oscZ (profFam H₂ r f T ρ) J k := hdec
    _ ≤ 4 * (ENNReal.ofReal ((C₁ * cap * M) ^ 2) *
          (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count))
        + 4 * (ENNReal.ofReal (8 * (cap * A) ^ 2) *
          (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = ENNReal.ofReal (4 * (C₁ * cap * M) ^ 2 + 32 * (cap * A) ^ 2) *
          (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := hfo
    _ ≤ ENNReal.ofReal ((max (2 * C₁) 6 * cap * (M + A)) ^ 2) *
          (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl

end

end Work.BourgainPlan.Oscillation.Lacunary
