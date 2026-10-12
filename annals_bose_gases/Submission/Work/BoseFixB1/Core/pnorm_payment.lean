import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.Core.symA_zero_decay_pow
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Core

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 0. Elementary facts about the corpus bump and the symbol -/

/-- The absolute sup of the corpus bump is positive. -/
private lemma chiSupAbs_pos : 0 < Submission.BoseGases.chiSupAbs := by
  rw [Submission.BoseGases.chiSupAbs]
  exact inv_pos.mpr (Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos)

/-- **Pointwise support/bookkeeping estimate.**  Since `χ_ℓ` is supported in `acube ℓ` and
`|χ_ℓ| ≤ chiSupAbs`, for `f ≥ 0` the integrand `χ_ℓ² f` is dominated by
`chiSupAbs² (acube ℓ).indicator f`. -/
private lemma chiScale_sq_mul_indicator_le {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (z : E3) :
    Submission.BoseGases.chiScale ℓ z ^ 2 * f z
      ≤ Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.acube ℓ).indicator f z := by
  by_cases hz : Submission.BoseGases.chiScale ℓ z = 0
  · rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun a _ => hf0 a) z)
  · rw [Set.indicator_of_mem (Submission.BoseGases.chiScale_mem_acube hℓ hz)]
    refine mul_le_mul_of_nonneg_right ?_ (hf0 z)
    have h := Submission.BoseGases.chiScale_abs_le_sup ℓ z
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **The `χ_ℓ²`-weighted integral is bounded by the mean-square over `acube ℓ`:**

    `∫ χ_ℓ(z)² f(z) dz ≤ chiSupAbs² ∫_{acube ℓ} f(z) dz`   for `f ≥ 0` integrable on `acube ℓ`.

`χ_ℓ` vanishes outside `acube ℓ` (`chiScale_mem_acube`) and is bounded by `chiSupAbs`
(`chiScale_abs_le_sup`), so the pointwise estimate of the previous lemma integrates. -/
private lemma integral_chiScale_sq_mul_le {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hfi : IntegrableOn f (Submission.BoseGases.acube ℓ)) :
    (∫ z : E3, Submission.BoseGases.chiScale ℓ z ^ 2 * f z)
      ≤ Submission.BoseGases.chiSupAbs ^ 2 * ∫ z in Submission.BoseGases.acube ℓ, f z := by
  have hae : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hgi : Integrable (fun z : E3 => Submission.BoseGases.chiSupAbs ^ 2 *
      (Submission.BoseGases.acube ℓ).indicator f z) :=
    ((integrable_indicator_iff hae).mpr hfi).const_mul _
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hf0 z)) hgi
    (Filter.Eventually.of_forall fun z => chiScale_sq_mul_indicator_le hℓ hf0 z)
  calc (∫ z : E3, Submission.BoseGases.chiScale ℓ z ^ 2 * f z)
      ≤ ∫ z : E3, Submission.BoseGases.chiSupAbs ^ 2 *
          (Submission.BoseGases.acube ℓ).indicator f z := hmono
    _ = Submission.BoseGases.chiSupAbs ^ 2 *
          ∫ z : E3, (Submission.BoseGases.acube ℓ).indicator f z :=
        MeasureTheory.integral_const_mul _ _
    _ = Submission.BoseGases.chiSupAbs ^ 2 *
          ∫ z in Submission.BoseGases.acube ℓ, f z := by
        rw [MeasureTheory.integral_indicator hae]

/-! ## 1. The arithmetic: extracting the smallness threshold from `μ(a v)³` -/

/-- `t ≤ A^{323/4}` forces `(t^{1/323})^4 ≤ A` (for `0 ≤ t`, `0 < A`). -/
private lemma threshold_pow {t A : ℝ} (ht : 0 ≤ t) (hA : 0 < A)
    (h : t ≤ A ^ ((323 : ℝ) / 4)) : (t ^ ((1 : ℝ) / 323)) ^ 4 ≤ A := by
  have h1 : (t ^ ((1 : ℝ) / 323)) ^ 4 = t ^ ((4 : ℝ) / 323) := by
    rw [← Real.rpow_natCast (t ^ ((1 : ℝ) / 323)) 4,
      ← Real.rpow_mul ht ((1 : ℝ) / 323) ((4 : ℕ) : ℝ)]
    congr 1
    norm_num
  have h2 : (A ^ ((323 : ℝ) / 4)) ^ ((4 : ℝ) / 323) = A := by
    rw [← Real.rpow_mul hA.le, show (323 : ℝ) / 4 * ((4 : ℝ) / 323) = 1 by norm_num,
      Real.rpow_one]
  calc (t ^ ((1 : ℝ) / 323)) ^ 4 = t ^ ((4 : ℝ) / 323) := h1
    _ ≤ (A ^ ((323 : ℝ) / 4)) ^ ((4 : ℝ) / 323) :=
        Real.rpow_le_rpow ht h (by norm_num)
    _ = A := h2

/-- `t ≤ 2^{-323}` forces `2 t^{1/323} ≤ 1`, i.e. `(1/(2s)) ≥ 1` at `s = t^{1/323}`. -/
private lemma two_mul_rpow_le_one {t : ℝ} (ht : 0 ≤ t) (h : t ≤ (2 : ℝ) ^ (-(323 : ℝ))) :
    2 * t ^ ((1 : ℝ) / 323) ≤ 1 := by
  have h1 : t ^ ((1 : ℝ) / 323) ≤ ((2 : ℝ) ^ (-(323 : ℝ))) ^ ((1 : ℝ) / 323) :=
    Real.rpow_le_rpow ht h (by norm_num)
  have h2 : ((2 : ℝ) ^ (-(323 : ℝ))) ^ ((1 : ℝ) / 323) = (2 : ℝ)⁻¹ := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (-(323 : ℝ)) * ((1 : ℝ) / 323) = -1 by norm_num, Real.rpow_neg_one]
  rw [h2] at h1
  linarith

/-- **The coefficient comparison.**  If `β ≤ K (2s)^16`, `d = s⁶` and
`K 2^{16} chiSupAbs² s⁴ ≤ b/8`, then `β chiSupAbs²/(dℓ)² ≤ b/(8ℓ²)`. -/
private lemma coef_le {K s d b β ℓ : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hℓ : 0 < ℓ)
    (hd6 : d = s ^ 6) (hb : b = 1 / 16) (hβ0 : 0 ≤ β) (hβ : β ≤ K * (2 * s) ^ 16)
    (hsmall : K * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2 * s ^ 4 ≤ b / 8) :
    β / (d * ℓ) ^ 2 * Submission.BoseGases.chiSupAbs ^ 2 ≤ b / (8 * ℓ ^ 2) := by
  have hχ2 : 0 ≤ Submission.BoseGases.chiSupAbs ^ 2 := sq_nonneg _
  have hdpos : 0 < d := by rw [hd6]; positivity
  have hden : 0 < (d * ℓ) ^ 2 := by positivity
  have step1 : β / (d * ℓ) ^ 2 * Submission.BoseGases.chiSupAbs ^ 2
      ≤ K * (2 * s) ^ 16 / (d * ℓ) ^ 2 * Submission.BoseGases.chiSupAbs ^ 2 :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hβ hden.le) hχ2
  have step2 : K * (2 * s) ^ 16 / (d * ℓ) ^ 2 * Submission.BoseGases.chiSupAbs ^ 2
      = K * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2 * s ^ 4 / ℓ ^ 2 := by
    rw [hd6]
    field_simp
  have step3 : K * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2 * s ^ 4 / ℓ ^ 2
      ≤ b / (8 * ℓ ^ 2) := by
    have hℓ2 : 0 < ℓ ^ 2 := pow_pos hℓ 2
    have h := div_le_div_of_nonneg_right hsmall hℓ2.le
    rw [div_div] at h
    exact h
  calc β / (d * ℓ) ^ 2 * Submission.BoseGases.chiSupAbs ^ 2
      ≤ K * (2 * s) ^ 16 / (d * ℓ) ^ 2 * Submission.BoseGases.chiSupAbs ^ 2 := step1
    _ = K * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2 * s ^ 4 / ℓ ^ 2 := step2
    _ ≤ b / (8 * ℓ ^ 2) := step3

/-! ## 2. The core payment estimate -/

/-- **The payment is covered by the gap slack.**  With `β` the constant term of the scaled
two-cut symbol comparison and `M = ℓ⁻³∫_{acube ℓ}ψ` the box mean, the `(β/(dℓ)²)`-multiple of
the `χ_ℓ²`-weighted mean-square deviation is dominated by `b/(8ℓ²)` times the mean-square
deviation over the box, as soon as `β ≤ K(2s)^{16}`, `d = s⁶` and the smallness
`K 2^{16} chiSupAbs² s⁴ ≤ b/8` holds. -/
private lemma payment_core {K ℓ s d b β : ℝ} (hK : 0 ≤ K) (hℓ : 0 < ℓ) (hs : 0 < s)
    (hd6 : d = s ^ 6) (hb : b = 1 / 16) (hβ0 : 0 ≤ β) (hβ : β ≤ K * (2 * s) ^ 16)
    (hsmall : K * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2 * s ^ 4 ≤ b / 8)
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    (β / (d * ℓ) ^ 2) *
        (∫ z : E3, Submission.BoseGases.chiScale ℓ z ^ 2 *
          (ψ z - (1 / ℓ ^ 3) * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2)
      ≤ (b / (8 * ℓ ^ 2)) *
        (∫ z in Submission.BoseGases.acube ℓ,
          (ψ z - (1 / ℓ ^ 3) * ∫ z' in Submission.BoseGases.acube ℓ, ψ z') ^ 2) := by
  let M : ℝ := (1 / ℓ ^ 3) * ∫ z' in Submission.BoseGases.acube ℓ, ψ z'
  have hcont : Continuous (fun z : E3 => (ψ z - M) ^ 2) :=
    (hψ.continuous.sub continuous_const).pow 2
  have hf0 : ∀ z : E3, 0 ≤ (ψ z - M) ^ 2 := fun z => sq_nonneg _
  have hfi : IntegrableOn (fun z : E3 => (ψ z - M) ^ 2) (Submission.BoseGases.acube ℓ) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      hcont.continuousOn
  have hIJ : (∫ z : E3, Submission.BoseGases.chiScale ℓ z ^ 2 * (ψ z - M) ^ 2)
      ≤ Submission.BoseGases.chiSupAbs ^ 2 *
        ∫ z in Submission.BoseGases.acube ℓ, (ψ z - M) ^ 2 :=
    integral_chiScale_sq_mul_le hℓ hf0 hfi
  have hJ : 0 ≤ ∫ z in Submission.BoseGases.acube ℓ, (ψ z - M) ^ 2 := by
    rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
    exact MeasureTheory.integral_nonneg
      (fun z => Set.indicator_nonneg (fun a _ => hf0 a) z)
  have hcoef : β / (d * ℓ) ^ 2 * Submission.BoseGases.chiSupAbs ^ 2 ≤ b / (8 * ℓ ^ 2) :=
    coef_le hK hs hℓ hd6 hb hβ0 hβ hsmall
  calc (β / (d * ℓ) ^ 2) *
        (∫ z : E3, Submission.BoseGases.chiScale ℓ z ^ 2 * (ψ z - M) ^ 2)
      ≤ (β / (d * ℓ) ^ 2) * (Submission.BoseGases.chiSupAbs ^ 2 *
          ∫ z in Submission.BoseGases.acube ℓ, (ψ z - M) ^ 2) :=
        mul_le_mul_of_nonneg_left hIJ (div_nonneg hβ0 (by positivity))
    _ = (β / (d * ℓ) ^ 2 * Submission.BoseGases.chiSupAbs ^ 2) *
          ∫ z in Submission.BoseGases.acube ℓ, (ψ z - M) ^ 2 := by ring
    _ ≤ (b / (8 * ℓ ^ 2)) *
          (∫ z in Submission.BoseGases.acube ℓ, (ψ z - M) ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef hJ

/-! ## 3. The theorem -/

/-- The constant term of the scaled two-cut symbol comparison is payable by the gap slack: with
`β = symA 1 (fsKinCoeff (1/(2s))) 0` (the value forced by `Work.BoseFixB1.symA_fsKinCoeff_mix_scaled`
at `C = 1/s`) and `ψ₀ = χ_ℓ(ψ − M)`, `M = ℓ⁻³∫_{acube ℓ}ψ`, `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`,
`b = (paramsAt μ (a v)).b`, the payment `(β/(dℓ)²)·‖ψ₀‖²₂` is at most `(b/(8ℓ²))·∫_{acube ℓ}(ψ−M)²`
for small diluteness `μ(a v)³ ≤ ε₀`.  Proof route: `symA_zero_decay_pow` gives `β ≤ K(2s)^{16}`,
`tsupport (chiScale ℓ) ⊆ acube ℓ` gives `∫χ_ℓ²(ψ−M)² ≤ chiSupAbs²∫_{acube ℓ}(ψ−M)²`
(`Work.ChiSmall.chiScale_abs_le_sup`), and `d = s⁶` (`Work.BoseFixB1S.d_eq_s_pow`), so it suffices
that `K 2^{16} chiSupAbs² s⁴ ≤ b/8`, true below an explicit threshold on `μ(a v)³`. -/
theorem pnorm_payment {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) ψ →
        (Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff
            (1 / (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s))) 0
          / ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d *
              Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)
          * (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2 *
              (ψ z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                ∫ z' in Submission.BoseGases.acube
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), ψ z') ^ 2)
        ≤ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b /
            (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) *
          (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (ψ z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                ∫ z' in Submission.BoseGases.acube
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), ψ z') ^ 2) := by
  obtain ⟨K, hK0, hKdecay⟩ := symA_zero_decay_pow
  have hχ0 : 0 < Submission.BoseGases.chiSupAbs := chiSupAbs_pos
  -- The explicit diluteness threshold.
  set T : ℝ := (128 * (K + 1) * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2)⁻¹ with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  refine ⟨min ((2 : ℝ) ^ (-(323 : ℝ))) (T ^ ((323 : ℝ) / 4)), ?_, ?_⟩
  · exact lt_min (by positivity) (Real.rpow_pos_of_pos hTpos _)
  · intro μ hAdm ψ hψ
    have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
    have ht_le : μ * (_root_.BoseGases.a v) ^ 3
        ≤ min ((2 : ℝ) ^ (-(323 : ℝ))) (T ^ ((323 : ℝ) / 4)) := hAdm.2.1
    have ht0 : 0 ≤ μ * (_root_.BoseGases.a v) ^ 3 := le_of_lt (mul_pos hμ (pow_pos hav 3))
    have ht2 : μ * (_root_.BoseGases.a v) ^ 3 ≤ (2 : ℝ) ^ (-(323 : ℝ)) :=
      le_trans ht_le (min_le_left _ _)
    have htT : μ * (_root_.BoseGases.a v) ^ 3 ≤ T ^ ((323 : ℝ) / 4) :=
      le_trans ht_le (min_le_right _ _)
    have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      Work.BoseFixB1.adm_ell_pos hAdm
    have hspos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s :=
      Work.BoseFixB1.adm_s_pos hAdm
    have hspow : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323) := by
      show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1 = _
      rfl
    have hd6 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 6 := by
      show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6
        = (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1) ^ 6
      rw [Work.BoseBox.fsXp_pow ht0 1 6]
      norm_num
    have hb : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b = 1 / 16 := by
      rw [Work.BoseFixB1.paramsAt_b_eq]
      norm_num [Work.BoseBox.bValue]
    -- `s⁴ ≤ T`, hence the smallness of `K 2^{16} chiSupAbs² s⁴`.
    have hs4 : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 4 ≤ T := by
      rw [hspow]
      exact threshold_pow ht0 hTpos htT
    have hsmall : K * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 4 ≤ 1 / 128 := by
      have hstep1 : K * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 4
          ≤ (K + 1) * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2
            * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 4 := by
        have hA : (0 : ℝ) ≤ 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2
            * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 4 := by positivity
        nlinarith [hK0, hA]
      have hstep2 : (K + 1) * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 4
          ≤ (K + 1) * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2 * T :=
        mul_le_mul_of_nonneg_left hs4 (by positivity)
      have hstep3 : (K + 1) * 2 ^ 16 * Submission.BoseGases.chiSupAbs ^ 2 * T = 1 / 128 := by
        rw [hT]
        field_simp
      rw [← hstep3]
      exact le_trans hstep1 hstep2
    -- `β ≥ 0` and `β ≤ K (2s)^{16}`.
    have hβ0 : 0 ≤ Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff
        (1 / (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s))) 0 := by
      rw [Work.OneBodyKin.symA]
      refine mul_nonneg (by positivity) (MeasureTheory.integral_nonneg (fun p => ?_))
      exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (sq_nonneg _)
    have hβ : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff
        (1 / (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s))) 0
        ≤ K * (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 16 := by
      have h2s : 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≤ 1 := by
        rw [hspow]
        exact two_mul_rpow_le_one ht0 ht2
      have hC : (1 : ℝ) ≤ 1 / (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) := by
        rw [one_div]
        exact (one_le_inv₀ (by positivity)).mpr h2s
      have hdec := hKdecay _ hC
      have he : (1 / (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)) ^ (-(16 : ℝ))
          = (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 16 := by
        rw [one_div,
          Real.inv_rpow (by positivity :
            (0 : ℝ) ≤ 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s),
          Real.rpow_neg (by positivity :
            (0 : ℝ) ≤ 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s),
          inv_inv, Real.rpow_ofNat]
      rwa [he] at hdec
    refine payment_core hK0 hℓpos hspos hd6 hb hβ0 hβ ?_ hψ
    rw [hb]
    linarith [hsmall]

end

end Work.BoseFixB1.Core
