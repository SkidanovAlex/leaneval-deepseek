import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open MeasureTheory

/-- The Lebesgue measure restricted to the interval `(0, 1]`. -/
private noncomputable def csMu : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- `v^(β/2) * v^(β/2) = v^β` for `v > 0` — the split of the `rpow` weight. -/
private lemma half_rpow_mul {β v : ℝ} (hv : 0 < v) :
    v ^ (β / 2) * v ^ (β / 2) = v ^ β := by
  rw [← Real.rpow_add hv, show β / 2 + β / 2 = β by ring]

/-- Abstract Cauchy–Schwarz on a measure space, with only `Integrable` hypotheses
(no measurability assumption on `f` or `g`): `(∫ f g)² ≤ (∫ f²)(∫ g²)`.

Proof: for every real `t` the integral `∫ (f - t g)²` is nonnegative and expands to the
quadratic `A - 2tB + t²C`; evaluating this quadratic (at `t = B/C`, or deriving `B = 0`
when `C = 0`) gives `B² ≤ A C`. -/
private lemma cs_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  suffices ∀ A B C : ℝ, A = ∫ x, f x ^ 2 ∂μ → B = ∫ x, f x * g x ∂μ →
      C = ∫ x, g x ^ 2 ∂μ → B ^ 2 ≤ A * C from this _ _ _ rfl rfl rfl
  intro A B C hA hB hC
  have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have hae : (fun x => (f x - t * g x) ^ 2)
        =ᵐ[μ] (fun x => f x ^ 2 - 2 * t * (f x * g x) + t ^ 2 * (g x) ^ 2) :=
      Filter.Eventually.of_forall fun x => by ring
    have hnn : 0 ≤ ∫ x, (f x - t * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have heval : (∫ x, (f x - t * g x) ^ 2 ∂μ) = A - 2 * t * B + t ^ 2 * C := by
      have e2 : (∫ x, f x ^ 2 - 2 * t * (f x * g x) + t ^ 2 * (g x) ^ 2 ∂μ)
          = (∫ x, f x ^ 2 - 2 * t * (f x * g x) ∂μ)
            + (∫ x, t ^ 2 * (g x) ^ 2 ∂μ) :=
        integral_add (hf.sub (hfg.const_mul (2 * t))) (hg.const_mul (t ^ 2))
      have e3 : (∫ x, f x ^ 2 - 2 * t * (f x * g x) ∂μ)
          = (∫ x, f x ^ 2 ∂μ) - (∫ x, 2 * t * (f x * g x) ∂μ) :=
        integral_sub hf (hfg.const_mul (2 * t))
      have e4 : (∫ x, 2 * t * (f x * g x) ∂μ) = 2 * t * (∫ x, f x * g x ∂μ) :=
        integral_const_mul (2 * t) (fun x => f x * g x)
      have e5 : (∫ x, t ^ 2 * (g x) ^ 2 ∂μ) = t ^ 2 * (∫ x, g x ^ 2 ∂μ) :=
        integral_const_mul (t ^ 2) (fun x => g x ^ 2)
      rw [integral_congr_ae hae, e2, e3, e4, e5, ← hA, ← hB, ← hC]
    linarith [hnn, heval]
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg fun x => sq_nonneg (f x)
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg fun x => sq_nonneg (g x)
  by_cases hCz : C = 0
  · have hB0 : B = 0 := by
      by_contra hBn
      have h2 : 2 * ((A + 1) / (2 * B)) * B = A + 1 := by
        field_simp
      have h3 := hquad ((A + 1) / (2 * B))
      rw [hCz, mul_zero, add_zero] at h3
      linarith [h3, h2]
    rw [hB0, hCz]
    simp
  · have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hCz)
    have h4 : 0 ≤ (A - 2 * (B / C) * B + (B / C) ^ 2 * C) * C :=
      mul_nonneg (hquad (B / C)) hCpos.le
    have hid : (A - 2 * (B / C) * B + (B / C) ^ 2 * C) * C = A * C - B ^ 2 := by
      field_simp
      ring
    rw [hid] at h4
    linarith

/-- If `v ↦ v^β * a v` is integrable on `(0,1]` and `|a| ≤ M` there, then also
`v ↦ v^β * a v^2` is integrable there.  (`a` need not be measurable: it is the quotient of
the integrable `v ↦ v^β * a v` by the continuous positive function `v ↦ v^β`.) -/
private lemma integrable_sq_of_integrable {β M : ℝ} (hM : 0 ≤ M) {a : ℝ → ℝ}
    (ha : ∀ v, v ∈ Set.Ioc (0 : ℝ) 1 → |a v| ≤ M)
    (hF : Integrable (fun v : ℝ => v ^ β * a v) csMu) :
    Integrable (fun v : ℝ => v ^ β * (a v) ^ 2) csMu := by
  have hb : AEStronglyMeasurable (fun v : ℝ => v ^ (-β)) csMu :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).aestronglyMeasurable
      measurableSet_Ioc
  have haesm : AEStronglyMeasurable a csMu := by
    have h1 : AEStronglyMeasurable (fun v : ℝ => (v ^ β * a v) * v ^ (-β)) csMu :=
      hF.aestronglyMeasurable.mul hb
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have h2 : v ^ β * v ^ (-β) = 1 := by
      rw [← Real.rpow_add hv.1, add_neg_cancel, Real.rpow_zero]
    calc (v ^ β * a v) * v ^ (-β) = a v * (v ^ β * v ^ (-β)) := by ring
      _ = a v * 1 := by rw [h2]
      _ = a v := by ring
  have hGaesm : AEStronglyMeasurable (fun v : ℝ => v ^ β * (a v) ^ 2) csMu := by
    have h1 : AEStronglyMeasurable (fun v : ℝ => (v ^ β * a v) * a v) csMu :=
      hF.aestronglyMeasurable.mul haesm
    exact h1.congr (Filter.Eventually.of_forall fun v => by ring)
  refine Integrable.mono' ((hF.const_mul M).norm) hGaesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hvp : 0 < v ^ β := Real.rpow_pos_of_pos hv.1 β
  have hle : |a v| ^ 2 ≤ M * |a v| := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (ha v hv) (abs_nonneg (a v))
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hvp, abs_of_nonneg hM]
  calc v ^ β * |a v| ^ 2 ≤ v ^ β * (M * |a v|) := mul_le_mul_of_nonneg_left hle hvp.le
    _ = M * (v ^ β * |a v|) := by ring

/-- Cauchy–Schwarz with the `rpow` weight split as `β = β/2 + β/2`, in the case where all
three integrability hypotheses hold. -/
private lemma cs_rpow_aux {β : ℝ} {a : ℝ → ℝ}
    (hW : Integrable (fun v : ℝ => v ^ β) csMu)
    (hF : Integrable (fun v : ℝ => v ^ β * a v) csMu)
    (hG : Integrable (fun v : ℝ => v ^ β * (a v) ^ 2) csMu) :
    (∫ v, v ^ β * a v ∂csMu) ^ 2
      ≤ (∫ v, v ^ β ∂csMu) * (∫ v, v ^ β * (a v) ^ 2 ∂csMu) := by
  have hmem : ∀ᵐ v ∂csMu, v ∈ Set.Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have ee_W : (fun v : ℝ => v ^ β) =ᵐ[csMu] (fun v : ℝ => (v ^ (β / 2)) ^ 2) := by
    filter_upwards [hmem] with v hv
    rw [pow_two, half_rpow_mul hv.1]
  have ee_F : (fun v : ℝ => v ^ β * a v) =ᵐ[csMu]
      (fun v : ℝ => v ^ (β / 2) * (v ^ (β / 2) * a v)) := by
    filter_upwards [hmem] with v hv
    rw [← mul_assoc, half_rpow_mul hv.1]
  have ee_G : (fun v : ℝ => v ^ β * (a v) ^ 2) =ᵐ[csMu]
      (fun v : ℝ => (v ^ (β / 2) * a v) ^ 2) := by
    filter_upwards [hmem] with v hv
    have h2 : (v ^ (β / 2)) ^ 2 = v ^ β := by rw [pow_two, half_rpow_mul hv.1]
    rw [mul_pow, h2]
  have hp : Integrable (fun v : ℝ => (v ^ (β / 2)) ^ 2) csMu := hW.congr ee_W
  have hpq : Integrable (fun v : ℝ => v ^ (β / 2) * (v ^ (β / 2) * a v)) csMu :=
    hF.congr ee_F
  have hq : Integrable (fun v : ℝ => (v ^ (β / 2) * a v) ^ 2) csMu := hG.congr ee_G
  have key := cs_sq_le (μ := csMu) (f := fun v : ℝ => v ^ (β / 2))
    (g := fun v : ℝ => v ^ (β / 2) * a v) hp hpq hq
  rw [integral_congr_ae ee_F.symm, integral_congr_ae ee_W.symm,
    integral_congr_ae ee_G.symm] at key
  exact key

/-- Cauchy–Schwarz for the `rpow`-weighted interval integral.  For `-1 < β` and `a` bounded by `M`
on `(0,1]`, the square of `∫₀¹ v^β a(v) dv` is at most `(∫₀¹ v^β) * (∫₀¹ v^β a(v)²)`.

No measurability of `a` is assumed: if `v ↦ v^β a(v)^2` is not (interval-)integrable, then
`v ↦ v^β a(v)` is not integrable either, so by the `integral_undef` convention both sides vanish. -/
theorem cs_rpow_bounded {β M : ℝ} (hβ : -1 < β) {a : ℝ → ℝ} (hM : 0 ≤ M)
    (ha : ∀ v, v ∈ Set.Ioc (0 : ℝ) 1 → |a v| ≤ M) :
    (∫ v in (0 : ℝ)..1, v ^ β * a v) ^ 2
      ≤ (∫ v in (0 : ℝ)..1, v ^ β) * (∫ v in (0 : ℝ)..1, v ^ β * (a v) ^ 2) := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  simp only [intervalIntegral.integral_of_le h01]
  change (∫ v, v ^ β * a v ∂csMu) ^ 2
      ≤ (∫ v, v ^ β ∂csMu) * (∫ v, v ^ β * (a v) ^ 2 ∂csMu)
  have hW : Integrable (fun v : ℝ => v ^ β) csMu := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hβ
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01] at h
    exact h
  by_cases hG : Integrable (fun v : ℝ => v ^ β * (a v) ^ 2) csMu
  · by_cases hF : Integrable (fun v : ℝ => v ^ β * a v) csMu
    · exact cs_rpow_aux hW hF hG
    · rw [integral_undef hF]
      have hY : 0 ≤ ∫ v, v ^ β ∂csMu := integral_nonneg_of_ae <| by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
        exact Real.rpow_nonneg hv.1.le β
      have hZ : 0 ≤ ∫ v, v ^ β * (a v) ^ 2 ∂csMu := integral_nonneg_of_ae <| by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
        exact mul_nonneg (Real.rpow_nonneg hv.1.le β) (sq_nonneg (a v))
      simpa using mul_nonneg hY hZ
  · have hFn : ¬ Integrable (fun v : ℝ => v ^ β * a v) csMu :=
      fun hF => hG (integrable_sq_of_integrable hM ha hF)
    rw [integral_undef hFn, integral_undef hG]
    simp

end Work.FTS_EllLimOK.ProducerH
