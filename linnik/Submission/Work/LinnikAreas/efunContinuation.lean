/-
# Analytic continuation of the Abel integral `∫ E(x) x^{-s-1} dx` to `Re s > 1/2`

For `χ` a Dirichlet character mod `q` the Abel-summation identity

  `s · ∫_1^∞ E(x) x^{-s-1} dx = ζ(s)L(s,χ) - s·L(1,χ)/(s-1)`

is available for `Re s > 1` (see `lamAbelIntegral`), where `E(x) = A(x) - x·L(1,χ)` is the
error term of the summatory function of `λ = 1 * χ`.  Under the input `‖E(x)‖ ≤ K √x` the
integral converges for `Re s > 1/2` and is analytic there (Mellin transform), while

  `(s-1)·(ζ(s)L(s,χ) - s·L(1,χ)/(s-1)) = riemannZeta₁ s · L(s,χ) - s·L(1,χ)`

is entire (`riemannZeta₁` is the removable singularity of `(s-1)ζ(s)` at `s = 1`).  The identity
principle therefore extends the Abel identity to the half-plane `Re s > 1/2`.  Evaluating at a
zero `β ∈ (1/2,1)` of `L(·,χ)` (where the `ζL` term vanishes) gives

  `∫_1^∞ E(x) x^{-1-β} dx = L(1,χ)/(1-β)`,

the key analytic input for the ratio bounds in `ratioZeroL1fixed`.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.efunMellinEqIntegral
import Submission.Work.LinnikAreas.efunIndicatorLocInt
import Submission.Work.LinnikAreas.efunIndicatorBigO

namespace Work.LinnikAreas

open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The truncated error term `1_{(1,∞)}·E` vanishes in a neighbourhood of `0`, so it is
`O(x^{-b})` at `0⁺` for every `b`. -/
lemma efunIndicator_isBigO_nhdsGT (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (Set.indicator (Set.Ioi (1:ℝ)) (Efun χ)) =O[𝓝[>] (0:ℝ)] (fun t : ℝ => t ^ (-b)) := by
  have hf0 : (Set.indicator (Set.Ioi (1:ℝ)) (Efun χ)) =ᶠ[𝓝[>] (0:ℝ)] 0 := by
    have h1 : Set.Iio (1:ℝ) ∈ 𝓝[>] (0:ℝ) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num))
    filter_upwards [h1] with t ht1
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; exact not_lt.mpr ht1.le)]
    rfl
  exact (hf0.isBigO).trans (isBigO_zero _ _)

/-- The Mellin transform of the truncated error term `1_{(1,∞)}·E` is analytic at every point of
the half-plane `Re s > 1/2`; this is the analytic continuation of the Abel integral. -/
lemma analyticAt_efunIntegral_aux (χ : DirichletCharacter ℂ q) {K : ℝ}
    (hE : ∀ x : ℝ, 1 ≤ x → ‖Efun χ x‖ ≤ K * Real.sqrt x) {s : ℂ} (hs : 1/2 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ) ^ (-(z + 1))) s := by
  have htop' : (Set.indicator (Set.Ioi (1:ℝ)) (Efun χ)) =O[atTop]
      (fun t : ℝ => t ^ (-(-(1/2) : ℝ))) := by
    refine (efunIndicatorBigO χ hE).congr_right ?_
    intro t
    congr 1
    norm_num
  have hloc : LocallyIntegrableOn (Set.indicator (Set.Ioi (1:ℝ)) (Efun χ)) (Set.Ioi 0) :=
    efunIndicatorLocInt χ hE
  have hr : 0 < (s.re - 1/2)/2 := by linarith
  have haux : ∀ z : ℂ, (1/2 : ℝ) < z.re → DifferentiableAt ℂ
      (fun w : ℂ => mellin (Set.indicator (Set.Ioi (1:ℝ)) (Efun χ)) (-w)) z := by
    intro z hz
    have hzt : (-z).re < (-(1/2) : ℝ) := by rw [Complex.neg_re]; linarith
    have hzb : (-z).re - 1 < (-z).re := by linarith
    exact ((mellin_differentiableAt_of_isBigO_rpow hloc htop' hzt
      (efunIndicator_isBigO_nhdsGT χ ((-z).re - 1)) hzb).comp z (by fun_prop))
  have hD : DifferentiableOn ℂ
      (fun w : ℂ => mellin (Set.indicator (Set.Ioi (1:ℝ)) (Efun χ)) (-w))
      (Metric.ball s ((s.re - 1/2)/2)) := by
    intro z hz
    have h1 : ‖z - s‖ < (s.re - 1/2)/2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact hz
    have h2 : |z.re - s.re| ≤ ‖z - s‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - s)
    rw [abs_le] at h2
    exact (haux z (by linarith [h2.1])).differentiableWithinAt
  have hAnal : AnalyticAt ℂ
      (fun w : ℂ => mellin (Set.indicator (Set.Ioi (1:ℝ)) (Efun χ)) (-w)) s :=
    hD.analyticAt (Metric.ball_mem_nhds s hr)
  have hΦeq : (fun w : ℂ => mellin (Set.indicator (Set.Ioi (1:ℝ)) (Efun χ)) (-w))
      = fun w : ℂ => ∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ) ^ (-(w + 1)) := by
    funext w
    rw [efunMellinEqIntegral χ (-w)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    congr 1
    ring
  rw [hΦeq] at hAnal
  exact hAnal

/-- **The Abel identity in the strip `1/2 < Re s < 1`.**  Multiplying the identity of
`lamAbelIntegral` by `s - 1` replaces the right-hand side by the entire function
`riemannZeta₁ s · L(s,χ) - s·L(1,χ)`, so the identity principle on the connected half-plane
`Re s > 1/2` extends it from `Re s > 1` to the whole half-plane. -/
lemma efunAbel_halfPlane (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : ℝ}
    (hE : ∀ x : ℝ, 1 ≤ x → ‖Efun χ x‖ ≤ K * Real.sqrt x)
    (hId : ∀ s : ℂ, 1 < s.re → s * (∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ) ^ (-(s + 1)))
        = riemannZeta s * DirichletCharacter.LFunction χ s
          - s * DirichletCharacter.LFunction χ 1 / (s - 1)) :
    ∀ s : ℂ, 1/2 < s.re →
      (s - 1) * (s * (∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ) ^ (-(s + 1))))
        = riemannZeta₁ s * DirichletCharacter.LFunction χ s
          - s * DirichletCharacter.LFunction χ 1 := by
  set U : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re} with hU
  set Φ : ℂ → ℂ := fun z : ℂ => ∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ) ^ (-(z + 1)) with hΦ
  have hΦan : AnalyticOnNhd ℂ Φ U := fun s hs => analyticAt_efunIntegral_aux χ hE hs
  have hζ₁an : AnalyticOnNhd ℂ riemannZeta₁ U :=
    (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ).mono
      (Set.subset_univ _)
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      isOpen_univ).mono (Set.subset_univ _)
  have hGan : AnalyticOnNhd ℂ
      (fun s : ℂ => (s - 1) * (s * Φ s) - riemannZeta₁ s * DirichletCharacter.LFunction χ s
        + s * DirichletCharacter.LFunction χ 1) U := by
    have h1 : AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * (s * Φ s)) U :=
      ((analyticOnNhd_id.sub analyticOnNhd_const).mul (analyticOnNhd_id.mul hΦan))
    have h2 : AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta₁ s * DirichletCharacter.LFunction χ s) U :=
      hζ₁an.mul hLan
    have h3 : AnalyticOnNhd ℂ (fun s : ℂ => s * DirichletCharacter.LFunction χ 1) U :=
      analyticOnNhd_id.mul analyticOnNhd_const
    exact (h1.sub h2).add h3
  have hvan : ∀ s ∈ U, (s - 1) * (s * Φ s) - riemannZeta₁ s * DirichletCharacter.LFunction χ s
        + s * DirichletCharacter.LFunction χ 1 = 0 := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hGan
      (analyticOnNhd_const (v := (0:ℂ))) (convex_halfSpace_re_gt (1/2)).isPreconnected
      (z₀ := (2:ℂ)) (by norm_num [U]) ?_
    have hopen : IsOpen {s : ℂ | (1:ℝ) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : {s : ℂ | (1:ℝ) < s.re} ∈ 𝓝 (2:ℂ) := hopen.mem_nhds (by norm_num)
    filter_upwards [hmem] with s hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hζ : (s - 1) * riemannZeta s = riemannZeta₁ s := by
      rw [riemannZeta_eq_inv_sub_mul hs1]
      field_simp
    have hid := hId s hs
    have hA : (s - 1) ≠ 0 := sub_ne_zero.mpr hs1
    rw [hid, ← hζ]
    field_simp
    ring
  intro s hs
  have hΦβ : (s - 1) * (s * (∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ) ^ (-(s + 1))))
      - riemannZeta₁ s * DirichletCharacter.LFunction χ s
      + s * DirichletCharacter.LFunction χ 1 = 0 := hvan s hs
  linear_combination hΦβ

theorem efunContinuation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : ℝ}
    (hE : ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ x‖ ≤ K * Real.sqrt x)
    (hId : ∀ s : ℂ, 1 < s.re → s * (∫ x in Set.Ioi (1:ℝ), Work.LinnikAreas.Efun χ x * (x:ℂ) ^ (-(s + 1)))
        = riemannZeta s * DirichletCharacter.LFunction χ s
          - s * DirichletCharacter.LFunction χ 1 / (s - 1))
    {β : ℝ} (hβ : 1/2 < β) (hβ1 : β < 1) (hL : DirichletCharacter.LFunction χ (β:ℂ) = 0) :
    (∫ x in Set.Ioi (1:ℝ), Work.LinnikAreas.Efun χ x * (x:ℂ) ^ (-(((1 + β : ℝ)) : ℂ)))
      = DirichletCharacter.LFunction χ 1 / (1 - β) := by
  -- the Abel identity, extended to the strip `1/2 < Re s < 1`
  have hhalf := efunAbel_halfPlane χ hχ hE hId
  have hβU : (1/2 : ℝ) < (β:ℂ).re := by simpa using hβ
  have key := hhalf (β:ℂ) hβU
  -- the term `ζ₁(β)L(β,χ)` vanishes because `L(β,χ) = 0`
  rw [hL, mul_zero, zero_sub] at key
  have hβne : (β:ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    linarith
  have hβm1 : (β:ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (ne_of_lt hβ1)
  have h1mβ : (1:ℂ) - (β:ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (ne_of_gt hβ1)
  have step1 : (β:ℂ) * (∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ) ^ (-((β:ℂ) + 1)))
      = -((β:ℂ) * DirichletCharacter.LFunction χ 1) / ((β:ℂ) - 1) := by
    rw [eq_div_iff hβm1]
    linear_combination key
  have step2 : -((β:ℂ) * DirichletCharacter.LFunction χ 1) / ((β:ℂ) - 1)
      = (β:ℂ) * (DirichletCharacter.LFunction χ 1 / (1 - (β:ℂ))) := by
    rw [show ((β:ℂ) - 1) = -((1:ℂ) - (β:ℂ)) by ring, neg_div_neg_eq]
    field_simp
  have hfinal : (∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ) ^ (-((β:ℂ) + 1)))
      = DirichletCharacter.LFunction χ 1 / (1 - (β:ℂ)) :=
    mul_left_cancel₀ hβne (step1.trans step2)
  rw [show (-(((1 + β : ℝ)) : ℂ)) = -((β:ℂ) + 1) by
    rw [Complex.ofReal_add, Complex.ofReal_one]; ring]
  exact hfinal

end

end Work.LinnikAreas
