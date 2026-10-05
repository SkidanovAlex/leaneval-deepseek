import Mathlib
import Submission.Work.RPB.B1a.HalfBallDefs
import Submission.Work.RPB.B1a.Defs
import Submission.Work.RPB.B1a.aux_loop_bound
import Submission.Work.RPB.B1a.exists_diam_le_of_connected_cover_frontier
import Submission.Work.RPB.Port.Drive.curve_straightening
import Submission.Work.RPB.Port.Drive.curve_localSep
import Submission.Work.RPB.Port.Drive.signed_jump_at_point
import Submission.Work.RPB.Port.Drive.CurveRatioAux
import Submission.Work.RPB1a.exists_smooth_embedding_descend
import Submission.Work.RPB.B1a.norm_straightenMap_sub_le
import Submission.Work.RPB.B1a.normal_points_different_component

/-!
# The local identification of a smooth loop with the straightened half-balls

For a smooth immersed loop `v : ℝ → ℂ` (`Work.RPB.B1a.IsSmoothLoop`) and a parameter `t₀`, the
straightening chart `straightenMap v t₀ p = v (t₀ + p.1) + p.2 * (I * deriv v t₀)` is a local
diffeomorphism at `0` whose image of the two upper/lower halves of a small ball, cut by the
conditions `‖straightenMap v t₀ p - v t₀‖ < ρ` and `‖p‖ < 2ρ/‖deriv v t₀‖`, are exactly the two
local sides of the loop near `v t₀`.

Consequently any connected open set `D` whose boundary is `range v` agrees, inside the ball of
radius `ρ` about `v t₀`, with one of those two half-ball images.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Complex Set Metric Filter
open scoped ContDiff Real Topology

noncomputable section

namespace Work.RPB.B1a

/-! ## The linearisation of the straightening chart -/

/-- The derivative of `straightenMap v t₀` at `0`, as a real-linear map `ℝ × ℝ → ℂ`. -/
noncomputable def straightenCLM (w : ℂ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℝ w).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Complex.I * w)

lemma straightenCLM_apply (w : ℂ) (p : ℝ × ℝ) :
    straightenCLM w p = (p.1 : ℂ) * w + (p.2 : ℂ) * (Complex.I * w) := by
  simp [straightenCLM, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- `straightenCLM w` vanishes only at the origin when `w ≠ 0`. -/
lemma straightenCLM_eq_zero (w : ℂ) (hw : w ≠ 0) {p : ℝ × ℝ} (hp : straightenCLM w p = 0) :
    p = 0 := by
  have h0 : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * w = 0 := by
    calc ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * w
        = (p.1 : ℂ) * w + (p.2 : ℂ) * (Complex.I * w) := by ring
      _ = straightenCLM w p := (straightenCLM_apply w p).symm
      _ = 0 := hp
  rcases mul_eq_zero.mp h0 with h | h
  · have h1 : p.1 = 0 := by
      have := congrArg Complex.re h; simpa using this
    have h2 : p.2 = 0 := by
      have := congrArg Complex.im h; simpa using this
    exact Prod.ext h1 h2
  · exact absurd h hw

/-- The derivative of the chart as a continuous linear equivalence (invertible because
`w ≠ 0`). -/
noncomputable def straightenEquiv (w : ℂ) (hw : w ≠ 0) : (ℝ × ℝ) ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.ofBijective (straightenCLM w)
    (by
      have hinj : Function.Injective (straightenCLM w) := by
        intro p q hpq
        have h0 : straightenCLM w (p - q) = 0 := by rw [map_sub, hpq, sub_self]
        have := straightenCLM_eq_zero w hw h0
        exact sub_eq_zero.mp this
      exact LinearMap.ker_eq_bot.mpr hinj)
    (by
      rw [LinearMap.range_eq_top]
      intro z
      refine ⟨Complex.equivRealProdCLM (z * w⁻¹), ?_⟩
      change straightenCLM w (Complex.equivRealProdCLM (z * w⁻¹)) = z
      rw [straightenCLM_apply]
      have h : ((Complex.equivRealProdCLM (z * w⁻¹)).1 : ℂ) +
          ((Complex.equivRealProdCLM (z * w⁻¹)).2 : ℂ) * Complex.I = z * w⁻¹ := by
        apply Complex.ext <;> simp
      calc ↑(Complex.equivRealProdCLM (z * w⁻¹)).1 * w
              + ↑(Complex.equivRealProdCLM (z * w⁻¹)).2 * (Complex.I * w)
          = (↑(Complex.equivRealProdCLM (z * w⁻¹)).1
              + ↑(Complex.equivRealProdCLM (z * w⁻¹)).2 * Complex.I) * w := by ring
        _ = (z * w⁻¹) * w := by rw [h]
        _ = z := by rw [mul_assoc, inv_mul_cancel₀ hw, mul_one])

lemma straightenEquiv_coe (w : ℂ) (hw : w ≠ 0) :
    ((straightenEquiv w hw : (ℝ × ℝ) →L[ℝ] ℂ)) = straightenCLM w := rfl

lemma straightenMap_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (t₀ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (straightenMap v t₀) := by
  rw [show straightenMap v t₀
      = fun p : ℝ × ℝ => v (t₀ + p.1) + (p.2 : ℂ) * (Complex.I * deriv v t₀) from rfl]
  exact (hv.comp (contDiff_const.add contDiff_fst)).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)

lemma hasFDerivAt_straightenMap (v : ℝ → ℂ) (hv : ContDiff ℝ 1 v) (t₀ : ℝ)
    (hw : deriv v t₀ ≠ 0) :
    HasFDerivAt (straightenMap v t₀)
      ((straightenEquiv (deriv v t₀) hw : (ℝ × ℝ) →L[ℝ] ℂ)) 0 := by
  have hv' : HasDerivAt v (deriv v t₀) t₀ :=
    (hv.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hGderiv : HasDerivAt (fun s : ℝ => v (t₀ + s)) (deriv v t₀) 0 :=
    HasDerivAt.comp_const_add t₀ 0 (by simpa using hv')
  have hGfd : HasFDerivAt (fun s : ℝ => v (t₀ + s))
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv v t₀)) 0 := hGderiv.hasFDerivAt
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => v (t₀ + p.1))
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv v t₀)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) 0 := by
    have h := HasFDerivAt.comp (𝕜 := ℝ) (x := (0 : ℝ × ℝ))
      (f := (fun p : ℝ × ℝ => p.1)) (g := (fun s : ℝ => v (t₀ + s))) hGfd
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
    simpa [Function.comp_def] using h
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => (p.2 : ℂ) * (Complex.I * deriv v t₀))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Complex.I * deriv v t₀)) 0 := by
    have hfun : (⇑((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Complex.I * deriv v t₀)) : ℝ × ℝ → ℂ)
        = fun p : ℝ × ℝ => (p.2 : ℂ) * (Complex.I * deriv v t₀) := by
      ext p
      simp [ContinuousLinearMap.smulRight_apply]
    rw [← hfun]
    exact (ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)
        (Complex.I * deriv v t₀)).hasFDerivAt
  have hsum := h1.add h2
  have hfun : (fun p : ℝ × ℝ => v (t₀ + p.1))
      + (fun p : ℝ × ℝ => (p.2 : ℂ) * (Complex.I * deriv v t₀)) = straightenMap v t₀ := by
    ext p; simp [straightenMap]
  have hder : ((ContinuousLinearMap.toSpanSingleton ℝ (deriv v t₀)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Complex.I * deriv v t₀))
      = ((straightenEquiv (deriv v t₀) hw : (ℝ × ℝ) →L[ℝ] ℂ)) := by
    rw [straightenEquiv_coe]; rfl
  rw [← hfun, ← hder]
  exact hsum

/-- **The straightening chart is a local homeomorphism at the origin.** -/
lemma exists_straighten_chart (v : ℝ → ℂ) (hvd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (t₀ : ℝ) (hw : deriv v t₀ ≠ 0) :
    ∃ (r : ℝ) (Ψ : OpenPartialHomeomorph (ℝ × ℝ) ℂ), 0 < r ∧
      (∀ z ∈ Metric.ball (0 : ℝ × ℝ) r, z ∈ Ψ.source) ∧
      (∀ z : ℝ × ℝ, Ψ z = straightenMap v t₀ z) := by
  have hv1 : ContDiff ℝ 1 v := hvd.of_le (by norm_num)
  have hdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (straightenMap v t₀) :=
    straightenMap_contDiff v hvd t₀
  have hderiv := hasFDerivAt_straightenMap v hv1 t₀ hw
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let Ψ : OpenPartialHomeomorph (ℝ × ℝ) ℂ :=
    ContDiffAt.toOpenPartialHomeomorph (straightenMap v t₀) hdiff.contDiffAt hderiv hn
  have hcoe : ⇑Ψ = straightenMap v t₀ := ContDiffAt.toOpenPartialHomeomorph_coe _ _ _
  have h0mem : (0 : ℝ × ℝ) ∈ Ψ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Ψ.open_source.mem_nhds h0mem)
  exact ⟨r, Ψ, hr, fun z hz => hball hz, fun z => by rw [hcoe]⟩

/-! ## Membership in the half-balls -/

lemma mem_halfBallUp_iff {v : ℝ → ℂ} {t₀ ρ : ℝ} {p : ℝ × ℝ} :
    p ∈ halfBallUp (fun x => v (t₀ + x) - v t₀) (deriv v t₀) ρ ↔
      0 < p.2 ∧ straightenMap v t₀ p ∈ Metric.ball (v t₀) ρ ∧
        p ∈ Metric.ball (0 : ℝ × ℝ) (2 * ρ / ‖deriv v t₀‖) := by
  have hEq : ∀ p : ℝ × ℝ,
      (v (t₀ + p.1) - v t₀) + (p.2 : ℂ) * (Complex.I * deriv v t₀)
        = straightenMap v t₀ p - v t₀ := by
    intro p; rw [straightenMap]; ring
  simp only [halfBallUp, Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm,
    dist_zero_right, hEq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

lemma mem_halfBallDn_iff {v : ℝ → ℂ} {t₀ ρ : ℝ} {p : ℝ × ℝ} :
    p ∈ halfBallDn (fun x => v (t₀ + x) - v t₀) (deriv v t₀) ρ ↔
      p.2 < 0 ∧ straightenMap v t₀ p ∈ Metric.ball (v t₀) ρ ∧
        p ∈ Metric.ball (0 : ℝ × ℝ) (2 * ρ / ‖deriv v t₀‖) := by
  have hEq : ∀ p : ℝ × ℝ,
      (v (t₀ + p.1) - v t₀) + (p.2 : ℂ) * (Complex.I * deriv v t₀)
        = straightenMap v t₀ p - v t₀ := by
    intro p; rw [straightenMap]; ring
  simp only [halfBallDn, Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm,
    dist_zero_right, hEq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-! ## Quantitative estimates for the chart -/

/-- The norm of `(a + b*I) * w` is `‖w‖` times the Euclidean norm of `(a,b)`. -/
lemma norm_add_mul_I_mul (a b : ℝ) (w : ℂ) :
    ‖((a : ℂ) + (b : ℂ) * Complex.I) * w‖
      = Real.sqrt (a ^ 2 + b ^ 2) * ‖w‖ := by
  rw [norm_mul, norm_add_mul_I]

/-- The Euclidean norm of `(p.1, p.2)` dominates the product norm of `p`. -/
lemma norm_le_sqrt (p : ℝ × ℝ) : ‖p‖ ≤ Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg p.2])
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg p.1])

/-- The chart's linearisation error bound, `Δ = ‖deriv v t₀‖ / 2`: if the chart takes equal values
at `p` and `q`, and both coordinates are small, then `p = q`. -/
lemma straightenMap_injOn (v : ℝ → ℂ) (hv : ContDiff ℝ 1 v) (t₀ : ℝ) {δ : ℝ}
    (hw : deriv v t₀ ≠ 0)
    (hΔ : ∀ s : ℝ, |s| ≤ δ → ‖deriv v (t₀ + s) - deriv v t₀‖ ≤ ‖deriv v t₀‖ / 2)
    {p q : ℝ × ℝ} (hp : |p.1| ≤ δ) (hq : |q.1| ≤ δ)
    (hpq : straightenMap v t₀ p = straightenMap v t₀ q) : p = q := by
  have h := norm_straightenMap_sub_le v hv t₀ hΔ hp hq
  have hE : straightenMap v t₀ p - straightenMap v t₀ q
      - (((p.1 : ℝ) - q.1 : ℝ) + ((p.2 : ℝ) - q.2 : ℝ) * Complex.I) * deriv v t₀
      = -((((p.1 : ℝ) - q.1 : ℝ) + ((p.2 : ℝ) - q.2 : ℝ) * Complex.I) * deriv v t₀) := by
    rw [hpq]; ring
  rw [hE, norm_neg, norm_mul, norm_add_mul_I] at h
  have hwpos : 0 < ‖deriv v t₀‖ := norm_pos_iff.mpr hw
  have h' : Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) ≤ |p.1 - q.1| / 2 := by
    have h3 : Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) * ‖deriv v t₀‖
        ≤ (|p.1 - q.1| / 2) * ‖deriv v t₀‖ := by
      nlinarith [h]
    exact (mul_le_mul_iff_of_pos_right hwpos).mp h3
  have hsq : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ (|p.1 - q.1| / 2) ^ 2 := by
    have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h' 2
    rwa [Real.sq_sqrt (by positivity)] at h4
  have ha : (p.1 - q.1) ^ 2 = 0 := by
    nlinarith [hsq, sq_abs (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  have hb : (p.2 - q.2) ^ 2 = 0 := by
    nlinarith [hsq, sq_abs (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  exact Prod.ext (sub_eq_zero.mp (sq_eq_zero_iff.mp ha)) (sub_eq_zero.mp (sq_eq_zero_iff.mp hb))

/-- The same linearisation bound, used as a *lower* bound for the chart: on the region where the
derivative of `v` is `‖deriv v t₀‖ / 2`-close to `deriv v t₀`,
`(‖deriv v t₀‖ / 2) ‖p‖ ≤ ‖straightenMap v t₀ p - v t₀‖`. -/
lemma norm_straightenMap_sub_ge (v : ℝ → ℂ) (hv : ContDiff ℝ 1 v) (t₀ : ℝ) {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hΔ : ∀ s : ℝ, |s| ≤ δ → ‖deriv v (t₀ + s) - deriv v t₀‖ ≤ ‖deriv v t₀‖ / 2)
    {p : ℝ × ℝ} (hp : |p.1| ≤ δ) :
    (‖deriv v t₀‖ / 2) * ‖p‖ ≤ ‖straightenMap v t₀ p - v t₀‖ := by
  have hq : |((0 : ℝ × ℝ).1)| ≤ δ := by simpa using hδ0
  have h := norm_straightenMap_sub_le v hv t₀ hΔ hp hq
  have h0 : straightenMap v t₀ 0 = v t₀ := by simp [straightenMap]
  rw [h0] at h
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at h
  have hA : ‖(((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I) * deriv v t₀‖
      ≤ ‖straightenMap v t₀ p - v t₀‖ + |p.1| * (‖deriv v t₀‖ / 2) := by
    have h1 : ‖(((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I) * deriv v t₀‖
        = ‖(straightenMap v t₀ p - v t₀)
            - (straightenMap v t₀ p - v t₀
              - (((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I) * deriv v t₀)‖ := by
      congr 1; ring
    rw [h1]
    have := norm_sub_le (straightenMap v t₀ p - v t₀)
      (straightenMap v t₀ p - v t₀
        - (((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I) * deriv v t₀)
    linarith
  rw [norm_mul, norm_add_mul_I] at hA
  have hz : ‖p‖ ≤ Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := norm_le_sqrt p
  have hal : |p.1| ≤ Real.sqrt (p.1 ^ 2 + p.2 ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg p.2])
  have h2 : Real.sqrt (p.1 ^ 2 + p.2 ^ 2) * (‖deriv v t₀‖ / 2)
      ≤ ‖straightenMap v t₀ p - v t₀‖ := by
    nlinarith [hA, hal, norm_nonneg (deriv v t₀),
      norm_nonneg (straightenMap v t₀ p - v t₀)]
  have h3 : ‖p‖ * (‖deriv v t₀‖ / 2) ≤ Real.sqrt (p.1 ^ 2 + p.2 ^ 2) * (‖deriv v t₀‖ / 2) :=
    mul_le_mul_of_nonneg_right hz (by positivity)
  calc (‖deriv v t₀‖ / 2) * ‖p‖ = ‖p‖ * (‖deriv v t₀‖ / 2) := by ring
    _ ≤ Real.sqrt (p.1 ^ 2 + p.2 ^ 2) * (‖deriv v t₀‖ / 2) := h3
    _ ≤ ‖straightenMap v t₀ p - v t₀‖ := h2

/-! ## The main theorem -/

theorem local_identification_of_smooth_loop (v : ℝ → ℂ) (hv : Work.RPB.B1a.IsSmoothLoop v)
    (t₀ : ℝ) :
    ∃ ρ₁, 0 < ρ₁ ∧ ∀ ρ, 0 < ρ → ρ ≤ ρ₁ → ∀ D : Set ℂ, IsOpen D → IsConnected D →
      closure D \ interior D = Set.range v →
      (D ∩ Metric.ball (v t₀) ρ =
          Work.RPB.B1a.straightenMap v t₀ ''
            (Work.RPB.B1a.halfBallUp (fun x => v (t₀ + x) - v t₀) (deriv v t₀) ρ) ∨
        D ∩ Metric.ball (v t₀) ρ =
          Work.RPB.B1a.straightenMap v t₀ ''
            (Work.RPB.B1a.halfBallDn (fun x => v (t₀ + x) - v t₀) (deriv v t₀) ρ)) := by
  obtain ⟨hvd, hper, hinj, himm⟩ := hv
  have hw : deriv v t₀ ≠ 0 := himm t₀
  have hv1 : ContDiff ℝ 1 v := hvd.of_le (by norm_num)
  have hdc : Continuous (deriv v) := hvd.continuous_deriv (by norm_num)
  -- ## A radius on which `deriv v (t₀ + ·)` is `‖deriv v t₀‖/2`-close to `deriv v t₀`.
  have hhalf : (0 : ℝ) < ‖deriv v t₀‖ / 2 := by positivity
  have htend : Tendsto (fun s : ℝ => deriv v (t₀ + s)) (𝓝 0) (𝓝 (deriv v t₀)) := by
    have h1 : Tendsto (fun s : ℝ => t₀ + s) (𝓝 0) (𝓝 t₀) := by
      simpa using (tendsto_const_nhds (x := t₀)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact hdc.continuousAt.tendsto.comp h1
  have hev : ∀ᶠ s : ℝ in 𝓝 0,
      ‖deriv v (t₀ + s) - deriv v t₀‖ < ‖deriv v t₀‖ / 2 :=
    (htend.eventually (Metric.ball_mem_nhds (deriv v t₀) hhalf)).mono (fun s hs => by
      rw [dist_eq_norm] at hs; exact hs)
  obtain ⟨r₀, hr₀pos, hr₀sub⟩ := Metric.mem_nhds_iff.mp hev
  obtain ⟨δ, hδpos, hΔ⟩ : ∃ δ > 0, ∀ s : ℝ, |s| ≤ δ →
      ‖deriv v (t₀ + s) - deriv v t₀‖ ≤ ‖deriv v t₀‖ / 2 := by
    refine ⟨r₀ / 2, by positivity, fun s hs => le_of_lt (hr₀sub ?_)⟩
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    linarith
  -- ## The global lower Lipschitz bound for the loop.
  obtain ⟨c, hcpos, hc⟩ := loop_lower_bound_aux v hv1 hper hinj himm
  -- ## The straightening chart.
  obtain ⟨r, Ψ, hrpos, hΨsrc, hΨcoe⟩ := exists_straighten_chart v hvd t₀ hw
  have hΨ0 : Ψ 0 = v t₀ := by rw [hΨcoe]; simp [straightenMap]
  have h0src : (0 : ℝ × ℝ) ∈ Ψ.source :=
    hΨsrc 0 (by rw [Metric.mem_ball, dist_zero_right]; simpa using hrpos)
  have hv0tgt : v t₀ ∈ Ψ.target := by
    rw [← hΨ0]; exact Ψ.map_source h0src
  obtain ⟨σ₁, hσ₁pos, hσ₁sub⟩ :=
    Metric.mem_nhds_iff.mp (Ψ.open_target.mem_nhds hv0tgt)
  have hsymm0 : Ψ.symm (v t₀) = 0 := by
    rw [← hΨ0]; exact Ψ.left_inv h0src
  have hcont_symm : ContinuousAt (⇑Ψ.symm) (v t₀) :=
    Ψ.continuousOn_symm.continuousAt (Ψ.open_target.mem_nhds hv0tgt)
  obtain ⟨σ₂, hσ₂pos, hσ₂sub⟩ : ∃ σ₂ > 0,
      ∀ z ∈ Metric.ball (v t₀) σ₂, Ψ.symm z ∈ Metric.ball (0 : ℝ × ℝ) δ := by
    have hpre : (⇑Ψ.symm) ⁻¹' Metric.ball (0 : ℝ × ℝ) δ ∈ 𝓝 (v t₀) := by
      have hmem : Metric.ball (0 : ℝ × ℝ) δ ∈ 𝓝 (Ψ.symm (v t₀)) := by
        rw [hsymm0]; exact Metric.ball_mem_nhds 0 hδpos
      exact hcont_symm.preimage_mem_nhds hmem
    obtain ⟨σ, hσpos, hσsub⟩ := Metric.mem_nhds_iff.mp hpre
    exact ⟨σ, hσpos, fun z hz => hσsub hz⟩
  -- ## The two-sided decomposition of the complement.
  obtain ⟨ins, out, hio, hjo, hpc₁, hpc₂, hb₁, hb₂, hne₁, hne₂, hicov, hidisj, hifr, hjfr⟩ :=
    exists_twoSidedDecomposition v ⟨hvd, hper, hinj, himm⟩
  -- ## The signed jump radius.
  obtain ⟨δJ, hδJpos, hδJ⟩ := normal_points_different_component v ⟨hvd, hper, hinj, himm⟩ t₀
  -- ## The radius `ρ₁`.
  refine ⟨min (min (min (min (δ * ‖deriv v t₀‖ / 2) (δ * c / 5)) σ₁) σ₂)
      (‖deriv v t₀‖ * δJ), ?_, ?_⟩
  · refine lt_min (lt_min (lt_min (lt_min ?_ ?_) hσ₁pos) hσ₂pos) ?_
    · exact div_pos (mul_pos hδpos (norm_pos_iff.mpr hw)) (by norm_num)
    · exact div_pos (mul_pos hδpos hcpos) (by norm_num)
    · exact mul_pos (norm_pos_iff.mpr hw) hδJpos
  intro ρ hρ hρle D hDo hDc hDfr
  -- extract the smallness conditions
  have hρ1 : ρ ≤ δ * ‖deriv v t₀‖ / 2 := le_trans hρle (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hρ2 : ρ ≤ δ * c / 5 := le_trans hρle (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hρ3 : ρ ≤ σ₁ := le_trans hρle (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hρ4 : ρ ≤ σ₂ := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ5 : ρ ≤ ‖deriv v t₀‖ * δJ := le_trans hρle (min_le_right _ _)
  -- ## Notation.
  set R : ℝ := 2 * ρ / ‖deriv v t₀‖ with hRdef
  set B : Set (ℝ × ℝ) := Metric.ball (0 : ℝ × ℝ) R with hBdef
  set U : Set ℂ := Metric.ball (v t₀) ρ with hUdef
  set Φ : (ℝ × ℝ) → ℂ := straightenMap v t₀ with hΦdef
  set HBU : Set (ℝ × ℝ) :=
    halfBallUp (fun x => v (t₀ + x) - v t₀) (deriv v t₀) ρ with hHBUdef
  set HBD : Set (ℝ × ℝ) :=
    halfBallDn (fun x => v (t₀ + x) - v t₀) (deriv v t₀) ρ with hHBDdef
  set U₁ : Set ℂ := Φ '' HBU with hU₁def
  set U₂ : Set ℂ := Φ '' HBD with hU₂def
  set Hp : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.2} ∩ B with hHpdef
  set Hm : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 < 0} ∩ B with hHmdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact div_pos (by linarith) (norm_pos_iff.mpr hw)
  have hRδ : R ≤ δ := by
    rw [hRdef, div_le_iff₀ (norm_pos_iff.mpr hw)]
    nlinarith [hρ1, norm_pos_iff.mpr hw]
  have hBmem : ∀ p : ℝ × ℝ, p ∈ B ↔ |p.1| < R ∧ |p.2| < R := by
    intro p
    rw [hBdef, Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs, max_lt_iff]
  have hBδ : ∀ p ∈ B, |p.1| ≤ δ := by
    intro p hp
    have hp1 : |p.1| < R := ((hBmem p).mp hp).1
    linarith [hp1, hRδ]
  -- ## The three fundamental properties of the chart.
  have hinj_chart : ∀ p ∈ B, ∀ q ∈ B, Φ p = Φ q → p = q := by
    intro p hp q hq hpq
    exact straightenMap_injOn v hv1 t₀ hw hΔ (hBδ p hp) (hBδ q hq) hpq
  have hcover : U ⊆ Φ '' B := by
    intro z hz
    have hztgt : z ∈ Ψ.target := hσ₁sub (Metric.ball_subset_ball hρ3 hz)
    refine ⟨Ψ.symm z, ?_, ?_⟩
    · rw [hBmem]
      have hz2 : z ∈ Metric.ball (v t₀) σ₂ := Metric.ball_subset_ball hρ4 hz
      have h1 := hσ₂sub z hz2
      have h2 : ‖Ψ.symm z‖ < δ := by
        have h3 := Metric.mem_ball.mp h1
        rwa [dist_zero_right] at h3
      have h4 : |(Ψ.symm z).1| ≤ δ := by
        have h5 : |(Ψ.symm z).1| ≤ ‖Ψ.symm z‖ := by
          rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _
        linarith
      have hzeq : straightenMap v t₀ (Ψ.symm z) = z := by
        have h := Ψ.right_inv hztgt
        rw [hΨcoe (Ψ.symm z)] at h
        exact h
      have hge := norm_straightenMap_sub_ge v hv1 t₀ hδpos.le hΔ h4
      rw [hzeq] at hge
      have hlt : ‖z - v t₀‖ < ρ := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
      have hpnorm : ‖Ψ.symm z‖ < R := by
        rw [hRdef, lt_div_iff₀ (norm_pos_iff.mpr hw)]
        nlinarith [hge, hlt, norm_pos_iff.mpr hw]
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff] at hpnorm
      exact ⟨hpnorm.1, hpnorm.2⟩
    · simpa [hΦdef, hΨcoe] using Ψ.right_inv hztgt
  have hoffaxis : ∀ p ∈ B, Φ p ∈ Set.range v → p.2 = 0 := by
    intro p hp hpmem
    obtain ⟨τ, hτ⟩ := hpmem
    obtain ⟨h, hhle, m, hm⟩ := exists_abs_le_pi_representative t₀ τ
    have hper_m : v ((t₀ + h) + (m : ℝ) * (2 * Real.pi)) = v (t₀ + h) := by
      have h1 := (Function.Periodic.int_mul hper m) (t₀ + h)
      simpa using h1
    have hτ' : τ = (t₀ + h) + (m : ℝ) * (2 * Real.pi) := hm
    have hpeq : v (t₀ + h) = Φ p := by
      have h1 : v τ = v (t₀ + h) := by
        rw [hτ']
        simpa using (Function.Periodic.int_mul hper m) (t₀ + h)
      exact h1.symm.trans hτ
    have hbnd : ‖v (t₀ + h) - v t₀‖ ≤ 5 * ρ := by
      rw [hpeq]
      have herr : ‖(v (t₀ + p.1) - v t₀) - (p.1 : ℂ) * deriv v t₀‖
          ≤ |p.1| * (‖deriv v t₀‖ / 2) := by
        have h1 := norm_straightenMap_sub_le v hv1 t₀ hΔ (hBδ p hp)
          (by have hz : |((0 : ℝ × ℝ).1)| = 0 := by simp
              rw [hz]; exact hδpos.le)
        have h0 : straightenMap v t₀ 0 = v t₀ := by simp [straightenMap]
        rw [h0] at h1
        simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, zero_mul, zero_add] at h1
        have harg : straightenMap v t₀ p - v t₀
              - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * deriv v t₀
            = (v (t₀ + p.1) - v t₀) - (p.1 : ℂ) * deriv v t₀ := by
          simp only [straightenMap]; ring
        rwa [harg] at h1
      have hp1 : |p.1| < R := ((hBmem p).mp hp).1
      have hp2 : |p.2| < R := ((hBmem p).mp hp).2
      have hRW : R * ‖deriv v t₀‖ = 2 * ρ := by rw [hRdef]; field_simp
      have hlin : ‖((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * deriv v t₀‖ ≤ 4 * ρ := by
        rw [norm_add_mul_I_mul]
        have hsqrt : Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ≤ 2 * R := by
          rw [Real.sqrt_le_iff]
          refine ⟨by linarith [hRpos], ?_⟩
          have hs1 : p.1 ^ 2 < R ^ 2 := by
            rw [sq_lt_sq]; rwa [abs_of_nonneg hRpos.le]
          have hs2 : p.2 ^ 2 < R ^ 2 := by
            rw [sq_lt_sq]; rwa [abs_of_nonneg hRpos.le]
          nlinarith [hs1, hs2, hRpos]
        calc Real.sqrt (p.1 ^ 2 + p.2 ^ 2) * ‖deriv v t₀‖
            ≤ (2 * R) * ‖deriv v t₀‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
          _ = 4 * ρ := by
              rw [show (2 * R) * ‖deriv v t₀‖ = 2 * (R * ‖deriv v t₀‖) from by ring, hRW]
              ring
      have herrρ : |p.1| * (‖deriv v t₀‖ / 2) ≤ ρ := by
        have hwpos : 0 < ‖deriv v t₀‖ := norm_pos_iff.mpr hw
        have hlt := mul_lt_mul_of_pos_right hp1 (show (0:ℝ) < ‖deriv v t₀‖ / 2 by linarith)
        have h2 : R * (‖deriv v t₀‖ / 2) = ρ := by nlinarith [hRW]
        linarith [hlt, h2]
      rw [show Φ p - v t₀ = ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * deriv v t₀
          + ((v (t₀ + p.1) - v t₀) - (p.1 : ℂ) * deriv v t₀) from by
        rw [hΦdef]; simp only [straightenMap]; ring]
      calc ‖((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * deriv v t₀
              + ((v (t₀ + p.1) - v t₀) - (p.1 : ℂ) * deriv v t₀)‖
          ≤ ‖((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) * deriv v t₀‖
              + ‖(v (t₀ + p.1) - v t₀) - (p.1 : ℂ) * deriv v t₀‖ := norm_add_le _ _
        _ ≤ 4 * ρ + ρ := add_le_add hlin (le_trans herr herrρ)
        _ = 5 * ρ := by ring
    have hcbound : c * |h| ≤ ‖v (t₀ + h) - v t₀‖ := hc t₀ h hhle
    have hhsmall : |h| ≤ δ := by
      have h5 : c * |h| ≤ 5 * ρ := le_trans hcbound hbnd
      have h6 : 5 * ρ ≤ c * δ := by linarith [hρ2]
      nlinarith [h5, h6, hcpos]
    have hΦq : Φ p = Φ (h, 0) := by
      rw [← hpeq]; simp [hΦdef, straightenMap]
    have hq : p = (h, 0) :=
      straightenMap_injOn v hv1 t₀ hw hΔ (hBδ p hp) (by simpa using hhsmall) hΦq
    rw [hq]
  -- ## Membership in the two pieces.
  have hHBU : HBU = Hp ∩ Φ ⁻¹' U := by
    ext p
    simp only [hHBUdef, mem_halfBallUp_iff, hHpdef, hΦdef, hUdef, hRdef, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  have hHBD : HBD = Hm ∩ Φ ⁻¹' U := by
    ext p
    simp only [hHBDdef, mem_halfBallDn_iff, hHmdef, hΦdef, hUdef, hRdef, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  have hU₁eq : U₁ = Φ '' Hp ∩ U := by
    rw [hU₁def, hHBU, Set.image_inter_preimage]
  have hU₂eq : U₂ = Φ '' Hm ∩ U := by
    rw [hU₂def, hHBD, Set.image_inter_preimage]
  have hU₁U : U₁ ⊆ U := by rw [hU₁eq]; exact Set.inter_subset_right
  have hU₂U : U₂ ⊆ U := by rw [hU₂eq]; exact Set.inter_subset_right
  -- ## The half-plane pieces are open, convex, nonempty.
  have hHpopen : IsOpen Hp := by
    rw [hHpdef, hBdef]
    exact (isOpen_lt continuous_const continuous_snd).inter Metric.isOpen_ball
  have hHmopen : IsOpen Hm := by
    rw [hHmdef, hBdef]
    exact (isOpen_lt continuous_snd continuous_const).inter Metric.isOpen_ball
  have hHpconv : Convex ℝ Hp := by
    rw [hHpdef, hBdef]
    have h : {p : ℝ × ℝ | 0 < p.2} = Set.univ ×ˢ Set.Ioi (0 : ℝ) := by ext p; simp
    rw [h]
    exact (convex_univ.prod (convex_Ioi 0)).inter (convex_ball (0 : ℝ × ℝ) R)
  have hHmconv : Convex ℝ Hm := by
    rw [hHmdef, hBdef]
    have h : {p : ℝ × ℝ | p.2 < 0} = Set.univ ×ˢ Set.Iio (0 : ℝ) := by ext p; simp
    rw [h]
    exact (convex_univ.prod (convex_Iio 0)).inter (convex_ball (0 : ℝ × ℝ) R)
  have hHpne : Hp.Nonempty := by
    refine ⟨(0, R / 2), ?_⟩
    rw [hHpdef]
    refine ⟨by change (0:ℝ) < R / 2; linarith [hRpos], ?_⟩
    rw [hBmem]
    exact ⟨by simpa using hRpos, by rw [abs_of_pos (by positivity : (0:ℝ) < R / 2)]; linarith [hRpos]⟩
  have hHmne : Hm.Nonempty := by
    refine ⟨(0, -R / 2), ?_⟩
    rw [hHmdef]
    refine ⟨by change (-R / 2 : ℝ) < 0; linarith [hRpos], ?_⟩
    rw [hBmem]
    exact ⟨by simpa using hRpos, by rw [abs_of_neg (by linarith : -R/2 < 0)]; linarith [hRpos]⟩
  have hΦcont : Continuous Φ := by
    rw [hΦdef]
    exact (hvd.continuous.comp (continuous_const.add continuous_fst)).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  -- ## The pieces miss the curve.
  have hΦHpKc : Φ '' Hp ⊆ (Set.range v)ᶜ := by
    rintro z ⟨p, hp, rfl⟩ hz
    rw [hHpdef] at hp
    exact absurd (hoffaxis p hp.2 hz) (ne_of_gt hp.1)
  have hΦHmKc : Φ '' Hm ⊆ (Set.range v)ᶜ := by
    rintro z ⟨p, hp, rfl⟩ hz
    rw [hHmdef] at hp
    exact absurd (hoffaxis p hp.2 hz) (ne_of_lt hp.1)
  have hU₁Kc : U₁ ⊆ (Set.range v)ᶜ := by
    intro z hz; rw [hU₁eq] at hz; exact hΦHpKc hz.1
  have hU₂Kc : U₂ ⊆ (Set.range v)ᶜ := by
    intro z hz; rw [hU₂eq] at hz; exact hΦHmKc hz.1
  -- ## The pieces are disjoint and cover `U \ range v`.
  have hdisj : Disjoint U₁ U₂ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [hU₁eq] at hz1
    rw [hU₂eq] at hz2
    obtain ⟨p, hp, hpe⟩ := hz1.1
    obtain ⟨q, hq, hqe⟩ := hz2.1
    rw [hHpdef] at hp
    rw [hHmdef] at hq
    have hpq : p = q := hinj_chart p hp.2 q hq.2 (hpe.trans hqe.symm)
    have hpq2 : p.2 = q.2 := congrArg Prod.snd hpq
    exact absurd (show (0:ℝ) < p.2 from hp.1)
      (by rw [hpq2]; exact not_lt.mpr hq.1.le)
  have hunion : U₁ ∪ U₂ = U \ Set.range v := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z (hz | hz)
      · exact ⟨hU₁U hz, hU₁Kc hz⟩
      · exact ⟨hU₂U hz, hU₂Kc hz⟩
    · rintro z ⟨hzU, hzK⟩
      obtain ⟨p, hpB, hpe⟩ := hcover hzU
      have hp2 : p.2 ≠ 0 := by
        intro h0
        refine hzK ?_
        rw [← hpe]
        exact ⟨t₀ + p.1, by simp [hΦdef, straightenMap, h0]⟩
      rw [hU₁eq, hU₂eq, ← Set.union_inter_distrib_right, ← Set.image_union]
      refine ⟨⟨p, ?_, hpe⟩, hzU⟩
      rcases lt_or_gt_of_ne hp2 with h | h
      · exact Or.inr (by rw [hHmdef]; exact ⟨h, hpB⟩)
      · exact Or.inl (by rw [hHpdef]; exact ⟨h, hpB⟩)
  -- ## The two normal points.
  set ε : ℝ := ρ / (2 * ‖deriv v t₀‖) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεδJ : ε < δJ := by
    rw [hεdef, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * ‖deriv v t₀‖)]
    nlinarith [hρ5, hδJpos, norm_pos_iff.mpr hw]
  have hεR : ε < R := by
    rw [hεdef, hRdef, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * ‖deriv v t₀‖)]
    have hwpos : 0 < ‖deriv v t₀‖ := norm_pos_iff.mpr hw
    have h2 : (2 * ρ / ‖deriv v t₀‖) * (2 * ‖deriv v t₀‖) = 4 * ρ := by field_simp; ring
    linarith [h2, hρ]
  set zp : ℂ := v t₀ + (ε : ℂ) * (Complex.I * deriv v t₀) with hzpdef
  set zm : ℂ := v t₀ - (ε : ℂ) * (Complex.I * deriv v t₀) with hzmdef
  set Cp : Set ℂ := pathComponentIn (Set.range v)ᶜ zp with hCpdef
  set Cm : Set ℂ := pathComponentIn (Set.range v)ᶜ zm with hCmdef
  have hδJε := hδJ ε hεpos hεδJ
  have hzpK : zp ∈ (Set.range v)ᶜ := by rw [hzpdef]; exact hδJε.1
  have hzmK : zm ∈ (Set.range v)ᶜ := by rw [hzmdef]; exact hδJε.2.1
  have hCne : Cp ≠ Cm := by
    rw [hCpdef, hCmdef, hzpdef, hzmdef]
    exact hδJε.2.2
  -- ## The pieces lie in the two path components.
  have hpHp : ((0 : ℝ), ε) ∈ Hp := by
    rw [hHpdef]
    refine ⟨by simpa using hεpos, ?_⟩
    rw [hBmem]
    exact ⟨by simpa using hRpos, by rw [abs_of_pos hεpos]; exact hεR⟩
  have hpHm : ((0 : ℝ), -ε) ∈ Hm := by
    rw [hHmdef]
    refine ⟨by change (-ε : ℝ) < 0; linarith [hεpos], ?_⟩
    rw [hBmem]
    exact ⟨by simpa using hRpos, by rw [abs_of_neg (by linarith : -ε < 0)]; linarith [hεR]⟩
  have hzpeq : Φ ((0 : ℝ), ε) = zp := by simp [hΦdef, straightenMap, hzpdef]
  have hzmeq : Φ ((0 : ℝ), -ε) = zm := by
    have h1 : Φ ((0 : ℝ), -ε) = v t₀ + ((-ε : ℝ) : ℂ) * (Complex.I * deriv v t₀) := by
      simp [hΦdef, straightenMap]
    rw [h1, hzmdef]
    rw [show ((-ε : ℝ) : ℂ) = -(ε : ℂ) by simp]
    ring
  have hpcd : IsPathConnected (Φ '' Hp) := (hHpconv.isPathConnected hHpne).image hΦcont
  have hpcm : IsPathConnected (Φ '' Hm) := (hHmconv.isPathConnected hHmne).image hΦcont
  have hHpC : Φ '' Hp ⊆ Cp := by
    refine hpcd.subset_pathComponentIn ?_ hΦHpKc
    rw [← hzpeq]; exact ⟨_, hpHp, rfl⟩
  have hHmC : Φ '' Hm ⊆ Cm := by
    refine hpcm.subset_pathComponentIn ?_ hΦHmKc
    rw [← hzmeq]; exact ⟨_, hpHm, rfl⟩
  have hU₁C : U₁ ⊆ Cp := fun z hz => hHpC (by rw [hU₁eq] at hz; exact hz.1)
  have hU₂C : U₂ ⊆ Cm := fun z hz => hHmC (by rw [hU₂eq] at hz; exact hz.1)
  -- ## The path components of the complement are `ins` and `out`.
  have hpcKc : ∀ x ∈ (Set.range v)ᶜ,
      pathComponentIn (Set.range v)ᶜ x = ins ∨ pathComponentIn (Set.range v)ᶜ x = out := by
    intro x hx
    have hsub : pathComponentIn (Set.range v)ᶜ x ⊆ ins ∪ out := by
      rw [← hicov]; exact pathComponentIn_subset
    rcases (isPathConnected_pathComponentIn hx).isConnected.isPreconnected.subset_or_subset
      hio hjo hidisj hsub with h | h
    · left
      refine Set.Subset.antisymm h ?_
      exact hpc₁.subset_pathComponentIn (h (mem_pathComponentIn_self hx))
        (by rw [hicov]; exact Set.subset_union_left)
    · right
      refine Set.Subset.antisymm h ?_
      exact hpc₂.subset_pathComponentIn (h (mem_pathComponentIn_self hx))
        (by rw [hicov]; exact Set.subset_union_right)
  -- ## `D` is a connected component of the complement.
  have hDsub : D ⊆ (Set.range v)ᶜ := by
    intro x hxD hxK
    have hxint : x ∈ interior D := by rw [hDo.interior_eq]; exact hxD
    have hxnot : x ∉ interior D := by
      rw [← hDfr] at hxK
      exact hxK.2
    exact hxnot hxint
  have hDne : D.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h1 : (Set.range v).Nonempty := ⟨v t₀, ⟨t₀, rfl⟩⟩
    rw [← hDfr, h] at h1
    simp at h1
  have hfrontD : frontier D = Set.range v := by
    rw [show frontier D = closure D \ interior D from rfl]; exact hDfr
  have hfrontc : (frontier D)ᶜ = interior D ∪ (closure D)ᶜ := by
    rw [show frontier D = closure D \ interior D from rfl]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union]
    tauto
  have hDins : D = ins ∨ D = out := by
    rcases hDc.isPreconnected.subset_or_subset hio hjo hidisj
      (by rw [← hicov]; exact hDsub) with h | h
    · left
      refine Set.Subset.antisymm h ?_
      have hKc : ins ⊆ D ∪ (closure D)ᶜ := by
        intro x hx
        have hxK : x ∈ (Set.range v)ᶜ := by rw [hicov]; exact Or.inl hx
        have hx2 : x ∈ (frontier D)ᶜ := by rw [hfrontD]; exact hxK
        rw [hfrontc, hDo.interior_eq] at hx2
        exact hx2
      rcases hpc₁.isConnected.isPreconnected.subset_or_subset hDo isClosed_closure.isOpen_compl
        (Set.disjoint_left.mpr (fun x hxD hxc => hxc (subset_closure hxD))) hKc with h2 | h2
      · exact h2
      · obtain ⟨x, hx⟩ := hDne
        exact absurd (subset_closure hx) (h2 (h hx))
    · right
      refine Set.Subset.antisymm h ?_
      have hKc : out ⊆ D ∪ (closure D)ᶜ := by
        intro x hx
        have hxK : x ∈ (Set.range v)ᶜ := by rw [hicov]; exact Or.inr hx
        have hx2 : x ∈ (frontier D)ᶜ := by rw [hfrontD]; exact hxK
        rw [hfrontc, hDo.interior_eq] at hx2
        exact hx2
      rcases hpc₂.isConnected.isPreconnected.subset_or_subset hDo isClosed_closure.isOpen_compl
        (Set.disjoint_left.mpr (fun x hxD hxc => hxc (subset_closure hxD))) hKc with h2 | h2
      · exact h2
      · obtain ⟨x, hx⟩ := hDne
        exact absurd (subset_closure hx) (h2 (h hx))
  -- ## Hence `D` is one of the two pieces' components.
  have hDpm : D = Cp ∨ D = Cm := by
    have h1 : Cp = ins ∨ Cp = out := hpcKc zp hzpK
    have h2 : Cm = ins ∨ Cm = out := hpcKc zm hzmK
    rcases hDins with hD | hD
    · rcases h1 with h1 | h1
      · exact Or.inl (hD.trans h1.symm)
      · rcases h2 with h2 | h2
        · exact Or.inr (hD.trans h2.symm)
        · exact absurd (h1.trans h2.symm) hCne
    · rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hCne
        · exact Or.inr (hD.trans h2.symm)
      · exact Or.inl (hD.trans h1.symm)
  -- ## Conclusion.
  rcases hDpm with hD | hD
  · left
    have hD' : D ∩ U = U₁ := by
      refine Set.Subset.antisymm ?_ ?_
      · intro z hz
        have hz12 : z ∈ U₁ ∪ U₂ := by rw [hunion]; exact ⟨hz.2, hDsub hz.1⟩
        rcases hz12 with h | h
        · exact h
        · exfalso
          have hzCm : z ∈ Cm := hU₂C h
          have hzCp : z ∈ Cp := hD ▸ hz.1
          exact hCne ((pathComponentIn_congr hzCp).symm.trans (pathComponentIn_congr hzCm))
      · intro z hz; exact ⟨hD.symm ▸ hU₁C hz, hU₁U hz⟩
    exact hD'
  · right
    have hD' : D ∩ U = U₂ := by
      refine Set.Subset.antisymm ?_ ?_
      · intro z hz
        have hz12 : z ∈ U₁ ∪ U₂ := by rw [hunion]; exact ⟨hz.2, hDsub hz.1⟩
        rcases hz12 with h | h
        · exfalso
          have hzCp : z ∈ Cp := hU₁C h
          have hzCm : z ∈ Cm := hD ▸ hz.1
          exact hCne ((pathComponentIn_congr hzCp).symm.trans (pathComponentIn_congr hzCm))
        · exact h
      · intro z hz; exact ⟨hD.symm ▸ hU₂C hz, hU₂U hz⟩
    exact hD'

end Work.RPB.B1a
