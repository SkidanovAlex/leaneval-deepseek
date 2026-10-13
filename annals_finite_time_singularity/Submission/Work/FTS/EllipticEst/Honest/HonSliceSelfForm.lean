import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.Honest.HonSliceBounds
import Submission.Work.FTS.EllipticEst.Honest.HonAntiderivTendsto
import Submission.Work.FTS.EllipticEst.Honest.HonSelfDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

/-!
## The angular self-form of `L₀` for an honestly smooth slice

`Lzero1 u = -u'' + (tan · u)' - 6u` is the angular part of the elliptic operator of the
straightened Elgindi coordinates.  For a function which is `C^∞` on the *open* interval
`(0, π/2)`, continuous on `[0, π/2]` and vanishes at both endpoints, with `(u'')² σ`
integrable (`σ = sin(2θ)^{-η}`, `η = 99/100`), the pointwise antiderivative identity

  `F' = Lzero1 u · u - (u')² - (1/2) (u/cos)² + 6 u²`,   `F θ = -u'(θ) u(θ) + (1/2) tan θ · u(θ)²`

integrates over `(0, π/2)` to the quadratic form, because `F → 0` at both endpoints and
`Lzero1 u · u` is integrable there.  The endpoint behaviour is not free: the hypothesis
`(u'')² σ ∈ L¹` (with `σ ≥ 1` on `(0,π/2)`) is what forces `u'` to be bounded and hence
`u = O(θ) = O(π/2 - θ)` near the ends.

The file contains, before the target, two private helpers for the integrability of
`Lzero1 u · u`, proved from scratch (the remaining information comes from the shared
modules `HonSliceBounds`, `HonAntiderivTendsto`, `HonSelfDeriv` and
`sliceLimitLeftExists`).
-/

/-! ## Integrability of `Lzero1 u · u` on the open interval -/

/-- The elementary absolute-value bound used for the integrand `Lzero1 u · u`. -/
private lemma abs_neg_add_sub_six_mul (a b c d : ℝ) (hb : 0 ≤ b) :
    |-(a) + b + c - 6 * d| ≤ |a| + b + |c| + 6 * |d| := by
  have h1 : -(a) + b + c - 6 * d = (-a + c) + (b - 6 * d) := by ring
  have h2 : |b - 6 * d| ≤ b + 6 * |d| := by
    calc |b - 6 * d| = |b + -(6 * d)| := by ring_nf
      _ ≤ |b| + |-(6 * d)| := abs_add_le _ _
      _ = b + 6 * |d| := by rw [abs_of_nonneg hb, abs_neg, abs_mul]; norm_num
  rw [h1]
  calc |(-a + c) + (b - 6 * d)| ≤ |-a + c| + |b - 6 * d| := abs_add_le _ _
    _ ≤ (|a| + |c|) + (b + 6 * |d|) := by
        refine add_le_add ?_ h2
        calc |-a + c| ≤ |-a| + |c| := abs_add_le _ _
          _ = |a| + |c| := by rw [abs_neg]
    _ = |a| + b + |c| + 6 * |d| := by ring

/-- **Pointwise domination of `Lzero1 u · u`** by `(u'')² + 8K² + MK` on the open interval,
where `M` bounds `u'` and `K cos θ` bounds `u`.  The only non-elementary input is the
identity `(tan θ · u(θ))' = u(θ)/cos²θ + tan θ · u'(θ)`. -/
private lemma hon_lzero1_pointwise_bound (u : ℝ → ℝ) {M K : ℝ}
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hKu : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ K * Real.cos θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Work.FTS.EllipticEst.Lzero1 u θ * u θ|
      ≤ (deriv (fun t : ℝ => deriv u t) θ) ^ 2 + (8 * K ^ 2 + M * K) := by
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcos : Real.cos θ ≠ 0 := ne_of_gt hcpos
  have hu1 : HasDerivAt u (deriv u θ) θ :=
    (((hsm 1).contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  have htd : deriv (fun s => Real.tan s * u s) θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ := (htan.mul hu1).deriv
  have e : Work.FTS.EllipticEst.Lzero1 u θ * u θ
      = -(deriv (fun t : ℝ => deriv u t) θ * u θ) + (u θ / Real.cos θ) ^ 2
        + (Real.tan θ * deriv u θ * u θ) - 6 * (u θ) ^ 2 := by
    rw [Work.FTS.EllipticEst.Lzero1, htd]
    field_simp
    ring
  have huK : |u θ| ≤ K := by
    calc |u θ| ≤ K * Real.cos θ := hKu θ hθ
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hK0
      _ = K := mul_one K
  have hucK : |u θ / Real.cos θ| ≤ K := by
    rw [abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
    exact hKu θ hθ
  have hA : |deriv (fun t : ℝ => deriv u t) θ * u θ|
      ≤ (deriv (fun t : ℝ => deriv u t) θ) ^ 2 + K ^ 2 := by
    rw [abs_mul]
    have h1 : |deriv (fun t : ℝ => deriv u t) θ| * |u θ|
        ≤ |deriv (fun t : ℝ => deriv u t) θ| * K :=
      mul_le_mul_of_nonneg_left huK (abs_nonneg _)
    have h2 : 2 * (|deriv (fun t : ℝ => deriv u t) θ| * K)
        ≤ (deriv (fun t : ℝ => deriv u t) θ) ^ 2 + K ^ 2 := by
      nlinarith [sq_nonneg (|deriv (fun t : ℝ => deriv u t) θ| - K),
        sq_abs (deriv (fun t : ℝ => deriv u t) θ)]
    nlinarith [h1, h2]
  have hB : (u θ / Real.cos θ) ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs (u θ / Real.cos θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hucK 2
  have hC : |Real.tan θ * deriv u θ * u θ| ≤ M * K := by
    have ht : Real.tan θ * u θ = Real.sin θ * (u θ / Real.cos θ) := by
      rw [Real.tan_eq_sin_div_cos]; field_simp
    rw [show Real.tan θ * deriv u θ * u θ = deriv u θ * (Real.tan θ * u θ) by ring, abs_mul,
      ht, abs_mul]
    have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hu1' : |deriv u θ| ≤ M := hM θ hθ
    calc |deriv u θ| * (|Real.sin θ| * |u θ / Real.cos θ|)
        ≤ M * (1 * K) := by
          refine mul_le_mul hu1' ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hM0
          exact mul_le_mul hs hucK (abs_nonneg _) (by norm_num)
      _ = M * K := by ring
  have hDsq : (u θ) ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs (u θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) huK 2
  calc |Work.FTS.EllipticEst.Lzero1 u θ * u θ|
      = |-(deriv (fun t : ℝ => deriv u t) θ * u θ) + (u θ / Real.cos θ) ^ 2
          + (Real.tan θ * deriv u θ * u θ) - 6 * (u θ) ^ 2| := by rw [e]
    _ ≤ |deriv (fun t : ℝ => deriv u t) θ * u θ| + (u θ / Real.cos θ) ^ 2
          + |Real.tan θ * deriv u θ * u θ| + 6 * |(u θ) ^ 2| :=
        abs_neg_add_sub_six_mul _ _ _ _ (sq_nonneg _)
    _ ≤ ((deriv (fun t : ℝ => deriv u t) θ) ^ 2 + K ^ 2) + K ^ 2 + M * K + 6 * K ^ 2 := by
        have : |(u θ) ^ 2| = (u θ) ^ 2 := abs_of_nonneg (sq_nonneg _)
        linarith [hA, hB, hC, hDsq]
    _ = (deriv (fun t : ℝ => deriv u t) θ) ^ 2 + (8 * K ^ 2 + M * K) := by ring

/-- **`Lzero1 u · u` is integrable on the open interval.**  Domination by
`(u'')² + 8K² + MK`: the square of the second derivative is integrable by
`sliceLim_integrableOn_sq_of_integrableOn_mul_sEta` (`σ ≥ 1` on `(0,π/2)`). -/
private theorem hon_lzero1_mul_integrable (u : ℝ → ℝ) {M K : ℝ}
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hKu : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ K * Real.cos θ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hsq : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u hint
  have hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 + (8 * K ^ 2 + M * K))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine hsq.add ?_
    exact MeasureTheory.integrableOn_const (C := 8 * K ^ 2 + M * K)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (by simp)
  have hmeas : AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hu : AEStronglyMeasurable u (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      (hsm 0).continuousOn.aestronglyMeasurable measurableSet_Ioo
    have hd1 : AEStronglyMeasurable (fun θ => deriv (fun t : ℝ => deriv u t) θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
    have hd2 : AEStronglyMeasurable (fun θ => deriv (fun s : ℝ => Real.tan s * u s) θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      (measurable_deriv (fun s : ℝ => Real.tan s * u s)).aestronglyMeasurable
    simp only [Work.FTS.EllipticEst.Lzero1]
    exact ((hd1.neg.add hd2).sub (hu.const_mul 6)).mul hu
  refine hD.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Real.norm_eq_abs]
  exact hon_lzero1_pointwise_bound u hM0 hK0 hsm hM hKu hθ

/-! ## The target -/

/-- **The angular self-form of `L₀` for a slice that is smooth on the open interval only.**
For `u` of class `C^∞` on `(0, π/2)`, continuous on `[0, π/2]`, with `u 0 = 0`, `u (π/2) = 0` and
`σ`-square-integrable second derivative (`σ θ = sin(2θ)^{-η}`), the pairing of `Lzero1 u` with `u`
is the quadratic form `∫ (u')² + (1/2) ∫ (u/cos)² - 6 ∫ u²`. -/
theorem HonSliceSelfForm (u : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 u θ * u θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- the uniform bounds `M` for `u'` and `K` for `u/cos` (with `|u| ≤ K cos`)
  obtain ⟨M, K, hM0, hK0, hMbd, hMu2, hKuc, hKdiv⟩ := HonSliceBounds u hsm hcont h0 h1 hint
  have hMu : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * θ := fun θ hθ => (hMu2 θ hθ).1
  -- the one-sided limits `u → 0` at the two endpoints, from continuity on `[0, π/2]`
  have hIo_sub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1.le, hx.2.le⟩
  have h0t : Tendsto u (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto u (𝓝[Set.Icc (0 : ℝ) (Real.pi / 2)] 0) (𝓝 (u 0)) :=
      hcont 0 ⟨le_rfl, hpi2.le⟩
    rw [h0] at h
    have := h.mono_left (nhdsWithin_mono 0 hIo_sub)
    rwa [nhdsWithin_Ioo_eq_nhdsGT hpi2] at this
  have hπt : Tendsto u (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have h : Tendsto u (𝓝[Set.Icc (0 : ℝ) (Real.pi / 2)] (Real.pi / 2))
        (𝓝 (u (Real.pi / 2))) := hcont (Real.pi / 2) ⟨hpi2.le, le_rfl⟩
    rw [h1] at h
    have := h.mono_left (nhdsWithin_mono (Real.pi / 2) hIo_sub)
    rwa [nhdsWithin_Ioo_eq_nhdsLT hpi2] at this
  -- the pointwise antiderivative identity `F' = the integrand of the FTC`
  have hderiv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
          - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2) θ := HonSelfDeriv u hsm
  have hcos_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- integrability of the four summands on the open interval
  have hsq : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hcd : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have hcd' : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact hcd'.continuousOn
    refine IntegrableOn.of_bound ?_ ((hcd.pow 2).aestronglyMeasurable measurableSet_Ioo)
      (M ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs (deriv u θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hMbd θ hθ) 2
  have hdiv2 : IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hcd : ContinuousOn (fun θ => u θ / Real.cos θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((hsm 1).continuousOn).div Real.continuous_cos.continuousOn hcos_ne
    refine IntegrableOn.of_bound ?_ ((hcd.pow 2).aestronglyMeasurable measurableSet_Ioo)
      (K ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs (u θ / Real.cos θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hKdiv θ hθ) 2
  have hu2 : IntegrableOn (fun θ => (u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hcd : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hsm 0).continuousOn
    refine IntegrableOn.of_bound ?_ ((hcd.pow 2).aestronglyMeasurable measurableSet_Ioo)
      (K ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs (u θ)]
      have hc0 : 0 ≤ Real.cos θ :=
        le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
      have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
      have hle : |u θ| ^ 2 ≤ (K * Real.cos θ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hKuc θ hθ) 2
      have hcos2 : (K * Real.cos θ) ^ 2 ≤ K ^ 2 := by
        have hc2 : Real.cos θ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hc0 hc1 2
        calc (K * Real.cos θ) ^ 2 = K ^ 2 * Real.cos θ ^ 2 := by ring
          _ ≤ K ^ 2 * 1 := mul_le_mul_of_nonneg_left (by simpa using hc2) (sq_nonneg K)
          _ = K ^ 2 := by ring
      linarith
  have hL : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hon_lzero1_mul_integrable u hM0 hK0 hsm hMbd hKuc hint
  have hG : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
      - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((hL.sub hsq).sub (hdiv2.const_mul (1 / 2))).add (hu2.const_mul 6)
  -- the two endpoint limits of the antiderivative
  obtain ⟨hFt0, hFtπ⟩ := HonAntiderivTendsto u hM0 hK0 hMbd hMu hKdiv h0t hπt
  -- the fundamental theorem of calculus on the open interval
  have hFTC := integral_Ioo_eq_sub_of_tendsto hpi2 hderiv hG hFt0 hFtπ
  have hFTC' : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
      - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2)) = 0 := by
    simpa using hFTC
  -- split the integral into its four summands
  have h1' : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hL.sub hsq
  have h2' : IntegrableOn (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2)
      - (1 / 2) * (u θ / Real.cos θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h1'.sub (hdiv2.const_mul (1 / 2))
  have hsplit : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
      - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2))
      = ((∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ * u θ)
          - (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2))
        - (1 / 2) * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ / Real.cos θ) ^ 2)
        + 6 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2) := by
    rw [integral_add h2' (hu2.const_mul 6), integral_sub h1' (hdiv2.const_mul (1 / 2)),
      integral_sub hL hsq, integral_const_mul, integral_const_mul]
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ * u θ)
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2)
        + (1 / 2) * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2) := by
    linarith [hFTC', hsplit]
  -- transport the four integrals from `(0, π/2)` to `Iθ = [0, π/2]` (the endpoints are null)
  have e1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 u θ * u θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ * u θ := by
    simp only [Work.Spaces.Iθ]; rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e2 : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]; rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e3 : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ / Real.cos θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]; rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e4 : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]; rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  rw [e1, e2, e3, e4]
  exact hmain

end Work.FTS.EllipticEst.Honest
