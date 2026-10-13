/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Aux3/LimDeriv.lean`

**Gap 1 of E5, the analytic core**: differentiability passes to a *pointwise* limit of `C¹`
functions as soon as the derivatives are *uniformly Lipschitz*.

Why this is the right statement for the `ε`-route: the limit family `g` of E5 is built by
Arzelà–Ascoli as (a subsequence of) the pointwise limit of the `ε`-solutions, so the only
regularity available at the limit is *pointwise* convergence plus the uniform `ℋ⁶`-bounds.  The
elliptic layer is evaluated at the limit through `E (slice g τ)`, and `EllLimOK` gives only the
*pointwise* convergence of the jets of `E` (order `≤ 2`); the smoothness of `E (slice g τ)`
(`ContDiffOn ℝ 2`, needed by `E5Law`'s `IsBslSolPos_add`, by `muDyn_tendstoH` and by the
`limApprox` jets) must therefore be *proved* from those two pieces of data.

The key point is that no *uniform convergence of the jets* is needed: the second-order Taylor
remainder of `f n` is bounded by `L‖h‖²` with `L` the Lipschitz constant of `f' n`, **uniformly
in `n`** (mean value inequality), and one then passes to the limit at the *fixed* step `h`.  So
the required input is a uniform `L`, not a uniform modulus of convergence.

The companion consequences (the concrete `ContDiffOn ℝ 2` statement in the `Fn`/`mixed`
vocabulary, and the producer of the uniform Lipschitz constant from the elliptic packages) are
separate modules of `E5Aux3`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Asymptotics

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The second-order Taylor bound, uniformly in the index.**  If `f n` is differentiable on the
open convex set `s` with derivative `f' n` which is `L`-Lipschitz on `s`, then for every `h` with
`p + h ∈ s` the second-order remainder of `f n` at `p` is bounded by `L‖h‖²`. -/
theorem norm_sub_sub_le_of_lipschitz_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hscv : Convex ℝ s) {p : E} (hp : p ∈ s) {L : ℝ} (hL : 0 ≤ L)
    (f : E → F) (f' : E → E →L[ℝ] F)
    (hd : ∀ q ∈ s, HasFDerivAt f (f' q) q)
    (hLip : ∀ q r, q ∈ s → r ∈ s → ‖f' q - f' r‖ ≤ L * ‖q - r‖)
    {h : E} (hh : p + h ∈ s) :
    ‖f (p + h) - f p - f' p h‖ ≤ L * ‖h‖ ^ 2 := by
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t • h ∈ s := by
    intro t ht
    have h1 : p + t • h = (1 - t) • p + t • (p + h) := by module
    rw [h1]
    exact hscv hp hh (by linarith [ht.2]) ht.1 (by ring)
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun u : ℝ => f (p + u • h) - u • (f' p) h)
        ((f' (p + t • h)) h - (f' p) h) (Set.Icc 0 1) t := by
    intro t ht
    have hmap : HasDerivAt (fun u : ℝ => p + u • h) h t := by
      have h1 := (HasDerivAt.smul_const (hasDerivAt_id t) h).const_add p
      simpa only [id_eq, one_smul] using h1
    have h1 : HasDerivAt (fun u : ℝ => f (p + u • h)) ((f' (p + t • h)) h) t :=
      (hd (p + t • h) (hseg t ht)).comp_hasDerivAt t hmap
    have h2 : HasDerivAt (fun u : ℝ => u • (f' p) h) ((f' p) h) t := by
      simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const ((f' p) h)
    exact (h1.sub h2).hasDerivWithinAt (s := Set.Icc 0 1)
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖(f' (p + t • h)) h - (f' p) h‖ ≤ L * ‖h‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    have h1 : (f' (p + t • h)) h - (f' p) h = (f' (p + t • h) - f' p) h := by
      simp only [sub_apply]
    rw [h1]
    have h2 : ‖(f' (p + t • h) - f' p) h‖ ≤ ‖f' (p + t • h) - f' p‖ * ‖h‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖f' (p + t • h) - f' p‖ ≤ L * ‖t • h‖ := by
      have h4 := hLip (p + t • h) p (hseg t ht') hp
      rwa [add_sub_cancel_left] at h4
    have h5 : ‖t • h‖ = t * ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have h6 : t * ‖h‖ * ‖h‖ ≤ ‖h‖ ^ 2 := by
      rw [pow_two]
      calc t * ‖h‖ * ‖h‖ ≤ 1 * ‖h‖ * ‖h‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg h)) (norm_nonneg h)
        _ = ‖h‖ * ‖h‖ := by ring
    calc ‖(f' (p + t • h) - f' p) h‖
        ≤ ‖f' (p + t • h) - f' p‖ * ‖h‖ := h2
      _ ≤ (L * ‖t • h‖) * ‖h‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg h)
      _ = (L * (t * ‖h‖)) * ‖h‖ := by rw [h5]
      _ = L * (t * ‖h‖ * ‖h‖) := by ring
      _ ≤ L * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_left h6 hL
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hbound
  have hrew : (fun u : ℝ => f (p + u • h) - u • (f' p) h) 1
      - (fun u : ℝ => f (p + u • h) - u • (f' p) h) 0
      = f (p + h) - f p - (f' p) h := by
    simp only [one_smul, zero_smul, sub_zero, add_zero]
    abel
  rw [hrew] at hmain
  exact hmain

/-- **Gap 1, analytic core.**  A pointwise limit of `C¹` functions whose derivatives are uniformly
`L`-Lipschitz (and converge pointwise at the base point) is differentiable at the base point, with
the limiting derivative.  No uniform convergence of the functions or of the derivatives is
assumed: the second-order Taylor bound of `norm_sub_sub_le_of_lipschitz_fderiv` is passed to the
limit at the *fixed* step `h`. -/
theorem hasFDerivAt_of_tendsto_of_lipschitz_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hso : IsOpen s) (hscv : Convex ℝ s) {p₀ : E} (hp₀ : p₀ ∈ s) {L : ℝ} (hL : 0 ≤ L)
    {f : ℕ → E → F} {f' : ℕ → E → E →L[ℝ] F} {F₀ : E → F} {F' : E →L[ℝ] F}
    (hd : ∀ n q, q ∈ s → HasFDerivAt (f n) (f' n q) q)
    (hLip : ∀ n q r, q ∈ s → r ∈ s → ‖f' n q - f' n r‖ ≤ L * ‖q - r‖)
    (hf : ∀ q ∈ s, Tendsto (fun n => f n q) atTop (𝓝 (F₀ q)))
    (hf' : Tendsto (fun n => f' n p₀) atTop (𝓝 F')) :
    HasFDerivAt F₀ F' p₀ := by
  -- the second-order Taylor bound, uniformly in `n`
  have hquad : ∀ n (h : E), p₀ + h ∈ s →
      ‖f n (p₀ + h) - f n p₀ - (f' n p₀) h‖ ≤ L * ‖h‖ ^ 2 := fun n h hh =>
    norm_sub_sub_le_of_lipschitz_fderiv hscv hp₀ hL (f n) (f' n) (fun q hq => hd n q hq)
      (fun q r hq hr => hLip n q r hq hr) hh
  -- the limit of `(f' n p₀) h`
  have happ : ∀ h : E, Tendsto (fun n => (f' n p₀) h) atTop (𝓝 (F' h)) := by
    intro h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hf'' : Tendsto (fun n => ‖f' n p₀ - F'‖) atTop (𝓝 0) := by
      rwa [tendsto_iff_norm_sub_tendsto_zero] at hf'
    have hb : ∀ n, ‖(f' n p₀) h - F' h‖ ≤ ‖f' n p₀ - F'‖ * ‖h‖ := by
      intro n
      have h1 : (f' n p₀) h - F' h = (f' n p₀ - F') h := by
        simp only [sub_apply]
      rw [h1]
      exact ContinuousLinearMap.le_opNorm _ _
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _)
      (Filter.Eventually.of_forall hb) ?_
    simpa using hf''.mul_const ‖h‖
  -- the second-order bound at the limit
  have hlim : ∀ h : E, p₀ + h ∈ s →
      ‖F₀ (p₀ + h) - F₀ p₀ - F' h‖ ≤ L * ‖h‖ ^ 2 := by
    intro h hh
    have htend : Tendsto (fun n => f n (p₀ + h) - f n p₀ - (f' n p₀) h) atTop
        (𝓝 (F₀ (p₀ + h) - F₀ p₀ - F' h)) :=
      (((hf (p₀ + h) hh).sub (hf p₀ hp₀)).sub (happ h))
    exact le_of_tendsto (htend.norm) (Filter.Eventually.of_forall fun n => hquad n h hh)
  -- conclude
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hev : ∀ᶠ h : E in 𝓝 (0 : E), p₀ + h ∈ s := by
    have hcont : Continuous fun h : E => p₀ + h := continuous_const.add continuous_id
    exact (hcont.tendsto (0 : E)).eventually (by simpa using hso.mem_nhds hp₀)
  have hO : (fun h : E => F₀ (p₀ + h) - F₀ p₀ - F' h) =O[𝓝 (0 : E)] (fun h : E => ‖h‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound L ?_
    filter_upwards [hev] with h hh
    rw [Real.norm_of_nonneg (sq_nonneg ‖h‖)]
    exact hlim h hh
  have hsq : (fun h : E => ‖h‖ ^ 2) =o[𝓝 (0 : E)] (fun h : E => h) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0 : E) hc] with h hh
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hh
    rw [Real.norm_of_nonneg (sq_nonneg ‖h‖)]
    have : ‖h‖ * ‖h‖ ≤ c * ‖h‖ :=
      mul_le_mul_of_nonneg_right (le_of_lt hh) (norm_nonneg h)
    simpa [pow_two] using this
  exact hO.trans_isLittleO hsq

end Work.FTS.StrongEps.E5Aux3
