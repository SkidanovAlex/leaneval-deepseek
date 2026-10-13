import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

set_option linter.unusedVariables false

/-- **Pointwise convergence + a uniform Lipschitz bound on a compact set implies uniform
convergence there.**

This is the ("Arzelà–Ascoli"-style) step that promotes the pointwise convergence of the
`v n` to local uniform convergence, which is what `hasDerivAt_of_tendstoLocallyUniformlyOn`
consumes.  The proof is the usual finite-subcover argument: `K` is covered by finitely many
`δ`-balls with `δ = ε / (3 (L + 1))`; at the centres of this cover the sequence converges
pointwise and everywhere else the common Lipschitz bound `L` (also valid for the limit `f`,
by passing to the limit in `|F n x - F n y| ≤ L |x - y|`) controls the error. -/
theorem tendstoUniformlyOn_of_pointwise_of_lipschitzOn {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    {L : ℝ} (hL0 : 0 ≤ L)
    (hF : ∀ n, ∀ x ∈ K, ∀ y ∈ K, |F n x - F n y| ≤ L * |x - y|)
    (hf : ∀ x ∈ K, ∀ y ∈ K, |f x - f y| ≤ L * |x - y|)
    (hK : IsCompact K) (hpt : ∀ x ∈ K, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x))) :
    TendstoUniformlyOn F f Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hL1pos : 0 < L + 1 := by linarith
  have hδpos : 0 < ε / (3 * (L + 1)) := by positivity
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun p => Metric.ball p (ε / (3 * (L + 1))))
    (fun p _ => Metric.ball_mem_nhds p hδpos)
  -- the centres of the finite cover are eventually close to the limit
  have hcen : ∀ᶠ n in Filter.atTop, ∀ y ∈ t, |f y - F n y| < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro y hy
    have h0 : Filter.Tendsto (fun _ : ℕ => f y) Filter.atTop (nhds (f y)) := tendsto_const_nhds
    have h2 : Filter.Tendsto (fun n => |f y - F n y|) Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (h0.sub (hpt y (htK y hy))).abs
    filter_upwards [Metric.tendsto_nhds.1 h2 (ε / 3) (by linarith)] with n hn
    simpa [Real.dist_eq, abs_abs] using hn
  filter_upwards [hcen] with n hn
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  have hyK : y ∈ K := htK y hyt
  have hxyδ : |x - y| < ε / (3 * (L + 1)) := by
    have h := Metric.mem_ball.1 hxy
    rwa [Real.dist_eq] at h
  have hscale : ∀ a : ℝ, L * |a| ≤ (L + 1) * |a| := fun a =>
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg a)
  have hdelta : (L + 1) * (ε / (3 * (L + 1))) = ε / 3 := by field_simp
  have h1 : |F n x - F n y| < ε / 3 := by
    calc |F n x - F n y| ≤ (L + 1) * |x - y| := le_trans (hF n x hx y hyK) (hscale (x - y))
      _ < (L + 1) * (ε / (3 * (L + 1))) := mul_lt_mul_of_pos_left hxyδ hL1pos
      _ = ε / 3 := hdelta
  have h3 : |f y - f x| < ε / 3 := by
    calc |f y - f x| ≤ (L + 1) * |y - x| := le_trans (hf y hyK x hx) (hscale (y - x))
      _ = (L + 1) * |x - y| := by rw [abs_sub_comm]
      _ < (L + 1) * (ε / (3 * (L + 1))) := mul_lt_mul_of_pos_left hxyδ hL1pos
      _ = ε / 3 := hdelta
  have h2 : |f y - F n y| < ε / 3 := hn y hyt
  rw [Real.dist_eq]
  calc |f x - F n x| ≤ |f x - f y| + |f y - F n y| + |F n y - F n x| := by
        rw [show f x - F n x = (f x - f y) + (f y - F n y) + (F n y - F n x) from by ring]
        exact abs_add_three _ _ _
    _ < ε := by
        have h4 : |f x - f y| < ε / 3 := by rw [abs_sub_comm]; exact h3
        have h5 : |F n y - F n x| < ε / 3 := by rw [abs_sub_comm]; exact h1
        linarith

/-- **Derivative of a pointwise limit with bounded derivatives.**

Let `u n : ℝ → ℝ` be differentiable on the open interval `(a,b)` with derivative `v n`
(bounded on `(a,b)`), let `v n` be differentiable on `(a,b)` with `|deriv (v n)| ≤ L`
uniformly in `n`, and suppose `u n → φ` and `v n → γ` pointwise on `(a,b)`.  Then `φ` is
differentiable on `(a,b)` with `φ' = γ`.

The uniform bound on `deriv (v n)` makes the `v n` Lipschitz with a common constant, so by
`tendstoUniformlyOn_of_pointwise_of_lipschitzOn` the pointwise convergence `v n → γ` is
locally uniform on the open set `(a,b)` (and the limit `γ` is Lipschitz with the same
constant).  Mathlib's `hasDerivAt_of_tendstoLocallyUniformlyOn` then transfers the
derivatives to the limit.  (No use is made of `hab` or of the `L^∞` bound `hM` on `v n`.) -/
theorem hasDerivAt_of_tendsto_deriv {a b : ℝ} (hab : a < b)
    {u v : ℕ → ℝ → ℝ} {φ γ : ℝ → ℝ}
    (hder : ∀ n, ∀ x ∈ Set.Ioo a b, HasDerivAt (u n) (v n x) x)
    (hvdiff : ∀ n, DifferentiableOn ℝ (v n) (Set.Ioo a b))
    (hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ∀ x ∈ Set.Ioo a b, |v n x| ≤ M)
    (hL : ∃ L : ℝ, 0 ≤ L ∧ ∀ n, ∀ x ∈ Set.Ioo a b, |deriv (v n) x| ≤ L)
    (hu : ∀ x ∈ Set.Ioo a b, Filter.Tendsto (fun n => u n x) Filter.atTop (nhds (φ x)))
    (hv : ∀ x ∈ Set.Ioo a b, Filter.Tendsto (fun n => v n x) Filter.atTop (nhds (γ x))) :
    ∀ x ∈ Set.Ioo a b, HasDerivAt φ (γ x) x := by
  obtain ⟨L, hL0, hL⟩ := hL
  -- the `v n` are `L`-Lipschitz on `(a,b)`, uniformly in `n` (mean value theorem)
  have hv_lip : ∀ n, ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, |v n x - v n y| ≤ L * |x - y| := by
    intro n x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := v n) (s := Set.Ioo a b) (C := L)
      (fun z hz => (hvdiff n).differentiableAt (isOpen_Ioo.mem_nhds hz))
      (fun z hz => by rw [Real.norm_eq_abs]; exact hL n z hz)
      (convex_Ioo a b) hx hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    rwa [abs_sub_comm (v n x) (v n y), abs_sub_comm x y]
  -- the limit `γ` inherits the same Lipschitz bound
  have hγ_lip : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, |γ x - γ y| ≤ L * |x - y| := by
    intro x hx y hy
    have hlim : Filter.Tendsto (fun n => |v n x - v n y|) Filter.atTop (nhds |γ x - γ y|) := by
      simpa using ((hv x hx).sub (hv y hy)).abs
    exact le_of_tendsto' hlim (fun n => hv_lip n x hx y hy)
  -- hence `v n → γ` locally uniformly on the open interval
  have hlu : TendstoLocallyUniformlyOn (fun n => v n) γ Filter.atTop (Set.Ioo a b) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioo]
    intro K hKsub hKc
    exact tendstoUniformlyOn_of_pointwise_of_lipschitzOn hL0
      (fun n x hx y hy => hv_lip n x (hKsub hx) y (hKsub hy))
      (fun x hx y hy => hγ_lip x (hKsub hx) y (hKsub hy)) hKc
      (fun x hx => hv x (hKsub hx))
  intro x hx
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hlu
    (Filter.Eventually.of_forall hder) hu hx

end Work.FTS_RegExport.RXR1
