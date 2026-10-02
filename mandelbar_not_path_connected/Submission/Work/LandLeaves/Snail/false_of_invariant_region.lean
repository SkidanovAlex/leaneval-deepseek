import Mathlib
import Submission.Work.LandLeaves.Snail.tendstoUniformlyOn_zero_of_bounded_of_pointwise
import Submission.Work.LandLeaves.Snail.tendsto_deriv_zero_of_tendsto_on_sphere

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `false_of_invariant_region`

A holomorphic germ `f` with `f 0 = 0`, `deriv f 0 = lam`, `‖lam‖ = 1` cannot admit *both*

* a bounded `f`-invariant open region `V` containing a disc around `0` (`V` open, `MapsTo f V V`,
  `IsBounded V`, `DifferentiableOn ℂ f V`, `Metric.ball 0 ρ ⊆ V`), and
* a nonzero orbit `w ≠ 0`, `f^[k] w ≠ 0`, `f^[k] w → 0`.

The reason is the classical "bounded invariant region forces an attracting fixed point" argument,
with the Montel/Vitali convergence theorem replacing the Denjoy–Wolff theorem:

* `f^[k]` maps `V` into the bounded `V`, hence is uniformly bounded on the disc `ball 0 ρ ⊆ V`;
* the points `x j := f^[j] w` are nonzero and tend to `0`, and for each fixed `j`,
  `f^[n] (x j) = f^[n+j] w → 0`; so the Vitali theorem
  (`tendstoUniformlyOn_zero_of_bounded_of_pointwise`) gives `f^[k] → 0` uniformly on a smaller
  disc;
* pointwise convergence on a circle `|z| = ρ/4 ⊆ V` together with the uniform bound, through
  Cauchy's integral formula plus dominated convergence
  (`tendsto_deriv_zero_of_tendsto_on_sphere`), gives `deriv (f^[k]) 0 → 0`;
* but the chain rule along the fixed point gives `deriv (f^[k]) 0 = lam ^ k`, whose norm is `1`.
-/

namespace Work.LandLeaves.Snail

open Filter Topology

/-- `(f^[n]) 0 = 0` when `0` is a fixed point of `f`. -/
lemma iterate_zero_of_fixed {f : ℂ → ℂ} (hfix : f 0 = 0) :
    ∀ n : ℕ, (f^[n]) 0 = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]

/-- The iterates of a germ fixing `0` are differentiable at `0`. -/
lemma differentiableAt_iterate_of_fixed {f : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0)
    (hfix : f 0 = 0) : ∀ n : ℕ, DifferentiableAt ℂ (f^[n]) 0 := by
  intro n
  induction n with
  | zero => simpa using differentiableAt_id
  | succ k ih =>
    change DifferentiableAt ℂ (f^[k] ∘ f) 0
    exact (by rw [hfix]; exact ih : DifferentiableAt ℂ (f^[k]) (f 0)).comp 0 hf

/-- The chain rule along a fixed point: `(f^[n])'(0) = (f'(0)) ^ n`. -/
lemma deriv_iterate_eq_of_fixed {f : ℂ → ℂ} {lam : ℂ} (hf : DifferentiableAt ℂ f 0)
    (hfix : f 0 = 0) (hder : deriv f 0 = lam) :
    ∀ n : ℕ, deriv (f^[n]) 0 = lam ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    change deriv ((f^[k]) ∘ f) 0 = lam ^ (k + 1)
    rw [deriv_comp (𝕜 := ℂ) 0
      (by rw [hfix]; exact differentiableAt_iterate_of_fixed hf hfix k) hf, hfix, ih, hder]
    ring

theorem false_of_invariant_region {f : ℂ → ℂ} {lam : ℂ}
    (hfix : f 0 = 0) (hder : deriv f 0 = lam) (h1 : ‖lam‖ = 1)
    {w : ℂ} (hw : w ≠ 0) (hav : ∀ k : ℕ, f^[k] w ≠ 0)
    (hlim : Filter.Tendsto (fun k : ℕ => f^[k] w) Filter.atTop (nhds 0))
    {ρ : ℝ} (hρ : 0 < ρ) {V : Set ℂ} (hVo : IsOpen V) (hVb : Metric.ball 0 ρ ⊆ V)
    (hVm : Set.MapsTo f V V) (hVbd : Bornology.IsBounded V)
    (hVd : DifferentiableOn ℂ f V) : False := by
  -- `0 ∈ V`, and `f` is differentiable at `0`.
  have h0V : (0 : ℂ) ∈ V := hVb (Metric.mem_ball_self hρ)
  have hfd : DifferentiableAt ℂ f 0 := hVd.differentiableAt (hVo.mem_nhds h0V)
  -- the iterates map `V` into itself
  have hmap : ∀ n : ℕ, Set.MapsTo (f^[n]) V V := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      exact ih (hVm hx)
  -- the iterates are holomorphic on `V`
  have hdiffV : ∀ n : ℕ, DifferentiableOn ℂ (f^[n]) V := by
    intro n
    induction n with
    | zero => simpa using (differentiableOn_id : DifferentiableOn ℂ (id : ℂ → ℂ) V)
    | succ k ih =>
      rw [Function.iterate_succ]
      exact ih.comp hVd hVm
  -- a bound for `V`
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hVbd
  have hCV : ∀ z ∈ V, ‖z‖ ≤ C := by
    intro z hz
    have := hC hz h0V
    simpa using this
  -- data for the Vitali convergence theorem
  have hd : ∀ n : ℕ, DifferentiableOn ℂ (f^[n]) (Metric.ball 0 ρ) :=
    fun n => (hdiffV n).mono hVb
  have hb : ∃ M : ℝ, ∀ n : ℕ, ∀ z : ℂ, z ∈ Metric.ball 0 ρ → ‖(f^[n]) z‖ ≤ M :=
    ⟨C, fun n z hz => hCV ((f^[n]) z) (hmap n (hVb hz))⟩
  have hx : Filter.Tendsto (fun j : ℕ => (f^[j]) w) Filter.atTop (nhds 0) := hlim
  have hxne : ∀ j : ℕ, (f^[j]) w ≠ 0 := hav
  have hconv : ∀ j : ℕ,
      Filter.Tendsto (fun n : ℕ => (f^[n]) ((f^[j]) w)) Filter.atTop (nhds 0) := by
    intro j
    have hshift : Filter.Tendsto (fun n : ℕ => n + j) Filter.atTop Filter.atTop :=
      Filter.tendsto_add_atTop_nat j
    have h := hlim.comp hshift
    simpa [Function.comp_def, Function.iterate_add_apply] using h
  -- Vitali: `f^[k] → 0` uniformly on a smaller disc
  obtain ⟨hρ2pos, hρ2lt⟩ : (0 : ℝ) < ρ / 2 ∧ ρ / 2 < ρ := by
    constructor <;> linarith
  have hVu : TendstoUniformlyOn (fun n : ℕ => (f^[n])) (fun _ : ℂ => (0 : ℂ)) Filter.atTop
      (Metric.ball 0 (ρ / 2)) :=
    tendstoUniformlyOn_zero_of_bounded_of_pointwise hρ hd hb hx hxne hconv hρ2pos hρ2lt
  -- pointwise convergence on the circle of radius `ρ/4`
  obtain ⟨hρ4pos, hρ4lt4⟩ : (0 : ℝ) < ρ / 4 ∧ ρ / 4 < ρ / 2 := by
    constructor <;> linarith
  have hρ4lt : ρ / 4 < ρ := by linarith
  have hpt : ∀ z ∈ Metric.sphere (0 : ℂ) (ρ / 4),
      Filter.Tendsto (fun n : ℕ => (f^[n]) z) Filter.atTop (nhds 0) := by
    intro z hz
    exact hVu.tendsto_at (Metric.sphere_subset_ball hρ4lt4 hz)
  -- dominated convergence + Cauchy give `(f^[k])'(0) → 0`
  have hderiv : Filter.Tendsto (fun n : ℕ => deriv (f^[n]) 0) Filter.atTop (nhds 0) :=
    tendsto_deriv_zero_of_tendsto_on_sphere (g := fun n : ℕ => (f^[n])) (R := ρ / 4) (M := C)
      hρ4pos (by simpa using hCV 0 h0V)
      (fun n => (hdiffV n).mono ((Metric.closedBall_subset_ball hρ4lt).trans hVb))
      (fun n z hz =>
        hCV ((f^[n]) z) (hmap n (hVb (Metric.sphere_subset_ball hρ4lt hz))))
      hpt
  -- but the chain rule gives `(f^[k])'(0) = lam ^ k`, of norm `1`
  have heq : (fun n : ℕ => deriv (f^[n]) 0) = fun n : ℕ => lam ^ n :=
    funext fun n => deriv_iterate_eq_of_fixed hfd hfix hder n
  have ht : Filter.Tendsto (fun n : ℕ => lam ^ n) Filter.atTop (nhds 0) := by
    rw [← heq]; exact hderiv
  have hnorm : Filter.Tendsto (fun n : ℕ => ‖lam ^ n‖) Filter.atTop (nhds 0) := by
    simpa using ht.norm
  have hconst : (fun n : ℕ => ‖lam ^ n‖) = fun _ : ℕ => (1 : ℝ) := by
    funext n; rw [norm_pow, h1, one_pow]
  rw [hconst] at hnorm
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hnorm)

end Work.LandLeaves.Snail
