import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.E_equivariant_of_eta0
import Submission.Work.Horn.basic

/-!
# `Work.L62.model_deep_branch` — the model's upward inverse branch on a deep half-plane

Let `d : ParabData g₀ D` be §4.1 data for a parabolic germ (`d.E = Φ ∘ φ` the lifted horn map,
with `d.E w - w → 0` at the upper end, `E_upper`).  Write

  `Ψ u = d.E u - u`  (the `1`-periodic correction of the horn map).

`E_upper` says that `Ψ u → 0` uniformly in a half-plane.  Hence, deep in the upper half-plane,
`u ↦ d.E u - β` is a small perturbation of the translation `u ↦ u - β` as soon as `Im β > 0`: the
map `u ↦ w + β - Ψ u` is a contraction on `ball (w + β) r`, and its fixed point `H w` satisfies
`d.E (H w) = w + β`.  Iterating from `w + β` gives `H` as a locally uniform limit of holomorphic
functions, hence `H` is holomorphic, and `H w = w + β + ρ w` with `ρ w = -Ψ (H w)` 1-periodic and
small; `ρ w → 0` because `Im (H w) → +∞`.

Everything here is done from the §4.1 fields alone (`ends_sub`, `φ_holo`, `Φ_holo`, `E_upper`;
`E_lower` is not needed, nor the horn data beyond `Bu ⊇ {η < im}`).
-/

namespace Work.L62

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-! ## 1. The correction `Ψ = d.E - id` of a lifted horn map -/

/-- **Uniform smallness of the correction at the upper end.**  For every `δ > 0` there is a depth
`R` with `‖d.E u - u‖ < δ` on the half-plane `{R < im u}`. -/
theorem model_deep_correction_small {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ u : ℂ, R < u.im → ‖d.E u - u‖ < δ := by
  intro δ hδ
  have h := d.E_upper.eventually (Metric.ball_mem_nhds (0 : ℂ) hδ)
  rw [MandelDim.upperEnd, Filter.eventually_comap, Filter.eventually_atTop] at h
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun u hu => ?_⟩
  have hthis := hR u.im (le_of_lt hu) u rfl
  simpa only [MandelDim.ParabData.E, dist_eq_norm, sub_zero] using hthis

/-- **Holomorphy of the correction on a deep half-plane** (`Y > η₀`). -/
theorem model_deep_correction_holo {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    {Y : ℝ} (hY : d.η₀ < Y) :
    DifferentiableOn ℂ (fun u : ℂ => d.E u - u) {u : ℂ | Y < u.im} := by
  have hsub : {u : ℂ | Y < u.im} ⊆ d.DE := fun u hu =>
    d.ends_sub u (lt_of_lt_of_le (lt_trans hY hu) (le_abs_self u.im))
  have hφ : DifferentiableOn ℂ d.φ {u : ℂ | Y < u.im} :=
    d.φ_holo.mono fun u hu => (hsub hu).1
  have hcomp : DifferentiableOn ℂ (d.Φ ∘ d.φ) {u : ℂ | Y < u.im} :=
    d.Φ_holo.comp hφ fun u hu => (hsub hu).2
  have hE : DifferentiableOn ℂ d.E {u : ℂ | Y < u.im} := hcomp
  exact hE.sub differentiableOn_id

/-- **The correction `Ψ = d.E - id` of a lifted horn map is small and flat on a deep half-plane.**
For §4.1 data `d` and `κ > 0` there is a depth `Y > d.η₀` such that `Ψ u = d.E u - u` is
holomorphic on `{Y < im u}`, satisfies `‖Ψ u‖ ≤ min (κ/8) (1/8)` and `‖deriv Ψ u‖ ≤ 1/2` there. -/
theorem model_deep_correction_bounds {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ Y : ℝ, d.η₀ < Y ∧
      DifferentiableOn ℂ (fun u : ℂ => d.E u - u) {u : ℂ | Y < u.im} ∧
      (∀ u : ℂ, Y < u.im → ‖d.E u - u‖ ≤ min (κ / 8) (1 / 8)) ∧
      (∀ u : ℂ, Y < u.im → ‖deriv (fun u : ℂ => d.E u - u) u‖ ≤ 1 / 2) := by
  have hε : 0 < min (κ / 8) (1 / 8) := lt_min (by linarith) (by norm_num)
  obtain ⟨R, hR⟩ := model_deep_correction_small d (min (κ / 8) (1 / 8)) hε
  refine ⟨max (d.η₀ + 2) (R + 1), ?_, ?_, ?_, ?_⟩
  · linarith [le_max_left (d.η₀ + 2) (R + 1)]
  · exact model_deep_correction_holo d
      (by linarith [le_max_left (d.η₀ + 2) (R + 1)] : d.η₀ < max (d.η₀ + 2) (R + 1))
  · intro u hu
    exact le_of_lt (hR u (by linarith [le_max_right (d.η₀ + 2) (R + 1)]))
  · intro u hu
    set Ψ : ℂ → ℂ := fun u => d.E u - u with hΨdef
    have hhol : DifferentiableOn ℂ Ψ {z : ℂ | max (d.η₀ + 2) (R + 1) - 1 < z.im} :=
      model_deep_correction_holo d (by linarith [le_max_left (d.η₀ + 2) (R + 1)])
    -- the disc of radius 1 around `u` lies in the larger half-plane
    have hball1 : Metric.closedBall u 1 ⊆ {z : ℂ | max (d.η₀ + 2) (R + 1) - 1 < z.im} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      have hz1 : ‖z - u‖ ≤ 1 := by
        have h := Metric.mem_closedBall.mp hz
        rwa [dist_eq_norm] at h
      have h2 : z.im ≥ u.im - ‖z - u‖ := by
        have h3 := (abs_le.mp (Complex.abs_im_le_norm (z - u))).1
        rw [Complex.sub_im] at h3
        linarith
      linarith
    have hdco : DiffContOnCl ℂ Ψ (Metric.ball u 1) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball u (by norm_num : (1 : ℝ) ≠ 0)]
      exact hhol.mono hball1
    have hC : ∀ z ∈ Metric.sphere u 1, ‖Ψ z‖ ≤ min (κ / 8) (1 / 8) := by
      intro z hz
      have hz1 : ‖z - u‖ = 1 := by
        have h := Metric.mem_sphere.mp hz
        rwa [dist_eq_norm] at h
      have h2 : z.im ≥ u.im - ‖z - u‖ := by
        have h3 := (abs_le.mp (Complex.abs_im_le_norm (z - u))).1
        rw [Complex.sub_im] at h3
        linarith
      refine le_of_lt (hR z ?_)
      have hY1R : R ≤ max (d.η₀ + 2) (R + 1) - 1 := by
        linarith [le_max_right (d.η₀ + 2) (R + 1)]
      linarith
    have hle := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := u) (R := 1)
      (C := min (κ / 8) (1 / 8)) (f := Ψ) (by norm_num) hdco hC
    rw [div_one] at hle
    have hfin : min (κ / 8) (1 / 8) ≤ 1 / 2 := by
      calc min (κ / 8) (1 / 8) ≤ 1 / 8 := min_le_right _ _
        _ ≤ 1 / 2 := by norm_num
    exact hle.trans hfin

/-! ## 2. Contractive fixed points depending holomorphically on a parameter -/

/-- Picard iterates of `u ↦ w + β - Ψ u`, started at `w + β`. -/
private def corrIter (Ψ : ℂ → ℂ) (β : ℂ) : ℕ → ℂ → ℂ
  | 0 => fun w => w + β
  | n + 1 => fun w => w + β - Ψ (corrIter Ψ β n w)

/-- Unpacking a fixed-point equation of `u ↦ w + β - Ψ u` into the equation for `F`, where
`Ψ = F - id`. -/
private lemma model_deep_eq_of_fixpt {Ψ F : ℂ → ℂ} (hΨF : ∀ u, Ψ u = F u - u) {β u w : ℂ}
    (h : u = w + β - Ψ u) : F u = w + β := by
  have h1 : u + Ψ u = w + β := by nth_rewrite 1 [h]; ring
  rw [hΨF u] at h1
  have h2 : u + (F u - u) = F u := by ring
  rwa [h2] at h1

private lemma model_deep_sub_eq_neg_of_fixpt {Ψ : ℂ → ℂ} {β u w : ℂ} (h : u = w + β - Ψ u) :
    u - w - β = -(Ψ u) := by
  nth_rewrite 1 [h]; ring

/-- Rewriting a fixed-point equation as an equation for `Ψ`. -/
private lemma psi_model_deep_eq_of_fixpt {Ψ : ℂ → ℂ} {β u w : ℂ} (h : u = w + β - Ψ u) :
    Ψ u = w + β - u := by
  have h1 : u + Ψ u = w + β := by nth_rewrite 1 [h]; ring
  nth_rewrite 1 [add_comm] at h1
  exact eq_sub_of_add_eq h1

/-- **Contractive fixed points depending holomorphically on a parameter.**  Let `Ψ` be holomorphic
on an open `Ω ⊆ ℂ`, `β : ℂ`, `0 < r`, `0 ≤ L < 1`.  If for every `w` in the open set `s` the closed
ball `closedBall (w + β) r` is contained in `Ω`, with `‖Ψ‖ ≤ (1 - L) * r` and `‖deriv Ψ‖ ≤ L`
there, then `u ↦ w + β - Ψ u` has a unique fixed point `H w` in that ball and `H` is holomorphic
on `s`. -/
theorem model_deep_contraction {s Ω : Set ℂ} (hs : IsOpen s) (hΩ : IsOpen Ω) {Ψ : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ Ω) {β : ℂ} {r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hball : ∀ w ∈ s, Metric.closedBall (w + β) r ⊆ Ω)
    (hsmall : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r, ‖Ψ u‖ ≤ (1 - L) * r)
    (hlip : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r, ‖deriv Ψ u‖ ≤ L) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H s ∧
      (∀ w ∈ s, H w ∈ Metric.closedBall (w + β) r ∧ H w = w + β - Ψ (H w)) ∧
      (∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r, u = w + β - Ψ u → u = H w) := by
  -- `Ψ` is `L`-Lipschitz on each of the balls
  have hlipΨ : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r,
      ∀ v ∈ Metric.closedBall (w + β) r, ‖Ψ u - Ψ v‖ ≤ L * ‖u - v‖ := by
    intro w hw u hu v hv
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hΨ.differentiableAt (hΩ.mem_nhds (hball w hw hz))))
      (fun z hz => hlip w hw z hz) (convex_closedBall _ _) hv hu
  -- the iterates stay in the ball
  have hmem : ∀ (n : ℕ) (w : ℂ), w ∈ s → corrIter Ψ β n w ∈ Metric.closedBall (w + β) r := by
    intro n
    induction n with
    | zero =>
      intro w hw
      simp only [corrIter, Metric.mem_closedBall, dist_eq_norm, sub_self, norm_zero]
      exact hr.le
    | succ k ih =>
      intro w hw
      have hk := ih w hw
      have hval := hsmall w hw _ hk
      have h1 : corrIter Ψ β (k + 1) w - (w + β) = -(Ψ (corrIter Ψ β k w)) := by
        simp only [corrIter]; ring
      rw [Metric.mem_closedBall, dist_eq_norm, h1, norm_neg]
      exact hval.trans (by nlinarith [hL0, hr])
  -- consecutive iterates are a geometric sequence
  have hstep : ∀ (n : ℕ) (w : ℂ), w ∈ s →
      ‖corrIter Ψ β (n + 1) w - corrIter Ψ β n w‖ ≤ L ^ n * ((1 - L) * r) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      have h1 : corrIter Ψ β 1 w - corrIter Ψ β 0 w = -(Ψ (w + β)) := by
        simp only [corrIter]; ring
      rw [h1, norm_neg, pow_zero, one_mul]
      exact hsmall w hw (w + β) (by rw [Metric.mem_closedBall, dist_self]; exact hr.le)
    | succ k ih =>
      intro w hw
      have h1 : corrIter Ψ β (k + 1 + 1) w - corrIter Ψ β (k + 1) w
          = -(Ψ (corrIter Ψ β (k + 1) w) - Ψ (corrIter Ψ β k w)) := by
        simp only [corrIter]; ring
      rw [h1, norm_neg]
      calc ‖Ψ (corrIter Ψ β (k + 1) w) - Ψ (corrIter Ψ β k w)‖
          ≤ L * ‖corrIter Ψ β (k + 1) w - corrIter Ψ β k w‖ :=
            hlipΨ w hw _ (hmem (k + 1) w hw) _ (hmem k w hw)
        _ ≤ L * (L ^ k * ((1 - L) * r)) := mul_le_mul_of_nonneg_left (ih w hw) hL0
        _ = L ^ (k + 1) * ((1 - L) * r) := by rw [pow_succ]; ring
  -- summability of the differences
  have hsummable : ∀ w ∈ s,
      Summable (fun n : ℕ => corrIter Ψ β (n + 1) w - corrIter Ψ β n w) := fun w hw =>
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hL0 hL1).mul_right ((1 - L) * r))
      (fun n => hstep n w hw)
  -- the limit function
  set H : ℂ → ℂ :=
    fun w => corrIter Ψ β 0 w + ∑' n : ℕ, (corrIter Ψ β (n + 1) w - corrIter Ψ β n w) with hHdef
  have hlim : ∀ w ∈ s, Tendsto (fun n => corrIter Ψ β n w) atTop (𝓝 (H w)) := by
    intro w hw
    have hh : Tendsto (fun n => ∑ i ∈ Finset.range n,
        (corrIter Ψ β (i + 1) w - corrIter Ψ β i w)) atTop
        (𝓝 (∑' n : ℕ, (corrIter Ψ β (n + 1) w - corrIter Ψ β n w))) :=
      (hsummable w hw).hasSum.tendsto_sum_nat
    have h2 : ∀ n : ℕ, (∑ i ∈ Finset.range n,
        (corrIter Ψ β (i + 1) w - corrIter Ψ β i w))
        = corrIter Ψ β n w - corrIter Ψ β 0 w :=
      fun n => Finset.sum_range_sub (fun i => corrIter Ψ β i w) n
    simp only [h2] at hh
    have hh' := hh.add_const (corrIter Ψ β 0 w)
    have h3 : (fun n => corrIter Ψ β n w - corrIter Ψ β 0 w + corrIter Ψ β 0 w)
        = fun n => corrIter Ψ β n w := by funext n; ring
    rw [h3] at hh'
    rw [hHdef]
    change Tendsto (fun n => corrIter Ψ β n w) atTop
      (𝓝 (corrIter Ψ β 0 w + ∑' n : ℕ, (corrIter Ψ β (n + 1) w - corrIter Ψ β n w)))
    rw [add_comm]
    exact hh'
  have hHclosed : ∀ w ∈ s, H w ∈ Metric.closedBall (w + β) r := fun w hw =>
    Metric.isClosed_closedBall.mem_of_tendsto (hlim w hw)
      (Filter.Eventually.of_forall fun n => hmem n w hw)
  -- each iterate is holomorphic on `s`
  have hDdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun w => corrIter Ψ β n w) s := by
    intro n
    induction n with
    | zero =>
      intro w hw
      exact (differentiableAt_id.add_const β).differentiableWithinAt
    | succ k ih =>
      have h1 : DifferentiableOn ℂ (fun w => Ψ (corrIter Ψ β k w)) s :=
        hΨ.comp ih fun w hw => hball w hw (hmem k w hw)
      have h2 : DifferentiableOn ℂ (fun w => w + β - Ψ (corrIter Ψ β k w)) s :=
        (differentiableOn_id.add_const β).sub h1
      intro w hw
      have := h2 w hw
      simpa only [corrIter] using this
  have hdiff : DifferentiableOn ℂ H s := by
    have hsum : DifferentiableOn ℂ
        (fun w => ∑' n : ℕ, (corrIter Ψ β (n + 1) w - corrIter Ψ β n w)) s :=
      Complex.differentiableOn_tsum_of_summable_norm
        ((summable_geometric_of_lt_one hL0 hL1).mul_right ((1 - L) * r))
        (fun n => (hDdiff (n + 1)).sub (hDdiff n)) hs (fun n w hw => hstep n w hw)
    rw [hHdef]
    exact (hDdiff 0).add hsum
  -- the fixed-point equation, by continuity
  have hfix : ∀ w ∈ s, H w = w + β - Ψ (H w) := by
    intro w hw
    have hHΩ : H w ∈ Ω := hball w hw (hHclosed w hw)
    have hcont : Tendsto (fun n => w + β - Ψ (corrIter Ψ β n w)) atTop (𝓝 (w + β - Ψ (H w))) :=
      tendsto_const_nhds.sub
        (((hΨ.differentiableAt (hΩ.mem_nhds hHΩ)).continuousAt.tendsto).comp (hlim w hw))
    have heq : (fun n => w + β - Ψ (corrIter Ψ β n w)) = fun n => corrIter Ψ β (n + 1) w := by
      funext n; simp only [corrIter]
    have hlim2 : Tendsto (fun n => corrIter Ψ β (n + 1) w) atTop (𝓝 (H w)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr (hlim w hw)
    exact tendsto_nhds_unique hlim2 (heq ▸ hcont)
  refine ⟨H, hdiff, fun w hw => ⟨hHclosed w hw, hfix w hw⟩, fun w hw u hu hufix => ?_⟩
  have hHu : H w = w + β - Ψ (H w) := hfix w hw
  have hlip' := hlipΨ w hw u hu (H w) (hHclosed w hw)
  have hdiff' : u - H w = -(Ψ u - Ψ (H w)) := by
    rw [psi_model_deep_eq_of_fixpt hufix, psi_model_deep_eq_of_fixpt hHu]; ring
  have h1 : ‖u - H w‖ ≤ L * ‖u - H w‖ := by
    have heq : ‖u - H w‖ = ‖Ψ u - Ψ (H w)‖ := by rw [hdiff', norm_neg]
    conv_lhs => rw [heq]
    exact hlip'
  have h2 : (1 - L) * ‖u - H w‖ ≤ 0 := by nlinarith [h1]
  have hpos : 0 < 1 - L := by linarith
  have hnn := norm_nonneg (u - H w)
  have h3 : ‖u - H w‖ = 0 := by nlinarith [h2, hnn, hpos]
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-! ## 3. The model's upward inverse branch -/

/-- **The model's upward inverse branch on a deep half-plane.**  For the lifted horn map
`E = d.E` of a germ `g₀ ∈ 𝓕₀` and `κ ≤ Im β`, and for every sufficiently deep threshold `y₁`, there
are a threshold `y' ≥ y₁`, a holomorphic injection `H` of the half-plane `{y' < im}` into the deep
region `{y₁ < im} ∩ Bu`, and a holomorphic `1`-periodic `ρ` with `H w = w + β + ρ w`,
`‖ρ w‖ ≤ κ/2`, `ρ w → 0` at the upper end, drill `κ/2 ≤ Im (H w - w)` and `E (H w) - β = w`. -/
theorem model_deep_branch {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {κ : ℝ} (hκ : 0 < κ) (hβ : κ ≤ Complex.im β) :
    ∃ y : ℝ, ∀ y₁ : ℝ, y ≤ y₁ →
      ∃ (H : ℂ → ℂ) (ρ : ℂ → ℂ) (y' : ℝ), y₁ ≤ y' ∧
        DifferentiableOn ℂ H {w : ℂ | y' < Complex.im w} ∧
        (∀ w : ℂ, y' < Complex.im w → y₁ < Complex.im (H w) ∧ H w ∈ hd.Bu ∧
          d.E (H w) - β = w) ∧
        (∀ w : ℂ, y' < Complex.im w → H w = w + β + ρ w) ∧
        DifferentiableOn ℂ ρ {w : ℂ | y' < Complex.im w} ∧
        (∀ w : ℂ, y' < Complex.im w → ρ (w + 1) = ρ w) ∧
        (∀ w : ℂ, y' < Complex.im w → ‖ρ w‖ ≤ κ / 2) ∧
        (∀ w : ℂ, y' < Complex.im w → κ / 2 ≤ Complex.im (H w - w)) ∧
        Set.InjOn H {w : ℂ | y' < Complex.im w} ∧
        Filter.Tendsto ρ (Filter.comap Complex.im Filter.atTop) (nhds 0) := by
  obtain ⟨Y, hYη, hΨdiff, hΨsmall, hΨderiv⟩ := model_deep_correction_bounds d hκ
  set Ψ : ℂ → ℂ := fun u => d.E u - u with hΨdef
  have hΨE : ∀ u : ℂ, Ψ u = d.E u - u := fun u => by simp only [hΨdef]
  -- `Ψ` is `1`-periodic on the deep half-plane
  have hΨper : ∀ u : ℂ, Y < u.im → Ψ (u + 1) = Ψ u := by
    intro u hu
    have h := E_equivariant_of_eta0 d (lt_of_lt_of_le (lt_trans hYη hu) (le_abs_self u.im))
    simp only [hΨdef]
    rw [h]
    ring
  set r : ℝ := κ / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  refine ⟨max Y hd.η + 1, fun y₁ hy₁ => ?_⟩
  set y' : ℝ := max y₁ (max Y hd.η) + 1 with hy'def
  have hy'1 : y₁ ≤ y' := by rw [hy'def]; linarith [le_max_left y₁ (max Y hd.η)]
  have hy'Y : Y + 1 ≤ y' := by
    rw [hy'def]; linarith [le_trans (le_max_left Y hd.η) (le_max_right y₁ (max Y hd.η))]
  have hy'η : hd.η + 1 ≤ y' := by
    rw [hy'def]; linarith [le_trans (le_max_right Y hd.η) (le_max_right y₁ (max Y hd.η))]
  have hy'eq : y' = max y₁ (max Y hd.η) + 1 := hy'def
  set s : Set ℂ := {w : ℂ | y' < w.im} with hsdef
  have hsopen : IsOpen s := by rw [hsdef]; exact isOpen_lt continuous_const continuous_im
  set Ω : Set ℂ := {u : ℂ | Y < u.im} with hΩdef
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact isOpen_lt continuous_const continuous_im
  have hΨΩ : DifferentiableOn ℂ Ψ Ω := by rw [hΨdef, hΩdef]; exact hΨdiff
  -- the balls of the contraction lie inside the deep half-plane
  have hball : ∀ w ∈ s, Metric.closedBall (w + β) r ⊆ Ω := by
    intro w hw u hu
    have h1 : ‖u - (w + β)‖ ≤ r := by
      have h := Metric.mem_closedBall.mp hu
      rwa [dist_eq_norm] at h
    have h2 : u.im ≥ (w + β).im - ‖u - (w + β)‖ := by
      have h3 := (abs_le.mp (Complex.abs_im_le_norm (u - (w + β)))).1
      rw [Complex.sub_im] at h3
      linarith
    have h6 : (w + β).im = w.im + β.im := Complex.add_im w β
    rw [hΩdef]
    simp only [Set.mem_ofPred_eq]
    rw [hrdef] at h1
    rw [h6] at h2
    have hw' : y' < w.im := hw
    linarith [hβ, h1, h2, hw']
  have hsmall : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r, ‖Ψ u‖ ≤ (1 - 1 / 2) * r := by
    intro w hw u hu
    have huΩ : u ∈ Ω := hball w hw hu
    rw [hΩdef] at huΩ
    simp only [Set.mem_ofPred_eq] at huΩ
    have h := hΨsmall u huΩ
    rw [hΨdef]
    refine h.trans ?_
    rw [hrdef]
    calc min (κ / 8) (1 / 8) ≤ κ / 8 := min_le_left _ _
      _ = (1 - 1 / 2) * (κ / 4) := by ring
  have hlip : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r, ‖deriv Ψ u‖ ≤ (1 / 2 : ℝ) := by
    intro w hw u hu
    have huΩ : u ∈ Ω := hball w hw hu
    rw [hΩdef] at huΩ
    simp only [Set.mem_ofPred_eq] at huΩ
    have h := hΨderiv u huΩ
    rwa [hΨdef] at h
  obtain ⟨H, hHdiff, hHfix, hHuniq⟩ := model_deep_contraction hsopen hΩopen hΨΩ hr
    (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1) hball hsmall hlip
  -- basic consequences of the fixed-point equation
  have hHmem : ∀ w ∈ s, H w ∈ Metric.closedBall (w + β) r := fun w hw => (hHfix w hw).1
  have hHΩ : ∀ w ∈ s, H w ∈ Ω := fun w hw => hball w hw (hHmem w hw)
  have hEdot : ∀ w ∈ s, d.E (H w) = w + β := fun w hw => model_deep_eq_of_fixpt hΨE (hHfix w hw).2
  have hEmem : ∀ w ∈ s, d.E (H w) - β = w := fun w hw => by rw [hEdot w hw]; ring
  have hρval : ∀ w ∈ s, H w - w - β = -(Ψ (H w)) := fun w hw =>
    model_deep_sub_eq_neg_of_fixpt (hHfix w hw).2
  have hρbd : ∀ w ∈ s, ‖H w - w - β‖ ≤ r := by
    intro w hw
    have h1 : ‖H w - (w + β)‖ ≤ r := by
      have h := Metric.mem_closedBall.mp (hHmem w hw)
      rwa [dist_eq_norm] at h
    have h2 : H w - w - β = H w - (w + β) := by ring
    rwa [h2]
  -- `w ∈ s` from a literal hypothesis
  have hmem_s : ∀ {w : ℂ}, y' < w.im → w ∈ s := by
    intro w hw; rw [hsdef]; exact hw
  refine ⟨H, fun w => H w - w - β, y', hy'1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hsdef] using hHdiff
  · intro w hw
    have hws : w ∈ s := hmem_s hw
    have hlow : (H w).im ≥ (w + β).im - ‖H w - (w + β)‖ := by
      have h3 := (abs_le.mp (Complex.abs_im_le_norm (H w - (w + β)))).1
      rw [Complex.sub_im] at h3
      linarith
    have hbd : ‖H w - (w + β)‖ ≤ r := by
      have h := Metric.mem_closedBall.mp (hHmem w hws)
      rwa [dist_eq_norm] at h
    have h6 : (w + β).im = w.im + β.im := Complex.add_im w β
    rw [hrdef] at hbd
    rw [h6] at hlow
    have hkey : max y₁ (max Y hd.η) < (H w).im := by
      linarith [hβ, hbd, hlow, hw, hy'eq]
    have hyy₁ : y₁ < (H w).im := lt_of_le_of_lt (le_max_left y₁ (max Y hd.η)) hkey
    have hyη : hd.η < (H w).im :=
      lt_of_le_of_lt (le_trans (le_max_right Y hd.η) (le_max_right y₁ (max Y hd.η))) hkey
    exact ⟨hyy₁, hd.upper hyη, hEmem w hws⟩
  · intro w hw
    ring
  · exact (hHdiff.sub differentiableOn_id).sub (differentiableOn_const β)
  · intro w hw
    have hws : w ∈ s := hmem_s hw
    have hw1 : w + 1 ∈ s := hmem_s (by simpa using hw)
    have hfix1 := (hHfix (w + 1) hw1)
    have hE1 : d.E (H (w + 1)) = (w + 1) + β := model_deep_eq_of_fixpt hΨE hfix1.2
    have hΨ1 : Ψ (H (w + 1)) = (w + 1) + β - H (w + 1) := by
      have := hΨE (H (w + 1))
      rw [hE1] at this
      exact this
    have hmem1' : H (w + 1) - 1 ∈ Metric.closedBall (w + β) r := by
      have h := Metric.mem_closedBall.mp hfix1.1
      rw [Metric.mem_closedBall]
      rw [dist_eq_norm] at h ⊢
      have hz : H (w + 1) - 1 - (w + β) = H (w + 1) - ((w + 1) + β) := by ring
      rw [hz]; exact h
    have hperψ : Ψ (H (w + 1) - 1) = Ψ (H (w + 1)) := by
      have hz : (H (w + 1) - 1) + 1 = H (w + 1) := by ring
      have hm1 : H (w + 1) ∈ Ω := hHΩ (w + 1) hw1
      have hm : H (w + 1) - 1 ∈ Ω := by
        rw [hΩdef] at hm1 ⊢
        simp only [Set.mem_ofPred_eq] at hm1 ⊢
        rw [Complex.sub_im, Complex.one_im, sub_zero]
        exact hm1
      have := hΨper (H (w + 1) - 1) hm
      rw [hz] at this
      exact this.symm
    have hpt : H (w + 1) - 1 = w + β - Ψ (H (w + 1) - 1) := by
      rw [hperψ, hΨ1]; ring
    have hconcl := hHuniq w hws (H (w + 1) - 1) hmem1' hpt
    show H (w + 1) - (w + 1) - β = H w - w - β
    rw [← hconcl]; ring
  · intro w hw
    have hws : w ∈ s := hmem_s hw
    have hb := hρbd w hws
    rw [hrdef] at hb
    linarith
  · intro w hw
    have hws : w ∈ s := hmem_s hw
    have hsplit : H w - w = β + (H w - w - β) := by ring
    rw [hsplit, Complex.add_im]
    have hb := hρbd w hws
    rw [hrdef] at hb
    have h3 := (abs_le.mp (Complex.abs_im_le_norm (H w - w - β))).1
    linarith
  · intro w hw w' hw' hEq
    have hws : w ∈ s := hmem_s hw
    have hw's : w' ∈ s := hmem_s hw'
    have h1 : w = d.E (H w) - β := (hEmem w hws).symm
    have h2 : w' = d.E (H w') - β := (hEmem w' hw's).symm
    rw [h1, h2, hEq]
  · -- `ρ w → 0` at the upper end
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨R₁, hR₁⟩ := model_deep_correction_small d δ hδ
    rw [Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨max (y' + 1) (R₁ + r + 1), fun b hb w hw => ?_⟩
    have hb' : y' < b := by linarith [le_max_left (y' + 1) (R₁ + r + 1)]
    have hws : w ∈ s := hmem_s (by rw [hw]; exact hb')
    have hfix := (hHfix w hws).2
    have hρw : H w - w - β = -(Ψ (H w)) := hρval w hws
    have hlow : (H w).im ≥ (w + β).im - ‖H w - (w + β)‖ := by
      have h3 := (abs_le.mp (Complex.abs_im_le_norm (H w - (w + β)))).1
      rw [Complex.sub_im] at h3
      linarith
    have hbd : ‖H w - (w + β)‖ ≤ r := by
      have h := Metric.mem_closedBall.mp (hHmem w hws)
      rwa [dist_eq_norm] at h
    have h6 : (w + β).im = w.im + β.im := Complex.add_im w β
    rw [hrdef] at hbd
    rw [h6] at hlow
    have him : R₁ < (H w).im := by
      have hb'' : R₁ + r + 1 ≤ b := le_trans (le_max_right (y' + 1) (R₁ + r + 1)) hb
      linarith [hβ, hbd, hlow, hw]
    rw [Complex.dist_eq, hρw, sub_zero, norm_neg]
    exact hR₁ (H w) him

end

end Work.L62
