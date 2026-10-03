import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.end_fourier

/-!
# `Work.L62.perturbed_branch` — the perturbed inverse branch on a deep half-plane

Given the exact model branch `H₀` of `E - β` on a deep half-plane, an admissible perturbation `R`
of `E` (holomorphic, `T`-equivariant, `δ`-close to `E` on the deep region, `δ ≤ κ/16`) is
re-inverted on a *deeper* half-plane with all the structural properties of `H₀`: the drift
`κ/4 ≤ Im (H w - w)`, an increment `ρ = H - id - β` that is holomorphic, `1`-periodic and bounded
by `κ/2`, `H` injective, and `ρ` having a limit `c` at the upper end.

The proof does not use `H₀` at all: deep in the upper half-plane the lifted horn map satisfies
`E u - u → 0` (`ParabData.E_upper`), so on a sufficiently deep half-plane `R - id` is a *small and
flat* perturbation of the identity: `‖R u - u‖ ≤ κ/8` and `‖deriv (R - id) u‖ ≤ 1/2`.  The map
`u ↦ w + β - (R u - u)` is then a contraction on the closed ball `closedBall (w + β) (κ/4)` whose
fixed point `H w` solves `R (H w) = w + β` and depends holomorphically on `w`.  The equivariance of
`R` and the uniqueness of the fixed point in the ball make `H` equivariant, so `ρ` is `1`-periodic,
and `end_fourier` (a bounded periodic holomorphic function on a deep half-plane has a limit at
`+i∞`) supplies the limit of `ρ`.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-- The `n`-th Picard iterate of `u ↦ w + β - Ψ u`, started at `w + β`. -/
private def picIter (Ψ : ℂ → ℂ) (β : ℂ) : ℕ → ℂ → ℂ
  | 0 => fun w => w + β
  | (n + 1) => fun w => w + β - Ψ (picIter Ψ β n w)

/-- **Contractive fixed points depending holomorphically on a parameter.**  Let `Ψ` be holomorphic
on an open set `Ω ⊆ ℂ`, `β : ℂ`, `r > 0`, `0 ≤ L < 1`.  If for every `w` in the open set `s` the
closed ball `closedBall (w + β) r` is contained in `Ω`, and on that ball `‖Ψ‖ ≤ (1 - L) * r` and
`‖deriv Ψ‖ ≤ L`, then `u ↦ w + β - Ψ u` has a unique fixed point `w ↦ H w` in that ball, and `H`
is holomorphic on `s` (as the uniform limit of the Picard iterates). -/
theorem contraction_fixed_point_holomorphic_tmp {s Ω : Set ℂ} (hs : IsOpen s) (hΩ : IsOpen Ω)
    {Ψ : ℂ → ℂ} (hΨ : DifferentiableOn ℂ Ψ Ω) {β : ℂ} {r L : ℝ} (hr : 0 < r)
    (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hball : ∀ w ∈ s, Metric.closedBall (w + β) r ⊆ Ω)
    (hsmall : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r, ‖Ψ u‖ ≤ (1 - L) * r)
    (hlip : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r, ‖deriv Ψ u‖ ≤ L) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H s ∧
      (∀ w ∈ s, H w ∈ Metric.closedBall (w + β) r ∧ H w = w + β - Ψ (H w)) ∧
      (∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) r, u = w + β - Ψ u → u = H w) := by
  -- the iterates stay in the ball
  have hbdd : ∀ n : ℕ, ∀ w ∈ s, picIter Ψ β n w ∈ Metric.closedBall (w + β) r := by
    intro n
    induction n with
    | zero =>
        intro w _
        simp only [picIter, Metric.mem_closedBall, dist_self]
        exact hr.le
    | succ n ih =>
        intro w hw
        show (fun w => w + β - Ψ (picIter Ψ β n w)) w ∈ Metric.closedBall (w + β) r
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : (w + β - Ψ (picIter Ψ β n w)) - (w + β) = -Ψ (picIter Ψ β n w) := by ring
        rw [h1, norm_neg]
        calc ‖Ψ (picIter Ψ β n w)‖ ≤ (1 - L) * r := hsmall w hw _ (ih w hw)
          _ ≤ r := by nlinarith [hL0, hr]
  -- `Ψ` is `L`-Lipschitz on each of the balls
  have hLip : ∀ w ∈ s, ∀ a ∈ Metric.closedBall (w + β) r, ∀ b ∈ Metric.closedBall (w + β) r,
      ‖Ψ a - Ψ b‖ ≤ L * ‖a - b‖ := by
    intro w hw a ha b hb
    exact Convex.norm_image_sub_le_of_norm_deriv_le (f := Ψ)
      (fun x hx => hΨ.differentiableAt (hΩ.mem_nhds (hball w hw hx)))
      (fun x hx => hlip w hw x hx) (convex_closedBall (w + β) r) hb ha
  -- one-step contraction estimate
  have hone : ∀ w ∈ s, ∀ n : ℕ,
      ‖picIter Ψ β (n + 1) w - picIter Ψ β n w‖ ≤ L ^ n * ((1 - L) * r) := by
    intro w hw n
    induction n with
    | zero =>
        show ‖(w + β - Ψ (picIter Ψ β 0 w)) - picIter Ψ β 0 w‖ ≤ L ^ 0 * ((1 - L) * r)
        have h1 : (w + β - Ψ (picIter Ψ β 0 w)) - picIter Ψ β 0 w = -Ψ (w + β) := by
          simp only [picIter]; ring
        rw [h1, norm_neg, pow_zero, one_mul]
        exact hsmall w hw (w + β) (by simp only [Metric.mem_closedBall, dist_self]; exact hr.le)
    | succ n ih =>
        show ‖(w + β - Ψ (picIter Ψ β (n + 1) w)) - (w + β - Ψ (picIter Ψ β n w))‖
          ≤ L ^ (n + 1) * ((1 - L) * r)
        have h1 : (w + β - Ψ (picIter Ψ β (n + 1) w)) - (w + β - Ψ (picIter Ψ β n w))
            = Ψ (picIter Ψ β n w) - Ψ (picIter Ψ β (n + 1) w) := by ring
        rw [h1]
        calc ‖Ψ (picIter Ψ β n w) - Ψ (picIter Ψ β (n + 1) w)‖
            ≤ L * ‖picIter Ψ β n w - picIter Ψ β (n + 1) w‖ :=
              hLip w hw _ (hbdd n w hw) _ (hbdd (n + 1) w hw)
          _ = L * ‖picIter Ψ β (n + 1) w - picIter Ψ β n w‖ := by rw [norm_sub_rev]
          _ ≤ L * (L ^ n * ((1 - L) * r)) := mul_le_mul_of_nonneg_left ih hL0
          _ = L ^ (n + 1) * ((1 - L) * r) := by rw [pow_succ]; ring
  -- geometric bound on the increments
  have hgeo : ∀ w ∈ s, ∀ k n : ℕ,
      ‖picIter Ψ β (n + k) w - picIter Ψ β n w‖ ≤ L ^ n * r := by
    intro w hw k
    induction k with
    | zero =>
        intro n
        rw [Nat.add_zero, sub_self, norm_zero]
        exact mul_nonneg (pow_nonneg hL0 n) hr.le
    | succ k ih =>
        intro n
        have hnk : n + (k + 1) = (n + 1) + k := by omega
        rw [hnk]
        calc ‖picIter Ψ β ((n + 1) + k) w - picIter Ψ β n w‖
            ≤ ‖picIter Ψ β ((n + 1) + k) w - picIter Ψ β (n + 1) w‖
                + ‖picIter Ψ β (n + 1) w - picIter Ψ β n w‖ := by
              have htri := dist_triangle (picIter Ψ β ((n + 1) + k) w)
                (picIter Ψ β (n + 1) w) (picIter Ψ β n w)
              rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
          _ ≤ L ^ (n + 1) * r + L ^ n * ((1 - L) * r) :=
              add_le_add (ih (n + 1)) (hone w hw n)
          _ = L ^ n * r := by rw [pow_succ]; ring
  -- the iterates are uniformly Cauchy on `s`
  have hcauchy : UniformCauchySeqOn (fun n => picIter Ψ β n) atTop s := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have htend : Tendsto (fun n : ℕ => L ^ n * r) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL1).mul_const r
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds hε))
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    rw [dist_eq_norm]
    rcases le_total n m with hnm | hmn
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact lt_of_le_of_lt (hgeo x hx k n) (hN n hn)
    · rw [norm_sub_rev]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact lt_of_le_of_lt (hgeo x hx k m) (hN m hm)
  -- the limit function
  let H : ℂ → ℂ := fun w => limUnder atTop (fun n => picIter Ψ β n w)
  have hHlim : ∀ w ∈ s, Tendsto (fun n => picIter Ψ β n w) atTop (nhds (H w)) := by
    intro w hw
    have hcw : CauchySeq (fun n => picIter Ψ β n w) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp hcauchy) ε hε
      exact ⟨N, fun m hm n hn => hN m hm n hn w hw⟩
    exact hcw.tendsto_limUnder
  have hHmem : ∀ w ∈ s, H w ∈ Metric.closedBall (w + β) r := fun w hw =>
    IsClosed.mem_of_tendsto Metric.isClosed_closedBall (hHlim w hw)
      (Eventually.of_forall (fun n => hbdd n w hw))
  have hHfix : ∀ w ∈ s, H w = w + β - Ψ (H w) := by
    intro w hw
    have hHΩ : H w ∈ Ω := hball w hw (hHmem w hw)
    have hcont : ContinuousAt Ψ (H w) :=
      (hΨ.differentiableAt (hΩ.mem_nhds hHΩ)).continuousAt
    have hlim1 : Tendsto (fun n => picIter Ψ β (n + 1) w) atTop (nhds (H w)) :=
      (tendsto_add_atTop_iff_nat 1).mpr (hHlim w hw)
    have hlim2 : Tendsto (fun n => w + β - Ψ (picIter Ψ β n w)) atTop
        (nhds (w + β - Ψ (H w))) :=
      (hcont.tendsto.comp (hHlim w hw)).const_sub (w + β)
    have heqfun : (fun n => picIter Ψ β (n + 1) w) = fun n => w + β - Ψ (picIter Ψ β n w) := by
      funext n; rw [show picIter Ψ β (n + 1) w = w + β - Ψ (picIter Ψ β n w) from rfl]
    rw [heqfun] at hlim1
    exact tendsto_nhds_unique hlim1 hlim2
  have hunif : TendstoUniformlyOn (fun n => picIter Ψ β n) H atTop s :=
    hcauchy.tendstoUniformlyOn_of_tendsto (fun w hw => hHlim w hw)
  have hGdiff : ∀ n : ℕ, DifferentiableOn ℂ (picIter Ψ β n) s := by
    intro n
    induction n with
    | zero => exact differentiableOn_id.add_const β
    | succ n ih =>
        show DifferentiableOn ℂ (fun w => w + β - Ψ (picIter Ψ β n w)) s
        exact (differentiableOn_id.add_const β).sub
          (hΨ.comp ih (fun w hw => hball w hw (hbdd n w hw)))
  have hHdiff : DifferentiableOn ℂ H s :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hGdiff) hs
  refine ⟨H, hHdiff, fun w hw => ⟨hHmem w hw, hHfix w hw⟩, ?_⟩
  -- uniqueness of the fixed point in the ball
  intro w hw u hu heq
  have hHu : u - H w = Ψ (H w) - Ψ u := by
    conv_lhs => rw [heq, hHfix w hw]
    ring
  have h1 : ‖u - H w‖ ≤ L * ‖u - H w‖ := by
    calc ‖u - H w‖ = ‖Ψ (H w) - Ψ u‖ := by rw [hHu]
      _ ≤ L * ‖H w - u‖ := hLip w hw (H w) (hHmem w hw) u hu
      _ = L * ‖u - H w‖ := by rw [norm_sub_rev]
  have h2 : ‖u - H w‖ = 0 := by
    have h3 : (1 - L) * ‖u - H w‖ ≤ 0 := by nlinarith [h1]
    have h4 : 0 < 1 - L := by linarith
    have h5 : 0 ≤ ‖u - H w‖ := norm_nonneg _
    nlinarith [h3, h4, h5]
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

/-! ## Two analytic tools -/

/-- **Cauchy estimate on a half-plane.**  A function holomorphic on `{Y < im}` and bounded there by
`B` has derivative bounded by `B / r` at every point `u` with `Y + r < im u` (so that the closed
ball of radius `r` about `u` stays inside the half-plane). -/
lemma halfplane_deriv_bound {g : ℂ → ℂ} {Y B r : ℝ} (hr : 0 < r)
    (hhol : DifferentiableOn ℂ g {z : ℂ | Y < z.im})
    (hbd : ∀ z : ℂ, Y < z.im → ‖g z‖ ≤ B) {u : ℂ} (hu : Y + r < u.im) :
    ‖deriv g u‖ ≤ B / r := by
  have hball : Metric.closedBall u r ⊆ {z : ℂ | Y < z.im} := by
    intro z hz
    show Y < z.im
    have h1 : ‖z - u‖ ≤ r := by
      have h := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at h
    have h2 := (abs_le.mp (Complex.abs_im_le_norm (z - u))).1
    rw [Complex.sub_im] at h2
    linarith
  have hdco : DiffContOnCl ℂ g (Metric.ball u r) :=
    DifferentiableOn.diffContOnCl_ball hhol hball
  have hC : ∀ z ∈ Metric.sphere u r, ‖g z‖ ≤ B := by
    intro z hz
    refine hbd z ?_
    show Y < z.im
    have h1 : ‖z - u‖ = r := by
      have h := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm] at h
    have h2 := (abs_le.mp (Complex.abs_im_le_norm (z - u))).1
    rw [Complex.sub_im] at h2
    linarith
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdco hC

/-- **Exponential decay at the upper end gives a limit.**  If `‖φ w - c‖` is dominated by
`M * exp (-2π (im w - Y - 1))` above `Y + 1`, then `φ` tends to `c` along the upper end. -/
lemma tendsto_upperEnd_of_decay {φ : ℂ → ℂ} {c : ℂ} {Y M : ℝ}
    (h : ∀ w : ℂ, Y + 1 ≤ w.im → ‖φ w - c‖ ≤ M * Real.exp (-2 * Real.pi * (w.im - Y - 1))) :
    Tendsto φ (Filter.comap Complex.im Filter.atTop) (nhds c) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (f := fun w : ℂ => ‖φ w - c‖)
    (g := fun w : ℂ => M * Real.exp (-2 * Real.pi * (w.im - Y - 1)))
    (Filter.Eventually.of_forall fun w => norm_nonneg _) ?_ ?_
  · filter_upwards [show {w : ℂ | Y + 1 ≤ w.im} ∈ Filter.comap Complex.im Filter.atTop from
      ⟨Set.Ici (Y + 1), Filter.Ici_mem_atTop (Y + 1), fun x hx => hx⟩] with w hw
    exact h w hw
  · have him : Tendsto (fun w : ℂ => w.im) (Filter.comap Complex.im Filter.atTop) Filter.atTop :=
      Filter.tendsto_comap
    have hinner : Tendsto (fun w : ℂ => 2 * Real.pi * (w.im - Y - 1))
        (Filter.comap Complex.im Filter.atTop) Filter.atTop := by
      have h1 : Tendsto (fun t : ℝ => t - (Y + 1)) Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right Filter.atTop (-(Y + 1)) tendsto_id
      have h2 := h1.const_mul_atTop (show (0 : ℝ) < 2 * Real.pi by positivity)
      have h3 := h2.comp him
      have heq : (fun w : ℂ => 2 * Real.pi * (w.im - Y - 1)) =
          fun w : ℂ => 2 * Real.pi * (w.im - (Y + 1)) := by
        funext w; ring
      rw [heq]
      simpa only [Function.comp_def] using h3
    have h4 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hinner).const_mul M
    simpa [Function.comp_def, mul_zero] using h4

/-! ## Smallness and flatness of the correction `u ↦ d.E u - u` at the upper end -/

/-- **Uniform smallness of the correction at the upper end**: for every `δ > 0` there is a depth
`R` with `‖d.E u - u‖ < δ` on the half-plane `{R < im u}` (`ParabData.E_upper`). -/
lemma E_sub_id_small {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ u : ℂ, R < u.im → ‖d.E u - u‖ < ε := by
  intro ε hε
  have h := d.E_upper.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)
  unfold MandelDim.upperEnd at h
  rw [Filter.eventually_iff] at h
  rw [Filter.mem_comap] at h
  obtain ⟨T, hT, hTsub⟩ := h
  obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.mp hT
  refine ⟨R, fun u hu => ?_⟩
  have huT : u.im ∈ T := hR u.im (le_of_lt hu)
  have hmem := hTsub huT
  rw [Set.mem_setOf_eq] at hmem
  rw [dist_eq_norm, sub_zero] at hmem
  simpa only [MandelDim.ParabData.E] using hmem

/-- **Holomorphy of the lifted horn map on a deep half-plane**, from the end inclusion of the horn
data (`{η < im} ⊆ Bu ⊆ DE`). -/
lemma E_differentiableOn_horn {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {Y : ℝ} (hY : hd.η < Y) :
    DifferentiableOn ℂ d.E {u : ℂ | Y < u.im} := by
  have hsub : {u : ℂ | Y < u.im} ⊆ d.DE := fun u hu =>
    hd.sub (Or.inl (hd.upper (lt_trans hY hu)))
  have hφ : DifferentiableOn ℂ d.φ {u : ℂ | Y < u.im} :=
    d.φ_holo.mono fun u hu => (hsub hu).1
  have hcomp : DifferentiableOn ℂ (d.Φ ∘ d.φ) {u : ℂ | Y < u.im} :=
    d.Φ_holo.comp hφ fun u hu => (hsub hu).2
  exact hcomp

/-- **Holomorphy of the correction on a deep half-plane** (`Y > η`). -/
lemma E_sub_id_differentiableOn {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {Y : ℝ} (hY : hd.η < Y) :
    DifferentiableOn ℂ (fun u : ℂ => d.E u - u) {u : ℂ | Y < u.im} :=
  (E_differentiableOn_horn d hd hY).sub differentiableOn_id

/-- **The correction `u ↦ d.E u - u` is small and flat on a deep half-plane.**  For `κ > 0` there is
a depth `Y > d.η₀`, `Y > η` with `‖d.E u - u‖ ≤ min (1/4) (κ/16)` for `Y < im u` and
`‖deriv (fun u => d.E u - u) u‖ ≤ min (1/4) (κ/16)` for `Y + 1 < im u`. -/
lemma correction_flat {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {κ : ℝ} (hκ : 0 < κ) :
    ∃ Y : ℝ, d.η₀ < Y ∧ hd.η < Y ∧
      DifferentiableOn ℂ (fun u : ℂ => d.E u - u) {u : ℂ | Y < u.im} ∧
      (∀ u : ℂ, Y < u.im → ‖d.E u - u‖ ≤ min (1 / 4) (κ / 16)) ∧
      (∀ u : ℂ, Y + 1 < u.im → ‖deriv (fun u : ℂ => d.E u - u) u‖ ≤ min (1 / 4) (κ / 16)) := by
  have hεpos : 0 < min (1 / 4) (κ / 16) := lt_min (by norm_num) (by linarith)
  obtain ⟨R₀, hR₀⟩ := E_sub_id_small d (min (1 / 4) (κ / 16)) hεpos
  refine ⟨max (R₀ + 2) (max (d.η₀ + 2) (hd.η + 2)), ?_, ?_, ?_, ?_, ?_⟩
  · have h := le_trans (le_max_left (d.η₀ + 2) (hd.η + 2)) (le_max_right (R₀ + 2) _)
    linarith
  · have h := le_trans (le_max_right (d.η₀ + 2) (hd.η + 2)) (le_max_right (R₀ + 2) _)
    linarith
  · refine E_sub_id_differentiableOn d hd ?_
    have h := le_trans (le_max_right (d.η₀ + 2) (hd.η + 2)) (le_max_right (R₀ + 2) _)
    linarith
  · intro u hu
    refine le_of_lt (hR₀ u ?_)
    have h := le_max_left (R₀ + 2) (max (d.η₀ + 2) (hd.η + 2))
    linarith
  · intro u hu
    set Y : ℝ := max (R₀ + 2) (max (d.η₀ + 2) (hd.η + 2)) with hYdef
    have hYR : R₀ < Y - 1 := by
      have h := le_max_left (R₀ + 2) (max (d.η₀ + 2) (hd.η + 2))
      rw [hYdef]; linarith
    have hYη : hd.η < Y - 1 := by
      have h := le_trans (le_max_right (d.η₀ + 2) (hd.η + 2)) (le_max_right (R₀ + 2) _)
      rw [hYdef]; linarith
    have hhol : DifferentiableOn ℂ (fun u : ℂ => d.E u - u) {z : ℂ | Y - 1 < z.im} :=
      E_sub_id_differentiableOn d hd hYη
    have hbd : ∀ z : ℂ, Y - 1 < z.im →
        ‖(fun u : ℂ => d.E u - u) z‖ ≤ min (1 / 4) (κ / 16) := by
      intro z hz
      refine le_of_lt (hR₀ z ?_)
      linarith
    have hu' : (Y - 1) + 1 < u.im := by rw [hYdef] at hu; linarith
    have h := halfplane_deriv_bound (g := fun u : ℂ => d.E u - u) (Y := Y - 1)
      (B := min (1 / 4) (κ / 16)) (r := 1) (by norm_num) hhol hbd hu'
    rwa [div_one] at h

/-! ## The perturbed inverse branch -/

theorem perturbed_branch {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {κ : ℝ} (hκ : 0 < κ) (hβ : κ ≤ Complex.im β)
    {y₁ : ℝ} {H₀ ρ₀ : ℂ → ℂ} {y₀' : ℝ} (hy : y₁ ≤ y₀')
    (hH₀d : DifferentiableOn ℂ H₀ {w : ℂ | y₀' < Complex.im w})
    (hH₀ : ∀ w : ℂ, y₀' < Complex.im w → y₁ < Complex.im (H₀ w) ∧ H₀ w ∈ hd.Bu ∧
      d.E (H₀ w) - β = w)
    (hinc₀ : ∀ w : ℂ, y₀' < Complex.im w → H₀ w = w + β + ρ₀ w)
    (hρ₀d : DifferentiableOn ℂ ρ₀ {w : ℂ | y₀' < Complex.im w})
    (hρ₀bd : ∀ w : ℂ, y₀' < Complex.im w → ‖ρ₀ w‖ ≤ κ / 4)
    (hdrift₀ : ∀ w : ℂ, y₀' < Complex.im w → κ / 2 ≤ Complex.im (H₀ w - w))
    {R : ℂ → ℂ} {DR : Set ℂ} (hDRo : IsOpen DR) (hTeq : MandelDim.IsTEquivariantOn R DR)
    (hRhol : DifferentiableOn ℂ R DR) (hDRmem : ∀ w : ℂ, y₁ < Complex.im w → w ∈ DR)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ ≤ κ / 16)
    (hclose : ∀ w : ℂ, y₁ < Complex.im w → ‖R w - d.E w‖ ≤ δ)
    (hclose' : ∀ w : ℂ, y₁ + 1 < Complex.im w →
      ‖deriv (fun u => R u - d.E u) w‖ ≤ δ) :
    ∃ (H : ℂ → ℂ) (ρ : ℂ → ℂ) (y'' : ℝ) (c : ℂ), y₀' ≤ y'' ∧
      DifferentiableOn ℂ H {w : ℂ | y'' < Complex.im w} ∧
      (∀ w : ℂ, y'' < Complex.im w → y₁ < Complex.im (H w) ∧ H w ∈ DR ∧ R (H w) - β = w ∧
        H w = w + β + ρ w) ∧
      DifferentiableOn ℂ ρ {w : ℂ | y'' < Complex.im w} ∧
      (∀ w : ℂ, y'' < Complex.im w → ρ (w + 1) = ρ w) ∧
      (∀ w : ℂ, y'' < Complex.im w → ‖ρ w‖ ≤ κ / 2) ∧
      (∀ w : ℂ, y'' < Complex.im w → κ / 4 ≤ Complex.im (H w - w)) ∧
      Set.InjOn H {w : ℂ | y'' < Complex.im w} ∧
      Filter.Tendsto ρ (Filter.comap Complex.im Filter.atTop) (nhds c) := by
  obtain ⟨Y₀, hY₀η, hY₀ηh, hEhol, hEsmall, hEderiv⟩ := correction_flat d hd hκ
  set b₁ : ℝ := max y₁ hd.η with hb₁def
  have hb₁y₁ : y₁ ≤ b₁ := le_max_left _ _
  have hb₁η : hd.η ≤ b₁ := le_max_right _ _
  set Y : ℝ := max (max (Y₀ + 1) (b₁ + 8 * δ + 1)) (y₁ + 1) with hYdef
  have hY1 : Y₀ + 1 ≤ Y := le_trans (le_max_left _ _) (le_max_left _ _)
  have hY2 : b₁ + 8 * δ + 1 ≤ Y := le_trans (le_max_right _ _) (le_max_left _ _)
  have hY3 : y₁ + 1 ≤ Y := le_max_right _ _
  -- the deep half-plane `Ω` in the `u`-variable, the target region `s` for the branch
  set Ω : Set ℂ := {u : ℂ | Y < u.im} with hΩdef
  set s : Set ℂ := {w : ℂ | Y + κ / 4 < (w + β).im} with hsdef
  have hΩopen : IsOpen Ω := by
    rw [hΩdef]; exact isOpen_lt continuous_const Complex.continuous_im
  have hsopen : IsOpen s := by
    rw [hsdef]
    exact isOpen_lt continuous_const
      (Complex.continuous_im.comp (continuous_id.add continuous_const))
  have hmemΩ : ∀ u : ℂ, u ∈ Ω ↔ Y < u.im := by intro u; rw [hΩdef]; exact Iff.rfl
  have hmems : ∀ w : ℂ, w ∈ s ↔ Y + κ / 4 < (w + β).im := by
    intro w; rw [hsdef]; exact Iff.rfl
  -- `R` and `d.E` are holomorphic on the deep half-plane
  have hRΩ : DifferentiableOn ℂ R Ω := by
    refine hRhol.mono fun u hu => hDRmem u ?_
    have h := (hmemΩ u).mp hu
    linarith
  have hEΩ : DifferentiableOn ℂ d.E Ω := by
    rw [hΩdef]
    exact E_differentiableOn_horn d hd (by linarith)
  have hηhol : DifferentiableOn ℂ (fun z : ℂ => R z - d.E z) Ω := hRΩ.sub hEΩ
  have hηbd : ∀ z : ℂ, z ∈ Ω → ‖R z - d.E z‖ ≤ δ := by
    intro z hz
    refine hclose z ?_
    have h := (hmemΩ z).mp hz
    linarith
  set Ψ : ℂ → ℂ := fun u => R u - u with hΨdef
  have hΨΩ : DifferentiableOn ℂ Ψ Ω := by
    rw [hΨdef]; exact hRΩ.sub differentiableOn_id
  have hΨsmall : ∀ u ∈ Ω, ‖Ψ u‖ ≤ (1 - 1 / 2) * (κ / 4) := by
    intro u hu
    have hu' : Y < u.im := (hmemΩ u).mp hu
    have h1 : ‖R u - d.E u‖ ≤ δ := hηbd u hu
    have h2 : ‖d.E u - u‖ ≤ min (1 / 4) (κ / 16) := hEsmall u (by linarith)
    have h3 : ‖R u - u‖ ≤ δ + min (1 / 4) (κ / 16) := by
      have hsplit : R u - u = (R u - d.E u) + (d.E u - u) := by ring
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    rw [hΨdef]
    refine h3.trans ?_
    have h4 : min (1 / 4) (κ / 16) ≤ κ / 16 := min_le_right _ _
    nlinarith [hδκ, hκ]
  have hΨderiv : ∀ u ∈ Ω, ‖deriv Ψ u‖ ≤ 1 / 2 := by
    intro u hu
    have hu' : Y < u.im := (hmemΩ u).mp hu
    have hfun : Ψ = (fun z : ℂ => R z - d.E z) + (fun z : ℂ => d.E z - z) := by
      funext z
      rw [hΨdef]
      simp only [Pi.add_apply]
      ring
    have hdη : DifferentiableAt ℂ (fun z : ℂ => R z - d.E z) u :=
      hηhol.differentiableAt (hΩopen.mem_nhds hu)
    have hdE' : DifferentiableAt ℂ (fun z : ℂ => d.E z - z) u :=
      (hEΩ.differentiableAt (hΩopen.mem_nhds hu)).sub differentiableAt_id
    have hderiv : deriv Ψ u =
        deriv (fun z : ℂ => R z - d.E z) u + deriv (fun z : ℂ => d.E z - z) u := by
      rw [hfun, deriv_add hdη hdE']
    have hb₁_lt : b₁ < u.im := by linarith
    have hηhol' : DifferentiableOn ℂ (fun z : ℂ => R z - d.E z) {z : ℂ | b₁ < z.im} := by
      have hR' : DifferentiableOn ℂ R {z : ℂ | b₁ < z.im} :=
        hRhol.mono fun z hz => hDRmem z (by have hz' : b₁ < z.im := hz; linarith)
      have hE' : DifferentiableOn ℂ d.E {z : ℂ | b₁ < z.im} := by
        have hsub2 : {z : ℂ | b₁ < z.im} ⊆ d.DE := fun z hz =>
          hd.sub (Or.inl (hd.upper (lt_of_le_of_lt hb₁η (show b₁ < z.im from hz))))
        have hφ2 : DifferentiableOn ℂ d.φ {z : ℂ | b₁ < z.im} :=
          d.φ_holo.mono fun z hz => (hsub2 hz).1
        exact d.Φ_holo.comp hφ2 fun z hz => (hsub2 hz).2
      exact hR'.sub hE'
    have hηbd' : ∀ z : ℂ, b₁ < z.im → ‖R z - d.E z‖ ≤ δ := by
      intro z hz
      refine hclose z ?_
      linarith
    have hηderiv : ‖deriv (fun z : ℂ => R z - d.E z) u‖ ≤ δ / ((u.im - b₁) / 2) :=
      halfplane_deriv_bound (by linarith) hηhol' hηbd' (by linarith)
    have hE'deriv : ‖deriv (fun z : ℂ => d.E z - z) u‖ ≤ min (1 / 4) (κ / 16) :=
      hEderiv u (by linarith)
    have hq : δ / ((u.im - b₁) / 2) ≤ 1 / 4 := by
      have hpos : 0 < (u.im - b₁) / 2 := by linarith
      have h8 : 8 * δ + 1 ≤ u.im - b₁ := by linarith
      rw [div_le_iff₀ hpos]
      nlinarith [hδ, h8]
    rw [hderiv]
    refine (norm_add_le _ _).trans ?_
    have hmin : min (1 / 4) (κ / 16) ≤ 1 / 4 := min_le_left _ _
    linarith
  -- the deep ball of the contraction stays inside the deep half-plane
  have hball : ∀ w ∈ s, Metric.closedBall (w + β) (κ / 4) ⊆ Ω := by
    intro w hw u hu
    rw [hmemΩ]
    have h1 : ‖u - (w + β)‖ ≤ κ / 4 := by
      have h := Metric.mem_closedBall.mp hu
      rwa [dist_eq_norm] at h
    have h2 := (abs_le.mp (Complex.abs_im_le_norm (u - (w + β)))).1
    rw [Complex.sub_im] at h2
    have h3 : Y + κ / 4 < (w + β).im := (hmems w).mp hw
    linarith
  obtain ⟨H, hHdiff, hHfix, hHuniq⟩ :=
    contraction_fixed_point_holomorphic_tmp (s := s) (Ω := Ω) (Ψ := Ψ) (β := β)
      (r := κ / 4) (L := 1 / 2) hsopen hΩopen hΨΩ (by linarith) (by norm_num)
      (by norm_num) hball
      (fun w hw u hu => hΨsmall u (hball w hw hu))
      (fun w hw u hu => hΨderiv u (hball w hw hu))
  -- consequences of the fixed point equation
  have hH_eq : ∀ w ∈ s, R (H w) = w + β := by
    intro w hw
    have h2 : H w = w + β - Ψ (H w) := (hHfix w hw).2
    rw [hΨdef] at h2
    have h5 : H w + (R (H w) - H w) = R (H w) := by ring
    have h3 : H w + (R (H w) - H w) = w + β := by
      nth_rewrite 1 [h2]; ring
    rwa [h5] at h3
  have hHmem_ball : ∀ w ∈ s, H w ∈ Metric.closedBall (w + β) (κ / 4) :=
    fun w hw => (hHfix w hw).1
  have hHimeq : ∀ w ∈ s, (w + β).im - κ / 4 ≤ (H w).im := by
    intro w hw
    have h := Metric.mem_closedBall.mp (hHmem_ball w hw)
    rw [dist_eq_norm] at h
    have h2 := (abs_le.mp (Complex.abs_im_le_norm (H w - (w + β)))).1
    rw [Complex.sub_im] at h2
    linarith
  have hHDR : ∀ w ∈ s, H w ∈ DR := by
    intro w hw
    refine hDRmem (H w) ?_
    have h1 := hHimeq w hw
    have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hw
    linarith
  -- `H` is equivariant (`T w = w + 1`), by uniqueness of the fixed point
  have hHper : ∀ w ∈ s, H (w + 1) = H w + 1 := by
    intro w hw
    have hw1 : w + 1 ∈ s := by
      refine (hmems (w + 1)).mpr ?_
      have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hw
      have h3 : (w + 1 + β).im = (w + β).im := by
        rw [show w + 1 + β = (w + β) + 1 by ring, Complex.add_im, Complex.one_im, add_zero]
      rw [h3]
      exact h2
    have hu_mem : H w + 1 ∈ Metric.closedBall (w + 1 + β) (κ / 4) := by
      have h : ‖H w - (w + β)‖ ≤ κ / 4 := by
        have h := Metric.mem_closedBall.mp (hHmem_ball w hw)
        rwa [dist_eq_norm] at h
      rw [Metric.mem_closedBall, dist_eq_norm]
      have he : H w + 1 - (w + 1 + β) = H w - (w + β) := by ring
      rw [he]; exact h
    have hfixpt : H w + 1 = (w + 1) + β - Ψ (H w + 1) := by
      have hR1 : R (H w + 1) = R (H w) + 1 := hTeq.2 (H w) (hHDR w hw)
      have hRw : R (H w) = w + β := hH_eq w hw
      rw [hΨdef]
      show H w + 1 = (w + 1) + β - (R (H w + 1) - (H w + 1))
      rw [hR1, hRw]
      ring
    exact (hHuniq (w + 1) hw1 (H w + 1) hu_mem hfixpt).symm
  -- the shrunken half-plane and the increment `ρ`
  set y'' : ℝ := max y₀' (Y + κ / 4 - β.im + 1) with hy''def
  have hy''_ge : y₀' ≤ y'' := le_max_left _ _
  have hsub_s : {w : ℂ | y'' < w.im} ⊆ s := by
    intro w hw
    refine (hmems w).mpr ?_
    have hw' : y'' < w.im := hw
    have h1 : Y + κ / 4 - β.im + 1 ≤ y'' := le_max_right _ _
    have h2 : Y + κ / 4 < w.im + β.im := by linarith
    rwa [Complex.add_im]
  set ρ : ℂ → ℂ := fun w => H w - w - β with hρdef
  have hρhol : DifferentiableOn ℂ ρ {w : ℂ | y'' < w.im} := by
    rw [hρdef]
    have he : (fun w : ℂ => H w - w - β) = fun w : ℂ => H w - (w + β) := by funext w; ring
    rw [he]
    exact (hHdiff.mono fun w hw => hsub_s hw).sub (differentiableOn_id.add_const β)
  have hρper : ∀ w : ℂ, y'' < w.im → ρ (w + 1) = ρ w := by
    intro w hw
    have hws : w ∈ s := hsub_s hw
    have hws1 : w + 1 ∈ s := by
      refine (hmems (w + 1)).mpr ?_
      have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hws
      have h3 : (w + 1 + β).im = (w + β).im := by
        rw [show w + 1 + β = (w + β) + 1 by ring, Complex.add_im, Complex.one_im, add_zero]
      rw [h3]
      exact h2
    simp only [hρdef]
    rw [hHper w hws]
    ring
  have hρbd : ∀ w : ℂ, y'' < w.im → ‖ρ w‖ ≤ κ / 4 := by
    intro w hw
    have h : ‖H w - (w + β)‖ ≤ κ / 4 := by
      have h := Metric.mem_closedBall.mp (hHmem_ball w (hsub_s hw))
      rwa [dist_eq_norm] at h
    have he : ρ w = H w - (w + β) := by simp only [hρdef]; ring
    rw [he]
    exact h
  -- the limit of `ρ` at the upper end
  obtain ⟨c, M, hdecay⟩ := end_fourier (φ := ρ) (Y := y'' + 1) (B := κ / 4)
    (fun w hw => hρper w (by linarith))
    (hρhol.mono (fun w hw => by
      rw [Set.mem_setOf_eq] at hw ⊢
      linarith))
    (fun w hw => hρbd w (by linarith))
  have hlim : Tendsto ρ (Filter.comap Complex.im Filter.atTop) (nhds c) :=
    tendsto_upperEnd_of_decay hdecay
  refine ⟨H, ρ, y'', c, hy''_ge, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlim⟩
  · exact hHdiff.mono (fun w hw => hsub_s hw)
  · intro w hw
    have hws : w ∈ s := hsub_s hw
    have h1 : Y < (H w).im := by
      have h := hHimeq w hws
      have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hws
      linarith
    refine ⟨by linarith, hHDR w hws, ?_, ?_⟩
    · rw [hH_eq w hws]; ring
    · rw [hρdef]; ring
  · exact hρhol
  · exact hρper
  · intro w hw
    refine le_trans (hρbd w hw) ?_
    linarith
  · intro w hw
    have hb := hρbd w hw
    have he : H w - w = β + ρ w := by rw [hρdef]; ring
    rw [he, Complex.add_im]
    have h2 := (abs_le.mp (Complex.abs_im_le_norm (ρ w))).1
    linarith
  · intro w hw w' hw' heq
    have h1 : R (H w) - β = w := by rw [hH_eq w (hsub_s hw)]; ring
    have h2 : R (H w') - β = w' := by rw [hH_eq w' (hsub_s hw')]; ring
    rw [← h1, ← h2, heq]

end

end Work.L62
