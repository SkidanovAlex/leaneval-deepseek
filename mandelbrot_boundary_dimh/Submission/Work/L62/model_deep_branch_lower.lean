import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.end_fourier
import Submission.Work.Horn.basic
import Submission.Work.L62.E_equivariant_of_eta0
import Submission.Work.L62.march_down_im_le_cl

namespace Work.L62

open MandelDim Filter Topology Complex Set
open scoped Topology

noncomputable section

/-! ## Generic lower-end (`im → -∞`) filter lemmas -/

/-- A predicate is eventually true along the lower end iff it holds on a deep half-plane. -/
lemma lowerEnd_eventually {P : ℂ → Prop} (h : {w : ℂ | P w} ∈ MandelDim.lowerEnd) :
    ∃ T : ℝ, ∀ w : ℂ, w.im < -T → P w := by
  rw [MandelDim.lowerEnd, Filter.mem_comap] at h
  obtain ⟨t, ht, hts⟩ := h
  rw [Filter.mem_atBot_sets] at ht
  obtain ⟨R, hR⟩ := ht
  refine ⟨-R, fun w hw => hts (hR w.im ?_)⟩
  have h1 : w.im < R := by linarith
  exact le_of_lt h1

/-- Sufficient condition for convergence to `a` along the lower end. -/
lemma tendsto_lowerEnd_of_deep {f : ℂ → ℂ} {a : ℂ}
    (h : ∀ ε > 0, ∃ T : ℝ, ∀ w : ℂ, w.im < -T → ‖f w - a‖ < ε) :
    Tendsto f MandelDim.lowerEnd (𝓝 a) := by
  rw [MandelDim.lowerEnd, Filter.tendsto_def]
  intro s hs
  rw [Filter.mem_comap]
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hεs⟩ := hs
  obtain ⟨T, hT⟩ := h ε hε
  refine ⟨Set.Iic (-(T + 1)), ?_, ?_⟩
  · rw [Filter.mem_atBot_sets]; exact ⟨-(T + 1), fun b hb => hb⟩
  · intro w hw
    have hw' : w.im ≤ -(T + 1) := hw
    refine hεs (by rw [Metric.mem_ball, dist_eq_norm]; exact hT w (by linarith))

/-! ## The Cauchy estimate on a deep half-plane -/

/-- **Cauchy estimate on a deep half-plane.**  If `ψ` is holomorphic on `{v | v.im < -Y0}` and
tends to `0` at the lower end, then `‖deriv ψ‖ ≤ ε` on a sufficiently deep half-plane. -/
lemma deep_psi_deriv_bound {ψ : ℂ → ℂ} {Y0 ε : ℝ}
    (hψ : DifferentiableOn ℂ ψ {v : ℂ | v.im < -Y0})
    (hend : Tendsto ψ MandelDim.lowerEnd (𝓝 0)) (hε : 0 < ε) :
    ∃ Y : ℝ, Y0 + 1 ≤ Y ∧ ∀ v : ℂ, v.im < -Y → ‖deriv ψ v‖ ≤ ε := by
  have h0 : {z : ℂ | ‖ψ z‖ < ε} ∈ MandelDim.lowerEnd := by
    have hmem : Metric.ball (0 : ℂ) ε ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hε
    have h1 := hend hmem
    rw [Filter.mem_map] at h1
    refine Filter.mem_of_superset h1 ?_
    intro z hz
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
  obtain ⟨T, hT⟩ := lowerEnd_eventually h0
  refine ⟨max (Y0 + 1) (T + 1), le_max_left _ _, fun v hv => ?_⟩
  have hv01 : v.im < -(Y0 + 1) := by
    have := le_max_left (Y0 + 1) (T + 1)
    linarith
  have hvT1 : v.im < -(T + 1) := by
    have := le_max_right (Y0 + 1) (T + 1)
    linarith
  have hsub : Metric.closedBall v 1 ⊆ {z : ℂ | z.im < -Y0} := by
    intro z hz
    have h1 : ‖z - v‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    have h2 : z.im ≤ v.im + ‖z - v‖ := by
      have h3 := Complex.im_le_norm (z - v)
      rw [Complex.sub_im] at h3
      linarith
    show z.im < -Y0
    linarith
  have hcd : Complex.cderiv 1 ψ v = deriv ψ v :=
    Complex.cderiv_eq_deriv (U := {z : ℂ | z.im < -Y0}) (f := ψ) (z := v) (r := 1)
      (isOpen_lt (f := Complex.im) (g := fun _ : ℂ => -Y0) Complex.continuous_im continuous_const)
      hψ (by norm_num) hsub
  rw [← hcd]
  have hb : ‖Complex.cderiv 1 ψ v‖ ≤ ε / 1 :=
    Complex.norm_cderiv_le (z := v) (r := 1) (M := ε) (f := ψ) (by norm_num) (fun w hw => by
      have hwd : w.im < -T := by
        rw [Metric.mem_sphere, dist_eq_norm] at hw
        have h2 : w.im ≤ v.im + ‖w - v‖ := by
          have h3 := Complex.im_le_norm (w - v)
          rw [Complex.sub_im] at h3
          linarith
        have h4 : ‖w - v‖ = 1 := hw
        linarith
      exact (hT w hwd).le)
  simpa using hb

/-! ## The analytic core: the downward inverse branch -/

/-- **The downward inverse branch on a deep half-plane (analytic core).**  Let `ψ` be holomorphic
on `{v | v.im < -Y}`, `1`-periodic there, with `‖ψ‖ ≤ κ/4`, `‖deriv ψ‖ ≤ 1/2` there and `ψ → 0`
at the lower end.  If `Complex.im (β - cl) ≤ -κ` (`κ > 0`) then the fixed point equation
`H w = w + (β - cl) - ψ (H w)` has a holomorphic solution `H` on a deeper half-plane
`{w | w.im < -y'}` (`y' ≥ Y + 1`), whose increment `ρ w = H w - (w + (β - cl))` satisfies
`ρ w = -ψ (H w)`, is `1`-periodic, bounded by `κ/2`, tends to `0` at the lower end; `H` maps into
`{w | w.im < -Y}` and is injective, and `H w - w` drifts downwards by at least `κ/2`. -/
lemma deep_branch_analytic {ψ : ℂ → ℂ} {Y : ℝ} {κ : ℝ} {β : ℂ} {cl : ℂ}
    (hκ : 0 < κ) (hdrift : Complex.im (β - cl) ≤ -κ)
    (hψ_diff : DifferentiableOn ℂ ψ {v : ℂ | Complex.im v < -Y})
    (hψ_per : ∀ v : ℂ, Complex.im v < -Y → ψ (v + 1) = ψ v)
    (hψ_bd : ∀ v : ℂ, Complex.im v < -Y → ‖ψ v‖ ≤ κ / 4)
    (hψ_deriv : ∀ v : ℂ, Complex.im v < -Y → ‖deriv ψ v‖ ≤ 1 / 2)
    (hψ_end : Filter.Tendsto ψ MandelDim.lowerEnd (nhds 0)) :
    ∃ (H : ℂ → ℂ) (ρ : ℂ → ℂ) (y' : ℝ), Y + 1 ≤ y' ∧
      DifferentiableOn ℂ H {w : ℂ | Complex.im w < -y'} ∧
      DifferentiableOn ℂ ρ {w : ℂ | Complex.im w < -y'} ∧
      (∀ w : ℂ, Complex.im w < -y' → H w = w + (β - cl) + ρ w) ∧
      (∀ w : ℂ, Complex.im w < -y' → ρ w = -ψ (H w)) ∧
      (∀ w : ℂ, Complex.im w < -y' → Complex.im (H w) < -Y) ∧
      (∀ w : ℂ, Complex.im w < -y' → ρ (w + 1) = ρ w) ∧
      (∀ w : ℂ, Complex.im w < -y' → ‖ρ w‖ ≤ κ / 2) ∧
      (∀ w : ℂ, Complex.im w < -y' → Complex.im (H w - w) ≤ -(κ / 2)) ∧
      Set.InjOn H {w : ℂ | Complex.im w < -y'} ∧
      Filter.Tendsto ρ (Filter.comap Complex.im Filter.atBot) (nhds 0) := by
  have hYc : -Y - (3 * κ / 4 + 1) < -Y := by linarith
  let M : ℂ → ℂ := fun w => w + (β - cl)
  let step : (ℂ → ℂ) → (ℂ → ℂ) := fun F w => M w - ψ (F w)
  let Hseq : ℕ → ℂ → ℂ := fun n => Nat.rec M (fun _ F => step F) n
  have hH0 : Hseq 0 = M := rfl
  have hHs : ∀ n : ℕ, Hseq (n + 1) = step (Hseq n) := fun n => rfl
  have hHval : ∀ n : ℕ, ∀ w : ℂ, Hseq (n + 1) w = M w - ψ (Hseq n w) := by
    intro n w
    show step (Hseq n) w = M w - ψ (Hseq n w)
    rfl
  have hMdiff : DifferentiableOn ℂ M {w : ℂ | w.im < -(Y + 1)} := by
    show DifferentiableOn ℂ (fun w : ℂ => w + (β - cl)) _
    exact differentiableOn_id.add (differentiableOn_const (β - cl))
  -- (A) the orbit stays in the closed half-plane `{im ≤ -Y - (3κ/4+1)}`
  have hmem : ∀ n : ℕ, ∀ w : ℂ, w.im < -(Y + 1) → (Hseq n w).im ≤ -Y - (3 * κ / 4 + 1) := by
    intro n
    induction n with
    | zero =>
        intro w hw
        show (M w).im ≤ -Y - (3 * κ / 4 + 1)
        show (w + (β - cl)).im ≤ -Y - (3 * κ / 4 + 1)
        rw [Complex.add_im]
        linarith
    | succ n ih =>
        intro w hw
        rw [hHval n w, Complex.sub_im]
        have h1 : (Hseq n w).im < -Y := lt_of_le_of_lt (ih w hw) hYc
        have h2 : -((ψ (Hseq n w)).im) ≤ κ / 4 := by
          have ha := Complex.abs_im_le_norm (ψ (Hseq n w))
          have hb : -((ψ (Hseq n w)).im) ≤ |(ψ (Hseq n w)).im| := neg_le_abs _
          have hc := hψ_bd _ h1
          linarith
        have h3 : (M w).im ≤ w.im - κ := by
          show (w + (β - cl)).im ≤ w.im - κ
          rw [Complex.add_im]
          linarith
        linarith
  -- (B) `ψ` is a `1/2`-contraction on the closed half-plane
  have hcontr : ∀ a b : ℂ, a.im ≤ -Y - (3 * κ / 4 + 1) → b.im ≤ -Y - (3 * κ / 4 + 1) →
      ‖ψ b - ψ a‖ ≤ (1 / 2) * ‖b - a‖ := by
    intro a b ha hb
    refine Convex.norm_image_sub_le_of_norm_deriv_le (s := {v : ℂ | v.im ≤ -Y - (3 * κ / 4 + 1)})
      ?_ ?_ (convex_halfSpace_im_le _) ha hb
    · intro x hx
      have hx1 : x.im ≤ -Y - (3 * κ / 4 + 1) := hx
      have hx2 : x.im < -Y := by linarith
      have hx3 : x ∈ {v : ℂ | v.im < -Y} := hx2
      exact hψ_diff.differentiableAt
        ((isOpen_lt (f := Complex.im) (g := fun _ : ℂ => -Y) Complex.continuous_im
          continuous_const).mem_nhds hx3)
    · intro x hx
      have hx1 : x.im ≤ -Y - (3 * κ / 4 + 1) := hx
      refine hψ_deriv x ?_
      show x.im < -Y
      linarith
  -- (C) geometric decay of the successive differences
  have hbdseq : ∀ n : ℕ, ∀ w : ℂ, w.im < -(Y + 1) →
      ‖Hseq (n + 1) w - Hseq n w‖ ≤ (κ / 4) * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
        intro w hw
        have hMw : (M w).im ≤ -Y - (3 * κ / 4 + 1) := by
          show (w + (β - cl)).im ≤ -Y - (3 * κ / 4 + 1)
          rw [Complex.add_im]
          linarith
        have hbd : ‖ψ (M w)‖ ≤ κ / 4 := hψ_bd _ (lt_of_le_of_lt hMw hYc)
        have he : Hseq (0 + 1) w - Hseq 0 w = -(ψ (M w)) := by
          rw [hHval 0 w, hH0]
          show (M w - ψ (M w)) - M w = -(ψ (M w))
          ring
        rw [he, norm_neg, pow_zero, mul_one]
        exact hbd
    | succ n ih =>
        intro w hw
        have h1 : (Hseq (n + 1) w).im ≤ -Y - (3 * κ / 4 + 1) := hmem (n + 1) w hw
        have h2 : (Hseq n w).im ≤ -Y - (3 * κ / 4 + 1) := hmem n w hw
        have hc2 := hcontr (Hseq (n + 1) w) (Hseq n w) h1 h2
        have he : Hseq (n + 1 + 1) w - Hseq (n + 1) w
            = ψ (Hseq n w) - ψ (Hseq (n + 1) w) := by
          rw [hHval (n + 1) w, hHval n w]
          show (M w - ψ (Hseq (n + 1) w)) - (M w - ψ (Hseq n w))
              = ψ (Hseq n w) - ψ (Hseq (n + 1) w)
          ring
        rw [he]
        have hb := ih w hw
        calc ‖ψ (Hseq n w) - ψ (Hseq (n + 1) w)‖
            ≤ (1 / 2) * ‖Hseq n w - Hseq (n + 1) w‖ := hc2
          _ = (1 / 2) * ‖Hseq (n + 1) w - Hseq n w‖ := by rw [norm_sub_rev]
          _ ≤ (1 / 2) * ((κ / 4) * (1 / 2) ^ n) :=
                mul_le_mul_of_nonneg_left hb (by norm_num)
          _ = (κ / 4) * (1 / 2) ^ (n + 1) := by rw [pow_succ]; ring
  -- (D) the orbit consists of holomorphic functions
  have hdiffseq : ∀ n : ℕ, DifferentiableOn ℂ (Hseq n) {w : ℂ | w.im < -(Y + 1)} := by
    intro n
    induction n with
    | zero =>
        show DifferentiableOn ℂ M {w : ℂ | w.im < -(Y + 1)}
        exact hMdiff
    | succ n ih =>
        show DifferentiableOn ℂ (step (Hseq n)) {w : ℂ | w.im < -(Y + 1)}
        show DifferentiableOn ℂ (fun w : ℂ => M w - ψ (Hseq n w)) {w : ℂ | w.im < -(Y + 1)}
        exact hMdiff.sub (hψ_diff.comp ih (fun w hw => lt_of_le_of_lt (hmem n w hw) hYc))
  -- (E) the uniform limit
  have hu : Summable (fun n : ℕ => (κ / 4) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left (κ / 4)
  let G : ℂ → ℂ := fun w => ∑' n : ℕ, (Hseq (n + 1) w - Hseq n w)
  have hGdiff : DifferentiableOn ℂ G {w : ℂ | w.im < -(Y + 1)} := by
    show DifferentiableOn ℂ (fun w => ∑' n : ℕ, (Hseq (n + 1) w - Hseq n w)) _
    exact Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => Hseq (n + 1) w - Hseq n w)
      (u := fun n => (κ / 4) * (1 / 2 : ℝ) ^ n) hu
      (fun n => (hdiffseq (n + 1)).sub (hdiffseq n))
      (isOpen_lt (f := Complex.im) (g := fun _ : ℂ => -(Y + 1)) Complex.continuous_im
        continuous_const)
      (fun n w hw => hbdseq n w hw)
  let H : ℂ → ℂ := fun w => M w + G w
  have hHdiff : DifferentiableOn ℂ H {w : ℂ | w.im < -(Y + 1)} := by
    show DifferentiableOn ℂ (fun w => M w + G w) _
    exact hMdiff.add hGdiff
  have hHtend : ∀ w : ℂ, w.im < -(Y + 1) → Tendsto (fun N : ℕ => Hseq N w) atTop (nhds (H w)) := by
    intro w hw
    have hsummable : Summable (fun n : ℕ => Hseq (n + 1) w - Hseq n w) :=
      Summable.of_norm_bounded hu (fun n => hbdseq n w hw)
    have hsum : HasSum (fun n : ℕ => Hseq (n + 1) w - Hseq n w) (G w) := hsummable.hasSum
    have htel : ∀ N : ℕ, ∑ n ∈ Finset.range N, (Hseq (n + 1) w - Hseq n w)
        = Hseq N w - M w := by
      intro N
      induction N with
      | zero => simp [hH0]
      | succ N ih =>
          rw [Finset.sum_range_succ, ih, hHval N w]
          ring
    have h1 : Tendsto (fun N : ℕ => Hseq N w - M w) atTop (nhds (G w)) := by
      have h := hsum.tendsto_sum_nat
      simpa only [htel] using h
    have h2 : Tendsto (fun N : ℕ => Hseq N w) atTop (nhds (M w + G w)) := by
      have h3 : Tendsto (fun N : ℕ => M w + (Hseq N w - M w)) atTop (nhds (M w + G w)) :=
        h1.const_add (M w)
      exact Filter.Tendsto.congr (fun N => by ring) h3
    show Tendsto (fun N : ℕ => Hseq N w) atTop (nhds (H w))
    rw [show H w = M w + G w from rfl]
    exact h2
  have hHmem : ∀ w : ℂ, w.im < -(Y + 1) → (H w).im ≤ -Y - (3 * κ / 4 + 1) := by
    intro w hw
    have h1 : Tendsto (fun N : ℕ => (Hseq N w).im) atTop (nhds ((H w).im)) :=
      (Complex.continuous_im.tendsto (H w)).comp (hHtend w hw)
    exact le_of_tendsto' h1 (fun N => hmem N w hw)
  have hHlt : ∀ w : ℂ, w.im < -(Y + 1) → (H w).im < -Y :=
    fun w hw => lt_of_le_of_lt (hHmem w hw) hYc
  -- (F) the fixed point equation
  have hfix : ∀ w : ℂ, w.im < -(Y + 1) → H w = M w - ψ (H w) := by
    intro w hw
    have hcont : Tendsto ψ (𝓝 (H w)) (𝓝 (ψ (H w))) :=
      (hψ_diff.differentiableAt
        ((isOpen_lt (f := Complex.im) (g := fun _ : ℂ => -Y) Complex.continuous_im
          continuous_const).mem_nhds (hHlt w hw))).continuousAt
    have h2 : Tendsto (fun N : ℕ => M w - ψ (Hseq N w)) atTop (nhds (M w - ψ (H w))) :=
      tendsto_const_nhds.sub (hcont.comp (hHtend w hw))
    have h3 : Tendsto (fun N : ℕ => Hseq (N + 1) w) atTop (nhds (H w)) :=
      (hHtend w hw).comp (tendsto_add_atTop_nat 1)
    have h4 : Tendsto (fun N : ℕ => M w - ψ (Hseq N w)) atTop (nhds (H w)) :=
      Filter.Tendsto.congr (fun N => hHval N w) h3
    exact tendsto_nhds_unique h4 h2
  -- (G) uniqueness in the closed half-plane, and the equivariance of `H`
  have huniq : ∀ w : ℂ, w.im < -(Y + 1) → ∀ u : ℂ, u.im ≤ -Y - (3 * κ / 4 + 1) →
      u = M w - ψ u → u = H w := by
    intro w hw u hu hufix
    have hf := hfix w hw
    have hHu := hHmem w hw
    have heq : u - H w = ψ (H w) - ψ u := by
      have h1 : u = M w - ψ u := hufix
      have h2 : H w = M w - ψ (H w) := hf
      have h3 : (u, H w) = (M w - ψ u, M w - ψ (H w)) := Prod.ext h1 h2
      have h4 := congrArg (fun p : ℂ × ℂ => p.1 - p.2) h3
      have h5 : (M w - ψ u) - (M w - ψ (H w)) = ψ (H w) - ψ u := by ring
      exact h4.trans h5
    have hsmall : ‖u - H w‖ ≤ (1 / 2) * ‖u - H w‖ := by
      have hcn : ‖ψ (H w) - ψ u‖ ≤ (1 / 2) * ‖u - H w‖ := by
        have h := hcontr (H w) u hHu hu
        rwa [norm_sub_rev] at h
      calc ‖u - H w‖ = ‖ψ (H w) - ψ u‖ := by rw [heq]
        _ ≤ (1 / 2) * ‖u - H w‖ := hcn
    have hzero : ‖u - H w‖ = 0 := by linarith [norm_nonneg (u - H w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have heq1 : ∀ w : ℂ, w.im < -(Y + 1) → H (w + 1) = H w + 1 := by
    intro w hw
    have hw1 : (w + 1).im < -(Y + 1) := by simpa using hw
    refine (huniq (w + 1) hw1 (H w + 1) ?_ ?_).symm
    · simpa using hHmem w hw
    · have hψp : ψ (H w + 1) = ψ (H w) := hψ_per (H w) (hHlt w hw)
      rw [hψp]
      show H w + 1 = (w + 1) + (β - cl) - ψ (H w)
      nth_rewrite 1 [hfix w hw]
      show (w + (β - cl) - ψ (H w)) + 1 = (w + 1) + (β - cl) - ψ (H w)
      ring
  -- the increment `ρ`
  let ρ : ℂ → ℂ := fun w => H w - M w
  have hρdiff : DifferentiableOn ℂ ρ {w : ℂ | w.im < -(Y + 1)} := by
    show DifferentiableOn ℂ (fun w => H w - M w) _
    exact hHdiff.sub hMdiff
  have hρfix : ∀ w : ℂ, w.im < -(Y + 1) → H w = w + (β - cl) + ρ w := by
    intro w hw
    show H w = w + (β - cl) + (H w - M w)
    show H w = w + (β - cl) + (H w - (w + (β - cl)))
    ring
  have hρψ : ∀ w : ℂ, w.im < -(Y + 1) → ρ w = -ψ (H w) := by
    intro w hw
    show H w - M w = -ψ (H w)
    show H w - (w + (β - cl)) = -ψ (H w)
    nth_rewrite 1 [hfix w hw]
    show (w + (β - cl) - ψ (H w)) - (w + (β - cl)) = -ψ (H w)
    ring
  have hρper : ∀ w : ℂ, w.im < -(Y + 1) → ρ (w + 1) = ρ w := by
    intro w hw
    show H (w + 1) - M (w + 1) = H w - M w
    rw [heq1 w hw]
    show H w + 1 - ((w + 1) + (β - cl)) = H w - (w + (β - cl))
    ring
  have hρbd : ∀ w : ℂ, w.im < -(Y + 1) → ‖ρ w‖ ≤ κ / 2 := by
    intro w hw
    rw [hρψ w hw, norm_neg]
    have h := hψ_bd _ (hHlt w hw)
    linarith
  have hρdrift : ∀ w : ℂ, w.im < -(Y + 1) → (H w - w).im ≤ -(κ / 2) := by
    intro w hw
    have he : H w - w = (β - cl) - ψ (H w) := by
      nth_rewrite 1 [hfix w hw]
      show (w + (β - cl) - ψ (H w)) - w = (β - cl) - ψ (H w)
      ring
    rw [he, Complex.sub_im]
    have hb : -((ψ (H w)).im) ≤ κ / 4 := by
      have ha := Complex.abs_im_le_norm (ψ (H w))
      have hb2 : -((ψ (H w)).im) ≤ |(ψ (H w)).im| := neg_le_abs _
      have hc := hψ_bd _ (hHlt w hw)
      linarith
    linarith
  have hInj : Set.InjOn H {w : ℂ | w.im < -(Y + 1)} := by
    intro w1 hw1 w2 hw2 hEq
    have h3 : ρ w1 = ρ w2 := by rw [hρψ w1 hw1, hρψ w2 hw2, hEq]
    have h4 : w1 + (β - cl) = w2 + (β - cl) := by
      have e1 : ρ w1 = H w1 - (w1 + (β - cl)) := rfl
      have e2 : ρ w2 = H w2 - (w2 + (β - cl)) := rfl
      rw [e1, e2, hEq] at h3
      exact sub_right_inj.mp h3
    exact add_right_cancel h4
  have hρend : Tendsto ρ MandelDim.lowerEnd (𝓝 0) := by
    apply tendsto_lowerEnd_of_deep
    intro ε hε
    have h0 : {z : ℂ | ‖ψ z‖ < ε} ∈ MandelDim.lowerEnd := by
      have hm := hψ_end (Metric.ball_mem_nhds (0 : ℂ) hε)
      rw [Filter.mem_map] at hm
      refine Filter.mem_of_superset hm ?_
      intro z hz
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
    obtain ⟨T, hT⟩ := lowerEnd_eventually h0
    refine ⟨max (Y + 1) (T + κ + 1), fun w hw => ?_⟩
    have hws : w.im < -(Y + 1) := by
      have h := le_max_left (Y + 1) (T + κ + 1)
      linarith
    have hHdeep : (H w).im < -T := by
      have he : H w = w + (β - cl) - ψ (H w) := hfix w hws
      have him : (H w).im ≤ w.im - 3 * κ / 4 := by
        rw [he, Complex.sub_im, Complex.add_im]
        have hb : -((ψ (H w)).im) ≤ κ / 4 := by
          have ha := Complex.abs_im_le_norm (ψ (H w))
          have hb2 : -((ψ (H w)).im) ≤ |(ψ (H w)).im| := neg_le_abs _
          have hc := hψ_bd _ (hHlt w hws)
          linarith
        linarith
      have hwT : w.im < -(T + κ + 1) := by
        have h := le_max_right (Y + 1) (T + κ + 1)
        linarith
      linarith
    rw [hρψ w hws]
    show ‖-ψ (H w) - 0‖ < ε
    rw [sub_zero, norm_neg]
    exact hT (H w) hHdeep
  exact ⟨H, ρ, Y + 1, le_rfl, hHdiff, hρdiff, hρfix, hρψ, hHlt, hρper, hρbd, hρdrift,
    hInj, hρend⟩

end

/-- **The model's downward inverse branch on a deep half-plane** (mirror of
`model_deep_branch`, using the lower end `E w - w → cl`).  For the lifted horn map `E = d.E` of a
germ `g₀ ∈ 𝓕₀`, a lower-end limit `cl` of `E - id` and `κ ≤ Im cl - Im β`, and for every sufficiently
deep threshold `y₁`, there are `y' ≥ y₁` and a holomorphic injection `H` of the half-plane
`{im < -y'}` into `{im < -y₁} ∩ Bl`, with `H w = w + (β - cl) + ρ w` for a holomorphic `1`-periodic
`ρ`, `‖ρ w‖ ≤ κ/2`, `ρ w → 0` at the lower end, drift `Im (H w - w) ≤ -κ/2`, and `E (H w) - β = w`. -/
theorem model_deep_branch_lower {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {cl : ℂ}
    (hcl : Filter.Tendsto (fun w : ℂ => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {β : ℂ} {κ : ℝ} (hκ : 0 < κ) (hβ : κ ≤ Complex.im cl - Complex.im β) :
    ∃ y : ℝ, ∀ y₁ : ℝ, y ≤ y₁ →
      ∃ (H : ℂ → ℂ) (ρ : ℂ → ℂ) (y' : ℝ), y₁ ≤ y' ∧
        DifferentiableOn ℂ H {w : ℂ | Complex.im w < -(y' : ℝ)} ∧
        (∀ w : ℂ, Complex.im w < -(y' : ℝ) → Complex.im (H w) < -(y₁ : ℝ) ∧ H w ∈ hd.Bl ∧
          d.E (H w) - β = w) ∧
        (∀ w : ℂ, Complex.im w < -(y' : ℝ) → H w = w + (β - cl) + ρ w) ∧
        DifferentiableOn ℂ ρ {w : ℂ | Complex.im w < -(y' : ℝ)} ∧
        (∀ w : ℂ, Complex.im w < -(y' : ℝ) → ρ (w + 1) = ρ w) ∧
        (∀ w : ℂ, Complex.im w < -(y' : ℝ) → ‖ρ w‖ ≤ κ / 2) ∧
        (∀ w : ℂ, Complex.im w < -(y' : ℝ) → Complex.im (H w - w) ≤ -(κ / 2)) ∧
        Set.InjOn H {w : ℂ | Complex.im w < -(y' : ℝ)} ∧
        Filter.Tendsto ρ (Filter.comap Complex.im Filter.atBot) (nhds 0) := by
  have hψend : Filter.Tendsto (fun v : ℂ => d.E v - v - cl) MandelDim.lowerEnd (nhds 0) := by
    have h1 := hcl.sub_const cl
    simpa using h1
  have hψdiff : DifferentiableOn ℂ (fun v : ℂ => d.E v - v - cl) {v : ℂ | v.im < -d.η₀} := by
    have hmem : ∀ w : ℂ, w.im < -d.η₀ → d.η₀ < |w.im| :=
      fun w hw => lt_of_lt_of_le (by linarith) (neg_le_abs w.im)
    have h2 : DifferentiableOn ℂ d.φ {w : ℂ | w.im < -d.η₀} :=
      d.φ_holo.mono (fun w hw => (d.ends_sub w (hmem w hw)).1)
    have h1 : Set.MapsTo d.φ {w : ℂ | w.im < -d.η₀} (ParabolicBasin g₀ D) :=
      fun w hw => (d.ends_sub w (hmem w hw)).2
    have h3 : DifferentiableOn ℂ (fun v : ℂ => d.Φ (d.φ v)) {w : ℂ | w.im < -d.η₀} :=
      d.Φ_holo.comp h2 h1
    exact (h3.sub differentiableOn_id).sub (differentiableOn_const cl)
  have hψper : ∀ v : ℂ, v.im < -d.η₀ →
      (fun v : ℂ => d.E v - v - cl) (v + 1) = (fun v : ℂ => d.E v - v - cl) v := by
    intro v hv
    have hv' : d.η₀ < |v.im| := lt_of_lt_of_le (by linarith) (neg_le_abs v.im)
    have hE : d.E (v + 1) = d.E v + 1 := E_equivariant_of_eta0 d hv'
    show d.E (v + 1) - (v + 1) - cl = d.E v - v - cl
    rw [hE]; ring
  obtain ⟨Yd, hYd, hYdb⟩ :=
    deep_psi_deriv_bound (ψ := fun v : ℂ => d.E v - v - cl) (Y0 := d.η₀) (ε := 1 / 2)
      hψdiff hψend (by norm_num)
  obtain ⟨Yb, hYbb⟩ := lowerEnd_eventually_norm d hcl (by linarith : (0 : ℝ) < κ / 4)
  refine ⟨max hd.η (max (d.η₀ + 1) (max Yd Yb)), fun y₁ hy₁ => ?_⟩
  have hyη : hd.η ≤ y₁ := le_trans (le_max_left _ _) hy₁
  have hyc : max (d.η₀ + 1) (max Yd Yb) ≤ y₁ := le_trans (le_max_right _ _) hy₁
  have hy01 : d.η₀ + 1 ≤ y₁ := le_trans (le_max_left _ _) hyc
  have hyYd : Yd ≤ y₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hyc
  have hyYb : Yb ≤ y₁ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hyc
  obtain ⟨H, ρ, y', hy', hHd, hρd, hfix, hρψ, hHim, hρper, hρbd, hdrift, hinj, hρlim⟩ :=
    deep_branch_analytic (ψ := fun v : ℂ => d.E v - v - cl) (Y := y₁) (κ := κ) (β := β)
      (cl := cl) hκ (by rw [Complex.sub_im]; linarith)
      (hψdiff.mono (fun v hv => show v.im < -d.η₀ from by
        have hv' : v.im < -y₁ := hv
        linarith))
      (fun v hv => hψper v (by have hv' : v.im < -y₁ := hv; linarith))
      (fun v hv => le_of_lt (hYbb v (by have hv' : v.im < -y₁ := hv; linarith)))
      (fun v hv => hYdb v (by have hv' : v.im < -y₁ := hv; linarith))
      hψend
  refine ⟨H, ρ, y', ?_, hHd, ?_, hfix, hρd, hρper, hρbd, hdrift, hinj, hρlim⟩
  · linarith
  · intro w hw
    refine ⟨hHim w hw, hd.lower (by have h := hHim w hw; show (H w).im < -hd.η; linarith), ?_⟩
    have h1 := hρψ w hw
    have h2 := hfix w hw
    have h3 : d.E (H w) = H w + cl - ρ w := by
      rw [h1]; ring
    rw [h3, h2]; ring

end Work.L62
