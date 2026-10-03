import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

/-!
# The tail of the chain marching to the lower end (mirror of `tail_of_branch`)

Given a downward inverse branch `H` of `ĥ = R - β` on the lower half-plane `{im < -y'}`
(`H w = w + γ + ρ w`, `‖ρ‖ ≤ κ/4`, drift `Im (H w - w) ≤ -κ`, `H` maps the half-plane into itself
and into `DR`, `R (H w) - β = w`) together with a "Fatou coordinate" `L`
(`L (H w) = L w + a`, `‖deriv L w - 1‖ ≤ 1/2`), the iterates `V t = H^t '' W₀` of a small disc `W₀`
form a chain of open connected discs marching to the lower end, bijectively mapped to the previous
disc by `ĥ`, `π`-disjoint from each other, with a uniform derivative bound
`1/3 < ‖(ĥ^[t])'‖ < 3`.

The key point of the analytic argument is that `L` linearises the dynamics, so that the derivative
of the `t`-th iterate of `ĥ` at a point `z ∈ V t` is the telescoping quotient
`deriv L z / deriv L (ĥ^[t] z)`; the strict inequality follows from the maximum modulus principle
applied to `deriv L - 1`.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-! ## Auxiliary analysis lemmas -/

/-- **Mean-value bound.**  If `L : ℂ → ℂ` is complex differentiable on the convex set `D` and
`‖deriv L w - 1‖ ≤ 1/2` there, then `L - id` is `1/2`-Lipschitz on `D`. -/
lemma lower_norm_sub_sub_le {L : ℂ → ℂ} {D : Set ℂ} (hD : Convex ℝ D)
    (hd : ∀ w ∈ D, DifferentiableAt ℂ L w) (hbd : ∀ w ∈ D, ‖deriv L w - 1‖ ≤ 1 / 2) :
    ∀ x ∈ D, ∀ y ∈ D, ‖(L y - y) - (L x - x)‖ ≤ 1 / 2 * ‖y - x‖ := by
  intro x hx y hy
  have hdiff : ∀ w ∈ D, DifferentiableAt ℂ (fun z : ℂ => L z - z) w := fun w hw =>
    (hd w hw).sub (by simpa using (differentiableAt_id (𝕜 := ℂ) (x := w)))
  have hbound : ∀ w ∈ D, ‖deriv (fun z : ℂ => L z - z) w‖ ≤ 1 / 2 := by
    intro w hw
    have h1 : deriv (fun z : ℂ => L z - z) w = deriv L w - 1 := by
      have hh : HasDerivAt (fun z : ℂ => L z - z) (deriv L w - 1) w :=
        (hd w hw).hasDerivAt.sub (hasDerivAt_id w)
      exact hh.deriv
    rw [h1]
    exact hbd w hw
  simpa using Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hD hx hy

/-- **Maximum-modulus rigidity at an extremal value.**  If `L` is complex differentiable on the
open convex set `D` with `‖deriv L w - 1‖ ≤ 1/2` there, and the bound is attained at `z ∈ D`, then
`deriv L` is constant on `D`. -/
lemma lower_deriv_eq_of_max {L : ℂ → ℂ} {D : Set ℂ} (hDc : Convex ℝ D) (hDo : IsOpen D)
    (hd : ∀ w ∈ D, DifferentiableAt ℂ L w) (hbd : ∀ w ∈ D, ‖deriv L w - 1‖ ≤ 1 / 2)
    {z : ℂ} (hz : z ∈ D) (heq : ‖deriv L z - 1‖ = 1 / 2) :
    ∀ w ∈ D, deriv L w = deriv L z := by
  have hLd : DifferentiableOn ℂ L D := fun w hw => (hd w hw).differentiableWithinAt
  have hana : AnalyticOnNhd ℂ L D := hLd.analyticOnNhd hDo
  have hderivd : DifferentiableOn ℂ (fun w => deriv L w - 1) D :=
    (hana.deriv.differentiableOn).sub_const 1
  have hmax : IsMaxOn (fun w => ‖deriv L w - 1‖) D z := by
    intro w hw
    show ‖deriv L w - 1‖ ≤ ‖deriv L z - 1‖
    rw [heq]
    exact hbd w hw
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hDc.isPreconnected hDo
    hderivd hz hmax
  intro w hw
  have h := hconst hw
  simpa using h

/-- **The `L`-coordinate linearises the iterates.**  If `H` maps the open set `D` into itself, `L`
is complex differentiable on `D` with nonzero derivative and `L (H w) = L w + a`, then
`deriv (H^[t]) u = deriv L u / deriv L (H^[t] u)` for `u ∈ D`. -/
lemma lower_deriv_iterate {D : Set ℂ} (hDo : IsOpen D) {H L : ℂ → ℂ} {a : ℂ}
    (hHd : ∀ w ∈ D, DifferentiableAt ℂ H w) (hHm : Set.MapsTo H D D)
    (hLd : ∀ w ∈ D, DifferentiableAt ℂ L w) (hLne : ∀ w ∈ D, deriv L w ≠ 0)
    (hLH : ∀ w ∈ D, L (H w) = L w + a) :
    ∀ t : ℕ, ∀ u ∈ D, deriv (H^[t]) u = deriv L u / deriv L (H^[t] u) := by
  have hHdt : ∀ t : ℕ, ∀ w ∈ D, DifferentiableAt ℂ (H^[t]) w := by
    intro t
    induction t with
    | zero => intro w hw; simpa using (differentiableAt_id (𝕜 := ℂ) (x := w))
    | succ n ih =>
      intro w hw
      have hcomp : (H^[n.succ]) = (H^[n]) ∘ H := funext fun z => Function.iterate_succ_apply H n z
      rw [hcomp]
      exact (ih (H w) (hHm hw)).comp w (hHd w hw)
  have hLcomp : ∀ t : ℕ, ∀ w ∈ D, L (H^[t] w) = L w + (t : ℂ) * a := by
    intro t
    induction t with
    | zero => intro w hw; simp
    | succ n ih =>
      intro w hw
      have h2 : (H^[n.succ]) w = H ((H^[n]) w) := Function.iterate_succ_apply' H n w
      rw [h2, hLH _ (hHm.iterate n hw), ih w hw]
      push_cast
      ring
  intro t u hu
  have hmem : (H^[t]) u ∈ D := hHm.iterate t hu
  have h1 : deriv (fun w => L (H^[t] w)) u = deriv L u := by
    have heq : (fun w => L (H^[t] w)) =ᶠ[𝓝 u] (fun w => L w + (t : ℂ) * a) := by
      filter_upwards [hDo.mem_nhds hu] with w hw
      exact hLcomp t w hw
    rw [heq.deriv_eq, deriv_add_const]
  have h2 : deriv (fun w => L (H^[t] w)) u = deriv L ((H^[t]) u) * deriv (H^[t]) u :=
    deriv_comp u (hLd _ hmem) (hHdt t u hu)
  have h3 : deriv (H^[t]) u * deriv L ((H^[t]) u) = deriv L u := by
    rw [mul_comm, ← h2, h1]
  exact (eq_div_iff (hLne _ hmem)).mpr h3

/-! ## The main theorem -/

theorem tail_of_branch_lower {R : ℂ → ℂ} {β γ : ℂ} {DR : Set ℂ} {κ : ℝ} (hκ : 0 < κ)
    {y' : ℝ} {H ρ : ℂ → ℂ} {a : ℂ}
    (hH : DifferentiableOn ℂ H {w : ℂ | Complex.im w < -y'})
    (hinc : ∀ w : ℂ, Complex.im w < -y' → H w = w + γ + ρ w)
    (hρd : DifferentiableOn ℂ ρ {w : ℂ | Complex.im w < -y'})
    (hρbd : ∀ w : ℂ, Complex.im w < -y' → ‖ρ w‖ ≤ κ / 4)
    (hHmem : ∀ w : ℂ, Complex.im w < -y' →
      Complex.im (H w) < -y' ∧ H w ∈ DR ∧ R (H w) - β = w)
    (hdrift : ∀ w : ℂ, Complex.im w < -y' → Complex.im (H w - w) ≤ -κ)
    {L : ℂ → ℂ} (hL : ∀ w : ℂ, Complex.im w < -y' →
      DifferentiableAt ℂ L w ∧ L (H w) = L w + a ∧ ‖deriv L w - 1‖ ≤ 1 / 2)
    {W₀ : Set ℂ} (hW₀open : IsOpen W₀) (hW₀conn : IsConnected W₀)
    (hW₀sub : W₀ ⊆ {w : ℂ | Complex.im w < -y'})
    (hW₀bd : Bornology.IsBounded W₀) (hW₀diam : Metric.diam W₀ ≤ 1 / 24)
    (hκdiam : 3 * Metric.diam W₀ < κ) :
    ∃ V : ℕ → Set ℂ, V 0 = W₀ ∧
      (∀ t, IsOpen (V t) ∧ IsConnected (V t)) ∧
      (∀ t, V (t + 1) ⊆ DR ∧ Set.InjOn (fun w => R w - β) (V (t + 1)) ∧
        (fun w => R w - β) '' V (t + 1) = V t) ∧
      (∀ i j, i ≠ j → Disjoint (piExp '' V i) (piExp '' V j)) ∧
      (∀ M : ℝ, ∃ T : ℕ, ∀ t, T ≤ t → ∀ w ∈ V t, Complex.im w < -M) ∧
      (∀ t, Bornology.IsBounded (V t) ∧ Metric.diam (V t) < 1 / 2) ∧
      (∀ t, ∃ u ∈ V t, ∃ u' ∈ V (t + 1), ‖u - u'‖ < ‖γ‖ + κ / 4 + 1) ∧
      (∀ t, ∀ w ∈ V t, 1 / 3 < ‖deriv ((fun u => R u - β)^[t]) w‖ ∧
        ‖deriv ((fun u => R u - β)^[t]) w‖ < 3) := by
  set D : Set ℂ := {w : ℂ | Complex.im w < -y'} with hDdef
  have hDopen : IsOpen D := by
    rw [hDdef]
    exact isOpen_lt Complex.continuous_im continuous_const
  have hDconv : Convex ℝ D := by
    rw [hDdef]
    exact convex_halfSpace_lt (f := Complex.im)
      ⟨fun x y => by simp [Complex.add_im],
        fun c x => by simp⟩ (-y')
  -- convert the hypotheses to the abbreviated set `D`
  have hHmemD : ∀ w : ℂ, w ∈ D → Complex.im (H w) < -y' ∧ H w ∈ DR ∧ R (H w) - β = w := by
    intro w hw
    exact hHmem w (by simpa [hDdef] using hw)
  have hincD : ∀ w : ℂ, w ∈ D → H w = w + γ + ρ w := by
    intro w hw
    exact hinc w (by simpa [hDdef] using hw)
  have hρbdD : ∀ w : ℂ, w ∈ D → ‖ρ w‖ ≤ κ / 4 := by
    intro w hw
    exact hρbd w (by simpa [hDdef] using hw)
  have hdriftD : ∀ w : ℂ, w ∈ D → Complex.im (H w - w) ≤ -κ := by
    intro w hw
    exact hdrift w (by simpa [hDdef] using hw)
  have hHD : DifferentiableOn ℂ H D := by rw [hDdef]; exact hH
  have hρdD : DifferentiableOn ℂ ρ D := by rw [hDdef]; exact hρd
  have hLfacts : ∀ w : ℂ, w ∈ D →
      DifferentiableAt ℂ L w ∧ L (H w) = L w + a ∧ ‖deriv L w - 1‖ ≤ 1 / 2 := by
    intro w hw
    exact hL w (by simpa [hDdef] using hw)
  -- basic facts
  have hHd : ∀ w ∈ D, DifferentiableAt ℂ H w := fun w hw => hHD.differentiableAt (hDopen.mem_nhds hw)
  have hHmaps : Set.MapsTo H D D := by
    intro w hw
    simpa [hDdef] using (hHmemD w hw).1
  have hHDR : ∀ w ∈ D, H w ∈ DR := fun w hw => (hHmemD w hw).2.1
  have hsec : ∀ w ∈ D, (fun u => R u - β) (H w) = w := fun w hw => (hHmemD w hw).2.2
  have hstep : ∀ w ∈ D, Complex.im (H w) ≤ Complex.im w - κ := by
    intro w hw
    have h := hdriftD w hw
    rw [Complex.sub_im] at h
    linarith
  have hLd : ∀ w ∈ D, DifferentiableAt ℂ L w := fun w hw => (hLfacts w hw).1
  have hLH : ∀ w ∈ D, L (H w) = L w + a := fun w hw => (hLfacts w hw).2.1
  have hLbd : ∀ w ∈ D, ‖deriv L w - 1‖ ≤ 1 / 2 := fun w hw => (hLfacts w hw).2.2
  have hLne : ∀ w ∈ D, deriv L w ≠ 0 := by
    intro w hw h0
    have h1 := hLbd w hw
    rw [h0] at h1
    norm_num at h1
  have hLup : ∀ v ∈ D, ‖deriv L v‖ ≤ 3 / 2 := by
    intro v hv
    have h1 := hLbd v hv
    have h2 : ‖deriv L v‖ ≤ ‖deriv L v - 1‖ + ‖(1 : ℂ)‖ := by
      have he : deriv L v = (deriv L v - 1) + 1 := by ring
      calc ‖deriv L v‖ = ‖(deriv L v - 1) + 1‖ := by rw [← he]
        _ ≤ ‖deriv L v - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    have h3 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h3] at h2
    linarith
  have hLlow' : ∀ v ∈ D, 1 / 2 ≤ ‖deriv L v‖ := by
    intro v hv
    have h1 := hLbd v hv
    have h2 : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) - deriv L v‖ + ‖deriv L v‖ := by
      have he : (1 : ℂ) = (1 - deriv L v) + deriv L v := by ring
      calc ‖(1 : ℂ)‖ = ‖(1 - deriv L v) + deriv L v‖ := by rw [← he]
        _ ≤ ‖(1 : ℂ) - deriv L v‖ + ‖deriv L v‖ := norm_add_le _ _
    have h3 : ‖(1 : ℂ) - deriv L v‖ = ‖deriv L v - 1‖ := norm_sub_rev _ _
    rw [h3] at h2
    have h4 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [h4] at h2
    linarith
  -- Lipschitz bounds for `L`, in the `x - y` orientation
  have hLlip : ∀ x ∈ D, ∀ y ∈ D, ‖L x - L y‖ ≤ 3 / 2 * ‖x - y‖ := by
    intro x hx y hy
    have h := lower_norm_sub_sub_le hDconv hLd hLbd y hy x hx
    have h2 : ‖L x - L y‖ ≤ ‖(L x - x) - (L y - y)‖ + ‖x - y‖ := by
      calc ‖L x - L y‖ = ‖((L x - x) - (L y - y)) + (x - y)‖ := by congr 1; ring
        _ ≤ ‖(L x - x) - (L y - y)‖ + ‖x - y‖ := norm_add_le _ _
    linarith
  have hLlow : ∀ x ∈ D, ∀ y ∈ D, 1 / 2 * ‖x - y‖ ≤ ‖L x - L y‖ := by
    intro x hx y hy
    have h := lower_norm_sub_sub_le hDconv hLd hLbd y hy x hx
    have h2 : ‖x - y‖ ≤ ‖(L x - x) - (L y - y)‖ + ‖L x - L y‖ := by
      calc ‖x - y‖ = ‖-(((L x - x) - (L y - y)) + (L y - L x))‖ := by congr 1; ring
        _ = ‖((L x - x) - (L y - y)) + (L y - L x)‖ := norm_neg _
        _ ≤ ‖(L x - x) - (L y - y)‖ + ‖L y - L x‖ := norm_add_le _ _
        _ = ‖(L x - x) - (L y - y)‖ + ‖L x - L y‖ := by rw [← norm_sub_rev (L x) (L y)]
    linarith
  have hLinj : Set.InjOn L D := by
    intro x hx y hy hxy
    have h := lower_norm_sub_sub_le hDconv hLd hLbd x hx y hy
    have h2 : ‖(L y - y) - (L x - x)‖ = ‖y - x‖ := by
      have he : (L y - y) - (L x - x) = -(y - x) := by rw [hxy]; ring
      rw [he, norm_neg]
    rw [h2] at h
    have h3 : ‖y - x‖ = 0 := by
      have h4 : (0 : ℝ) ≤ ‖y - x‖ := norm_nonneg _
      linarith
    exact (sub_eq_zero.mp (norm_eq_zero.mp h3)).symm
  -- iterates of `H`
  have hHmaps_t : ∀ t : ℕ, Set.MapsTo (H^[t]) D D := fun t => hHmaps.iterate t
  have hHd_t : ∀ t : ℕ, ∀ w ∈ D, DifferentiableAt ℂ (H^[t]) w := by
    intro t
    induction t with
    | zero => intro w hw; simpa using (differentiableAt_id (𝕜 := ℂ) (x := w))
    | succ n ih =>
      intro w hw
      have hcomp : (H^[n.succ]) = (H^[n]) ∘ H := funext fun z => Function.iterate_succ_apply H n z
      rw [hcomp]
      exact (ih (H w) (hHmaps hw)).comp w (hHd w hw)
  have hHdiff_t : ∀ t : ℕ, DifferentiableOn ℂ (H^[t]) D :=
    fun t w hw => (hHd_t t w hw).differentiableWithinAt
  have hH_inj : Set.InjOn H D := by
    intro x hx y hy hxy
    have h1 := hsec x hx
    rw [hxy] at h1
    rw [hsec y hy] at h1
    exact h1.symm
  have hIter_inj : ∀ t : ℕ, Set.InjOn (H^[t]) D := fun t => hH_inj.iterate hHmaps t
  have hLcomp_t : ∀ t : ℕ, ∀ w ∈ D, L ((H^[t]) w) = L w + (t : ℂ) * a := by
    intro t
    induction t with
    | zero => intro w hw; simp
    | succ n ih =>
      intro w hw
      have h2 : (H^[n.succ]) w = H ((H^[n]) w) := Function.iterate_succ_apply' H n w
      rw [h2, hLH _ (hHmaps_t n hw), ih w hw]
      push_cast
      ring
  have hiter_sec : ∀ t : ℕ, ∀ w : ℂ, w ∈ D → (fun u => R u - β)^[t] ((H^[t]) w) = w := by
    intro t
    induction t with
    | zero => intro w hw; simp
    | succ n ih =>
      intro w hw
      have h1 : (fun u => R u - β)^[n.succ] ((H^[n.succ]) w)
          = (fun u => R u - β)^[n] ((fun u => R u - β) ((H^[n.succ]) w)) :=
        Function.iterate_succ_apply (fun u => R u - β) n _
      rw [h1]
      have h2 : (H^[n.succ]) w = H ((H^[n]) w) := Function.iterate_succ_apply' H n w
      rw [h2, hsec _ (hHmaps_t n hw), ih w hw]
  -- basic facts about `W₀`
  have hW₀subD : W₀ ⊆ D := fun w hw => by simpa [hDdef] using hW₀sub hw
  obtain ⟨w₀, hw₀⟩ := hW₀conn.nonempty
  have hw₀D : w₀ ∈ D := hW₀subD hw₀
  have hw₀1D : w₀ + 1 ∈ D := by
    have h : Complex.im (w₀ + 1) < -y' := by
      have h2 : Complex.im w₀ < -y' := by simpa [hDdef] using hw₀D
      simpa using h2
    simpa [hDdef] using h
  have hWdiam : ∀ x ∈ W₀, ∀ y ∈ W₀, ‖x - y‖ ≤ Metric.diam W₀ := by
    intro x hx y hy
    have h := Metric.dist_le_diam_of_mem hW₀bd hx hy
    rwa [dist_eq_norm] at h
  have hΔnn : 0 ≤ 3 * Metric.diam W₀ := by linarith [Metric.diam_nonneg (s := W₀)]
  -- the chain of discs
  let V : ℕ → Set ℂ := fun t => (H^[t]) '' W₀
  have hVt : ∀ t : ℕ, V t = (H^[t]) '' W₀ := fun t => rfl
  have hV0 : V 0 = W₀ := by rw [hVt 0]; simp
  have hVsub : ∀ t : ℕ, V t ⊆ D := by
    intro t z hz
    rw [hVt t] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact hHmaps_t t (hW₀subD hu)
  have hVne : ∀ t : ℕ, (V t).Nonempty := by
    intro t
    exact ⟨(H^[t]) w₀, by rw [hVt t]; exact ⟨w₀, hw₀, rfl⟩⟩
  have hIter_hhat : ∀ t : ℕ, ∀ z : ℂ, z ∈ V t → (H^[t]) ((fun u => R u - β)^[t] z) = z := by
    intro t z hz
    rw [hVt t] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [hiter_sec t u (hW₀subD hu)]
  have hhat_image : ∀ t : ℕ, (fun u => R u - β) '' V (t + 1) = V t := by
    intro t
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hVt (t + 1)] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      have h2 : (H^[t.succ]) u = H ((H^[t]) u) := Function.iterate_succ_apply' H t u
      rw [h2, hsec _ (hHmaps_t t (hW₀subD hu))]
      exact ⟨u, hu, rfl⟩
    · rintro hz
      rw [hVt t] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      refine ⟨(H^[t.succ]) u, ?_, ?_⟩
      · rw [hVt (t + 1)]; exact ⟨u, hu, rfl⟩
      · have h2 : (H^[t.succ]) u = H ((H^[t]) u) := Function.iterate_succ_apply' H t u
        rw [h2]
        exact hsec _ (hHmaps_t t (hW₀subD hu))
  have hhat_inj : ∀ t : ℕ, Set.InjOn (fun u => R u - β) (V (t + 1)) := by
    intro t z hz z' hz' heq
    rw [hVt (t + 1)] at hz hz'
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨v, hv, rfl⟩ := hz'
    have h2 : (H^[t.succ]) u = H ((H^[t]) u) := Function.iterate_succ_apply' H t u
    have h3 : (H^[t.succ]) v = H ((H^[t]) v) := Function.iterate_succ_apply' H t v
    rw [h2, h3, hsec _ (hHmaps_t t (hW₀subD hu)), hsec _ (hHmaps_t t (hW₀subD hv))] at heq
    have huv : u = v := hIter_inj t (hW₀subD hu) (hW₀subD hv) heq
    rw [huv]
  have hVDR : ∀ t : ℕ, V (t + 1) ⊆ DR := by
    intro t z hz
    rw [hVt (t + 1)] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have h2 : (H^[t.succ]) u = H ((H^[t]) u) := Function.iterate_succ_apply' H t u
    rw [h2]
    exact hHDR _ (hHmaps_t t (hW₀subD hu))
  -- diameter and boundedness
  have hVdiam : ∀ t : ℕ, ∀ x ∈ V t, ∀ y ∈ V t, ‖x - y‖ ≤ 3 * Metric.diam W₀ := by
    intro t x hx y hy
    rw [hVt t] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have h1 : 1 / 2 * ‖(H^[t]) u - (H^[t]) v‖ ≤ ‖L ((H^[t]) u) - L ((H^[t]) v)‖ :=
      hLlow ((H^[t]) u) (hHmaps_t t (hW₀subD hu)) ((H^[t]) v) (hHmaps_t t (hW₀subD hv))
    have h2 : ‖L ((H^[t]) u) - L ((H^[t]) v)‖ = ‖L u - L v‖ := by
      rw [hLcomp_t t u (hW₀subD hu), hLcomp_t t v (hW₀subD hv)]
      congr 1; ring
    have h3 : ‖L u - L v‖ ≤ 3 / 2 * ‖u - v‖ := hLlip u (hW₀subD hu) v (hW₀subD hv)
    have h4 : ‖u - v‖ ≤ Metric.diam W₀ := hWdiam u hu v hv
    linarith
  have hVbdd : ∀ t : ℕ, Bornology.IsBounded (V t) := by
    intro t
    obtain ⟨x₀, hx₀⟩ := hVne t
    rw [Metric.isBounded_iff]
    refine ⟨‖x₀‖ + 3 * Metric.diam W₀, fun x hx y hy => ?_⟩
    have h := hVdiam t x hx y hy
    calc dist x y = ‖x - y‖ := dist_eq_norm _ _
      _ ≤ 3 * Metric.diam W₀ := h
      _ ≤ ‖x₀‖ + 3 * Metric.diam W₀ := by linarith [norm_nonneg x₀]
  have hVdiamlt : ∀ t : ℕ, Metric.diam (V t) < 1 / 2 := by
    intro t
    have h := Metric.diam_le_of_forall_dist_le (s := V t) (C := 3 * Metric.diam W₀) hΔnn
      (fun x hx y hy => by rw [dist_eq_norm]; exact hVdiam t x hx y hy)
    linarith
  -- marching down
  have hVim : ∀ t : ℕ, ∀ z : ℂ, z ∈ V t →
      Complex.im z ≤ Complex.im w₀ + Metric.diam W₀ - (t : ℝ) * κ := by
    intro t z hz
    rw [hVt t] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hiter : Complex.im ((H^[t]) u) ≤ Complex.im u - (t : ℝ) * κ := by
      induction t with
      | zero => simp
      | succ n ih =>
        have h2 : (H^[n.succ]) u = H ((H^[n]) u) := Function.iterate_succ_apply' H n u
        rw [h2]
        have hmem : (H^[n]) u ∈ D := hHmaps_t n (hW₀subD hu)
        have h1 : Complex.im (H ((H^[n]) u)) ≤ Complex.im ((H^[n]) u) - κ := hstep _ hmem
        push_cast
        linarith
    have hu_im : Complex.im u ≤ Complex.im w₀ + Metric.diam W₀ := by
      have h1 : ‖u - w₀‖ ≤ Metric.diam W₀ := hWdiam u hu w₀ hw₀
      have h2 := Complex.abs_im_le_norm (u - w₀)
      rw [Complex.sub_im] at h2
      have h3 : Complex.im u - Complex.im w₀ ≤ Metric.diam W₀ := by
        have h4 := (abs_le.mp (le_trans h2 h1)).2
        linarith
      linarith
    linarith
  have hmarch : ∀ M : ℝ, ∃ T : ℕ, ∀ t, T ≤ t → ∀ z ∈ V t, Complex.im z < -M := by
    intro M
    obtain ⟨T, hT⟩ := exists_nat_gt ((Complex.im w₀ + Metric.diam W₀ + M) / κ)
    refine ⟨T, fun t ht z hz => ?_⟩
    have h1 := hVim t z hz
    have h2 : (T : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have h3 : Complex.im w₀ + Metric.diam W₀ + M < (T : ℝ) * κ := by
      rw [div_lt_iff₀ hκ] at hT
      linarith
    have h4 : (0:ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    nlinarith [h1, h2, h3, hκ]
  -- vertical separation of the discs
  have hsepV : ∀ t : ℕ, ∀ z ∈ V (t + 1), ∀ x ∈ V t, Complex.im z < Complex.im x := by
    intro t z hz x hx
    rw [hVt (t + 1)] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have h2 : (H^[t.succ]) u = H ((H^[t]) u) := Function.iterate_succ_apply' H t u
    rw [h2]
    have h1 : Complex.im (H ((H^[t]) u)) ≤ Complex.im ((H^[t]) u) - κ :=
      hstep _ (hHmaps_t t (hW₀subD hu))
    have hz' : (H^[t]) u ∈ V t := by rw [hVt t]; exact ⟨u, hu, rfl⟩
    have h3 : Complex.im ((H^[t]) u) - Complex.im x ≤ 3 * Metric.diam W₀ := by
      have h4 : ‖(H^[t]) u - x‖ ≤ 3 * Metric.diam W₀ := hVdiam t _ hz' x hx
      have h5 := Complex.abs_im_le_norm ((H^[t]) u - x)
      rw [Complex.sub_im] at h5
      have h6 := (abs_le.mp (le_trans h5 h4)).2
      linarith
    linarith
  have hsep : ∀ j : ℕ, ∀ i : ℕ, i < j → ∀ x ∈ V i, ∀ z ∈ V j, Complex.im z < Complex.im x := by
    intro j
    induction j with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi x hx z hz
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | heq
      · rw [hVt (n + 1)] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        have h2 : (H^[n.succ]) u = H ((H^[n]) u) := Function.iterate_succ_apply' H n u
        rw [h2]
        have hmem : (H^[n]) u ∈ D := hHmaps_t n (hW₀subD hu)
        have h1 : Complex.im (H ((H^[n]) u)) ≤ Complex.im ((H^[n]) u) - κ := hstep _ hmem
        have hz' : (H^[n]) u ∈ V n := by rw [hVt n]; exact ⟨u, hu, rfl⟩
        have h3 := ih i h x hx _ hz'
        linarith
      · exact hsepV n z hz x (heq ▸ hx)
  -- `π`-disjointness
  have hdisj : ∀ i j, i ≠ j → Disjoint (piExp '' V i) (piExp '' V j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', heq⟩ := hx'
    obtain ⟨k, hk⟩ := (Work.Horn.MandelDim.piExp_eq_iff).mp heq
    have him : Complex.im z = Complex.im z' := by rw [hk]; simp
    rcases lt_or_gt_of_ne hij with h | h
    · have hlt := hsep j i h z hz z' hz'
      linarith
    · have hlt := hsep i j h z' hz' z hz
      linarith
  -- consecutive discs are close
  have hclose : ∀ t : ℕ, ∃ u ∈ V t, ∃ u' ∈ V (t + 1), ‖u - u'‖ < ‖γ‖ + κ / 4 + 1 := by
    intro t
    obtain ⟨w, hw⟩ := hVne t
    refine ⟨w, hw, H w, ?_, ?_⟩
    · rw [hVt (t + 1)]
      rw [hVt t] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      exact ⟨u, hu, Function.iterate_succ_apply' H t u⟩
    · have hmem : w ∈ D := hVsub t hw
      have h1 : H w - w = γ + ρ w := by rw [hincD w hmem]; ring
      calc ‖w - H w‖ = ‖H w - w‖ := norm_sub_rev _ _
        _ = ‖γ + ρ w‖ := by rw [h1]
        _ ≤ ‖γ‖ + ‖ρ w‖ := norm_add_le _ _
        _ ≤ ‖γ‖ + κ / 4 := by linarith [hρbdD w hmem]
        _ < ‖γ‖ + κ / 4 + 1 := by linarith
  -- openness and connectedness
  have hVconn : ∀ t : ℕ, IsConnected (V t) := by
    intro t
    rw [hVt t]
    exact hW₀conn.image _ ((hHdiff_t t).continuousOn.mono hW₀subD)
  have hVopen : ∀ t : ℕ, IsOpen (V t) := by
    intro t
    rw [hVt t]
    have hana : AnalyticOnNhd ℂ (H^[t]) D := (hHdiff_t t).analyticOnNhd hDopen
    rcases hana.is_constant_or_isOpen hDconv.isPreconnected with hconst | hopen
    · exfalso
      obtain ⟨c, hc⟩ := hconst
      have h1 : (H^[t]) w₀ = (H^[t]) (w₀ + 1) := by rw [hc w₀ hw₀D, hc (w₀ + 1) hw₀1D]
      have h2 := hIter_inj t hw₀D hw₀1D h1
      have h3 : (w₀).re = (w₀).re + 1 := by simpa using congrArg Complex.re h2
      linarith
    · exact hopen W₀ hW₀subD hW₀open
  -- Lipschitz bound for the inverse iterates, for continuity
  have hhatlip : ∀ t : ℕ, LipschitzOnWith 3 (fun u => R u - β)^[t] (V t) := by
    intro t
    refine LipschitzOnWith.of_dist_le_mul (K := 3) ?_
    intro z hz z' hz'
    rw [hVt t] at hz hz'
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨v, hv, rfl⟩ := hz'
    have h1 : (fun u => R u - β)^[t] ((H^[t]) u) = u := hiter_sec t u (hW₀subD hu)
    have h2 : (fun u => R u - β)^[t] ((H^[t]) v) = v := hiter_sec t v (hW₀subD hv)
    have h3 : 1 / 2 * ‖u - v‖ ≤ ‖L u - L v‖ := hLlow u (hW₀subD hu) v (hW₀subD hv)
    have h4 : ‖L u - L v‖ = ‖L ((H^[t]) u) - L ((H^[t]) v)‖ := by
      rw [hLcomp_t t u (hW₀subD hu), hLcomp_t t v (hW₀subD hv)]
      congr 1; ring
    have h5 : ‖L ((H^[t]) u) - L ((H^[t]) v)‖ ≤ 3 / 2 * ‖(H^[t]) u - (H^[t]) v‖ :=
      hLlip ((H^[t]) u) (hHmaps_t t (hW₀subD hu)) ((H^[t]) v) (hHmaps_t t (hW₀subD hv))
    rw [h1, h2, dist_eq_norm, dist_eq_norm]
    push_cast
    linarith
  -- the derivative bound
  have hderivconj : ∀ t : ℕ, ∀ w ∈ V t, 1 / 3 < ‖deriv ((fun u => R u - β)^[t]) w‖ ∧
      ‖deriv ((fun u => R u - β)^[t]) w‖ < 3 := by
    intro t w hw
    rw [hVt t] at hw
    obtain ⟨u₀, hu₀, rfl⟩ := hw
    have hu₀D : u₀ ∈ D := hW₀subD hu₀
    have hmemD : (H^[t]) u₀ ∈ D := hHmaps_t t hu₀D
    have hzV : (H^[t]) u₀ ∈ V t := by rw [hVt t]; exact ⟨u₀, hu₀, rfl⟩
    have hderH : deriv (H^[t]) u₀ = deriv L u₀ / deriv L ((H^[t]) u₀) :=
      lower_deriv_iterate hDopen hHd hHmaps hLd hLne hLH t u₀ hu₀D
    have hderHne : deriv (H^[t]) u₀ ≠ 0 := by
      rw [hderH]
      exact div_ne_zero (hLne u₀ hu₀D) (hLne _ hmemD)
    have hhas : HasDerivAt (H^[t]) (deriv (H^[t]) u₀) ((fun u => R u - β)^[t] ((H^[t]) u₀)) := by
      rw [hiter_sec t u₀ hu₀D]
      exact (hHd_t t u₀ hu₀D).hasDerivAt
    have hcont : ContinuousAt ((fun u => R u - β)^[t]) ((H^[t]) u₀) :=
      ((hhatlip t).continuousOn).continuousAt ((hVopen t).mem_nhds hzV)
    have hevent : ∀ᶠ y in 𝓝 ((H^[t]) u₀), (H^[t]) ((fun u => R u - β)^[t] y) = y := by
      filter_upwards [(hVopen t).mem_nhds hzV] with y hy
      exact hIter_hhat t y hy
    have hinv := HasDerivAt.of_local_left_inverse hcont hhas hderHne hevent
    have hder : deriv ((fun u => R u - β)^[t]) ((H^[t]) u₀) = (deriv (H^[t]) u₀)⁻¹ := hinv.deriv
    have hnorm : ‖deriv ((fun u => R u - β)^[t]) ((H^[t]) u₀)‖
        = ‖deriv L ((H^[t]) u₀)‖ / ‖deriv L u₀‖ := by
      rw [hder, hderH, inv_div, norm_div]
    have hp_le : ‖deriv L ((H^[t]) u₀)‖ ≤ 3 / 2 := hLup _ hmemD
    have hp_ge : 1 / 2 ≤ ‖deriv L ((H^[t]) u₀)‖ := hLlow' _ hmemD
    have hq_le : ‖deriv L u₀‖ ≤ 3 / 2 := hLup _ hu₀D
    have hq_ge : 1 / 2 ≤ ‖deriv L u₀‖ := hLlow' _ hu₀D
    have hqpos : 0 < ‖deriv L u₀‖ := by linarith
    have key : (‖deriv L ((H^[t]) u₀)‖ = 1 / 2 ∨ ‖deriv L ((H^[t]) u₀)‖ = 3 / 2) →
        ∀ v ∈ D, deriv L v = deriv L ((H^[t]) u₀) := by
      intro hcase
      apply lower_deriv_eq_of_max hDconv hDopen hLd hLbd hmemD
      rcases hcase with h | h
      · have h3 := hLbd _ hmemD
        have h4 : ‖(1 : ℂ)‖ ≤ ‖deriv L ((H^[t]) u₀) - 1‖ + ‖deriv L ((H^[t]) u₀)‖ := by
          calc ‖(1 : ℂ)‖ = ‖-(deriv L ((H^[t]) u₀) - 1) + deriv L ((H^[t]) u₀)‖ := by
                congr 1; ring
            _ ≤ ‖-(deriv L ((H^[t]) u₀) - 1)‖ + ‖deriv L ((H^[t]) u₀)‖ := norm_add_le _ _
            _ = ‖deriv L ((H^[t]) u₀) - 1‖ + ‖deriv L ((H^[t]) u₀)‖ := by rw [norm_neg]
        have h5 : ‖(1 : ℂ)‖ = 1 := by simp
        rw [h5, h] at h4
        linarith
      · have h3 := hLbd _ hmemD
        have h4 : ‖deriv L ((H^[t]) u₀)‖
            ≤ ‖deriv L ((H^[t]) u₀) - 1‖ + ‖(1 : ℂ)‖ := by
          calc ‖deriv L ((H^[t]) u₀)‖ = ‖(deriv L ((H^[t]) u₀) - 1) + 1‖ := by
                congr 1; ring
            _ ≤ ‖deriv L ((H^[t]) u₀) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        have h5 : ‖(1 : ℂ)‖ = 1 := by simp
        rw [h5, h] at h4
        linarith
    rw [hnorm]
    by_cases hcase : ‖deriv L ((H^[t]) u₀)‖ = 1 / 2 ∨ ‖deriv L ((H^[t]) u₀)‖ = 3 / 2
    · have hconst := key hcase
      have hqeq : ‖deriv L u₀‖ = ‖deriv L ((H^[t]) u₀)‖ := by rw [hconst u₀ hu₀D]
      have hpne : ‖deriv L ((H^[t]) u₀)‖ ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le (by norm_num) hp_ge)
      rw [hqeq, div_self hpne]
      norm_num
    · have hp_lt : ‖deriv L ((H^[t]) u₀)‖ < 3 / 2 :=
        lt_of_le_of_ne hp_le (fun h => hcase (Or.inr h))
      have hp_gt : 1 / 2 < ‖deriv L ((H^[t]) u₀)‖ :=
        lt_of_le_of_ne hp_ge (fun h => hcase (Or.inl h.symm))
      constructor
      · rw [lt_div_iff₀ hqpos]
        nlinarith [hq_le, hp_gt]
      · rw [div_lt_iff₀ hqpos]
        nlinarith [hp_lt, hq_ge]
  exact ⟨V, hV0, fun t => ⟨hVopen t, hVconn t⟩, fun t => ⟨hVDR t, hhat_inj t, hhat_image t⟩,
    hdisj, hmarch, fun t => ⟨hVbdd t, hVdiamlt t⟩, hclose, hderivconj⟩

end

end Work.L62
