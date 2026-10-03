import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.deriv_iterate_eq
import Submission.Work.L62.deriv_eq_of_norm_extreme

open MandelDim

namespace Work.L62

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- The half plane `{w | y' < Im w}` is open. -/
theorem isOpen_halfPlane (y' : ℝ) : IsOpen {w : ℂ | y' < Complex.im w} :=
  isOpen_lt continuous_const Complex.continuous_im

/-- The half plane `{w | y' < Im w}` is nonempty. -/
theorem nonempty_halfPlane (y' : ℝ) : ({w : ℂ | y' < Complex.im w}).Nonempty :=
  ⟨((y' + 1 : ℝ) : ℂ) * Complex.I, by
    show y' < Complex.im (((y' + 1 : ℝ) : ℂ) * Complex.I)
    rw [Complex.mul_I_im, Complex.ofReal_re]; linarith⟩

/-- Convex mean-value bound for complex differentiation: if `f : ℂ → ℂ` is differentiable on the
convex set `s` and `‖deriv f‖ ≤ C` there, then `‖f y - f x‖ ≤ C * ‖y - x‖` for `x y ∈ s`. -/
theorem norm_image_sub_le_of_deriv_le {f : ℂ → ℂ} {s : Set ℂ} {C : ℝ}
    (hd : ∀ z ∈ s, DifferentiableAt ℂ f z) (hb : ∀ z ∈ s, ‖deriv f z‖ ≤ C)
    (hs : Convex ℝ s) {x y : ℂ} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_fderiv_le hd
    (fun z hz => by rw [← norm_deriv_eq_norm_fderiv]; exact hb z hz) hx hy

/-- Two points with different imaginary part have different `piExp`-images. -/
theorem piExp_im_ne {z z' : ℂ} (h : piExp z = piExp z') : Complex.im z = Complex.im z' := by
  have h2 : Complex.exp (2 * Real.pi * Complex.I * z) = Complex.exp (2 * Real.pi * Complex.I * z') := h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h2
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    have h2' : (2 : ℂ) ≠ 0 := by norm_num
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero h2' hp) Complex.I_ne_zero
  have hz : (2 * Real.pi * Complex.I) * (z - z' - (n : ℂ)) = 0 := by
    rw [mul_sub, mul_sub, hn]; ring_nf
  have h4 : z - z' - (n : ℂ) = 0 := (mul_eq_zero.mp hz).resolve_left hπ
  have hz' : z = z' + (n : ℂ) := by linear_combination h4
  rw [hz', Complex.add_im, Complex.intCast_im, add_zero]

theorem tail_of_branch {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {κ : ℝ} (hκ : 0 < κ)
    {y' : ℝ} {H ρ : ℂ → ℂ} {a : ℂ}
    (hH : DifferentiableOn ℂ H {w : ℂ | y' < Complex.im w})
    (hinc : ∀ w : ℂ, y' < Complex.im w → H w = w + β + ρ w)
    (hρd : DifferentiableOn ℂ ρ {w : ℂ | y' < Complex.im w})
    (hρbd : ∀ w : ℂ, y' < Complex.im w → ‖ρ w‖ ≤ κ / 4)
    (hHmem : ∀ w : ℂ, y' < Complex.im w →
      y' < Complex.im (H w) ∧ H w ∈ DR ∧ R (H w) - β = w)
    (hdrift : ∀ w : ℂ, y' < Complex.im w → κ ≤ Complex.im (H w - w))
    {L : ℂ → ℂ} (hL : ∀ w : ℂ, y' < Complex.im w →
      DifferentiableAt ℂ L w ∧ L (H w) = L w + a ∧ ‖deriv L w - 1‖ ≤ 1 / 2)
    {W₀ : Set ℂ} (hW₀open : IsOpen W₀) (hW₀conn : IsConnected W₀)
    (hW₀sub : W₀ ⊆ {w : ℂ | y' < Complex.im w})
    (hW₀bd : Bornology.IsBounded W₀) (hW₀diam : Metric.diam W₀ ≤ 1 / 24)
    (hκdiam : 3 * Metric.diam W₀ < κ) :
    ∃ V : ℕ → Set ℂ, V 0 = W₀ ∧
      (∀ t, IsOpen (V t) ∧ IsConnected (V t)) ∧
      (∀ t, V (t + 1) ⊆ DR ∧ Set.InjOn (fun w => R w - β) (V (t + 1)) ∧
        (fun w => R w - β) '' V (t + 1) = V t) ∧
      (∀ i j, i ≠ j → Disjoint (piExp '' V i) (piExp '' V j)) ∧
      (∀ M : ℝ, ∃ T : ℕ, ∀ t, T ≤ t → ∀ w ∈ V t, M < Complex.im w) ∧
      (∀ t, Bornology.IsBounded (V t) ∧ Metric.diam (V t) < 1 / 2) ∧
      (∀ t, ∃ u ∈ V t, ∃ u' ∈ V (t + 1), ‖u - u'‖ < ‖β‖ + κ / 4 + 1) ∧
      (∀ t, ∀ w ∈ V t, 1 / 3 < ‖deriv ((fun u => R u - β)^[t]) w‖ ∧
        ‖deriv ((fun u => R u - β)^[t]) w‖ < 3) := by
  classical
  let U : Set ℂ := {w : ℂ | y' < Complex.im w}
  have hUo : IsOpen U := isOpen_halfPlane y'
  have hUc : Convex ℝ U := convex_halfSpace_im_gt y'
  have hUpc : IsPreconnected U := hUc.isPreconnected
  have hHan : AnalyticOnNhd ℂ H U := hH.analyticOnNhd hUo
  have hHd : DifferentiableOn ℂ H U := hH
  have hLd : DifferentiableOn ℂ L U := fun w hw => (hL w hw).1.differentiableWithinAt
  have hHmemU : ∀ w ∈ U, H w ∈ U := fun w hw => (hHmem w hw).1
  have hdriftU : ∀ w ∈ U, κ ≤ Complex.im (H w - w) := hdrift
  have hLH : ∀ w ∈ U, L (H w) = L w + a := fun w hw => (hL w hw).2.1
  have hbU : ∀ w ∈ U, ‖deriv L w - 1‖ ≤ 1 / 2 := fun w hw => (hL w hw).2.2
  have WsubU : W₀ ⊆ U := hW₀sub
  -- bounds for `‖deriv L‖`
  have derivL_bounds : ∀ w ∈ U, 1 / 2 ≤ ‖deriv L w‖ ∧ ‖deriv L w‖ ≤ 3 / 2 := by
    intro w hw
    have h := hbU w hw
    have hlo : (1 : ℝ) - ‖deriv L w‖ ≤ ‖deriv L w - 1‖ := by
      have h' := norm_sub_norm_le (1 : ℂ) (deriv L w)
      rw [norm_one, norm_sub_rev] at h'
      exact h'
    have hhi : ‖deriv L w‖ - 1 ≤ ‖deriv L w - 1‖ := by
      have h' := norm_sub_norm_le (deriv L w) 1
      rw [norm_one] at h'
      exact h'
    constructor <;> linarith
  -- `deriv L` never vanishes
  have bne : ∀ w ∈ U, deriv L w ≠ 0 := by
    intro w hw h0
    have h1 := hbU w hw
    have h2 : ‖deriv L w - 1‖ = 1 := by rw [h0, zero_sub, norm_neg, norm_one]
    rw [h2] at h1
    norm_num at h1
  -- `H` is non-constant on `U`
  have hHnc : ¬ ∃ c, ∀ w ∈ U, H w = c := by
    rintro ⟨c, hc⟩
    have hm1 : y' < Complex.im (((y' + 1 : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.mul_I_im, Complex.ofReal_re]; linarith
    have hm2 : y' < Complex.im (((y' + 2 : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.mul_I_im, Complex.ofReal_re]; linarith
    have h1 : R c - β = ((y' + 1 : ℝ) : ℂ) * Complex.I := by
      rw [← hc _ hm1]
      exact (hHmem (((y' + 1 : ℝ) : ℂ) * Complex.I) hm1).2.2
    have h2 : R c - β = ((y' + 2 : ℝ) : ℂ) * Complex.I := by
      rw [← hc _ hm2]
      exact (hHmem (((y' + 2 : ℝ) : ℂ) * Complex.I) hm2).2.2
    have h3 : ((y' + 1 : ℝ) : ℂ) * Complex.I = ((y' + 2 : ℝ) : ℂ) * Complex.I := by
      rw [← h1, h2]
    have h4 := congrArg Complex.im h3
    rw [Complex.mul_I_im, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_re] at h4
    linarith
  have himage : ∀ s ⊆ U, IsOpen s → IsOpen (H '' s) := by
    rcases hHan.is_constant_or_isOpen hUpc with h | h
    · exact absurd h hHnc
    · exact h
  -- iterating `H`: membership, drift, analyticity, and the relation `(R-β)^k (H^k x) = x`
  have HmemU : ∀ t (w : ℂ), w ∈ U → H^[t] w ∈ U := by
    intro t
    induction t with
    | zero => intro w hw; exact hw
    | succ t ih =>
        intro w hw
        rw [Nat.add_one, Function.iterate_succ_apply']
        exact hHmemU _ (ih w hw)
  have him_drift : ∀ k : ℕ, ∀ y : ℂ, y ∈ U → Complex.im y + (k : ℝ) * κ ≤ Complex.im (H^[k] y) := by
    intro k
    induction k with
    | zero => intro y hy; simp
    | succ k ih =>
        intro y hy
        have hHky : H^[k] y ∈ U := HmemU k y hy
        have hstep : Complex.im (H^[k] y) + κ ≤ Complex.im (H (H^[k] y)) := by
          have h := hdriftU (H^[k] y) hHky
          rw [Complex.sub_im] at h
          linarith
        have hih := ih y hy
        have hcast : ((Nat.succ k : ℕ) : ℝ) * κ = (k : ℝ) * κ + κ := by
          rw [Nat.cast_succ, add_mul, one_mul]
        rw [Nat.add_one, Function.iterate_succ_apply', hcast]
        linarith
  have Hana : ∀ k (y : ℂ), y ∈ U → AnalyticAt ℂ (H^[k]) y := by
    intro k
    induction k with
    | zero => intro y hy; change AnalyticAt ℂ id y; exact analyticAt_id
    | succ k ih =>
        intro y hy
        rw [Nat.add_one, Function.iterate_succ']
        exact (hHan.analyticOn.analyticAt (hUo.mem_nhds (HmemU k y hy))).comp (ih y hy)
  have Riter : ∀ k (x : ℂ), x ∈ U → (fun u => R u - β)^[k] (H^[k] x) = x := by
    intro k
    induction k with
    | zero => intro x hx; change x = x; rfl
    | succ k ih =>
        intro x hx
        have hHkx : H^[k] x ∈ U := HmemU k x hx
        have hstep : (fun u => R u - β) (H (H^[k] x)) = H^[k] x :=
          (hHmem (H^[k] x) hHkx).2.2
        have h1 : (fun u => R u - β)^[k+1] (H^[k+1] x)
            = (fun u => R u - β)^[k] ((fun u => R u - β) (H (H^[k] x))) := by
          rw [Nat.add_one, Function.iterate_succ_apply, Function.iterate_succ_apply']
        rw [h1, hstep]
        exact ih x hx
  obtain ⟨hdform, hlip⟩ := deriv_iterate_eq hUo hUc hHd hLd hHmemU hLH hbU
  have hext := deriv_eq_of_norm_extreme hUo hUpc hLd hbU
  -- the sequence `V`
  let V : ℕ → Set ℂ := fun t => H^[t] '' W₀
  have Vzero : V 0 = W₀ := by
    change H^[0] '' W₀ = W₀
    rw [Function.iterate_zero]
    exact Set.image_id W₀
  have Vsucc : ∀ t, V (t + 1) = H '' V t := by
    intro t
    change H^[t+1] '' W₀ = H '' (H^[t] '' W₀)
    rw [Nat.add_one, Function.iterate_succ']
    exact Set.image_comp H (H^[t]) W₀
  have Vsub : ∀ t, V t ⊆ U := by
    intro t x hx
    change x ∈ H^[t] '' W₀ at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact HmemU t w (WsubU hw)
  have Vopen : ∀ t, IsOpen (V t) := by
    intro t
    induction t with
    | zero => rw [Vzero]; exact hW₀open
    | succ t ih =>
        rw [show V (Nat.succ t) = H '' V t from Vsucc t]
        exact himage _ (Vsub t) ih
  have Vconn : ∀ t, IsConnected (V t) := by
    intro t
    induction t with
    | zero => rw [Vzero]; exact hW₀conn
    | succ t ih =>
        rw [show V (Nat.succ t) = H '' V t from Vsucc t]
        exact ih.image H (hH.continuousOn.mono (Vsub t))
  have Vdiam : ∀ t, Metric.diam (V t) ≤ 3 * Metric.diam W₀ := by
    intro t
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    intro u hu u' hu'
    change u ∈ H^[t] '' W₀ at hu
    change u' ∈ H^[t] '' W₀ at hu'
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hu'
    rw [dist_eq_norm]
    calc ‖H^[t] a - H^[t] b‖ ≤ 3 * ‖a - b‖ := hlip t b (WsubU hb) a (WsubU ha)
      _ ≤ 3 * Metric.diam W₀ := by
          gcongr
          rw [← dist_eq_norm]
          exact Metric.dist_le_diam_of_mem hW₀bd ha hb
  have Vbdd : ∀ t, Bornology.IsBounded (V t) := by
    intro t
    obtain ⟨z₀, hz₀⟩ := hW₀conn.nonempty
    refine (Metric.isBounded_closedBall (x := H^[t] z₀) (r := 3 * Metric.diam W₀)).subset ?_
    intro u hu
    change u ∈ H^[t] '' W₀ at hu
    obtain ⟨b, hb, rfl⟩ := hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖H^[t] b - H^[t] z₀‖ ≤ 3 * ‖b - z₀‖ := hlip t z₀ (WsubU hz₀) b (WsubU hb)
      _ ≤ 3 * Metric.diam W₀ := by
          gcongr
          rw [← dist_eq_norm]
          exact Metric.dist_le_diam_of_mem hW₀bd hb hz₀
  have Vdiam_lt : ∀ t, Metric.diam (V t) < κ := fun t => lt_of_le_of_lt (Vdiam t) hκdiam
  have Vdiam_half : ∀ t, Metric.diam (V t) < 1 / 2 := by
    intro t
    have h1 := Vdiam t
    linarith [hW₀diam, h1]
  -- the chain relations
  have VsubDR : ∀ t, V (t + 1) ⊆ DR := by
    intro t
    rw [Vsucc t]
    rintro u ⟨w, hw, rfl⟩
    exact (hHmem w (Vsub t hw)).2.1
  have Vinj : ∀ t, Set.InjOn (fun w => R w - β) (V (t + 1)) := by
    intro t x hx y hy hxy
    rw [Vsucc t] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    change R (H x') - β = R (H y') - β at hxy
    have hx'' : R (H x') - β = x' := (hHmem x' (Vsub t hx')).2.2
    have hy'' : R (H y') - β = y' := (hHmem y' (Vsub t hy')).2.2
    rw [hx'', hy''] at hxy
    rw [hxy]
  have Vimg : ∀ t, (fun w => R w - β) '' (V (t + 1)) = V t := by
    intro t
    rw [Vsucc t]
    ext y
    constructor
    · rintro ⟨x, ⟨w, hw, rfl⟩, hxy⟩
      change R (H w) - β = y at hxy
      have hx : R (H w) - β = w := (hHmem w (Vsub t hw)).2.2
      rw [hx] at hxy
      rw [← hxy]
      exact hw
    · intro hy
      exact ⟨H y, ⟨y, hy, rfl⟩, (hHmem y (Vsub t hy)).2.2⟩
  -- height separation
  have hsep : ∀ i j, i < j → ∀ z ∈ V i, ∀ z' ∈ V j, Complex.im z < Complex.im z' := by
    intro i j hij z hz z' hz'
    change z ∈ H^[i] '' W₀ at hz
    change z' ∈ H^[j] '' W₀ at hz'
    obtain ⟨w', hw', rfl⟩ := hz'
    have hw'i : H^[i] w' ∈ U := HmemU i w' (WsubU hw')
    have hmem_i : H^[i] w' ∈ V i := by
      change H^[i] w' ∈ H^[i] '' W₀
      exact ⟨w', hw', rfl⟩
    have hdist : dist z (H^[i] w') ≤ Metric.diam (V i) :=
      Metric.dist_le_diam_of_mem (Vbdd i) hz hmem_i
    have hzlt : Complex.im z < Complex.im (H^[i] w') + κ := by
      have himle : Complex.im z - Complex.im (H^[i] w') ≤ ‖z - H^[i] w'‖ := by
        have h := Complex.abs_im_le_norm (z - H^[i] w')
        rw [Complex.sub_im] at h
        exact (le_abs_self _).trans h
      rw [dist_eq_norm] at hdist
      have hlt := Vdiam_lt i
      linarith
    have hdj : H^[j] w' = H^[j - i] (H^[i] w') := by
      conv_lhs => rw [← Nat.sub_add_cancel hij.le]
      rw [Function.iterate_add_apply]
    have hdrift' : Complex.im (H^[i] w') + ((j - i : ℕ) : ℝ) * κ ≤ Complex.im (H^[j] w') := by
      rw [hdj]
      exact him_drift (j - i) (H^[i] w') hw'i
    have hκle : κ ≤ ((j - i : ℕ) : ℝ) * κ := by
      have hj1 : (1 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by
        have h1 : 1 ≤ j - i := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hij)
        exact_mod_cast h1
      nlinarith [hκ]
    linarith
  have hheight : ∀ M : ℝ, ∃ T : ℕ, ∀ t, T ≤ t → ∀ w ∈ V t, M < Complex.im w := by
    intro M
    obtain ⟨T, hT⟩ := exists_nat_gt ((M - y') / κ)
    refine ⟨T, ?_⟩
    intro t ht w hw
    change w ∈ H^[t] '' W₀ at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvU : v ∈ U := WsubU hv
    have hvim : y' < Complex.im v := hvU
    have h1 := him_drift t v hvU
    have hMT : M < y' + (T : ℝ) * κ := by
      rw [div_lt_iff₀ hκ] at hT
      linarith
    have hTt : (T : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have h2 : y' + (T : ℝ) * κ ≤ y' + (t : ℝ) * κ := by nlinarith [hκ]
    linarith
  -- consecutive discs are close
  have hclose : ∀ t, ∃ u ∈ V t, ∃ u' ∈ V (t + 1), ‖u - u'‖ < ‖β‖ + κ / 4 + 1 := by
    intro t
    obtain ⟨z₀, hz₀⟩ := hW₀conn.nonempty
    refine ⟨H^[t] z₀, ?_, H^[t+1] z₀, ?_, ?_⟩
    · change H^[t] z₀ ∈ H^[t] '' W₀; exact ⟨z₀, hz₀, rfl⟩
    · change H^[t+1] z₀ ∈ H^[t+1] '' W₀; exact ⟨z₀, hz₀, rfl⟩
    · have hzU : H^[t] z₀ ∈ U := HmemU t z₀ (WsubU hz₀)
      have hinc' : H (H^[t] z₀) = H^[t] z₀ + β + ρ (H^[t] z₀) := hinc _ hzU
      have hρ := hρbd _ hzU
      have hval : H^[t+1] z₀ - H^[t] z₀ = β + ρ (H^[t] z₀) := by
        rw [Nat.add_one, Function.iterate_succ_apply', hinc']
        ring
      calc ‖H^[t] z₀ - H^[t+1] z₀‖ = ‖H^[t+1] z₀ - H^[t] z₀‖ := norm_sub_rev _ _
        _ = ‖β + ρ (H^[t] z₀)‖ := by rw [hval]
        _ ≤ ‖β‖ + ‖ρ (H^[t] z₀)‖ := norm_add_le _ _
        _ ≤ ‖β‖ + κ / 4 := by linarith
        _ < ‖β‖ + κ / 4 + 1 := by linarith
  -- the derivative bound on the discs
  have hderiv : ∀ t, ∀ w ∈ V t, 1 / 3 < ‖deriv ((fun u => R u - β)^[t]) w‖ ∧
      ‖deriv ((fun u => R u - β)^[t]) w‖ < 3 := by
    intro t w hw
    change w ∈ H^[t] '' W₀ at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hyU : y ∈ U := WsubU hy
    have htU : H^[t] y ∈ U := HmemU t y hyU
    have hana : AnalyticAt ℂ (H^[t]) y := Hana t y hyU
    have hstr : HasStrictDerivAt (H^[t]) (deriv (H^[t]) y) y := hana.hasStrictDerivAt
    have hf' : deriv (H^[t]) y ≠ 0 := by
      rw [(hdform t y hyU).2]
      exact div_ne_zero (bne y hyU) (bne _ htU)
    have hev : ∀ᶠ x in 𝓝 y, ((fun u => R u - β)^[t]) ((H^[t]) x) = x := by
      filter_upwards [hUo.mem_nhds hyU] with x hx
      exact Riter t x hx
    have hres := hstr.to_local_left_inverse hf' hev
    have hval : deriv ((fun u => R u - β)^[t]) (H^[t] y) = (deriv (H^[t]) y)⁻¹ :=
      hres.hasDerivAt.deriv
    have hnorm : ‖(deriv (H^[t]) y)⁻¹‖ = ‖deriv L (H^[t] y)‖ / ‖deriv L y‖ := by
      rw [norm_inv, (hdform t y hyU).2, norm_div, inv_div]
    have hAb := derivL_bounds (H^[t] y) htU
    have hBb := derivL_bounds y hyU
    have hBpos : 0 < ‖deriv L y‖ := by linarith [hBb.1]
    rw [hval, hnorm]
    have hge : 1 / 3 ≤ ‖deriv L (H^[t] y)‖ / ‖deriv L y‖ := by
      rw [le_div_iff₀ hBpos]; nlinarith [hAb.1, hBb.2]
    have hle : ‖deriv L (H^[t] y)‖ / ‖deriv L y‖ ≤ 3 := by
      rw [div_le_iff₀ hBpos]; nlinarith [hAb.2, hBb.1]
    have hne1 : ‖deriv L (H^[t] y)‖ / ‖deriv L y‖ ≠ 1 / 3 := by
      intro hcon
      have hcon' : ‖deriv L (H^[t] y)‖ = (1 / 3) * ‖deriv L y‖ :=
        (div_eq_iff (ne_of_gt hBpos)).mp hcon
      have hAeq : ‖deriv L (H^[t] y)‖ = 1 / 2 := by nlinarith [hcon', hAb.1, hBb.2]
      have hBeq : ‖deriv L y‖ = 3 / 2 := by nlinarith [hcon', hAb.1, hBb.2]
      have hconst := hext.1 (H^[t] y) htU hAeq
      rw [hconst y hyU] at hBeq
      norm_num at hBeq
    have hne3 : ‖deriv L (H^[t] y)‖ / ‖deriv L y‖ ≠ 3 := by
      intro hcon
      have hcon' : ‖deriv L (H^[t] y)‖ = 3 * ‖deriv L y‖ :=
        (div_eq_iff (ne_of_gt hBpos)).mp hcon
      have hAeq : ‖deriv L (H^[t] y)‖ = 3 / 2 := by nlinarith [hcon', hAb.2, hBb.1]
      have hBeq : ‖deriv L y‖ = 1 / 2 := by nlinarith [hcon', hAb.2, hBb.1]
      have hconst := hext.2 (H^[t] y) htU hAeq
      rw [hconst y hyU] at hBeq
      norm_num at hBeq
    exact ⟨lt_of_le_of_ne hge (Ne.symm hne1), lt_of_le_of_ne hle hne3⟩
  refine ⟨V, Vzero, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; exact ⟨Vopen t, Vconn t⟩
  · intro t; exact ⟨VsubDR t, Vinj t, Vimg t⟩
  · intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro ζ hζ hζ'
    obtain ⟨z, hz, rfl⟩ := hζ
    obtain ⟨z', hz', heq⟩ := hζ'
    have him : Complex.im z = Complex.im z' := (piExp_im_ne heq).symm
    rcases lt_or_gt_of_ne hij with h | h
    · exact absurd him (ne_of_lt (hsep i j h z hz z' hz'))
    · exact absurd him (ne_of_gt (hsep j i h z' hz' z hz))
  · exact hheight
  · intro t; exact ⟨Vbdd t, Vdiam_half t⟩
  · exact hclose
  · exact hderiv

end

end Work.L62
