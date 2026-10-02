import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Set Function Filter
open scoped Topology

/-! ### Auxiliary lemmas

These three lemmas are the elementary ingredients of the main result below; they are also
stated (and proved) as standalone leaves of the library in
`Submission/Work/LandLeaves/{exists_fixedpoint_in_closedBall,iterate_norm_sub_le,continuousOn_iterate_family}.lean`.
-/

/-- Banach fixed point on a closed ball: if `f` maps the closed ball `B(y,ρ)` into itself
(`hmaps` puts `f y` in the ball, `hlip` is the contraction which keeps the ball invariant) and
is `κ`-Lipschitz on it with `κ < 1`, then `f` has a fixed point in the ball. -/
private theorem aux_exists_fixedpoint_in_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : E → E} {y : E} {ρ κ : ℝ} (hρ : 0 < ρ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hmaps : ‖f y - y‖ ≤ (1 - κ) * ρ)
    (hlip : ∀ z z' : E, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ → ‖f z - f z'‖ ≤ κ * ‖z - z'‖) :
    ∃ z : E, ‖z - y‖ ≤ ρ ∧ f z = z := by
  have hball : ∀ z : E, ‖z - y‖ ≤ ρ → ‖f z - y‖ ≤ ρ := by
    intro z hz
    have h1 : ‖f z - y‖ ≤ ‖f z - f y‖ + ‖f y - y‖ := by
      rw [show f z - y = (f z - f y) + (f y - y) by abel]
      exact norm_add_le _ _
    have h2 : ‖f z - f y‖ ≤ κ * ‖z - y‖ := hlip z y hz (by simpa using hρ.le)
    have h3 : κ * ‖z - y‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left hz hκ0
    nlinarith [hmaps]
  have hsc : IsComplete (Metric.closedBall y ρ : Set E) := Metric.isClosed_closedBall.isComplete
  have hsf : MapsTo f (Metric.closedBall y ρ) (Metric.closedBall y ρ) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    exact hball z hz
  have hcw : ContractingWith ⟨κ, hκ0⟩ (Set.MapsTo.restrict f (Metric.closedBall y ρ)
      (Metric.closedBall y ρ) hsf) := by
    constructor
    · exact_mod_cast hκ1
    · refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have ha : ‖(a : E) - y‖ ≤ ρ := by
        have h := a.2
        rw [Metric.mem_closedBall, dist_eq_norm] at h
        exact h
      have hb : ‖(b : E) - y‖ ≤ ρ := by
        have h := b.2
        rw [Metric.mem_closedBall, dist_eq_norm] at h
        exact h
      show dist (f (a : E)) (f (b : E)) ≤ κ * dist (a : E) (b : E)
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip _ _ ha hb
  obtain ⟨z, hz, hfx, -⟩ :=
    ContractingWith.exists_fixedPoint' hsc hsf hcw (x := y)
      (by rw [Metric.mem_closedBall]; simpa using hρ.le) (edist_ne_top y (f y))
  exact ⟨z, by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, hfx⟩

/-- Iterating a `κ`-Lipschitz self-map that preserves a set `s` dilates distances of points of
`s` by at most `κ ^ n`. -/
private theorem aux_iterate_norm_sub_le {E : Type*} [NormedAddCommGroup E] {f : E → E}
    {s : Set E} {κ : ℝ} (hκ0 : 0 ≤ κ) (hmaps : Set.MapsTo f s s)
    (hlip : ∀ z z' : E, z ∈ s → z' ∈ s → ‖f z - f z'‖ ≤ κ * ‖z - z'‖) (n : ℕ) {a b : E}
    (ha : a ∈ s) (hb : b ∈ s) :
    ‖f^[n] a - f^[n] b‖ ≤ κ ^ n * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ k ih =>
    have ha' : f^[k] a ∈ s := hmaps.iterate k ha
    have hb' : f^[k] b ∈ s := hmaps.iterate k hb
    have h1 := hlip _ _ ha' hb'
    have h2 : κ * ‖f^[k] a - f^[k] b‖ ≤ κ * (κ ^ k * ‖a - b‖) :=
      mul_le_mul_of_nonneg_left ih hκ0
    have h3 : ‖f (f^[k] a) - f (f^[k] b)‖ ≤ κ ^ (k + 1) * ‖a - b‖ := by
      calc ‖f (f^[k] a) - f (f^[k] b)‖ ≤ κ * ‖f^[k] a - f^[k] b‖ := h1
        _ ≤ κ * (κ ^ k * ‖a - b‖) := h2
        _ = κ ^ (k + 1) * ‖a - b‖ := by ring
    simpa only [Function.iterate_succ_apply'] using h3

/-- The `n`-th iterate `p ↦ (F p)^[n] y` of a parametrized family is continuous in `p` on the
ball `B(c,δ)`, assuming the family maps the closed ball `B(y,ρ)` into itself (`hmaps`+`hlip`)
and the uncurried map `(p,z) ↦ F p z` is continuous on `B(c,δ) × B(y,ρ)`. -/
private theorem aux_continuousOn_iterate_family {ι E : Type*} [PseudoMetricSpace ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ι → E → E} {c : ι} {y : E} {δ ρ κ : ℝ} (hρ : 0 < ρ) (hκ0 : 0 ≤ κ)
    (hmaps : ∀ p, dist p c < δ → ‖F p y - y‖ ≤ (1 - κ) * ρ)
    (hlip : ∀ p, dist p c < δ → ∀ z z' : E, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ →
      ‖F p z - F p z'‖ ≤ κ * ‖z - z'‖)
    (hcont : ContinuousOn (fun q : ι × E => F q.1 q.2)
      {q : ι × E | dist q.1 c < δ ∧ ‖q.2 - y‖ ≤ ρ}) (n : ℕ) :
    ContinuousOn (fun p : ι => (F p)^[n] y) {p : ι | dist p c < δ} := by
  have hball : ∀ p, dist p c < δ → ∀ z : E, ‖z - y‖ ≤ ρ → ‖F p z - y‖ ≤ ρ := by
    intro p hp z hz
    have h1 : ‖F p z - y‖ ≤ ‖F p z - F p y‖ + ‖F p y - y‖ := by
      rw [show F p z - y = (F p z - F p y) + (F p y - y) by abel]
      exact norm_add_le _ _
    have h2 : ‖F p z - F p y‖ ≤ κ * ‖z - y‖ := hlip p hp z y hz (by simpa using hρ.le)
    have h3 : κ * ‖z - y‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left hz hκ0
    nlinarith [hmaps p hp]
  have hmem : ∀ p, dist p c < δ → ∀ n : ℕ, ‖(F p)^[n] y - y‖ ≤ ρ := by
    intro p hp n
    induction n with
    | zero => simpa using hρ.le
    | succ k ih => simpa only [Function.iterate_succ_apply'] using hball p hp _ ih
  induction n with
  | zero => simpa using (continuousOn_const (c := y) (s := {p : ι | dist p c < δ}))
  | succ k ih =>
    have hpair : ContinuousOn (fun p : ι => (p, (F p)^[k] y)) {p : ι | dist p c < δ} :=
      continuousOn_id.prodMk ih
    have hmapsto : MapsTo (fun p : ι => (p, (F p)^[k] y)) {p : ι | dist p c < δ}
        {q : ι × E | dist q.1 c < δ ∧ ‖q.2 - y‖ ≤ ρ} := fun p hp => ⟨hp, hmem p hp k⟩
    have key : ContinuousOn (fun p : ι => F p ((F p)^[k] y)) {p : ι | dist p c < δ} :=
      hcont.comp hpair hmapsto
    simpa only [Function.iterate_succ_apply'] using key

/-- **Banach fixed point with a parameter, uniform on a ball.**

Let `F : ι → E → E` be a family of self-maps of a complete normed space `E`, indexed by a
(pseudo)metric space `ι`. Suppose that for every `p` in the ball `B(c, δ)`:
* `F p` maps the closed ball `B(y, ρ)` into itself (`hmaps` + `hlip`), and
* `F p` is `κ`-Lipschitz on `B(y, ρ)`,

and suppose that `(p, z) ↦ F p z` is continuous on `B(c,δ) × B(y,ρ)` and `F c y = y`.

Then there is a *continuous* family of fixed points `yf : ι → E` (a section of the fixed point
correspondence), with `yf c = y`, `F p (yf p) = yf p` on `B(c,δ)`, the a priori bound
`‖yf p - y‖ ≤ ‖F p y - y‖/(1-κ)`, and *uniqueness* of the fixed point of `F p` in `B(y,ρ)`. -/
theorem continuous_family_fixedpoint {ι E : Type*} [PseudoMetricSpace ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ι → E → E} {c : ι} {y : E} {δ ρ κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hbase : F c y = y)
    (hmaps : ∀ p, dist p c < δ → ‖F p y - y‖ ≤ (1 - κ) * ρ)
    (hlip : ∀ p, dist p c < δ → ∀ z z' : E, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ →
      ‖F p z - F p z'‖ ≤ κ * ‖z - z'‖)
    (hcont : ContinuousOn (fun q : ι × E => F q.1 q.2)
      {q : ι × E | dist q.1 c < δ ∧ ‖q.2 - y‖ ≤ ρ}) :
    ∃ yf : ι → E, yf c = y ∧ ContinuousOn yf {p : ι | dist p c < δ} ∧
      (∀ p, dist p c < δ → F p (yf p) = yf p) ∧
      (∀ p, dist p c < δ → ‖yf p - y‖ ≤ ‖F p y - y‖ / (1 - κ)) ∧
      (∀ p, dist p c < δ → ∀ z : E, ‖z - y‖ ≤ ρ → F p z = z → z = yf p) := by
  -- the closed ball `B(y,ρ)` is invariant under every `F p`, `p ∈ B(c,δ)`
  have hball : ∀ p, dist p c < δ → ∀ z : E, ‖z - y‖ ≤ ρ → ‖F p z - y‖ ≤ ρ := by
    intro p hp z hz
    have h1 : ‖F p z - y‖ ≤ ‖F p z - F p y‖ + ‖F p y - y‖ := by
      rw [show F p z - y = (F p z - F p y) + (F p y - y) by abel]
      exact norm_add_le _ _
    have h2 : ‖F p z - F p y‖ ≤ κ * ‖z - y‖ := hlip p hp z y hz (by simpa using hρ.le)
    have h3 : κ * ‖z - y‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left hz hκ0
    nlinarith [hmaps p hp]
  have hmap : ∀ p, dist p c < δ → MapsTo (F p) (Metric.closedBall y ρ) (Metric.closedBall y ρ) := by
    intro p hp z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    exact hball p hp z hz
  -- a fixed point in the ball for every `p ∈ B(c,δ)`
  have hex : ∀ p, dist p c < δ → ∃ z : E, z ∈ Metric.closedBall y ρ ∧ F p z = z := by
    intro p hp
    obtain ⟨z, hz, hfix⟩ :=
      aux_exists_fixedpoint_in_closedBall hρ hκ0 hκ1 (hmaps p hp) (hlip p hp)
    exact ⟨z, by rwa [Metric.mem_closedBall, dist_eq_norm], hfix⟩
  -- the family of fixed points
  set yf : ι → E := fun p => if h : dist p c < δ then Classical.choose (hex p h) else y
    with hyf_def
  have hyf_eq : ∀ p (h : dist p c < δ), yf p = Classical.choose (hex p h) := by
    intro p h
    rw [hyf_def]
    exact dite_eq_left h
  have hyf_mem : ∀ p, dist p c < δ → yf p ∈ Metric.closedBall y ρ := by
    intro p h
    rw [hyf_eq p h]
    exact (Classical.choose_spec (hex p h)).1
  have hyf_fix : ∀ p, dist p c < δ → F p (yf p) = yf p := by
    intro p h
    rw [hyf_eq p h]
    exact (Classical.choose_spec (hex p h)).2
  have hyf_norm : ∀ p, dist p c < δ → ‖yf p - y‖ ≤ ρ := by
    intro p h
    have := hyf_mem p h
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hyf_iter : ∀ p, dist p c < δ → ∀ m : ℕ, (F p)^[m] (yf p) = yf p := by
    intro p h m
    induction m with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hyf_fix p h]
  -- uniqueness of the fixed point in the ball
  have huniq : ∀ p, dist p c < δ → ∀ z w : E, ‖z - y‖ ≤ ρ → ‖w - y‖ ≤ ρ →
      F p z = z → F p w = w → z = w := by
    intro p hp z w hz hw hfz hfw
    have h := hlip p hp z w hz hw
    rw [hfz, hfw] at h
    have hpos : 0 < 1 - κ := by linarith
    have hA : (1 - κ) * ‖z - w‖ ≤ 0 := by linarith
    have h0 : ‖z - w‖ ≤ 0 := by
      by_contra hcon
      have hcon' : 0 < ‖z - w‖ := not_le.mp hcon
      nlinarith [hpos, hA, mul_pos hpos hcon']
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _)))
  refine ⟨yf, ?_, ?_, ?_, ?_, ?_⟩
  · -- `yf c = y`
    have hc : dist c c < δ := by simpa using hδ
    exact huniq c hc (yf c) y (hyf_norm c hc) (by simpa using hρ.le) (hyf_fix c hc) hbase
  · -- continuity of the family, by uniform convergence of the iterates
    have hiter : ∀ n : ℕ, ContinuousOn (fun p : ι => (F p)^[n] y) {p : ι | dist p c < δ} :=
      fun n => aux_continuousOn_iterate_family hρ hκ0 hmaps hlip hcont n
    refine TendstoUniformlyOn.continuousOn ?_ (Filter.Frequently.of_forall (f := atTop) hiter)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hpow : Tendsto (fun n : ℕ => κ ^ n * ρ) atTop (𝓝 (0 : ℝ)) := by
      have h1 : Tendsto (fun n : ℕ => κ ^ n) atTop (𝓝 (0 : ℝ)) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1
      simpa using h1.mul tendsto_const_nhds
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hpow ε hε
    refine Filter.eventually_atTop.2 ⟨N, fun n hn p hp => ?_⟩
    have hlt : κ ^ n * ρ < ε := by
      have h2 := hN n hn
      rwa [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (pow_nonneg hκ0 n) hρ.le)] at h2
    have hbound : dist (yf p) ((F p)^[n] y) ≤ κ ^ n * ρ := by
      have hL := aux_iterate_norm_sub_le hκ0 (hmap p hp)
        (fun z z' hz hz' => hlip p hp z z'
          (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
          (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz'))
        n (hyf_mem p hp) (Metric.mem_closedBall_self hρ.le)
      calc dist (yf p) ((F p)^[n] y) = ‖yf p - (F p)^[n] y‖ := dist_eq_norm _ _
        _ = ‖(F p)^[n] (yf p) - (F p)^[n] y‖ := by rw [hyf_iter p hp n]
        _ ≤ κ ^ n * ‖yf p - y‖ := hL
        _ ≤ κ ^ n * ρ := mul_le_mul_of_nonneg_left (hyf_norm p hp) (pow_nonneg hκ0 n)
    exact lt_of_le_of_lt hbound hlt
  · intro p hp
    exact hyf_fix p hp
  · -- a priori bound
    intro p hp
    have h1 : ‖yf p - y‖ ≤ κ * ‖yf p - y‖ + ‖F p y - y‖ := by
      have hdecomp : yf p - y = (F p (yf p) - F p y) + (F p y - y) := by
        rw [hyf_fix p hp]; abel
      calc ‖yf p - y‖ = ‖(F p (yf p) - F p y) + (F p y - y)‖ := by rw [hdecomp]
        _ ≤ ‖F p (yf p) - F p y‖ + ‖F p y - y‖ := norm_add_le _ _
        _ ≤ κ * ‖yf p - y‖ + ‖F p y - y‖ :=
            add_le_add (hlip p hp (yf p) y (hyf_norm p hp) (by simpa using hρ.le)) le_rfl
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - κ)]
    linarith
  · -- uniqueness in the ball
    intro p hp z hz hfz
    exact huniq p hp z (yf p) hz (hyf_norm p hp) hfz (hyf_fix p hp)

end Work.LandLeaves
