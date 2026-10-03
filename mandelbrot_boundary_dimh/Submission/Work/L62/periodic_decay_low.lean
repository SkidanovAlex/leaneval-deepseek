import Mathlib

/-!
# Sharp exponential decay of a bounded periodic holomorphic function on a lower half-plane

If `ψ` is holomorphic and `1`-periodic on the half-plane `{im w < -y}`, is bounded there by `M`
and tends to `0` at `-i∞`, then for every `z` with `im z < -y`,

`‖ψ z‖ ≤ M * exp (-2 π (-y - im z))`.

The exponent is sharp: `ψ z = c * exp (-2 π i z)` with `‖c‖ ≤ M * exp (2 π y)` gives equality.

## Proof

After the reflection `w ↦ -w` and the substitution `q = exp (2 π i w)` the half-plane
`{im w > y}` becomes the punctured disc of radius `R = exp (-2 π y)` and `ψ` becomes the
`q`-expansion of a holomorphic function `F` on that disc.  Since `ψ` tends to `0` at the end,
`F` extends holomorphically to the origin with `F 0 = 0`, and since `ψ` is bounded by `M`, we have
`‖F‖ ≤ M`.  The Schwarz lemma on the disc of radius `R` then gives `‖F q‖ ≤ (M / R) ‖q‖`, which
translates back to the claimed decay.

Formalising the descent needs a *globally* periodic function, so we first push the half-plane up
to a line `{im = c}`, `c > y` (`pushUp`), which stays inside the domain of `ψ`; this makes the
pushed function globally periodic and bounded, and the desired estimate follows with `c` in place
of `y`.  Letting `c ↓ y` gives the sharp constant.

The three reusable ingredients (`cusp_schwarz_ball`: the Schwarz lemma for
`Function.Periodic.cuspFunction`; `flip_periodic_aux`: the push-up construction;
`le_of_forall_exp_decay`: the limiting step) are stated separately below.
-/

namespace Work.L62

open Complex Set Metric Filter Topology
open scoped Topology

/-- Replace the imaginary part of `w` by `max c w.im`. -/
private def pushUp (c : ℝ) (w : ℂ) : ℂ := w.re + (max c w.im) * Complex.I

private lemma pushUp_im (c : ℝ) (w : ℂ) : (pushUp c w).im = max c w.im := by
  simp [pushUp]

private lemma pushUp_eq_self (c : ℝ) {w : ℂ} (h : c ≤ w.im) : pushUp c w = w := by
  simp [pushUp, max_eq_right h, Complex.re_add_im]

private lemma pushUp_add_one (c : ℝ) (w : ℂ) : pushUp c (w + 1) = pushUp c w + 1 := by
  apply Complex.ext <;>
    simp [pushUp, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]

/-- **Schwarz bound for the cusp function.** Let `f : ℂ → ℂ` be globally periodic of period `1`,
bounded by `M`, tending to `0` at `+i∞` and holomorphic on the half-plane `{c < im z}`.  Then for
every `q` with `‖q‖ < exp (-2πc)` — i.e. every `q` of the form `qParam 1 w` with `c < im w` —
the cusp function of `f` satisfies the Schwarz bound `‖cuspFunction 1 f q‖ ≤ (M / exp (-2πc)) ‖q‖`.

(The point `q = 0` is covered because `ZeroAtFilter` gives `cuspFunction 1 f 0 = 0`.) -/
theorem cusp_schwarz_ball {f : ℂ → ℂ} {M c : ℝ}
    (hfper : Function.Periodic f 1)
    (hbd : ∀ w : ℂ, ‖f w‖ ≤ M)
    (hzero : (Filter.comap Complex.im Filter.atTop).ZeroAtFilter f)
    (hdiff : ∀ z : ℂ, c < Complex.im z → DifferentiableAt ℂ f z) :
    ∀ q : ℂ, ‖q‖ < Real.exp (-2 * Real.pi * c) →
      ‖Function.Periodic.cuspFunction 1 f q‖ ≤ M / Real.exp (-2 * Real.pi * c) * ‖q‖ := by
  set R : ℝ := Real.exp (-2 * Real.pi * c) with hRdef
  have hMnn : 0 ≤ M := (norm_nonneg (f 0)).trans (hbd 0)
  have hev : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ f z := by
    refine Filter.eventually_iff_exists_mem.mpr ⟨{z : ℂ | c < z.im}, ?_, fun z hz => hdiff z hz⟩
    rw [Filter.mem_comap]
    exact ⟨Set.Ioi c, Filter.Ioi_mem_atTop c, fun x hx => hx⟩
  have hbdd : (Filter.comap Complex.im Filter.atTop).BoundedAtFilter f := by
    rw [Filter.BoundedAtFilter, Asymptotics.isBigO_iff]
    exact ⟨max M 0, Filter.Eventually.of_forall fun x => by
      simp only [Pi.one_apply, norm_one, mul_one]
      exact (hbd x).trans (le_max_left M 0)⟩
  have hd0 : DifferentiableAt ℂ (Function.Periodic.cuspFunction 1 f) 0 :=
    Function.Periodic.differentiableAt_cuspFunction_zero one_pos hfper hev hbdd
  have h0 : Function.Periodic.cuspFunction 1 f 0 = 0 :=
    Function.Periodic.cuspFunction_zero_of_zero_at_inf one_pos hzero
  -- differentiability at the non-zero points of the disc
  have hdne : ∀ q : ℂ, q ≠ 0 → ‖q‖ < R →
      DifferentiableAt ℂ (Function.Periodic.cuspFunction 1 f) q := by
    intro q hq hqR
    set z : ℂ := Function.Periodic.invQParam 1 q with hz
    have hqz : Function.Periodic.qParam 1 z = q := by
      rw [hz]; exact Function.Periodic.qParam_right_inv one_ne_zero hq
    have himz : c < z.im := by
      refine (Function.Periodic.norm_qParam_lt_iff one_pos c z).mp ?_
      rw [hqz, show -2 * Real.pi * c / 1 = -2 * Real.pi * c by ring]
      exact hqR
    have h := Function.Periodic.differentiableAt_cuspFunction one_ne_zero hfper (hdiff z himz)
    rwa [hqz] at h
  have hdOn : DifferentiableOn ℂ (Function.Periodic.cuspFunction 1 f) (ball 0 R) := by
    intro q hq
    rw [mem_ball, dist_zero_right] at hq
    rcases eq_or_ne q 0 with rfl | hq0
    · exact hd0.differentiableWithinAt
    · exact (hdne q hq0 hq).differentiableWithinAt
  have hmaps : MapsTo (Function.Periodic.cuspFunction 1 f) (ball 0 R)
      (closedBall (Function.Periodic.cuspFunction 1 f 0) M) := by
    intro q hq
    rw [mem_ball, dist_zero_right] at hq
    rw [mem_closedBall]
    rcases eq_or_ne q 0 with rfl | hq0
    · rw [h0, dist_self]; exact hMnn
    · rw [h0, dist_zero_right, Function.Periodic.cuspFunction_eq_of_nonzero 1 f hq0]
      exact hbd _
  intro q hq
  have hq' : q ∈ ball 0 R := by rw [mem_ball, dist_zero_right]; exact hq
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdOn hmaps hq'
  rw [dist_eq_norm, h0, sub_zero, dist_zero_right, hRdef] at h
  exact h

/-- **Push-up of a periodic holomorphic function on a half-plane.**  Let `ψ` be holomorphic and
`1`-periodic on the half-plane `{im < -y}`, bounded by `M` there and tending to `0` at `-i∞`, and
let `c > y`.  Define `G w = ψ (-(w.re + max c w.im * I))` (the argument is first *pushed up* so
that its imaginary part is at most `-c < -y`, and then reflected).  Then `G` is globally
`1`-periodic, globally bounded by `M`, tends to `0` at `+i∞`, is complex differentiable on
`{c < im w}`, and agrees with `w ↦ ψ (-w)` on `{c ≤ im w}`. -/
theorem flip_periodic_aux {ψ : ℂ → ℂ} {y M c : ℝ} (hcy : y < c)
    (hhol : DifferentiableOn ℂ ψ {w : ℂ | Complex.im w < -y})
    (hper : ∀ w : ℂ, Complex.im w < -y → ψ (w + 1) = ψ w)
    (hbd : ∀ w : ℂ, Complex.im w < -y → ‖ψ w‖ ≤ M)
    (hlim : Filter.Tendsto ψ (Filter.comap Complex.im Filter.atBot) (nhds 0)) :
    Function.Periodic (fun w : ℂ => ψ (-(pushUp c w))) 1 ∧
    (∀ w : ℂ, ‖ψ (-(pushUp c w))‖ ≤ M) ∧
    (Filter.comap Complex.im Filter.atTop).ZeroAtFilter (fun w : ℂ => ψ (-(pushUp c w))) ∧
    (∀ z : ℂ, c < Complex.im z → DifferentiableAt ℂ (fun w : ℂ => ψ (-(pushUp c w))) z) ∧
    (∀ w : ℂ, c ≤ Complex.im w → ψ (-(pushUp c w)) = ψ (-w)) := by
  have hpmax : ∀ w : ℂ, c ≤ max c w.im := fun w => le_max_left c w.im
  have hnegim : ∀ w : ℂ, (-(pushUp c w)).im = -(max c w.im) := by
    intro w; rw [Complex.neg_im, pushUp_im]
  have hmem : ∀ w : ℂ, (-(pushUp c w)).im < -y := by
    intro w; rw [hnegim]; linarith [hpmax w, hcy]
  have hsid : ∀ w : ℂ, (-(pushUp c w) - 1).im < -y := by
    intro w; rw [Complex.sub_im, Complex.one_im, hnegim]; linarith [hpmax w, hcy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- global periodicity
    intro w
    show ψ (-(pushUp c (w + 1))) = ψ (-(pushUp c w))
    rw [pushUp_add_one, show -(pushUp c w + 1) = -(pushUp c w) - 1 by ring]
    have h := (hper (-(pushUp c w) - 1) (hsid w)).symm
    rw [show (-(pushUp c w) - 1) + 1 = -(pushUp c w) by ring] at h
    exact h
  · intro w; exact hbd _ (hmem w)
  · -- vanishing at `+i∞`
    have hneg : Filter.Tendsto (fun w : ℂ => -w) (Filter.comap Complex.im Filter.atTop)
        (Filter.comap Complex.im Filter.atBot) := by
      rw [Filter.tendsto_comap_iff]
      have h1 : (Complex.im ∘ fun w : ℂ => -w) = fun w => -(Complex.im w) := by
        funext w; simp [Complex.neg_im]
      rw [h1]
      exact tendsto_neg_atTop_atBot.comp tendsto_comap
    have h2 : Filter.Tendsto (fun w : ℂ => ψ (-w)) (Filter.comap Complex.im Filter.atTop)
        (nhds 0) := hlim.comp hneg
    have hpush : (fun w : ℂ => ψ (-(pushUp c w))) =ᶠ[Filter.comap Complex.im Filter.atTop]
        (fun w : ℂ => ψ (-w)) := by
      refine Filter.eventually_iff_exists_mem.mpr ⟨{w : ℂ | c ≤ w.im}, ?_, ?_⟩
      · rw [Filter.mem_comap]
        exact ⟨Set.Ici c, Filter.Ici_mem_atTop c, fun x hx => hx⟩
      · intro w hw
        show ψ (-(pushUp c w)) = ψ (-w)
        rw [pushUp_eq_self c hw]
    exact h2.congr' hpush.symm
  · -- differentiability on `{c < im w}`
    intro z hz
    have hopen : {w : ℂ | c < w.im} ∈ 𝓝 z :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
    have heq : (fun w : ℂ => ψ (-(pushUp c w))) =ᶠ[𝓝 z] (fun w : ℂ => ψ (-w)) := by
      filter_upwards [hopen] with w hw
      show ψ (-(pushUp c w)) = ψ (-w)
      rw [pushUp_eq_self c (le_of_lt hw)]
    have hmem2 : {w : ℂ | w.im < -y} ∈ 𝓝 (-z) := by
      refine (isOpen_lt Complex.continuous_im continuous_const).mem_nhds ?_
      show (-z).im < -y
      rw [Complex.neg_im]; linarith [hz, hcy]
    have hcomp : DifferentiableAt ℂ (fun w : ℂ => ψ (-w)) z :=
      (hhol.differentiableAt hmem2).comp z (by fun_prop)
    exact hcomp.congr_of_eventuallyEq heq
  · intro w hw
    show ψ (-(pushUp c w)) = ψ (-w)
    rw [pushUp_eq_self c hw]

/-- **Pushing a uniform exponential bound to the boundary.**  If `A ≤ M * exp (-2π (s - c))` for
every `c` with `y < c < s`, then the same bound holds at `c = y`.  (The right-hand side is
continuous in `c`, and the half-line `[A, ∞)` is closed.) -/
theorem le_of_forall_exp_decay {A M y s : ℝ} (hys : y < s)
    (h : ∀ c : ℝ, y < c → c < s → A ≤ M * Real.exp (-2 * Real.pi * (s - c))) :
    A ≤ M * Real.exp (-2 * Real.pi * (s - y)) := by
  have hcont : Continuous fun c : ℝ => M * Real.exp (-2 * Real.pi * (s - c)) := by fun_prop
  have htend : Filter.Tendsto (fun c : ℝ => M * Real.exp (-2 * Real.pi * (s - c)))
      (𝓝[>] y) (𝓝 (M * Real.exp (-2 * Real.pi * (s - y)))) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ c : ℝ in 𝓝[>] y, A ≤ M * Real.exp (-2 * Real.pi * (s - c)) := by
    rw [eventually_nhdsWithin_iff]
    have hIio : Set.Iio s ∈ 𝓝 y := isOpen_Iio.mem_nhds hys
    filter_upwards [hIio] with c hcs hcy
    exact h c hcy hcs
  exact ge_of_tendsto htend hev

set_option linter.unusedVariables false in
/-- **Sharp exponential decay on a lower half-plane.**  A `1`-periodic holomorphic function on
`{im < -y}`, bounded by `M` and tending to `0` at `-i∞`, decays like `exp (2 π i z)`:  for every
`z` with `im z < -y`, `‖ψ z‖ ≤ M * exp (-2 π (-y - im z))`. -/
theorem periodic_decay_low {ψ : ℂ → ℂ} {y M : ℝ} (hM : 0 ≤ M)
    (hhol : DifferentiableOn ℂ ψ {w : ℂ | Complex.im w < -y})
    (hper : ∀ w : ℂ, Complex.im w < -y → ψ (w + 1) = ψ w)
    (hbd : ∀ w : ℂ, Complex.im w < -y → ‖ψ w‖ ≤ M)
    (hlim : Filter.Tendsto ψ (Filter.comap Complex.im Filter.atBot) (nhds 0)) :
    ∀ z : ℂ, Complex.im z < -y → ‖ψ z‖ ≤ M * Real.exp (-2 * Real.pi * (-y - Complex.im z)) := by
  intro z hz
  -- for every `c ∈ (y, -im z)` we get the estimate with `c` in place of `y`
  have haux : ∀ c : ℝ, y < c → c < -Complex.im z →
      ‖ψ z‖ ≤ M * Real.exp (-2 * Real.pi * (-Complex.im z - c)) := by
    intro c hcy hcs
    obtain ⟨hper', hbd', hzero', hdiff', hagree'⟩ := flip_periodic_aux hcy hhol hper hbd hlim
    have hS := cusp_schwarz_ball (c := c) (M := M) hper' hbd' hzero' hdiff'
    set w : ℂ := -z with hw
    have hwim : c ≤ w.im := by rw [hw, Complex.neg_im]; linarith
    have hq : ‖Function.Periodic.qParam 1 w‖ < Real.exp (-2 * Real.pi * c) := by
      rw [Function.Periodic.norm_qParam 1 w, Real.exp_lt_exp,
        show -2 * Real.pi * w.im / 1 = -2 * Real.pi * w.im by ring, hw, Complex.neg_im]
      rw [show -2 * Real.pi * (-z.im) = -(2 * Real.pi * (-z.im)) by ring,
        show -2 * Real.pi * c = -(2 * Real.pi * c) by ring, neg_lt_neg_iff]
      exact mul_lt_mul_of_pos_left hcs (by positivity)
    have hb := hS (Function.Periodic.qParam 1 w) hq
    rw [Function.Periodic.eq_cuspFunction (h := (1:ℝ))
          (f := fun w : ℂ => ψ (-(pushUp c w))) one_ne_zero hper' w,
        hagree' w hwim, Function.Periodic.norm_qParam 1 w] at hb
    have hnegw : -w = z := by rw [hw]; simp
    rw [hnegw] at hb
    have hexp1 : Real.exp (-2 * Real.pi * w.im / 1) = Real.exp (2 * Real.pi * Complex.im z) := by
      rw [show -2 * Real.pi * w.im / 1 = -2 * Real.pi * w.im by ring]
      congr 1
      rw [hw, Complex.neg_im]; ring
    rw [hexp1] at hb
    rw [show M * Real.exp (-2 * Real.pi * (-Complex.im z - c))
        = M / Real.exp (-2 * Real.pi * c) * Real.exp (2 * Real.pi * Complex.im z) by
      rw [show -2 * Real.pi * (-Complex.im z - c)
          = 2 * Real.pi * c + 2 * Real.pi * Complex.im z by ring]
      rw [Real.exp_add, div_eq_mul_inv, ← Real.exp_neg,
        show -(-2 * Real.pi * c) = 2 * Real.pi * c by ring]
      ring]
    exact hb
  have hys : y < -Complex.im z := by linarith
  rw [show -2 * Real.pi * (-y - Complex.im z) = -2 * Real.pi * (-Complex.im z - y) by ring]
  exact le_of_forall_exp_decay hys (fun c hcy hcs => haux c hcy hcs)

end Work.L62
