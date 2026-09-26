import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

/-!
# There is no continuous retraction of the closed disc onto its boundary circle

Let `𝔻 = {z : ℂ | ‖z‖ ≤ 1}` be the closed unit disc and `r : 𝔻 → 𝔻` a continuous map which

* takes all its values in the unit circle (`hr`), and
* fixes the boundary circle pointwise (`hf`).

Then `False` (`Work.Smooth.SphereJordan.no_retraction_disc`).

## The mathematics

The loop `θ ↦ r (e^{iθ}) = e^{iθ}` of the unit circle is *null-homotopic*: it extends continuously
over the disc (it is `r` itself, read as a map to the circle).  Its **degree** is therefore `0`.
On the other hand the loop `θ ↦ e^{iθ}` has the continuous lift `Λ θ = θ` to the universal cover
`Complex.exp : ℂ → ℂ ∖ {0}` of the punctured plane, so its degree is `1`: `Λ (2π) - Λ 0 = 2πi ≠ 0`.
A loop which extends over the disc has all its lifts closed (`Λ (2π) = Λ 0`), which is the
contradiction.

The formalisation of the last step is the standard monodromy computation for a covering map:

* `Work.Smooth.SphereJordan.NoRetraction.discScale` is the radial contraction of the disc,
  `(a, t) ↦ a • e^{it}` for `a ∈ [0,1]`; it exhibits the loop `θ ↦ r (e^{iθ})` as the end of a
  homotopy `H (s, t) = r (s • e^{it})` whose *start* is the constant loop at `r 0`;
* `H` is lifted along the covering `Complex.exp : ℂ → ℂ ∖ {0}` by the homotopy lifting property
  (`IsCoveringMap.liftHomotopy`); the lift `lk` of the restriction of `H` to `{0} × I` is the
  constant map `log (r 0)`;
* the two parametrisations of the boundary circle of the *square* `I × I` are *radial*, so the
  difference `s ↦ lk (s,1) - lk (s,0)` exponentiates to `1`; by uniqueness of the lift through the
  covering in the connected parameter `s`
  (`Work.Smooth.SphereJordan.NoRetraction.exp_eq_one_const`, which is
  `IsCoveringMap.const_of_comp` for `Complex.exp`) it vanishes, so `lk (1,1) = lk (1,0)`;
* the map `t ↦ lk (1,t) - 2πi t` also exponentiates to `1`, so it is constant as well, giving
  `lk (1,1) - 2πi = lk (1,0)` together with the previous line: `2πi = 0`, absurd.

An alternative route, using instead the covering `Circle.exp : ℝ → S¹` and the monodromy statement
`Work.CoreTopology.circle_lift_eq_of_extends_disk` ("a loop of `S¹` extending over the disc has
every lift closed"), is the one taken by `Work.Smooth.SphereJordan.no_retraction_disc_aux` in
`Submission/Work/Smooth/SphereJordan/discEmbedding_surjective.lean`; the present file is
self-contained and needs nothing from the workspace besides `Defs`.

## Main definitions and results

* `NoRetraction.discScale`, `NoRetraction.continuous_discScale` — the radial contraction `(a,t) ↦ a • e^{it}`;
* `NoRetraction.exp_eq_one_const` — a continuous map to `ℂ` whose exponential is `1` is constant on
  `[0,1]` (uniqueness of the lift through `Complex.exp` for a connected parameter space);
* **`Work.Smooth.SphereJordan.no_retraction_disc`** — the theorem.
-/

namespace Work.Smooth.SphereJordan

namespace NoRetraction

open Set

/-- The parametrisation `θ ↦ e^{iθ}` of the boundary circle of the disc is continuous. -/
theorem continuous_circlePoint : Continuous (circlePoint : ℝ → Disc) := by
  refine Continuous.subtype_mk ?_ (fun θ => (circlePoint θ).2)
  show Continuous fun θ : ℝ => Complex.exp (θ * Complex.I)
  fun_prop

/-- The boundary circle consists of points of norm one. -/
theorem coreNormCirclePoint (θ : ℝ) : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- The parametrisation of the boundary circle is `2π`-periodic. -/
theorem circlePoint_add_two_pi (θ : ℝ) : circlePoint (θ + 2 * Real.pi) = circlePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I from by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `circlePoint (2π) = circlePoint 0`: the boundary parametrisation is a loop. -/
theorem circlePoint_two_pi : circlePoint (2 * Real.pi) = circlePoint 0 := by
  simpa using circlePoint_add_two_pi 0

/-- **The radial contraction of the disc**: the point `a • e^{it}` of the closed unit disc, for
`a ∈ [0,1]` (the scaling is that of the ambient plane `ℂ`). -/
noncomputable def discScale (a : unitInterval) (t : ℝ) : Disc :=
  ⟨(a : ℝ) • ((circlePoint t : Disc) : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have h1 : |(a : ℝ)| ≤ 1 := by rw [abs_of_nonneg a.2.1]; exact a.2.2
    have h2 : ‖((circlePoint t : Disc) : ℂ)‖ = 1 := coreNormCirclePoint t
    rw [h2, mul_one]
    exact h1⟩

@[simp] theorem discScale_zero (t : ℝ) : discScale 0 t = 0 := by
  apply Subtype.ext; simp [discScale]

@[simp] theorem discScale_one (t : ℝ) : discScale 1 t = circlePoint t := by
  apply Subtype.ext; simp [discScale]

/-- The radial contraction is `2π`-periodic in the angle. -/
theorem discScale_per (a : unitInterval) : discScale a (2 * Real.pi) = discScale a 0 := by
  apply Subtype.ext; simp [discScale, circlePoint_two_pi]

/-- The radial contraction is continuous on `[0,1] × ℝ`. -/
theorem continuous_discScale : Continuous fun p : unitInterval × ℝ => discScale p.1 p.2 := by
  have h : Continuous fun p : unitInterval × ℝ => (p.1 : ℝ) • ((circlePoint p.2 : Disc) : ℂ) :=
    (continuous_subtype_val.comp continuous_fst).smul
      ((continuous_subtype_val.comp continuous_circlePoint).comp continuous_snd)
  exact Continuous.subtype_mk h (fun p => (discScale p.1 p.2).2)

/-- **Uniqueness of the lift through `Complex.exp` on a connected parameter space.**

If `v : [0,1] → ℂ` is continuous and `Complex.exp (v t) = 1` for all `t`, then `v` is constant:
`v 1 = v 0`.  This is the instance for the covering map `Complex.exp : ℂ → ℂ ∖ {0}`
(`Complex.isCoveringMap_exp`) of `IsCoveringMap.const_of_comp`, which says that a continuous map
whose composition with a covering map is constant is itself constant on a preconnected domain. -/
theorem exp_eq_one_const {v : unitInterval → ℂ} (hv : Continuous v)
    (h : ∀ t, Complex.exp (v t) = 1) : v 1 = v 0 :=
  Complex.isCoveringMap_exp.const_of_comp hv (fun a a' => Subtype.ext ((h a).trans (h a').symm)) 1 0

end NoRetraction

open NoRetraction

/-- **There is no continuous retraction of the closed unit disc onto its boundary circle.**

If `r : 𝔻 → 𝔻` is continuous, takes all its values on the unit circle and fixes the boundary circle
pointwise, then `False`.

This is Brouwer's theorem in the form needed by the Jordan-curve chapters: the identity loop of the
circle extends over the disc (through `r`), has the non-closed lift `θ ↦ θ` to the universal cover
of `ℂ ∖ {0}`, and a loop extending over the disc has all its lifts closed — the degree `1` of the
identity loop contradicts the degree `0` of a null-homotopic one.  The formalised proof lifts the
radial contraction `H (s, t) = r (s • e^{it})` of the loop along `Complex.exp` by the homotopy
lifting property and compares the two parametrisations of the boundary of the parameter square. -/
theorem no_retraction_disc (r : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc))
    (hr : ∀ z : Work.Smooth.SphereJordan.Disc, ‖((r z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1)
    (hf : ∀ θ : ℝ, r (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) :
    False := by
  -- the radial contraction of the boundary circle to the centre of the disc
  let Φ : unitInterval × unitInterval → Disc :=
    fun st => discScale st.1 (2 * Real.pi * (st.2 : ℝ))
  have hΦc : Continuous Φ := by
    have hg : Continuous fun st : unitInterval × unitInterval => (st.1, 2 * Real.pi * (st.2 : ℝ)) :=
      continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
    exact continuous_discScale.comp hg
  have hΦ0 : ∀ t : unitInterval, Φ (0, t) = 0 := by
    intro t; show discScale (0 : unitInterval) (2 * Real.pi * (t : ℝ)) = 0
    simp
  have hΦ1 : ∀ t : unitInterval, Φ (1, t) = circlePoint (2 * Real.pi * (t : ℝ)) := by
    intro t
    show discScale (1 : unitInterval) (2 * Real.pi * (t : ℝ))
      = circlePoint (2 * Real.pi * (t : ℝ))
    simp
  have hΦper : ∀ s : unitInterval, Φ (s, 1) = Φ (s, 0) := by
    intro s
    show discScale s (2 * Real.pi * ((1 : unitInterval) : ℝ))
      = discScale s (2 * Real.pi * ((0 : unitInterval) : ℝ))
    rw [show (2 * (Real.pi : ℝ) * ((1 : unitInterval) : ℝ)) = 2 * Real.pi by norm_num,
        show (2 * (Real.pi : ℝ) * ((0 : unitInterval) : ℝ)) = 0 by norm_num]
    exact discScale_per s
  -- the loop in the punctured plane, read in the covering space
  have Hne : ∀ st : unitInterval × unitInterval, ((r (Φ st) : Disc) : ℂ) ≠ 0 := by
    intro st
    rw [← norm_ne_zero_iff, hr (Φ st)]
    norm_num
  let H : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun st => ⟨((r (Φ st) : Disc) : ℂ), Hne st⟩,
      Continuous.subtype_mk ((continuous_subtype_val.comp r.continuous).comp hΦc) Hne⟩
  have H_apply : ∀ st : unitInterval × unitInterval,
      ((H st : {z : ℂ // z ≠ 0}) : ℂ) = ((r (Φ st) : Disc) : ℂ) := fun st => rfl
  -- a lift of the starting circle `H (0, ·)`, which is constant
  have hc₀ : ((r 0 : Disc) : ℂ) ≠ 0 := by
    rw [← norm_ne_zero_iff, hr 0]
    norm_num
  let f : C(unitInterval, ℂ) := ContinuousMap.const unitInterval (Complex.log ((r 0 : Disc) : ℂ))
  have hf_apply : ∀ t : unitInterval, f t = Complex.log ((r 0 : Disc) : ℂ) := fun t => rfl
  have H_0 : ∀ a : unitInterval,
      H (0, a) = (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) (f a) := by
    intro a
    apply Subtype.ext
    show ((r (Φ (0, a)) : Disc) : ℂ) = Complex.exp (f a)
    rw [hf_apply a, Complex.exp_log hc₀, hΦ0 a]
  -- the lift of the whole homotopy along the universal cover of the punctured plane
  let lk : C(unitInterval × unitInterval, ℂ) := Complex.isCoveringMap_exp.liftHomotopy H f H_0
  have lk_lifts : (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ lk = H :=
    Complex.isCoveringMap_exp.liftHomotopy_lifts H f H_0
  have lk_zero : ∀ a : unitInterval, lk (0, a) = f a :=
    Complex.isCoveringMap_exp.liftHomotopy_zero H f H_0
  have lk_exp : ∀ st : unitInterval × unitInterval, Complex.exp (lk st) = (H st : ℂ) :=
    fun st => congrArg Subtype.val (congrFun lk_lifts st)
  have hHper : ∀ s : unitInterval, H (s, 1) = H (s, 0) := by
    intro s
    apply Subtype.ext
    show ((r (Φ (s, 1)) : Disc) : ℂ) = ((r (Φ (s, 0)) : Disc) : ℂ)
    rw [hΦper s]
  -- Step 1: the lift of the whole boundary is a family of loops, so its two end circles agree
  have hstep1 : lk (1, 1) = lk (1, 0) := by
    have hcont : Continuous fun s : unitInterval => lk (s, 1) - lk (s, 0) := by fun_prop
    have hexp : ∀ s : unitInterval, Complex.exp (lk (s, 1) - lk (s, 0)) = 1 := by
      intro s
      rw [Complex.exp_sub, div_eq_one_iff_eq (Complex.exp_ne_zero _), lk_exp (s, 1), lk_exp (s, 0),
        hHper s]
    have h0 : lk (0, 1) - lk (0, 0) = 0 := by
      rw [lk_zero 1, lk_zero 0, hf_apply 1, hf_apply 0, sub_self]
    exact sub_eq_zero.mp ((exp_eq_one_const hcont hexp).trans h0)
  -- Step 2: the lift of the fundamental circle ends one period away from where it starts
  have hstep2 : lk (1, 1) - 2 * (Real.pi : ℂ) * Complex.I = lk (1, 0) := by
    have hcont : Continuous fun t : unitInterval =>
        lk (1, t) - (2 * (Real.pi : ℂ) * (t : ℝ)) * Complex.I := by fun_prop
    have hexp : ∀ t : unitInterval,
        Complex.exp (lk (1, t) - (2 * (Real.pi : ℂ) * (t : ℝ)) * Complex.I) = 1 := by
      intro t
      have h1 : Complex.exp (lk (1, t))
          = Complex.exp (2 * (Real.pi : ℂ) * (t : ℝ) * Complex.I) := by
        rw [lk_exp (1, t), H_apply (1, t), hΦ1 t, hf (2 * Real.pi * (t : ℝ)),
          Work.Smooth.Jordan.circlePoint_coe]
        congr 1
        push_cast
        ring
      rw [Complex.exp_sub, div_eq_one_iff_eq (Complex.exp_ne_zero _), h1]
    have h1 := exp_eq_one_const hcont hexp
    have h2 : lk (1, 1) - (2 * (Real.pi : ℂ) * ((1 : unitInterval) : ℝ)) * Complex.I
        = lk (1, 0) - (2 * (Real.pi : ℂ) * ((0 : unitInterval) : ℝ)) * Complex.I := h1
    simpa using h2
  -- the two descriptions of `lk (1, ·)` contradict each other
  have hzero : (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    have h : lk (1, 1) - 2 * (Real.pi : ℂ) * Complex.I = lk (1, 1) := by rw [hstep2, hstep1]
    have h2 : (lk (1, 1) - 2 * (Real.pi : ℂ) * Complex.I) - lk (1, 1) = 0 := sub_eq_zero.mpr h
    have h3 : -(2 * (Real.pi : ℂ) * Complex.I) = 0 := by rw [← h2]; ring
    exact neg_eq_zero.mp h3
  exact Work.Smooth.Jordan.two_pi_I_ne_zero hzero

end Work.Smooth.SphereJordan
