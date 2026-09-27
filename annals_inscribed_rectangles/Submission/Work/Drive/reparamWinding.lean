import Mathlib
import Submission.Work.Drive.WindingNumber
import Submission.Work.Drive.dirC_half_perp
import Submission.Work.Drive.chord_loop_winding

/-!
# The parametrisation bridge `Circle` ⇄ `UnitAddCircle` (wiring step 1 of the capping)

The winding API (`Work.Drive.winding`, `Work.Drive.winding_values`,
`Work.Drive.exists_winding_ne_zero`, `Work.Drive.exists_translate_origin_winding_ne_zero`) is stated
for curves `UnitAddCircle → ℝ × ℝ`, while the capping API (`Work.Drive.position_angle_lift`,
`Work.Drive.polarLift`, `Work.Drive.exists_periodic_cap_angle`) is stated for curves
`Circle → ℝ × ℝ`.  This file supplies the dictionary between the two parametrisations and the
transport of a lift total along it — the only non-instantiation item of step 1 of the wiring of the
capping (`OMEGA_CHAIN_STATUS.md`, `BRIDGE_CIRCLE_UNITADD.md`).

* `Work.Drive.ccirc` is the `Circle`-valued dictionary `φ ↦ e^{2πiφ}` on `ℝ/ℤ` (the
  `AddCircle.homeomorphCircle`-mediated homeomorphism, *not* followed by the coercion into `ℂ`);
* `Work.Drive.ccirc_coe_eq_exp` identifies it with the standard parametrisation
  `t ↦ Circle.exp (2π t)` of the unit circle — this is what makes a `UnitAddCircle`-curve
  `u ↦ γ (ccirc u)` and a `Circle`-curve `γ` the same closed curve;
* `Work.Drive.lift_total_reparam` is the **reparametrisation invariance of a lift total**: a
  continuous lift `ΨU` of the doubled direction of `φ ↦ γ (ccirc φ) - c` and a continuous lift `ΨC`
  of the doubled direction of `t ↦ γ (exp t) - c` have the same total change over a period,
  `ΨU 1 - ΨU 0 = ΨC (2π) - ΨC 0`;
* `Work.Drive.lift_total_eq_winding` is the consequence used by the wiring: the total of the lift
  `ΨC` on the `Circle` side is the winding number of the `UnitAddCircle`-curve `u ↦ γ (ccirc u) - c`.
  With `Work.Drive.winding_values` (the value is `0` or `±2`) and
  `Work.Drive.exists_translate_origin_winding_ne_zero` (some translate has non-zero winding) this
  produces the lift `Ψ` of the doubled *position* direction with total `±2` that the sign-match step
  of the capping consumes.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open scoped Topology ContDiff

/-- **The dictionary `ℝ/ℤ → S¹`.**  The `AddCircle.homeomorphCircle`-mediated homeomorphism from
`UnitAddCircle = ℝ/ℤ` to the unit circle, kept `Circle`-valued (so that it can be used as the
parametrisation of a `Circle`-curve); its coercion to `ℂ` is `Work.Drive.circleOf`. -/
def ccirc (φ : UnitAddCircle) : Circle :=
  AddCircle.homeomorphCircle (T := 1) one_ne_zero φ

lemma ccirc_continuous : Continuous ccirc :=
  (AddCircle.homeomorphCircle (T := 1) one_ne_zero).continuous

lemma ccirc_injective : Function.Injective ccirc :=
  (AddCircle.homeomorphCircle (T := 1) one_ne_zero).injective

lemma ccirc_surjective : Function.Surjective ccirc :=
  (AddCircle.homeomorphCircle (T := 1) one_ne_zero).surjective

/-- **The dictionary is the standard parametrisation.**  For a real angle in turns, `ccirc` is
`Circle.exp` of `2π` times the angle, so that `u ↦ γ (ccirc u)` and `t ↦ γ (Circle.exp t)` are the
same closed curve, reparametrised by `u = t / 2π`. -/
lemma ccirc_coe_eq_exp (t : ℝ) :
    ccirc ((t : ℝ) : UnitAddCircle) = Circle.exp (2 * Real.pi * t) := by
  apply Subtype.ext
  rw [ccirc, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk (T := 1), div_one]

/-- **Reparametrisation invariance of a lift total.**  Let `ΨU` be a continuous lift of the doubled
direction of the `UnitAddCircle`-curve `u ↦ γ (ccirc u) - c` and `ΨC` a continuous lift of the
doubled direction of the `Circle`-curve `t ↦ γ (exp t) - c`.  Since the two classes agree at the
parameters `u = t / 2π` (by `ccirc_coe_eq_exp`), the difference `ΨU φ - ΨC (2π φ)` is a continuous
`ℤ`-valued function of `φ` on the connected `ℝ`, hence constant; evaluating at `φ = 1` and `φ = 0`
gives that the two monodromies — the totals — coincide. -/
theorem lift_total_reparam (γ : Circle → ℝ × ℝ) (c : ℝ × ℝ) {ΨU ΨC : ℝ → ℝ}
    (hUc : Continuous ΨU) (hCc : Continuous ΨC)
    (hU : ∀ φ : ℝ, ((ΨU φ : ℝ) : UnitAddCircle)
      = Submission.Collision.dirC (γ (ccirc ((φ : ℝ) : UnitAddCircle)) - c))
    (hC : ∀ t : ℝ, ((ΨC t : ℝ) : UnitAddCircle)
      = Submission.Collision.dirC (γ (Circle.exp t) - c)) :
    ΨU 1 - ΨU 0 = ΨC (2 * Real.pi) - ΨC 0 := by
  -- the two classes agree at the matched parameters
  have hcls : ∀ φ : ℝ,
      ((ΨU φ : ℝ) : UnitAddCircle) = ((ΨC (2 * Real.pi * φ) : ℝ) : UnitAddCircle) := by
    intro φ
    rw [hU φ, ccirc_coe_eq_exp, ← hC (2 * Real.pi * φ)]
  -- hence `ΨU φ - ΨC (2π φ)` is `ℤ`-valued
  have hint : ∀ φ : ℝ, ∃ n : ℤ, ΨU φ - ΨC (2 * Real.pi * φ) = (n : ℝ) := by
    intro φ
    obtain ⟨n, hn⟩ := (coe_eq_coe_iff_int (ΨU φ) (ΨC (2 * Real.pi * φ))).mp (hcls φ)
    exact ⟨n, hn.symm⟩
  have hcont : Continuous fun φ : ℝ => ΨU φ - ΨC (2 * Real.pi * φ) :=
    hUc.sub (hCc.comp (by fun_prop))
  -- a continuous `ℤ`-valued function on the connected `ℝ` is constant
  have hconst := (isLocallyConstant_of_int_valued hcont hint).apply_eq_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (1 : ℝ)) (Set.mem_univ (0 : ℝ))
  rw [show 2 * Real.pi * 1 = 2 * Real.pi by ring, mul_zero] at hconst
  linarith [hconst]

/-- **The total of a lift on the `Circle` side is the winding number of the `UnitAddCircle` side.**

For a continuous `γ : Circle → ℝ × ℝ` and a point `c` off its image, the `Circle`-curve
`t ↦ γ (exp t) - c` has a continuous lift of its doubled direction whose total change over a period is
the winding number of the reparametrised `UnitAddCircle`-curve `u ↦ γ (ccirc u) - c` about the origin.
This is "wiring step 1" of the capping: combined with `winding_values` / `winding_translate` it gives
the lift of the doubled *position* direction with total `±2`. -/
theorem lift_total_eq_winding (γ : Circle → ℝ × ℝ) (hγc : Continuous γ) (c : ℝ × ℝ)
    (h0 : (0 : ℝ × ℝ) ∉ Set.range (fun u : UnitAddCircle => γ (ccirc u) - c))
    {ΨC : ℝ → ℝ} (hCc : Continuous ΨC)
    (hC : ∀ t : ℝ, ((ΨC t : ℝ) : UnitAddCircle)
      = Submission.Collision.dirC (γ (Circle.exp t) - c)) :
    ΨC (2 * Real.pi) - ΨC 0
      = Work.Drive.winding (fun u : UnitAddCircle => γ (ccirc u) - c)
          ((hγc.comp ccirc_continuous).sub continuous_const) h0 := by
  have hηc : Continuous (fun u : UnitAddCircle => γ (ccirc u) - c) :=
    (hγc.comp ccirc_continuous).sub continuous_const
  have hdc : Continuous (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) :=
    continuous_dirCurve _ hηc 0 h0
  -- the canonical lift of the `UnitAddCircle` side
  have hU : ∀ φ : ℝ, ((liftOf (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc φ
        : ℝ) : UnitAddCircle)
      = Submission.Collision.dirC (γ (ccirc ((φ : ℝ) : UnitAddCircle)) - c) := by
    intro φ
    rw [liftOf_lifts]
    show Submission.Collision.dirC ((fun u : UnitAddCircle => γ (ccirc u) - c)
        ((φ : ℝ) : UnitAddCircle) - 0) = _
    simp
  have htot : liftOf (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc 1
        - liftOf (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc 0
      = ΨC (2 * Real.pi) - ΨC 0 :=
    lift_total_reparam γ c (liftOf_continuous _ hdc) hCc hU hC
  have hone : liftOf (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc 1
      = liftOf (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc 0
        + (degree (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc : ℝ) := by
    have h := liftOf_add_one (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc 0
    norm_num at h
    exact h
  have hwind : Work.Drive.winding (fun u : UnitAddCircle => γ (ccirc u) - c) hηc h0
      = degree (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc := rfl
  rw [hwind, ← htot, hone]
  ring

end Work.Drive
