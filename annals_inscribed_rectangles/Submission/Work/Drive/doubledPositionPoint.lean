import Mathlib
import Submission.Work.Drive.doubled_position_total_eq_doubled_tangent_total
import Submission.Work.Drive.positionAngleCont
import Submission.Work.Drive.reparamWinding

/-!
# The cap angle of the configuration strip's diagonal, and the sign match about a point

This file closes the wiring of the capping's cap angle (`OMEGA_CHAIN_STATUS.md`, steps 1–3 of
"remaining wiring") for a smooth embedded plane curve, without needing the translate of a smooth
embedding to again be a smooth embedding (`BRIDGE_CIRCLE_UNITADD.md`, item (B2)): every lemma used
below is stated about a *general* point of the plane, or only asks for continuity.

* `Work.Drive.exists_lift_doubled_dir` — the lift of the doubled *position* direction of `γ` about a
  point `c` off `γ`, with total change equal to the (doubled) winding number of `γ` about `c`.  This
  is the output of wiring step 1: the winding API (`Work.Drive.winding`, on `ℝ/ℤ`-parametrised
  curves) transported to the `Circle`-parametrised lift through the dictionary `Work.Drive.ccirc`
  (`Work.Drive.reparamWinding`).
* `Work.Drive.doubled_position_total_eq_doubled_tangent_total_of_point` — the sign match about a
  general point `p`: a lift of the doubled *position* direction `dirC (γ (exp t) - p)` with non-zero
  total and a lift of the doubled *tangent* direction have the *same* total.  This is the
  point-general form of `Work.Drive.doubled_position_total_eq_doubled_tangent_total`, obtained by
  replacing the origin-based polar lift `Work.Drive.position_angle_lift` (which needs the translate
  `γ - p` to be a smooth embedding) by its continuity-only form
  `Work.Drive.position_angle_lift_sub` (`Drive/positionAngleCont.lean`).
* (in `Drive/capAngleOfSmooth.lean`, which additionally needs the winding chapter)
  `Work.Drive.exists_cap_angle_data` — for a smooth embedding `γ` there are `c`, a lift `Ψ` of the
  doubled position direction about `c`, a lift `Φ` of the doubled tangent direction, and `ε = ±1`,
  with `Ψ (2π) - Ψ 0 = Φ (2π) - Φ 0 = 2ε`.
* `Work.Drive.exists_periodic_cap_angle_of_smooth` — the resulting periodic cap angle
  `Θc = Φ - 2·(Ψ/2) = Φ - Ψ`: continuous, `2π`-periodic, with `(Θc t) = (Φ t) - (Ψ t)` in `ℝ/ℤ`.
  (`Θ := Ψ/2` is the position angle of the midpoint up to the harmless ambiguity of sign: the cap
  angle only sees `2Θ`, which is insensitive to it.)  This is the input
  `Work.Drive.exists_cap_disk_gluing_strip` fills by a disk, i.e. `∂M` is a meridian of the cap
  solid torus.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

open Submission.Collision (dirC)

/-- **The lift of the doubled position direction about a point, with its total.**

For a continuous `γ : Circle → ℝ × ℝ` and `c : ℝ × ℝ` with `c ∉ range γ` (the hypothesis is expressed
in the `ℝ/ℤ`-parametrisation, where the winding API lives), there is a continuous lift `Ψ` of the
doubled direction of the position vector `t ↦ γ (exp t) - c`, whose total change over one period is
the winding number of `γ` about `c` (a multiple of `2` for a Jordan curve, by
`Work.Drive.winding_values`). -/
theorem exists_lift_doubled_dir (γ : Circle → ℝ × ℝ) (hγc : Continuous γ) (c : ℝ × ℝ)
    (h0 : (0 : ℝ × ℝ) ∉ Set.range (fun u : UnitAddCircle => γ (ccirc u) - c)) :
    ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧
      (∀ t : ℝ, ((Ψ t : ℝ) : UnitAddCircle) = dirC (γ (Circle.exp t) - c)) ∧
      Ψ (2 * Real.pi) - Ψ 0
        = (Work.Drive.winding (fun u : UnitAddCircle => γ (ccirc u) - c)
            ((hγc.comp ccirc_continuous).sub continuous_const) h0 : ℝ) := by
  have hηc : Continuous (fun u : UnitAddCircle => γ (ccirc u) - c) :=
    (hγc.comp ccirc_continuous).sub continuous_const
  have hdc : Continuous (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) :=
    continuous_dirCurve _ hηc 0 h0
  refine ⟨fun t : ℝ => liftOf (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc
      (t / (2 * Real.pi)), ?_, ?_, ?_⟩
  · exact (liftOf_continuous _ hdc).comp (continuous_id.div_const _)
  · intro t
    rw [liftOf_lifts]
    show dirC ((γ (ccirc ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)) - c) - 0)
      = dirC (γ (Circle.exp t) - c)
    have harg : 2 * Real.pi * (t / (2 * Real.pi)) = t := by
      field_simp
    rw [ccirc_coe_eq_exp, harg]
    simp
  · show liftOf (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc
        (2 * Real.pi / (2 * Real.pi)) - liftOf (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c)
        hηc 0 h0) hdc (0 / (2 * Real.pi))
      = (Work.Drive.winding (fun u : UnitAddCircle => γ (ccirc u) - c) hηc h0 : ℝ)
    rw [div_self (by positivity : (2 : ℝ) * Real.pi ≠ 0), zero_div]
    have hone := liftOf_add_one (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc 0
    norm_num at hone
    have hwind : Work.Drive.winding (fun u : UnitAddCircle => γ (ccirc u) - c) hηc h0
        = degree (dirCurve (fun u : UnitAddCircle => γ (ccirc u) - c) hηc 0 h0) hdc := rfl
    rw [hwind, hone]
    ring

/-- **The sign match about a general point.**

Let `γ` be a smooth embedded closed plane curve, `p` a point off it, `Ψ` a continuous lift of the
doubled direction of the position vector `t ↦ γ (exp t) - p` whose total change over a period is
non-zero.  Then the doubled *tangent* direction has a continuous lift `Φ` with the *same* total: the
orientation fact that the winding of the curve about an enclosed point equals its Umlauf sign.

This is `Work.Drive.doubled_position_total_eq_doubled_tangent_total` with the origin replaced by the
general point `p`; the polar lift about `p` is supplied by
`Work.Drive.position_angle_lift_sub`, which asks only for continuity — so no translation of the
smooth embedding is needed. -/
theorem doubled_position_total_eq_doubled_tangent_total_of_point
    (hU : Submission.Drive.UmlaufProp) (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {p : ℝ × ℝ} (hp : p ∉ Set.range γ)
    (Ψ : ℝ → ℝ) (hΨc : Continuous Ψ)
    (hΨ : ∀ t : ℝ, ((Ψ t : ℝ) : UnitAddCircle) = dirC (γ (Circle.exp t) - p))
    (henclosed : Ψ (2 * Real.pi) - Ψ 0 ≠ 0) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧
      (∀ t : ℝ, ((Φ t : ℝ) : UnitAddCircle)
        = dirC (deriv (fun s : ℝ => γ (Circle.exp s)) t)) ∧
      Φ (2 * Real.pi) - Φ 0 = Ψ (2 * Real.pi) - Ψ 0 := by
  obtain ⟨θ, ρ', ε, hε, hθc, hρ'pos, hθderiv, hθper⟩ := hU γ hγ
  obtain ⟨ρ, Θ, hρc, hΘc, hρpos, hlift, hm⟩ :=
    position_angle_lift_sub γ hγ.isEmbedding.continuous (fun x hx => hp ⟨x, hx⟩)
  obtain ⟨m, hm⟩ := hm
  have hΨtot : Ψ (2 * Real.pi) - Ψ 0 = 2 * (m : ℝ) := by
    rw [total_change_of_position_lift (γ := fun x : Circle => γ x - p) hρpos hlift hΘc hΨc hΨ, hm]
  have hmne : m ≠ 0 := by
    intro h
    refine henclosed ?_
    rw [hΨtot, h]
    norm_num
  have hmε : m = ε :=
    position_winding_eq_umlauf_sign γ hγ hp hρc hΘc hρpos hlift hm hε hθc hρ'pos hθderiv hθper hmne
  refine ⟨fun t => θ t / Real.pi, hθc.div_const _, ?_, ?_⟩
  · intro t
    rw [hθderiv t, Submission.Configuration.dirC_smul_pos (hρ'pos t)]
    exact (dirC_cos_sin (θ t)).symm
  · show θ (2 * Real.pi) / Real.pi - θ 0 / Real.pi = Ψ (2 * Real.pi) - Ψ 0
    have h2 : θ (2 * Real.pi) - θ 0 = 2 * Real.pi * (ε : ℝ) := by
      simpa using hθper 0
    have hΦ : θ (2 * Real.pi) / Real.pi - θ 0 / Real.pi = 2 * (ε : ℝ) := by
      rw [div_sub_div_same, h2]
      field_simp
    rw [hmε] at hΨtot
    linarith

end Work.Drive
