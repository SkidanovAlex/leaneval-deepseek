import Mathlib
import Submission.Work.Drive.doubledPositionPoint
import Submission.Work.Drive.reparamWinding
import Submission.Work.Drive.translateWinding

/-!
# The periodic cap angle of the configuration strip's diagonal

`Drive/reparamWinding.lean` transports the winding (an `ℝ/ℤ`-parametrised invariant) to a lift of the
doubled *position* direction of a `Circle`-parametrised curve, and
`Drive/doubledPositionPoint.lean` proves the sign match — a lift of the doubled position direction
about a point `p` with non-zero total and a lift of the doubled tangent direction have the same total.
This file assembles them into the cap angle:

* `Work.Drive.monodromy_const_of_int_valued` — the monodromy `t ↦ f (t + 2π) - f t` of a continuous
  lift of a `2π`-periodic class function is integer-valued and continuous, hence *constant*;
* `Work.Drive.exists_cap_angle_data` — a point `c` off the curve, a continuous lift `Ψ` of the doubled
  position direction about `c`, a continuous lift `Φ` of the doubled tangent direction, with *matching
  monodromy*: `Φ (t + 2π) - Φ t = Ψ (t + 2π) - Ψ t` for all `t`;
* `Work.Drive.exists_periodic_cap_angle_of_smooth` — the cap angle `Θc = Φ - Ψ`: continuous,
  `2π`-periodic, of class `Φ - Ψ` in `ℝ/ℤ`.

Nothing about the *value* of the monodromy is needed: the cap angle is `Φ - 2Θ` with `Θ = Ψ/2` the
position angle of the midpoint, and `2Θ = Ψ` only depends on `Ψ`, so the half-integer ambiguity in
"half of the doubled position angle" is harmless.  (The classical sharpening — that the common
monodromy is `±2`, i.e. `ε = ±1` — needs `Work.Drive.winding_values` and is recorded separately once
that chapter's import closure is available again.) -/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

open Submission.Collision (dirC)

/-- **The monodromy of a lift of a periodic class function is constant.**

Let `f : ℝ → ℝ` be continuous and suppose that over every period its value changes by an *integer*
(for instance because `f` is a lift of a `2π`-periodic function into `ℝ/ℤ`).  Then
`t ↦ f (t + 2π) - f t` is a continuous `ℤ`-valued function on the connected `ℝ`, hence constant. -/
lemma monodromy_const_of_int_valued {f : ℝ → ℝ} (hf : Continuous f)
    (hint : ∀ t : ℝ, ∃ k : ℤ, f (t + 2 * Real.pi) - f t = (k : ℝ)) :
    ∀ t : ℝ, f (t + 2 * Real.pi) - f t = f (2 * Real.pi) - f 0 := by
  have hcont : Continuous fun t : ℝ => f (t + 2 * Real.pi) - f t :=
    (hf.comp (continuous_id.add continuous_const)).sub hf
  have hlc : IsLocallyConstant fun t : ℝ => f (t + 2 * Real.pi) - f t :=
    isLocallyConstant_of_int_valued hcont hint
  intro t
  simpa using hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ t) (Set.mem_univ 0)

/-- **The cap-angle data of a smooth embedding.**

There are a point `c` off the curve, a continuous lift `Ψ` of the doubled *position* direction
`t ↦ dirC (γ (exp t) - c)`, and a continuous lift `Φ` of the doubled *tangent* direction
`t ↦ dirC ((γ ∘ exp)' t)`, whose monodromies are both constant and *equal*:

`Ψ (t + 2π) - Ψ t = Ψ (2π) - Ψ 0 = Φ (2π) - Φ 0 = Φ (t + 2π) - Φ t` for every `t`.

* `Ψ` exists with non-zero total by the winding chapter:
  `Work.Drive.exists_translate_origin_winding_ne_zero` (input A: a point off the curve about which the
  winding is non-zero) followed by `Work.Drive.exists_lift_doubled_dir`;
* `Φ` with the *same* total comes from the sign match about a general point,
  `Work.Drive.doubled_position_total_eq_doubled_tangent_total_of_point`;
* the monodromies are constant, not merely the total over `[0, 2π]`, by
  `Work.Drive.monodromy_const_of_int_valued`: the two class functions are `2π`-periodic
  (`Circle.exp_add_two_pi`, `Work.Drive.deriv_curve_periodic`), so the monodromies are integer-valued
  and continuous. -/
theorem exists_cap_angle_data (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ (c : ℝ × ℝ) (Ψ Φ : ℝ → ℝ), c ∉ Set.range γ ∧ Continuous Ψ ∧ Continuous Φ ∧
      (∀ t : ℝ, ((Ψ t : ℝ) : UnitAddCircle) = dirC (γ (Circle.exp t) - c)) ∧
      (∀ t : ℝ, ((Φ t : ℝ) : UnitAddCircle) = dirC (deriv (Work.Drive.curve γ) t)) ∧
      (∀ t : ℝ, Ψ (t + 2 * Real.pi) - Ψ t = Ψ (2 * Real.pi) - Ψ 0) ∧
      (∀ t : ℝ, Φ (t + 2 * Real.pi) - Φ t = Φ (2 * Real.pi) - Φ 0) ∧
      Φ (2 * Real.pi) - Φ 0 = Ψ (2 * Real.pi) - Ψ 0 ∧ Ψ (2 * Real.pi) - Ψ 0 ≠ 0 := by
  have hγc : Continuous γ := hγ.isEmbedding.continuous
  have hγinj : Function.Injective γ := hγ.isEmbedding.injective
  -- the `ℝ/ℤ`-reparametrisation of `γ`
  have hηc : Continuous (fun u : UnitAddCircle => γ (ccirc u)) := hγc.comp ccirc_continuous
  have hηinj : Function.Injective (fun u : UnitAddCircle => γ (ccirc u)) :=
    fun u v huv => ccirc_injective (hγinj huv)
  have hηsm : ContDiff ℝ 1 (fun t : ℝ => γ (ccirc (t : UnitAddCircle))) := by
    have hbase : ContDiff ℝ 1 (fun t : ℝ => γ (Circle.exp t)) :=
      (hγ.contMDiff.comp contMDiff_circleExp).contDiff.of_le (by simp)
    have hcomp : ContDiff ℝ 1 (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))) :=
      hbase.comp (by fun_prop)
    have hfun : (fun t : ℝ => γ (ccirc (t : UnitAddCircle)))
        = fun t : ℝ => γ (Circle.exp (2 * Real.pi * t)) := by
      funext t
      rw [ccirc_coe_eq_exp t]
    rw [hfun]
    exact hcomp
  -- input A: a point `c` off the curve about which the winding is non-zero
  obtain ⟨c, h0, hne⟩ :=
    exists_translate_origin_winding_ne_zero (fun u : UnitAddCircle => γ (ccirc u)) hηc hηinj hηsm
  -- `c` is off the curve, so the position direction about it is defined on the whole curve
  have hcsurj : Function.Surjective ccirc := ccirc_surjective
  have hpc : c ∉ Set.range γ := by
    rintro ⟨x, hx⟩
    obtain ⟨u, rfl⟩ := hcsurj x
    exact h0 ⟨u, by simp [hx]⟩
  -- the lift of the doubled position direction about `c`, with non-zero total
  obtain ⟨Ψ, hΨc, hΨ, hΨtot⟩ := exists_lift_doubled_dir γ hγc c (by simpa using h0)
  have hΨne : Ψ (2 * Real.pi) - Ψ 0 ≠ 0 := by
    rw [hΨtot]
    exact fun h => hne (Int.cast_eq_zero.mp h)
  -- the sign match: the doubled tangent direction has the same total
  obtain ⟨Φ, hΦc, hΦ, hΦtot⟩ :=
    doubled_position_total_eq_doubled_tangent_total_of_point umlauf γ hγ hpc Ψ hΨc hΨ hΨne
  -- the two monodromies are constant
  have hΨint : ∀ t : ℝ, ∃ k : ℤ, Ψ (t + 2 * Real.pi) - Ψ t = (k : ℝ) := by
    intro t
    have hcls : ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle) = ((Ψ t : ℝ) : UnitAddCircle) := by
      rw [hΨ (t + 2 * Real.pi), hΨ t, Circle.exp_add_two_pi]
    obtain ⟨k, hk⟩ := (coe_eq_coe_iff_int (Ψ (t + 2 * Real.pi)) (Ψ t)).mp hcls
    exact ⟨k, hk.symm⟩
  have hΦint : ∀ t : ℝ, ∃ k : ℤ, Φ (t + 2 * Real.pi) - Φ t = (k : ℝ) := by
    intro t
    have hper : deriv (fun s : ℝ => γ (Circle.exp s)) (t + 2 * Real.pi)
        = deriv (fun s : ℝ => γ (Circle.exp s)) t :=
      deriv_curve_periodic γ hγ t
    have hcls : ((Φ (t + 2 * Real.pi) : ℝ) : UnitAddCircle) = ((Φ t : ℝ) : UnitAddCircle) := by
      rw [hΦ (t + 2 * Real.pi), hΦ t, hper]
    obtain ⟨k, hk⟩ := (coe_eq_coe_iff_int (Φ (t + 2 * Real.pi)) (Φ t)).mp hcls
    exact ⟨k, hk.symm⟩
  exact ⟨c, Ψ, Φ, hpc, hΨc, hΦc, hΨ, hΦ,
    monodromy_const_of_int_valued hΨc hΨint, monodromy_const_of_int_valued hΦc hΦint, hΦtot, hΨne⟩

/-- **The periodic cap angle of the configuration strip's diagonal.**

For a smooth embedded plane curve there are a point `c` off it, a lift `Ψ` of the doubled *position*
direction about `c`, a lift `Φ` of the doubled *tangent* direction whose monodromy matches that of
`Ψ`, and a continuous `2π`-periodic function `Θc` — the cap angle — of class `Φ - Ψ`:
`(Θc t) = (Φ t) - (Ψ t)` in `ℝ/ℤ`.

Geometrically `Θc = Φ - 2Θ` where `Θ = Ψ/2` is the position angle of the midpoint (the doubled
position direction is `2Θ`), and `∂M` being a meridian of the cap solid torus is exactly the
statement that this is a function of the parameter on the circle — the input which
`Work.Drive.exists_cap_disk_gluing_strip` fills by a disk. -/
theorem exists_periodic_cap_angle_of_smooth (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ (c : ℝ × ℝ) (Ψ Φ Θc : ℝ → ℝ), Continuous Ψ ∧ Continuous Φ ∧ Continuous Θc ∧
      (∀ t : ℝ, ((Ψ t : ℝ) : UnitAddCircle) = dirC (γ (Circle.exp t) - c)) ∧
      (∀ t : ℝ, ((Φ t : ℝ) : UnitAddCircle) = dirC (deriv (Work.Drive.curve γ) t)) ∧
      (∀ t : ℝ, Θc (t + 2 * Real.pi) = Θc t) ∧
      (∀ t : ℝ, ((Θc t : ℝ) : UnitAddCircle)
        = (Φ t : UnitAddCircle) - (Ψ t : UnitAddCircle)) := by
  obtain ⟨c, Ψ, Φ, -, hΨc, hΦc, hΨ, hΦ, hΨmono, hΦmono, hmatch⟩ := exists_cap_angle_data γ hγ
  refine ⟨c, Ψ, Φ, fun t => Φ t - Ψ t, hΨc, hΦc, hΦc.sub hΨc, hΨ, hΦ, ?_, ?_⟩
  · intro t
    have h1 := hΦmono t
    have h2 := hΨmono t
    show Φ (t + 2 * Real.pi) - Ψ (t + 2 * Real.pi) = Φ t - Ψ t
    linarith
  · intro t
    show ((Φ t - Ψ t : ℝ) : UnitAddCircle) = (Φ t : UnitAddCircle) - (Ψ t : UnitAddCircle)
    rw [AddCircle.coe_sub]

/-- **The cap angle in polar form.**  The cap angle `Θc = Φ - 2Θ` with `Θ` the *position angle* of
the midpoint (the polar lift about the point `c`), `Φ` the doubled tangent direction and `Ψ` the
doubled position direction:

there are continuous `ρ > 0`, `Θ`, `Ψ`, `Φ`, `Θc` and a point `c` off the curve such that
`polarLift (ρ t, Θ t) = γ (exp t) - c`, `Ψ` and `Φ` are lifts of the doubled position and tangent
directions, `Θ` is periodic in the *class* sense, and `Θc` is `2π`-periodic of class
`(Φ t) - 2 • (Θ t)`.

This is the form the disk-gluing input `Work.Drive.exists_cap_disk_gluing_strip` consumes (there with
the cap angle and the position angle, both periodic in the class sense). -/
theorem exists_periodic_cap_angle_polar (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ (c : ℝ × ℝ) (ρ Θ Ψ Φ Θc : ℝ → ℝ),
      Continuous ρ ∧ Continuous Θ ∧ Continuous Ψ ∧ Continuous Φ ∧ Continuous Θc ∧
      (∀ t : ℝ, 0 < ρ t) ∧ (∀ t : ℝ, Work.Drive.polarLift (ρ t, Θ t) = γ (Circle.exp t) - c) ∧
      (∀ t : ℝ, ((Ψ t : ℝ) : UnitAddCircle) = dirC (γ (Circle.exp t) - c)) ∧
      (∀ t : ℝ, ((Φ t : ℝ) : UnitAddCircle) = dirC (deriv (Work.Drive.curve γ) t)) ∧
      (∀ t : ℝ, ((Θ (t + 2 * Real.pi) : ℝ) : UnitAddCircle) = ((Θ t : ℝ) : UnitAddCircle)) ∧
      (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Θ (2 * Real.pi) - Θ 0 = (ε : ℝ) ∧
        Ψ (2 * Real.pi) - Ψ 0 = 2 * (ε : ℝ) ∧ Φ (2 * Real.pi) - Φ 0 = 2 * (ε : ℝ)) ∧
      (∀ t : ℝ, Θc (t + 2 * Real.pi) = Θc t) ∧
      (∀ t : ℝ, ((Θc t : ℝ) : UnitAddCircle)
        = (Φ t : UnitAddCircle) - 2 • (Θ t : UnitAddCircle)) := by
  obtain ⟨c, Ψ, Φ, hpc, hΨc, hΦc, hΨ, hΦ, hΨmono, hΦmono, hmatch, hΨne⟩ :=
    exists_cap_angle_data γ hγ
  -- the polar lift of the position vector about `c`
  obtain ⟨ρ, Θ, hρc, hΘc, hρpos, hlift, hm⟩ :=
    position_angle_lift_sub γ hγ.isEmbedding.continuous (fun x hx => hpc ⟨x, hx⟩)
  obtain ⟨m, hm⟩ := hm
  -- `Ψ - 2Θ` is a continuous `ℤ`-valued function, hence constant
  have hcls : ∀ t : ℝ, ((Ψ t : ℝ) : UnitAddCircle) = ((2 * Θ t : ℝ) : UnitAddCircle) := by
    intro t
    have h2 : ((2 * Θ t : ℝ) : UnitAddCircle) = 2 • ((Θ t : ℝ) : UnitAddCircle) := by
      rw [show (2 * Θ t : ℝ) = 2 • Θ t by rw [two_nsmul]; ring]
      rw [AddCircle.coe_nsmul]
    rw [hΨ t, ← hlift t, dirC_polarLift (ne_of_gt (hρpos t)), h2]
  have hint : ∀ t : ℝ, ∃ k : ℤ, Ψ t - 2 * Θ t = (k : ℝ) := by
    intro t
    obtain ⟨k, hk⟩ := (coe_eq_coe_iff_int (Ψ t) (2 * Θ t)).mp (hcls t)
    exact ⟨k, hk.symm⟩
  have hconst : ∀ t : ℝ, Ψ t - 2 * Θ t = Ψ 0 - 2 * Θ 0 := by
    have hcont : Continuous fun t : ℝ => Ψ t - 2 * Θ t := hΨc.sub (hΘc.const_mul 2)
    have hlc := isLocallyConstant_of_int_valued hcont hint
    intro t
    exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ t) (Set.mem_univ 0)
  have hrel : ∀ t : ℝ, Ψ (t + 2 * Real.pi) - Ψ t = 2 * (Θ (t + 2 * Real.pi) - Θ t) := by
    intro t
    have h1 := hconst (t + 2 * Real.pi)
    have h2 := hconst t
    linarith
  -- the monodromy of `Θ` is the integer `m`: the position angle winds `m` times
  have hΘdiff : ∀ t : ℝ, Θ (t + 2 * Real.pi) - Θ t = (m : ℝ) := by
    intro t
    have h1 := hrel t
    have h2 := hΨmono t
    have h3 : Ψ (2 * Real.pi) - Ψ 0 = 2 * (Θ (2 * Real.pi) - Θ 0) := by
      simpa using hrel 0
    linarith
  have hΘclass : ∀ t : ℝ, ((Θ (t + 2 * Real.pi) : ℝ) : UnitAddCircle)
      = ((Θ t : ℝ) : UnitAddCircle) := by
    intro t
    exact (coe_eq_coe_iff_int (Θ (t + 2 * Real.pi)) (Θ t)).mpr ⟨m, (hΘdiff t).symm⟩
  -- the common monodromy is `±2`: the position angle winds exactly once, in the direction of the
  -- turning of the curve (the sign coherent with the Umlauf sign)
  have hmne : m ≠ 0 := by
    intro hm0
    refine hΨne ?_
    have h : Ψ (2 * Real.pi) - Ψ 0 = 2 * (m : ℝ) := by
      have h1 : Ψ (2 * Real.pi) - Ψ 0 = 2 * (Θ (2 * Real.pi) - Θ 0) := by simpa using hrel 0
      rw [h1, hm]
    rw [h, hm0]; norm_num
  obtain ⟨θ, ρ', ε, hε, hθc, hρ'pos, hθderiv, hθper⟩ := umlauf γ hγ
  have hmε : m = ε :=
    position_winding_eq_umlauf_sign γ hγ hpc hρc hΘc hρpos hlift hm hε hθc hρ'pos hθderiv hθper hmne
  have hΘtot : Θ (2 * Real.pi) - Θ 0 = (ε : ℝ) := by rw [hm, hmε]
  have hΨtot : Ψ (2 * Real.pi) - Ψ 0 = 2 * (ε : ℝ) := by
    have h1 : Ψ (2 * Real.pi) - Ψ 0 = 2 * (Θ (2 * Real.pi) - Θ 0) := by simpa using hrel 0
    rw [h1, hΘtot]
  have hΦtot : Φ (2 * Real.pi) - Φ 0 = 2 * (ε : ℝ) := by rw [hmatch, hΨtot]
  refine ⟨c, ρ, Θ, Ψ, Φ, fun t => Φ t - 2 * Θ t, hρc, hΘc, hΨc, hΦc,
    hΦc.sub (hΘc.const_mul 2), hρpos, hlift, hΨ, hΦ, hΘclass,
    ⟨ε, hε, hΘtot, hΨtot, hΦtot⟩, ?_, ?_⟩
  · intro t
    have h1 := hΦmono t
    have h2 := hΨmono t
    have h3 := hrel t
    have h4 := hmatch
    show Φ (t + 2 * Real.pi) - 2 * Θ (t + 2 * Real.pi) = Φ t - 2 * Θ t
    linarith
  · intro t
    show ((Φ t - 2 * Θ t : ℝ) : UnitAddCircle) = (Φ t : UnitAddCircle) - 2 • (Θ t : UnitAddCircle)
    rw [show (Φ t - 2 * Θ t : ℝ) = Φ t - 2 • Θ t by rw [nsmul_eq_mul]; norm_num]
    rw [AddCircle.coe_sub, AddCircle.coe_nsmul]

end Work.Drive
