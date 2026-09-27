import Mathlib
import Submission.Work.Drive.position_winding_eq_umlauf_sign
import Submission.Work.Drive.position_angle_lift

/-!
# The doubled position total equals the doubled tangent total

Let `γ : Circle → ℝ × ℝ` be a smooth embedded closed plane curve avoiding the origin, `Ψ` a
continuous lift of the doubled *position* direction `t ↦ dirC (γ (exp t))` (doubled direction:
`dirC v` is the class of `arg v / π` in `ℝ/ℤ`), whose total change over one period is non-zero, and
`(θ, ρ', ε)` the Umlauf data of `γ` (`deriv (γ ∘ exp) t = ρ' t • (cos (θ t), sin (θ t))`,
`θ (t + 2π) - θ t = 2π ε`, `ε = ±1`).

Then the doubled *tangent* direction `t ↦ dirC (deriv (γ ∘ exp) t)` has a continuous lift `Φ` whose
total change over the period is the same as that of `Ψ`:

`Φ (2π) - Φ 0 = Ψ (2π) - Ψ 0`.

Concretely `Φ := θ / π`, and the identity is `2 m = 2 ε` where `m` is the winding number of `γ`
around the origin, read off from any polar lift `(ρ, Θ)` of `γ`:
`Ψ (2π) - Ψ 0 = 2 (Θ (2π) - Θ 0) = 2 m` (`Work.Drive.total_change_of_position_lift`), and `m = ε`
because a smooth Jordan curve through a point of non-zero winding winds around it exactly once, in
the direction of its turning (`Work.Drive.position_winding_eq_umlauf_sign`).  The hypothesis
`Ψ (2π) - Ψ 0 ≠ 0` is exactly what rules out the origin lying outside the curve.

This is the "sign match" input of the capping of the configuration Möbius strip: the two coordinates
of `∂M` are the doubled tangent direction and the doubled position direction, and they have the same
monodromy.
-/

namespace Work.Drive

/-- **The total change of a lift of the doubled position direction is twice that of the position
angle.**  If `(ρ, Θ)` is a polar lift of `γ ∘ exp` with `ρ > 0` and `Θ` continuous, and `Ψ` is a
continuous lift of the doubled direction `dirC (γ (exp t))`, then `Ψ - 2 Θ` is continuous and
`ℤ`-valued (because `dirC (polarLift (r, ψ))` is the class of `2 ψ`), hence constant on the
connected `ℝ`; evaluating the constancy at `2π` and `0` gives the stated identity. -/
lemma total_change_of_position_lift {γ : Circle → ℝ × ℝ} {ρ Θ Ψ : ℝ → ℝ}
    (hρ : ∀ t, 0 < ρ t) (hpol : ∀ t, polarLift (ρ t, Θ t) = γ (Circle.exp t))
    (hΘ : Continuous Θ) (hΨ : Continuous Ψ)
    (hdoubled : ∀ t, ((Ψ t : ℝ) : UnitAddCircle) = Submission.Collision.dirC (γ (Circle.exp t))) :
    Ψ (2 * Real.pi) - Ψ 0 = 2 * (Θ (2 * Real.pi) - Θ 0) := by
  -- `Ψ` and `2 Θ` have the same class in `ℝ/ℤ` at every point
  have hclass : ∀ t, ((Ψ t : ℝ) : UnitAddCircle) = ((2 * Θ t : ℝ) : UnitAddCircle) := by
    intro t
    rw [hdoubled t, ← hpol t]
    exact dirC_polarLift (ne_of_gt (hρ t))
  -- hence `Ψ - 2 Θ` takes values in `ℤ`
  have hint : ∀ t, ∃ n : ℤ, Ψ t - 2 * Θ t = (n : ℝ) := by
    intro t
    have h2 : ((Ψ t - 2 * Θ t : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
      rw [AddCircle.coe_sub, hclass t, sub_self, AddCircle.coe_zero]
    obtain ⟨n, hn⟩ :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ) (x := Ψ t - 2 * Θ t)).mp h2
    exact ⟨n, by rw [zsmul_one] at hn; exact hn.symm⟩
  have hcont : Continuous fun t : ℝ => Ψ t - 2 * Θ t := hΨ.sub (hΘ.const_mul 2)
  -- a continuous `ℤ`-valued function on the connected `ℝ` is constant
  have hconst := (isLocallyConstant_of_int_valued hcont hint).apply_eq_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (2 * Real.pi)) (Set.mem_univ 0)
  linarith [hconst]

theorem doubled_position_total_eq_doubled_tangent_total (hU : Submission.Drive.UmlaufProp)
    (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (h0 : ∀ x : Circle, γ x ≠ 0)
    (Ψ : ℝ → ℝ) (hΨc : Continuous Ψ)
    (hΨ : ∀ t, ((Ψ t : ℝ) : UnitAddCircle) = Submission.Collision.dirC (γ (Circle.exp t)))
    (henclosed : Ψ (2 * Real.pi) - Ψ 0 ≠ 0) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧
      (∀ t, ((Φ t : ℝ) : UnitAddCircle)
        = Submission.Collision.dirC (deriv (fun s : ℝ => γ (Circle.exp s)) t)) ∧
      Φ (2 * Real.pi) - Φ 0 = Ψ (2 * Real.pi) - Ψ 0 := by
  -- the Umlauf data of `γ`
  obtain ⟨θ, ρ', ε, hε, hθc, hρ'pos, hθderiv, hθper⟩ := hU γ hγ
  -- a polar lift of the position vector
  obtain ⟨ρ, Θ, hρc, hΘc, hρpos, hlift, hm⟩ := position_angle_lift γ hγ h0
  obtain ⟨m, hm⟩ := hm
  -- the total change of `Ψ` is twice the winding number `m`
  have hΨtot : Ψ (2 * Real.pi) - Ψ 0 = 2 * (m : ℝ) := by
    rw [total_change_of_position_lift hρpos hlift hΘc hΨc hΨ, hm]
  -- which is therefore non-zero
  have hmne : m ≠ 0 := by
    intro h
    refine henclosed ?_
    rw [hΨtot, h]
    norm_num
  have hp : (0 : ℝ × ℝ) ∉ Set.range γ := by
    rintro ⟨x, hx⟩
    exact h0 x hx
  -- the winding number about the origin is the Umlauf sign
  have hmε : m = ε :=
    position_winding_eq_umlauf_sign γ hγ hp hρc hΘc hρpos
      (fun t => by simpa using hlift t) hm hε hθc hρ'pos hθderiv hθper hmne
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
