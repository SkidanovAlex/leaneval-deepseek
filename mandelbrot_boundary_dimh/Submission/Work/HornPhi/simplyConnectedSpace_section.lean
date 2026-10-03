import Mathlib

set_option linter.style.haveILetI false

namespace Work.HornPhi

open Set Metric

/-- If `Φ : ℂ → ℂ` is continuous on `U`, and `Ψ` is a continuous two-sided section of `Φ`
between the ball `ball b ρ` and the piece `S = U ∩ Φ ⁻¹' (ball b ρ)` of `U` lying over it
(`Ψ` maps the ball into `S` with `Φ ∘ Ψ = id` on the ball, and on `S` it is a left inverse of `Φ`),
then `S` is simply connected.  This is the topological half of the statement that an inverse
branch of an injective holomorphic function realises the piece of its domain over a disc as a disc. -/
theorem simplyConnectedSpace_section {Φ : ℂ → ℂ} {U : Set ℂ} {b : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hΦc : ContinuousOn Φ U) (Ψ : ℂ → ℂ)
    (hΨc : ContinuousOn Ψ (Metric.ball b ρ))
    (hΨmem : ∀ u ∈ Metric.ball b ρ, Ψ u ∈ U ∧ Φ (Ψ u) = u)
    (hΨinv : ∀ z ∈ U, Φ z ∈ Metric.ball b ρ → Ψ (Φ z) = z) :
    SimplyConnectedSpace ↥{w : ℂ | w ∈ U ∧ Φ w ∈ Metric.ball b ρ} := by
  -- The piece of `U` over the ball.
  set S : Set ℂ := {w : ℂ | w ∈ U ∧ Φ w ∈ Metric.ball b ρ} with hSdef
  have hSU : S ⊆ U := fun w hw => hw.1
  -- `Ψ u` lies in `S` for `u` in the ball, and `Φ ∘ Ψ = id` there.
  have hmem : ∀ u : ↥(Metric.ball b ρ), Φ (Ψ (u : ℂ)) ∈ Metric.ball b ρ :=
    fun u => by rw [(hΨmem (u : ℂ) u.2).2]; exact u.2
  -- The ball is convex, hence contractible, hence simply connected.
  haveI : ContractibleSpace ↥(Metric.ball b ρ) :=
    (convex_ball b ρ).contractibleSpace ⟨b, mem_ball_self hρ⟩
  haveI : SimplyConnectedSpace ↥(Metric.ball b ρ) := SimplyConnectedSpace.ofContractible _
  -- Continuity of the two maps, as maps of subtypes.
  have hΦS : Continuous fun z : ↥S => Φ (z : ℂ) := (hΦc.mono hSU).domRestrict
  have hΨb : Continuous fun u : ↥(Metric.ball b ρ) => Ψ (u : ℂ) := hΨc.domRestrict
  have hF : Continuous fun z : ↥S => (⟨Φ (z : ℂ), z.2.2⟩ : ↥(Metric.ball b ρ)) :=
    Continuous.subtype_mk hΦS (fun z => z.2.2)
  have hG : Continuous fun u : ↥(Metric.ball b ρ) =>
      (⟨Ψ (u : ℂ), (hΨmem (u : ℂ) u.2).1, hmem u⟩ : ↥S) :=
    Continuous.subtype_mk hΨb (fun u => ⟨(hΨmem (u : ℂ) u.2).1, hmem u⟩)
  -- `Φ` and `Ψ` are mutually inverse between `S` and the ball.
  let e : ↥S ≃ ↥(Metric.ball b ρ) :=
    { toFun := fun z => ⟨Φ (z : ℂ), z.2.2⟩
      invFun := fun u => ⟨Ψ (u : ℂ), (hΨmem (u : ℂ) u.2).1, hmem u⟩
      left_inv := fun z => by
        apply Subtype.ext
        exact hΨinv z.1 z.2.1 z.2.2
      right_inv := fun u => by
        apply Subtype.ext
        exact (hΨmem (u : ℂ) u.2).2 }
  have he : ↥S ≃ₜ ↥(Metric.ball b ρ) := Homeomorph.mk e hF hG
  -- Transport simple connectivity along the homeomorphism.
  exact he.toHomotopyEquiv.simplyConnectedSpace

end Work.HornPhi
