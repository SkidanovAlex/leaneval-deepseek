import Mathlib
import Submission.Work.ORHughesFree.Prop51

namespace Work.ORHughesFree.Prop51

theorem ofGroup_t_pow {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    (k : ℤ) :
    d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ k)) =
      d.laurentEmbed ↑((Work.ORHughesFree.skewLaurentSeriesT ↥DN) ^ k) := by
  -- `RatU.ofGroup t` is a unit of `RatU Γ`, with inverse `RatU.ofGroup t⁻¹`; we promote
  -- `RatU.ofGroup` to a monoid homomorphism `Γ →* (RatU Γ)ˣ` into the unit group, so that
  -- integer powers can be handled by `map_zpow`.
  let F : Γ →* (RatU Γ)ˣ :=
    { toFun := fun u => Units.mk (RatU.ofGroup u) (RatU.ofGroup u⁻¹)
        (by rw [← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one])
        (by rw [← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one])
      map_one' := by ext; simp
      map_mul' := fun u v => by ext; simp [RatU.ofGroup_mul] }
  -- The left hand side is the `k`-th power of the unit `Φ (ofGroup t)`, computed inside `P`.
  have key1 : d.Φ (RatU.ofGroup (d.t ^ k)) =
      ↑((Units.map d.Φ.toMonoidHom (F d.t)) ^ k) := by
    change (d.Φ.toMonoidHom) ↑(F (d.t ^ k)) = _
    rw [← Units.coe_map]
    rw [map_zpow F d.t k]
    rw [map_zpow (Units.map d.Φ.toMonoidHom) (F d.t) k]
  -- The right hand side is the `k`-th power of the image of the unit `t` of `DN((t;τ))`,
  -- and this unit maps to `Φ (ofGroup t)` by `Φ_t`.
  have key2 : d.laurentEmbed ↑((skewLaurentSeriesT ↥DN) ^ k) =
      ↑((Units.map d.Φ.toMonoidHom (F d.t)) ^ k) := by
    have hu : Units.map d.laurentEmbed.toMonoidHom (skewLaurentSeriesT ↥DN) =
        Units.map d.Φ.toMonoidHom (F d.t) := by
      ext
      rw [Units.coe_map, Units.coe_map]
      exact d.Φ_t.symm
    change (d.laurentEmbed.toMonoidHom) (↑((skewLaurentSeriesT ↥DN) ^ k)) = _
    rw [← Units.coe_map]
    rw [map_zpow (Units.map d.laurentEmbed.toMonoidHom) (skewLaurentSeriesT ↥DN) k]
    rw [hu]
  rw [key1, key2]

end Work.ORHughesFree.Prop51
