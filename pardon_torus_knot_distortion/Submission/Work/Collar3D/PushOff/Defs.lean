import Submission.Work.Collar3D.Model.Defs

/-!
# The push-off ("cap") of a disc along its collar

Let `e : 𝔻 → ℝ³` be an embedded disc with a collar `c : DiscCollar e`, i.e. a homeomorphism
`Φ : U ≃ₜ ℂ × ℝ` of a neighbourhood of the disc to the model, carrying `e` to the parametrisation
`z ↦ (z, 0)` of the plane.  For any *profile* `ψ : 𝔻 → ℝ` the **cap**

`Work.Collar3D.DiscCollar.cap c ψ : 𝔻 → ℝ³`,   `z ↦ Φ.symm (z, ψ z)`

is a disc of the collar which agrees with `e` exactly where `ψ` vanishes on the boundary circle
and lies on the side of the disc prescribed by the sign of `ψ`.  This is the push-off of Pardon's
cut-and-paste ("push the disc off the surface along a collar"), and the three properties that the
argument consumes are

* `Work.Collar3D.DiscCollar.cap_injective` — the cap is embedded;
* `Work.Collar3D.DiscCollar.cap_boundary` — it has the same boundary curve as `e` when `ψ = 0` on
  `∂𝔻`;
* `Work.Collar3D.DiscCollar.cap_notMem_range` — if `ψ` does not vanish in the interior then the cap
  is disjoint from the disc.

The *profile* is produced by `Work.Collar3D.exists_bump`: a continuous function vanishing outside
an interval and equal to a prescribed value on a smaller interval inside it.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

/-- The model disc in the plane, seen in the collar `ℂ × ℝ` as the middle sheet. -/
def discChartFun (p : (Set.univ : Set R3)) : ℂ × ℝ := (p.1 0 + p.1 1 * Complex.I, p.1 2)

@[simp] theorem discChartFun_fst (p : (Set.univ : Set R3)) :
    (discChartFun p).1 = p.1 0 + p.1 1 * Complex.I := rfl

@[simp] theorem discChartFun_snd (p : (Set.univ : Set R3)) : (discChartFun p).2 = p.1 2 := rfl

namespace DiscCollar

variable {e : C(Disc, R3)} (c : DiscCollar e)

/-- **The cap of a disc along its collar, with profile `ψ`**: the disc
`z ↦ Φ.symm (z, ψ z)`. -/
def cap (ψ : Disc → ℝ) (z : Disc) : R3 := (c.Φ.symm (((z : ℂ)), ψ z) : R3)

theorem cap_apply (ψ : Disc → ℝ) (z : Disc) :
    c.cap ψ z = (c.Φ.symm (((z : ℂ)), ψ z) : R3) := rfl

theorem cap_mem_U (ψ : Disc → ℝ) (z : Disc) : c.cap ψ z ∈ c.U := (c.Φ.symm _).2

/-- The chart of the cap: `Φ (cap z) = (z, ψ z)`. -/
theorem Φ_cap (ψ : Disc → ℝ) (z : Disc) :
    c.Φ ⟨c.cap ψ z, c.cap_mem_U ψ z⟩ = (((z : ℂ)), ψ z) :=
  Homeomorph.apply_symm_apply _ _

end DiscCollar

end

end Work.Collar3D
