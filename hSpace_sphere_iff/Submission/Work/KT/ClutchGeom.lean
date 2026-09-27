import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FPatch

/-!
# Geometric instantiation of the patching framework (`Work.KT.ClutchGeom`)

`TwoDisk V` is the fibre product of two copies of `C(Ball V, ℂ)` over `C(Sph V, ℂ)` (restriction to
the boundary sphere): the algebra of the space obtained by gluing two copies of the closed unit
ball of `V` along their boundary spheres.  For `finrank ℝ V = d` this space is the sphere `S^d`,
so `TwoDisk V` is the algebra in which the clutching idempotent of `Work.KT.sphere_GL` lives.
-/

namespace Work.KT

noncomputable section

open Matrix

variable (V : Type) [NormedAddCommGroup V]

/-- The inclusion of the unit sphere of `V` into the closed unit ball. -/
def sphToBall : C(Sph V, Ball V) where
  toFun x := ⟨(x : V), mem_closedBall_zero_iff.mpr (le_of_eq (mem_sphere_zero_iff_norm.mp x.2))⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

@[simp] lemma sphToBall_apply (x : Sph V) : ((sphToBall V x : Ball V) : V) = (x : V) := rfl

/-- Restriction of functions on the ball to the boundary sphere. -/
def restRho : C(Ball V, ℂ) →+* C(Sph V, ℂ) := (pullAlg (sphToBall V)).toRingHom

@[simp] lemma restRho_apply (f : C(Ball V, ℂ)) (x : Sph V) :
    restRho V f x = f (sphToBall V x) := rfl

/-- The *double disk* algebra: two disks glued along their boundary spheres. -/
abbrev TwoDisk : Type := FiberProd (restRho V) (restRho V)

end

end Work.KT
