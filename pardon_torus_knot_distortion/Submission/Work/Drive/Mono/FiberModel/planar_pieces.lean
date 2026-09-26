import Mathlib
import Submission.Work.Drive.Mono.FiberModel.planarImage

/-!
# The three plane pieces of the shadow chamber

`wingPlus`, `wingMinus` and `cap0` are the closures of the parts of `interior W` strictly beyond the
two slab faces and strictly above the level.  Each is convex (the closure of a convex set), and
their union is the closure of the planar image (`planar_closure_facts`; the first conjunct of that
statement is proved here as `closure_planarImage_eq_pieces`).
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.FiberModel

noncomputable section

/-- The half-spaces of the plane are convex (for the two coordinate functionals). -/
theorem convex_setOf_fst_gt (a : ℝ) : Convex ℝ {X : ℝ × ℝ | a < X.1} :=
  (convex_Ioi a).linear_preimage (LinearMap.fst ℝ ℝ ℝ)

theorem convex_setOf_fst_lt (a : ℝ) : Convex ℝ {X : ℝ × ℝ | X.1 < a} :=
  (convex_Iio a).linear_preimage (LinearMap.fst ℝ ℝ ℝ)

theorem convex_setOf_snd_gt (a : ℝ) : Convex ℝ {X : ℝ × ℝ | a < X.2} :=
  (convex_Ioi a).linear_preimage (LinearMap.snd ℝ ℝ ℝ)

/-- The shadow `W` is convex: it is the closure of the image of the convex box. -/
theorem convex_boxShadow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    Convex ℝ (boxShadow s c σ v ℓ) := by
  rw [boxShadow, ClBox, shadow]
  exact (Work.Topology.SphereSlicing.convex_PBox s c σ).closure.linear_image
    (levPairCLM v ℓ).toLinearMap

/-- The pieces of the shadow chamber are convex. -/
theorem convex_wingPlus (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (a h : ℝ) : Convex ℝ (wingPlus (boxShadow s c σ v ℓ) a h) :=
  ((convex_boxShadow s c σ v ℓ).interior.inter (convex_setOf_fst_gt (a + h))).closure

theorem convex_wingMinus (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (a h : ℝ) : Convex ℝ (wingMinus (boxShadow s c σ v ℓ) a h) :=
  ((convex_boxShadow s c σ v ℓ).interior.inter (convex_setOf_fst_lt (a - h))).closure

theorem convex_cap0 (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (lam : ℝ) : Convex ℝ (cap0 (boxShadow s c σ v ℓ) lam) :=
  ((convex_boxShadow s c σ v ℓ).interior.inter (convex_setOf_snd_gt lam)).closure

end

end Work.Drive.Mono.FiberModel
