import Mathlib
import Submission.Work.Serre.MapPathDefs

/-!
# The mapping path space deformation retracts onto the image of `mpathOf`

For `p : E → B`, the mapping path space `mpath p` is the space of pairs `(e, γ)` with `γ` a path
in `B` starting at `p e`.  It is homotopy equivalent to `E`, the two maps being the projection
`mpathFst p : mpath p → E`, `(e, γ) ↦ e`, and the section `mpathOf p : E → mpath p`,
`e ↦ (e, const (p e))`.

Here we prove one half of the round trip,

`(mpathOf p).comp (mpathFst p) ~ ContinuousMap.id (mpath p)`,

i.e. that `mpathFst p` is a left inverse of `mpathOf p` up to homotopy.  The homotopy is the
*compression* of the path coordinate: for `x = (e, γ) : mpath p` and `t : I` it sends `x` to
`(e, γ_t)` where `γ_t s = γ (t * s)`.  At `t = 0` this is the constant path `const (p e)` (using
`γ 0 = p e`), i.e. `mpathOf p (mpathFst p x)`, and at `t = 1` it is `γ`, i.e. `x`.

The first coordinate is untouched, so all the topology happens in the path space `C(I, B)`; the
homotopy is built by currying the continuous map `((t, x), s) ↦ (mpathSnd p x) (t * s)`.
-/

open scoped Topology unitInterval
open ContinuousMap

namespace Work.FGThm

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The uncurried compression of the path coordinate of the mapping path space,
`((t, x), s) ↦ (mpathSnd p x) (t * s)`. -/
private def compress (p : C(E, B)) : C((I × Work.Serre.mpath p) × I, B) where
  toFun z := (Work.Serre.mpathSnd p) z.1.2 (z.1.1 * z.2)
  continuous_toFun := by fun_prop

/-- The curried compression, `(t, x) ↦ (s ↦ (mpathSnd p x) (t * s))`, as a continuous map into
the path space. -/
private def compressCurry (p : C(E, B)) : C(I × Work.Serre.mpath p, C(I, B)) :=
  (compress p).curry

/-- At `t = 0` the compressed path is the constant path at `p (mpathFst p x)`. -/
private lemma compressCurry_zero (p : C(E, B)) (x : Work.Serre.mpath p) :
    (compressCurry p) (0, x) =
      ContinuousMap.const I (p ((Work.Serre.mpathFst p) x)) := by
  ext s
  change (Work.Serre.mpathSnd p) x ((0 : I) * s) = p ((Work.Serre.mpathFst p) x)
  rw [zero_mul]
  exact x.2

/-- At `t = 1` the compressed path is the original path. -/
private lemma compressCurry_one (p : C(E, B)) (x : Work.Serre.mpath p) :
    (compressCurry p) (1, x) = (Work.Serre.mpathSnd p) x := by
  ext s
  change (Work.Serre.mpathSnd p) x ((1 : I) * s) = (Work.Serre.mpathSnd p) x s
  rw [one_mul]

/-- The compression homotopy, as a continuous map `I × mpath p → mpath p`. -/
private def homTo (p : C(E, B)) : C(I × Work.Serre.mpath p, Work.Serre.mpath p) where
  toFun y := ⟨((Work.Serre.mpathFst p) y.2, (compressCurry p) y), by
    change (Work.Serre.mpathSnd p) y.2 (y.1 * 0) = p ((Work.Serre.mpathFst p) y.2)
    rw [mul_zero]
    exact y.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Continuous.prodMk ((Work.Serre.mpathFst p).continuous.comp continuous_snd)
      (compressCurry p).continuous

theorem mpathOf_comp_mpathFst_homotopic {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) :
    ContinuousMap.Homotopic ((Work.Serre.mpathOf p).comp (Work.Serre.mpathFst p))
      (ContinuousMap.id (Work.Serre.mpath p)) := by
  refine ⟨{ toContinuousMap := homTo p, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact compressCurry_zero p x
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact compressCurry_one p x

end

end Work.FGThm
