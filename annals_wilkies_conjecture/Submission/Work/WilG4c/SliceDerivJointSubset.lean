/-
  WilG4c — joint ⟹ fibre: the *slice* derivative graph is contained in (the projection of) the
  joint derivative graph, and the derivative values agree there.

  If `w = Fin.init z` lies in the **interior** of the joint `C^{|L|}`-locus of the family written
  as a single function `famFunHat f` on `ℝ^{p + (n+1)}`, then the *slice*
  `y ↦ f (parPt w) y` is `C^{|L|}` at the cube point `cubePt w`, and the iterated *joint*
  directional derivative of `famFunHat f` at `w` along the lifted directions
  `L.map (Fin.natAdd p)` equals the iterated *fibre* derivative of the slice along `L`.

  This is the "joint ⟹ fibre" direction of `AlDgListSlice`: the joint locus is contained in the
  fibre locus, and the two derivative values agree there.

  ## Proof

  Let `w := Fin.init z`.  Two ingredients, both already available:

  * `Fin.append_castAdd_natAdd` identifies `w` with `Fin.append (parPt w) (cubePt w)`, so the
    slice `y ↦ f (parPt w) y` is `famFunHat f` precomposed with the affine inclusion
    `y ↦ Fin.append (parPt w) y` (`famFunHat_append`), and the chain rule for `ContDiffAt` under
    that inclusion gives the first conjunct (the inclusion is the continuous linear map
    `lastIncl p n` plus a constant, hence `C^∞`).
  * `iterDir_append_transport` (from `iterDir_famFunHat_xPt`) transports the iterated
    directional derivative across the same inclusion, turning the joint `iterDir` along
    `L.map (Fin.natAdd p)` into the fibre `iterDir` along `L`; `iterDir_eq_iteratedFDeriv`
    converts that into the `iteratedFDeriv` of the slice.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv
import Submission.Work.WilG4c.iterDir_famFunHat_xPt

namespace Work.WilG4c

open Work.WilkG4c

theorem SliceDerivJointSubset {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (z : Fin (p + (n + 1) + 1) → ℝ)
    (hz : Fin.init z ∈ interior {w | ContDiffAt ℝ L.length (Work.WilkG4c.famFunHat f) w}) :
    ContDiffAt ℝ L.length (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt (Fin.init z)) y)
        (Work.WilkG4c.cubePt (Fin.init z)) ∧
      Work.WilkG4c.iterDir (L.map (fun j => Fin.natAdd p j)) (Work.WilkG4c.famFunHat f) (Fin.init z) =
        iteratedFDeriv ℝ L.length
          (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt (Fin.init z)) y)
          (Work.WilkG4c.cubePt (Fin.init z)) (fun j => Pi.single (L.get j) 1) := by
  -- `w = Fin.init z` is a joint-`C^{|L|}` point, and it is `Fin.append (parPt w) (cubePt w)`.
  have hmem : ContDiffAt ℝ L.length (Work.WilkG4c.famFunHat f) (Fin.init z) := interior_subset hz
  have happ : Fin.append (Work.WilkG4c.parPt (Fin.init z)) (Work.WilkG4c.cubePt (Fin.init z))
      = Fin.init z := Fin.append_castAdd_natAdd
  have hjoint : ContDiffAt ℝ L.length (Work.WilkG4c.famFunHat f)
      (Fin.append (Work.WilkG4c.parPt (Fin.init z)) (Work.WilkG4c.cubePt (Fin.init z))) := by
    rw [happ]
    exact hmem
  -- First conjunct: the slice is `famFunHat f` composed with the affine inclusion
  -- `y ↦ Fin.append (parPt w) y`, which is `lastIncl p n` plus a constant, hence smooth.
  have hslice : ContDiffAt ℝ L.length
      (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt (Fin.init z)) y)
      (Work.WilkG4c.cubePt (Fin.init z)) := by
    have hΦ : ContDiffAt ℝ L.length
        (fun y : Fin (n + 1) → ℝ => Fin.append (Work.WilkG4c.parPt (Fin.init z)) y)
        (Work.WilkG4c.cubePt (Fin.init z)) := by
      have hfun : (fun y : Fin (n + 1) → ℝ => Fin.append (Work.WilkG4c.parPt (Fin.init z)) y)
          = fun y => lastIncl p n y
              + Fin.append (Work.WilkG4c.parPt (Fin.init z)) (0 : Fin (n + 1) → ℝ) :=
        funext (fun y => append_eq_lastIncl_add p n (Work.WilkG4c.parPt (Fin.init z)) y)
      rw [hfun]
      exact ((lastIncl p n).contDiff.contDiffAt).add contDiffAt_const
    have hmain := ContDiffAt.comp (Work.WilkG4c.cubePt (Fin.init z)) hjoint hΦ
    simpa only [Function.comp_def, famFunHat_append] using hmain
  refine ⟨hslice, ?_⟩
  -- Second conjunct: transport the iterated directional derivative across the inclusion.
  have htrans : Work.WilkG4c.iterDir (L.map (Fin.natAdd p)) (Work.WilkG4c.famFunHat f) (Fin.init z)
      = Work.WilkG4c.iterDir L (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt (Fin.init z)) y)
          (Work.WilkG4c.cubePt (Fin.init z)) := by
    have h1 := iterDir_append_transport (Work.WilkG4c.famFunHat f)
        (Work.WilkG4c.parPt (Fin.init z)) L (Work.WilkG4c.cubePt (Fin.init z)) hjoint
    have hfun : (fun w' : Fin (n + 1) → ℝ =>
          Work.WilkG4c.famFunHat f (Fin.append (Work.WilkG4c.parPt (Fin.init z)) w'))
        = (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt (Fin.init z)) y) :=
      funext (fun y => famFunHat_append f (Work.WilkG4c.parPt (Fin.init z)) y)
    rw [hfun] at h1
    rw [happ] at h1
    exact h1
  rw [htrans]
  exact iterDir_eq_iteratedFDeriv L
    (fun y : Fin (n + 1) → ℝ => f (Work.WilkG4c.parPt (Fin.init z)) y)
    (Work.WilkG4c.cubePt (Fin.init z)) hslice

end Work.WilG4c
