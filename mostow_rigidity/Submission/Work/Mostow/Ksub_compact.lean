import Mathlib
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.isCompact_matBallToPO

/-!
# Compactness of the stabiliser of the origin in `PO n 1`

`Work.Mostow.Ksub n hA` is the stabiliser of the origin `0 : E n` in `PO n 1`
(`Work.Mostow.HaarBase`); geometrically it is the compact group `O(n)`.

The proof has two halves, neither of which uses the structure theory of `Ksub`:

* `Ksub` is *closed*: it is the preimage of the singleton `{0}` under the orbit map
  `g ↦ g • 0`, which is continuous by `POActionProp` (the action map
  `PO n 1 × E n → E n` is continuous).
* `Ksub` is contained in the *compact* set `matBallToPO n 1`: an element fixing the origin
  moves it by distance `0 ≤ 0`, so `nearStab_orbitBall_subset` (from
  `Submission.Work.Mostow.finite_nearStab`) puts it in `matBallToPO n (cosh (max 0 0))`,
  and `matBallToPO n C` is compact by `isCompact_matBallToPO`.

A closed subset of a compact set is compact, which is `IsCompact.of_isClosed_subset`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- The orbit map `g ↦ g • 0` of `PO n 1` is continuous, by the continuity of the action
contained in `POActionProp`. -/
theorem continuous_smul_zero {n : ℕ} (hA : POActionProp n) :
    Continuous (fun g : PO n 1 => g • (0 : E n)) :=
  (hA.2.2.2.2.2.2.1).comp (continuous_id.prodMk continuous_const)

/-- `Ksub` is closed: it is the preimage of the point `0` under the continuous orbit map. -/
theorem isClosed_Ksub {n : ℕ} (hA : POActionProp n) :
    IsClosed ((Ksub n hA : Subgroup (PO n 1)) : Set (PO n 1)) := by
  have h1 : IsClosed (Set.preimage (fun g : PO n 1 => g • (0 : E n)) ({0} : Set (E n))) :=
    isClosed_singleton.preimage (continuous_smul_zero hA)
  have h2 : Set.preimage (fun g : PO n 1 => g • (0 : E n)) ({0} : Set (E n))
      = ((Ksub n hA : Subgroup (PO n 1)) : Set (PO n 1)) := by
    ext g
    simp [Ksub]
  rwa [h2] at h1

/-- `Ksub` is contained in the compact set `matBallToPO n 1`: its elements do not move the
origin at all. -/
theorem Ksub_subset_matBallToPO {n : ℕ} (hA : POActionProp n) :
    ((Ksub n hA : Subgroup (PO n 1)) : Set (PO n 1)) ⊆ matBallToPO n 1 := by
  intro g hg
  have h1 : hdist (0 : E n) (g • (0 : E n)) ≤ (0 : ℝ) := by
    have hfix : g • (0 : E n) = 0 := hg
    rw [hfix]
    simp [hdist, tpart, Real.arcosh_zero]
  have h2 := nearStab_orbitBall_subset (n := n) (0 : ℝ) h1
  simpa using h2

theorem Ksub_compact (n : ℕ) (hA : Submission.Mostow.POActionProp n) :
    IsCompact (Work.Mostow.Ksub n hA : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) :=
  (isCompact_matBallToPO (n := n) 1).of_isClosed_subset (isClosed_Ksub hA)
    (Ksub_subset_matBallToPO hA)

end Work.Mostow
