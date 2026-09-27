import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.Interfaces

/-!
# The eight boundary pieces of the parameter box of the germ route

The charted difference system of the germ route is a map on `Amb 4 = ℝ⁵` whose unknown coordinates are
the loop parameter `z 0`, a *dummy* coordinate `z 1` (the charts' difference map does not see it, since
the loop is presented by `sgLoop`, which reads only `z 0`), and the three chain parameters `z 2, z 3,
z 4`.  The parametric-Sard brick also excludes zeros on the boundary of the box, which is what gives
the *interiority* clause of `GoodPair`; the boundary is covered by eight `3`-dimensional faces: pin one
of the four *box* coordinates at `0` or `1`, pin the dummy at `0`, and let the remaining three
coordinates run over the box.

This module fixes those eight embeddings, as affine maps `sgFace k vv : ℝ³ → ℝ⁵` (the *scatter* map
`scatterCLM k` puts the free coordinates into the box coordinates other than the `k`-th, and
`(vv : ℝ) • basisVec5 (boxIdx k)` pins the `k`-th one), together with their inverse assignment
`gatherCLM`.

* `Work.Drive.boxIdx : Fin 4 → Fin 5` — the four box coordinates, in increasing order;
* `Work.Drive.basisVec5`, `Work.Drive.coord3` — the standard basis vector and the coordinate
  projections;
* `Work.Drive.scatterCLM`, `Work.Drive.sgFace`, `Work.Drive.gatherCLM` — the pieces and their inverse;
* `Work.Drive.contDiff_sgFace` — the pieces are `C^∞` (they are affine);
* `Work.Drive.gatherCLM_sgFace` — `gatherCLM` inverts the free part of `sgFace`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-- **The four *box* coordinates of `Amb 4 = ℝ⁵`**: the coordinates other than the dummy `1`, in
increasing order (`0, 2, 3, 4`). -/
def boxIdx : Fin 4 → Fin 5 := Fin.succAbove 1

/-- The `i`-th standard basis vector of `Amb 4`. -/
def basisVec5 (i : Fin 5) : Amb 4 := WithLp.toLp 2 (Pi.single i 1)

/-- The `i`-th coordinate of `ℝ³` as a continuous linear map. -/
def coord3 (i : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

/-- **The scatter map**: put the three coordinates of `y` into the box coordinates other than the
`k`-th, leaving the `k`-th box coordinate and the dummy coordinate at `0`. -/
def scatterCLM (k : Fin 4) : EuclideanSpace ℝ (Fin 3) →L[ℝ] Amb 4 :=
  ∑ j : Fin 3, (coord3 j).smulRight (basisVec5 (boxIdx (Fin.succAbove k j)))

/-- **The `k`-th face embedding of the parameter box**: the box coordinate `k` is pinned at `vv`
(thought of as `0` or `1`) and the dummy coordinate at `0`; the free coordinates are those of `y`. -/
def sgFace (k : Fin 4) (vv : Fin 2) : EuclideanSpace ℝ (Fin 3) → Amb 4 :=
  fun y => (vv : ℝ) • basisVec5 (boxIdx k) + scatterCLM k y

/-- **The inverse assignment of the free coordinates**: read off the box coordinates of `z` other than
the `k`-th, in the order of `Fin.succAbove k`. -/
def gatherCLM (k : Fin 4) : Amb 4 →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm :
      (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)).comp
    (ContinuousLinearMap.pi (fun j : Fin 3 =>
      PiLp.proj 2 (fun _ : Fin 5 => ℝ) (boxIdx (Fin.succAbove k j))))

@[simp] lemma gatherCLM_apply (k : Fin 4) (z : Amb 4) (j : Fin 3) :
    gatherCLM k z j = z (boxIdx (Fin.succAbove k j)) := by
  simp [gatherCLM, PiLp.proj_apply]

@[simp] lemma basisVec5_apply (i j : Fin 5) :
    basisVec5 i j = (Pi.single i (1 : ℝ) : Fin 5 → ℝ) j := by
  rw [basisVec5, WithLp.ofLp_toLp, Pi.single_apply]

@[simp] lemma coord3_apply (i : Fin 3) (y : EuclideanSpace ℝ (Fin 3)) : coord3 i y = y i := by
  simp [coord3, PiLp.proj_apply]

@[simp] lemma scatterCLM_apply (k : Fin 4) (y : EuclideanSpace ℝ (Fin 3)) :
    scatterCLM k y = ∑ j : Fin 3, (y j) • basisVec5 (boxIdx (Fin.succAbove k j)) := by
  simp only [scatterCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    coord3_apply]

lemma contDiff_sgFace (k : Fin 4) (vv : Fin 2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sgFace k vv) :=
  contDiff_const.add (scatterCLM k).contDiff

lemma boxIdx_zero : boxIdx 0 = (0 : Fin 5) := rfl
lemma boxIdx_one : boxIdx 1 = (2 : Fin 5) := rfl
lemma boxIdx_two : boxIdx 2 = (3 : Fin 5) := rfl
lemma boxIdx_three : boxIdx 3 = (4 : Fin 5) := rfl

lemma boxIdx_ne_dummy (k : Fin 4) : boxIdx k ≠ (1 : Fin 5) := by
  fin_cases k <;> decide

lemma continuous_sgFace (k : Fin 4) (vv : Fin 2) : Continuous (sgFace k vv) :=
  (contDiff_sgFace k vv).continuous

lemma cbIdx_eq_boxIdx (j : Fin 3) : cbIdx j = boxIdx (Fin.succ j) := by
  fin_cases j <;> rfl

lemma exists_boxIdx_eq (i : Fin 5) (hi : i ≠ 1) : ∃ k : Fin 4, boxIdx k = i := by
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact absurd rfl hi
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

end

end Work.Drive
