/-
  WilE9 / Sharp — the `Layer` vocabulary of the E9 input assembly.

  The target `Work.WilE9.Sharp.layer_strata` produces, from a `Gen`-presentation of the graph of
  a function `f`, a `*`-set `Z` with `graphOf f = psiV ⁻¹' Z` plus a *list of effectively smooth
  strata* `S : List (Σ m, EffStratum n m)` which densely covers `Z`.

  The pieces `P : StarPiece (n+1)` of `Z` live in the ambient `ℝ^{(n+1)+m}` (base `n+1`, fibre
  `m`), while `EffStratum n m` wants a semi-Pfaffian set in `ℝ^{n+(1+m)}` (base `n`, fibre
  `1+m`).  This file fixes the translation between the two shapes:

  * `pcX P` is the semi-Pfaffian set of `P` reindexed along `(n+1)+m = n+(1+m)`, so that
    `pcX P : SemiPf (n + (1 + P.m))` is exactly what `EffStratum n P.m` consumes;
  * `pcP P` is the transported base point;
  * `stratProj` (from `Vocab`) projects `ℝ^{n+(1+m)}` onto the first `n+1` coordinates, and the
    API below records that `stratProj '' (pcX P).set = projFirst (n+1) P.m '' P.X.set`,
    `stratProj '' connectedComponentIn (pcX P).set (pcP P) = StarPiece.set P`, and that
    `stratProj` is continuous.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.SemiPf_castFin_set
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## The reindexed shape of a `*`-piece -/

/-- The semi-Pfaffian set of a `*`-piece `P : StarPiece (n+1)`, reindexed along the
value-preserving identification `(n+1)+m = n+(1+m)` of the ambient coordinates.  Its ambient
`ℝ^{n+(1+m)}` is the shape required by `EffStratum n P.m` (base `ℝⁿ`, fibre `ℝ^{1+m}`). -/
def pcX {n : ℕ} (P : StarPiece (n+1)) : SemiPf (n + (1 + P.m)) :=
  SemiPf.castFin (addSplit n P.m) P.X

/-- The transported base point of the reindexed `*`-piece `pcX P`. -/
def pcP {n : ℕ} (P : StarPiece (n+1)) : Fin (n + (1 + P.m)) → ℝ :=
  fun i => P.p (Fin.cast (addSplit n P.m).symm i)

/-! ## `stratProj` and the coordinate identification -/

/-- The definition of `stratProj` in terms of `projFirst` and the coordinate equivalence
`Fin.cast (addSplit n m)`; this is the form in which all the image computations are done. -/
theorem stratProj_eq_projFirst_comp {n m : ℕ} (y : Fin (n + (1 + m)) → ℝ) :
    stratProj y
      = WilkiesDesign.E.projFirst (n + 1) m
          (fun j => y (Fin.cast (Work.WilE9.Sharp.addSplit n m) j)) := rfl

/-- `stratProj` is continuous (it is a linear projection after a permutation of the
coordinates). -/
theorem continuous_stratProj {n m : ℕ} :
    Continuous (stratProj : (Fin (n + (1 + m)) → ℝ) → (Fin (n + 1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  exact continuous_apply _

/-- The image of the coordinate reindexing of a set under `stratProj` is the first-`n+1`
projection of the set. -/
theorem stratProj_image_preimage {n m : ℕ} (S : Set (Fin ((n + 1) + m) → ℝ)) :
    stratProj '' {y : Fin (n + (1 + m)) → ℝ |
        (fun i => y (Fin.cast (Work.WilE9.Sharp.addSplit n m) i)) ∈ S}
      = WilkiesDesign.E.projFirst (n + 1) m '' S := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun i => y (Fin.cast (addSplit n m) i), hy, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun i => w (Fin.cast (addSplit n m).symm i), ?_, ?_⟩
    · change (fun i => w (Fin.cast (addSplit n m).symm (Fin.cast (addSplit n m) i))) ∈ S
      have hfun : (fun i => w (Fin.cast (addSplit n m).symm (Fin.cast (addSplit n m) i))) = w := by
        funext i
        exact congrArg w (Fin.ext (by simp))
      rw [hfun]
      exact hw
    · funext i
      show w (Fin.cast (addSplit n m).symm
          (Fin.cast (addSplit n m) (Fin.castAdd m i))) = w (Fin.castAdd m i)
      exact congrArg w (Fin.ext (by simp))

/-- The image under `stratProj` of the closure of a set is contained in the closure of its
image. -/
theorem stratProj_image_closure_subset {n m : ℕ} (S : Set (Fin (n + (1 + m)) → ℝ)) :
    stratProj '' closure S ⊆ closure (stratProj '' S) :=
  image_closure_subset_closure_image continuous_stratProj

/-! ## The API of `pcX` / `pcP` -/

theorem pcX_set {n : ℕ} (P : StarPiece (n+1)) :
    (pcX P).set = {y : Fin (n + (1 + P.m)) → ℝ |
      (fun i => y (Fin.cast (addSplit n P.m) i)) ∈ P.X.set} :=
  (SemiPf_castFin_set (addSplit n P.m) P.X).1

theorem pcX_fmt {n : ℕ} (P : StarPiece (n+1)) : (pcX P).fmt = P.X.fmt :=
  (SemiPf_castFin_set (addSplit n P.m) P.X).2.1

theorem pcX_deg {n : ℕ} (P : StarPiece (n+1)) : (pcX P).deg = P.X.deg :=
  (SemiPf_castFin_set (addSplit n P.m) P.X).2.2.1

theorem pcX_basics {n : ℕ} (P : StarPiece (n+1)) :
    (pcX P).basics.length = P.X.basics.length :=
  (SemiPf_castFin_set (addSplit n P.m) P.X).2.2.2

theorem pcX_fmt_le {n F : ℕ} (P : StarPiece (n+1)) (h : P.X.fmt ≤ F) : (pcX P).fmt ≤ F := by
  rw [pcX_fmt]; exact h

/-- The transported base point belongs to the reindexed set as soon as the original base point
belongs to the original set. -/
theorem pcP_mem {n : ℕ} (P : StarPiece (n+1)) (h : P.p ∈ P.X.set) : pcP P ∈ (pcX P).set := by
  rw [pcX_set]
  change (fun i => pcP P (Fin.cast (addSplit n P.m) i)) ∈ P.X.set
  have hfun : (fun i => pcP P (Fin.cast (addSplit n P.m) i)) = P.p := by
    funext i
    exact congrArg P.p (Fin.ext (by simp [pcP]))
  rw [hfun]
  exact h

/-- **The projection of the reindexed piece.**  The connected component of the reindexed set
projects exactly onto the `*`-piece: this is the identification that lets `EffStrat` (which lives
in the `n + (1+m)` shape) be applied to a `StarPiece` (which lives in the `(n+1) + m` shape). -/
theorem stratProj_image_component {n : ℕ} (P : StarPiece (n+1)) :
    stratProj '' connectedComponentIn (pcX P).set (pcP P) = StarPiece.set P := by
  have h1 : pcX P = Work.WilE7.SemiPf.reindex (finCongr (addSplit n P.m)) P.X :=
    SemiPf.castFin_eq_reindex (addSplit n P.m) P.X
  have h2 : pcP P = fun i => P.p ((finCongr (addSplit n P.m)).symm i) := rfl
  rw [h1, h2, Work.WilE7.reindex_component]
  exact stratProj_image_preimage (connectedComponentIn P.X.set P.p)

/-- A `*`-piece whose base point is outside its semi-Pfaffian set is empty. -/
theorem starPiece_set_eq_empty {n : ℕ} (P : StarPiece (n+1)) (h : P.p ∉ P.X.set) :
    StarPiece.set P = ∅ := by
  unfold StarPiece.set
  rw [connectedComponentIn_eq_empty h, Set.image_empty]

/-- A `*`-piece is a subset of the projection of its own semi-Pfaffian set. -/
theorem starPiece_set_subset_proj {n : ℕ} (P : StarPiece (n+1)) :
    StarPiece.set P ⊆ WilkiesDesign.E.projFirst (n + 1) P.m '' P.X.set := by
  unfold StarPiece.set
  exact Set.image_mono (connectedComponentIn_subset _ _)

end Work.WilE9.Sharp
