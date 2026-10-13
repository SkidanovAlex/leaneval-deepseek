/-
  `Work.CoreStep.StratReindexDefs`: reindexing the coordinates of an ambient stratum
  `Stratum 0 N` along an equivalence `e : Fin (0 + N) ≃ Fin (0 + N')` of coordinate sets.

  The construction is `Work.WilE7.SemiPf.reindex e` on the semi-Pfaffian part, together with
  the same renaming `Work.WilE7.EAPoly.reindex e` on the equations `h`.  This file records the
  elementary consequences that the main statement of `stratReindex_exists` needs:

  * the set: `(Stratum.reindex e S).X.set = {y | fun i => y (e i) ∈ S.X.set}` (`reindex_X_set`);
  * the degree: `(Stratum.reindex e S).deg = S.deg` (`reindex_deg`);
  * the evaluation of the equations and of their symbolic derivatives: `reindex_h_eval`,
    `reindex_eaD`, `reindex_jac_entry`.

  (The reindexing is `Work.CoreStep.Stratum.reindex`, so — as for `Work.WilE7.SemiPf.reindex` —
  it is applied explicitly, `Stratum.reindex e S`, rather than by dot notation `S.reindex e`.)

  The two non-elementary halves of the main statement — the transport of `Good` and the
  transport of `jac` as a linear map — are proved separately (on top of this file).
-/
import Mathlib
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.reindex_eval
import Submission.Work.WilE7.CoreStep.eaD_reindex

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- **Reindexing a stratum.**  Along an equivalence `e : Fin (p + q) ≃ Fin (p + q')` of
coordinate sets, a stratum in `ℝ^{p+q}` is transported to one in `ℝ^{p+q'}`: the
semi-Pfaffian set is reindexed and every equation `h a` is renamed accordingly (the number of
equations `j` and the chain size `r` are unchanged). -/
def Stratum.reindex {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q')) (S : Stratum p q) :
    Stratum p q' :=
  ⟨Work.WilE7.SemiPf.reindex e S.X, S.j, fun a => Work.WilE7.EAPoly.reindex e (S.h a)⟩

theorem Stratum.reindex_j {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) : (Stratum.reindex e S).j = S.j := rfl

theorem Stratum.reindex_r {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) : (Stratum.reindex e S).X.r = S.X.r := rfl

theorem Stratum.reindex_X {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) : (Stratum.reindex e S).X = Work.WilE7.SemiPf.reindex e S.X := rfl

theorem Stratum.reindex_h {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) (a : Fin S.j) :
    (Stratum.reindex e S).h a = Work.WilE7.EAPoly.reindex e (S.h a) := rfl

/-- The set of a reindexed stratum is the preimage of the original set under `y ↦ y ∘ e`. -/
theorem Stratum.reindex_X_set {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) :
    (Stratum.reindex e S).X.set =
      {y : Fin (p + q') → ℝ | (fun i : Fin (p + q) => y (e i)) ∈ S.X.set} :=
  Work.WilE7.sp_reindex_set e S.X

/-- Membership form of `reindex_X_set`. -/
theorem Stratum.reindex_mem {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) (y : Fin (p + q') → ℝ) :
    y ∈ (Stratum.reindex e S).X.set ↔ (fun i : Fin (p + q) => y (e i)) ∈ S.X.set := by
  rw [Stratum.reindex_X_set]
  exact Iff.rfl

/-- The degree of a reindexed stratum is the degree of the original stratum. -/
theorem Stratum.reindex_deg {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) : (Stratum.reindex e S).deg = S.deg := by
  show (Work.WilE7.SemiPf.reindex e S.X).deg
      + (∑ a : Fin S.j, atomDeg (Work.WilE7.EAPoly.reindex e (S.h a)))
      = S.X.deg + ∑ a : Fin S.j, atomDeg (S.h a)
  rw [Work.WilE7.sp_reindex_deg]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Work.WilE7.sp_atomDeg_reindex e (S.h a)

/-- The equations of the reindexed stratum evaluate at `y` as the original equations at
`y ∘ e`. -/
theorem Stratum.reindex_h_eval {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) (y : Fin (p + q') → ℝ) (a : Fin S.j) :
    eaEval (Stratum.reindex e S).X.c ((Stratum.reindex e S).h a) y =
      eaEval S.X.c (S.h a) (fun i : Fin (p + q) => y (e i)) :=
  Work.WilE7.sp_reindex_eval e S.X.c (S.h a) y

/-- The symbolic derivative of the equations of the reindexed stratum: `eaD` in the new
direction `l` is the rename of `eaD` in the old direction `e.symm l`. -/
theorem Stratum.reindex_eaD {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) (a : Fin S.j) (l : Fin (p + q')) :
    eaD (Stratum.reindex e S).X.c l ((Stratum.reindex e S).h a) =
      Work.WilE7.EAPoly.reindex e (eaD S.X.c (e.symm l) (S.h a)) := by
  have h := Work.WilE7.CoreStep.eaD_reindex e S.X.c (e.symm l) (S.h a)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- Entrywise: the Jacobian entries of the reindexed stratum at `y` are the Jacobian entries
of the original stratum at `y ∘ e`, in the corresponding direction. -/
theorem Stratum.reindex_jac_entry {p q q' : ℕ} (e : Fin (p + q) ≃ Fin (p + q'))
    (S : Stratum p q) (y : Fin (p + q') → ℝ) (a : Fin S.j) (l : Fin (p + q')) :
    eaEval (Stratum.reindex e S).X.c
        (eaD (Stratum.reindex e S).X.c l ((Stratum.reindex e S).h a)) y =
      eaEval S.X.c (eaD S.X.c (e.symm l) (S.h a)) (fun i : Fin (p + q) => y (e i)) := by
  rw [Stratum.reindex_eaD e S a l]
  exact Work.WilE7.sp_reindex_eval e S.X.c (eaD S.X.c (e.symm l) (S.h a)) y

end Work.CoreStep
