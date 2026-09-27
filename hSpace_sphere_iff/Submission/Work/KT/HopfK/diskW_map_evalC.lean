import Mathlib
import Submission.Work.KT.HopfK.Disk

namespace Work.KT.HopfK

open _root_.Matrix

/-- `diskQ1` is natural under evaluation at a point. -/
lemma diskQ1_map_evalC {T : Type} [TopologicalSpace T] (t : T) {n : ℕ}
    (P Q E : Matrix (Fin n) (Fin n) C(T, ℂ)) :
    (diskQ1 P Q E).map (evalC t) =
      diskQ1 (P.map (evalC t)) (Q.map (evalC t)) (E.map (evalC t)) := by
  unfold diskQ1
  simpa using fromBlocks_kron_map (φ := (evalC t).toRingHom) P Q E E

/-- `diskQ2` is natural under evaluation at a point. -/
lemma diskQ2_map_evalC {T : Type} [TopologicalSpace T] (t : T) {n : ℕ}
    (P Q E : Matrix (Fin n) (Fin n) C(T, ℂ)) :
    (diskQ2 P Q E).map (evalC t) =
      diskQ2 (P.map (evalC t)) (Q.map (evalC t)) (E.map (evalC t)) := by
  unfold diskQ2
  simpa using fromBlocks_kron_map (φ := (evalC t).toRingHom) P E E Q

/-- `Wblk` is natural under evaluation at a point. -/
lemma Wblk_map_evalC {T : Type} [TopologicalSpace T] (t : T) {p : ℕ}
    (C : Matrix (Fin p) (Fin p) C(T, ℂ)) :
    (Wblk p C).map (evalC t) = Wblk p (C.map (evalC t)) := by
  simpa using Wblk_map (φ := (evalC t).toRingHom) C

/-- `Dblk` is natural under evaluation at a point. -/
lemma Dblk_map_evalC {T : Type} [TopologicalSpace T] (t : T) {p : ℕ}
    (X C : Matrix (Fin p) (Fin p) C(T, ℂ)) :
    (Dblk p X C).map (evalC t) = Dblk p (X.map (evalC t)) (C.map (evalC t)) := by
  simpa using Dblk_map (φ := (evalC t).toRingHom) X C

/-- `diskC` is natural under evaluation at a point. -/
lemma diskC_map_evalC {T : Type} [TopologicalSpace T] (t : T) {n : ℕ}
    (P Q E : Matrix (Fin n) (Fin n) C(T, ℂ)) (c s : C(T, ℂ)) :
    (diskC P Q E c s).map (evalC t) =
      diskC (P.map (evalC t)) (Q.map (evalC t)) (E.map (evalC t))
        (evalC t c) (evalC t s) := by
  unfold diskC
  rw [Matrix.map_mul (f := (evalC t)), Matrix.map_mul (f := (evalC t)),
    rotMat_map_eval, rotMatInv_map_eval, diskQ2_map_evalC]
  rfl

lemma diskW_map_evalC {T : Type} [TopologicalSpace T] (t : T) {n : ℕ}
    (P Q E : Matrix (Fin n) (Fin n) C(T, ℂ)) (c s : C(T, ℂ)) :
    (diskW P Q E c s).map (evalC t) =
      diskW (P.map (evalC t)) (Q.map (evalC t)) (E.map (evalC t)) (evalC t c) (evalC t s) := by
  unfold diskW
  rw [Matrix.map_mul (f := (evalC t)), Matrix.map_mul (f := (evalC t)),
    Wblk_map_evalC, Dblk_map_evalC, diskC_map_evalC, diskQ1_map_evalC]

end Work.KT.HopfK
