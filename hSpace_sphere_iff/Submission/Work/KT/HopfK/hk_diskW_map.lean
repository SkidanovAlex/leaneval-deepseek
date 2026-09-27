import Mathlib
import Submission.Work.KT.HopfK.Disk

namespace Work.KT.HopfK

open _root_.Matrix

/-! ## Naturality of the `W`-construction under an arbitrary ring hom

These are the general-ring analogues of the evaluation-at-a-point lemmas in
`Submission/Work/KT/HopfK/diskW_map_evalC.lean`.  They are proved by unfolding the
definitions and rewriting with the corresponding naturality lemmas for `kronMat`,
`rotMat`, `Wblk` and `Dblk` from `Submission/Work/KT/hk_relprod.lean`. -/

section GeneralMap

variable {R S : Type} [CommRing R] [CommRing S]

/-- `diskQ1` is natural under a ring hom. -/
lemma diskQ1_map (φ : R →+* S) {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R) :
    (diskQ1 P Q E).map φ = diskQ1 (P.map φ) (Q.map φ) (E.map φ) := by
  unfold diskQ1
  simpa using fromBlocks_kron_map (φ := φ) P Q E E

/-- `diskQ2` is natural under a ring hom. -/
lemma diskQ2_map (φ : R →+* S) {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R) :
    (diskQ2 P Q E).map φ = diskQ2 (P.map φ) (Q.map φ) (E.map φ) := by
  unfold diskQ2
  simpa using fromBlocks_kron_map (φ := φ) P E E Q

/-- `diskC` is natural under a ring hom. -/
lemma diskC_map (φ : R →+* S) {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R)
    (c s : R) :
    (diskC P Q E c s).map φ =
      diskC (P.map φ) (Q.map φ) (E.map φ) (φ c) (φ s) := by
  unfold diskC
  rw [Matrix.map_mul (f := φ), Matrix.map_mul (f := φ),
    rotMat_map, rotMatInv_map, diskQ2_map]

/-- `diskW` is natural under a ring hom. -/
theorem hk_diskW_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (P Q E : Matrix (Fin n) (Fin n) R) (c s : R) :
    (diskW P Q E c s).map φ = diskW (P.map φ) (Q.map φ) (E.map φ) (φ c) (φ s) := by
  unfold diskW
  rw [Matrix.map_mul (f := φ), Matrix.map_mul (f := φ),
    Wblk_map, Dblk_map, diskC_map, diskQ1_map]

end GeneralMap

end Work.KT.HopfK
