import Mathlib
import Submission.Work.PTCert.Glue3

namespace Work.PTCert.KleinGlue

open Submission.PTCert Submission.PTCert.G Submission.RouteB

theorem chiSPerm {m : ℕ} (S : Finset (Fin m)) (q : Equiv.Perm (Fin m))
    (h : ∀ i : Fin m, i ∈ S ↔ q i ∈ S) (a : Fin m → ZMod 2) :
    chiS S (fun i => a (q.symm i)) = chiS S a := by
  have hmap : S.map q.symm.toEmbedding = S := by
    ext x
    rw [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, hqa⟩
      rw [← hqa]
      exact (h (q.symm a)).mpr (by rwa [Equiv.apply_symm_apply])
    · intro hx
      exact ⟨q x, (h x).mp hx, by simp⟩
  have h1 : chiS S (fun i => a (q.symm i)) = chiS (S.map q.symm.toEmbedding) a := by
    simp [chiS, Finset.prod_map]
  rw [h1, hmap]

end Work.PTCert.KleinGlue
