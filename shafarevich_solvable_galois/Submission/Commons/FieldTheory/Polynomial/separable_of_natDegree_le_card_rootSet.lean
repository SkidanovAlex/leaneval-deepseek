import Mathlib.FieldTheory.Separable
import Submission.Commons.FieldTheory.Polynomial.rootSet_map_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Polynomial

lemma separable_of_natDegree_le_card_rootSet {F K : Type*} [Field F] [Field K] [Algebra F K]
    {f : Polynomial F} (hf : f ≠ 0) (hsplit : (f.map (algebraMap F K)).Splits)
    (h : f.natDegree ≤ Fintype.card ↑((f.map (algebraMap F K)).rootSet K)) : f.Separable := by
  classical
  have hmap : (f.map (algebraMap F K)).rootSet K = f.rootSet K :=
    rootSet_map_eq (K := F) (L := K) f
  rw [Set.fintypeCard_eq_ncard] at h
  rw [hmap] at h
  have hle : Set.ncard (f.rootSet K) ≤ f.natDegree := Polynomial.ncard_rootSet_le f K
  have heq : Fintype.card ↑(f.rootSet K) = f.natDegree := by
    rw [Set.fintypeCard_eq_ncard]
    exact le_antisymm hle h
  exact (Polynomial.card_rootSet_eq_natDegree_iff_of_splits hf hsplit).mp heq

end Commons.FieldTheory.Polynomial