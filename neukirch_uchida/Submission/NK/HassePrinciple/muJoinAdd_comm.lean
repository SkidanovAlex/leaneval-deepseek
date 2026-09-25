import Mathlib
import Submission.NK.HassePrinciple.MuColimAdd

universe u

namespace NK.HassePrinciple

theorem muJoinAdd_comm {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) (x y : NK.HassePrinciple.MuColim p V) :
    NK.HassePrinciple.muJoinAdd p V x y = NK.HassePrinciple.muJoinAdd p V y x := by
  obtain ⟨L, a, rfl⟩ := (muLevelSystem p V).ofLevel_surjective x
  obtain ⟨L', b, rfl⟩ := (muLevelSystem p V).ofLevel_surjective y
  calc muJoinAdd p V ((muLevelSystem p V).ofLevel L a) ((muLevelSystem p V).ofLevel L' b)
      = (muLevelSystem p V).ofLevel (L ⊔ L')
          ((muLevelSystem p V).map (le_sup_left : L ≤ L ⊔ L') a
            + (muLevelSystem p V).map (le_sup_right : L' ≤ L ⊔ L') b) :=
        muJoinAdd_ofLevel_le (p := p) (V := V) (L := L) (L' := L') (M := L ⊔ L')
          le_sup_left le_sup_right a b
    _ = (muLevelSystem p V).ofLevel (L ⊔ L')
          ((muLevelSystem p V).map (le_sup_right : L' ≤ L ⊔ L') b
            + (muLevelSystem p V).map (le_sup_left : L ≤ L ⊔ L') a) := by rw [add_comm]
    _ = muJoinAdd p V ((muLevelSystem p V).ofLevel L' b) ((muLevelSystem p V).ofLevel L a) :=
        (muJoinAdd_ofLevel_le (p := p) (V := V) (L := L') (L' := L) (M := L ⊔ L')
          (le_sup_right : L' ≤ L ⊔ L') (le_sup_left : L ≤ L ⊔ L') b a).symm

end NK.HassePrinciple
