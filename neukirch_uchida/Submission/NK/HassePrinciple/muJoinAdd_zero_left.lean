import Mathlib
import Submission.NK.HassePrinciple.MuColimAdd

universe u

namespace NK.HassePrinciple

/-- **The zero of the `μ_p` colimit is neutral on the left for `muJoinAdd`.**

The zero `muColimZero p V` is the class of `0` at the bottom level `⊥`.  Given an arbitrary
element `x = ofLevel L a`, the sum `muJoinAdd (ofLevel ⊥ 0) (ofLevel L a)` is computed at the
common upper bound `L` of `⊥` and `L` (`muJoinAdd_ofLevel_le`): it is the class of
`map bot_le 0 + map le_rfl a`, which is `0 + a = a` because the transition maps are additive
(`muLevelSystem_map_zero`) and the transition along an identity is the identity
(`muLevelSystem_map_refl_apply`). -/
theorem muJoinAdd_zero_left {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) (x : NK.HassePrinciple.MuColim p V) :
    NK.HassePrinciple.muJoinAdd p V (NK.HassePrinciple.muColimZero p V) x = x := by
  obtain ⟨L, a, rfl⟩ := (muLevelSystem p V).ofLevel_surjective x
  change muJoinAdd p V (MuColim.ofLevel p V ⊥ (0 : (muLevelSystem p V).obj ⊥))
    (MuColim.ofLevel p V L a) = MuColim.ofLevel p V L a
  rw [muJoinAdd_ofLevel_le (p := p) (V := V) (L := ⊥) (L' := L) (M := L)
    bot_le le_rfl (0 : (muLevelSystem p V).obj ⊥) a]
  congr 1
  rw [muLevelSystem_map_zero, muLevelSystem_map_refl_apply, zero_add]

end NK.HassePrinciple
