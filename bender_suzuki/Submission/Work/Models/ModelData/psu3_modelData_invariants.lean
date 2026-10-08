import Mathlib
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.orderOf_conj
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.mem_map_conj_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Models.ModelData

open LeanEval.GroupTheory.Defs

/-- Conjugating a subgroup does not change the number of involutions it contains. -/
lemma ncard_involutions_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    (Submission.Blueprint.involutions (Submission.Blueprint.conj g H : Set G)).ncard
      = (Submission.Blueprint.involutions (H : Set G)).ncard := by
  have hset : Submission.Blueprint.involutions (Submission.Blueprint.conj g H : Set G)
      = MulAut.conj g '' Submission.Blueprint.involutions (H : Set G) := by
    ext x
    simp only [Submission.Blueprint.involutions, Set.mem_ofPred_eq, Set.mem_image,
      Submission.Blueprint.conj]
    constructor
    · rintro ⟨hmem, hord⟩
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hmem
      rw [← hax] at hord
      refine ⟨a, ⟨ha, ?_⟩, hax⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Commons.GroupTheory.StronglyEmbedded.orderOf_conj g a] using hord
    · rintro ⟨y, ⟨hyH, hy2⟩, rfl⟩
      refine ⟨Subgroup.mem_map.mpr ⟨y, hyH, rfl⟩, ?_⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Commons.GroupTheory.StronglyEmbedded.orderOf_conj g y] using hy2
  rw [hset]
  exact Set.ncard_image_of_injective _ (MulAut.conj g).injective

theorem psu3_modelData_invariants {n : ℕ} (hn : 2 ≤ n)
    (P : Work.Models.ModelData (LeanEval.GroupTheory.Defs.PSU3Model n)) :
    Nat.card ↥P.K0 + 1 = 2 ^ n ∧ Nat.card ↥P.U = (2 ^ n) ^ 3 := by
  have hn1 : 1 ≤ n := by omega
  -- The number of involutions of `P.K0` equals the involution count of the standard Borel,
  -- since every strongly embedded subgroup is a conjugate of it.
  have hK0 : Nat.card ↥P.K0 = 2 ^ n - 1 := by
    rw [P.hK0card]
    obtain ⟨g, hg⟩ := Work.Models.Abstract.exists_conj_eq
      (Submission.PSU3.psu3BenderPair n hn) (H := P.B) P.hSemb
    rw [hg, ncard_involutions_conj]
    exact ncard_involutions_psu3B n hn
  -- `P.U` is a Sylow `2`-subgroup, hence conjugate to the standard one.
  have hU : Nat.card ↥P.U = Nat.card ↥(Submission.PSU3.psu3U n) := by
    obtain ⟨S, hS⟩ := P.exists_sylow_eq_U
    obtain ⟨S₀, hS₀⟩ := (Submission.PSU3.psu3BenderPair n hn).exists_sylow_eq_U
    have hS₀' : (S₀ : Subgroup (PSU3Model n)) = Submission.PSU3.psu3U n := by
      rw [hS₀]; rfl
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := PSU3Model n) S₀ S
    have hcoe : (S : Subgroup (PSU3Model n))
        = (S₀ : Subgroup (PSU3Model n)).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.smul_def]; rfl
    rw [← hS, ← hS₀', hcoe, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  rw [hK0, hU]
  constructor
  · rw [Nat.sub_add_cancel Nat.one_le_two_pow]
  · rw [Submission.card_psu3U n hn, Submission.PSU3.card_suUS n hn1]
    rw [← pow_mul, Nat.mul_comm n 3]

end Work.Models.ModelData
