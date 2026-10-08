import Mathlib
import Submission.Work.Models.ModelData.szModelData
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.Models.Abstract.modelData_mapEquiv
import Submission.Work.Models.Port.BenderPairModels

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.ModelData

open LeanEval.GroupTheory.Defs

theorem sz_modelData_invariants {n : ℕ} (hn : 1 ≤ n)
    (P : Work.Models.ModelData (LeanEval.GroupTheory.Defs.SzModel n)) :
    Nat.card ↥P.K0 + 1 = 2 ^ (2 * n + 1) ∧ Nat.card ↥P.U = (2 ^ (2 * n + 1)) ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · -- `|K₀| = #Inv(B) = q - 1`
    rw [P.hK0card]
    -- every strongly embedded subgroup of `Sz(q)` is a conjugate of the Borel
    obtain ⟨g, hg⟩ :=
      Work.Models.Abstract.exists_conj_eq (Submission.Sz.szBenderPair n hn) P.hSemb
    rw [hg, show (Submission.Sz.szBenderPair n hn).B = Submission.Sz.szBorelS n from rfl]
    rw [Work.Models.Abstract.ncard_involutions_map_mulEquiv (MulAut.conj g)
      (Submission.Sz.szBorelS n)]
    rw [Work.Models.Sz.ncard_involutions_szBorelS n]
    have hq : 0 < 2 ^ (2 * n + 1) := pow_pos (by norm_num) _
    omega
  · -- `|U| = |U_sz| = q²`, both being Sylow `2`-subgroups of `Sz(q)`
    let S₁ : Sylow 2 (LeanEval.GroupTheory.Defs.SzModel n) :=
      P.hU2.toSylow P.not_two_dvd_index_U
    let S₂ : Sylow 2 (LeanEval.GroupTheory.Defs.SzModel n) := Submission.Sz.szSylow n
    have hS₁ : (↑S₁ : Subgroup (LeanEval.GroupTheory.Defs.SzModel n)) = P.U :=
      IsPGroup.toSylow_coe _ _
    have hS₂ : (↑S₂ : Subgroup (LeanEval.GroupTheory.Defs.SzModel n)) =
        Submission.Sz.szTwoGroupS n := Submission.Sz.szSylow_coe_sub n
    have hcard : Nat.card ↥P.U = Nat.card ↥(Submission.Sz.szTwoGroupS n) := by
      rw [← hS₁, ← hS₂]
      exact Nat.card_congr (Sylow.equiv S₁ S₂).toEquiv
    rw [hcard, Submission.Sz.card_szTwoGroupS, ← pow_mul]
    congr 1
    ring

end Work.Models.ModelData
