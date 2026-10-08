import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.modelDataBorel
import Submission.Work.Models.Abstract.modelFactsFor
import Submission.Work.Models.Abstract.modelData_mapEquiv
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.Models.Abstract.ncard_involutions_B
import Submission.Work.Models.Abstract.eq_U_of_isSplitRankOne
import Submission.Work.Models.ModelData.sz_modelData_invariants
import Submission.Work.Models.ModelData.psu3_modelData_invariants
import Submission.Work.Models.ModelData.psl2_modelData_invariants

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-
# Step 5 (branch determination): the invariants `(|U|, #Inv(B))` force `PSU3`

Peterfalvi II.7.4(1) + step 3 of the reduction give, for `Y = U/Z(U)` with its split rank-one
datum `(B_Y, U_Y, w_Y)`, the two invariants

  `|U_Y| = ℓ³`   and   `#Inv(B_Y) + 1 = ℓ`   (`ℓ = |C_{Q₀}(P)|`).

This result turns those data into the *identification*: if in a simple Bender group a split
rank-one datum satisfies `|U| = (#Inv(B) + 1)³`, then the group is `PSU3Model m` and
`#Inv(B) + 1 = 2^m`, `m ≥ 2`.  (Note the parentheses: `^` binds tighter than `+`, so the
hypothesis must be written `((…).ncard + 1) ^ 3`.)

Route.  Write `q := #Inv(B) + 1`.  Since the involutions of a strongly embedded subgroup are a
conjugacy-invariant class (`Work.Models.Abstract.exists_conj_eq`: every strongly embedded subgroup
is a conjugate of the Borel of any `ModelData`), transportation along `e : Y ≃* Model` gives
`#Inv(B) = #Inv(B_model)`, and `|U| = |e U|`.  The model invariants (all in the workspace) are

* `PSL2Model m`: `|U| = 2^m`, `#Inv(B) = 2^m - 1` (`psl2NcardInvolutionsStab`,
  `card_unipotentPSLHom_range`), so `|U| = q`;
* `SzModel m`: `q = 2^{2m+1}`, `|U| = q²`, `#Inv(B) = q - 1` (`ncard_involutions_szBorelS`,
  `card_szTS`), so `|U| = q²`;
* `PSU3Model m`: `q = 2^m`, `|U| = q³`, `#Inv(B) = q - 1` (`card_psu3U`,
  `ncard_involutions_psu3B`), so `|U| = q³`.

Each model also satisfies the *index* identity `[Y : B] = 1 + |U|`
(`psu3B_index_eq_one_add_card_psu3U` and its `PSL2`/`Sz` analogues), which transports to `Y` and
makes `U` a Sylow `2`-subgroup of `Y` (the index `1 + |U| = 1 + q^k` is odd); this is what
identifies `|U|` with the model's unipotent order.  Since `q ≥ 3` in all three families,
`|U| = q³` excludes the first two branches, leaving `Y ≅ PSU3Model m` with `#Inv(B) + 1 = 2^m`
and `2 ≤ m`.
-/
theorem exists_PSU3_of_card_sylow_eq_cube {Y : Type} [Group Y] [Finite Y]
    (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y) {B U : Subgroup Y} {w : Y}
    (h : Submission.Blueprint.IsSplitRankOne B U w)
    (hcard : Nat.card ↥U = ((Submission.Blueprint.involutions (B : Set Y)).ncard + 1) ^ 3) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (Y ≃* LeanEval.GroupTheory.Defs.PSU3Model m) ∧
      (Submission.Blueprint.involutions (B : Set Y)).ncard + 1 = 2 ^ m := by
  obtain ⟨P, hPB⟩ := Work.PSU3.StageA.modelDataBorel hY h.stronglyEmbedded
  have hsplit : Submission.Blueprint.IsSplitRankOne P.B U w := hPB.symm ▸ h
  have hUeq : U = P.U :=
    Work.Models.Abstract.eq_U_of_isSplitRankOne P.toBenderPair hsplit
  cases hY with
  | isPSL2 n hn e =>
      exfalso
      obtain ⟨P', hB', hU', hT', hw', hK0'⟩ := Work.Models.Abstract.modelData_mapEquiv P e
      obtain ⟨hK0raw, hUraw⟩ := Work.Models.ModelData.psl2_modelData_invariants (n := n) hn P'
      rw [hU', Subgroup.card_map_of_injective (MulEquiv.injective e)] at hUraw
      rw [hK0', Subgroup.card_map_of_injective (MulEquiv.injective e)] at hK0raw
      have hq : (Submission.Blueprint.involutions (B : Set Y)).ncard + 1 = 2 ^ n := by
        rw [← hPB, ← P.hK0card]
        exact hK0raw
      have hUY : Nat.card ↥U = 2 ^ n := by
        rw [hUeq]
        exact hUraw
      rw [hUY, hq] at hcard
      have h4 : (1 : ℕ) < 2 ^ n := by
        have : (4 : ℕ) ≤ 2 ^ n := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
      have hlt : (2 ^ n) ^ 1 < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right h4 (by norm_num)
      rw [pow_one] at hlt
      omega
  | isSuzuki n hn e =>
      exfalso
      obtain ⟨P', hB', hU', hT', hw', hK0'⟩ := Work.Models.Abstract.modelData_mapEquiv P e
      obtain ⟨hK0raw, hUraw⟩ := Work.Models.ModelData.sz_modelData_invariants (n := n) hn P'
      rw [hU', Subgroup.card_map_of_injective (MulEquiv.injective e)] at hUraw
      rw [hK0', Subgroup.card_map_of_injective (MulEquiv.injective e)] at hK0raw
      have hq : (Submission.Blueprint.involutions (B : Set Y)).ncard + 1 = 2 ^ (2 * n + 1) := by
        rw [← hPB, ← P.hK0card]
        exact hK0raw
      have hUY : Nat.card ↥U = (2 ^ (2 * n + 1)) ^ 2 := by
        rw [hUeq]
        exact hUraw
      rw [hUY, hq] at hcard
      have hgt : (1 : ℕ) < 2 ^ (2 * n + 1) := by
        have : (2 : ℕ) ≤ 2 ^ (2 * n + 1) := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hlt : (2 ^ (2 * n + 1)) ^ 2 < (2 ^ (2 * n + 1)) ^ 3 :=
        Nat.pow_lt_pow_right hgt (by norm_num)
      omega
  | isPSU3 n hn e =>
      obtain ⟨P', hB', hU', hT', hw', hK0'⟩ := Work.Models.Abstract.modelData_mapEquiv P e
      obtain ⟨hK0raw, -⟩ := Work.Models.ModelData.psu3_modelData_invariants (n := n) hn P'
      rw [hK0', Subgroup.card_map_of_injective (MulEquiv.injective e)] at hK0raw
      refine ⟨n, hn, ⟨e⟩, ?_⟩
      rw [← hPB, ← P.hK0card]
      exact hK0raw

end Work.PSU3.StageB
