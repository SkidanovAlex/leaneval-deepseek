/-
The Suzuki group `Sz(2^(2n+1))` acts 2-transitively on the `q^2 + 1` cosets of its Borel
subgroup `B`.

Indeed, the Bruhat decomposition `Sz = B ∪ B w B` says that every element outside `B` lies in the
single double coset `B w B`; a general lemma on double cosets then shows that the left coset
action of `G` on `G ⧸ B` is 2-transitive.  Consequences recorded here: the degree is `q^2 + 1`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Main
import Submission.Work.Models.Port.Sz.BNPair
import Submission.Work.Models.Port.Sz.StronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.coset_multiplyPretransitive_two_of_two_doubleCosets
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_quotient_leftRel
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.normalizer_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-- The Weyl element `w` as an element of `SzModel n`. -/
noncomputable def szWgM (n : ℕ) : SzModel n := ⟨szWg n, szWg_mem_szModel n⟩

/-- The Borel subgroup `B` as a subgroup of `SzModel n`. -/
noncomputable def szBorelS (n : ℕ) : Subgroup (SzModel n) :=
  (szBorel n).subgroupOf (SzModel n)

/-- The Bruhat decomposition, expressed as the cover hypothesis `G = B ∪ B w B` used by the
double-coset lemma. -/
theorem sz_cover (n : ℕ) :
    ∀ g : SzModel n, g ∈ szBorelS n ∨ ∃ b₁ b₂ : ↥(szBorelS n),
      g = (b₁ : SzModel n) * szWgM n * (b₂ : SzModel n) := by
  intro g
  by_cases hg : g ∈ szBorelS n
  · exact Or.inl hg
  · right
    have hcar : (SzModel n : Set (GL (Fin 4) (SzField n))) = szBwBSet n := by
      rw [szModel_eq_szBwBSubgroup' n]; ext x; rfl
    have hgs : (g : GL (Fin 4) (SzField n)) ∈ szBwBSet n := le_of_eq hcar g.2
    have hnotB : (g : GL (Fin 4) (SzField n)) ∉ szBorel n := by
      intro h
      exact hg (show g ∈ (szBorel n).subgroupOf (SzModel n) from
        Subgroup.mem_subgroupOf.mpr h)
    rcases hgs with h | h
    · exact absurd h hnotB
    · obtain ⟨b₁, hb₁, b₂, hb₂, heq⟩ := (mem_szBwB n _).mp h
      refine ⟨⟨⟨b₁, szBorel_le_szModel n hb₁⟩, hb₁⟩,
        ⟨⟨b₂, szBorel_le_szModel n hb₂⟩, hb₂⟩, ?_⟩
      apply Subtype.ext
      show (g : GL (Fin 4) (SzField n)) =
        ((⟨⟨b₁, szBorel_le_szModel n hb₁⟩, hb₁⟩ : ↥(szBorelS n)) : SzModel n) *
          (⟨szWg n, szWg_mem_szModel n⟩ : SzModel n) *
          ((⟨⟨b₂, szBorel_le_szModel n hb₂⟩, hb₂⟩ : ↥(szBorelS n)) : SzModel n)
      exact heq.symm

/-- `Sz(2^(2n+1))` acts 2-transitively on the cosets of its Borel subgroup. -/
theorem szModel_isMultiplyPretransitive_two (n : ℕ) :
    MulAction.IsMultiplyPretransitive (SzModel n) ((SzModel n) ⧸ szBorelS n) 2 :=
  Commons.GroupTheory.GroupAction.coset_multiplyPretransitive_two_of_two_doubleCosets
    (szBorelS n) (szWgM n) (sz_cover n)

/-- The degree of the coset action: `|Sz : B| = q^2 + 1`. -/
theorem card_szBorelS_index (n : ℕ) :
    (szBorelS n).index = Nat.card (SzField n) ^ 2 + 1 := by
  have hcard : Nat.card ↥(szBorelS n) = Nat.card ↥(szBorel n) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szBorel_le_szModel n)).toEquiv
  have hprod : Nat.card ↥(szBorelS n) * (szBorelS n).index = Nat.card (SzModel n) :=
    Subgroup.card_mul_index _
  rw [hcard, card_szModel_eq_borel_mul n] at hprod
  haveI : Nonempty ↥(szBorel n) := ⟨1⟩
  exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(szBorel n))) hprod

/-- The number of cosets is `q^2 + 1`. -/
theorem card_quotient_szBorelS (n : ℕ) :
    Nat.card ((SzModel n) ⧸ szBorelS n) = Nat.card (SzField n) ^ 2 + 1 :=
  card_szBorelS_index n


/-- `2 ^ (k+1) + 1` is odd. -/
lemma odd_two_pow_add_one (k : ℕ) : Odd (2 ^ (k + 1) + 1) :=
  ⟨2 ^ k, by rw [pow_succ]; ring⟩

section SylowCount

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The Suzuki 2-group as a subgroup of `SzModel n`. -/
noncomputable def szTwoGroupS (n : ℕ) : Subgroup (SzModel n) :=
  (szTwoGroup n).subgroupOf (SzModel n)

lemma szTwoGroupS_isPGroup (n : ℕ) : IsPGroup 2 ↥(szTwoGroupS n) :=
  IsPGroup.of_equiv (isPGroup_szTwoGroup n)
    (Subgroup.subgroupOfEquivOfLe (szTwoGroup_le_szModel n)).symm

lemma card_szTwoGroupS (n : ℕ) : Nat.card ↥(szTwoGroupS n) = 2 ^ (4 * n + 2) := by
  rw [szTwoGroupS,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szTwoGroup_le_szModel n)).toEquiv,
    card_szTwoGroup_eq]

lemma szTwoGroupS_index (n : ℕ) :
    (szTwoGroupS n).index = (2 ^ (2 * n + 1) - 1) * (2 ^ (4 * n + 2) + 1) := by
  have hprod : Nat.card ↥(szTwoGroupS n) * (szTwoGroupS n).index = Nat.card (SzModel n) :=
    Subgroup.card_mul_index _
  rw [card_szTwoGroupS, card_szModel_final'] at hprod
  have h2 : 2 ^ (4 * n + 2) * (szTwoGroupS n).index =
      2 ^ (4 * n + 2) * ((2 ^ (2 * n + 1) - 1) * (2 ^ (4 * n + 2) + 1)) := by
    rw [hprod]; ring
  exact Nat.mul_left_cancel (pow_pos (by norm_num) _) h2

lemma not_dvd_index_szTwoGroupS (n : ℕ) : ¬ 2 ∣ (szTwoGroupS n).index := by
  rw [szTwoGroupS_index]
  exact fun h => Nat.not_even_iff_odd.mpr
    ((odd_two_pow_sub_one (2 * n + 1) (by omega)).mul
      (odd_two_pow_add_one (4 * n + 1))) (even_iff_two_dvd.mpr h)

/-- The normalizer of the Suzuki 2-group inside `SzModel n` is the Borel subgroup. -/
lemma normalizer_szTwoGroupS (n : ℕ) :
    Subgroup.normalizer ((szTwoGroupS n) : Set (SzModel n)) = szBorelS n := by
  rw [szTwoGroupS, szBorelS,
    Commons.GroupTheory.Subgroup.normalizer_subgroupOf (szTwoGroup n) (SzModel n)
      (szTwoGroup_le_szModel n),
    normalizer_szTwoGroup_inf_szModel]

/-- A Sylow 2-subgroup of `Sz(2^(2n+1))`: the Suzuki 2-group. -/
noncomputable def szSylow (n : ℕ) : Sylow 2 (SzModel n) :=
  (szTwoGroupS_isPGroup n).toSylow (not_dvd_index_szTwoGroupS n)

lemma szSylow_coe_sub (n : ℕ) :
    ((szSylow n : Sylow 2 (SzModel n)) : Subgroup (SzModel n)) = szTwoGroupS n := by
  rw [szSylow]
  exact IsPGroup.toSylow_coe (szTwoGroupS_isPGroup n) (not_dvd_index_szTwoGroupS n)

lemma szSylow_coe (n : ℕ) :
    ((szSylow n : Sylow 2 (SzModel n)) : Set (SzModel n)) = szTwoGroupS n := by
  rw [← Sylow.coe_coe, szSylow_coe_sub]

/-- The number of Sylow 2-subgroups of `Sz(2^(2n+1))` is `q^2 + 1`. -/
theorem card_sylow2_szModel (n : ℕ) :
    Nat.card (Sylow 2 (SzModel n)) = Nat.card (SzField n) ^ 2 + 1 := by
  rw [Sylow.card_eq_index_normalizer (szSylow n),
    show (↑(szSylow n) : Set (SzModel n)) = szTwoGroupS n from szSylow_coe n,
    normalizer_szTwoGroupS, card_szBorelS_index]

end SylowCount

end Submission.Sz
