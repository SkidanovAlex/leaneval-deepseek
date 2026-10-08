/-
**The rank-`1` BN-pair skeleton of `Sz(2^(2n+1))`, re-derived from the abstract commons layer.**

The file `Submission/BenderAction.lean` proves the numerical Suzuki condition
`[G : B] = |U| + 1` for the three families by ad-hoc cardinal arithmetic.  Here we re-derive the
same facts for the Suzuki family *purely* from the general rank-`1` BN-pair framework that lives
in the shared commons:

* `Commons.GroupTheory.Subgroup.index_eq_one_add_card_of_doubleCoset_cover_of_notMem`
  (`B = U ⊔ T`, `U ⊓ T = ⊥`, `T ≤ N(U)`, `G = B ∪ B w B`, `B ⊓ B^w = T` ⟹ `[G : B] = |U| + 1`),
* `Commons.GroupTheory.DoubleCoset.inf_map_conj_eq_bot_of_doubleCoset_cover`
  (`U ⊓ B^g = ⊥` for `g ∉ B` when `T` has odd order),
* `Commons.GroupTheory.IsPGroup.not_dvd_index_of_eq_sup`
  (`U` is a Sylow `2`-subgroup of `G`),
* `Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add`
  (`U` acts regularly on the non-base points of the Bender action).

This demonstrates that the models really do satisfy the abstract hypotheses of Suzuki's
classification, with no model-specific input beyond the BN-pair data itself.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.Faithful
import Submission.Work.Models.Port.BenderAction
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.subgroupOf_inf_map_conj_eq
import Submission.Work.Models.Port.Commons.GroupTheory.DoubleCoset.inf_map_conj_eq_bot_of_doubleCoset_cover
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.index_eq_one_add_card_of_doubleCoset_cover_of_notMem
import Submission.Work.Models.Port.Commons.GroupTheory.IsPGroup.not_dvd_index_of_eq_sup
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add

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

/-- The maximal torus `T` of `Sz(2^(2n+1))` as a subgroup of `SzModel n`. -/
noncomputable abbrev szTS (n : ℕ) : Subgroup (SzModel n) :=
  (szTgHom n).range.subgroupOf (SzModel n)

lemma szTwoGroupS_le_szBorelS (n : ℕ) : szTwoGroupS n ≤ szBorelS n :=
  Subgroup.subgroupOf_mono (SzModel n) (by rw [szBorel]; exact le_sup_left)

/-- `B = U ⊔ T` inside `SzModel n`. -/
lemma szBorelS_eq_sup (n : ℕ) : szBorelS n = szTwoGroupS n ⊔ szTS n := by
  rw [szBorelS, szTwoGroupS, szTS, szBorel,
    Subgroup.subgroupOf_sup (szTwoGroup_le_szModel n) (szTgHom_range_le_szModel n)]

/-- `U ⊓ T = ⊥` inside `SzModel n`. -/
lemma szTS_inf_szTwoGroupS (n : ℕ) : szTwoGroupS n ⊓ szTS n = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxU, hxT⟩ := Subgroup.mem_inf.mp hx
  have hxU' : (x : GL (Fin 4) (SzField n)) ∈ szTwoGroup n := Subgroup.mem_subgroupOf.mp hxU
  have hxT' : (x : GL (Fin 4) (SzField n)) ∈ (szTgHom n).range := Subgroup.mem_subgroupOf.mp hxT
  refine Subtype.ext ?_
  have h1 : (x : GL (Fin 4) (SzField n)) ∈ (⊥ : Subgroup (GL (Fin 4) (SzField n))) := by
    rw [← szTwoGroup_inf_range_szTgHom n]
    exact ⟨hxU', hxT'⟩
  simpa using h1

/-- The torus of `Sz(2^(2n+1))` normalizes the Suzuki `2`-group inside `SzModel n`. -/
lemma szTS_le_normalizer_szTwoGroupS (n : ℕ) :
    szTS n ≤ Subgroup.normalizer (szTwoGroupS n : Set (SzModel n)) := by
  rw [Subgroup.le_normalizer_iff]
  intro t ht y hy
  have ht' : (t : GL (Fin 4) (SzField n)) ∈ (szTgHom n).range := Subgroup.mem_subgroupOf.mp ht
  have hy' : (y : GL (Fin 4) (SzField n)) ∈ szTwoGroup n := Subgroup.mem_subgroupOf.mp hy
  have hconj : (t : GL (Fin 4) (SzField n)) * (y : GL (Fin 4) (SzField n)) *
      (t : GL (Fin 4) (SzField n))⁻¹ ∈ szTwoGroup n :=
    (Subgroup.le_normalizer_iff.mp (szTgHom_range_le_normalizer n)) t ht' y hy'
  have hcoe : (((t * y * t⁻¹ : ↥(SzModel n))) : GL (Fin 4) (SzField n)) =
      (t : GL (Fin 4) (SzField n)) * (y : GL (Fin 4) (SzField n)) *
        (t : GL (Fin 4) (SzField n))⁻¹ := by
    simp
  change (((t * y * t⁻¹ : ↥(SzModel n))) : GL (Fin 4) (SzField n)) ∈ szTwoGroup n
  rw [hcoe]
  exact hconj

/-- The BN-pair intersection `B ⊓ B^w` inside `SzModel n` is the torus. -/
lemma szBorelS_inf_map_conj_eq (n : ℕ) :
    szBorelS n ⊓ (szBorelS n).map (MulAut.conj (szWgM n)).toMonoidHom = szTS n := by
  have hw : ((szWgM n : ↥(SzModel n)) : GL (Fin 4) (SzField n)) = szWg n := rfl
  rw [szBorelS, Commons.GroupTheory.Subgroup.subgroupOf_inf_map_conj_eq (szBorel n) (SzModel n)
    (szBorel_le_szModel n) (szWgM n), szTS, hw]
  exact congrArg (fun H => H.subgroupOf (SzModel n)) (szBorel_inf_conj_szBorel_eq_torus n)

/-- **The Suzuki condition** `[Sz : B] = |U| + 1`, derived from the abstract rank-`1` BN-pair
theory in the commons. -/
theorem szBorelS_index_eq_one_add (n : ℕ) :
    (szBorelS n).index = 1 + Nat.card ↥(szTwoGroupS n) :=
  Commons.GroupTheory.Subgroup.index_eq_one_add_card_of_doubleCoset_cover_of_notMem
    (szTwoGroupS n) (szTS n) (szBorelS n) (szWgM n)
    (szBorelS_eq_sup n) (szTS_inf_szTwoGroupS n) (szTS_le_normalizer_szTwoGroupS n)
    (sz_cover n) (szWgM_notMem n) (by rw [szBorelS_inf_map_conj_eq n])

/-- `U` meets the conjugate `B^g` trivially for every `g ∉ B`: the rank-`1` BN-pair
"trivial intersection" property. -/
theorem szTwoGroupS_inf_map_conj_eq_bot (n : ℕ) {g : SzModel n} (hg : g ∉ szBorelS n) :
    szTwoGroupS n ⊓ (szBorelS n).map (MulAut.conj g).toMonoidHom = ⊥ :=
  Commons.GroupTheory.DoubleCoset.inf_map_conj_eq_bot_of_doubleCoset_cover
    (szTS n) (szBorelS n) (szWgM n) (sz_cover n) (szBorelS_inf_map_conj_eq n)
    (szTwoGroupS_le_szBorelS n) (szTwoGroupS_isPGroup n)
    (by
      rw [szTS,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szTgHom_range_le_szModel n)).toEquiv]
      exact odd_card_torus n)
    hg

/-- The Suzuki `2`-group is a Sylow `2`-subgroup of `Sz(2^(2n+1))`, via the abstract
rank-`1` BN-pair lemma `IsPGroup.not_dvd_index_of_eq_sup`. -/
theorem not_dvd_index_szTwoGroupS_commons (n : ℕ) : ¬ 2 ∣ (szTwoGroupS n).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : ¬ 2 ∣ Nat.card ↥(szTS n) := by
    rw [szTS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szTgHom_range_le_szModel n)).toEquiv,
      card_range_szTgHom, card_szField]
    intro h
    exact Nat.not_even_iff_odd.mpr (odd_two_pow_sub_one (2 * n + 1) (by omega))
      (even_iff_two_dvd.mpr h)
  have hB : ¬ 2 ∣ (szBorelS n).index := by
    rw [card_szBorelS_index, card_szField, ← pow_mul,
      show (2 * n + 1) * 2 = 4 * n + 2 from by ring]
    intro h
    exact Nat.not_even_iff_odd.mpr (odd_two_pow_add_one (4 * n + 1)) (even_iff_two_dvd.mpr h)
  exact Commons.GroupTheory.IsPGroup.not_dvd_index_of_eq_sup (p := 2) (szTwoGroupS n) (szTS n)
    (szBorelS n) (szBorelS_eq_sup n) (szTS_inf_szTwoGroupS n)
    (szTS_le_normalizer_szTwoGroupS n) (szTwoGroupS_isPGroup n) hT hB

/-- **`U` acts regularly on the non-base points of the Bender action.**  The Suzuki condition
plus the free action off the base point (a consequence of the Bender action axioms) says that
`U` is sharply transitive on `Ω ∖ {base}`: the Frobenius structure of the Borel subgroup. -/
theorem szTwoGroupS_exists_smul_eq_of_ne (n : ℕ) (hn : 1 ≤ n)
    {x y : SzModel n ⧸ szBorelS n}
    (hx : x ≠ ((1 : SzModel n) : SzModel n ⧸ szBorelS n))
    (hy : y ≠ ((1 : SzModel n) : SzModel n ⧸ szBorelS n)) :
    ∃ u : ↥(szTwoGroupS n), (u : SzModel n) • x = y := by
  refine Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add
    (U := szTwoGroupS n) (((1 : SzModel n) : SzModel n ⧸ szBorelS n)) ?_ ?_ ?_ hx hy
  · show (szBorelS n).index = Nat.card ↥(szTwoGroupS n) + 1
    rw [szBorelS_index_eq_one_add n, Nat.add_comm]
  · intro u
    rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
    exact szTwoGroupS_le_szBorelS n u.2
  · intro u hu x hx
    exact szTwoGroupS_fixedPoint_eq_one n hn u hu hx

end Submission.Sz
