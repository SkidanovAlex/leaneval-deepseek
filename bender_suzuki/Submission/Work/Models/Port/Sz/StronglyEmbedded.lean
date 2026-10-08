/-
The Borel subgroup of `Sz(2^(2n+1))` is strongly embedded.

For `g ∉ B`, the Bruhat decomposition gives `g ∈ B w B`, and then
`B ∩ B^g = (B ∩ w B w)^{b₁} = T^{b₁}` is conjugate to the torus `T`, of odd order `q - 1`.
Since `|B| = q^2 (q-1)` is even and `B ≠ Sz`, the Borel subgroup is strongly embedded.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.BNPair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-- `2^k - 1` is odd for `k ≥ 1`. -/
lemma odd_two_pow_sub_one (k : ℕ) (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  refine ⟨2 ^ j - 1, ?_⟩
  rw [pow_succ]
  have h : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

lemma odd_card_torus (n : ℕ) : Odd (Nat.card ↥(szTgHom n).range) := by
  rw [card_range_szTgHom, card_szField]
  exact odd_two_pow_sub_one (2 * n + 1) (by omega)

/-- For `g ∈ B w B`, the cardinality of `B ∩ B^g` equals the order of the torus. -/
lemma card_szBorel_inf_conj (n : ℕ) {g : GL (Fin 4) (SzField n)} (hg : g ∈ szBwB n) :
    Nat.card ↥(szBorel n ⊓ (szBorel n).map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥(szTgHom n).range := by
  obtain ⟨b, hb, heq⟩ := szBorel_inf_conj_eq_conj_torus n hg
  rw [heq]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective (szTgHom n).range
    (MulAut.conj b).toMonoidHom (MulEquiv.injective _)).toEquiv).symm

/-- The intersection of `M = B ≤ Sz` with its conjugate by `g ∉ M` is conjugate (inside `Sz`)
to the torus, hence has the same cardinality. -/
lemma card_subgroupOf_inf_map_conj (n : ℕ) (g : SzModel n)
    (hg : g ∉ (szBorel n).subgroupOf (SzModel n)) :
    Nat.card ↥((szBorel n).subgroupOf (SzModel n) ⊓
        ((szBorel n).subgroupOf (SzModel n)).map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥(szTgHom n).range := by
  have hconjGL : ∀ w : SzModel n,
      (SzModel n).subtype ((MulAut.conj g).toMonoidHom w) =
        (MulAut.conj (g : GL (Fin 4) (SzField n))).toMonoidHom
          (w : GL (Fin 4) (SzField n)) := by
    intro w
    simp [MulAut.conj_apply]
  have hsub : ((szBorel n).subgroupOf (SzModel n) ⊓
      ((szBorel n).subgroupOf (SzModel n)).map (MulAut.conj g).toMonoidHom).map
        (SzModel n).subtype =
      szBorel n ⊓ (szBorel n).map (MulAut.conj (g : GL (Fin 4) (SzField n))).toMonoidHom := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzM, hzMg⟩, rfl⟩
      refine ⟨hzM, ?_⟩
      obtain ⟨w, hwM, hwg⟩ := Subgroup.mem_map.mp hzMg
      refine ⟨(w : GL (Fin 4) (SzField n)), hwM, ?_⟩
      rw [← hwg, hconjGL w]
    · rintro ⟨hyB, y', hy'B, hy'eq⟩
      have hyS : y ∈ SzModel n := szBorel_le_szModel n hyB
      refine ⟨⟨y, hyS⟩, ⟨hyB, ?_⟩, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨y', szBorel_le_szModel n hy'B⟩, hy'B, by
        apply Subtype.ext
        show (SzModel n).subtype
          ((MulAut.conj g).toMonoidHom ⟨y', szBorel_le_szModel n hy'B⟩) = y
        rw [hconjGL ⟨y', szBorel_le_szModel n hy'B⟩]
        exact hy'eq⟩
  rw [← card_szBorel_inf_conj n (g := (g : GL (Fin 4) (SzField n))) ?_]
  · rw [← hsub]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ (SzModel n).subtype
      Subtype.coe_injective).toEquiv
  · have hcar : (SzModel n : Set (GL (Fin 4) (SzField n))) = szBwBSet n := by
        rw [szModel_eq_szBwBSubgroup' n]
        ext x
        rfl
    have hmem : (g : GL (Fin 4) (SzField n)) ∈ szBwBSet n :=
      le_of_eq hcar g.2
    rcases hmem with hmem | hmem
    · exact absurd (show g ∈ (szBorel n).subgroupOf (SzModel n) from hmem) hg
    · exact hmem

/-- The Borel subgroup of `Sz(2^(2n+1))` is strongly embedded in `Sz(2^(2n+1))`. -/
theorem szBorel_stronglyEmbedded (n : ℕ) (hn : 1 ≤ n) :
    IsStronglyEmbedded ((szBorel n).subgroupOf (SzModel n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact szWg_notMem_szBorel n (h (szWg_mem_szModel n))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szBorel_le_szModel n)).toEquiv,
      card_szBorel_eq]
    obtain ⟨k, hk⟩ := odd_two_pow_sub_one (2 * n + 1) (by omega)
    refine ⟨2 ^ (4 * n + 1) * (2 * k + 1), ?_⟩
    rw [hk, show 2 ^ (4 * n + 2) = 2 ^ (4 * n + 1) * 2 from by
      rw [show 4 * n + 2 = (4 * n + 1) + 1 from by ring, pow_succ]]
    ring
  · intro g hg
    rw [card_subgroupOf_inf_map_conj n g hg]
    exact odd_card_torus n

end Submission.Sz
