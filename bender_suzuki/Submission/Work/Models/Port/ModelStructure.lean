/-
**The `2`-local structure of the three Bender families: `N(U) = B` and involution fusion.**

For each of the three families `PSL(2,2ⁿ)`, `Sz(2^(2n+1))`, `PSU(3,2ⁿ)` the Borel subgroup `B`
is the *normalizer of the unipotent radical* `U = O₂(B)`.  This is the point where the abstract
Bender theory (`Commons.GroupTheory.StronglyEmbedded.normalizer_le_of_isPGroup_le`) meets the
models: a non-trivial `2`-subgroup of a strongly embedded subgroup has normalizer inside it, so
`N(U) ≤ B`, while `U ⊴ B` gives the reverse inclusion.

We also transfer the fusion of involutions from `SU(3,2ⁿ)` to the quotient `PSU(3,2ⁿ)`.  The
projection `SU(3,2ⁿ) → PSU(3,2ⁿ)` has an odd kernel (of order `gcd(3, q+1)`), so every involution
of `PSU(3,2ⁿ)` lifts to an involution of `SU(3,2ⁿ)`; since all involutions of `SU(3,2ⁿ)` are
conjugate (`Submission.PSU3.su3_involutions_conj`), the same holds in the quotient.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Main
import Submission.Work.Models.Port.PSU3.Simple
import Submission.Work.Models.Port.PSU3.SuzukiCondition
import Submission.Work.Models.Port.PSU3.Involutions
import Submission.Work.Models.Port.PSU3.InvolutionsConj
import Submission.Work.Models.Port.Sz.Main
import Submission.Work.Models.Port.SuzukiSetup
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.Port.Sz.Involutions
import Submission.Work.Models.Port.PSL2Torus
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.normalizer_le_of_isPGroup_le
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.exists_sylow_two_elementaryAbelian_projectiveSpecialLinearGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped LinearAlgebra.Projectivization

/-! ## `Sz(2^(2n+1))` -/

namespace Submission.Sz

/-- **The Borel subgroup of `Sz(2^(2n+1))` is the normalizer of the Suzuki `2`-group `U`.** -/
theorem szBorelS_eq_normalizer (n : ℕ) (hn : 1 ≤ n) :
    Subgroup.normalizer (szTwoGroupS n : Set (SzModel n)) = szBorelS n := by
  obtain ⟨-, -, hodd⟩ := szBorel_stronglyEmbedded n hn
  have hUne : szTwoGroupS n ≠ ⊥ := by
    intro h
    have hc := card_szTwoGroupS n
    rw [h, Subgroup.card_bot] at hc
    have h1 : 1 < 2 ^ (4 * n + 2) := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  exact le_antisymm
    (Commons.GroupTheory.StronglyEmbedded.normalizer_le_of_isPGroup_le (szBorelS n) hodd
      (szTwoGroupS_isPGroup n) (szTwoGroupS_le_szBorelS n) hUne)
    (szBorelS_le_normalizer_szTwoGroupS n)

end Submission.Sz

/-! ## `PSU(3, 2ⁿ)` -/

namespace Submission.PSU3

/-- **The Borel subgroup of `PSU(3,2ⁿ)` is the normalizer of the unipotent radical `U`.** -/
theorem psu3B_eq_normalizer (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.normalizer (psu3U n : Set (PSU3Model n)) = psu3B n := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, -, hodd⟩ := psu3B_stronglyEmbedded n hn
  have hUne : psu3U n ≠ ⊥ := by
    intro h
    have hc : Nat.card ↥(psu3U n) = 2 ^ (3 * n) :=
      (Submission.card_psu3U n hn).trans (card_suUS n hn1)
    rw [h, Subgroup.card_bot] at hc
    have h1 : 1 < 2 ^ (3 * n) := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hle : psu3B n ≤ Subgroup.normalizer (psu3U n : Set (PSU3Model n)) :=
    (Subgroup.map_mono (suUS_le_normalizer_suUS_self n hn1)).trans
      (Subgroup.le_normalizer_map (psu3Hom n))
  exact le_antisymm
    (Commons.GroupTheory.StronglyEmbedded.normalizer_le_of_isPGroup_le (psu3B n) hodd
      (isPGroup_psu3U n hn1) (psu3U_le_psu3B n) hUne)
    hle

end Submission.PSU3

/-! ## `PSL(2, 2ⁿ)` -/

namespace Submission.PSL2

open Commons.GroupTheory.SL2

/-- **The Borel subgroup of `PSL(2,2ⁿ)` is the normalizer of the unipotent subgroup `U`.** -/
theorem pSL2Stabilizer_eq_normalizer_unipotent (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.normalizer ((unipotentPSLHom (GaloisField 2 n)).range :
        Set (PSL2Model n)) =
      MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n)) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  have hcard : 2 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card (p := 2) (n := n) (by omega)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinj : Function.Injective (unipotentPSLHom (GaloisField 2 n)) :=
    unipotentPSLHom_injective (K := GaloisField 2 n) hchar
  have hcardU : Nat.card ↥((unipotentPSLHom (GaloisField 2 n)).range) =
      Nat.card (GaloisField 2 n) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      ← Nat.card_congr Multiplicative.ofAdd]
  obtain ⟨-, -, hodd⟩ :=
    Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup
      (K := GaloisField 2 n) hchar hcard (pt0 (GaloisField 2 n))
  have hU2 : IsPGroup 2 ↥((unipotentPSLHom (GaloisField 2 n)).range) :=
    IsPGroup.of_card (n := n)
      (hcardU.trans (GaloisField.card (p := 2) (n := n) (by omega)))
  have hUne : (unipotentPSLHom (GaloisField 2 n)).range ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardU
    have h1 : 1 < Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card (p := 2) (n := n) (by omega)]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    omega
  refine le_antisymm ?_ ?_
  · exact Commons.GroupTheory.StronglyEmbedded.normalizer_le_of_isPGroup_le
      (MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n))) hodd hU2
      (unipotent_range_le_stabilizer_pt0 (K := GaloisField 2 n)) hUne
  · rw [← unipotent_sup_diag_eq_stabilizer_pt0 (K := GaloisField 2 n)]
    exact sup_le Subgroup.le_normalizer
      (diag_range_le_normalizer_unipotent (K := GaloisField 2 n))

end Submission.PSL2

/-! ## Fusion of involutions in `PSU(3, 2ⁿ)` -/

namespace Submission.PSU3

/-- Every involution of `PSU(3,2ⁿ)` lifts to an involution of `SU(3,2ⁿ)`: the kernel of the
projection has odd order, so a suitable odd power of a preimage is an involution. -/
lemma psu3_exists_lift_involution (n : ℕ) (hn : 1 ≤ n) {h : PSU3Model n}
    (hh : orderOf h = 2) : ∃ g : ↥(SU3 n), orderOf g = 2 ∧ psu3Hom n g = h := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := psu3Hom_surjective n h
  have hh2 : h ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one h
    rwa [hh] at h1
  have hh1 : h ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hh
    omega
  have hx2ker : x ^ 2 ∈ (psu3Hom n).ker := by
    rw [MonoidHom.mem_ker, map_pow, hx, hh2]
  have hk : (x ^ 2) ^ Nat.card (psu3Hom n).ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      (Subgroup.orderOf_dvd_natCard (psu3Hom n).ker hx2ker)
  have hodd : Odd (Nat.card (psu3Hom n).ker) := odd_card_psu3Hom_ker n hn
  refine ⟨x ^ Nat.card (psu3Hom n).ker, ?_, ?_⟩
  · have hg2 : (x ^ Nat.card (psu3Hom n).ker) ^ 2 = 1 := by
      rw [← pow_mul,
        show Nat.card (psu3Hom n).ker * 2 = 2 * Nat.card (psu3Hom n).ker by ring, pow_mul]
      exact hk
    have hg1 : x ^ Nat.card (psu3Hom n).ker ≠ 1 := by
      intro h1
      have h2 : h ^ Nat.card (psu3Hom n).ker = 1 := by
        rw [← hx, ← map_pow, h1, map_one]
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hh2, one_pow, one_mul] at h2
      exact hh1 h2
    exact orderOf_eq_prime (p := 2) hg2 hg1
  · have h2 : h ^ Nat.card (psu3Hom n).ker = h := by
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hh2, one_pow, one_mul]
    rw [map_pow, hx]; exact h2

/-- **All involutions of `PSU(3,2ⁿ)` are conjugate.**  They lift to involutions of
`SU(3,2ⁿ)` (`psu3_exists_lift_involution`), where the result is
`Submission.PSU3.su3_involutions_conj`. -/
theorem psu3Model_involutions_conj (n : ℕ) (hn : 2 ≤ n) (t s : PSU3Model n)
    (ht : orderOf t = 2) (hs : orderOf s = 2) :
    ∃ z : PSU3Model n, z * t * z⁻¹ = s := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨t₀, ht₀, hφt⟩ := psu3_exists_lift_involution n hn1 ht
  obtain ⟨s₀, hs₀, hφs⟩ := psu3_exists_lift_involution n hn1 hs
  obtain ⟨z, hz⟩ := su3_involutions_conj n hn1 t₀ s₀ ht₀ hs₀
  refine ⟨psu3Hom n z, ?_⟩
  rw [← hφt, ← hφs, ← hz, map_mul, map_mul, map_inv]

/-- The involutions of `PSU(3,2ⁿ)` form a single conjugacy class. -/
theorem psu3Model_involutions_single_class (n : ℕ) (hn : 2 ≤ n) {t s : PSU3Model n}
    (ht : orderOf t = 2) (hs : orderOf s = 2) : IsConj t s :=
  isConj_iff.mpr (psu3Model_involutions_conj n hn t s ht hs)

end Submission.PSU3
