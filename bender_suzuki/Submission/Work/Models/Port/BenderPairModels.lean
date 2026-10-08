/-
**The three families as abstract rank-one `(B,N)`-pairs.**

`Submission/BenderSetup.lean` introduces the structure `Submission.BenderPair` (~the data produced
by Bender's theorem for a finite group with a strongly embedded subgroup) and derives the standard
structural theory from the axioms.  Here we verify that the axioms are satisfied by
`Sz(2^(2n+1))`, `PSU(3,2ⁿ)` and `PSL(2,2ⁿ)`, by assembling the lemmas proved in
`Submission/Sz/`, `Submission/PSU3/` and `Submission/PSL2Torus.lean`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.Port.Sz.Weyl
import Submission.Work.Models.Port.Sz.StronglyEmbedded
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.PSU3.BNPairQuotient
import Submission.Work.Models.Port.PSU3.StronglyEmbedded
import Submission.Work.Models.Port.PSU3.SuzukiCondition
import Submission.Work.Models.Port.PSU3SylowConj
import Submission.Work.Models.Port.PSL2Torus
import Submission.Work.Models.Port.SuzukiSetup
import Submission.Work.Models.Port.TISylow
import Submission.Work.Models.Port.SzSylowConj
import Submission.Work.Models.Port.PSL2SylowConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise LinearAlgebra.Projectivization

namespace Submission.Sz

open Submission (BenderPair)

/-- **`Sz(2^(2n+1))` carries a rank-one `(B,N)`-pair.** -/
noncomputable def szBenderPair (n : ℕ) (hn : 1 ≤ n) : BenderPair (SzModel n) where
  B := szBorelS n
  U := szTwoGroupS n
  T := szTS n
  w := szWgM n
  hSemb := szBorel_stronglyEmbedded n hn
  hU2 := szTwoGroupS_isPGroup n
  hUne := by
    intro h
    have hc := card_szTwoGroupS n
    rw [h, Subgroup.card_bot] at hc
    have h1 : 1 < 2 ^ (4 * n + 2) := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  hoddT := by
    rw [szTS,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szTgHom_range_le_szModel n)).toEquiv]
    exact odd_card_torus n
  hB := szBorelS_eq_sup n
  hUT := szTS_inf_szTwoGroupS n
  hTnU := szTS_le_normalizer_szTwoGroupS n
  hwB := szWgM_notMem_szBorelS n
  hwT := szWgM_mem_normalizer_szTS n
  hCU := fun u hu hcent => eq_one_of_mem_szTwoGroupS_of_centralizes_szTS n hn hu hcent
  hindex := by rw [szBorelS_index_eq_one_add n, Nat.add_comm]

end Submission.Sz

namespace Submission.PSU3

open Submission (BenderPair)

/-- **`PSU(3,2ⁿ)` carries a rank-one `(B,N)`-pair.** -/
noncomputable def psu3BenderPair (n : ℕ) (hn : 2 ≤ n) : BenderPair (PSU3Model n) where
  B := psu3B n
  U := psu3U n
  T := psu3T n
  w := psu3Weyl n
  hSemb := psu3B_stronglyEmbedded n hn
  hU2 := isPGroup_psu3U n (by omega)
  hUne := by
    intro h
    have hc : Nat.card ↥(psu3U n) = 2 ^ (3 * n) :=
      (card_psu3U n hn).trans (card_suUS n (by omega))
    rw [h, Subgroup.card_bot] at hc
    have h1 : 1 < 2 ^ (3 * n) := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  hoddT := by
    have hdiv : Nat.card ↥(psu3T n) ∣ Nat.card ↥(suTS n) := by
      have h := Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker (psu3Hom n)
        (psu3Hom_surjective n) (suTS n)
      exact ⟨Nat.card ↥(suTS n ⊓ (psu3Hom n).ker), h.symm⟩
    have hodd : Odd (Nat.card ↥(suTS n)) := by
      rw [suTS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suT_le_SU3 n)).toEquiv,
        card_suT n (by omega)]
      exact odd_two_pow_sub_one (2 * n) (by omega)
    exact hodd.of_dvd_nat hdiv
  hB := psu3B_eq_sup_psu3T n
  hUT := psu3U_inf_psu3T n
  hTnU := psu3T_le_normalizer_psu3U n
  hwB := psu3W_notMem_psu3B n
  hwT := psu3W_mem_normalizer_psu3T n
  hCU := fun u hu hcent => centralizer_psu3U_psu3T n hn hu hcent
  hindex := by rw [psu3B_index_eq_one_add_card_psu3U n hn, Nat.add_comm]

end Submission.PSU3

namespace Submission.PSL2

open Commons.GroupTheory.SL2

/-- The unipotent subgroup of `PSL(2,2ⁿ)` has `2ⁿ` elements. -/
lemma card_unipotentPSLHom_range (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥((unipotentPSLHom (GaloisField 2 n)).range) = 2 ^ n := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  rw [← Nat.card_congr
      (MonoidHom.ofInjective (unipotentPSLHom_injective (K := GaloisField 2 n) hchar)).toEquiv,
    ← Nat.card_congr Multiplicative.ofAdd,
    GaloisField.card (p := 2) (n := n) (by omega)]

/-- **`PSL(2,2ⁿ)` carries a rank-one `(B,N)`-pair.** -/
noncomputable def pSL2BenderPair (n : ℕ) (hn : 2 ≤ n) : BenderPair (PSL2Model n) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  exact
{ B := MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n))
  U := (unipotentPSLHom (GaloisField 2 n)).range
  T := (diagPSLHom (GaloisField 2 n)).range
  w := weylPSL (GaloisField 2 n)
  hSemb := by
    have hchar : CharP (GaloisField 2 n) 2 := inferInstance
    have hcard : 2 ≤ Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card (p := 2) (n := n) (by omega)]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup
      (K := GaloisField 2 n) hchar hcard (pt0 (GaloisField 2 n))
  hU2 := isPGroup_unipotent_range n (by omega)
  hUne := by
    intro h
    have hc := card_unipotentPSLHom_range n (by omega)
    rw [h, Subgroup.card_bot] at hc
    have h1 : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  hoddT := by
    have hchar : CharP (GaloisField 2 n) 2 := inferInstance
    rw [card_diagPSLHom_range (K := GaloisField 2 n),
      GaloisField.card (p := 2) (n := n) (by omega)]
    exact Commons.Nat.odd_two_pow_sub_one n (by omega)
  hB := (unipotent_sup_diag_eq_stabilizer_pt0 (K := GaloisField 2 n)).symm
  hUT := unipotent_inf_diag_eq_bot (K := GaloisField 2 n)
  hTnU := diag_range_le_normalizer_unipotent (K := GaloisField 2 n)
  hwB := weylPSL_not_mem_stabilizer_pt0 (K := GaloisField 2 n)
  hwT := weylPSL_mem_normalizer_diagPSLHom (K := GaloisField 2 n)
  hCU := by
    have hchar : CharP (GaloisField 2 n) 2 := inferInstance
    intro u hu hcent
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hu
    have hofw : w = Multiplicative.ofAdd (Multiplicative.toAdd w) :=
      (Equiv.apply_symm_apply Multiplicative.ofAdd w).symm
    rcases eq_or_ne (Multiplicative.toAdd w) 0 with hc | hc
    · rw [hofw, hc]
      exact map_one _
    · exfalso
      haveI : Fintype (GaloisField 2 n)ˣ := Fintype.ofFinite _
      have hcardK : 1 < Fintype.card (GaloisField 2 n)ˣ := by
        rw [← Nat.card_eq_fintype_card, Nat.card_units (GaloisField 2 n),
          GaloisField.card (p := 2) (n := n) (by omega)]
        have h3 : 3 ≤ 2 ^ n := by
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
      obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card hcardK (1 : (GaloisField 2 n)ˣ)
      have hta1 : diagPSLHom (GaloisField 2 n) a ≠ 1 := by
        intro h
        exact ha ((diagPSLHom_injective (K := GaloisField 2 n) hchar) (by rw [h, map_one]))
      have hmem : diagPSLHom (GaloisField 2 n) a ∈
          Subgroup.centralizer
            (singleton (unipotentPSLHom (GaloisField 2 n)
              (Multiplicative.ofAdd (Multiplicative.toAdd w))) : Set (PSL2Model n)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcent _ (MonoidHom.mem_range.mpr ⟨a, rfl⟩)).symm
      rw [centralizer_unipotentPSLHom_eq_range (K := GaloisField 2 n) hc] at hmem
      have hmem2 : diagPSLHom (GaloisField 2 n) a ∈
          (unipotentPSLHom (GaloisField 2 n)).range ⊓ (diagPSLHom (GaloisField 2 n)).range :=
        ⟨hmem, ⟨a, rfl⟩⟩
      rw [unipotent_inf_diag_eq_bot (K := GaloisField 2 n), Subgroup.mem_bot] at hmem2
      exact hta1 hmem2
  hindex := by
    rw [Submission.pSL2Stabilizer_index_eq_one_add_sylowTwo n (by omega)
        (pt0 (GaloisField 2 n)),
      card_unipotentPSLHom_range n (by omega), Nat.add_comm]
}

end Submission.PSL2

/-! ## Cross-validation: the abstract order formula reproduces the known orders

`BenderPair.card_eq_card_U_mul_card_T_mul_succ` says `|G| = |U| · |T| · (|U| + 1)` for any
Bender group.  Substituting the cardinalities of `U` and `T` verified above recovers the orders
`q(q-1)(q+1)`, `q²(q-1)(q²+1)` and `q³(q²-1)(q³+1)/gcd(3,q+1)` of `PSL(2,2ⁿ)`, `Sz(2^(2n+1))` and
`PSU(3,2ⁿ)` established in `Submission/PSL2Torus.lean`, `Submission/Sz/Main.lean` and
`Submission/PSU3/PSU3Order.lean`. -/

namespace Submission.Sz

/-- The order of `Sz(2^(2n+1))` from the rank-one `(B,N)`-pair: `|U|(|U|+1)|T|`. -/
theorem szModel_card_eq_bnpair (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (SzModel n) =
      2 ^ (4 * n + 2) * (2 ^ (2 * n + 1) - 1) * (2 ^ (4 * n + 2) + 1) := by
  have h := (szBenderPair n hn).card_eq_card_U_mul_card_T_mul_succ
  have hU : Nat.card ↥((szBenderPair n hn).U) = 2 ^ (4 * n + 2) := card_szTwoGroupS n
  have hT : Nat.card ↥((szBenderPair n hn).T) = 2 ^ (2 * n + 1) - 1 := by
    show Nat.card ↥(szTS n) = _
    rw [szTS,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szTgHom_range_le_szModel n)).toEquiv,
      card_range_szTgHom, card_szField]
  rw [hU, hT] at h
  exact h

end Submission.Sz

namespace Submission.PSL2

/-- The order of `PSL(2,2ⁿ)` from the rank-one `(B,N)`-pair: `|U|(|U|+1)|T|`. -/
theorem pSL2Model_card_eq_bnpair (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (PSL2Model n) = 2 ^ n * (2 ^ n - 1) * (2 ^ n + 1) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have h := (pSL2BenderPair n hn).card_eq_card_U_mul_card_T_mul_succ
  have hU : Nat.card ↥((pSL2BenderPair n hn).U) = 2 ^ n :=
    card_unipotentPSLHom_range n (by omega)
  have hT : Nat.card ↥((pSL2BenderPair n hn).T) = 2 ^ n - 1 := by
    show Nat.card ↥((diagPSLHom (GaloisField 2 n)).range) = _
    rw [card_diagPSLHom_range (K := GaloisField 2 n),
      GaloisField.card (p := 2) (n := n) (by omega)]
  rw [hU, hT] at h
  exact h

end Submission.PSL2

namespace Submission.PSU3

/-- The order of `PSU(3,2ⁿ)` from the rank-one `(B,N)`-pair: `|U|(|U|+1)|T|`, with the odd part
`|T| · gcd(3, q+1) = q² - 1` of the torus. -/
theorem psu3Model_card_eq_bnpair (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (PSU3Model n) * Nat.gcd 3 (2 ^ n + 1) =
      2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by
  have h := (psu3BenderPair n hn).card_eq_card_U_mul_card_T_mul_succ
  have hU : Nat.card ↥((psu3BenderPair n hn).U) = 2 ^ (3 * n) :=
    (card_psu3U n hn).trans (card_suUS n (by omega))
  have hT : Nat.card ↥((psu3BenderPair n hn).T) * Nat.gcd 3 (2 ^ n + 1) = 2 ^ (2 * n) - 1 := by
    show Nat.card ↥((suTS n).map (psu3Hom n)) * Nat.gcd 3 (2 ^ n + 1) = _
    have hker : suTS n ⊓ (psu3Hom n).ker = (psu3Hom n).ker :=
      inf_eq_right.mpr (psu3Hom_ker_le_suTS n)
    have h1 := Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker (psu3Hom n)
      (psu3Hom_surjective n) (suTS n)
    rw [hker, card_psu3Hom_ker n (by omega)] at h1
    have h2 : Nat.card ↥(suTS n) = 2 ^ (2 * n) - 1 := by
      rw [suTS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suT_le_SU3 n)).toEquiv,
        card_suT n (by omega)]
    rw [h2] at h1
    exact h1
  calc Nat.card (PSU3Model n) * Nat.gcd 3 (2 ^ n + 1)
      = Nat.card ↥((psu3BenderPair n hn).U) * Nat.card ↥((psu3BenderPair n hn).T) *
          (Nat.card ↥((psu3BenderPair n hn).U) + 1) * Nat.gcd 3 (2 ^ n + 1) := by rw [h]
    _ = Nat.card ↥((psu3BenderPair n hn).U) * (Nat.card ↥((psu3BenderPair n hn).T) *
          Nat.gcd 3 (2 ^ n + 1)) * (Nat.card ↥((psu3BenderPair n hn).U) + 1) := by ring
    _ = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by rw [hU, hT]

end Submission.PSU3

/-! ## The models realise the hypothesis and the conclusion of `BenderStructure`

For each of the three families the Borel subgroup is strongly embedded and is the normalizer of a
Sylow `2`-subgroup (its unipotent radical), and a `BenderPair` with that Borel subgroup exists;
this is exactly the situation to which `Submission.BenderStructure` (Bender's structural theorem,
`Submission/BenderReduction.lean`) applies. -/

namespace Submission.Sz

theorem szBorel_eq_normalizer_sylow (n : ℕ) (hn : 1 ≤ n) :
    ∃ S : Sylow 2 (SzModel n), (S : Subgroup (SzModel n)) = szTwoGroupS n ∧
      Subgroup.normalizer ((S : Subgroup (SzModel n)) : Set (SzModel n)) = szBorelS n := by
  obtain ⟨S, hS⟩ := (szBenderPair n hn).exists_sylow_eq_U
  exact ⟨S, hS, by rw [hS]; exact (szBenderPair n hn).normalizer_U⟩

theorem szBenderStructure_realised (n : ℕ) (hn : 1 ≤ n) :
    ∃ P : BenderPair (SzModel n), P.B = szBorelS n := ⟨szBenderPair n hn, rfl⟩

end Submission.Sz

namespace Submission.PSU3

theorem psu3B_eq_normalizer_sylow (n : ℕ) (hn : 2 ≤ n) :
    ∃ S : Sylow 2 (PSU3Model n), (S : Subgroup (PSU3Model n)) = psu3U n ∧
      Subgroup.normalizer ((S : Subgroup (PSU3Model n)) : Set (PSU3Model n)) = psu3B n := by
  obtain ⟨S, hS⟩ := (psu3BenderPair n hn).exists_sylow_eq_U
  exact ⟨S, hS, by rw [hS]; exact (psu3BenderPair n hn).normalizer_U⟩

theorem psu3BenderStructure_realised (n : ℕ) (hn : 2 ≤ n) :
    ∃ P : BenderPair (PSU3Model n), P.B = psu3B n := ⟨psu3BenderPair n hn, rfl⟩

end Submission.PSU3

namespace Submission.PSL2

open Commons.GroupTheory.SL2

theorem pSL2Stabilizer_eq_normalizer_sylow (n : ℕ) (hn : 2 ≤ n) :
    ∃ S : Sylow 2 (PSL2Model n),
      (S : Subgroup (PSL2Model n)) = (unipotentPSLHom (GaloisField 2 n)).range ∧
      Subgroup.normalizer ((S : Subgroup (PSL2Model n)) : Set (PSL2Model n)) =
        MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n)) := by
  obtain ⟨S, hS⟩ := (pSL2BenderPair n hn).exists_sylow_eq_U
  exact ⟨S, hS, by rw [hS]; exact (pSL2BenderPair n hn).normalizer_U⟩

theorem pSL2BenderStructure_realised (n : ℕ) (hn : 2 ≤ n) :
    ∃ P : BenderPair (PSL2Model n),
      P.B = MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n)) :=
  ⟨pSL2BenderPair n hn, rfl⟩

end Submission.PSL2

/-! ## Every strongly embedded subgroup is the Borel subgroup of some `BenderPair`

Combining `BenderPair.conj` with the classification of the strongly embedded subgroups of the three
families (`*StronglyEmbedded_eq_sylow_normalizer`) shows that the *whole* hypothesis and
conclusion of `Submission.BenderStructure` is realised in the models: a strongly embedded subgroup
of `Sz(2^(2n+1))`, `PSU(3,2ⁿ)` or `PSL(2,2ⁿ)` is the Borel subgroup of a rank-one `(B,N)`-pair. -/

namespace Submission.Sz

theorem szStronglyEmbedded_eq_benderPair_borel (n : ℕ) (hn : 1 ≤ n) (M : Subgroup (SzModel n))
    (hM : IsStronglyEmbedded M) :
    ∃ g : SzModel n, M = ((szBenderPair n hn).conj g).B := by
  obtain ⟨T, hT⟩ := szStronglyEmbedded_eq_sylow_normalizer n hn M hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : MulAction.IsPretransitive (SzModel n) (Sylow 2 (SzModel n)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := SzModel n) (szSylow n) T
  refine ⟨g, ?_⟩
  have hcoe : (T : Subgroup (SzModel n)) = (szTwoGroupS n).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def]
    rfl
  rw [hT, hcoe, Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj,
    szBorelS_eq_normalizer n hn]
  rfl

end Submission.Sz

namespace Submission.PSU3

theorem psu3StronglyEmbedded_eq_benderPair_borel (n : ℕ) (hn : 2 ≤ n)
    (M : Subgroup (PSU3Model n)) (hM : IsStronglyEmbedded M) :
    ∃ g : PSU3Model n, M = ((psu3BenderPair n hn).conj g).B := by
  obtain ⟨T, hT⟩ := psu3StronglyEmbedded_eq_sylow_normalizer n hn M hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : MulAction.IsPretransitive (PSU3Model n) (Sylow 2 (PSU3Model n)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := PSU3Model n)
    (psu3Sylow n hn) T
  refine ⟨g, ?_⟩
  have hcoe : (T : Subgroup (PSU3Model n)) = (psu3U n).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def]
    rfl
  rw [hT, hcoe, Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj,
    psu3B_eq_normalizer n hn]
  rfl

end Submission.PSU3

namespace Submission.PSL2

open Commons.GroupTheory.SL2

theorem pSL2StronglyEmbedded_eq_benderPair_borel (n : ℕ) (hn : 2 ≤ n)
    (M : Subgroup (PSL2Model n)) (hM : IsStronglyEmbedded M) :
    ∃ g : PSL2Model n, M = ((pSL2BenderPair n hn).conj g).B := by
  obtain ⟨T, hT⟩ := pSL2StronglyEmbedded_eq_sylow_normalizer n hn M hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : MulAction.IsPretransitive (PSL2Model n) (Sylow 2 (PSL2Model n)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := PSL2Model n)
    (pSL2Sylow n (by omega)) T
  refine ⟨g, ?_⟩
  have hcoe : (T : Subgroup (PSL2Model n)) =
      ((unipotentPSLHom (GaloisField 2 n)).range).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def]
    rfl
  rw [hT, hcoe, Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj,
    pSL2Stabilizer_eq_normalizer_unipotent n hn]
  rfl

end Submission.PSL2
