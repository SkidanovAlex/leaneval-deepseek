import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.CORE2A.inf_centralizer_eq_center_map
import Submission.Work.A7.Defs
import Submission.Work.CORE3.MDataAux

/-!
# CORE3 (`MData`): the centralizer of the layer is odd

`Work.CORE3.MData.OddCentralizerLayerAux`: in a finite group `M` whose layer `E = E(M)` is
quasisimple with odd centre, with `E/Z(E) ≅ A₇` and `|M|₂ = 2³`, the centralizer `C_M(E)` has
odd order.

## Argument

* `hiso` and `|A₇| = 2520` give `|E| = 2520 · |Z(E)|`, so `(Nat.card E).factorization 2 = 3`
  (the centre is odd).
* `|M| = |E| · [M : E]` and `|M|₂ = 2³` therefore give `[M : E]` odd (its `2`-adic valuation is
  zero, and a number of `2`-adic valuation `0` is odd).
* For `C = C_M(E)` there is a homomorphism `f : ↥C →* M/E` whose kernel is `C ⊓ E` and whose
  range lies in `M/E`; hence `|C| = |f.range| · |C ⊓ E|` with `|f.range|` dividing the odd number
  `[M : E]`, and `|C ⊓ E| = |Z(E)|` because `E ⊓ C_M(E) = Z(E)`.
-/

open Subgroup
namespace Work.CORE3.MData

theorem OddCentralizerLayerAux {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (hEq : Work.GW2.IsQuasisimple (Work.GW2.layer ↥M))
    (hZodd : Odd (Nat.card (Subgroup.center ↥(Work.GW2.layer ↥M))))
    (h2M : (Nat.card ↥M).factorization 2 = 3)
    (hiso : Nonempty ((↥(Work.GW2.layer ↥M) ⧸ Subgroup.center ↥(Work.GW2.layer ↥M)) ≃*
      alternatingGroup (Fin 7))) :
    Odd (Nat.card ↥(Subgroup.centralizer ((Work.GW2.layer ↥M : Subgroup ↥M) : Set ↥M))) := by
  classical
  set E : Subgroup ↥M := Work.GW2.layer ↥M with hEdef
  haveI hEnorm : E.Normal := Work.CORE3.mdata_layer_normal M
  -- (1) the 2-part of `|E|`
  have hE2 : (Nat.card ↥E).factorization 2 = 3 := by
    obtain ⟨e⟩ := hiso
    have hZcard : Nat.card ↥(Subgroup.center ↥E) ≠ 0 := Nat.card_pos.ne'
    have hq : Nat.card (↥E ⧸ Subgroup.center ↥E) = 2520 := by
      rw [Nat.card_congr e.toEquiv, Work.A7.card_alternatingGroup_seven]
    have hZfac : (Nat.card ↥(Subgroup.center ↥E)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h2
        exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h2))
    have h2520 : (2520 : ℕ).factorization 2 = 3 := by
      have h1 : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
      rw [h1, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2:ℕ) ∣ 315)]
    calc (Nat.card ↥E).factorization 2
        = (Nat.card (↥E ⧸ Subgroup.center ↥E) *
            Nat.card ↥(Subgroup.center ↥E)).factorization 2 := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup]
      _ = (Nat.card (↥E ⧸ Subgroup.center ↥E)).factorization 2 +
            (Nat.card ↥(Subgroup.center ↥E)).factorization 2 := by
          rw [Nat.factorization_mul (by rw [hq]; norm_num) hZcard, Finsupp.add_apply]
      _ = 3 := by rw [hq, h2520, hZfac, add_zero]
  -- (2) `|M : E|` is odd
  have hidxodd : Odd E.index := by
    have hEne : Nat.card ↥E ≠ 0 := Nat.card_pos.ne'
    have hidxne : E.index ≠ 0 := by
      rw [Subgroup.index_eq_card]
      exact (Nat.card_pos_iff.mpr
        ⟨⟨(QuotientGroup.mk' E) 1⟩, inferInstance⟩).ne'
    have hfac := Nat.factorization_mul hEne hidxne
    have hmul := Subgroup.card_mul_index E
    have hsum : (Nat.card ↥E).factorization 2 + (E.index).factorization 2 = 3 := by
      have h1 : (Nat.card ↥E * E.index).factorization 2
          = (Nat.card ↥E).factorization 2 + (E.index).factorization 2 := by
        rw [hfac, Finsupp.add_apply]
      rw [← h1, hmul, h2M]
    have hidx0 : (E.index).factorization 2 = 0 := by omega
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2dvd
    obtain ⟨m, hm⟩ := h2dvd
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, mul_zero] at hm
      exact hidxne hm
    · have hfac2 : (2 * m).factorization 2 = 1 + m.factorization 2 := by
        rw [Nat.factorization_mul (by norm_num) (Nat.pos_iff_ne_zero.mp hmpos),
          Nat.Prime.factorization Nat.prime_two]
        simp [Finsupp.add_apply]
      rw [hm, hfac2] at hidx0
      omega
  -- (3) `C = C_M(E)` is odd
  set C : Subgroup ↥M := Subgroup.centralizer ((E : Subgroup ↥M) : Set ↥M) with hCdef
  let f : ↥C →* (↥M ⧸ E) := (QuotientGroup.mk' E).comp C.subtype
  have hker : f.ker = (C ⊓ E).subgroupOf C := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show (QuotientGroup.mk' E) (x : ↥M) = 1 ↔ (x : ↥M) ∈ C ∧ (x : ↥M) ∈ E
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hCcard : Nat.card ↥C = Nat.card ↥f.range * Nat.card ↥(C ⊓ E) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    have h2 : Nat.card ↥f.ker = Nat.card ↥(C ⊓ E) := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ⊓ E ≤ C)).toEquiv
    rwa [h2] at h1
  have hCE : C ⊓ E = (Subgroup.center ↥E).map E.subtype := by
    rw [inf_comm]; exact Work.CORE2A.inf_centralizer_eq_center_map E
  have hCinfcard : Nat.card ↥(C ⊓ E) = Nat.card ↥(Subgroup.center ↥E) := by
    rw [hCE, Subgroup.card_map_of_injective E.subtype_injective]
  have hrangeodd : Odd (Nat.card ↥f.range) := by
    have h1 : Nat.card ↥f.range ∣ Nat.card ↥(⊤ : Subgroup (↥M ⧸ E)) :=
      Subgroup.card_dvd_of_le (le_top : f.range ≤ ⊤)
    rw [Subgroup.card_top, ← Subgroup.index_eq_card] at h1
    exact Odd.of_dvd_nat hidxodd h1
  rw [hCcard, hCinfcard]
  exact hrangeodd.mul hZodd

end Work.CORE3.MData
