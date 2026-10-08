import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.thm32
import Submission.Work.BG.nCases
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.lemma33Case1b
import Submission.Work.BG.lemma33Case2

/-!
# Area BG: Bender–Glauberman 1981, Lemma 3.3 (`Work.GW2.C16.Lemma33Prop`), p. 209

The paper's statement is

  **LEMMA 3.3.** Let `χ ∈ ±Irr(G)`.  Suppose `𝒮(χ)` contains two characters `ν` such that
  `ν^s = ν` and `|Λν| = m`.  Then `𝒮(χ)` consists of three such characters, and `S` has
  order `4`,

where `𝒮(χ) = bset C f χ`, `m = D.n = |H₀ : U|` and `·̃ = f` is the coherent map of
Theorem 2.3.

This file is the **assembly**: the paper splits its proof into

* the case that `𝒮(χ)` contains *exactly* two `s`-fixed members with `|Λν| = m`
  (`Work.BG.lemma33Case1b`): then Lemma 2.4 together with Lemmas 1.8/1.9 on `B = C_U(S)`
  and Gorenstein 4.2.10 give `χ ≡ μ + ν ≢ 0` and `χ ≡ 0` on `B` — a contradiction;
* the case `|S| ≥ 8` with three such members (`Work.BG.lemma33Case2`): Lemma 2.1 produces
  three pairwise orthogonal degree-zero `δᵢ`, whose coherence relations force `χ(1) = 0`.

Theorem 3.2 (`Work.BG.thm32`, `|𝒮(χ)| ≤ 3`) then shows that `𝒮(χ)` consists exactly of the
three members, and `NCasesProp` (`Work.BG.nCases`, `D.n = 2 ∨ 4 ≤ D.n`) pins `D.n = 2`.

The argument runs as follows.  Write `P ν` for "`ν ∈ 𝒮(χ)`, `ν^s = ν` and `|Λν| = D.n`".
By hypothesis `P ν₁` and `P ν₂` with `ν₁ ≠ ν₂`.

* If no third `ν` satisfies `P`, Lemma 3.3's first case (`lemma33Case1b`) gives `False`.
  Hence some `ν₃` with `P ν₃` and `ν₃ ∉ {ν₁, ν₂}` exists.
* If `D.n ≠ 2` then `4 ≤ D.n` (`nCases`), and the second case (`lemma33Case2`) applied to
  `ν₁, ν₂, ν₃` gives `False`.  Hence `D.n = 2`.
* As `|𝒮(χ)| ≤ 3` (`thm32`) and `{ν₁, ν₂, ν₃} ⊆ 𝒮(χ)` has three distinct elements, we get
  `𝒮(χ) = {ν₁, ν₂, ν₃}`, and every element of `𝒮(χ)` is one of these, hence satisfies `P`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma33Leaf {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Lemma33Prop D C := by
  classical
  intro hDC hS3 f hf χ hχ ν₁ hν₁ ν₂ hν₂ hne hs1 hs2 ho1 ho2
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥C.P.H0) := finite_irreducibleCharacter (G := ↥C.P.H0)
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  -- **(1)** some third `s`-fixed member of `𝒮(χ)` with `|Λν| = D.n` exists.
  have hthird : ∃ ν₃ : ClassFunction ↥C.P.H0 ℂ, ν₃ ∈ bset C f χ ∧ ν₃ ≠ ν₁ ∧ ν₃ ≠ ν₂ ∧
      sconj C ν₃ = ν₃ ∧ (lamOrbit C ν₃).ncard = D.n := by
    by_contra hc
    refine lemma33Case1b D C hDC hS3 f hf χ hχ ν₁ hν₁ ν₂ hν₂ hne hs1 hs2 ho1 ho2 ?_
    intro ν hν hs ho
    by_contra h3
    exact hc ⟨ν, hν, (fun h => h3 (Or.inl h)), (fun h => h3 (Or.inr h)), hs, ho⟩
  obtain ⟨ν₃, hν₃, h31, h32, hs3, ho3⟩ := hthird
  have h13 : ν₁ ≠ ν₃ := fun h => h31 h.symm
  have h23 : ν₂ ≠ ν₃ := fun h => h32 h.symm
  -- **(2)** `D.n = 2`.
  have hDn : D.n = 2 := by
    rcases (nCases G D).1 with h2 | h4
    · exact h2
    · exact False.elim (lemma33Case2 D C hDC hS3 f hf χ hχ h4 ν₁ hν₁ ν₂ hν₂ ν₃ hν₃
        hne h13 h23 hs1 hs2 hs3 ho1 ho2 ho3)
  -- **(3)** `𝒮(χ) = {ν₁, ν₂, ν₃}` hence `|𝒮(χ)| = 3` and every member is one of the three.
  have hset3 : ({ν₁, ν₂, ν₃} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    have h1 : ν₁ ∉ ({ν₂, ν₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, h13⟩
    have h2 : ν₂ ∉ ({ν₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simp only [Set.mem_singleton_iff]
      exact h23
    rw [show ({ν₁, ν₂, ν₃} : Set (ClassFunction ↥C.P.H0 ℂ))
        = insert ν₁ (insert ν₂ ({ν₃} : Set (ClassFunction ↥C.P.H0 ℂ))) from rfl]
    rw [Set.ncard_insert_of_notMem h1 (Set.Finite.insert ν₂ (Set.finite_singleton ν₃)),
      Set.ncard_insert_of_notMem h2 (Set.finite_singleton ν₃), Set.ncard_singleton]
  have hsub : ({ν₁, ν₂, ν₃} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro ν hν
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl | rfl
    · exact hν₁
    · exact hν₂
    · exact hν₃
  have hbset3 : (bset C f χ).ncard = 3 := by
    have hle : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
    have hge : 3 ≤ (bset C f χ).ncard :=
      le_trans (le_of_eq hset3.symm) (Set.ncard_le_ncard hsub hfin)
    exact le_antisymm hle hge
  refine ⟨hDn, hbset3, ?_⟩
  intro ν hν
  have hmem : ν = ν₁ ∨ ν = ν₂ ∨ ν = ν₃ := by
    by_contra hc
    have hnotmem : ν ∉ ({ν₁, ν₂, ν₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      intro hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      exact hc hm
    have hsub4 : (insert ν ({ν₁, ν₂, ν₃} : Set (ClassFunction ↥C.P.H0 ℂ))) ⊆ bset C f χ :=
      Set.insert_subset hν hsub
    have h4 : (insert ν ({ν₁, ν₂, ν₃} : Set (ClassFunction ↥C.P.H0 ℂ))).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem hnotmem (hfin.subset hsub), hset3]
    have hle4 : (insert ν ({ν₁, ν₂, ν₃} : Set (ClassFunction ↥C.P.H0 ℂ))).ncard ≤
        (bset C f χ).ncard := Set.ncard_le_ncard hsub4 hfin
    omega
  rcases hmem with rfl | rfl | rfl
  · exact ⟨hs1, ho1⟩
  · exact ⟨hs2, ho2⟩
  · exact ⟨hs3, ho3⟩

end Work.BG
