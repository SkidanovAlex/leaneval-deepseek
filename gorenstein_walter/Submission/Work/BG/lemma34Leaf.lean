/-
# Area BG: Bender–Glauberman 1981, Lemma 3.4 (`Work.GW2.C16.Lemma34Prop`), p. 209

Source: H. Bender and G. Glauberman, *Characters of finite groups with dihedral Sylow
2-subgroups*, J. Algebra **70** (1981) 200–215.

The paper's statement (p. 209) is

  **LEMMA 3.4.** Let `χ ∈ ±Irr(G)`.  Suppose `𝒮(χ)` contains a character `ν` not fixed by
  `s` such that `ν^s ∉ Λν` or `|Λν| = m`.  Then `𝒮(χ) = {ν, ν^s}` and `ν̃(t) = 2ν(t)`,

where `𝒮(χ) = bset C f χ`, `m = D.n = |H₀ : U|` and `·̃ = f` is the coherent map of
Theorem 2.3.

This file is the *assembly* of the paper's argument from the two hard inputs:

* `Work.BG.thm32` — Theorem 3.2, `|𝒮(χ)| ≤ 3`;
* `Work.BG.lemma34Exc` — the exceptional configuration
  `|Λν| = 4 ∧ (Λν)^s = Λν` (which, together with the standing hypothesis, forces `m = 4`):
  there the paper rules out a third character in `𝒮(χ)` by a separate computation
  (Lemma 3.3, Theorem 4.2.10, Lemmas 1.8/1.9 on `B₁`).

Everything else is proved here:

* **`(2)` when the `GoodOn` situation applies.**  If `¬(|Λν| = 4 ∧ (Λν)^s = Λν)` then the
  `(vi)` clause of `GoodOn` gives `f ν t = 2ν(t)` immediately.
* **`(2)` from `𝒮(χ) = {ν, ν^s}`.**  Lemma 2.4 (`Work.BG.lemma24`) evaluated at `t` for the
  signed irreducible `f ν` gives `f ν(t) = 2ν(t)` when only `ν`, `ν^s` survive.
* **`(2) ⟹ (1)`: `𝒮(χ) = {ν, ν^s}`.**  `f ν ∈ ℤ[Irr G]` has norm `1` and `⟨χ, f ν⟩ ≠ 0`, so
  `χ = ±f ν`.  If `ξ ∈ 𝒮(χ)` were a third character, Theorem 3.2 would give
  `𝒮(χ) = {ν, ν^s, ξ}`, and Lemma 2.4 for `f ν` at `t` would give
  `f ν(t) = 2ν(t) + e·ξ(t)` with `e ≠ 0` and `ξ(t) ≠ 0`, contradicting `(2)`.
-/

import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma24
import Submission.Work.BG.centralValue
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma34Exc

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

section Helpers

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **Norm-one `ℤ[Irr G]` elements are signed irreducibles.**  If `φ ∈ ℤ[Irr G]` has norm
one and a signed irreducible `χ` is not orthogonal to `φ`, then `φ = ±χ`.  (`φ` has exactly
one constituent `ψ ∈ Irr G`, and `⟨χ, ψ⟩ ≠ 0` forces `χ = ±ψ` by orthonormality.) -/
theorem l34_eq_pm_of_inner_ne_zero {φ χ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hn : ClassFunction.inner φ φ = 1) (hχ : IsPmIrr χ)
    (h : ClassFunction.inner χ φ ≠ 0) : φ = χ ∨ φ = -χ := by
  obtain ⟨ε, ψ, hε, hφeq⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hn
  have hinner : ClassFunction.inner χ (ψ : ClassFunction G ℂ) ≠ 0 := by
    rcases hε with rfl | rfl
    · rw [one_smul] at hφeq; rw [← hφeq]; exact h
    · rw [neg_smul, one_smul] at hφeq
      have h' : ClassFunction.inner χ (-(ψ : ClassFunction G ℂ)) ≠ 0 := by
        rw [← hφeq]; exact h
      rw [ClassFunction.inner_neg_right] at h'
      exact neg_ne_zero.mp h'
  rcases hχ with hχi | hχi
  · have hχψ : χ = (ψ : ClassFunction G ℂ) := by
      by_contra hc
      have h0 : ClassFunction.inner χ (ψ : ClassFunction G ℂ) = 0 := by
        rw [irreducibleCharacter_inner_eq_ite ⟨χ, hχi⟩ ψ]
        exact ite_eq_right (fun hh => hc (by simpa using congrArg Subtype.val hh))
      exact hinner h0
    rcases hε with rfl | rfl
    · left; rw [hφeq, one_smul]; exact hχψ.symm
    · right; rw [hφeq, neg_smul, one_smul, ← hχψ]
  · have hnegψ : -χ = (ψ : ClassFunction G ℂ) := by
      by_contra hc
      have h0 : ClassFunction.inner (-χ) (ψ : ClassFunction G ℂ) = 0 := by
        rw [irreducibleCharacter_inner_eq_ite ⟨-χ, hχi⟩ ψ]
        exact ite_eq_right (fun hh => hc (by simpa using congrArg Subtype.val hh))
      have hh := ClassFunction.inner_neg_left (G := G) χ (ψ : ClassFunction G ℂ)
      rw [h0] at hh
      exact hinner (neg_eq_zero.mp hh.symm)
    rcases hε with rfl | rfl
    · right; rw [hφeq, one_smul, ← hnegψ]
    · left
      have h2 : χ = -(ψ : ClassFunction G ℂ) := by
        have := congrArg (fun z : ClassFunction G ℂ => -z) hnegψ
        simpa using this
      rw [hφeq, neg_smul, one_smul, ← h2]

end Helpers

open Work.GW2 Work.GW2.C16 in
theorem lemma34Leaf {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Lemma34Prop D C := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj
  obtain ⟨hνirr, hνne0⟩ := hν
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  -- the coherence clause at `(ν, ν)`
  have hkey : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
  have hG := (hf.1 ν hνirr) ν hkey ν hkey hνirr hνirr
  obtain ⟨hZIfν, hsconjf, hnormf, -, -, hvi⟩ := hG
  have hnormf1 : ClassFunction.inner (f ν) (f ν) = 1 := by rw [hnormf]; simp [hne]
  -- `f ν` is a signed irreducible, and `χ = ± f ν`
  obtain ⟨ε, ψ, hε, hfeq⟩ :=
    exists_zsmul_irreducibleCharacter_of_inner_self_one hZIfν hnormf1
  have hpmfν : IsPmIrr (f ν) := by
    rcases hε with rfl | rfl
    · left; rw [hfeq, one_smul]; exact ψ.2
    · right
      have h2 : -(f ν) = (ψ : ClassFunction G ℂ) := by rw [hfeq]; simp
      rw [h2]; exact ψ.2
  have hχeq : χ = f ν ∨ χ = - f ν := by
    rcases l34_eq_pm_of_inner_ne_zero hZIfν hnormf1 hχ hνne0 with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      have h2 : - f ν = χ := by rw [h]; simp
      exact h2.symm
  have hbset_eq : bset C f (f ν) = bset C f χ := by
    rcases hχeq with h | h
    · rw [h]
    · rw [h]
      ext η
      simp only [bset, Set.mem_ofPred_eq]
      rw [ClassFunction.inner_neg_left]
      simp
  have hνs_mem : sconj C ν ∈ bset C f χ := by
    refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hνirr, ?_⟩
    rw [hsconjf]; exact hνne0
  have hsub2 : ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl
    · exact ⟨hνirr, hνne0⟩
    · exact hνs_mem
  -- the value at `t`
  have hval : f ν (C.t : G) = 2 * ν C.t := by
    by_cases hexc : (lamOrbit C ν).ncard = 4 ∧ sconj C '' lamOrbit C ν = lamOrbit C ν
    · by_cases hbset : bset C f χ = {ν, sconj C ν}
      · -- only `ν`, `ν^s` occur in `𝒮(χ)`: Lemma 2.4 for `f ν` at `t`
        have hbsetν : bset C f (f ν) = {ν, sconj C ν} := by rw [hbset_eq]; exact hbset
        have hT := (lemma24 C f hf (f ν) hpmfν).2.1 C.t C.t_not_mem_U
        have hnot1 : ν ∉ ({sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
          intro hmem
          rw [Set.mem_singleton_iff] at hmem
          exact hne hmem.symm
        have hsum : (∑ᶠ η ∈ bset C f (f ν), ClassFunction.inner (f ν) (f η) * η C.t)
            = 2 * ν C.t := by
          rw [hbsetν,
            finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
              (a := ν) (s := ({sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)))
              hnot1 (Set.toFinite _),
            finsum_mem_singleton,
            hsconjf, hnormf1, sconj_apply_t]
          ring
        rw [hsum] at hT
        exact hT
      · -- the exceptional configuration: `𝒮(χ)` cannot contain a third character
        have hne_sub : ¬ ((bset C f χ) ⊆ ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ))) :=
          fun hsub => hbset (Set.Subset.antisymm hsub hsub2)
        obtain ⟨ξ, hξmem, hξnot⟩ := Set.not_subset.mp hne_sub
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hξnot
        exact (lemma34Exc D C hDC hS3 f hf χ hχ ν ⟨hνirr, hνne0⟩ hne hdisj
          hexc.1 hexc.2 ξ hξmem (fun h => hξnot (Or.inl h))
            (fun h => hξnot (Or.inr h))).elim
    · exact hvi hne hexc
  -- `𝒮(χ) = {ν, ν^s}`
  have hcard : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  refine ⟨?_, hval⟩
  ext ξ
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hξ
    by_contra hnot
    have hξν : ξ ≠ ν := fun h => hnot (Or.inl h)
    have hξνs : ξ ≠ sconj C ν := fun h => hnot (Or.inr h)
    obtain ⟨hξirr, hξne0⟩ := hξ
    -- the three characters span `𝒮(χ)`
    have hsub : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
      intro η hη
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hη
      rcases hη with rfl | rfl | rfl
      · exact ⟨hνirr, hνne0⟩
      · exact hνs_mem
      · exact ⟨hξirr, hξne0⟩
    have hnot1 : ν ∉ ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      intro hmem
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · exact hne h.symm
      · exact hξν h.symm
    have hnot2 : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      intro hmem
      rw [Set.mem_singleton_iff] at hmem
      exact hξνs hmem.symm
    have h3 : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (s := ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
            (a := ν) hnot1 (Set.toFinite _),
          Set.ncard_insert_of_notMem (s := ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
            (a := sconj C ν) hnot2 (Set.toFinite _),
          Set.ncard_singleton]
    have heq : bset C f χ = {ν, sconj C ν, ξ} :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [h3]; exact hcard) hfin).symm
    have hbsetν : bset C f (f ν) = {ν, sconj C ν, ξ} := by rw [hbset_eq]; exact heq
    -- Lemma 2.4 for `f ν` at `t`
    have hT := (lemma24 C f hf (f ν) hpmfν).2.1 C.t C.t_not_mem_U
    have hsum : (∑ᶠ η ∈ bset C f (f ν), ClassFunction.inner (f ν) (f η) * η C.t)
        = 2 * ν C.t + ClassFunction.inner (f ν) (f ξ) * ξ C.t := by
      rw [hbsetν,
        finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
          (a := ν) (s := ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
          hnot1 (Set.toFinite _),
        finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
          (a := sconj C ν) (s := ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) hnot2 (Set.toFinite _),
        finsum_mem_singleton,
        hsconjf, hnormf1, sconj_apply_t]
      ring
    rw [hsum] at hT
    rw [hval] at hT
    have hξmemν : ξ ∈ bset C f (f ν) := by
      rw [hbsetν]
      exact Set.mem_insert_of_mem ν (Set.mem_insert_of_mem (sconj C ν) (Set.mem_singleton ξ))
    have hzero : ClassFunction.inner (f ν) (f ξ) * ξ C.t = 0 := by
      have h1 : 2 * ν C.t + ClassFunction.inner (f ν) (f ξ) * ξ C.t = 2 * ν C.t + 0 := by
        rw [add_zero]; exact hT.symm
      exact add_left_cancel h1
    exact mul_ne_zero hξmemν.2 (value_t_ne_zero C ξ hξirr) hzero
  · rintro (rfl | rfl)
    · exact ⟨hνirr, hνne0⟩
    · exact hνs_mem

end Work.BG
