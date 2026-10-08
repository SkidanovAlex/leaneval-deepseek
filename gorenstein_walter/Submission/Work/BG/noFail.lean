import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_lemma21Ext
import Submission.Work.BG.s02_pairCount_conj
import Submission.Work.BG.s02_pairCount_sum
import Submission.Work.BG.s02_pairCount_T_card
import Submission.Work.BG.s02_involutionPair
import Submission.Work.BG.lemma17_ii
import Submission.Work.BG.lemma17_iii
import Submission.Work.BG.lemma16_mod_two
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.centralValue
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_lemma17T
import Submission.Work.BG.l41Vi
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02c_LamEquiv_sconj
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.s02_bsValueAtT
import Submission.Work.BG.s02_lemma22Sq
import Submission.Work.BG.remark15Disjoint
import Submission.Work.BG.lemma24
import Submission.Work.BG.nfSevenSq

namespace Work.BG

open OddOrder.RepresentationTheory
open Classical

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary facts -/

/-- `t` is fixed by `s`-conjugation: `sconj` does not change the value at `t`. -/
theorem nf_sconj_apply_t (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C ν C.t = ν C.t := by
  have hfix : conjMulEquiv C.P C.s C.t = C.t := by
    apply Subtype.ext
    rw [conjMulEquiv_apply, C.t_comm_H (C.s : G) C.s.2, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : sconj C ν C.t = ν (conjMulEquiv C.P C.s C.t) := by
    rw [sconj, conjByH_apply]
  rw [h1, hfix]

/-- `ind C ∘ sconj = ind C`: induction to `G` does not see conjugation by `s`. -/
theorem nf_ind_sconj (C : Sec2Ctx G) [Fintype G] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (θ : ClassFunction ↥C.P.H0 ℂ) : ind C (sconj C θ) = ind C θ :=
  induce_conjByH C.P C.s θ

theorem nf_ind_negI (C : Sec2Ctx G) [Fintype G] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (θ : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.induce C.P.H0 (-θ) = -ClassFunction.induce C.P.H0 θ := by
  have h1 : (-θ : ClassFunction ↥C.P.H0 ℂ) = (-1 : ℂ) • θ := by ext x; simp
  rw [h1, ClassFunction.induce_smul]
  simp

theorem nf_ind_subI (C : Sec2Ctx G) [Fintype G] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (θ θ' : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.induce C.P.H0 (θ - θ') =
      ClassFunction.induce C.P.H0 θ - ClassFunction.induce C.P.H0 θ' := by
  have h1 : ClassFunction.induce C.P.H0 (θ - θ') = ClassFunction.induce C.P.H0 (θ + -θ') := by
    rw [sub_eq_add_neg]
  rw [h1, ClassFunction.induce_add, nf_ind_negI, sub_eq_add_neg]

theorem nf_ind_neg (C : Sec2Ctx G) [Fintype G] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (θ : ClassFunction ↥C.P.H0 ℂ) : ind C (-θ) = -ind C θ := by
  change ClassFunction.induce C.P.H0 (-θ) = -ClassFunction.induce C.P.H0 θ
  exact nf_ind_negI C θ

theorem nf_ind_sub (C : Sec2Ctx G) [Fintype G] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (θ θ' : ClassFunction ↥C.P.H0 ℂ) : ind C (θ - θ') = ind C θ - ind C θ' := by
  change ClassFunction.induce C.P.H0 (θ - θ') =
    ClassFunction.induce C.P.H0 θ - ClassFunction.induce C.P.H0 θ'
  exact nf_ind_subI C θ θ'

/-- **The orbit `Λν` is `s`-invariant when it contains an `s`-fixed character.** -/
theorem nf_lamOrbit_sconj_eq_self (C : Sec2Ctx G) {η ν : ClassFunction ↥C.P.H0 ℂ}
    (hην : LamEquiv C η ν) (hfix : sconj C ν = ν) :
    sconj C '' lamOrbit C η = lamOrbit C η := by
  have h1 : sconj C '' lamOrbit C η = lamOrbit C (sconj C η) :=
    s02c_sconj_image_lamOrbit C (sconjLam C) η
  have h2 : lamOrbit C (sconj C η) = lamOrbit C (sconj C ν) :=
    s02c_lamOrbit_eq_of_lamEquiv C (s02c_LamEquiv_sconj C hην)
  rw [h1, h2, hfix, ← s02c_lamOrbit_eq_of_lamEquiv C hην]

/-- A `Λ`-orbit transversal of `Irr(H₀)` sending the `Λ`-orbit of `μ₀` to `μ₀`. -/
noncomputable def nfRep (C : Sec2Ctx G) (μ₀ : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥C.P.H0 ℂ := by
  classical
  exact fun χ =>
    if h : IsIrreducibleCharacter χ then
      if LamEquiv C μ₀ χ then μ₀
      else ((orbitRep C ⟨χ, h⟩ : IrreducibleCharacter ↥C.P.H0) : ClassFunction ↥C.P.H0 ℂ)
    else χ

theorem nfRep_apply (C : Sec2Ctx G) (μ₀ χ : ClassFunction ↥C.P.H0 ℂ)
    (hχ : IsIrreducibleCharacter χ) :
    nfRep C μ₀ χ = if LamEquiv C μ₀ χ then μ₀
      else ((orbitRep C ⟨χ, hχ⟩ : IrreducibleCharacter ↥C.P.H0) : ClassFunction ↥C.P.H0 ℂ) := by
  classical
  simp only [nfRep, dif_pos hχ]

theorem nfRep_irr (C : Sec2Ctx G) (μ₀ : ClassFunction ↥C.P.H0 ℂ) (hμ₀ : IsIrreducibleCharacter μ₀)
    (ν : IrreducibleCharacter ↥C.P.H0) :
    IsIrreducibleCharacter (nfRep C μ₀ (ν : ClassFunction ↥C.P.H0 ℂ)) ∧
    LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (nfRep C μ₀ (ν : ClassFunction ↥C.P.H0 ℂ)) := by
  classical
  rw [nfRep_apply C μ₀ _ ν.2]
  by_cases h : LamEquiv C μ₀ (ν : ClassFunction ↥C.P.H0 ℂ)
  · rw [if_pos h]; exact ⟨hμ₀, s02c_LamEquiv_symm C h⟩
  · rw [if_neg h]; exact ⟨(orbitRep C ν).2, orbitRep_mem C ν⟩

theorem nfRep_eq_of_lamEquiv (C : Sec2Ctx G) (μ₀ : ClassFunction ↥C.P.H0 ℂ)
    (ν ν' : IrreducibleCharacter ↥C.P.H0)
    (h : LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (ν' : ClassFunction ↥C.P.H0 ℂ)) :
    nfRep C μ₀ (ν : ClassFunction ↥C.P.H0 ℂ) = nfRep C μ₀ (ν' : ClassFunction ↥C.P.H0 ℂ) := by
  classical
  rw [nfRep_apply C μ₀ _ ν.2, nfRep_apply C μ₀ _ ν'.2]
  have hiff : LamEquiv C μ₀ (ν : ClassFunction ↥C.P.H0 ℂ) ↔
      LamEquiv C μ₀ (ν' : ClassFunction ↥C.P.H0 ℂ) :=
    ⟨fun h1 => s02c_LamEquiv_trans C h1 h,
     fun h1 => s02c_LamEquiv_trans C h1 (s02c_LamEquiv_symm C h)⟩
  by_cases h1 : LamEquiv C μ₀ (ν : ClassFunction ↥C.P.H0 ℂ)
  · rw [if_pos h1, if_pos (hiff.mp h1)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.mpr h2)), orbitRep_eq_of_lamEquiv (C := C) h]

theorem nfRep_eq_of_mem (C : Sec2Ctx G) (μ₀ : ClassFunction ↥C.P.H0 ℂ)
    (ν : IrreducibleCharacter ↥C.P.H0)
    (h : LamEquiv C μ₀ (ν : ClassFunction ↥C.P.H0 ℂ)) :
    nfRep C μ₀ (ν : ClassFunction ↥C.P.H0 ℂ) = μ₀ := by
  classical
  rw [nfRep_apply C μ₀ _ ν.2, if_pos h]

open OddOrder.RepresentationTheory in
theorem noFail {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.NoFailProp C := by
  intro ι _ _ r i1 i2 i3 j hIrr hLam htrans hi12 hi13 hi23 hj1 hj2 hj3 hns1 hns2 ht2 hfixj hFail
  classical
  obtain ⟨g₁, g₂, g₃, φ, hg₁, hg₂, hg₃, hφ, hD2, hD3, hDj,
    h12, h13, h23, h1φ, h2φ, h3φ, hgrad⟩ := hFail
  have hD2' : ind C (r i1 - r i2) = g₁ - g₂ := hD2
  have hD3' : ind C (r i1 - r i3) = g₁ - g₃ := hD3
  have hDj' : ind C (r i1 - r j) = φ - g₂ - g₃ := hDj
  have hgrad' : ∀ i, i ≠ i1 → i ≠ j → ClassFunction.inner (ind C (r i1 - r i)) g₁ = 1 :=
    fun i hi hj => hgrad i hi hj
  -- ### 1. structure of the transversal `r`
  have key : ∀ i k : ι, (r i = r k ∨ r i = sconj C (r k)) → i = k := by
    intro i k h
    obtain ⟨i₀, _, huniq⟩ := htrans (r i) (hIrr i) (hLam i)
    exact (huniq i (Or.inl rfl)).trans (huniq k h).symm
  have keyr : ∀ i k : ι, r i = r k → i = k := fun i k h => key i k (Or.inl h)
  have keys : ∀ i k : ι, r i = sconj C (r k) → i = k := fun i k h => key i k (Or.inr h)
  have keysr : ∀ i k : ι, sconj C (r i) = r k → i = k := by
    intro i k h
    exact keys i k (by rw [← h, s02c_sconj_involutive C (r i)])
  -- ### 2. the orbit of `r i1` is `s`-invariant
  have hDorbit : sconj C '' lamOrbit C (r i1) = lamOrbit C (r i1) :=
    nf_lamOrbit_sconj_eq_self C (hLam j) hfixj
  have hmemSO : ∀ i, sconj C (r i) ∈ lamOrbit C (r i1) := fun i => by
    rw [← hDorbit]; exact ⟨r i, hLam i, rfl⟩
  have hsconjO : ∀ ξ, ¬ LamEquiv C (r i1) ξ → ¬ LamEquiv C (r i1) (sconj C ξ) := by
    intro ξ hξ h
    refine hξ ?_
    have h1 : sconj C (sconj C ξ) ∈ sconj C '' lamOrbit C (r i1) := ⟨sconj C ξ, h, rfl⟩
    rwa [hDorbit, s02c_sconj_involutive C ξ] at h1
  -- ### 3. the Brauer-Suzuki Gram matrix for the `D i = (r i1 - r i)^G`
  have hcHa : cH C (r i1) (r i1) = 1 := by
    rw [cH, if_pos rfl, if_neg hns1.symm, add_zero]
  have hcHb : ∀ k, k ≠ i1 → cH C (r i1) (r k) = 0 := by
    intro k hk
    rw [cH, if_neg (fun h => hk (keyr k i1 h)), if_neg (fun h => hk (keys k i1 h)), add_zero]
  have hcHc : ∀ i, i ≠ i1 → cH C (r i) (r i1) = 0 := by
    intro i hi
    rw [cH, if_neg (fun h => hi (keyr i i1 h.symm)),
      if_neg (fun h => hi (keysr i i1 h.symm)), add_zero]
  have hgram : ∀ i k, i ≠ i1 → k ≠ i1 →
      ClassFunction.inner (ind C (r i1 - r i)) (ind C (r i1 - r k)) = 1 + cH C (r i) (r k) := by
    intro i k hi hk
    rw [s02_gram C (r i1) (r i) (r i1) (r k) (hIrr i1) (hIrr i) (hIrr i1) (hIrr k)
      (hLam i) (hLam k), hcHa, hcHb k hk, hcHc i hi]
    ring
  have hgramNe : ∀ i k, i ≠ i1 → k ≠ i1 → i ≠ k →
      ClassFunction.inner (ind C (r i1 - r i)) (ind C (r i1 - r k)) = 1 := by
    intro i k hi hk hik
    rw [hgram i k hi hk, cH,
      if_neg (fun h => hik (keyr i k h.symm)),
      if_neg (fun h => hik (keys i k (by rw [h, s02c_sconj_involutive C (r i)])))]
    ring
  have hgramSelf2 : ClassFunction.inner (ind C (r i1 - r i2)) (ind C (r i1 - r i2)) = 2 := by
    rw [hgram i2 i2 hi12.symm hi12.symm, cH, if_pos rfl, if_neg hns2.symm]
    norm_num
  have hGramI2I : ∀ i, i ≠ i1 → i ≠ i2 →
      ClassFunction.inner (ind C (r i1 - r i2)) (ind C (r i1 - r i)) = 1 :=
    fun i hi hi2 => hgramNe i2 i hi12.symm hi (Ne.symm hi2)
  -- ### 4. norms of the signed irreducibles
  have hIrrS : IsIrreducibleCharacter (sconj C (r i2)) :=
    IsIrreducibleCharacter.conjByH C.P C.s (hIrr i2)
  have pmIrrSelf : ∀ {g : ClassFunction G ℂ}, IsPmIrr g → ClassFunction.inner g g = 1 := by
    intro g hg
    rcases hg with h | h
    · exact IsIrreducibleCharacter.inner_self_eq_one h
    · have h1 : ClassFunction.inner g g = ClassFunction.inner (-g) (-g) := by
        rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg]
      rw [h1]
      exact IsIrreducibleCharacter.inner_self_eq_one h
  -- ### 5. the values `⟨g₂, D i⟩`
  have hg1D2 : ClassFunction.inner g₁ (ind C (r i1 - r i2)) = 1 := by
    rw [hD2', ClassFunction.inner_sub_right, pmIrrSelf hg₁, h12, sub_zero]
  have hg2D2 : ClassFunction.inner g₂ (ind C (r i1 - r i2)) = -1 := by
    have h : g₂ = g₁ - ind C (r i1 - r i2) := by rw [hD2']; abel
    rw [h, ClassFunction.inner_sub_left, hg1D2, hgramSelf2]
    ring
  have hg2Dj : ClassFunction.inner g₂ (ind C (r i1 - r j)) = -1 := by
    rw [hDj', ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
      h2φ, h23, pmIrrSelf hg₂]
    ring
  have hGramG2 : ∀ i, i ≠ i1 → i ≠ i2 → i ≠ j →
      ClassFunction.inner g₂ (ind C (r i1 - r i)) = 0 := by
    intro i hi hi2 hij
    by_cases hi1 : i = i1
    · rw [hi1, sub_self]
      simp [ClassFunction.induce_zero]
    · have h : g₂ = g₁ - ind C (r i1 - r i2) := by rw [hD2']; abel
      have hg1Di : ClassFunction.inner g₁ (ind C (r i1 - r i)) = 1 := by
        rw [ClassFunction.inner_star_comm]
        rw [show ClassFunction.inner (ind C (r i1 - r i)) g₁ = 1 from hgrad' i hi hij, star_one]
      rw [h, ClassFunction.inner_sub_left, hg1Di, hGramI2I i hi hi2]
      ring
  -- ### 6. the transversal used in Lemma 1.7
  have hrep1 : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      IsIrreducibleCharacter (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)) ∧
      LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)) :=
    fun ν => nfRep_irr C (r i1) (hIrr i1) ν
  have hrep2 : ∀ ν ν' : IrreducibleCharacter ↥C.P.H0,
      LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (ν' : ClassFunction ↥C.P.H0 ℂ) →
      nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ) = nfRep C (r i1) (ν' : ClassFunction ↥C.P.H0 ℂ) :=
    fun ν ν' h => nfRep_eq_of_lamEquiv C (r i1) ν ν' h
  have h17 := s02_lemma17T C g₂ (nfRep C (r i1)) hrep1 hrep2 C.t C.t_not_mem_U
  let F : IrreducibleCharacter ↥C.P.H0 → ℂ := fun ν =>
    ClassFunction.inner g₂ (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))) *
      ((ν : ClassFunction ↥C.P.H0 ℂ) C.t)
  have h17' : g₂ (C.t : G) = ∑ ν : IrreducibleCharacter ↥C.P.H0, F ν := h17
  -- ### 7. the summand vanishes off the three exceptional classes
  have hzero : ∀ ν ∈ (Finset.univ : Finset (IrreducibleCharacter ↥C.P.H0)),
      ν ∉ ({⟨r i2, hIrr i2⟩, ⟨sconj C (r i2), hIrrS⟩, ⟨r j, hIrr j⟩} :
        Finset (IrreducibleCharacter ↥C.P.H0)) → F ν = 0 := by
    intro ν _ hνS
    have hν2 : (ν : ClassFunction ↥C.P.H0 ℂ) ≠ r i2 := by
      intro h
      apply hνS
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Subtype.ext h)
    have hνs : (ν : ClassFunction ↥C.P.H0 ℂ) ≠ sconj C (r i2) := by
      intro h
      apply hνS
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (Subtype.ext h))
    have hνj : (ν : ClassFunction ↥C.P.H0 ℂ) ≠ r j := by
      intro h
      apply hνS
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Subtype.ext h))
    by_cases hO : LamEquiv C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
    · obtain ⟨i, hi, -⟩ := htrans (ν : ClassFunction ↥C.P.H0 ℂ) ν.2 hO
      have hrν : nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ) = r i1 :=
        nfRep_eq_of_mem C (r i1) ν hO
      have hind : ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - r i1) = -(ind C (r i1 - r i)) := by
        have h1 : ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - r i1)
            = ind C (ν : ClassFunction ↥C.P.H0 ℂ) - ind C (r i1) := nf_ind_sub C _ _
        have h2 : ind C (ν : ClassFunction ↥C.P.H0 ℂ) = ind C (r i) := by
          rcases hi with hi | hi
          · rw [hi]
          · rw [hi]; exact nf_ind_sconj C (r i)
        have h3 : ind C (r i1 - r i) = ind C (r i1) - ind C (r i) := nf_ind_sub C _ _
        rw [h1, h2, h3]
        abel
      have hdi : ClassFunction.inner g₂ (ind C (r i1 - r i)) = 0 := by
        by_cases hi2 : i = i2
        · exfalso
          rw [hi2] at hi
          rcases hi with hi | hi
          · exact hν2 hi
          · exact hνs hi
        · by_cases hij : i = j
          · exfalso
            rw [hij] at hi
            rcases hi with hi | hi
            · exact hνj hi
            · rw [hfixj] at hi; exact hνj hi
          · by_cases hi1 : i = i1
            · rw [hi1, sub_self]
              simp [ClassFunction.induce_zero]
            · exact hGramG2 i hi1 hi2 hij
      have hval : ClassFunction.inner g₂ (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) -
            nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))) = 0 := by
        rw [hrν, hind, ClassFunction.inner_neg_right, hdi, neg_zero]
      show ClassFunction.inner g₂ (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) -
        nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))) * ((ν : ClassFunction ↥C.P.H0 ℂ) C.t) = 0
      rw [hval, zero_mul]
    · have hrepO : ¬ LamEquiv C (r i1) (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)) :=
        fun h => hO (s02c_LamEquiv_trans C h (s02c_LamEquiv_symm C (hrep1 ν).2))
      have hνsO : ¬ LamEquiv C (r i1) (sconj C (ν : ClassFunction ↥C.P.H0 ℂ)) := hsconjO _ hO
      have hrsO : ¬ LamEquiv C (r i1) (sconj C (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))) :=
        hsconjO _ hrepO
      have hcH0 : ∀ ξ : ClassFunction ↥C.P.H0 ℂ, ¬ LamEquiv C (r i1) ξ →
          ¬ LamEquiv C (r i1) (sconj C ξ) → ∀ i : ι, cH C ξ (r i) = 0 := by
        intro ξ hξ hξs i
        rw [cH, if_neg (fun h => hξ (by rw [← h]; exact hLam i)),
          if_neg (fun h => hξs (by rw [← h]; exact hLam i)), add_zero]
      set Ψ : ClassFunction G ℂ :=
        ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
        with hΨdef
      have hG2 : ClassFunction.inner Ψ (ind C (r i1 - r i2)) = 0 := by
        rw [hΨdef,
          s02_gram C (ν : ClassFunction ↥C.P.H0 ℂ) (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
            (r i1) (r i2) ν.2 (hrep1 ν).1 (hIrr i1) (hIrr i2) (hrep1 ν).2 (hLam i2)]
        rw [hcH0 _ hO hνsO i1, hcH0 _ hO hνsO i2, hcH0 _ hrepO hrsO i1,
          hcH0 _ hrepO hrsO i2]
        ring
      have hG3 : ClassFunction.inner Ψ (ind C (r i1 - r i3)) = 0 := by
        rw [hΨdef,
          s02_gram C (ν : ClassFunction ↥C.P.H0 ℂ) (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
            (r i1) (r i3) ν.2 (hrep1 ν).1 (hIrr i1) (hIrr i3) (hrep1 ν).2 (hLam i3)]
        rw [hcH0 _ hO hνsO i1, hcH0 _ hO hνsO i3, hcH0 _ hrepO hrsO i1,
          hcH0 _ hrepO hrsO i3]
        ring
      have hGj : ClassFunction.inner Ψ (ind C (r i1 - r j)) = 0 := by
        rw [hΨdef,
          s02_gram C (ν : ClassFunction ↥C.P.H0 ℂ) (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
            (r i1) (r j) ν.2 (hrep1 ν).1 (hIrr i1) (hIrr j) (hrep1 ν).2 (hLam j)]
        rw [hcH0 _ hO hνsO i1, hcH0 _ hO hνsO j, hcH0 _ hrepO hrsO i1,
          hcH0 _ hrepO hrsO j]
        ring
      have hΨ1 : ClassFunction.inner Ψ g₁ = ClassFunction.inner Ψ g₂ := by
        have h := hG2
        rw [hD2', ClassFunction.inner_sub_right] at h
        exact sub_eq_zero.mp h
      have hΨ2 : ClassFunction.inner Ψ g₁ = ClassFunction.inner Ψ g₃ := by
        have h := hG3
        rw [hD3', ClassFunction.inner_sub_right] at h
        exact sub_eq_zero.mp h
      have hΨφ : ClassFunction.inner Ψ φ = 2 * ClassFunction.inner Ψ g₁ := by
        have h := hGj
        rw [hDj', ClassFunction.inner_sub_right, ClassFunction.inner_sub_right] at h
        rw [← hΨ1, ← hΨ2] at h
        linear_combination h
      have hΨZIrr : Ψ ∈ ZIrr G := by
        rw [hΨdef]
        exact (s02_indDiff C (ν : ClassFunction ↥C.P.H0 ℂ)
          (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)) ν.2 (hrep1 ν).1 (hrep1 ν).2).1
      have hgramΨ : ClassFunction.inner Ψ Ψ
          = cH C (ν : ClassFunction ↥C.P.H0 ℂ) (ν : ClassFunction ↥C.P.H0 ℂ)
            - cH C (ν : ClassFunction ↥C.P.H0 ℂ)
                (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
            - cH C (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
                (ν : ClassFunction ↥C.P.H0 ℂ)
            + cH C (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
                (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)) := by
        rw [hΨdef]
        exact s02_gram C (ν : ClassFunction ↥C.P.H0 ℂ)
          (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
          (ν : ClassFunction ↥C.P.H0 ℂ)
          (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
          ν.2 (hrep1 ν).1 ν.2 (hrep1 ν).1 (hrep1 ν).2 (hrep1 ν).2
      set N : ℤ := ((if (ν : ClassFunction ↥C.P.H0 ℂ) = (ν : ClassFunction ↥C.P.H0 ℂ)
            then 1 else 0) + (if (ν : ClassFunction ↥C.P.H0 ℂ) = sconj C (ν : ClassFunction ↥C.P.H0 ℂ)
              then 1 else 0))
        - ((if nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ) = (ν : ClassFunction ↥C.P.H0 ℂ)
              then 1 else 0) + (if nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
                = sconj C (ν : ClassFunction ↥C.P.H0 ℂ) then 1 else 0))
        - ((if (ν : ClassFunction ↥C.P.H0 ℂ) = nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
              then 1 else 0) + (if (ν : ClassFunction ↥C.P.H0 ℂ)
                = sconj C (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)) then 1 else 0))
        + ((if nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
              = nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ) then 1 else 0)
            + (if nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
                = sconj C (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)) then 1 else 0))
        with hNdef
      have hN : ClassFunction.inner Ψ Ψ = (N : ℂ) := by
        rw [hgramΨ, hNdef]
        simp only [cH]
        push_cast
        ring
      have hN4 : N ≤ 4 := by
        have hle : ∀ (P : Prop), (if P then (1 : ℤ) else 0) ≤ 1 := by
          intro P; by_cases h : P <;> simp [h]
        have hge : ∀ (P : Prop), (0 : ℤ) ≤ (if P then (1 : ℤ) else 0) := by
          intro P; by_cases h : P <;> simp [h]
        rw [hNdef]
        have a1 := hle ((ν : ClassFunction ↥C.P.H0 ℂ) = (ν : ClassFunction ↥C.P.H0 ℂ))
        have a2 := hle ((ν : ClassFunction ↥C.P.H0 ℂ) = sconj C (ν : ClassFunction ↥C.P.H0 ℂ))
        have a3 := hle (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
          = nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
        have a4 := hle (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
          = sconj C (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)))
        have b1 := hge (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
          = (ν : ClassFunction ↥C.P.H0 ℂ))
        have b2 := hge (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)
          = sconj C (ν : ClassFunction ↥C.P.H0 ℂ))
        have b3 := hge ((ν : ClassFunction ↥C.P.H0 ℂ)
          = nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ))
        have b4 := hge ((ν : ClassFunction ↥C.P.H0 ℂ)
          = sconj C (nfRep C (r i1) (ν : ClassFunction ↥C.P.H0 ℂ)))
        linarith
      have hz : ClassFunction.inner Ψ g₁ = 0 :=
        nfSevenSq hΨZIrr N hN hN4 hg₁ hg₂ hg₃ hφ h12 h13 h23 h1φ h2φ h3φ hΨ1 hΨ2 hΨφ
      have hgz : ClassFunction.inner g₂ Ψ = 0 := by
        rw [ClassFunction.inner_star_comm, ← hΨ1, hz, star_zero]
      show ClassFunction.inner g₂ Ψ * ((ν : ClassFunction ↥C.P.H0 ℂ) C.t) = 0
      rw [hgz, zero_mul]
  -- ### 8. collapse the sum to the three exceptional classes
  have hne_ab : (⟨r i2, hIrr i2⟩ : IrreducibleCharacter ↥C.P.H0) ≠ ⟨sconj C (r i2), hIrrS⟩ := by
    intro h
    have h2 : r i2 = sconj C (r i2) := by simpa using congrArg Subtype.val h
    exact hns2 h2.symm
  have hne_ac : (⟨r i2, hIrr i2⟩ : IrreducibleCharacter ↥C.P.H0) ≠ ⟨r j, hIrr j⟩ := by
    intro h
    have h2 : r i2 = r j := by simpa using congrArg Subtype.val h
    exact hj2 (keyr i2 j h2).symm
  have hne_bc : (⟨sconj C (r i2), hIrrS⟩ : IrreducibleCharacter ↥C.P.H0) ≠ ⟨r j, hIrr j⟩ := by
    intro h
    have h2 : sconj C (r i2) = r j := by simpa using congrArg Subtype.val h
    exact hj2 (keysr i2 j h2).symm
  have hcollapse : (∑ ν : IrreducibleCharacter ↥C.P.H0, F ν)
      = ∑ ν ∈ ({⟨r i2, hIrr i2⟩, ⟨sconj C (r i2), hIrrS⟩, ⟨r j, hIrr j⟩} :
          Finset (IrreducibleCharacter ↥C.P.H0)), F ν :=
    (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hzero x (Finset.mem_univ x) hx)).symm
  have hra : nfRep C (r i1) (r i2) = r i1 :=
    nfRep_eq_of_mem C (r i1) ⟨r i2, hIrr i2⟩ (hLam i2)
  have hrb : nfRep C (r i1) (sconj C (r i2)) = r i1 :=
    nfRep_eq_of_mem C (r i1) ⟨sconj C (r i2), hIrrS⟩ (hmemSO i2)
  have hrc : nfRep C (r i1) (r j) = r i1 :=
    nfRep_eq_of_mem C (r i1) ⟨r j, hIrr j⟩ (hLam j)
  have ha2 : ind C ((r i2 : ClassFunction ↥C.P.H0 ℂ) - r i1) = -(ind C (r i1 - r i2)) := by
    have h1 : ind C ((r i2 : ClassFunction ↥C.P.H0 ℂ) - r i1) = ind C (r i2) - ind C (r i1) :=
      nf_ind_sub C _ _
    have h2 : ind C (r i1 - r i2) = ind C (r i1) - ind C (r i2) := nf_ind_sub C _ _
    rw [h1, h2]; abel
  have hb2 : ind C ((sconj C (r i2) : ClassFunction ↥C.P.H0 ℂ) - r i1)
      = -(ind C (r i1 - r i2)) := by
    have h1 : ind C ((sconj C (r i2) : ClassFunction ↥C.P.H0 ℂ) - r i1)
        = ind C (sconj C (r i2)) - ind C (r i1) := nf_ind_sub C _ _
    have h2 : ind C (r i1 - r i2) = ind C (r i1) - ind C (r i2) := nf_ind_sub C _ _
    rw [h1, h2, nf_ind_sconj]; abel
  have hc2 : ind C ((r j : ClassFunction ↥C.P.H0 ℂ) - r i1) = -(ind C (r i1 - r j)) := by
    have h1 : ind C ((r j : ClassFunction ↥C.P.H0 ℂ) - r i1) = ind C (r j) - ind C (r i1) :=
      nf_ind_sub C _ _
    have h2 : ind C (r i1 - r j) = ind C (r i1) - ind C (r j) := nf_ind_sub C _ _
    rw [h1, h2]; abel
  have hFa : F ⟨r i2, hIrr i2⟩ = r i2 C.t := by
    have ha1 : ((⟨r i2, hIrr i2⟩ : IrreducibleCharacter ↥C.P.H0) :
        ClassFunction ↥C.P.H0 ℂ) = r i2 := rfl
    simp only [F, ha1, hra]
    rw [ha2, ClassFunction.inner_neg_right, hg2D2]
    ring
  have hFb : F ⟨sconj C (r i2), hIrrS⟩ = r i2 C.t := by
    have hb1 : ((⟨sconj C (r i2), hIrrS⟩ : IrreducibleCharacter ↥C.P.H0) :
        ClassFunction ↥C.P.H0 ℂ) = sconj C (r i2) := rfl
    simp only [F, hb1, hrb]
    rw [hb2, ClassFunction.inner_neg_right, hg2D2, nf_sconj_apply_t]
    ring
  have hFc : F ⟨r j, hIrr j⟩ = r j C.t := by
    have hc1 : ((⟨r j, hIrr j⟩ : IrreducibleCharacter ↥C.P.H0) :
        ClassFunction ↥C.P.H0 ℂ) = r j := rfl
    simp only [F, hc1, hrc]
    rw [hc2, ClassFunction.inner_neg_right, hg2Dj]
    ring
  have hthree : ∑ ν ∈ ({⟨r i2, hIrr i2⟩, ⟨sconj C (r i2), hIrrS⟩, ⟨r j, hIrr j⟩} :
      Finset (IrreducibleCharacter ↥C.P.H0)), F ν = 2 * r i2 C.t + r j C.t := by
    rw [Finset.sum_insert (by simp [hne_ab, hne_ac]),
      Finset.sum_insert (by simp [hne_bc]), Finset.sum_singleton, hFa, hFb, hFc]
    ring
  -- ### 9. contradiction
  have hmain : g₂ (C.t : G) = 2 * r i2 C.t + r j C.t := by
    rw [h17', hcollapse, hthree]
  have ht2' : r i1 C.t = -r i2 C.t := by rw [ht2]; ring
  have hvi := l41Vi C (r i1) (r i2) (hIrr i1) (hIrr i2) (hLam i2) hns1 hns2 ht2' g₁ g₂ hg₁ hg₂ hD2'
  have hrj : r j C.t = 0 := by
    rw [hvi] at hmain
    have h2 : r j C.t = (2 * r i2 C.t + r j C.t) - 2 * r i2 C.t := by ring
    rw [h2, ← hmain, sub_self]
  have hne : r j C.t ≠ 0 := by
    obtain ⟨h, h1⟩ := centralValue C (r j) (hIrr j)
    rcases h with h | h
    · rw [h]; exact h1
    · rw [h]; exact neg_ne_zero.mpr h1
  exact hne hrj

end Work.BG
