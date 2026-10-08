import Mathlib
import Submission.Work.BG.L41Aux
import Submission.Work.BG.lemma24
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.L33DDefs
import Submission.Work.BG.lemma33ShapeA
import Submission.Work.BG.lemma33Arith
import Submission.Work.BG.glaubCorrDistinct
import Submission.Work.BG.rem31Orth

set_option linter.unusedSectionVars false

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## Auxiliary lemmas for Bender–Glauberman Lemma 4.1 (i)

Everything below is stated for the `|S| = 4` case `D.n = 2`, where `H₀/U` has order two, so
that `Λμ = {μ, λ₂μ}` for `λ₂ = lamCF C β₂` (`L41Aux.lamOrbit_eq`). -/

/-- **Lemma 3.4 (BG p. 209) in the non-exceptional configuration.**  If `ν ∈ 𝒮(χ)` is not
`s`-fixed and the exceptional configuration `|Λν| = 4 ∧ (Λν)^s = Λν` does *not* occur, then
`𝒮(χ) = {ν, ν^s}`.  (In the `D.n = 2` case the exception is impossible: `|Λν| = 2`.)  This is
`Work.BG.lemma34Leaf` with the exceptional case, which needs
`Work.BG.lemma34Exc`, removed: there the paper's argument needs the extra input
`f ν(t) = 2 ν(t)`, which the `(vi)`-clause of `GoodOn` supplies as soon as
`¬(|Λν| = 4 ∧ (Λν)^s = Λν)`. -/
theorem l41_bset_eq_pair (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (hexc : ¬ ((lamOrbit C ν).ncard = 4 ∧ sconj C '' lamOrbit C ν = lamOrbit C ν)) :
    bset C f χ = {ν, sconj C ν} := by
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
  -- the value at `t`: the `(vi)` clause of `GoodOn` in the non-exceptional configuration
  have hval : f ν (C.t : G) = 2 * ν C.t := hvi hne hexc
  -- `𝒮(χ) = {ν, ν^s}`: no third character
  have hcard : (bset C f χ).ncard ≤ 3 := thm32 D C hc hS3 f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
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

/-- `λ_β(1) = 1`. -/
theorem l41_lamCF_apply_one (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    lamCF C β (1 : ↥C.P.H0) = 1 := by
  simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]

/-- `(λ_β μ)(1) = μ(1)`. -/
theorem l41_lamCF_mul_apply_one (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (μ : ClassFunction ↥C.P.H0 ℂ) : (lamCF C β * μ) (1 : ↥C.P.H0) = μ 1 := by
  rw [ClassFunction.mul_apply, l41_lamCF_apply_one, one_mul]

/-- In the `|S| = 4` case the two elements of `Λμ = {μ, λ₂μ}` have values `μ(t)` and `-μ(t)`
at `t` while both have degree `μ(1)`, so (as `μ(t) = ±μ(1) ≠ 0`) exactly one of them has
value equal to its degree at `t`: this is it. -/
noncomputable def l41_tGood (C : Sec2Ctx G) (β₂ : quotGroup C.P →* ℂˣ)
    (μ : ClassFunction ↥C.P.H0 ℂ) : ClassFunction ↥C.P.H0 ℂ :=
  if μ C.t = μ 1 then μ else lamCF C β₂ * μ

theorem l41_tGood_of_pos (C : Sec2Ctx G) {β₂ : quotGroup C.P →* ℂˣ}
    {μ : ClassFunction ↥C.P.H0 ℂ} (h : μ C.t = μ 1) : l41_tGood C β₂ μ = μ := by
  simp [l41_tGood, h]

theorem l41_tGood_of_neg (C : Sec2Ctx G) {β₂ : quotGroup C.P →* ℂˣ}
    {μ : ClassFunction ↥C.P.H0 ℂ} (h : ¬ μ C.t = μ 1) :
    l41_tGood C β₂ μ = lamCF C β₂ * μ := by
  simp [l41_tGood, h]

/-- The chosen representative lies in the `Λ`-orbit. -/
theorem l41_tGood_mem_lamOrbit (C : Sec2Ctx G) {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (μ : ClassFunction ↥C.P.H0 ℂ) : l41_tGood C β₂ μ ∈ lamOrbit C μ := by
  rw [lamOrbit_eq C h2 hβ μ, Set.mem_ofPred_eq]
  by_cases h : μ C.t = μ 1
  · exact Or.inl (l41_tGood_of_pos C h)
  · exact Or.inr (l41_tGood_of_neg C h)

/-- The chosen representative has value equal to its degree at `t`. -/
theorem l41_tGood_apply_t (C : Sec2Ctx G) {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ) :
    l41_tGood C β₂ μ C.t = l41_tGood C β₂ μ 1 := by
  have htv : μ C.t = μ 1 ∨ μ C.t = -μ 1 := (centralValue C μ hμ).1
  by_cases h : μ C.t = μ 1
  · rw [l41_tGood_of_pos C h]; exact h
  · rw [l41_tGood_of_neg C h, lam_two_mul_apply_t C h2 hβ μ,
      l41_lamCF_mul_apply_one C β₂ μ, htv.resolve_left h]
    ring

/-- The chosen representative is the unique element of `Λμ` with value `μ(1)` at `t`. -/
theorem l41_tGood_eq_of_mem (C : Sec2Ctx G) {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hνmem : ν ∈ lamOrbit C μ) (hνt : ν C.t = ν 1) :
    ν = l41_tGood C β₂ μ := by
  have h1ne : μ 1 ≠ 0 := (centralValue C μ hμ).2
  rw [lamOrbit_eq C h2 hβ μ, Set.mem_ofPred_eq] at hνmem
  rcases hνmem with h | h
  · rw [h] at hνt ⊢
    by_cases h' : μ C.t = μ 1
    · exact (l41_tGood_of_pos C h').symm
    · exact absurd hνt h'
  · rw [h] at hνt ⊢
    by_cases h' : μ C.t = μ 1
    · exfalso
      have h1 : (lamCF C β₂ * μ) C.t = μ 1 := by
        rw [hνt, l41_lamCF_mul_apply_one]
      rw [lam_two_mul_apply_t C h2 hβ μ, h'] at h1
      have hz : μ 1 = 0 := by linear_combination (-1 / 2 : ℂ) * h1
      exact h1ne hz
    · exact (l41_tGood_of_neg C h').symm

/-- For an irreducible `μ` whose `Λ`-orbit is `s`-stable, the chosen `t`-good representative
lies in `S4Index C`. -/
theorem l41_tGood_mem_S4Index (C : Sec2Ctx G) {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ) (hfixμ : sconj C μ = μ) :
    l41_tGood C β₂ μ ∈ S4Index C := by
  have htv := l41_tGood_apply_t C h2 hβ hμ
  have hmem := l41_tGood_mem_lamOrbit C h2 hβ μ
  rw [lamOrbit_eq C h2 hβ μ, Set.mem_ofPred_eq] at hmem
  rcases hmem with h | h
  · have htv' : μ C.t = μ 1 := by rw [h] at htv; exact htv
    rw [h]
    exact ⟨hμ, hfixμ, htv'⟩
  · have htv' : (lamCF C β₂ * μ) C.t = (lamCF C β₂ * μ) 1 := by rw [h] at htv; exact htv
    rw [h]
    exact ⟨lam_two_mul_irr C hμ, by rw [sconj_lam_two_mul C h2 hβ μ, hfixμ], htv'⟩

/-- The coherence clause (iii) for the pair `(ν, λ₂ν)`: `δ_ν = f ν - f (λ₂ν)`. -/
theorem l41_delta_eq (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β₂ : quotGroup C.P →* ℂˣ)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    delta C β₂ ν = f ν - f (lamCF C β₂ * ν) := by
  have hlamirr : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hν
  have hkey : LamEquiv C ν (lamCF C β₂ * ν) := ⟨β₂, rfl⟩
  have hgood := (hf.1 ν hν) ν (Or.inl (s02c_LamEquiv_refl C ν))
      (lamCF C β₂ * ν) (Or.inl hkey) hν hlamirr
  exact hgood.2.2.2.1 hkey

/-- **BG Lemma 4.1, the "if and only if" of p. 212**: for `ν ∈ 𝓢'(χ) ⊆ S4Index C`,
`ν ∈ 𝓢'(χ)` iff `𝓢(χ)` contains `ν` or `λ₂ν`.  (It cannot contain both, by
`bset_orbit_struct`.) -/
theorem l41_iff (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    (β₂ : quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    ∀ ν ∈ S4Index C,
      (ν ∈ bset' C β₂ χ) ↔ (bset C f χ ∩ lamOrbit C ν).Nonempty := by
  intro ν hνin
  have hνirr : IsIrreducibleCharacter ν := hνin.1
  have hνs : sconj C ν = ν := hνin.2.1
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hlamirr : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hνirr
  have hdelta := l41_delta_eq C β₂ f hf hνirr
  have hstruct := bset_orbit_struct C f hf χ hχ
  -- `𝓢(χ)` cannot contain both `ν` and `λ₂ν`
  have hnotboth : ¬ (ν ∈ bset C f χ ∧ lamCF C β₂ * ν ∈ bset C f χ) := by
    rintro ⟨h1, h2'⟩
    have heq := hstruct.2 ν h1 (lamCF C β₂ * ν) h2' ⟨β₂, rfl⟩
      (lam_two_mul_ne_self C h2 hβ hνirr)
    exact lam_two_mul_ne_self C h2 hβ hνirr (heq.trans hνs)
  have hinner : ClassFunction.inner χ (delta C β₂ ν)
      = ClassFunction.inner χ (f ν) - ClassFunction.inner χ (f (lamCF C β₂ * ν)) := by
    rw [hdelta, ClassFunction.inner_sub_right]
  constructor
  · intro hmem
    have hne0 : ClassFunction.inner χ (delta C β₂ ν) ≠ 0 := hmem.2
    have hcases : ClassFunction.inner χ (f ν) ≠ 0 ∨
        ClassFunction.inner χ (f (lamCF C β₂ * ν)) ≠ 0 := by
      by_contra hc'
      push_neg at hc'
      exact hne0 (by rw [hinner, hc'.1, hc'.2, sub_zero])
    rcases hcases with h | h
    · refine ⟨ν, ⟨hνirr, h⟩, ?_⟩
      rw [lamOrbit_eq C h2 hβ ν, Set.mem_ofPred_eq]
      exact Or.inl rfl
    · refine ⟨lamCF C β₂ * ν, ⟨hlamirr, h⟩, ?_⟩
      rw [lamOrbit_eq C h2 hβ ν, Set.mem_ofPred_eq]
      exact Or.inr rfl
  · rintro ⟨μ, hμbset, hμorb⟩
    refine ⟨hνin, ?_⟩
    rw [lamOrbit_eq C h2 hβ ν, Set.mem_ofPred_eq] at hμorb
    rw [hinner]
    rcases hμorb with h | h
    · rw [h] at hμbset
      have hz : ClassFunction.inner χ (f (lamCF C β₂ * ν)) = 0 := by
        by_contra hc'
        exact hnotboth ⟨hμbset, ⟨hlamirr, hc'⟩⟩
      rw [hz, sub_zero]
      exact hμbset.2
    · rw [h] at hμbset
      have hz : ClassFunction.inner χ (f ν) = 0 := by
        by_contra hc'
        exact hnotboth ⟨⟨hνirr, hc'⟩, hμbset⟩
      rw [hz, zero_sub]
      exact neg_ne_zero.mpr hμbset.2

/-- **BG Lemma 4.1 (i), the shape of `𝓢(χ)`**: every member of `𝓢(χ) = bset C f χ` is
`s`-fixed with `|Λμ| = D.n`.  A non-`s`-fixed member would give `𝓢(χ) = {μ, μ^s}`
(Lemma 3.4), contradicting the "if and only if" at a witness of `𝓢'(χ) ≠ ∅`. -/
theorem l41_fix (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    (β₂ : quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (hiff : ∀ ν ∈ S4Index C,
      (ν ∈ bset' C β₂ χ) ↔ (bset C f χ ∩ lamOrbit C ν).Nonempty)
    (hne : (bset' C β₂ χ).Nonempty) :
    ∀ μ ∈ bset C f χ, sconj C μ = μ ∧ (lamOrbit C μ).ncard = D.n := by
  intro μ hμ
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hS3 : Work.GW2.C16.Sec3Hyp D := l41_sec3Hyp D hn
  have hμirr : IsIrreducibleCharacter μ := hμ.1
  refine ⟨?_, ?_⟩
  · by_contra hs
    have hexc : ¬ ((lamOrbit C μ).ncard = 4 ∧ sconj C '' lamOrbit C μ = lamOrbit C μ) := by
      rintro ⟨h4, -⟩
      rw [lamOrbit_ncard_eq_two C h2 hβ hμirr] at h4
      omega
    have hbset : bset C f χ = {μ, sconj C μ} :=
      l41_bset_eq_pair D C hc hn hS3 f hf χ hχ hμ hs hexc
    obtain ⟨ν, hν⟩ := hne
    obtain ⟨η, hηbset, hηorb⟩ := (hiff ν hν.1).mp hν
    have hsfixν : sconj C ν = ν := hν.1.2.1
    have hsfixLam : ∀ ξ ∈ lamOrbit C ν, sconj C ξ = ξ := by
      intro ξ hξ
      rw [lamOrbit_eq C h2 hβ ν, Set.mem_ofPred_eq] at hξ
      rcases hξ with rfl | rfl
      · exact hsfixν
      · rw [sconj_lam_two_mul C h2 hβ ν, hsfixν]
    have hηs : sconj C η = η := hsfixLam η hηorb
    have hηcases : η = μ ∨ η = sconj C μ := by
      have h' := hηbset
      rw [hbset] at h'
      simpa using h'
    rcases hηcases with rfl | hη
    · exact hs hηs
    · have h2' : sconj C (sconj C μ) = sconj C μ := by rw [← hη]; exact hηs
      rw [s02c_sconj_involutive C μ] at h2'
      exact hs h2'.symm
  · rw [lamOrbit_ncard_eq_two C h2 hβ hμirr, hn]

/-- **BG Lemma 4.1 (i), cardinality form**: `|𝓢'(χ)| = |𝓢(χ)|`.  The map `μ ↦` (the unique
element of `Λμ` with value equal to its degree at `t`) is a bijection `𝓢(χ) → 𝓢'(χ)`. -/
theorem l41_card_eq (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    (β₂ : quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (hiff : ∀ ν ∈ S4Index C,
      (ν ∈ bset' C β₂ χ) ↔ (bset C f χ ∩ lamOrbit C ν).Nonempty)
    (hfix : ∀ μ ∈ bset C f χ, sconj C μ = μ) :
    (bset' C β₂ χ).ncard = (bset C f χ).ncard := by
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hbs := bset_orbit_struct C f hf χ hχ
  have h1 : ∀ μ ∈ bset C f χ, l41_tGood C β₂ μ ∈ bset' C β₂ χ := by
    intro μ hμ
    have hS4 : l41_tGood C β₂ μ ∈ S4Index C :=
      l41_tGood_mem_S4Index C h2 hβ hμ.1 (hfix μ hμ)
    exact (hiff (l41_tGood C β₂ μ) hS4).mpr
      ⟨μ, hμ, s02c_LamEquiv_symm C (l41_tGood_mem_lamOrbit C h2 hβ μ)⟩
  have h2' : ∀ μ₁ μ₂, μ₁ ∈ bset C f χ → μ₂ ∈ bset C f χ →
      l41_tGood C β₂ μ₁ = l41_tGood C β₂ μ₂ → μ₁ = μ₂ := by
    intro μ₁ μ₂ hμ₁ hμ₂ heq
    by_contra hne
    have hL1 : LamEquiv C μ₁ (l41_tGood C β₂ μ₁) := l41_tGood_mem_lamOrbit C h2 hβ μ₁
    have hL2 : LamEquiv C μ₂ (l41_tGood C β₂ μ₂) := l41_tGood_mem_lamOrbit C h2 hβ μ₂
    have hLam : LamEquiv C μ₁ μ₂ := by
      refine s02c_LamEquiv_trans C hL1 ?_
      rw [heq]
      exact s02c_LamEquiv_symm C hL2
    have hcase := hbs.2 μ₁ hμ₁ μ₂ hμ₂ hLam (Ne.symm hne)
    rw [hfix μ₁ hμ₁] at hcase
    exact hne hcase.symm
  have h3' : ∀ b ∈ bset' C β₂ χ, ∃ a, ∃ (_ : a ∈ bset C f χ), l41_tGood C β₂ a = b := by
    intro ν hν
    obtain ⟨μ, hμ, hμorb⟩ := (hiff ν hν.1).mp hν
    refine ⟨μ, hμ, ?_⟩
    have hνmem : ν ∈ lamOrbit C μ := s02c_LamEquiv_symm C hμorb
    exact (l41_tGood_eq_of_mem C h2 hβ hμ.1 hνmem hν.1.2.2).symm
  have hcongr : (bset C f χ).ncard = (bset' C β₂ χ).ncard :=
    Set.ncard_congr (fun μ _ => l41_tGood C β₂ μ) h1 h2' h3'
  exact hcongr.symm

/-- **BG Lemma 3.3, first case, in the `|S| = 4` shape needed by Lemma 4.1 (i).**

`χ ∈ ±Irr(G)` cannot have `𝓢(χ) = bset C f χ = {μ₁, μ₂}` with `μ₁ ≠ μ₂` both `s`-fixed.

Paper p. 209 (the "Suppose `𝓢(χ)` contains exactly two such characters" case), specialised to
`D.n = 2`, where the paper's "no third such member" hypothesis is `𝓢(χ) = {μ₁, μ₂}` itself:

* **(a)** for `u ∈ C_U(S)`, `χ(u) ≡ 0 (mod 2)`: at `u = 1` Lemma 2.4 gives
  `χ(1) ≡ μ₁(1) + μ₂(1)` with `μᵢ(1)` odd (so `χ(1)` is even); for general `u`,
  Gorenstein 4.2.10 (`Work.BG.centralIntegral`) makes `|G : C_G(u)| · χ(u)/χ(1)` an algebraic
  integer, and multiplying by the algebraic integer `χ(1)/2` plus oddness of `|G : C_G(u)|`
  (`D.S ≤ C_G(u)`) gives `χ(u) ≡ 0` (`Work.BG.lemma33Arith`).
* **(b)** `χ(u) ≡ μ₁(u) + μ₂(u)` for `u ∈ U` (Lemma 2.4 at `u`, using `𝓢(χ) = {μ₁, μ₂}`).
* **(c)** some `b ∈ C_U(S)` has `μ₁(b) ≢ μ₂(b)` (mod 2): by Remark 3.1
  (`Work.BG.lemma33ShapeA`, `|Λμᵢ| = D.n` forces `μᵢ|_U` to be irreducible and `H₀`-invariant)
  the two restrictions are distinct `S`-invariant irreducible characters of `U` (invariance
  from `sconj C μᵢ = μᵢ` via `Work.BG.L33D.invariant_phiS`; distinctness from
  `Work.BG.rem31Orth` plus `hnotlam`), so Glauberman injectivity modulo 2
  (`Work.BG.glaubCorrDistinct`, with the conjugation action `Work.BG.L33D.phiS D C hc`)
  applies.

Contradiction: (a) and (b) give `μ₁(b) + μ₂(b) ≡ 0`; since `-μ₂(b) ≡ μ₂(b)` (mod 2),
`μ₁(b) ≡ μ₂(b)`, contradicting (c). -/
theorem l41_no_two_aux {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (μ₁ μ₂ : ClassFunction ↥C.P.H0 ℂ)
    (hbset : bset C f χ = {μ₁, μ₂}) (hne : μ₁ ≠ μ₂)
    (hsf₁ : sconj C μ₁ = μ₁) (hsf₂ : sconj C μ₂ = μ₂)
    (hl₁ : (lamOrbit C μ₁).ncard = D.n) (hl₂ : (lamOrbit C μ₂).ncard = D.n)
    (hnotlam : ¬ LamEquiv C μ₁ μ₂) : False := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype ↥(fixedSubgroupS (L33D.phiS D C hc)) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroupS (L33D.phiS D C hc)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- the two members of `𝓢(χ)`
  have hμ₁ : μ₁ ∈ bset C f χ := by rw [hbset]; simp
  have hμ₂ : μ₂ ∈ bset C f χ := by rw [hbset]; simp
  -- **(1)** the restrictions to `U` are irreducible and `H₀`-invariant
  obtain ⟨a₁, ha₁irr, hres₁, hH0₁⟩ := lemma33ShapeA D C hc hμ₁.1 hl₁
  obtain ⟨a₂, ha₂irr, hres₂, hH0₂⟩ := lemma33ShapeA D C hc hμ₂.1 hl₂
  -- **(2)** and invariant under the conjugation action of `S` on `U`
  have hinv : ∀ (ν : ClassFunction ↥C.P.H0 ℂ) (a : ClassFunction ↥(Uin C) ℂ),
      sconj C ν = ν → ClassFunction.restrict (Uin C) ν = a →
      (∀ g : ↥C.P.H0, ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) g a = a) →
      ∀ s : ↥(D.S), ∀ u : ↥(Uin C), a (L33D.phiS D C hc s u) = a u := by
    intro ν a hsf hres hH0
    refine L33D.invariant_phiS D C hc a ?_ ?_
    · intro s hs u
      have hg0 : (s : G) ∈ C.P.H0 := by
        rw [hc.H0_eq]
        exact Subgroup.mem_sup_right hs
      have h2 := congrArg (fun φ : ClassFunction ↥(Uin C) ℂ => φ u) (hH0 ⟨(s : G), hg0⟩)
      rw [ClassFunction.conjBy_apply] at h2
      rw [← h2]
      congr 1
    · intro u
      have hcoe : ((L33D.phiS D C hc ⟨D.t1, D.t1_mem⟩ u : ↥(Uin C)) : ↥C.P.H0)
          = conjMulEquiv C.P C.s (u : ↥C.P.H0) := by
        refine Subtype.ext ?_
        rw [L33D.phiS_apply, conjMulEquiv_apply, hc.s_eq]
      have hν : ν (conjMulEquiv C.P C.s (u : ↥C.P.H0)) = ν (u : ↥C.P.H0) := by
        have h := congrArg
          (fun φ : ClassFunction ↥C.P.H0 ℂ => φ (u : ↥C.P.H0)) hsf
        rw [sconj, conjByH_apply] at h
        exact h
      calc a (L33D.phiS D C hc ⟨D.t1, D.t1_mem⟩ u)
          = ν ((L33D.phiS D C hc ⟨D.t1, D.t1_mem⟩ u : ↥(Uin C)) : ↥C.P.H0) := by
            rw [← hres, ClassFunction.restrict_apply]
        _ = ν (conjMulEquiv C.P C.s (u : ↥C.P.H0)) := by rw [hcoe]
        _ = ν (u : ↥C.P.H0) := hν
        _ = a u := by rw [← hres, ClassFunction.restrict_apply]
  have hInvar₁ : IsInvariant (L33D.phiS D C hc) a₁ := hinv μ₁ a₁ hsf₁ hres₁ hH0₁
  have hInvar₂ : IsInvariant (L33D.phiS D C hc) a₂ := hinv μ₂ a₂ hsf₂ hres₂ hH0₂
  -- **(3)** the two restrictions are distinct
  have hne_a : a₁ ≠ a₂ := by
    intro heq
    have hinner : ClassFunction.inner (ClassFunction.restrict (Uin C) μ₁)
        (ClassFunction.restrict (Uin C) μ₂) ≠ 0 := by
      rw [hres₁, hres₂, heq]
      have h1 : ClassFunction.inner a₂ a₂ = 1 := by
        rw [irreducibleCharacter_inner_eq_ite
          (⟨a₂, ha₂irr⟩ : IrreducibleCharacter ↥(Uin C)) ⟨a₂, ha₂irr⟩]
        simp
      rw [h1]
      norm_num
    exact hinner ((rem31Orth D C hc μ₁ μ₂ hμ₁.1 hμ₂.1).2 hnotlam)
  -- **(4)** Glauberman: the two differ modulo `2` somewhere on `C_U(S)`
  obtain ⟨u₀, hu₀⟩ := glaubCorrDistinct (S := ↥(D.S : Subgroup G)) (U := ↥(Uin C))
    (L33D.isPGroup_S D) (L33D.odd_card_Uin D C hc) (L33D.phiS D C hc) a₁ a₂
    ha₁irr ha₂irr hInvar₁ hInvar₂ hne_a
  -- **(5)** the congruence `χ(u) ≡ μ₁(u) + μ₂(u)` on `U`
  have hsum_eq : ∀ u : ↥C.P.H0, (∑ᶠ ν ∈ bset C f χ, ν u) = μ₁ u + μ₂ u := by
    intro u
    rw [hbset,
      finsum_mem_insert (f := fun ν : ClassFunction ↥C.P.H0 ℂ => ν u)
        (a := μ₁) (s := ({μ₂} : Set (ClassFunction ↥C.P.H0 ℂ)))
        (by simpa [Set.mem_singleton_iff] using hne) (Set.toFinite _),
      finsum_mem_singleton]
  -- `χ(1)` is even
  have heven : AlgIntModTwo (μ₁ (1 : ↥C.P.H0) + μ₂ (1 : ↥C.P.H0)) 0 := by
    have hoddUin : Odd (Nat.card ↥(Uin C)) := L33D.odd_card_Uin D C hc
    obtain ⟨d₁, -, hd₁eq, hd₁dvd⟩ := ha₁irr.exists_natDegree_charValue_one_dvd_card
    obtain ⟨d₂, -, hd₂eq, hd₂dvd⟩ := ha₂irr.exists_natDegree_charValue_one_dvd_card
    have hμ₁1 : μ₁ (1 : ↥C.P.H0) = (d₁ : ℂ) := by
      have h1 : ClassFunction.restrict (Uin C) μ₁ (1 : ↥(Uin C)) = μ₁ (1 : ↥C.P.H0) :=
        ClassFunction.restrict_apply ..
      rw [← h1, hres₁]
      exact hd₁eq
    have hμ₂1 : μ₂ (1 : ↥C.P.H0) = (d₂ : ℂ) := by
      have h1 : ClassFunction.restrict (Uin C) μ₂ (1 : ↥(Uin C)) = μ₂ (1 : ↥C.P.H0) :=
        ClassFunction.restrict_apply ..
      rw [← h1, hres₂]
      exact hd₂eq
    rw [hμ₁1, hμ₂1]
    obtain ⟨k₁, hk₁⟩ := hoddUin.of_dvd_nat hd₁dvd
    obtain ⟨k₂, hk₂⟩ := hoddUin.of_dvd_nat hd₂dvd
    refine ⟨((k₁ + k₂ + 1 : ℕ) : ℂ), isIntegral_natCast _, ?_⟩
    rw [hk₁, hk₂]
    push_cast
    ring
  have hEvenχ1 : AlgIntModTwo (χ 1) 0 := by
    have h24 := (lemma24 C f hf χ hχ).2.2 (1 : ↥C.P.H0) C.P.U.one_mem
    rw [hsum_eq 1] at h24
    have h24' : AlgIntModTwo (χ 1) (μ₁ (1 : ↥C.P.H0) + μ₂ (1 : ↥C.P.H0)) := by
      simpa using h24
    exact h24'.trans heven
  -- **(6)** the two congruences at the Glauberman point give the contradiction
  have hxU : (((u₀ : ↥(Uin C)) : ↥C.P.H0) : G) ∈ C.P.U := (u₀ : ↥(Uin C)).2
  have hxcomm : ∀ s ∈ (D.S : Subgroup G),
      s * (((u₀ : ↥(Uin C)) : ↥C.P.H0) : G) * s⁻¹ = (((u₀ : ↥(Uin C)) : ↥C.P.H0) : G) :=
    fun s hs => (L33D.mem_fixedSubgroupS_phiS' D C hc (u₀ : ↥(Uin C))).mp u₀.2 s hs
  have harith := lemma33Arith D C hc hχ hEvenχ1 hxU hxcomm
  have h24u := (lemma24 C f hf χ hχ).2.2 ((u₀ : ↥(Uin C)) : ↥C.P.H0) hxU
  rw [hsum_eq ((u₀ : ↥(Uin C)) : ↥C.P.H0)] at h24u
  have hzero : AlgIntModTwo
      (μ₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0) + μ₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)) 0 :=
    h24u.symm.trans harith
  have hδ : AlgIntModTwo (μ₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0))
      (μ₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)) := by
    have h2 : AlgIntModTwo (2 * μ₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)) 0 :=
      AlgIntModTwo.mul_two
        (isIntegral_apply_of_isIrreducibleCharacter' hμ₂.1 ((u₀ : ↥(Uin C)) : ↥C.P.H0))
    have h3 := hzero.sub h2
    have heq : (μ₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0) + μ₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0))
        - 2 * μ₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)
        = μ₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0) - μ₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0) := by ring
    rw [heq] at h3
    obtain ⟨c, hc', hceq⟩ := h3
    exact ⟨c, hc', by simpa using hceq⟩
  have hcong_a : AlgIntModTwo (a₁ (u₀ : ↥(Uin C))) (a₂ (u₀ : ↥(Uin C))) := by
    have h1 : a₁ (u₀ : ↥(Uin C)) = μ₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0) := by
      rw [← hres₁, ClassFunction.restrict_apply]
    have h2 : a₂ (u₀ : ↥(Uin C)) = μ₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0) := by
      rw [← hres₂, ClassFunction.restrict_apply]
    rw [h1, h2]
    exact hδ
  exact hu₀ hcong_a

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **BG Lemma 4.1 (i) skeleton, p. 212**: the shape of `𝒮(χ) = bset C f χ` and its
bijection with `𝒮'(χ) = bset' C β₂ χ`.

Route (all inputs are in the imports):
* `Sec3Hyp D` holds because `D.n = 2` gives `|S₀| = 2` (`Work.BG.nCases`), so every `x ∈ S₀`
  satisfies `x ^ 2 = 1`; supply it inline to `thm32`/`lemma33Leaf`/`lemma34Leaf`.
* `L41Aux` gives `lamOrbit C μ = {μ, λ₂μ}` with `λ₂ = lamCF C β₂`, hence `|Λμ| = 2 = D.n`
  for every irreducible `μ` (`lamOrbit_ncard_eq_two`), and `ν^s ≠ λ₂ν` (`sconj_ne_lam_two_mul`).
* `hf.1` (clause (iii) of `GoodOn`) gives `delta C β₂ ν = f ν - f (lamCF C β₂ * ν)`.
* `bset_orbit_struct` says `𝒮(χ)` contains at most one of `ν`, `λ₂ν` (its members are `±1`
  against `χ`), which yields clause (3) and the injectivity of `μ ↦ Λμ` on `𝒮(χ)`.
* `thm32` gives `|𝒮(χ)| ≤ 3`; `lemma34Leaf` rules out non-`s`-fixed members (the disjunction
  there is automatic since `|Λμ| = 2 = D.n`); `lemma33Leaf` rules out `|𝒮(χ)| = 2` and gives
  clause (2).  Clause (4) is the bijection `μ ↦` (the `s`-fixed element of `Λμ`) with inverse
  given by clause (3); clause (1) then follows from `|𝒮(χ)| ∈ {1,3}`. -/
theorem l41Shape {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    (β₂ : Work.BG.quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ)
    (hne : (Work.GW2.C16.bset' C β₂ χ).Nonempty) :
    ((Work.GW2.C16.bset C f χ).ncard = 1 ∨ (Work.GW2.C16.bset C f χ).ncard = 3) ∧
    (∀ μ ∈ Work.GW2.C16.bset C f χ,
        Work.BG.sconj C μ = μ ∧ (Work.BG.lamOrbit C μ).ncard = D.n) ∧
    (∀ ν ∈ Work.GW2.C16.S4Index C,
        (ν ∈ Work.GW2.C16.bset' C β₂ χ) ↔
          (Work.GW2.C16.bset C f χ ∩ Work.BG.lamOrbit C ν).Nonempty) ∧
    (Work.GW2.C16.bset' C β₂ χ).ncard = (Work.GW2.C16.bset C f χ).ncard := by
  classical
  haveI : Finite (IrreducibleCharacter ↥C.P.H0) := finite_irreducibleCharacter
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hS3 : Work.GW2.C16.Sec3Hyp D := l41_sec3Hyp D hn
  have hiff := l41_iff D C hc hn β₂ hβ f hf χ hχ
  have hfix := l41_fix D C hc hn β₂ hβ f hf χ hχ hiff hne
  have hnebset : (bset C f χ).Nonempty := by
    obtain ⟨ν, hν⟩ := hne
    obtain ⟨μ, hμ, -⟩ := (hiff ν hν.1).mp hν
    exact ⟨μ, hμ⟩
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  refine ⟨?_, hfix, hiff, ?_⟩
  · have hle3 : (bset C f χ).ncard ≤ 3 := thm32 D C hc hS3 f hf χ hχ
    have hge1 : 1 ≤ (bset C f χ).ncard := by
      have := (Set.ncard_pos hfin).mpr hnebset
      omega
    have hne2 : (bset C f χ).ncard ≠ 2 := by
      intro h2'
      obtain ⟨μ₁, μ₂, hne12, hset⟩ := Set.ncard_eq_two.mp h2'
      have hμ₁ : μ₁ ∈ bset C f χ := by rw [hset]; simp
      have hμ₂ : μ₂ ∈ bset C f χ := by rw [hset]; simp
      have hnotlam : ¬ LamEquiv C μ₁ μ₂ := by
        intro hlam
        have heq := (bset_orbit_struct C f hf χ hχ).2 μ₁ hμ₁ μ₂ hμ₂ hlam (Ne.symm hne12)
        rw [(hfix μ₁ hμ₁).1] at heq
        exact hne12 heq.symm
      exact l41_no_two_aux D C hc hn hS3 f hf χ hχ μ₁ μ₂ hset hne12
        (hfix μ₁ hμ₁).1 (hfix μ₂ hμ₂).1 (hfix μ₁ hμ₁).2 (hfix μ₂ hμ₂).2 hnotlam
    omega
  · exact l41_card_eq D C hc hn β₂ hβ f hf χ hχ hiff (fun μ hμ => (hfix μ hμ).1)

end Work.BG
