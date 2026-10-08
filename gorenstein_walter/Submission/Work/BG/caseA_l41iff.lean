-- Minimal clean extract of `Submission/Work/BG/l41Shape.lean`: the declarations that neither
-- use the `sorry`-based `Work.BG.lemma33Leaf` / `Work.BG.lemma34Leaf` nor anything derived from
-- them.  It provides `Work.BG.CaseACopy.l41_iff` (the "if and only if" of BG Lemma 4.1 (i)),
-- `Work.BG.CaseACopy.l41_delta_eq` and `Work.BG.CaseACopy.l41_sec3Hyp`, which are the only
-- inputs the proof of `Work.BG.caseA` needs from Lemma 4.1 / the §3 hypothesis.
import Mathlib
import Submission.Work.BG.L41Aux
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_lemma21

set_option linter.unusedSectionVars false

namespace Work.BG.CaseACopy

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## Auxiliary lemmas for Bender–Glauberman Lemma 4.1 (i)

Everything below is stated for the `|S| = 4` case `D.n = 2`, where `H₀/U` has order two, so
that `Λμ = {μ, λ₂μ}` for `λ₂ = lamCF C β₂` (`L41Aux.lamOrbit_eq`). -/

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


end Work.BG.CaseACopy
