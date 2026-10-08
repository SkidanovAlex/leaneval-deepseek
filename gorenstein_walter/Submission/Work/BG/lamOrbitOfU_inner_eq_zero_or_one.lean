import Mathlib
import Submission.Work.BG.rem31Shape

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **The multiplicity of a `U`-irreducible in `ν|_U` is `0` or `1`.**  For
`ν ∈ Irr(H₀)` and `a ∈ Irr(U)`, `⟨ν|_U, a⟩ ∈ {0, 1}`.

Route: `Work.BG.rem31Shape D C hDC hS3 ν hν` gives `ν|_U = a₀` or `ν|_U = a₀ + a₂`
(`a₀, a₂ ∈ Irr(U)`); then `⟨ν|_U, a⟩` is `⟨a₀, a⟩` or `⟨a₀, a⟩ + ⟨a₂, a⟩`, and each is `0` or `1`
by orthonormality (`irr_cf_inner`, `irreducibleCharacter_inner_eq_ite`) and additivity
(`ClassFunction.inner_add_left`).  Note `rem31Shape` needs `Invertible (Nat.card G : ℂ)`,
which is synthesised automatically from `[Fintype G]` (add `haveI` if needed). -/
theorem lamOrbitOfU_inner_eq_zero_or_one {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    (hS3 : Work.GW2.C16.Sec3Hyp D)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    {a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ} (ha : IsIrreducibleCharacter a) :
    ClassFunction.inner (ClassFunction.restrict (Work.GW2.C16.Uin C) ν) a = 0 ∨
      ClassFunction.inner (ClassFunction.restrict (Work.GW2.C16.Uin C) ν) a = 1 := by
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨a₀, ha₀, hcase⟩ := rem31Shape D C hDC hS3 ν hν
  have ha₀mem : a₀ ∈ irreducibleCharacters ↥(Uin C) := mem_irreducibleCharacters.mpr ha₀
  have hamem : a ∈ irreducibleCharacters ↥(Uin C) := mem_irreducibleCharacters.mpr ha
  rcases hcase with ⟨hνU, -⟩ | ⟨a₂, ha₂, ha₂ne, -, hνU, -⟩
  · rw [hνU, irr_cf_inner ha₀mem hamem]
    by_cases h : a₀ = a
    · exact Or.inr (ite_eq_left h)
    · exact Or.inl (ite_eq_right h)
  · rw [hνU, ClassFunction.inner_add_left, irr_cf_inner ha₀mem hamem,
      irr_cf_inner (mem_irreducibleCharacters.mpr ha₂) hamem]
    by_cases h : a₀ = a
    · have h2 : ¬ (a₂ = a) := by rw [← h]; exact ha₂ne
      rw [ite_eq_left h, ite_eq_right h2]
      norm_num
    · rw [ite_eq_right h]
      by_cases h2 : a₂ = a
      · rw [ite_eq_left h2]; norm_num
      · rw [ite_eq_right h2]; norm_num

end Work.BG
