import Mathlib
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.lamOrbitOfU_inner_eq_zero_or_one

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-! ## Auxiliary computation with `ClassFunction.inner` -/

section InnerAux

variable {Y : Type*} [Group Y] [Finite Y] [Fintype Y] [Invertible (Nat.card Y : ℂ)]

/-- Expansion of `⟨a + b, a + b'⟩` when `a` is orthogonal to `b'` (on the right) and `b` to `a`
(on the left). -/
private lemma inner_add_add_eq_one_add (a b b' : ClassFunction Y ℂ)
    (ha : IsIrreducibleCharacter a)
    (hb' : ClassFunction.inner a b' = 0) (hb : ClassFunction.inner b a = 0) :
    ClassFunction.inner (a + b) (a + b') = 1 + ClassFunction.inner b b' := by
  rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right, ClassFunction.inner_add_right,
    inner_self_eq_one a ha, hb', hb]
  ring

/-- `b = 0` or `b` an irreducible character different from `a` makes `b` orthogonal to `a`
on the left. -/
private lemma inner_eq_zero_of_eq_zero_or_irr_ne {a b : ClassFunction Y ℂ}
    (ha : IsIrreducibleCharacter a)
    (hb : b = 0 ∨ (IsIrreducibleCharacter b ∧ b ≠ a)) :
    ClassFunction.inner b a = 0 := by
  rcases hb with h | ⟨hirr, hne⟩
  · rw [h, ClassFunction.inner_zero_left]
  · rw [irr_cf_inner (mem_irreducibleCharacters.mpr hirr) (mem_irreducibleCharacters.mpr ha),
      ite_eq_right hne]

/-- `b' = 0` or `b'` an irreducible character different from `a` makes `a` orthogonal to `b'`
on the right. -/
private lemma inner_eq_zero_of_eq_zero_or_irr_ne' {a b' : ClassFunction Y ℂ}
    (ha : IsIrreducibleCharacter a)
    (hb' : b' = 0 ∨ (IsIrreducibleCharacter b' ∧ b' ≠ a)) :
    ClassFunction.inner a b' = 0 := by
  rcases hb' with h | ⟨hirr, hne⟩
  · rw [h, ClassFunction.inner_zero_right]
  · rw [irr_cf_inner (mem_irreducibleCharacters.mpr ha) (mem_irreducibleCharacters.mpr hirr),
      ite_eq_right (fun h => hne h.symm)]

/-- If `a ∈ Irr(Y)` and `b, b'` are each either `0` or an irreducible character different from
`a`, then `⟨a + b, a + b'⟩ ≠ 0`.  Explicitly `⟨a + b, a + b'⟩ = 1 + ⟨b, b'⟩ ∈ {1, 2}`. -/
private lemma inner_add_add_ne_zero (a b b' : ClassFunction Y ℂ)
    (ha : IsIrreducibleCharacter a)
    (hb : b = 0 ∨ (IsIrreducibleCharacter b ∧ b ≠ a))
    (hb' : b' = 0 ∨ (IsIrreducibleCharacter b' ∧ b' ≠ a)) :
    ClassFunction.inner (a + b) (a + b') ≠ 0 := by
  rw [inner_add_add_eq_one_add a b b' ha (inner_eq_zero_of_eq_zero_or_irr_ne' ha hb')
    (inner_eq_zero_of_eq_zero_or_irr_ne ha hb)]
  rcases hb with h | ⟨hbirr, -⟩
  · rw [h, ClassFunction.inner_zero_left]; norm_num
  rcases hb' with h | ⟨hb'irr, -⟩
  · rw [h, ClassFunction.inner_zero_right]; norm_num
  rw [irr_cf_inner (mem_irreducibleCharacters.mpr hbirr) (mem_irreducibleCharacters.mpr hb'irr)]
  split_ifs <;> norm_num

end InnerAux

/-! ## The shape of `ν|_U` split off the constituent `a` -/

section Split

/-- **`ν|_U = a + b` with `b` either `0` or an irreducible `≠ a`.**  If `a ∈ Irr(U)` occurs in
`ν|_U` for `ν ∈ Irr(H₀)`, then `Work.BG.rem31Shape` (`ν|_U = a₀` or `ν|_U = a₀ + a₂`) forces
`a` to be one of the displayed constituents (orthonormality; in the case `ν|_U = a₀` one gets
`a₀ = a`), and the remainder is the other constituent, or nothing. -/
private lemma exists_split_of_constituent {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    (hS3 : Work.GW2.C16.Sec3Hyp D)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    {a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ} (ha : IsIrreducibleCharacter a)
    (hconva : ClassFunction.inner (ClassFunction.restrict (Work.GW2.C16.Uin C) ν) a ≠ 0) :
    ∃ b : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ,
      ClassFunction.restrict (Work.GW2.C16.Uin C) ν = a + b ∧
        (b = 0 ∨ (IsIrreducibleCharacter b ∧ b ≠ a)) := by
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨a₀, ha₀, hcase⟩ := rem31Shape D C hDC hS3 ν hν
  have ha₀mem : a₀ ∈ irreducibleCharacters ↥(Uin C) := mem_irreducibleCharacters.mpr ha₀
  have hamem : a ∈ irreducibleCharacters ↥(Uin C) := mem_irreducibleCharacters.mpr ha
  rcases hcase with ⟨hνU, -⟩ | ⟨a₂, ha₂, ha₂ne, -, hνU, -⟩
  · -- `ν|_U = a₀`: orthonormality together with `hconva` forces `a₀ = a`
    have h0 : ClassFunction.inner a₀ a ≠ 0 := by rw [← hνU]; exact hconva
    rw [irr_cf_inner ha₀mem hamem] at h0
    have heq : a₀ = a := by
      by_contra h
      exact h0 (by rw [ite_eq_right h])
    exact ⟨0, by rw [hνU, heq, add_zero], Or.inl rfl⟩
  · -- `ν|_U = a₀ + a₂`: `a` is one of the two constituents
    have h0 : ClassFunction.inner (a₀ + a₂) a ≠ 0 := by rw [← hνU]; exact hconva
    rw [ClassFunction.inner_add_left, irr_cf_inner ha₀mem hamem,
      irr_cf_inner (mem_irreducibleCharacters.mpr ha₂) hamem] at h0
    by_cases h1 : a₀ = a
    · refine ⟨a₂, by rw [hνU, h1], Or.inr ⟨ha₂, fun h => ha₂ne (h.trans h1.symm)⟩⟩
    · have h2 : a₂ = a := by
        by_contra h2
        exact h0 (by rw [ite_eq_right h1, ite_eq_right h2, add_zero])
      exact ⟨a₀, by rw [hνU, h2]; exact add_comm a₀ a, Or.inr ⟨ha₀, h1⟩⟩

end Split

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **The `U`-constituents lying in a common `Λ`-orbit are `Λ`-equivalent.**  If `ν, ν' ∈ Irr(H₀)`
both have `a ∈ Irr(U)` as a constituent of their restriction to `U`, then `LamEquiv C ν ν'`.

Route: `Work.BG.rem31Orth D C` says `⟨ν|_U, ν'|_U⟩ = D.n / |Λν'|` when `LamEquiv C ν ν'`, and
`0` otherwise; so it suffices to show `⟨ν|_U, ν'|_U⟩ ≠ 0`.

Write `ν|_U = a + b` and `ν'|_U = a + b'` with `b` (resp. `b'`) either `0` or an irreducible
`≠ a`: indeed `Work.BG.rem31Shape` gives `ν|_U = a₀` or `a₀ + a₂`, and
`Work.BG.lamOrbitOfU_inner_eq_zero_or_one` together with `hconva ≠ 0` forces `a` to be one of
the displayed constituents (in the case `ν|_U = a₀` one gets `a₀ = a` from orthonormality).
Then `⟨a+b, a+b'⟩ = ⟨a,a⟩ + ⟨a,b'⟩ + ⟨b,a⟩ + ⟨b,b'⟩ = 1 + 0 + 0 + ⟨b,b'⟩` with `⟨b,b'⟩ ∈ {0,1}`
(orthonormality; `⟨a,b'⟩`, `⟨b,a⟩` vanish as `b,b' ≠ a` or `0`), hence `⟨ν|_U,ν'|_U⟩ ∈ {1,2}`
is nonzero.  Uses `ClassFunction.inner_add_left`/`inner_add_right` and `irr_cf_inner`.
`Invertible (Nat.card G : ℂ)` is synthesised automatically from `[Fintype G]`. -/
theorem lamOrbitOfU_lamEquiv {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    (hS3 : Work.GW2.C16.Sec3Hyp D)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    {ν ν' : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    (hν' : IsIrreducibleCharacter ν')
    {a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ} (ha : IsIrreducibleCharacter a)
    (h1 : ClassFunction.inner (ClassFunction.restrict (Work.GW2.C16.Uin C) ν) a ≠ 0)
    (h2 : ClassFunction.inner (ClassFunction.restrict (Work.GW2.C16.Uin C) ν') a ≠ 0) :
    LamEquiv C ν ν' := by
  classical
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨b, hb, hbshape⟩ := exists_split_of_constituent D C hDC hS3 hν ha h1
  obtain ⟨b', hb', hb'shape⟩ := exists_split_of_constituent D C hDC hS3 hν' ha h2
  have hne : ClassFunction.inner (ClassFunction.restrict (Uin C) ν)
      (ClassFunction.restrict (Uin C) ν') ≠ 0 := by
    rw [hb, hb']
    exact inner_add_add_ne_zero a b b' ha hbshape hb'shape
  by_contra hcon
  exact hne ((rem31Orth D C hDC ν ν' hν hν').2 hcon)

end Work.BG
