import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.CharBridge
import Submission.Work.BG.restrictEqOfInvariantConstituent

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Remark 3.1 (BG 1981, p. 208), case `|Λν| = m`.** For an irreducible `ν` of `H₀` whose `Λ`-orbit has `m = |H₀ : U| = D.n` elements, `ν|_U` is a single irreducible character of `U` that is invariant under all of `H₀`. (Proof sketch: `Work.BG.rem31Orth` gives `(ν|_U, ν|_U)_U = D.n / |Λν| = 1`; a class function of norm `1` that is a genuine character is a single irreducible character `a`; Clifford's single-orbit theorem (`OddOrder.RepresentationTheory.restrictionConstituentsSingleOrbit_of_isIrreducible` in `Submission.OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit`) applied to `conjBy g a`, which still lies over `ν`, forces `conjBy g a = a`.) -/
theorem lemma33ShapeA {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(Work.GW2.C16.Uin C)] [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (hDC : Work.GW2.C16.Compat D C)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    (hn : (Work.BG.lamOrbit C ν).ncard = D.n) :
    ∃ a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ, IsIrreducibleCharacter a ∧
      ClassFunction.restrict (Work.GW2.C16.Uin C) ν = a ∧
      (∀ g : ↥C.P.H0, ClassFunction.conjBy (G := ↥C.P.H0)
        (H := Work.GW2.C16.Uin C) g a = a) := by
  classical
  -- `rem31Orth` at `μ = ν = ν` (`LamEquiv` is reflexive) gives `(ν|_U, ν|_U)_U = n / |Λν| = 1`.
  have horth := (rem31Orth D C hDC ν ν hν hν).1 (s02c_LamEquiv_refl C ν)
  have hnorm : ClassFunction.inner (ClassFunction.restrict (Uin C) ν)
      (ClassFunction.restrict (Uin C) ν) = 1 := by
    rw [horth, hn, div_self]
    have hn0 : D.n ≠ 0 := by have h := D.two_le; omega
    exact_mod_cast hn0
  -- the degree of `ν|_U` is a positive natural number
  obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ⟨ν, hν⟩
  have hpos : ∃ e : ℕ, 0 < e ∧
      (ClassFunction.restrict (Uin C) ν : ↥(Uin C) → ℂ) 1 = (e : ℂ) :=
    ⟨d, hdpos, by simpa [ClassFunction.restrict_apply] using hd⟩
  -- `ν|_U` is a virtual character of norm `1` and positive degree, hence irreducible
  have hmem : ClassFunction.restrict (Uin C) ν ∈ ZIrr ↥(Uin C) :=
    ClassFunction.restrict_mem_ZIrr (Uin C) hν.mem_ZIrr
  have hirr : IsIrreducibleCharacter (ClassFunction.restrict (Uin C) ν) :=
    isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos hmem hnorm hpos
  refine ⟨ClassFunction.restrict (Uin C) ν, hirr, rfl, ?_⟩
  -- invariance: `ν|_U` is a class function of `H₀`, so `H₀`-conjugates have equal values
  intro g
  ext u
  simp only [ClassFunction.conjBy_apply, ClassFunction.restrict_apply]
  exact ClassFunction.conj_eq ν u g

end Work.BG
