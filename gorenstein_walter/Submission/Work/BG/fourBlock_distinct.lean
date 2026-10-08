import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.L41Aux

open OddOrder.RepresentationTheory

namespace Work.BG

/-- **The four blocks are distinct** (Bender–Glauberman 1981, §4, `|S| = 4`).

With `|H₀/U| = 2` the group `Λ` of linear characters of `H₀/U` is `{1, λ₂}`
(`λ₂ = lamCF C β₂`, `β₂ ≠ 1`), so the `Λ`-orbit of any `ν ∈ Irr(H₀)` is `{ν, λ₂ν}` and the
`⟨s⟩`-orbit of a `Λ`-orbit has at most four elements.  This lemma collects the distinctness
of the four blocks `{μ, λ₂μ, μ^s, λ₂μ^s}` (for `μ` with `μ^s ∉ Λμ`) together with their
separation from the `s`-fixed irreducible `ν₀` (and its blocks `{ν₀, λ₂ν₀}`), and the
irreducibility of each of the twisted/conjugated characters involved.

Proof: `λ₂` is the unique non-trivial element of `Λ` (`lamOrbit_eq`), it is an involution
(`lamCF_two_mul_self`) commuting with `s`-conjugation (`sconj_lam_two_mul`), and
`(λ₂ν)(t) = -ν(t) ≠ 0` (`lam_two_mul_ne_self`, `sconj_ne_lam_two_mul`).  The remaining
separation statements are then formal algebra with the `s`-fixedness of `ν₀` and the
hypothesis that `μ^s` is outside the `Λ`-orbit of `μ`. -/
theorem fourBlock_distinct {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (h2 : Nat.card (Work.BG.quotGroup C.P) = 2)
    {β₂ : Work.BG.quotGroup C.P →* ℂˣ} (hβ₂ : β₂ ≠ 1)
    {ν₀ μ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ}
    (hν₀ : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν₀)
    (hν₀fix : Work.BG.sconj C ν₀ = ν₀)
    (hμ : OddOrder.RepresentationTheory.IsIrreducibleCharacter μ)
    (hμmoved : Work.BG.sconj C μ ∉ Work.BG.lamOrbit C μ) :
    μ ≠ Work.BG.lamCF C β₂ * μ ∧ μ ≠ Work.BG.sconj C μ ∧
    μ ≠ Work.BG.lamCF C β₂ * Work.BG.sconj C μ ∧
    Work.BG.lamCF C β₂ * μ ≠ Work.BG.sconj C μ ∧
    Work.BG.lamCF C β₂ * μ ≠ Work.BG.lamCF C β₂ * Work.BG.sconj C μ ∧
    Work.BG.sconj C μ ≠ Work.BG.lamCF C β₂ * Work.BG.sconj C μ ∧
    ν₀ ≠ μ ∧ ν₀ ≠ Work.BG.lamCF C β₂ * μ ∧ ν₀ ≠ Work.BG.sconj C μ ∧
    ν₀ ≠ Work.BG.lamCF C β₂ * Work.BG.sconj C μ ∧
    Work.BG.lamCF C β₂ * ν₀ ≠ μ ∧ Work.BG.lamCF C β₂ * ν₀ ≠ Work.BG.lamCF C β₂ * μ ∧
    Work.BG.lamCF C β₂ * ν₀ ≠ Work.BG.sconj C μ ∧
    Work.BG.lamCF C β₂ * ν₀ ≠ Work.BG.lamCF C β₂ * Work.BG.sconj C μ ∧
    ν₀ ≠ Work.BG.lamCF C β₂ * ν₀ ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (Work.BG.lamCF C β₂ * μ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (Work.BG.sconj C μ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (Work.BG.lamCF C β₂ * Work.BG.sconj C μ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (Work.BG.lamCF C β₂ * ν₀) := by
  have hμ_orbit : μ ∈ Work.BG.lamOrbit C μ := by
    rw [Work.BG.lamOrbit_eq C h2 hβ₂]; exact Or.inl rfl
  have hlsq : Work.BG.lamCF C β₂ * Work.BG.lamCF C β₂ =
      (linearClassFunction (1 : ↥C.P.H0 →* ℂˣ)) := Work.BG.lamCF_two_mul_self C h2
  have hslam : ∀ ν : ClassFunction ↥C.P.H0 ℂ,
      Work.BG.sconj C (Work.BG.lamCF C β₂ * ν) =
        Work.BG.lamCF C β₂ * Work.BG.sconj C ν := fun ν =>
    Work.BG.sconj_lam_two_mul C h2 hβ₂ ν
  have hll : ∀ a : ClassFunction ↥C.P.H0 ℂ,
      Work.BG.lamCF C β₂ * (Work.BG.lamCF C β₂ * a) = a := by
    intro a
    calc Work.BG.lamCF C β₂ * (Work.BG.lamCF C β₂ * a)
        = (Work.BG.lamCF C β₂ * Work.BG.lamCF C β₂) * a :=
          (Work.BG.mul_assoc_cf _ _ _).symm
      _ = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) * a := by rw [hlsq]
      _ = a := Work.BG.one_mul_cf a
  have hcancel : ∀ {a b : ClassFunction ↥C.P.H0 ℂ},
      Work.BG.lamCF C β₂ * a = Work.BG.lamCF C β₂ * b → a = b := by
    intro a b hab
    have hh := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => Work.BG.lamCF C β₂ * φ) hab
    rwa [hll a, hll b] at hh
  have hmov : Work.BG.sconj C μ ≠ μ := fun h => hμmoved (by rw [h]; exact hμ_orbit)
  have hs_irr : IsIrreducibleCharacter (Work.BG.sconj C μ) :=
    IsIrreducibleCharacter.conjByH C.P C.s hμ
  have hlamν0fix : Work.BG.sconj C (Work.BG.lamCF C β₂ * ν₀) =
      Work.BG.lamCF C β₂ * ν₀ := by rw [hslam ν₀, hν₀fix]
  have h7 : ν₀ ≠ μ := by
    intro h; subst h
    exact hμmoved (by rw [hν₀fix]; exact hμ_orbit)
  have h8 : ν₀ ≠ Work.BG.lamCF C β₂ * μ := by
    intro h
    have hfix : Work.BG.sconj C (Work.BG.lamCF C β₂ * μ) = Work.BG.lamCF C β₂ * μ := by
      rw [← h]; exact hν₀fix
    rw [hslam μ] at hfix
    exact hmov (hcancel hfix)
  have h9 : ν₀ ≠ Work.BG.sconj C μ := by
    intro h
    have hfix : Work.BG.sconj C (Work.BG.sconj C μ) = Work.BG.sconj C μ := by
      rw [← h]; exact hν₀fix
    rw [Work.BG.sconj_sconj] at hfix
    exact hμmoved (by rw [← hfix]; exact hμ_orbit)
  have h10 : ν₀ ≠ Work.BG.lamCF C β₂ * Work.BG.sconj C μ := by
    intro h
    have hfix : Work.BG.sconj C (Work.BG.lamCF C β₂ * Work.BG.sconj C μ) =
        Work.BG.lamCF C β₂ * Work.BG.sconj C μ := by rw [← h]; exact hν₀fix
    rw [hslam (Work.BG.sconj C μ), Work.BG.sconj_sconj] at hfix
    exact hmov (hcancel hfix).symm
  have h13 : Work.BG.lamCF C β₂ * ν₀ ≠ Work.BG.sconj C μ := by
    intro h
    have hfix : Work.BG.sconj C (Work.BG.sconj C μ) = Work.BG.sconj C μ := by
      rw [← h]; exact hlamν0fix
    rw [Work.BG.sconj_sconj] at hfix
    exact hμmoved (by rw [← hfix]; exact hμ_orbit)
  refine ⟨(Work.BG.lam_two_mul_ne_self C h2 hβ₂ hμ).symm, hmov.symm, ?_, ?_, ?_, ?_, h7, h8, h9,
    h10, ?_, ?_, h13, ?_, (Work.BG.lam_two_mul_ne_self C h2 hβ₂ hν₀).symm,
    Work.BG.lam_two_mul_irr C hμ, hs_irr, Work.BG.lam_two_mul_irr C hs_irr,
    Work.BG.lam_two_mul_irr C hν₀⟩
  · intro h
    have hh := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => Work.BG.sconj C φ) h
    rw [hslam (Work.BG.sconj C μ), Work.BG.sconj_sconj] at hh
    exact Work.BG.sconj_ne_lam_two_mul C h2 hβ₂ hμ hh
  · exact (Work.BG.sconj_ne_lam_two_mul C h2 hβ₂ hμ).symm
  · intro h; exact hmov (hcancel h).symm
  · exact (Work.BG.lam_two_mul_ne_self C h2 hβ₂ hs_irr).symm
  · intro h
    have hh := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => Work.BG.lamCF C β₂ * φ) h
    rw [hll ν₀] at hh
    exact h8 hh
  · intro h; exact h7 (hcancel h)
  · intro h; exact h9 (hcancel h)

end Work.BG
