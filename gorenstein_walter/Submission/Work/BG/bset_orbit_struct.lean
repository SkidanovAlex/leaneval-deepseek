import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_assemblyFull
import Submission.Work.BG.s02_dcf_mem_irr
import Submission.Work.BG.inner_pmIrr_eq_pm_one

/-!
# Area BG: the orbit structure of `𝒮(χ) = bset C f χ`

For a coherent map `f` (BG Coherence Theorem 2.3, `Work.GW2.C16.IsCoherent`) and a signed
irreducible character `χ` of `G`, the `f`-support `𝒮(χ) = bset C f χ` (BG p. 207) has the
following structure.

1. It is stable under `ν ↦ ν^s`, with `f (ν^s) = f ν` (both are literally clause (ii) of
   `GoodOn`, i.e. `ν̃^s = ν̃` — coherence on the third term is *not* needed), and every
   `(χ, f ν)` is `±1`: `f ν ∈ ℤ[Irr G]` has norm `1` or `2`, so the Fourier coefficient of
   a signed irreducible character is an integer with `m² ≤ 2`, and it is nonzero on
   `𝒮(χ)`.
2. Two `Λ`-equivalent members of `𝒮(χ)` are equal or `s`-conjugate: if `μ ≠ ν` and
   `μ ≠ sconj C ν`, coherence clause (iii) makes `f μ` and `f ν` orthogonal (disjoint
   supports in `Irr G`), yet both meet the signed irreducible `χ`.

Neither part uses the algebraic-integrality or value clauses of coherence: everything is
read off `GoodOn` at the key `orbitKey C ν` together with `inner_pmIrr_eq_pm_one`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- The inner product is conjugate-symmetric up to `star`, so non-vanishing is symmetric. -/
private theorem inner_ne_zero_comm {K : Type} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {a b : ClassFunction K ℂ}
    (h : ClassFunction.inner a b ≠ 0) : ClassFunction.inner b a ≠ 0 := by
  intro h0
  refine h ?_
  rw [ClassFunction.inner_star_comm, h0, star_zero]

/-- A signed irreducible character that is not orthogonal to both `a` and `b` prevents
`a` and `b` from being disjoint (having no common irreducible constituent). -/
private theorem not_disjointCF_of_inner_ne_zero {K : Type} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {a b χ : ClassFunction K ℂ}
    (hχ : IsPmIrr χ) (ha : ClassFunction.inner χ a ≠ 0)
    (hb : ClassFunction.inner χ b ≠ 0) : ¬ DisjointCF a b := by
  have ha' := inner_ne_zero_comm ha
  have hb' := inner_ne_zero_comm hb
  intro hd
  rcases hχ with hχ | hχ
  · rcases hd (⟨χ, hχ⟩ : IrreducibleCharacter K) with h | h
    · exact ha' h
    · exact hb' h
  · rcases hd (⟨-χ, hχ⟩ : IrreducibleCharacter K) with h | h
    · rw [ClassFunction.inner_neg_right] at h
      exact ha' (neg_eq_zero.mp h)
    · rw [ClassFunction.inner_neg_right] at h
      exact hb' (neg_eq_zero.mp h)

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem bset_orbit_struct {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    (∀ ν ∈ bset C f χ, sconj C ν ∈ bset C f χ ∧ f (sconj C ν) = f ν ∧
       (ClassFunction.inner χ (f ν) = 1 ∨ ClassFunction.inner χ (f ν) = -1)) ∧
    (∀ ν ∈ bset C f χ, ∀ μ ∈ bset C f χ, LamEquiv C ν μ → μ ≠ ν → μ = sconj C ν) := by
  classical
  constructor
  · -- **(1)** `𝒮(χ)` is `s`-stable and `(χ, ν̃) = ±1` on it.
    rintro ν ⟨hνirr, hνne⟩
    -- coherence at the key `Λν ∪ (Λν)^s`, read off at the pair `(ν, ν)`
    have hkey := (hf.1 ν hνirr) ν (Or.inl (s02c_LamEquiv_refl C ν)) ν
      (Or.inl (s02c_LamEquiv_refl C ν)) hνirr hνirr
    refine ⟨⟨?_, ?_⟩, hkey.2.1, ?_⟩
    · -- `ν^s` is again irreducible
      show IsIrreducibleCharacter (conjByH C.P C.s ν)
      exact IsIrreducibleCharacter.conjByH C.P C.s hνirr
    · -- and `f (ν^s) = f ν`, so the coefficient is the same, hence nonzero
      rw [hkey.2.1]
      exact hνne
    · -- `f ν ∈ ℤ[Irr G]` has norm `1` or `2`; the coefficient of the signed irreducible
      -- `χ` is a nonzero integer of square at most `2`, hence `±1`
      refine inner_pmIrr_eq_pm_one hkey.1 ?_ hχ hνne
      have h := hkey.2.2.1
      by_cases hss : sconj C ν = ν
      · exact Or.inr (by simpa [hss] using h)
      · exact Or.inl (by simpa [hss] using h)
  · -- **(2)** `Λ`-equivalent members of `𝒮(χ)` are equal or `s`-conjugate.
    rintro ν ⟨hνirr, hνne⟩ μ ⟨hμirr, hμne⟩ hLam hne
    by_contra hconj
    -- coherence at the key `Λν ∪ (Λν)^s`, read off at the pair `(μ, ν)`
    have hkey := (hf.1 ν hνirr) μ (Or.inl hLam) ν (Or.inl (s02c_LamEquiv_refl C ν))
      hμirr hνirr
    exact not_disjointCF_of_inner_ne_zero hχ hμne hνne
      (hkey.2.2.2.2.1 (s02c_LamEquiv_symm C hLam) hne hconj)

end Work.BG
