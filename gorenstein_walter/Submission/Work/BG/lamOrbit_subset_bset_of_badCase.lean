import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.inner_coherence_coeff
import Submission.Work.BG.lambda_mul_irreducible

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Step 3 of BG Lemma 3.6 (equality case, part (a)).**  Suppose `Ξ` is a union of `Λ`-orbits
(`hΞorb`), disjoint from `𝒮(χ)` (`hΞfree`), containing the support of `χ|H₀` (`hsupp`), and every
member of `𝒮(χ)` has multiplicity `0` in `χ|H₀` (`hzero`).  Then the `Λ`-orbit of every member of
`𝒮(χ)` is contained in `𝒮(χ)`.

(In the application `Ξ = Ω ∪ Ω^{t₁}`, the support of `χ|H₀` in the equality case; `Ξ` being
`Λ`-orbit-closed — rather than a single `Λ`-orbit — is what makes the statement apply.)

Route: let `ν₀ ∈ 𝒮(χ)` and `ν ∈ Λν₀`.  If `ν ∉ 𝒮(χ)`, then its multiplicity in `χ|H₀` is
`⟨χ|H₀, ν₀⟩ + ⟨χ, fν - fν₀⟩ = 0 + 0 - ⟨χ, fν₀⟩ ≠ 0`, where
`⟨χ, fν - fν₀⟩ = ⟨χ|H₀, ν - ν₀⟩` is `Work.BG.inner_coherence_coeff` (coherence clause
`ind C (ν - ν₀) = fν - fν₀` plus Frobenius reciprocity; `Λ`-equivalent irreducibles stay
irreducible by `Work.BG.lambda_mul_irreducible`), and `⟨χ, fν⟩ = 0` because `ν ∉ 𝒮(χ)`.
So `ν` lies in the support, hence in `Ξ` (`hsupp`); `Λν₀ = Λν ⊆ Ξ` (`hΞorb`), so `ν₀ ∈ Ξ`,
contradicting `hΞfree` since `ν₀ ∈ 𝒮(χ)`. -/
theorem lamOrbit_subset_bset_of_badCase {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hf : Work.GW2.C16.IsCoherent C f)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (Ξ : Set (OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ))
    (hΞorb : ∀ ν ∈ Ξ, Work.BG.lamOrbit C ν ⊆ Ξ)
    (hΞfree : ∀ ν ∈ Ξ, ν ∉ Work.GW2.C16.bset C f χ)
    (hsupp : ∀ ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ν →
      OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ) ν ≠ 0 → ν ∈ Ξ)
    (hzero : ∀ ν ∈ Work.GW2.C16.bset C f χ,
      OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ) ν = 0) :
    ∀ ν₀ ∈ Work.GW2.C16.bset C f χ, Work.BG.lamOrbit C ν₀ ⊆ Work.GW2.C16.bset C f χ := by
  intro ν₀ hν₀ ν hν
  -- `Λ`-equivalence is symmetric, kept aside because `obtain` below clears `hν`
  have hsym : Work.BG.LamEquiv C ν ν₀ := Work.BG.s02c_LamEquiv_symm C hν
  obtain ⟨hν₀irr, hν₀ne⟩ := hν₀
  -- `ν₀ ∈ 𝒮(χ)` has multiplicity `0` in `χ|H₀` by `hzero`
  have hν₀zero : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν₀ = 0 :=
    hzero ν₀ ⟨hν₀irr, hν₀ne⟩
  -- `ν = λ_β · ν₀` is again irreducible
  obtain ⟨β, hβ⟩ := hν
  have hνirr : IsIrreducibleCharacter ν := by
    rw [hβ]
    exact Work.BG.lambda_mul_irreducible C.P ⟨β, rfl⟩ hν₀irr
  refine ⟨hνirr, ?_⟩
  -- suppose `ν ∉ 𝒮(χ)`, i.e. `⟨χ, fν⟩ = 0` (it is irreducible)
  intro hνzero
  -- coherence: `⟨χ, fν - fν₀⟩ = ⟨χ|H₀, ν - ν₀⟩`
  have hcoe : ClassFunction.inner χ (f ν - f ν₀)
      = ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (ν - ν₀) :=
    Work.BG.inner_coherence_coeff C f hf χ hνirr hν₀irr hsym
  -- linearity of the inner product splits off the `ν₀` component
  have hsplit : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν
      = ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν₀
        + ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (ν - ν₀) := by
    conv_lhs => rw [← sub_add_cancel ν ν₀]
    rw [ClassFunction.inner_add_right, add_comm]
  -- so the multiplicity of `ν` in `χ|H₀` is `-⟨χ, fν₀⟩ ≠ 0`
  have hval : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν
      = - ClassFunction.inner χ (f ν₀) := by
    rw [hsplit, hν₀zero, ← hcoe, ClassFunction.inner_sub_right, hνzero, zero_sub, zero_add]
  -- hence `ν` lies in the support of `χ|H₀`, so `ν ∈ Ξ` (`hsupp`)
  have hνmem : ν ∈ Ξ := by
    apply hsupp ν hνirr
    rw [hval]
    exact neg_ne_zero.mpr hν₀ne
  -- `Ξ` is `Λ`-orbit-closed and `ν₀ ∈ Λν`, so `ν₀ ∈ Ξ`
  have hν₀mem : ν₀ ∈ Ξ := hΞorb ν hνmem hsym
  -- ... contradicting `Ξ ∩ 𝒮(χ) = ∅` since `ν₀ ∈ 𝒮(χ)`
  exact hΞfree ν₀ hν₀mem ⟨hν₀irr, hν₀ne⟩

end Work.BG
