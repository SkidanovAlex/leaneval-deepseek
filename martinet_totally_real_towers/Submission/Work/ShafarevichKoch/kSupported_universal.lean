import Mathlib
import Submission.Work.ShafarevichKoch.SupportedTower

/-!
# `Work.ShafarevichKoch.kSupported_universal` -- the universal property of `k_∅`

The maximal pro-`2` extension `k_∅ = kSupported F 2 ∅` of a number field `F` unramified at *every*
finite prime is universal: every finite Galois pro-`2` extension `M/F` with trivial relative
different embeds into it as an `F`-algebra.

The proof has no arithmetic content beyond "a prime ideal dividing the unit ideal is the unit
ideal": a prime `P ∣ ⊤` would force `P = ⊤`, which is impossible for a prime ideal of the Dedekind
domain `𝓞 M`.  Hence the `S = ∅` support condition on the different is vacuous for `M`, and `M`
is one of the fields whose supremum defines `kSupported F 2 ∅`.

Concretely: transport `M` into the algebraic closure `Ω = AlgebraicClosure F` along some
`F`-embedding `e : M →ₐ[F] Ω` (available by `IsAlgClosed.lift`), producing the intermediate field
`e.fieldRange ≤ Ω`, which is finite dimensional, Galois, pro-`2` and has `∅`-supported different;
then `e.fieldRange ≤ k_∅` by the defining supremum.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **Universality of `k_∅`.**  Every finite Galois pro-`2` extension of `F` with trivial relative
different embeds into the maximal everywhere-unramified pro-`2` extension of `F`. -/
theorem kSupported_universal (F : Type) [Field F] [NumberField F]
    (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M]
    (hpg : IsPGroup 2 (M ≃ₐ[F] M))
    (hdiff : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers M) = ⊤) :
    ∃ φ : M →ₐ[F] ↥(kSupported F 2 (∅ : Finset ℕ)), True := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the support condition is vacuous for `M`
  have hsuppM : ∀ (P : Ideal (NumberField.RingOfIntegers M)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers M) →
        ∃ q ∈ (∅ : Finset ℕ),
          P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
    intro P hP _ hdvd
    rw [hdiff] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hle : (⊤ : Ideal (NumberField.RingOfIntegers M)) ≤ P := by
      rw [hc]
      exact Ideal.mul_le_left
    exact absurd (top_le_iff.mp hle) hP.ne_top
  -- embed `M` into the algebraic closure of `F`
  let Ω := AlgebraicClosure F
  let e : M →ₐ[F] Ω := IsAlgClosed.lift (R := F) (S := M) (M := Ω)
  let eeq : M ≃ₐ[F] ↥e.fieldRange := AlgEquiv.ofInjectiveField e
  haveI hfdL : FiniteDimensional F ↥(e.fieldRange) := eeq.toLinearEquiv.finiteDimensional
  haveI hgalL : IsGalois F ↥(e.fieldRange) := IsGalois.of_algEquiv eeq
  haveI hnumL : NumberField ↥(e.fieldRange) :=
    NumberField.of_module_finite F ↥(e.fieldRange)
  have hpgL : IsPGroup 2 (↥(e.fieldRange) ≃ₐ[F] ↥(e.fieldRange)) :=
    hpg.of_equiv (AlgEquiv.autCongr eeq)
  have hsuppL : ∀ (P : Ideal (NumberField.RingOfIntegers ↥(e.fieldRange))), P.IsPrime →
      P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers ↥(e.fieldRange)) →
        ∃ q ∈ (∅ : Finset ℕ), P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    Submission.NumberField.differentIdeal_supp_of_algEquiv (F := F) (∅ : Finset ℕ) eeq hsuppM
  -- `e.fieldRange` is one of the fields in the supremum defining `k_∅`
  have hle : e.fieldRange ≤ kSupported F 2 (∅ : Finset ℕ) :=
    le_iSup (fun i : Submission.NumberField.SupportedPField F 2 (∅ : Finset ℕ) => i.L)
      { L := e.fieldRange, hfd := hfdL, hgal := hgalL, hnum := hnumL,
        hpg := hpgL, hsupp := hsuppL }
  exact ⟨(IntermediateField.inclusion hle).comp eeq.toAlgHom, trivial⟩

end Work.ShafarevichKoch
