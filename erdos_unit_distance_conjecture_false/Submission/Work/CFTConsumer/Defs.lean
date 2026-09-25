import Mathlib
import Submission.CFTLib.Interfaces
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Unramified.All
import Submission.Work.Tower.Shafarevich.Defs

/-!
# Vocabulary for the CFTLib consumer

This file fixes the two notions in which the consumer of the shared class-field-theory
interfaces (`Submission/CFTLib/Interfaces.lean`) states its results:

* `Work.CFTConsumer.EFOne F L 𝔭` — the ramification–inertia form of complete splitting: every
  prime of `𝓞 L` above `𝔭` has ramification index `1` and inertia degree `1` over `𝓞 F`.
  This is the form in which the compositum and transport lemmas of
  `Work.Tower.Unramified` are stated (`ef_one_of_algHom`, `compositum_ramification_inertia`),
  and it is equivalent to `Work.Tower.SplitsCompletelyIn F L 𝔭` for a nonzero prime `𝔭`.

* `Work.CFTConsumer.WeakShaf C₀` — Shafarevich's relation-rank estimate in the form supplied by
  `CFTLib.ShafBound`: the bound is asserted only for the finite everywhere-unramified Galois
  `3`-extension `K/F` which is maximal among those in which a finite set `T` of *nonzero* primes
  splits completely *and in which `T` itself splits completely* (the extra hypothesis that
  `CFTLib.ShafBound` requires, and which holds in the tower-cutting application where `K` is
  constructed as the supremum of the `T`-split extensions, cf. `Work.Tower.TowerCut.goodImages`).
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.CFTConsumer

/-- **Ramification–inertia form of complete splitting.**  Every prime of `𝓞 L` lying over `𝔭`
has ramification index `1` and inertia degree `1` over `𝓞 F`. -/
def EFOne (F L : Type) [Field F] [Field L] [Algebra F L] (𝔭 : Ideal (𝓞 F)) : Prop :=
  ∀ P : 𝔭.primesOver (𝓞 L), P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1

/-- `EFOne` implies complete splitting, for `𝔭` a nonzero prime. -/
theorem EFOne.splitsCompletelyIn {F L : Type} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥) (h : EFOne F L 𝔭) :
    Work.Tower.SplitsCompletelyIn F L 𝔭 :=
  Work.Tower.Unramified.splitsCompletelyIn_of_NF h𝔭 h0
    (Work.Tower.Unramified.splitsCompletelyInNF_of_ramification_inertia h𝔭 h)

/-- Complete splitting implies `EFOne`, for `𝔭` a nonzero prime. -/
theorem EFOne.of_splitsCompletelyIn {F L : Type} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] {𝔭 : Ideal (𝓞 F)} (h0 : 𝔭 ≠ ⊥)
    (h : Work.Tower.SplitsCompletelyIn F L 𝔭) : EFOne F L 𝔭 :=
  Work.Tower.Unramified.ef_eq_one_of_splitsCompletelyIn h0 h

/-- `EFOne` descends along an injective `F`-algebra map of number fields. -/
theorem EFOne.of_algHom {F L L' : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Field L'] [NumberField L'] [Algebra F L] [Algebra F L'] [FiniteDimensional F L]
    [FiniteDimensional F L'] {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥)
    (φ : L' →ₐ[F] L) (h : EFOne F L 𝔭) : EFOne F L' 𝔭 :=
  Work.Tower.Unramified.CSCA.ef_one_of_algHom h𝔭 h0 φ h

/-- `EFOne` is invariant under an `F`-algebra isomorphism. -/
theorem EFOne.of_algEquiv {F L L' : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Field L'] [NumberField L'] [Algebra F L] [Algebra F L'] [FiniteDimensional F L]
    [FiniteDimensional F L'] {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥)
    (e : L ≃ₐ[F] L') (h : EFOne F L 𝔭) : EFOne F L' 𝔭 :=
  EFOne.of_algHom h𝔭 h0 e.symm.toAlgHom h

/-- **The Shafarevich estimate in the form supplied by `CFTLib.ShafBound`.**  For a totally real
cubic field `F`, a finite everywhere-unramified Galois `3`-extension `K/F`, and a finite set `T` of
nonzero primes of `F` which splits completely in `K`, is Frobenius-trivial in the Frattini quotient
and with respect to which `K` is maximal among the `T`-split extensions, the pro-`3` relation rank
of `Gal(K/F)` exceeds its generator rank by at most `C₀ + |T|`. -/
def WeakShaf (C₀ : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Module.finrank ℚ F = 3 →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      ∀ (T : Finset (Ideal (𝓞 F))), (∀ 𝔭 ∈ T, 𝔭.IsPrime) → (∀ 𝔭 ∈ T, 𝔭 ≠ ⊥) →
        Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T →
        Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T →
        (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F K 𝔭) →
        Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F)) ≤
          Work.Tower.generatorRank (Gal(K/F)) + C₀ + T.card

end Work.CFTConsumer
