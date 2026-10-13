import Mathlib
import Submission.Work.DSEQ0.CechImageModel

/-!
# Vanishing of `cechZ` from vanishing of `cech`

`DSMap.cechZ A X f U` is the same Čech complex as `DSMap.cech A X f U`, but reindexed by `ℤ`
(it is the extension `(cech A X f U).extend ComplexShape.embeddingUpNat`).  Two general facts
about such an extension give the transfer of vanishing statements:

* in degrees `i < 0` the complex is concentrated in nonnegative degrees
  (`CochainComplex.IsStrictlyGE _ 0`), so its homology vanishes;
* in degrees `(n : ℤ)` with `n : ℕ` the homology is the homology of the original complex, via
  `HomologicalComplex.extendHomologyIso`.

Hence vanishing of the `ℕ`-indexed homology in all degrees `≥ Nat.card ι` implies vanishing of
the `ℤ`-indexed homology in all degrees `≥ Nat.card ι`.
-/

universe a

namespace Work.DSEQ0

theorem cechZ_of_cech_isZero {A : Type a} [CommRing A] {X : AlgebraicGeometry.Scheme.{a}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (h : ∀ n : ℕ, Nat.card ι ≤ n → CategoryTheory.Limits.IsZero ((DSMap.cech A X f U).homology n)) :
    ∀ i : ℤ, (Nat.card ι : ℤ) ≤ i → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i) := by
  intro i hi
  rcases lt_or_ge i 0 with hneg | hpos
  · -- negative degrees: the extension lives in degrees `≥ 0`
    rw [show DSMap.cechZ A X f U
        = (DSMap.cech A X f U).extend ComplexShape.embeddingUpNat from rfl]
    exact CochainComplex.isZero_of_isGE _ 0 i hneg
  · -- nonnegative degrees: transfer along `extendHomologyIso`
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    exact ((HomologicalComplex.extendHomologyIso (DSMap.cech A X f U)
        ComplexShape.embeddingUpNat rfl).isZero_iff).mpr
      (h n (by exact_mod_cast hi))

end Work.DSEQ0
