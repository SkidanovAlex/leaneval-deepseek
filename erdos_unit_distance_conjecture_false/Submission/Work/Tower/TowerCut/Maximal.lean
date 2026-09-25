import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.TowerCut.Basic
import Submission.Work.Tower.TowerCut.Transfer
import Submission.Work.Tower.TowerCut.finite_setOf_unramified

/-!
# The maximal admissible extension (tower cutting, Step 2)

Fix a number field `F`, a finite set `T` of primes of `F` and a bound `N₀`.  We consider the
"good" extensions of `F`: finite everywhere-unramified Galois extensions with `3`-group Galois
group in which every prime of `T` splits completely, of degree `< N₀` over `ℚ`.  `goodImages` is
the set of images of such extensions inside a fixed algebraic closure `F̄ = AlgebraicClosure F`.

Hermite's theorem (here: `TowerCut.finite_setOf_unramified`) shows that this set is finite, so
its supremum `K` is a finite extension of `F`; it is the maximal good extension, and every good
extension embeds into it.  The properties of `K` are collected in `Main`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace TowerCut

variable {F : Type*} [Field F] [NumberField F]

/-- The set of images, inside `AlgebraicClosure F`, of the "good" extensions of `F`: finite
everywhere-unramified Galois `3`-group extensions of degree `< N₀` over `ℚ` in which every
prime of `T` splits completely. -/
def goodImages (F : Type*) [Field F] [NumberField F] (T : Finset (Ideal (𝓞 F))) (N₀ : ℕ) :
    Set (IntermediateField F (AlgebraicClosure F)) :=
  {M | ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
        (_ : FiniteDimensional F L) (_ : IsGalois F L) (ψ : L →ₐ[F] AlgebraicClosure F),
      IsUnramifiedExtension F L ∧ IsPGroup 3 (Gal(L/F)) ∧
        (∀ 𝔭 ∈ T, SplitsCompletelyIn F L 𝔭) ∧ Module.finrank ℚ L < N₀ ∧
        M = ψ.fieldRange}

/-- The properties of an element of `goodImages`: it is a finite-dimensional everywhere
unramified Galois extension of `F` with `3`-group Galois group and degree `< N₀` over `ℚ`. -/
theorem goodImages_spec {T : Finset (Ideal (𝓞 F))} {N₀ : ℕ}
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ goodImages F T N₀) :
    FiniteDimensional F M ∧ IsUnramifiedExtensionForallPrimes F ↥M ∧ IsGalois F ↥M ∧
      IsPGroup 3 (Gal(↥M/F)) ∧ Module.finrank ℚ ↥M < N₀ := by
  obtain ⟨L, _, _, _, _, _, ψ, hunr, h3, -, hlt, hMeq⟩ := hM
  have hinj : Function.Injective ψ := ψ.injective
  have e : L ≃ₐ[F] ↥(ψ.fieldRange) := AlgEquiv.ofInjective ψ hinj
  haveI hfd : FiniteDimensional F ↥(ψ.fieldRange) := finiteDimensional_of_algEquiv e
  haveI hnf : NumberField ↥(ψ.fieldRange) := NumberField.of_module_finite F ↥(ψ.fieldRange)
  have hunr' : IsUnramifiedExtensionForallPrimes F L := hunr.forallPrimes
  subst hMeq
  refine ⟨hfd, isUnramifiedExtensionForallPrimes_of_algEquiv e hunr', IsGalois.of_algEquiv e,
    isPGroup_gal_of_algEquiv e h3, ?_⟩
  have hfin : Module.finrank ℚ L = Module.finrank ℚ ↥(ψ.fieldRange) :=
    (e.toLinearEquiv.restrictScalars ℚ).finrank_eq
  rw [← hfin]
  exact hlt

/-- `goodImages` is finite: Hermite's theorem. -/
theorem goodImages_finite (T : Finset (Ideal (𝓞 F))) (N₀ : ℕ) :
    (goodImages F T N₀).Finite :=
  (finite_setOf_unramified F N₀).subset fun M hM =>
    let h := goodImages_spec hM
    ⟨h.1, h.2.1, le_of_lt h.2.2.2.2⟩

end TowerCut
end Tower
end Work
