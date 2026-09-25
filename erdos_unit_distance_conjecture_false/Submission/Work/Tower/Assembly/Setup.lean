import Submission.Work.Tower.Defs
import Submission.Work.Defs.Basic
import Submission.Work.Tower.Glue.TowerParams

/-!
# Assembly: the two remaining inputs, and basic consequences

This file states the two remaining inputs of the project (the cyclotomic base of the tower, built
in `Submission/Work/Tower/CyclotomicBase/`, and S̆afarevič's relation-rank estimate, built in
`Submission/Work/Tower/Shafarevich/`) and derives the elementary consequences used by the
assembly.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace Assembly

/-- The interface of the cyclotomic base of the tower (paper Proposition 3.2), in the literal
`IntermediateField` shape in which the area `Tower/CyclotomicBase` produces it.

This is the hypothesis of `Work.Tower.Assembly.exists_tower_intermediateField`.  The main theorem
`Work.Tower.Assembly.exists_tower_of_base_and_shafarevich` uses the equivalent "bare type" form
`PackagedBaseInterface` below instead, because the two canonical `ℚ`-module structures on
`↥F` for `F : IntermediateField ℚ M` (`IntermediateField.module'` and
`Algebra.toModule F.algebra'`) are not definitionally equal, so `Module.finrank ℚ ↥F` cannot be
passed between the statement of this interface and the already proved areas; see the module
docstring of `Submission/Work/Tower/Assembly/Main.lean`. -/
def BaseInterface : Prop :=
  ∀ (ℓ : ℕ) (r : Fin ℓ → ℕ), (∀ i, Nat.Prime (r i)) → (∀ i, r i % 3 = 1) →
    Function.Injective r →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ℚ M) (_ : IsGalois ℚ M)
      (F : IntermediateField ℚ M),
      Module.finrank ℚ ↥F = 3 ∧ IsGalois ℚ ↥F ∧ NumberField.IsTotallyReal ↥F ∧
      IsAbelianGalois ↥F M ∧ Module.finrank ↥F M = 3 ^ (ℓ - 1) ∧
      (∀ σ : Gal(M/↥F), σ ^ 3 = 1) ∧ IsUnramifiedExtension ↥F M ∧
      |NumberField.discr ↥F| = ((∏ i, r i : ℕ) : ℤ) ^ 2

/-- The same interface as `BaseInterface`, in the shape actually consumed by
`Work.Tower.Assembly.exists_tower_of_base_and_shafarevich`: `F` is a bare type carrying its own
type-class data and `M` is an `F`-algebra.  This is *documentation only*: the main theorem states
the interface inline in its binder, because wrapping it in a `def` would block dependent
elimination of the inner `∃`.  The bridge
`Work.Tower.Assembly.exists_tower_intermediateField` shows that the two forms are interchangeable.
-/
def PackagedBaseInterface : Prop :=
  ∀ (ℓ : ℕ) (r : Fin ℓ → ℕ), (∀ i, Nat.Prime (r i)) → (∀ i, r i % 3 = 1) →
    Function.Injective r →
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyReal F)
      (_ : IsGalois ℚ F)
      (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra F M)
      (_ : FiniteDimensional F M) (_ : IsGalois F M),
      Module.finrank ℚ F = 3 ∧ IsAbelianGalois F M ∧ Module.finrank F M = 3 ^ (ℓ - 1) ∧
      (∀ σ : Gal(M/F), σ ^ 3 = 1) ∧ IsUnramifiedExtension F M ∧
      |NumberField.discr F| = ((∏ i, r i : ℕ) : ℤ) ^ 2

/-- The interface of S̆afarevič's relation-rank estimate (once `K` is maximal among the
`T`-split everywhere-unramified `3`-extensions of `F`).  This is the hypothesis `hshaf` of
`Work.Tower.Assembly.exists_tower_of_base_and_shafarevich`, verbatim. -/
def ShafarevichInterface : Prop :=
  ∃ C₀ : ℕ,
    ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
      Module.finrank ℚ F = 3 →
      ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
        IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
        ∀ (T : Finset (Ideal (𝓞 F))), (∀ 𝔭 ∈ T, 𝔭.IsPrime) →
          (∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
             [FiniteDimensional F L] [IsGalois F L],
             IsUnramifiedExtension F L → IsAbelianGalois F L → (∀ σ : Gal(L/F), σ ^ 3 = 1) →
             SplitsCompletelyIn F L 𝔭) →
          (∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
             [IsGalois F L],
             IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
             (∀ 𝔭 ∈ T, SplitsCompletelyIn F L 𝔭) → ∃ (φ : L →ₐ[F] K), True) →
          relationRankWith (Gal(K/F)) (generatorRank (Gal(K/F))) ≤
            generatorRank (Gal(K/F)) + C₀ + T.card

/-- `3` does not divide `∏ i, r i` when every `r i ≡ 1 (mod 3)` is prime. -/
lemma three_not_dvd_prod {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) : ¬ (3 : ℕ) ∣ ∏ i, r i := by
  have h3 : Nat.Prime 3 := by norm_num
  have hcop : ∀ i, Nat.Coprime 3 (r i) := by
    intro i
    refine h3.coprime_iff_not_dvd.mpr fun hdiv => ?_
    have heq : 3 = r i := (Nat.prime_dvd_prime_iff_eq h3 (hr i)).mp hdiv
    have := hr3 i
    rw [← heq] at this
    norm_num at this
  have hprod : Nat.Coprime 3 (∏ i, r i) := Nat.Coprime.prod_right fun i _ => hcop i
  intro hdiv
  have hone : 3 ∣ 1 := by
    have := hprod.dvd_of_dvd_mul_right (show (3 : ℕ) ∣ 1 * ∏ i, r i by simpa using hdiv)
    simpa using this
  exact h3.not_dvd_one hone


/-- A finite commutative group of exponent `3` is a `3`-group. -/
lemma isPGroup_three_of_exp {G : Type*} [CommGroup G] [Finite G] (h : ∀ g : G, g ^ 3 = 1) :
    IsPGroup 3 G := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Module (ZMod 3) (Additive G) := AddCommGroup.zmodModule (n := 3) (by
    intro x
    obtain ⟨g, rfl⟩ := Additive.ofMul.surjective x
    show 3 • Additive.ofMul g = 0
    rw [show (3 : ℕ) • Additive.ofMul g = Additive.ofMul (g ^ 3) from rfl, h g]
    rfl)
  refine IsPGroup.of_card (n := Module.finrank (ZMod 3) (Additive G)) ?_
  rw [Nat.card_congr Additive.ofMul, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 3) (V := Additive G), ZMod.card]

end Assembly
end Tower
end Work
