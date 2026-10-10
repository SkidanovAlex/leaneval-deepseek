import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.SSGRoute.kummer_level_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A Kummer generator for the cocycle of a derivation `I ⟶ (Lˣ)^p`

For a finite Galois extension `L/k` of number fields, a prime `p`, and a morphism of
`Gal(L/k)`-representations `f : I[Gal(L/k)] ⟶ (Lˣ)^p` (where `I` is the augmentation ideal of the
group algebra `k[Gal(L/k)]` and `(Lˣ)^p` denotes the `p`-th powers inside `Lˣ`, realized as the
range of the `p`-th power endomorphism of `Additive Lˣ`), the crossed homomorphism
`derivCochain f` attached to `f` by the derivation bridge `Hom(I, M) ≅ Z¹(G, M)` is a
**coboundary**:

  `∃ x : Lˣ, ∀ σ, derivCochain f σ = σ • x - x`.

In other words every crossed homomorphism `Gal(L/k) → Lˣ` with values in the `p`-th powers is
already a coboundary; the `p`-power hypothesis plays no role.  This is Hilbert's Theorem 90,
Noether's crossed-homomorphism form (`Work.AbsoluteKummer.exists_algEquiv_div_of_isCrossedHom`,
itself a wrapper around Mathlib's `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`),
applied to the unit-valued crossed homomorphism `σ ↦ derivCochain f σ`.

## Main result

* `exists_kummer_generator_of_derivCochain` — a Kummer generator `x` for `derivCochain f`.

## Implementation notes

The auxiliary lemmas record that the structures in play are compatible *definitionally*:
`(Lˣ)^p ⊆ Lˣ` is a submodule of `Additive Lˣ` with the induced Galois action, and `Additive.toMul`
transports sums to products and the Galois action to the Galois action on `Lˣ` (`Units.map`).
They are stated because `simp`/`rw` will not, on its own, unfold the instance projections
(`Submodule`'s addition and `SMul` on a subtype) far enough to match.
-/

namespace Work.SSGRoute

open CategoryTheory

/-- The coercion of the `p`-th powers `(Lˣ)^p ⊆ Additive Lˣ` is additive. -/
theorem pthSubX_coe_add {L : Type} [Field L] (p : ℕ) (a b : ↥(pthSubX L p)) :
    ((a + b : ↥(pthSubX L p)) : Additive Lˣ) = (a : Additive Lˣ) + (b : Additive Lˣ) := rfl

/-- The coercion of the `p`-th powers `(Lˣ)^p ⊆ Additive Lˣ` is `Gal(L/k)`-equivariant. -/
theorem pthSubX_coe_smul {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) (γ : L ≃ₐ[k] L)
    (z : ↥(pthSubX L p)) :
    ((γ • z : ↥(pthSubX L p)) : Additive Lˣ) = γ • (z : Additive Lˣ) := rfl

/-- `Additive.toMul` turns sums of units into products. -/
theorem additiveToMul_add_units {L : Type} [Field L] (a b : Additive Lˣ) :
    Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b := rfl

/-- `Additive.toMul` turns the Galois action on `Additive Lˣ` into the Galois action on `Lˣ`. -/
theorem additiveToMul_smul_units {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (γ : L ≃ₐ[k] L) (v : Additive Lˣ) :
    Additive.toMul (γ • v) = γ • Additive.toMul v := rfl

theorem exists_kummer_generator_of_derivCochain (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime]
    (f : Work.SSGRoute.ExtH1.augI (L ≃ₐ[k] L) ⟶ Work.SSGRoute.pthRepX k L p) :
    ∃ x : Lˣ, ∀ σ : L ≃ₐ[k] L,
      ((Work.SSGRoute.ExtH1.derivCochain (L ≃ₐ[k] L) f σ : ↥(Work.SSGRoute.pthSubX L p))
          : Additive Lˣ)
        = σ • (Additive.ofMul x) - Additive.ofMul x := by
  classical
  -- the cocycle `derivCochain f`, read multiplicatively as a map into `Lˣ`
  let φ : (L ≃ₐ[k] L) → Lˣ := fun σ =>
    Additive.toMul (((Work.SSGRoute.ExtH1.derivCochain (L ≃ₐ[k] L) f σ
      : ↥(Work.SSGRoute.pthSubX L p)) : Additive Lˣ))
  -- it is a crossed homomorphism in Noether's multiplicative form
  have hφcross : ∀ σ τ : (L ≃ₐ[k] L), (φ (σ * τ) : L) = (φ σ : L) * σ (φ τ : L) := by
    intro σ τ
    have h1 := Work.SSGRoute.ExtH1.derivCochain_isCrossedHom (G := L ≃ₐ[k] L) f σ τ
    -- the crossed-homomorphism condition, in `Additive Lˣ` rather than in `(Lˣ)^p`
    have h1' : ((Work.SSGRoute.ExtH1.derivCochain (L ≃ₐ[k] L) f (σ * τ)
          : ↥(Work.SSGRoute.pthSubX L p)) : Additive Lˣ)
        = ((Work.SSGRoute.ExtH1.derivCochain (L ≃ₐ[k] L) f σ
            : ↥(Work.SSGRoute.pthSubX L p)) : Additive Lˣ)
          + σ • ((Work.SSGRoute.ExtH1.derivCochain (L ≃ₐ[k] L) f τ
            : ↥(Work.SSGRoute.pthSubX L p)) : Additive Lˣ) := by
      have h := congrArg (fun z : ↥(Work.SSGRoute.pthSubX L p) => (z : Additive Lˣ)) h1
      rw [pthSubX_coe_add, pthSubX_coe_smul] at h
      exact h
    -- the multiplicative form in `Lˣ`
    have h2 : (φ (σ * τ) : Lˣ) = (φ σ : Lˣ) * (σ • (φ τ : Lˣ)) := by
      have h := congrArg (fun v : Additive Lˣ => Additive.toMul v) h1'
      rw [additiveToMul_add_units, additiveToMul_smul_units] at h
      simpa only [φ] using h
    -- and finally in `L`
    calc (φ (σ * τ) : L) = (((φ σ : Lˣ) * (σ • (φ τ : Lˣ)) : Lˣ) : L) := by rw [h2]
      _ = (φ σ : L) * σ (φ τ : L) := by
          rw [Units.val_mul, AlgEquiv.smul_units_def, Units.coe_map]
          rfl
  -- Hilbert 90: `φ` is a coboundary
  obtain ⟨x, hx⟩ := Work.AbsoluteKummer.exists_algEquiv_div_of_isCrossedHom φ hφcross
  refine ⟨x, fun σ => ?_⟩
  have hσ : φ σ = σ • x / x := by
    refine Units.ext ?_
    rw [hx σ, Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map]
    rfl
  calc ((Work.SSGRoute.ExtH1.derivCochain (L ≃ₐ[k] L) f σ
        : ↥(Work.SSGRoute.pthSubX L p)) : Additive Lˣ)
      = Additive.ofMul (φ σ) := rfl
    _ = Additive.ofMul ((σ • x) / x) := by rw [hσ]
    _ = Additive.ofMul (σ • x) - Additive.ofMul x := rfl
    _ = σ • (Additive.ofMul x) - Additive.ofMul x := by
        rw [show Additive.ofMul (σ • x) = σ • (Additive.ofMul x) from rfl]

end Work.SSGRoute
