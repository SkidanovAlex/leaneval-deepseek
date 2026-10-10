import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Submission.NK.Reconstruct.NumFieldIn
import Submission.NK.Reconstruct.gammaHaus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `K^{(∞,ℓ)}`: the field of Shimizu's `Γ_K`

Shimizu (arXiv:2009.10431, §4) writes `K^{(∞,ℓ)}` for the extension of `K` *corresponding to*
`Γ_K = G_K^{ab,(ℓ),/torsion}`, i.e. the fixed field of the kernel of the canonical surjection
`G_K ↠ Γ_K`.  In this development the correct topological model of `Γ_K` is
`NK.Reconstruct.GammaHaus` (`γ_K^{tf}`), so we define

  `levelInfinity K ℓ = {x : Ω | ∀ g : Gal(Ω/↥K), γ_K^{tf}(galToGamma g) = 1 → g x = x}`,

the fixed field of `ker (galToGamma ≫ gammaHausMk : Gal(Ω/↥K) → Γ_K^{tf})`, as an intermediate
field of `Ω/ℚ`.

Because `Γ_K^{tf}` is Hausdorff and `galToGamma ≫ gammaHausMk` is continuous, the kernel is closed,
and the Galois correspondence applies: `Gal(Ω/levelInfinity K ℓ) ≃* Γ_K^{tf}` — this is the
dictionary between the group-theoretic and the field-theoretic sides used by Shimizu's Lemmas 4f.4
and 4f.5.

## Main definitions

* `levelInfinity` — Shimizu's `K^{(∞,ℓ)}`;
* `mem_levelInfinity_iff` — its defining membership condition;
* `levelInfinity_le_fixed` — the invisible subgroup of `G_K` fixes `K^{(∞,ℓ)}` pointwise.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω]

/-- **Shimizu's field `K^{(∞,ℓ)}`**: the fixed field of the kernel of `G_K ↠ Γ_K^{tf}`, i.e. the
compositum of the `ℤ_ℓ`-extensions of `K` (as a subfield of `Ω`, over `ℚ`). -/
noncomputable def levelInfinity (K : IntermediateField ℚ Ω) [NumberField ↥K] [IsSepClosure ↥K Ω] (ℓ : ℕ)
    [Fact ℓ.Prime] : IntermediateField ℚ Ω where
  carrier := {x : Ω | ∀ g : Gal(Ω/↥K),
    gammaHausMk (K := ↥K) (K' := Ω) ℓ (galToGamma (K := ↥K) (K' := Ω) ℓ g) = 1 → g x = x}
  mul_mem' := by
    intro x y hx hy g hg
    rw [map_mul, hx g hg, hy g hg]
  one_mem' := by
    intro g _
    rw [map_one]
  add_mem' := by
    intro x y hx hy g hg
    rw [map_add, hx g hg, hy g hg]
  zero_mem' := by
    intro g _
    rw [map_zero]
  inv_mem' := by
    intro x hx g hg
    simpa [hx g hg]
  algebraMap_mem' := by
    intro c g _
    rw [IsScalarTower.algebraMap_apply ℚ ↥K Ω]
    exact g.commutes _

@[simp] theorem mem_levelInfinity_iff (K : IntermediateField ℚ Ω) [NumberField ↥K] [IsSepClosure ↥K Ω] (ℓ : ℕ)
    [Fact ℓ.Prime] (x : Ω) :
    x ∈ levelInfinity K ℓ ↔ ∀ g : Gal(Ω/↥K),
      gammaHausMk (K := ↥K) (K' := Ω) ℓ (galToGamma (K := ↥K) (K' := Ω) ℓ g) = 1 → g x = x :=
  Iff.rfl

/-- An element of the invisible subgroup of `G_K` fixes `K^{(∞,ℓ)}` pointwise. -/
theorem levelInfinity_le_fixed (K : IntermediateField ℚ Ω) [NumberField ↥K] [IsSepClosure ↥K Ω] (ℓ : ℕ)
    [Fact ℓ.Prime] (g : Gal(Ω/↥K))
    (hg : gammaHausMk (K := ↥K) (K' := Ω) ℓ (galToGamma (K := ↥K) (K' := Ω) ℓ g) = 1) :
    ∀ x ∈ levelInfinity K ℓ, g x = x :=
  fun x hx => hx g hg

section FrobLevel

variable [IsGalois ℚ Ω]

/-- `K^{(∞,ℓ)}` for a finite number-field level `K` of `Ω/ℚ`. -/
noncomputable def levelInfinityOf (K : NumFieldIn ℚ Ω) [IsSepClosure ↥(K.L) Ω] (ℓ : ℕ)
    [Fact ℓ.Prime] : IntermediateField ℚ Ω :=
  levelInfinity (K := K.L) ℓ

end FrobLevel

end NK.Reconstruct
