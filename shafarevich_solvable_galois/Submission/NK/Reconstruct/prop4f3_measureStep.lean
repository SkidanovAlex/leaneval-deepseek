import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Reconstruct.not_isOpen_ker_of_infinite_range
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The measure step of Shimizu's Proposition 4f.3

Shimizu (arXiv:2009.10431, proof of Proposition 4f.3) argues as follows.  For the finitely many
`τ ∈ G(L/ℚ)` he forms the homomorphisms

  `φ_τ : Γ_L → Γ_{K₂},  γ ↦ (σ̄ ∘ π_{L/K₁})(γ) · (π_{L/K₂} ∘ τ^*)(γ)⁻¹`

and assumes that all of them are non-trivial.  Then each `ker(φ_τ)` is a closed subgroup of `Γ_L`
which is not open (a non-trivial continuous homomorphism out of the profinite group `Γ_L` does not
factor through a finite quotient), so a finite union of them cannot exhaust `Γ_L`; and since the
*Frobenius elements* are dense in `Γ_L` (Čebotarev for the infinite extension), a prime `𝔭` can be
found whose Frobenius element lies outside the union.  That is the contradiction which produces the
`τ` of Proposition 4f.3.

This file proves that step completely, in the abstract form in which it is used.

## Contents

* `exists_notMem_iUnion_ker_of_infinite_range` — the pure Baire-category form: finitely many
  continuous homomorphisms out of `Γ_K` with infinite range are simultaneously non-trivial
  somewhere;
* `exists_isFrobElementAt_notMem_iUnion_ker_of_infinite_range` — the form used in Proposition 4f.3:
  a Frobenius element at some prime can be found at which all of them are non-trivial (this is where
  Čebotarev, hypothesis (c) of the reconstruction, enters).

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4;
J.-P. Serre, *Abelian ℓ-adic Representations and Elliptic Curves*, Ch. I §2.2 Cor. 2.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

section Measure

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsSepClosure K K']

/-- The kernel of a continuous homomorphism, as a closed subset. -/
theorem isClosed_ker_of_continuous {G : Type*} [Group G] [TopologicalSpace G] {C : Type*}
    [Group C] [TopologicalSpace C] [T1Space C] (φ : G →* C) (hφ : Continuous φ) :
    IsClosed ((φ.ker : Subgroup G) : Set G) := by
  rw [show ((φ.ker : Subgroup G) : Set G) = φ ⁻¹' ({1} : Set C) from by
    ext x; simp [MonoidHom.mem_ker]]
  exact isClosed_singleton.preimage hφ

/-- **The pure Baire-category form of the measure step**: finitely many continuous homomorphisms
out of `Γ_K` with infinite range are simultaneously non-trivial somewhere. -/
theorem exists_notMem_iUnion_ker_of_infinite_range (ℓ : ℕ) {ι : Type*} [Finite ι]
    {C : ι → Type*} [∀ i, Group (C i)] [∀ i, TopologicalSpace (C i)] [∀ i, T1Space (C i)]
    (φ : ∀ i, Gamma K K' ℓ →* C i)
    (hcont : ∀ i, Continuous (φ i)) (hinf : ∀ i, ¬ Finite (φ i).range) :
    ∃ γ : Gamma K K' ℓ, ∀ i, φ i γ ≠ 1 := by
  obtain ⟨γ, -, hγ⟩ := exists_mem_dense_notMem_iUnion_closedSubgroup (G := Gamma K K' ℓ)
    (H := fun i => (φ i).ker)
    (fun i => isClosed_ker_of_continuous (φ i) (hcont i))
    (fun i => not_isOpen_ker_of_infinite_range (φ i) (hinf i)) dense_univ
  exact ⟨γ, fun i => by simpa using hγ i⟩

/-- **The measure step of Proposition 4f.3**: finitely many continuous homomorphisms out of `Γ_K`
with infinite range are simultaneously non-trivial on the image of a *Frobenius element at some
prime* of `K`.  This is the exact form in which Proposition 4f.3 consumes the density theorem
(hypothesis (c)). -/
theorem exists_isFrobElementAt_notMem_iUnion_ker_of_infinite_range (hc : ChebotarevInput K K')
    (ℓ : ℕ) {ι : Type*} [Finite ι] {C : ι → Type*} [∀ i, Group (C i)]
    [∀ i, TopologicalSpace (C i)] [∀ i, T1Space (C i)] (φ : ∀ i, Gamma K K' ℓ →* C i)
    (hcont : ∀ i, Continuous (φ i)) (hinf : ∀ i, ¬ Finite (φ i).range) :
    ∃ (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(K'/K)),
      IsFrobElementAt p σ ∧ ∀ i, φ i (galToGamma (K := K) (K' := K') ℓ σ) ≠ 1 := by
  obtain ⟨p, σ, hp, hσ⟩ := exists_isFrobElementAt_notMem_iUnion_closedSubgroup (K := K) (K' := K')
    hc ℓ (H := fun i => (φ i).ker)
    (fun i => isClosed_ker_of_continuous (φ i) (hcont i))
    (fun i => not_isOpen_ker_of_infinite_range (φ i) (hinf i))
  exact ⟨p, σ, hp, fun i => by simpa using hσ i⟩

end Measure

end NK.Reconstruct
