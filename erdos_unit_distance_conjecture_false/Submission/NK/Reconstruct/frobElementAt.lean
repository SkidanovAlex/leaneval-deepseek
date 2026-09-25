import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.galToGamma_continuous
import Submission.NK.Reconstruct.denseRange_galToGamma
import Submission.NK.Reconstruct.denseSet_avoidClosedSubgroups

/-!
# The ℓ-adic Frobenius elements are dense in `Γ_K`, and avoid finitely many closed subgroups

This file supplies the *analytic* input of Shimizu's Proposition 4f.3 (arXiv:2009.10431, §4) at the
level of `Γ_K`: the elements of `Γ_K` which are Frobenius elements at a prime of `K` (at every
finite level) are dense, and hence meet the complement of any finite union of non-open closed
subgroups.

The density is **Čebotarev** — this is where hypothesis (c) of the reconstruction, the density
theorem for the infinite extension (Serre, *Abelian ℓ-adic Representations*, Ch. I §2.2 Cor. 2), is
consumed.  It is *not* a consequence of the general "Frobenius elements generate `G_K`" statement:
the latter is stated in this area for the predicate `NK.Reconstruct.IsFrobElement`, which is
satisfied by *every* element of `Gal(K'/K)` — the finite level `L = ⊥` always gives a witness, since
the trivial automorphism of the residue field satisfies Fermat.  The correct notion, used below, is
Serre's: `σ` is a Frobenius element at `p` when it *is* the Frobenius at `p` at every finite level
(which forces `p` to be unramified in the corresponding ℓ-extension).

## Contents

* `IsFrobElementAt p σ` — `σ ∈ Gal(K'/K)` is a Frobenius element at the prime `p` of `K`;
* `dense_isFrobElementAt` — Čebotarev: the elements which are Frobenius elements at *some* prime
  are dense (`NK.Chebotarev.DenseFrobeniusSet`);
* `dense_image_galToGamma_isFrobElementAt` — their images in `Γ_K` are dense;
* `exists_isFrobElementAt_notMem_iUnion_closedSubgroup` — the form used in Proposition 4f.3: given
  finitely many non-open closed subgroups of `Γ_K`, there is a prime `p` and a Frobenius element at
  `p` whose image in `Γ_K` lies outside all of them.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4;
J.-P. Serre, *Abelian ℓ-adic Representations and Elliptic Curves*, Ch. I §1.2, §2.2.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

section Basic

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']

/-- **`σ` is an arithmetic Frobenius element at the prime `p` of `K`** (Serre's notion): for every
finite normal level `L/K` inside `K'`, the restriction of `σ` to `L` is the arithmetic Frobenius at
a prime of `L` above `p`.

For a prime `p` unramified in the extension of `K` corresponding to the relevant quotient, this
defines *the* Frobenius element `Frob_p`, and the ℓ-adic Frobenius element of `Γ_K` is the image of
`σ` under `galToGamma` (`NK.Reconstruct.exists_frobElement`); the two agree by construction. -/
def IsFrobElementAt (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(K'/K)) : Prop :=
  ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
    ∃ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal ∧
      NK.Chebotarev.IsFrobAt P (AlgEquiv.restrictNormalHom L σ)

end Basic

section Density

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsSepClosure K K']

/-- **Čebotarev: the Frobenius elements are dense.**  The elements of `Gal(K'/K)` which are the
Frobenius element at some prime of `K` (at every finite level) are dense in the Krull topology.

This is `NK.Chebotarev.DenseFrobeniusSet`, i.e. the density theorem for the infinite extension —
hypothesis (c) of the reconstruction. -/
theorem dense_isFrobElementAt (hc : ChebotarevInput K K') :
    Dense {σ : Gal(K'/K) | ∃ p : NK.Chebotarev.PrimeIdeal K, IsFrobElementAt p σ} :=
  dense_frobeniusSet_of_chebotarev (K₁ := K) (K₁' := K') hc

/-- **The ℓ-adic Frobenius elements are dense in `Γ_K`**: the image under `galToGamma` of the
Frobenius elements of `Gal(K'/K)` is dense, because `galToGamma` is continuous with dense range.

This is item 1 of the plan of README §17, in its correct (Čebotarev) form. -/
theorem dense_image_galToGamma_isFrobElementAt (hc : ChebotarevInput K K') (ℓ : ℕ) :
    Dense ((galToGamma (K := K) (K' := K') ℓ) ''
      {σ : Gal(K'/K) | ∃ p : NK.Chebotarev.PrimeIdeal K, IsFrobElementAt p σ}) :=
  DenseRange.dense_image (denseRange_galToGamma (K := K) (K' := K') ℓ)
    (galToGamma_continuous (K := K) (K' := K') ℓ) (dense_isFrobElementAt hc)

/-- **The Frobenius-avoidance lemma of Proposition 4f.3.**  Given finitely many closed subgroups of
`Γ_K` which are not open (in the application: the kernels `ker(φ_τ)` of the finitely many
`τ ∈ G(L/ℚ)`), there is a prime `p` of `K` and a Frobenius element `σ` at `p` whose image in `Γ_K`
lies outside all of them.

This is the *only* place where the density theorem (c) enters the measure argument of Shimizu's
Proposition 4f.3; everything else is the Baire-category statement
`NK.Reconstruct.exists_mem_dense_notMem_iUnion_closedSubgroup`. -/
theorem exists_isFrobElementAt_notMem_iUnion_closedSubgroup (hc : ChebotarevInput K K') (ℓ : ℕ)
    {ι : Type*} [Finite ι] (H : ι → Subgroup (Gamma K K' ℓ))
    (hcl : ∀ i, IsClosed (H i : Set (Gamma K K' ℓ)))
    (h : ∀ i, ¬ IsOpen (H i : Set (Gamma K K' ℓ))) :
    ∃ (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(K'/K)),
      IsFrobElementAt p σ ∧ ∀ i, galToGamma (K := K) (K' := K') ℓ σ ∉ H i := by
  obtain ⟨d, ⟨σ, hσ, rfl⟩, hd⟩ :=
    exists_mem_dense_notMem_iUnion_closedSubgroup H hcl h
      (dense_image_galToGamma_isFrobElementAt hc ℓ)
  obtain ⟨p, hp⟩ := hσ
  exact ⟨p, σ, hp, hd⟩

/-- **The Frobenius-avoidance lemma in the form used by Proposition 4f.3**: if the kernels
`ker(φ_τ)` of a finite family of homomorphisms out of `Γ_K` are all non-open and closed, then a
Frobenius element at some prime lies outside all of them. -/
theorem exists_isFrobElementAt_notMem_iUnion_ker (hc : ChebotarevInput K K') (ℓ : ℕ)
    {ι : Type*} [Finite ι] {C : Type*} [Group C] (φ : ι → Gamma K K' ℓ →* C)
    (hcl : ∀ i, IsClosed ((φ i).ker : Set (Gamma K K' ℓ)))
    (h : ∀ i, ¬ IsOpen ((φ i).ker : Set (Gamma K K' ℓ))) :
    ∃ (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(K'/K)),
      IsFrobElementAt p σ ∧ ∀ i, φ i (galToGamma (K := K) (K' := K') ℓ σ) ≠ 1 := by
  obtain ⟨p, σ, hσ, hd⟩ :=
    exists_isFrobElementAt_notMem_iUnion_closedSubgroup (K := K) (K' := K') hc ℓ
      (fun i => (φ i).ker) hcl h
  exact ⟨p, σ, hσ, fun i => by simpa using hd i⟩

end Density

end NK.Reconstruct
