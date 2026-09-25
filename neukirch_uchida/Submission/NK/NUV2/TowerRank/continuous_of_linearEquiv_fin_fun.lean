import Mathlib

/-!
# Continuity of `ℤ_[ℓ]`-linear equivalences out of a submodule of `ℤ_[ℓ]^r`

`ℤ_[ℓ]` is not a field, so `LinearMap.continuous_of_finiteDimensional` does not apply directly to
a `ℤ_[ℓ]`-linear map out of a submodule `N ≤ ℤ_[ℓ]^r`.  The continuity is nevertheless true, and
here is the reason: the inverse `σ.symm : ℤ_[ℓ]^r → N`, viewed as a linear map of the *free*
module `ℤ_[ℓ]^r` (whose topology is its module topology, a finite product of the topological ring
`ℤ_[ℓ]`), is a linear map between free finite modules, hence continuous.  Since `ℤ_[ℓ]^r` is
compact and `N` is Hausdorff, that continuous bijection is a homeomorphism, so its inverse `σ` is
continuous as well.

The statement is the one requested by the requester of the lemma (`NK.NUV2.TowerRank`).
-/

namespace NK.NUV2.TowerRank

/-- A `ℤ_[ℓ]`-linear equivalence from a submodule of `ℤ_[ℓ]^r` onto `ℤ_[ℓ]^r` is continuous.

Proof: its inverse, composed with the inclusion `N ↪ ℤ_[ℓ]^r`, is a `ℤ_[ℓ]`-linear endomorphism of
the free module `ℤ_[ℓ]^r`; the topology on `ℤ_[ℓ]^r` is the module topology (a finite product of
the topological ring `ℤ_[ℓ]`), so every linear endomorphism of it is continuous.  That continuous
bijection goes from the compact space `ℤ_[ℓ]^r` to the Hausdorff space `N`, hence is a
homeomorphism, and so its inverse `σ` is continuous. -/
theorem continuous_of_linearEquiv_fin_fun {ℓ r : ℕ} [Fact ℓ.Prime]
    {N : Submodule (PadicInt ℓ) (Fin r → PadicInt ℓ)}
    (σ : N ≃ₗ[PadicInt ℓ] (Fin r → PadicInt ℓ)) : Continuous σ := by
  -- The inverse of `σ`, as a linear endomorphism of the free module `ℤ_[ℓ]^r`.
  have hS : Continuous fun x : Fin r → PadicInt ℓ => ((σ.symm x : N) : Fin r → PadicInt ℓ) :=
    IsModuleTopology.continuous_of_linearMap (N.subtype.comp σ.symm.toLinearMap)
  -- The same map, now with values in `N` (which carries the subspace topology).
  have hsymm : Continuous fun x : Fin r → PadicInt ℓ => (σ.symm x : N) :=
    hS.subtype_mk _
  -- A continuous bijection from a compact space to a T2 space has continuous inverse.
  have h1 : Continuous (⇑(σ.symm.toEquiv).symm) :=
    Continuous.continuous_symm_of_equiv_compact_to_t2 (f := σ.symm.toEquiv) hsymm
  have hfun : ⇑(σ.symm.toEquiv).symm = ⇑σ := by
    funext x
    rw [Equiv.symm_apply_eq]
    simp
  rwa [hfun] at h1

end NK.NUV2.TowerRank
