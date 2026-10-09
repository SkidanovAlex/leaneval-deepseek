import Mathlib
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Reconstruct.not_isOpen_ker_gammaTF_addHom
import Submission.NK.Reconstruct.GammaObject
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The measure step of Shimizu's Proposition 4f.3 at the torsion-free level

Shimizu (arXiv:2009.10431, §4) needs the following elementary but essential avoidance statement:
for finitely many continuous non-zero additive maps `φ_i : Γ_L^TF →+ Γ_M^TF` out of the
torsion-free ℓ-adic abelianisation `Γ_L^TF = NK.Reconstruct.GammaTF`, there is a prime `p` of `L`
and a Frobenius element `g` at `p` whose image in `Γ_L^TF` lies outside every kernel `ker φ_i`.

## The argument

Everything happens on the *limit* `Γ_L = NK.Reconstruct.Gamma K K' ℓ`, on which the Baire
argument is available: `Γ_L` is a compact Hausdorff topological group
(`NK.Reconstruct.instCompactSpaceGamma`), and a finite union of closed non-open subgroups cannot
cover it (`NK.Reconstruct.exists_notMem_iUnion_closedSubgroup`).  The torsion-free quotient
`Γ_L^TF` is the quotient of `Γ_L` by its ℓ-torsion submodule, and — crucially — the closedness of
the torsion is **not** needed:

* for each `i`, the kernel of the composite `ψ_i = φ_i ∘ gammaTFMk` is closed in `Γ_L`, because
  `gammaTFMk` is continuous (`Submodule.continuous_mkQ`) and `ker φ_i` is closed by hypothesis;
* `ψ_i ≠ 0` because `gammaTFMk` is surjective and `φ_i ≠ 0`;
* consequently `ker ψ_i` is not open in the compact group `Γ_L`: if it were, the quotient
  `Γ_L ⧸ ker ψ_i` would be discrete and compact, hence finite, and the first isomorphism theorem
  would make the range of `ψ_i` finite — contradicting
  `NK.Reconstruct.not_finite_range_of_ne_zero_add` (a non-zero additive map into a torsion-free
  `ℤ_ℓ`-module has infinite range).

Čebotarev enters only through the density of the Frobenius elements
(`NK.Reconstruct.dense_image_galToGamma_isFrobElementAt`): the dense set meets the complement of
the finite union of the non-open closed subgroups `ker ψ_i`.

## Contents

* `exists_isFrobElementAt_notMem_ker_gammaTF` — the requested statement.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4;
J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. XII §12.1–2.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

theorem exists_isFrobElementAt_notMem_ker_gammaTF {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] (L M : FrobLevel ℚ Ω) [IsSepClosure ↥L.L Ω] (hc : ChebotarevInput ↥L.L Ω)
    (ℓ : ℕ) [Fact ℓ.Prime] {ι : Type*} [Finite ι]
    (φ : ι → GammaTF (K := ↥L.L) (K' := Ω) ℓ →+ GammaTF (K := ↥M.L) (K' := Ω) ℓ)
    (hcont : ∀ i, Continuous (φ i)) (hne : ∀ i, φ i ≠ 0)
    (hcl : ∀ i, IsClosed ((φ i).ker : Set (GammaTF (K := ↥L.L) (K' := Ω) ℓ))) :
    ∃ (p : NK.Chebotarev.PrimeIdeal ↥L.L) (g : Gal(Ω/↥L.L)), IsFrobElementAt p g ∧
      ∀ i, φ i (gammaTFMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ)
        (galToGamma (K := ↥L.L) (K' := Ω) ℓ g)) ≠ 0 := by
  classical
  -- the composites `φ_i ∘ gammaTFMk`, additively and multiplicatively
  let ψ : ι → Additive (Gamma ↥L.L Ω ℓ) →+ GammaTF (K := ↥M.L) (K' := Ω) ℓ := fun i =>
    (φ i).comp (gammaTFMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ)).toAddMonoidHom
  let Ψ : ι → Gamma ↥L.L Ω ℓ →* Multiplicative (GammaTF (K := ↥M.L) (K' := Ω) ℓ) := fun i =>
    { toFun := fun x => Multiplicative.ofAdd (ψ i (Additive.ofMul x))
      map_one' := by simp [ψ]
      map_mul' := by
        intro x y
        apply Multiplicative.toAdd.injective
        simp [ψ, map_add] }
  -- the quotient map `Γ_L → Γ_L^TF` is continuous
  have hcontγ' : Continuous (fun x : Additive (Gamma ↥L.L Ω ℓ) =>
      gammaTFMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) x) := Submodule.continuous_mkQ _
  have hcontγ : Continuous (fun x : Gamma ↥L.L Ω ℓ =>
      gammaTFMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul x)) := hcontγ'
  -- the kernels of the composites are closed: they are the preimages of the closed `ker φ_i`
  have hcl' : ∀ i, IsClosed ((Ψ i).ker : Set (Gamma ↥L.L Ω ℓ)) := by
    intro i
    have hset : ((Ψ i).ker : Set (Gamma ↥L.L Ω ℓ)) =
        (fun x : Gamma ↥L.L Ω ℓ =>
          gammaTFMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul x)) ⁻¹'
          ((φ i).ker : Set (GammaTF (K := ↥L.L) (K' := Ω) ℓ)) := by
      ext x
      simp [MonoidHom.mem_ker, AddMonoidHom.mem_ker, Ψ, ψ]
    rw [hset]
    exact (hcl i).preimage hcontγ
  -- the composites are non-zero, since `gammaTFMk` is surjective
  have hnonzero : ∀ i, ψ i ≠ 0 := by
    intro i hzero
    apply hne i
    ext y
    obtain ⟨x, rfl⟩ := gammaTFMk_surjective (K := ↥L.L) (K' := Ω) (ℓ := ℓ) y
    have h1 : ψ i x = 0 := by rw [hzero]; rfl
    simpa [ψ] using h1
  -- hence their kernels are not open: an open kernel would force a finite range
  have hnotopen : ∀ i, ¬ IsOpen ((Ψ i).ker : Set (Gamma ↥L.L Ω ℓ)) := by
    intro i hopen
    haveI : DiscreteTopology (Gamma ↥L.L Ω ℓ ⧸ (Ψ i).ker) := QuotientGroup.discreteTopology hopen
    have hfinQ : Finite (Gamma ↥L.L Ω ℓ ⧸ (Ψ i).ker) := finite_of_compact_of_discrete
    have hfinrange : Finite ↥(Ψ i).range :=
      (QuotientGroup.quotientKerEquivRange (Ψ i)).finite_iff.mp hfinQ
    exact (not_finite_range_of_ne_zero_add (ℓ := ℓ) (ψ i) (hnonzero i)) hfinrange
  -- Baire + Čebotarev: the dense set of Frobenius elements avoids all the kernels
  obtain ⟨d, hdD, hd⟩ := exists_mem_dense_notMem_iUnion_closedSubgroup (H := fun i => (Ψ i).ker)
    hcl' hnotopen (dense_image_galToGamma_isFrobElementAt (K := ↥L.L) (K' := Ω) hc ℓ)
  obtain ⟨σ, hσ, rfl⟩ := hdD
  obtain ⟨p, hp⟩ := hσ
  refine ⟨p, σ, hp, fun i => ?_⟩
  have hmem : (Ψ i) (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ) ≠ 1 := by
    simpa [MonoidHom.mem_ker] using hd i
  intro hzero
  exact hmem (by
    show Multiplicative.ofAdd (ψ i (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))) = 1
    rw [show ψ i (Additive.ofMul (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)) = 0 from hzero]
    rfl)

end NK.Reconstruct
