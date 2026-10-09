import Mathlib
import Submission.NK.Reconstruct.gammaBaseChange
import Submission.NK.Reconstruct.proj_surjective
import Submission.NK.Reconstruct.LevelInclExact.ker_proj_le_range_gammaBaseChangeHom
import Submission.NK.Reconstruct.LevelInclExact.range_gammaBaseChangeHom_le_ker_proj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cokernel of the base-change map `π_{L/K} : Γ_L → Γ_K` is finite

For a finite Galois level `L` of `K'/K` (`NK.Reconstruct.FrobLevel`) and a prime `ℓ`, the
base-change map of Shimizu's §4,

  `π_{L/K} = gammaBaseChangeHom ℓ L : Γ_L →* Γ_K`,

is the map on the ℓ-adic abelianisations of the absolute Galois groups induced by the inclusion
`G_L ⊆ G_K` (`NK.Reconstruct.gammaBaseChange`); its projection to a level `N` of `K'/K` passes to
the compositum `N ⊔ L`, forgets the `L`-structure (`NK.Reconstruct.ellIncl`) and restricts back
(`NK.Reconstruct.ellRestrict`).

This file proves that its cokernel is finite, `NK.Reconstruct.finite_coker_gammaBaseChangeHom`.
This is the provable half of Shimizu's Lemma 4f.1 (arXiv:2009.10431, §4); it is what makes the
restriction `Hom_{cts}(Γ_K, ℤ_ℓ) → Hom_{cts}(Γ_L, ℤ_ℓ)` on the continuous duals injective, via
`NK.Reconstruct.dual_injective_of_finite_index` (a `ℤ_ℓ`-linear form vanishing on a finite-index
submodule is zero).

## The argument

The precise statement proved here is the exactness of the sequence of profinite groups

  `Γ_L --π_{L/K}--> Γ_K --proj_L--> Γ_{L,ℓ} = ℓ-part(Gal(L/K)^{ab}) --> 1`,

i.e. `range(π_{L/K}) = ker(proj_L)`
(`NK.Reconstruct.ker_proj_eq_range_gammaBaseChangeHom`). Its two halves are:

* `range(π) ≤ ker(proj_L)`: projecting `π(f)` to the level `L` passes through the level
  `L ⊔ L = L` viewed over `L`, whose absolute Galois group is trivial
  (`NK.Reconstruct.LevelInclExact.range_gammaBaseChangeHom_le_ker_proj`);
* `ker(proj_L) ≤ range(π)`: given `f ∈ Γ_K` with `f_L = 1`, every finite set of constraints
  `ellIncl(g_M) = f_M` (`M ⊇ L` a level of `K'/K`) is satisfiable — the component `f_M` lies in
  the kernel of the restriction `Γ_{M,ℓ}(K) → Γ_{L,ℓ}(K)`, which by level-wise exactness of the
  level inclusion (`NK.Reconstruct.LevelInclExact.ellIncl_range_eq_ker_ellRestrict`, the
  ℓ-primary part of the classical exactness `Ab(Gal(M/L)) → Ab(Gal(M/K)) → Ab(Gal(L/K)) → 0`) is
  the image of `Γ_{M,ℓ}(L) → Γ_{M,ℓ}(K)`; pass to a common upper bound of the finitely many
  levels, lift there and restrict. Compactness of the profinite group `Γ_L` then produces a single
  `g ∈ Γ_L` satisfying all constraints
  (`NK.Reconstruct.LevelInclExact.ker_proj_le_range_gammaBaseChangeHom`), and it satisfies
  `π(g) = f` because the two agree on all levels `M ⊇ L`, hence everywhere, by coherence.

Since the projection `proj_L` is surjective (`NK.Reconstruct.proj_surjective`), the exactness
identifies the cokernel of `π_{L/K}` with the *finite* group `Γ_{L,ℓ}`, and in particular

  `Γ_K ⧸ range(π_{L/K}) ≅* ℓ-part(Gal(L/K)^{ab})`,

which is the finiteness asserted by `NK.Reconstruct.finite_coker_gammaBaseChangeHom`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3 and Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

/-- **Exactness of the base-change sequence at `Γ_K`**: the image of Shimizu's base-change map
`π_{L/K} : Γ_L → Γ_K` is exactly the kernel of the projection `Γ_K → Γ_{L,ℓ}` onto the finite level
`L`, so that `coker(π_{L/K}) ≅ (Gal(L/K)^{ab})^{(ℓ)}`. -/
theorem ker_proj_eq_range_gammaBaseChangeHom {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L : FrobLevel K K') :
    (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker = (gammaBaseChangeHom ℓ L).range :=
  le_antisymm (LevelInclExact.ker_proj_le_range_gammaBaseChangeHom ℓ L)
    (LevelInclExact.range_gammaBaseChangeHom_le_ker_proj ℓ L)

/-- **The cokernel of the base-change map is finite.**  For a finite Galois level `L` of `K'/K`,
the base-change map `π_{L/K} = gammaBaseChangeHom ℓ L : Γ_L → Γ_K` (Shimizu's canonical map
induced by the inclusion `G_L ⊆ G_K`) has finite cokernel; indeed
`coker(π_{L/K}) ≅ (Gal(L/K)^{ab})^{(ℓ)}`.  This is the provable half of Shimizu's Lemma 4f.1: it
gives the injectivity of the restriction `Hom_{cts}(Γ_K, ℤ_ℓ) → Hom_{cts}(Γ_L, ℤ_ℓ)` via
`NK.Reconstruct.dual_injective_of_finite_index`. -/
theorem finite_coker_gammaBaseChangeHom {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (L : FrobLevel K K') :
    Finite ((Gamma K K' ℓ) ⧸ (gammaBaseChangeHom ℓ L).range) := by
  classical
  -- The range of the base-change map is the kernel of the projection to the level `L` ...
  have hker : (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker =
      (gammaBaseChangeHom ℓ L).range := ker_proj_eq_range_gammaBaseChangeHom ℓ L
  -- ... whose quotient is the finite level group `Γ_{L,ℓ}`, the projection being surjective.
  have hsurj : Function.Surjective (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L) :=
    proj_surjective ℓ L
  have e : Gamma K K' ℓ ⧸ (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker ≃*
      LevelEllPart L.L ℓ :=
    QuotientGroup.quotientKerEquivOfSurjective _ hsurj
  have hle : (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker ≤
      (QuotientGroup.mk' (gammaBaseChangeHom ℓ L).range).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (QuotientGroup.eq_one_iff x).mpr (hker.le hx)
  -- The quotient by the range is therefore a quotient of the finite group `Γ_{L,ℓ}`.
  let q : Gamma K K' ℓ ⧸ (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker →*
      Gamma K K' ℓ ⧸ (gammaBaseChangeHom ℓ L).range :=
    QuotientGroup.lift _ (QuotientGroup.mk' _) hle
  have hcomp : q.comp (QuotientGroup.mk' (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker)
      = QuotientGroup.mk' (gammaBaseChangeHom ℓ L).range := by
    ext x
    simp [q]
  have hqsurj : Function.Surjective q :=
    Function.Surjective.of_comp (f := ⇑q)
      (g := ⇑(QuotientGroup.mk' (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker)) (by
        show Function.Surjective ⇑(q.comp (QuotientGroup.mk' _))
        rw [hcomp]
        exact QuotientGroup.mk'_surjective _)
  refine Finite.of_surjective (fun y : LevelEllPart L.L ℓ => q (e.symm y)) ?_
  intro z
  obtain ⟨w, hw⟩ := hqsurj z
  exact ⟨e w, by show q (e.symm (e w)) = z; rw [MulEquiv.symm_apply_apply, hw]⟩

end NK.Reconstruct
