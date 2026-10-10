import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.ellRestrict_comp
import Submission.NK.Reconstruct.proj_surjective
import Submission.NK.Reconstruct.torsionFreeGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base-change map `π_{L/K} : Γ_L → Γ_K` of Shimizu's §4

Shimizu (arXiv:2009.10431, §4, before Prop. 4f.3) uses, for a finite extension `L/K` of number
fields, the "canonical homomorphism"

  `π_{L/K} = π_{L/K,ℓ} : Γ_L → Γ_K`,

induced by the inclusion `G_L ⊆ G_K` on the torsion-free ℓ-adic abelianisations.  It is the map with
`π_{L/K}(Frob_𝔭) = Frob_{𝔭|_K}`, and both Lemma 4f.1 (`res = π_{L/K}^*`) and Prop. 4f.4/4f.5 are
stated in terms of it.

This file constructs it in the projective-system language of `GammaObject.lean`: for a finite Galois
level `L` of `K'/K`, a level `N` of `K'/K` containing `L` is also a level of `K'/L`, and at that
level `π_{L/K}` is the map

  `Γ_{N,ℓ}(L) = ℓ-part(Gal(N/L)^{ab})  →  ℓ-part(Gal(N/K)^{ab}) = Γ_{N,ℓ}(K)`

induced by the inclusion `Gal(N/L) ⊆ Gal(N/K)` (a normal subgroup, `L/K` being Galois).  Levels not
containing `L` are handled by first passing to the compositum `N ⊔ L` and restricting back.

## Contents

* `levelInclHom` — the inclusion `Gal(M/L) →* Gal(M/K)` (the "forget the `L`-structure" map);
* `levelInclHom_apply_coe` — it does not move the underlying element of `K'`;
* `ellIncl` — the induced map `Γ_{M,ℓ}(L) → Γ_{M,ℓ}(K)` on the ℓ-primary parts;
* `levelExtend` — a `K`-level containing `L`, viewed as a level over `L`;
* `ellIncl_ellRestrict` — **the naturality square**: the level inclusions commute with the
  transition maps of the two projective systems (restrict then forget = forget then restrict);
* `GammaBaseChange` / `pi` — the map `π_{L/K} : Γ_L → Γ_K` between the limits, with the projection
  formula `pi_proj`;
* `pi_continuous` — `π_{L/K}` is continuous (it is the projection of a closed subgroup of a
  product).

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace NK.Reconstruct

open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-! ## A level over `K` containing `L`, viewed over `L` -/

/-- **A finite Galois level of `K'/K` containing `L` is a finite Galois level of `K'/L`.** -/
noncomputable def levelExtend (L N : FrobLevel K K') (h : L.L ≤ N.L) : FrobLevel ↥L.L K' where
  L := IntermediateField.extendScalars h
  finite := by
    haveI : Module.Finite K ↥(IntermediateField.extendScalars h : IntermediateField ↥L.L K') :=
      N.finite
    exact Module.Finite.of_restrictScalars_finite K ↥L.L _
  normal := by
    haveI : Normal K ↥(IntermediateField.extendScalars h : IntermediateField ↥L.L K') := N.normal
    exact Normal.tower_top_of_normal K ↥L.L _
  numberField := N.numberField

@[simp] theorem levelExtend_L (L N : FrobLevel K K') (h : L.L ≤ N.L) :
    (levelExtend L N h).L = IntermediateField.extendScalars h := rfl

/-- The order relation of `K`-levels transports to the relative levels over `L`. -/
theorem levelExtend_mono (L A B : FrobLevel K K') (hA : L.L ≤ A.L) (hB : L.L ≤ B.L)
    (hAB : A.L ≤ B.L) : (levelExtend L A hA).L ≤ (levelExtend L B hB).L := hAB

/-! ## The inclusion of the level Galois groups -/

/-- **The inclusion `Gal(M/L) →* Gal(M/K)`** for finite Galois levels `L ⊆ M` of `K'/K`: an
automorphism of `M` fixing `L` is in particular an automorphism of `M` fixing `K`.  This is the
forgetful map of the extension of scalars `K ⊆ L`. -/
noncomputable def levelInclHom (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    Gal(↥(levelExtend L M h).L/↥L.L) →* Gal(↥M.L/K) :=
  AlgEquiv.restrictScalarsHom (R := K) (S := ↥L.L) (A := ↥(levelExtend L M h).L)

/-- **The inclusion does not move the underlying element**: the value of `levelInclHom L M h g` at
`x ∈ M` is the value of `g` at `x`, read off in the ambient field `K'`. -/
theorem levelInclHom_apply_coe (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (g : Gal(↥(levelExtend L M h).L/↥L.L)) (x : ↥M.L) :
    (((levelInclHom L M h g : Gal(↥M.L/K)) x : ↥M.L) : K')
      = ((g ⟨(x : K'), (show (x : K') ∈ M.L from x.2)⟩ : ↥(levelExtend L M h).L) : K') := rfl

/-- **The induced map on the ℓ-primary parts of the abelianisations**,
`Γ_{M,ℓ}(L) → Γ_{M,ℓ}(K)`: the functoriality of the ℓ-part of the abelianisation applied to
`levelInclHom`. -/
noncomputable def ellIncl (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L M h).L ℓ →*
      LevelEllPart (K := K) (K' := K') M.L ℓ where
  toFun x := ⟨Abelianization.map (levelInclHom L M h) x.1,
    ellPart_map_le ℓ (Abelianization.map (levelInclHom L M h))
      (Subgroup.mem_map_of_mem (Abelianization.map (levelInclHom L M h)) x.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] theorem ellIncl_coe (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (x : LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L M h).L ℓ) :
    ((ellIncl ℓ L M h x : LevelEllPart (K := K) (K' := K') M.L ℓ) :
      Abelianization Gal(↥M.L/K)) = Abelianization.map (levelInclHom L M h) x.1 := rfl

/-! ## The naturality square (statement; see `ellInclNaturality.lean`)

The two lemmas below are the *only* point at which the inclusion of the two projective systems
requires a computation with the explicit identifications `levelToEquiv` of `GammaObject.lean`; their
statements are recorded here and proved in `Submission/Work/Reconstruct/ellInclNaturality.lean`. -/

end NK.Reconstruct
