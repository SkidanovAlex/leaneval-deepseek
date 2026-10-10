import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.GlobalCFT.Reciprocity
import Submission.NK.HeckeL.Artin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors Topology
open Filter

open NK.GlobalCFT (Idele IdeleClassGroup)

noncomputable section

namespace NK.HeckeL

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **Compatibility of the reciprocity isomorphism with the Frobenius elements at the unramified
primes** — the defining property of the Artin map, and the second named input of the chapter.

For a finite abelian extension `L/K`, a modulus `S` containing the ramified primes, and an
isomorphism `e` identifying the ray class group of the modulus with `C_K ⧸ N_{L/K} C_L`, the
composite `e ≫ h.iso : 𝕀 K ⧸ (Kˣ·U) ≃* Gal(L/K)` sends the class of the prime `𝔭 ∉ S` to the
Frobenius element at `𝔭` (`NK.Chebotarev.frobAtPrime`). -/
structure FrobeniusCompatibility (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (U : Subgroup (Idele K))
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : IdeleClassGroup.rayClassGroup K U ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L))
    (S : Finset (PrimeIdeal K)) : Prop where
  /-- the Artin map sends the class of `𝔭` to the Frobenius at `𝔭`, for `𝔭 ∉ S` -/
  iso_primeClass : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ S →
    (e.trans h.iso) (primeClass K U 𝔭) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭

/-! ## The dictionary between ray class characters and Galois characters -/

variable {U : Subgroup (Idele K)}

/-- **Artin reciprocity**, as an isomorphism between the ray class group of the modulus and the
Galois group of the abelian extension. -/
noncomputable def reciprocityEquiv (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : IdeleClassGroup.rayClassGroup K U ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L)) :
    IdeleClassGroup.rayClassGroup K U ≃* Gal(L/K) :=
  e.trans h.iso

/-- **The identification of the characters of the ray class group with those of `Gal(L/K)`**,
via Artin reciprocity. -/
noncomputable def rayCharEquivGalois (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : IdeleClassGroup.rayClassGroup K U ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L)) :
    RayChar K U ≃* (Gal(L/K) →* ℂˣ) where
  toFun χ := χ.comp (reciprocityEquiv h e).symm.toMonoidHom
  invFun ψ := ψ.comp (reciprocityEquiv h e).toMonoidHom
  left_inv χ := MonoidHom.ext fun x => by simp
  right_inv ψ := MonoidHom.ext fun y => by simp
  map_mul' χ χ' := MonoidHom.ext fun x => by simp [MonoidHom.mul_apply]

/-- The value at `g` of the Galois character attached to a ray class character. -/
theorem rayCharEquivGalois_apply_apply (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : IdeleClassGroup.rayClassGroup K U ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L))
    (χ : RayChar K U) (g : Gal(L/K)) :
    rayCharEquivGalois h e χ g = χ ((reciprocityEquiv h e).symm g) := rfl

/-- The trivial ray class character corresponds to the trivial Galois character. -/
@[simp] theorem rayCharEquivGalois_one (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : IdeleClassGroup.rayClassGroup K U ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L)) :
    rayCharEquivGalois h e (1 : RayChar K U) = 1 :=
  map_one _

/-- The dictionary is an isomorphism of character groups: a ray class character is trivial if and
only if the corresponding Galois character is. -/
theorem rayCharEquivGalois_eq_one_iff (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : IdeleClassGroup.rayClassGroup K U ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L)) {χ : RayChar K U} :
    rayCharEquivGalois h e χ = 1 ↔ χ = 1 := by
  constructor
  · intro h1
    refine MonoidHom.ext fun x => ?_
    have h2 := congrArg (fun φ : Gal(L/K) →* ℂˣ => φ ((reciprocityEquiv h e) x)) h1
    simpa [rayCharEquivGalois_apply_apply] using h2
  · rintro rfl
    exact rayCharEquivGalois_one h e

/-- Under the dictionary, the Euler factors agree, provided the reciprocity isomorphism is
compatible with the Frobenius at the unramified primes. -/
theorem artinEulerFactor_toGalois (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : IdeleClassGroup.rayClassGroup K U ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L))
    (S : Finset (PrimeIdeal K)) (hFrob : FrobeniusCompatibility K L U h e S)
    (χ : RayChar K U) (𝔭 : PrimeIdeal K) (h𝔭 : 𝔭 ∉ S) (s : ℝ) :
    artinEulerFactor (K := K) (L := L) (rayCharEquivGalois h e χ) s 𝔭
      = eulerFactor K U χ s 𝔭 := by
  have h1 : (reciprocityEquiv h e).symm (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
      = primeClass K U 𝔭 := by
    rw [← hFrob.iso_primeClass 𝔭 h𝔭, reciprocityEquiv, MulEquiv.symm_apply_apply]
  simp only [artinEulerFactor, eulerFactor, RayChar.atPrime, rayCharEquivGalois_apply_apply, h1]

end NK.HeckeL
