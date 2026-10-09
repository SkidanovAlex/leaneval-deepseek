import Mathlib
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFTdeep.HNU.NormTransportDefs
import Submission.NK.GlobalCFTdeep.HNU.NormTransportMain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm form of Hasse's norm theorem in an arbitrary universe

The whole cohomological development of `NK.GlobalCFTdeep` — `Ĥ⁻¹(Gal(L/K), C_L) = 0`, the
five-term Tate sequence and hence the local–global principle for norms
`Kˣ ∩ N_{L/K}𝕀_L = N_{L/K}Lˣ` — is carried out in `Type 0`, because Mathlib's `tateCohomology`
ties the universe of the coefficient ring `ℤ` to that of the group.  The present module removes
that restriction.

A number field `K` in an arbitrary universe is countable (`NumberField K` gives
`FiniteDimensional ℚ K`), hence `Small.{0} K` and equivalent to its model `Shrink.{0} K`, on which
Mathlib transports the field/algebra/module structures (`Mathlib.Algebra.Ring.Shrink`,
`Mathlib.Algebra.Field.Shrink`, `Shrink.ringEquiv`).  The transport of the extension itself is
elementary (`shrink_lift`): the `Shrink K`-algebra structure on `Shrink L` is given by
`RingHom.toAlgebra` of the composite `Shrink K → K → L → Shrink L`, so that the two `Shrink`
ring equivalences are compatible with the algebra maps *on the nose*; finiteness, Galois-ness and
cyclicity of the extension then follow from Mathlib's `Module.Finite.of_equiv_equiv`,
`IsGalois.of_equiv_equiv`, and conjugation of Galois groups (`galConjMulEquiv`).

The transfer of the hypothesis `principalIdele K a ∈ N_{L/K}𝕀_L` is the invariance of the norm
subgroup under a compatible pair of ring equivalences of extensions;
`mem_normImage_of_ringEquiv` (delegated).  The transfer of the conclusion is Mathlib's
`Algebra.norm_eq_of_equiv_equiv`: at the level of units the conclusion reads
`Algebra.norm K b = a`, so the witness found by the `Type 0` theorem is transported back along the
`Shrink` ring equivalence.  The `Type 0` result applied to the model is
`NK.GlobalCFTdeep.hasseNormTheorem.hasse_norm`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-! ### `Shrink` transfers of the number-field structure -/

/-- `Shrink` preserves characteristic zero (the cast is the transported one). -/
theorem shrink_charZero (K : Type*) [Field K] [CharZero K] [Small.{0} K] :
    CharZero (Shrink.{0} K) := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h2 : (equivShrink K).symm ((n : Shrink.{0} K)) = (n : K) := by
    rw [show (n : Shrink.{0} K) = (equivShrink K) (n : K) from rfl]
    exact Equiv.symm_apply_apply _ _
  have h3 : (equivShrink K).symm (0 : Shrink.{0} K) = (0 : K) := by
    rw [show (0 : Shrink.{0} K) = (equivShrink K) (0 : K) from rfl]
    exact Equiv.symm_apply_apply _ _
  have h4 := congrArg (fun z => (equivShrink K).symm z) hn
  rw [h2, h3] at h4
  exact CharZero.cast_injective (R := K) (by simpa using h4)

/-- `Shrink` preserves finite-dimensionality over `ℚ`. -/
theorem shrink_finiteDimensional_rat (K : Type*) [Field K] [NumberField K] [Small.{0} K] :
    FiniteDimensional ℚ (Shrink.{0} K) :=
  LinearEquiv.finiteDimensional (Shrink.linearEquiv ℚ K).symm

/-! ### Conjugation of Galois groups by ring equivalences -/

/-- **The conjugation isomorphism of Galois groups** induced by a compatible pair of ring
equivalences of field extensions: `σ ↦ eL ∘ σ ∘ eL⁻¹`. -/
noncomputable def galConjMulEquiv {K L K' L' : Type*} [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (h : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    (L ≃ₐ[K] L) ≃* (L' ≃ₐ[K'] L') where
  toFun σ := AlgEquiv.ofRingEquiv (f := eL.symm.trans (σ.toRingEquiv.trans eL)) (by
    intro a
    change eL (σ (eL.symm (algebraMap K' L' a))) = algebraMap K' L' a
    have h1 : eL.symm (algebraMap K' L' a) = algebraMap K L (eK.symm a) := by
      apply eL.injective
      rw [RingEquiv.apply_symm_apply, h, eK.apply_symm_apply]
    rw [h1, AlgEquiv.commutes, h, eK.apply_symm_apply])
  invFun τ := AlgEquiv.ofRingEquiv (f := eL.trans (τ.toRingEquiv.trans eL.symm)) (by
    intro a
    change eL.symm (τ (eL (algebraMap K L a))) = algebraMap K L a
    rw [h a, AlgEquiv.commutes, ← h a, RingEquiv.symm_apply_apply])
  left_inv σ := by
    ext x
    simp [AlgEquiv.ofRingEquiv]
  right_inv τ := by
    ext x
    simp [AlgEquiv.ofRingEquiv]
  map_mul' σ τ := by
    ext x
    simp [AlgEquiv.ofRingEquiv]

/-! ### The transport inputs

Two equivalent routes to the transport of the hypothesis `principalIdele K a ∈ N_{L/K} 𝕀 L` to the
`Type 0` model are recorded here, so that either may be plugged in as soon as it is available:

* `map_normIdeleHom_ideleEquiv_aux` — naturality of the idèle norm for the transport
  `NK.GlobalCFTdeep.Transport.ideleEquiv` along a compatible pair of ring equivalences
  (delegated); together with `Transport.ideleEquiv_principalIdele` (on disk) it gives
* `mem_normImage_of_ringEquiv_aux` — the invariance of the norm subgroup itself (the statement
  delegated in `Transport/mem_normImage_of_ringEquiv.lean`). -/

/-- Naturality of the idèle norm under the transport along a compatible pair of ring equivalences
of extensions: `ideleEquivExplicit eK ∘ N_{L/K} = N_{L'/K'} ∘ ideleEquivExplicit eL`. -/
theorem map_normIdeleHom_ideleEquivExplicit_aux
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
    [Algebra K' L'] [FiniteDimensional K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (h : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (y : Idele L) :
    HNU.ideleEquivExplicit eK (Idele.normIdeleHom K L y) =
      Idele.normIdeleHom K' L' (HNU.ideleEquivExplicit eL y) :=
  HNU.map_normIdeleHom_ideleEquivExplicit_aux eK eL h y

/-- The invariance of the norm subgroup of the idèles under a compatible pair of ring equivalences
of extensions, in the principal-idèle form in which it is used below. -/
theorem mem_normImage_of_ringEquiv_aux
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
    [Algebra K' L'] [FiniteDimensional K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (h : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (a : Kˣ) (ha : NK.GlobalCFT.Idele.principalIdele K a ∈
      NK.GlobalCFT.Idele.normImage K L) :
    NK.GlobalCFT.Idele.principalIdele K' (Units.map eK.toMonoidHom a) ∈
      NK.GlobalCFT.Idele.normImage K' L' := by
  rw [Idele.normImage_eq_map] at ha ⊢
  obtain ⟨y, hy⟩ := ha
  refine ⟨HNU.ideleEquivExplicit eL y, ?_⟩
  rw [← map_normIdeleHom_ideleEquivExplicit_aux eK eL h y, hy]
  exact HNU.ideleEquivExplicit_principalIdele eK a

/-- **Norm form of Hasse's norm result.**  For cyclic `L/K` of number fields, in an arbitrary
universe: an element `a` of `Kˣ` whose principal idèle is a norm from the idèles of `L` is the norm
of an element of `Lˣ` (the local–global principle for norms, `Kˣ ∩ N_{L/K}𝕀_L = N_{L/K}Lˣ`).

At universe zero this is `NK.GlobalCFTdeep.hasseNormTheorem` (the second field of
`NK.HassePrinciple.HasseNormTheorem`, via
`NK.GlobalCFTdeep.hasseNorm_of_subsingleton_tateCohomology_neg_one`); the general case is obtained
by pure transport along a universe-zero model of the number fields, using the invariance of the
principal idèles and of the norm subgroup under ring equivalences of extensions (the same bridge as
`NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv`). -/
theorem hasseNorm_form_universe {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] (a : Kˣ)
    (ha : NK.GlobalCFT.Idele.principalIdele K a ∈ NK.GlobalCFT.Idele.normImage K L) :
    ∃ b : Lˣ, NK.GlobalCFT.Idele.principalIdele K a =
      NK.GlobalCFT.Idele.normIdeleFun K L (NK.GlobalCFT.Idele.principalIdele L b) := by
  -- a number field is countable, hence `Small`, so it has a model in `Type 0`
  haveI hcK : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  haveI hcL : Countable L := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := L)
  haveI hsK : Small.{0} K := Countable.toSmall K
  haveI hsL : Small.{0} L := Countable.toSmall L
  haveI hnfK : NumberField (Shrink.{0} K) :=
    { to_charZero := shrink_charZero K
      to_finiteDimensional := shrink_finiteDimensional_rat K }
  haveI hnfL : NumberField (Shrink.{0} L) :=
    { to_charZero := shrink_charZero L
      to_finiteDimensional := shrink_finiteDimensional_rat L }
  -- the two `Shrink` ring equivalences
  let eK : K ≃+* Shrink.{0} K := (Shrink.ringEquiv K).symm
  let eL : L ≃+* Shrink.{0} L := (Shrink.ringEquiv L).symm
  -- the `Shrink K`-algebra structure on `Shrink L`, compatible with `eK`, `eL` by construction
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) :=
    RingHom.toAlgebra ((eL : L →+* Shrink.{0} L).comp
      ((algebraMap K L).comp eK.symm.toRingHom))
  have hcomp : ∀ x : K,
      eL (algebraMap K L x) = algebraMap (Shrink.{0} K) (Shrink.{0} L) (eK x) := by
    intro x
    rw [RingHom.algebraMap_toAlgebra]
    show eL (algebraMap K L x) = eL (algebraMap K L (eK.symm (eK x)))
    rw [eK.symm_apply_apply]
  have hring : (algebraMap (Shrink.{0} K) (Shrink.{0} L)).comp (eK : K →+* Shrink.{0} K) =
      (eL : L →+* Shrink.{0} L).comp (algebraMap K L) :=
    RingHom.ext fun x => (hcomp x).symm
  -- the extension transports
  haveI : Module.Finite (Shrink.{0} K) (Shrink.{0} L) :=
    Module.Finite.of_equiv_equiv eK eL hring
  haveI : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) := ‹Module.Finite _ _›
  haveI : IsGalois (Shrink.{0} K) (Shrink.{0} L) :=
    Commons.FieldTheory.Galois.isGalois_of_ringEquiv eK eL hcomp
  have hcyc : IsCyclic ((Shrink.{0} L) ≃ₐ[Shrink.{0} K] (Shrink.{0} L)) :=
    isCyclic_of_surjective (galConjMulEquiv eK eL hcomp).toMonoidHom
      (galConjMulEquiv eK eL hcomp).surjective
  -- the hypothesis transports
  have ha₀ : Idele.principalIdele (Shrink.{0} K) (Units.map eK.toMonoidHom a) ∈
      Idele.normImage (Shrink.{0} K) (Shrink.{0} L) :=
    mem_normImage_of_ringEquiv_aux eK eL hcomp a ha
  -- Hasse's norm theorem in `Type 0`, applied to the model
  obtain ⟨b₀, hb₀⟩ := NK.GlobalCFTdeep.hasseNormTheorem.hasse_norm
    (K := Shrink.{0} K) (L := Shrink.{0} L) hcyc (Units.map eK.toMonoidHom a) ha₀
  -- convert the model statement into the field-norm statement `Algebra.norm K₀ b₀ = eK a`
  have h1 : Idele.normIdeleHom (Shrink.{0} K) (Shrink.{0} L)
        (Idele.principalIdele (Shrink.{0} L) b₀) =
      Idele.principalIdele (Shrink.{0} K) (Units.map eK.toMonoidHom a) := by
    refine Idele.ext fun v => ?_
    rw [Idele.normIdeleHom_apply]
    exact (congrFun hb₀ v).symm
  have h2 : Units.map (Algebra.norm (Shrink.{0} K)) b₀ = Units.map eK.toMonoidHom a := by
    refine Ideles.globalCFT_principalIdele_injective ?_
    rw [← Idele.normIdeleHom_principalIdele]
    exact h1
  have h2val : Algebra.norm (Shrink.{0} K) (b₀ : Shrink.{0} L) = eK (a : K) := by
    simpa using congrArg (fun u : (Shrink.{0} K)ˣ => (u : Shrink.{0} K)) h2
  -- transport the witness back to `L`
  set b : Lˣ := Units.map eL.symm.toMonoidHom b₀ with hb
  have hbval : (eL (b : L) : Shrink.{0} L) = (b₀ : Shrink.{0} L) := by
    simp [hb]
  have hnorm : Units.map (Algebra.norm K) b = a := by
    refine Units.ext ?_
    rw [Units.coe_map]
    have hkey : Algebra.norm K (b : L) =
        eK.symm (Algebra.norm (Shrink.{0} K) (eL (b : L))) :=
      Algebra.norm_eq_of_equiv_equiv eK eL hring (b : L)
    rw [hkey, hbval, h2val, eK.symm_apply_apply]
  refine ⟨b, ?_⟩
  funext v
  rw [← Idele.normIdeleHom_apply (K := K) (L := L) (x := Idele.principalIdele L b) v,
    Idele.normIdeleHom_principalIdele, hnorm]

end NK.GlobalCFTdeep
