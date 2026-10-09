import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.GlobalCFTdeep.SecondInequality.primeClass_eq_one_of_splitsCompletely
import Submission.NK.GlobalCFTdeep.SecondInequality.primeClass_eq_one_of_splitsCompletely_of_le
import Submission.NK.CFTLib.integralIdelesLeNormImage
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The character of the idèle class group attached to a character of the class group

This small module collects the vocabulary shared by the `p`-class-field files
(`NK.CFTLib.pClassField_exists`, `NK.CFTLib.pClassFieldArtin_of_fc` and the
`NK.CFTLib.Existence.*` files): the lift `classChar K p χ = χ ∘ idealClassHom` of a character of
the ideal class group to the idèle class group, its index, the class of the idèle of a prime, and
the openness of the modulus-`1` ray group.

It imports nothing from `NK.CFTLib.pClassField_exists`, so that the files which consume the
`p`-class-field *inputs* (`NK.CFTLib.Existence.classField_exists_primeIndex`,
`NK.CFTLib.Existence.splitting_of_normClass`) can use it without a cycle.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct IsMulCommutative nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

/-! ## The character of `C_K` attached to a character of the class group -/

/-- The character `χ̃` of the idèle class group attached to a character `χ` of the ideal class
group: the composite of `χ` with the ideal class map `C_K →* Cl(K)`. -/
def classChar (K : Type) [Field K] [NumberField K] (p : ℕ)
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) :
    IdeleClassGroup K →* Multiplicative (ZMod p) :=
  χ.comp (IdeleClassGroup.idealClassHom K)

@[simp] theorem classChar_apply (K : Type) [Field K] [NumberField K] (p : ℕ)
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) (x : IdeleClassGroup K) :
    classChar K p χ x = χ (IdeleClassGroup.idealClassHom K x) := rfl

/-- The kernel of `χ̃` is the preimage of the kernel of `χ`. -/
theorem ker_classChar (K : Type) [Field K] [NumberField K] (p : ℕ)
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) :
    (classChar K p χ).ker = (χ.ker).comap (IdeleClassGroup.idealClassHom K) := by
  ext x
  simp only [MonoidHom.mem_ker, classChar, MonoidHom.comp_apply, Subgroup.mem_comap]

/-- **The index of the kernel of `χ̃` is `p`** when `χ ≠ 1` and `p` is prime. -/
theorem index_ker_classChar (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) (hχ : χ ≠ 1) :
    (classChar K p χ).ker.index = p := by
  classical
  have hp := Fact.out (p := p.Prime)
  rw [ker_classChar, Subgroup.index_comap_of_surjective _
    (IdeleClassGroup.idealClassHom_surjective K), Subgroup.index_ker]
  -- `χ` is nontrivial, so its range is a nontrivial subgroup of a group of order `p`
  have hx : ∃ x, χ x ≠ 1 := by
    by_contra h
    exact hχ (MonoidHom.ext fun x => by simpa using not_exists.mp h x)
  have hbot : χ.range ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := hx
    refine hx ?_
    have hmem : χ x ∈ χ.range := ⟨x, rfl⟩
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hone : 1 < Nat.card ↥χ.range := (Subgroup.one_lt_card_iff_ne_bot χ.range).mpr hbot
  have hne : Nat.card ↥χ.range ≠ 1 := by
    intro h1
    rw [h1] at hone
    exact lt_irrefl 1 hone
  have hcard : Nat.card ↥χ.range ∣ p := by
    have h1 : Nat.card ↥χ.range ∣ Nat.card (Multiplicative (ZMod p)) :=
      Subgroup.card_subgroup_dvd_card χ.range
    rwa [Nat.card_congr (Multiplicative.ofAdd (α := ZMod p)).symm, Nat.card_zmod] at h1
  rcases hp.eq_one_or_self_of_dvd _ hcard with h | h
  · exact absurd h hne
  · exact h

/-- The image of the modulus-1 ray group is contained in `ker χ̃`: those idèles have trivial
ideal class. -/
theorem integralIdeles_map_le_ker_classChar (K : Type) [Field K] [NumberField K] (p : ℕ)
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) :
    (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ (classChar K p χ).ker := by
  intro x hx
  rw [ker_classChar, Subgroup.mem_comap, MonoidHom.mem_ker]
  have hx' : (IdeleClassGroup.idealClassHom K) x = 1 := by
    have hmem : x ∈ (IdeleClassGroup.idealClassHom K).ker := by
      rw [IdeleClassGroup.ker_idealClassHom K]
      exact hx
    simpa using hmem
  rw [hx', map_one]

/-! ## The class of the idèle of a prime is the class of the prime -/

/-- The fractional ideal of the idèle of a prime is that prime. -/
theorem idealOf_ideleOfPrime (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Idele.idealOf (HeckeL.ideleOfPrime K v) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  refine IdeleClassGroup.fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot) fun q => ?_
  rw [Idele.count_idealOf, HeckeL.ideleOfPrime, IdeleClassGroup.exp_ideleOfFun,
    FractionalIdeal.count_maximal]
  by_cases h : q = v
  · simp [h]
  · have h' : ¬ v = q := fun h'' => h h''.symm
    simp [h, h']

/-- **The ideal class of the idèle of a prime is the class of the prime.** -/
theorem idealClassHom_mk_ideleOfPrime (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup.idealClassHom K (IdeleClassGroup.mk K (HeckeL.ideleOfPrime K v))
      = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  have h1 : IdeleClassGroup.idealClassHom K (IdeleClassGroup.mk K (HeckeL.ideleOfPrime K v))
      = IdeleClassGroup.idealClassMap K (HeckeL.ideleOfPrime K v) := rfl
  rw [h1, IdeleClassGroup.idealClassMap_apply]
  rw [show Units.mk0 (Idele.idealOf (HeckeL.ideleOfPrime K v))
        (Idele.idealOf_ne_zero (HeckeL.ideleOfPrime K v))
      = Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot) from
    Units.ext (by rw [Units.val_mk0, Units.val_mk0, idealOf_ideleOfPrime])]
  exact ClassGroup.mk_mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/-! ## Openness of the modulus-1 ray group -/

/-- The idèles that are local units at every finite place form an open subgroup of `𝕀 K`. -/
theorem isOpen_integralIdeles (K : Type) [Field K] [NumberField K] :
    IsOpen (Idele.integralIdeles K : Set (Idele K)) := by
  haveI : Fact (∀ v : Place K, IsOpen (Place.localUnits K v : Set ((Place.localField K v)ˣ))) :=
    inferInstance
  have h := RestrictedProduct.isOpen_forall_imp_mem (ι := Place K)
    (R := fun v : Place K => (Place.localField K v)ˣ)
    (A := fun v : Place K => Place.localUnits K v)
    (p := fun v : Place K => v.IsFinite)
    (fun v => Fact.out (p := ∀ v : Place K,
      IsOpen (Place.localUnits K v : Set ((Place.localField K v)ˣ))) v)
  change IsOpen {x : Idele K | ∀ v : Place K, v.IsFinite → x v ∈ Place.localUnits K v}
  exact h

/-- The image in `C_K` of the modulus-1 ray group is open. -/
theorem isOpen_map_integralIdeles (K : Type) [Field K] [NumberField K] :
    IsOpen ((Idele.integralIdeles K).map (IdeleClassGroup.mk K) :
      Set (IdeleClassGroup K)) := by
  rw [Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe (Idele.integralIdeles K : Set (Idele K))
    (isOpen_integralIdeles K)

/-- A subgroup containing an open subgroup is open. -/
theorem isOpen_of_le_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U V : Subgroup G} (hU : IsOpen (U : Set G)) (h : U ≤ V) : IsOpen (V : Set G) := by
  have hV : (V : Set G) = ⋃ v ∈ (V : Set G), (fun x => v * x) '' (U : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · intro hx
      exact ⟨x, hx, 1, U.one_mem, by simp⟩
    · rintro ⟨v, hv, y, hy, hxy⟩
      rw [← hxy]
      exact V.mul_mem hv (h hy)
  rw [hV]
  refine isOpen_iUnion fun v => isOpen_iUnion fun _ => ?_
  rw [Set.image_mul_left]
  exact hU.preimage (continuous_const.mul continuous_id)

end NK.CFTLib
