import Mathlib
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.ringConjHom
import Submission.NK.Reconstruct.galToGamma

/-!
# The outer action `τ^*` of a ring automorphism of `K'` on `Γ_L` (Shimizu, Prop. 4f.3)

Let `K` be a number field, `K'` a separable closure, `L ⊆ K'` a finite (number-field) level and
`θ : K' ≃+* K'` a ring automorphism preserving `L` as a set.  The main result of this file is

  `exists_tauStar`:  there is a group automorphism `τstar` of `Γ_L = Gamma ↥L K' ℓ` with
  `τstar (galToGamma g) = galToGamma (θ g θ⁻¹)`  for every `g : Gal(K'/L)`.

Arithmetically `τstar` is the *outer* action of `θ` (i.e. of the automorphism `θ|_L` of `L`) on the
ℓ-adic abelianisation `Γ_L`: the conjugation map `g ↦ θ g θ⁻¹` is an automorphism of `G_L` which
does not preserve the base `L` pointwise, so it is not an inner automorphism, but its effect on the
*abelianisation* depends only on `θ|_L` and is therefore well defined; it is the twist `τ^*` with
which Shimizu compares the maps `π_{L/K}`, and hence a prerequisite of Proposition 4f.3.

## The route

`galToGamma ℓ : Gal(K'/L) →* Γ_L` is surjective (`NK.Reconstruct.galToGamma_surjective`), so an
automorphism of `Γ_L` compatible with `galToGamma` exists exactly when the conjugation
`ringConjHom L θ hθ` preserves the kernel of `galToGamma ℓ`; then one descends to the quotient
`G_L ⧸ ker` (which is `Γ_L` by the first isomorphism theorem) and transports the induced
automorphism of the quotient along `QuotientGroup.quotientKerEquivOfSurjective`.

* `conjLevel` — the level `θ⁻¹M` (for a level `M` of `K'/L`), with the `FrobLevel` structure
  `conjFrobLevel`: `FiniteDimensional` and `NumberField` are transported along the ring isomorphism
  `θ|_M` (via the canonical `ℚ`-structure of a characteristic-zero field, using the tower
  `ℚ ⊆ L ⊆ K'`), normality is `Normal.of_equiv_equiv`.
* `conjLevelRingEquiv : ↥(θ⁻¹M) ≃+* ↥M`, `x ↦ θ x`, and its conjugate action on the *relative*
  automorphism group, `conjLevelAlgEquivHom : Gal(θ⁻¹M/L) →* Gal(M/L)`, `u ↦ θ u θ⁻¹`.
* `conjLevelAlgEquivHom_restrictNormalHom` — the fundamental compatibility: restricting
  `g ∈ Gal(K'/L)` to `θ⁻¹M` and then conjugating is restricting `θ g θ⁻¹` to `M`.  This is the
  levelwise expression of the functoriality of the construction.
* `levelComponent_conj`, `ker_galToGamma_le_conj` — the resulting statement at the level of the
  ℓ-primary components, and hence at the level of `galToGamma`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.1–12.2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

section Basic

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
  [Algebra K K'] [IsSepClosure K K']
  (L : IntermediateField K K') [NumberField ↥L]
  (θ : K' ≃+* K')

theorem hθ_symm (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) : ∀ x : K', x ∈ L ↔ θ.symm x ∈ L :=
  fun x => by simpa using (hθ (θ.symm x)).symm

/-- **The level `θ⁻¹M`**: the intermediate field of `K'/L` whose elements are those `x` with
`θ x ∈ M`.  Conjugation by `θ` is an isomorphism `Gal(θ⁻¹M/L) ≅ Gal(M/L)`
(`NK.Reconstruct.conjLevelAlgEquivHom`) and `θ|_M` an isomorphism `θ⁻¹M ≃+* M`
(`NK.Reconstruct.conjLevelRingEquiv`). -/
noncomputable def conjLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') : IntermediateField ↥L K' :=
  Subfield.toIntermediateField (Subfield.comap θ.toRingHom M.toSubfield) (fun c => by
    rw [Subfield.mem_comap]
    have hL : θ ((algebraMap ↥L K') c) ∈ L := (hθ _).mp c.2
    exact (bot_le : (⊥ : IntermediateField ↥L K') ≤ M)
      (show θ ((algebraMap ↥L K') c) ∈ (⊥ : IntermediateField ↥L K') from by
        rw [IntermediateField.mem_bot]
        exact ⟨⟨_, hL⟩, rfl⟩))

theorem mem_conjLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (M : IntermediateField ↥L K') (x : K') :
    x ∈ conjLevel L θ hθ M ↔ θ x ∈ M := by
  change θ x ∈ M ↔ θ x ∈ M
  exact Iff.rfl

/-- **The ring isomorphism `θ⁻¹M ≃+* M` given by `θ`.** -/
noncomputable def conjLevelRingEquiv (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') : ↥(conjLevel L θ hθ M) ≃+* ↥M where
  toFun x := ⟨θ x, by
    have := x.2
    rwa [mem_conjLevel L θ hθ M] at this⟩
  invFun y := ⟨θ.symm y, by rw [mem_conjLevel]; simp⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

theorem conjLevelRingEquiv_apply_coe (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') (x : ↥(conjLevel L θ hθ M)) :
    ((conjLevelRingEquiv L θ hθ M x : ↥M) : K') = θ x := rfl

theorem conjLevelRingEquiv_symm_apply_coe (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') (x : ↥M) :
    (((conjLevelRingEquiv L θ hθ M).symm x : ↥(conjLevel L θ hθ M)) : K') = θ.symm x := rfl

/-- **The restriction `θ|_L : L ≃+* L`.** -/
noncomputable def thetaOnL (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) : ↥L ≃+* ↥L where
  toFun x := ⟨θ x, (hθ x).mp x.2⟩
  invFun y := ⟨θ.symm y, (hθ_symm L θ hθ y).mp y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

end Basic

/-! ## The conjugate action on the relative automorphism groups -/

section ConjAction

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
  [Algebra K K'] [IsSepClosure K K']
  (L : IntermediateField K K') [NumberField ↥L]
  (θ : K' ≃+* K')

/-- **Conjugation by `θ` on the relative automorphisms**: `u ↦ θ u θ⁻¹`, an `L`-algebra
automorphism of `M` because `θ(L) = L`. -/
noncomputable def conjLevelAlgEquiv (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') (u : Gal(↥(conjLevel L θ hθ M)/↥L)) : Gal(↥M/↥L) where
  toRingEquiv := (conjLevelRingEquiv L θ hθ M).symm.trans
    (u.toRingEquiv.trans (conjLevelRingEquiv L θ hθ M))
  commutes' c := by
    show conjLevelRingEquiv L θ hθ M
        (u ((conjLevelRingEquiv L θ hθ M).symm (algebraMap ↥L ↥M c))) = algebraMap ↥L ↥M c
    have hmem : θ.symm (c : K') ∈ L := (hθ_symm L θ hθ (c : K')).mp c.2
    have h1 : (conjLevelRingEquiv L θ hθ M).symm (algebraMap ↥L ↥M c)
        = algebraMap ↥L ↥(conjLevel L θ hθ M) (⟨θ.symm (c : K'), hmem⟩ : ↥L) := by
      apply Subtype.ext
      rfl
    rw [h1, AlgEquiv.commutes]
    exact Subtype.ext (by
      rw [conjLevelRingEquiv_apply_coe]
      simp)

theorem conjLevelAlgEquiv_apply (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') (u : Gal(↥(conjLevel L θ hθ M)/↥L)) (x : ↥M) :
    conjLevelAlgEquiv L θ hθ M u x
      = conjLevelRingEquiv L θ hθ M (u ((conjLevelRingEquiv L θ hθ M).symm x)) := rfl

/-- **The conjugate action as a monoid homomorphism** `Gal(θ⁻¹M/L) →* Gal(M/L)`. -/
noncomputable def conjLevelAlgEquivHom (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') :
    Gal(↥(conjLevel L θ hθ M)/↥L) →* Gal(↥M/↥L) where
  toFun := conjLevelAlgEquiv L θ hθ M
  map_one' := by
    ext x
    rw [conjLevelAlgEquiv_apply]
    simp
  map_mul' u v := by
    ext x
    simp only [AlgEquiv.mul_apply, conjLevelAlgEquiv_apply, RingEquiv.symm_apply_apply]

theorem conjLevelAlgEquivHom_apply (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') (u : Gal(↥(conjLevel L θ hθ M)/↥L)) (x : ↥M) :
    conjLevelAlgEquivHom L θ hθ M u x
      = conjLevelRingEquiv L θ hθ M (u ((conjLevelRingEquiv L θ hθ M).symm x)) := rfl

end ConjAction

/-! ## The conjugate level has the same arithmetic structure -/

section Transport

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
  [Algebra K K'] [IsSepClosure K K']
  (L : IntermediateField K K') [NumberField ↥L]
  (θ : K' ≃+* K')

/-- **`θ⁻¹M` is finite over `L`.**  The ring isomorphism `θ : M ≃+* θ⁻¹M` is an isomorphism over
`ℚ` (all ring homomorphisms out of the prime field `ℚ` agree), so it transports
`FiniteDimensional ℚ`; the tower lemma `Module.Finite.of_restrictScalars_finite` then gives
finiteness over `L`. -/
theorem finiteDimensional_conjLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') [FiniteDimensional ↥L ↥M] :
    FiniteDimensional ↥L ↥(conjLevel L θ hθ M) := by
  haveI : IsScalarTower ℚ ↥L ↥M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional ℚ ↥M := FiniteDimensional.trans ℚ ↥L ↥M
  haveI : IsScalarTower ℚ ↥L ↥(conjLevel L θ hθ M) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional ℚ ↥(conjLevel L θ hθ M) :=
    (LinearEquiv.finiteDimensional
      (RingEquiv.toRatAlgEquiv (conjLevelRingEquiv L θ hθ M).symm).toLinearEquiv)
  exact Module.Finite.of_restrictScalars_finite ℚ ↥L ↥(conjLevel L θ hθ M)

/-- **`θ⁻¹M` is normal over `L`**, transported by `Normal.of_equiv_equiv` along the square
`θ⁻¹M ≅ M` over `L ≅ L`. -/
theorem normal_conjLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') [Normal ↥L ↥M] : Normal ↥L ↥(conjLevel L θ hθ M) :=
  Normal.of_equiv_equiv (f := (thetaOnL L θ hθ).symm)
    (g := (conjLevelRingEquiv L θ hθ M).symm) (by ext c; rfl)

/-- **`θ⁻¹M` is a number field** when `M` is. -/
theorem numberField_conjLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') [NumberField ↥M] : NumberField ↥(conjLevel L θ hθ M) :=
  NumberField.of_ringEquiv _ _ (conjLevelRingEquiv L θ hθ M).symm

/-- The instances of the conjugate level, available for type class search: finiteness, normality
and the number-field structure of `θ⁻¹M` are those of `M`. -/
instance instFiniteDimensionalConjLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') [FiniteDimensional ↥L ↥M] :
    FiniteDimensional ↥L ↥(conjLevel L θ hθ M) :=
  finiteDimensional_conjLevel L θ hθ M

instance instNormalConjLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') [Normal ↥L ↥M] : Normal ↥L ↥(conjLevel L θ hθ M) :=
  normal_conjLevel L θ hθ M

instance instNumberFieldConjLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : IntermediateField ↥L K') [NumberField ↥M] : NumberField ↥(conjLevel L θ hθ M) :=
  numberField_conjLevel L θ hθ M

/-- **The conjugate level of a finite normal level**, with its `FrobLevel` structure. -/
noncomputable def conjFrobLevel (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : FrobLevel ↥L K') : FrobLevel ↥L K' where
  L := conjLevel L θ hθ M.L
  finite := finiteDimensional_conjLevel L θ hθ M.L
  normal := normal_conjLevel L θ hθ M.L
  numberField := numberField_conjLevel L θ hθ M.L

end Transport

/-! ## The functoriality of the conjugate action

The restriction of `g ∈ Gal(K'/L)` to the conjugate level `θ⁻¹M`, conjugated by `θ`, is the
restriction of `θ g θ⁻¹` to `M`.  This is the levelwise statement that makes the conjugation
`ringConjHom L θ hθ` compatible with `galToGamma` (`NK.Reconstruct.levelComponent_conj`). -/

section Nat

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
  [Algebra K K'] [IsSepClosure K K']
  (L : IntermediateField K K') [NumberField ↥L]
  (θ : K' ≃+* K')

theorem conjLevelAlgEquivHom_restrictNormalHom (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : FrobLevel ↥L K') (g : Gal(K'/↥L)) :
    conjLevelAlgEquivHom L θ hθ M.L
        (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := K') (conjLevel L θ hθ M.L) g)
      = AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := K') M.L (ringConjAlgEquiv L θ hθ g) := by
  ext x
  rw [conjLevelAlgEquivHom_apply, conjLevelRingEquiv_apply_coe]
  simp only [AlgEquiv.restrictNormalHom_apply]
  rw [ringConjAlgEquiv_apply, conjLevelRingEquiv_symm_apply_coe]

end Nat

end NK.Reconstruct
