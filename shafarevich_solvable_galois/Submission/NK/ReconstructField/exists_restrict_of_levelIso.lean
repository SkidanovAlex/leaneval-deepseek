import Mathlib
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.LevelPrime
import Submission.NK.ReconstructField.eq_of_isNormal_of_algEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restricting a level isomorphism to a smaller level

This file proves `NK.ReconstructField.exists_restrict_of_levelIso`: if `L ≤ E` are finite
levels of `K₁'` with `L` normal over `K₁`, and `σ : ↥E ≃+* ↥(levelMap ϕ E)` is *any* isomorphism
of the corresponding level of `K₂'`, then `σ` restricts to an isomorphism
`τ : ↥L ≃+* ↥(levelMap ϕ L)`, i.e. `σ` carries `L` onto `levelMap ϕ L`.

The mathematical content is the rigidity of the normal level `levelMap ϕ L` over `ℚ`.  Write
`ψ : ↥(levelMap ϕ L) → K₂'` for the `ℚ`-algebra homomorphism
`x ↦ σ (inclusion of σ₀⁻¹ x in E)` built from `σ` and from a chosen level isomorphism
`σ₀ : ↥L ≃+* ↥(levelMap ϕ L)` (whose existence is the hypothesis `hiso`).

* `ψ` maps `levelMap ϕ L` into itself: for `x ∈ levelMap ϕ L`, `ψ x` is a root of
  `minpoly ℚ x`, and *all* roots of `minpoly ℚ x` lie in `levelMap ϕ L` since that field is normal
  (indeed Galois) over `ℚ`.  Equivalently `σ(L) ⊆ levelMap ϕ L`.  This is the lemma
  `mem_of_algHom_of_isNormal` below.
* Applying the same argument to the *inverse* map on the image field `ψ.fieldRange` (which is
  again normal over `ℚ`, being `ℚ`-isomorphic to `levelMap ϕ L`) gives the reverse inclusion:
  `ψ` is surjective onto `levelMap ϕ L`.  Hence `σ(L) = levelMap ϕ L` and `σ|_L` is the required
  isomorphism `τ`.

The two applications of the rigidity lemma are the only field-theoretic inputs; no arithmetic of
the number fields is used.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace NK.ReconstructField

open NK.Reconstruct

/-- **Rigidity of a normal level.** Let `M ⊆ K'` be an intermediate field which is normal over `ℚ`
and let `ψ : ↥M →ₐ[ℚ] K'` be a `ℚ`-algebra homomorphism.  Then `ψ` maps `M` into itself.

Indeed, for `x ∈ M` the element `ψ x` is a root of `minpoly ℚ x` (`ψ` is a `ℚ`-algebra
homomorphism and `x` is a root of its minimal polynomial), and all roots in `K'` of `minpoly ℚ x`
already lie in `M` because `minpoly ℚ x` splits in `M`. -/
lemma mem_of_algHom_of_isNormal {K' : Type*} [Field K'] [Algebra ℚ K']
    (M : IntermediateField ℚ K') [Normal ℚ M] (ψ : ↥M →ₐ[ℚ] K') (x : ↥M) :
    ψ x ∈ (M : Set K') := by
  have hsplit : ((minpoly ℚ x).map (algebraMap ℚ ↥M)).Splits :=
    Normal.splits (inferInstanceAs (Normal ℚ ↥M)) x
  have hne : (minpoly ℚ x).map (algebraMap ℚ ↥M) ≠ 0 :=
    ((minpoly.monic (Normal.isIntegral (inferInstanceAs (Normal ℚ ↥M)) x)).map
      (algebraMap ℚ ↥M)).ne_zero
  have hroot : (((minpoly ℚ x).map (algebraMap ℚ ↥M)).map M.toSubfield.subtype).IsRoot (ψ x) := by
    rw [Polynomial.IsRoot, Polynomial.map_map]
    have hcomp : M.toSubfield.subtype.comp (algebraMap ℚ ↥M) = algebraMap ℚ K' := by
      ext q
      simp
    rw [hcomp, Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
      minpoly.aeval, map_zero]
  exact Polynomial.Splits.mem_subfield_of_isRoot M.toSubfield hsplit hne hroot

/-- **Restriction of a level isomorphism.**  Let `L ≤ E` be finite levels of the separable closure
`K₁'` with `L` normal over `K₁` and `E` a number field, let `σ : ↥E ≃+* ↥(levelMap ϕ E)` be any
isomorphism onto the corresponding level of `K₂'`, and assume the two levels `L` and
`levelMap ϕ L` are isomorphic.  Then the restriction of `σ` to `L` is an isomorphism
`τ : ↥L ≃+* ↥(levelMap ϕ L)` onto the corresponding level. -/
theorem exists_restrict_of_levelIso {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)]
    (E : IntermediateField K₁ K₁') [FiniteDimensional K₁ E] [NumberField ↥E] (hLE : L ≤ E)
    (σ : ↥E ≃+* ↥(NK.Reconstruct.levelMap ϕ E))
    (hiso : Nonempty (↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L))) :
    ∃ τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L),
      ∀ x : ↥L, ((τ x : ↥(NK.Reconstruct.levelMap ϕ L)) : K₂') =
        ((σ ⟨(x : K₁'), hLE x.2⟩ : ↥(NK.Reconstruct.levelMap ϕ E)) : K₂') := by
  -- `K₂'` is an extension of the number field `K₂`, hence a `ℚ`-algebra.
  haveI hchar : CharZero K₂' := ⟨fun m n h => by
    have h' : algebraMap K₂ K₂' (m : K₂) = algebraMap K₂ K₂' (n : K₂) := by simpa using h
    exact Nat.cast_injective (RingHom.injective (algebraMap K₂ K₂') h')⟩
  haveI hst : IsScalarTower ℚ K₂ K₂' := inferInstance
  -- the level `Lv := levelMap ϕ L` is normal over `ℚ`
  let Lv := ↥(NK.Reconstruct.levelMap ϕ L)
  haveI hnormLv : Normal ℚ Lv := IsGalois.to_normal
  obtain ⟨σ₀⟩ := hiso
  -- the `ℚ`-algebra homomorphism `ψE : levelMap ϕ L → K₂'`, `x ↦ σ (σ₀⁻¹ x)`
  let ψE : Lv →ₐ[ℚ] K₂' :=
    { toFun := fun x => (σ ((IntermediateField.inclusion hLE) (σ₀.symm x)) : K₂')
      map_one' := by simp
      map_mul' := by intro a b; simp
      map_zero' := by simp
      map_add' := by intro a b; simp
      commutes' := fun c => by
        show (σ ((IntermediateField.inclusion hLE) (σ₀.symm (algebraMap ℚ Lv c))) : K₂')
          = algebraMap ℚ K₂' c
        rw [show (σ₀.symm (algebraMap ℚ Lv c)) = algebraMap ℚ ↥L c by
          simpa using map_ratCast σ₀.symm c]
        rw [show ((IntermediateField.inclusion hLE) (algebraMap ℚ ↥L c)) = algebraMap ℚ ↥E c by
          exact map_ratCast (IntermediateField.inclusion hLE) c]
        simpa using map_ratCast σ c }
  have hψE_apply : ∀ x : Lv, ψE x =
      (σ ⟨((σ₀.symm x : ↥L) : K₁'), hLE (σ₀.symm x).2⟩ : K₂') := by
    intro x
    dsimp only [ψE]
    congr 3
  -- the same subfield of `K₂'`, viewed as an intermediate field of `K₂'/ℚ`
  let ML' : IntermediateField ℚ K₂' := (NK.Reconstruct.levelMap ϕ L).restrictScalars ℚ
  haveI hnormML' : Normal ℚ ↥ML' := inferInstanceAs (Normal ℚ Lv)
  -- first inclusion: `ψE` maps `levelMap ϕ L` into itself
  have hmem : ∀ x : Lv, ψE x ∈ (NK.Reconstruct.levelMap ϕ L : Set K₂') :=
    fun x => mem_of_algHom_of_isNormal ML' ψE x
  have hF_le : ψE.fieldRange ≤ ML' := by
    intro y hy
    rw [AlgHom.mem_fieldRange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact hmem x
  -- second inclusion: the inverse map on the image field `ψE.fieldRange`, which is normal over `ℚ`
  haveI hF_normal : Normal ℚ ↥(ψE.fieldRange) := Normal.of_algEquiv ψE.equivFieldRange
  let ψ₂ : ↥(ψE.fieldRange) →ₐ[ℚ] K₂' :=
    ((NK.Reconstruct.levelMap ϕ L).val.restrictScalars ℚ).comp ψE.equivFieldRange.symm.toAlgHom
  have h₂ : ∀ y : ↥(ψE.fieldRange), ψ₂ y ∈ (ψE.fieldRange : Set K₂') :=
    fun y => mem_of_algHom_of_isNormal ψE.fieldRange ψ₂ y
  have hψ₂ : ∀ z : ↥(ψE.fieldRange), ψ₂ z = ((ψE.equivFieldRange.symm z : Lv) : K₂') :=
    fun z => rfl
  have hML_le : ML' ≤ ψE.fieldRange := by
    intro y hy
    have hy' : y ∈ (NK.Reconstruct.levelMap ϕ L : Set K₂') := hy
    have h := h₂ (ψE.equivFieldRange ⟨y, hy'⟩)
    rw [hψ₂, AlgEquiv.symm_apply_apply] at h
    simpa using h
  -- hence `σ` maps `L` into `levelMap ϕ L`
  have hτmem : ∀ x : ↥L, (σ ((IntermediateField.inclusion hLE) x) : K₂') ∈
      (NK.Reconstruct.levelMap ϕ L : Set K₂') := by
    intro x
    have h := hmem (σ₀ x)
    rw [hψE_apply, RingEquiv.symm_apply_apply] at h
    exact h
  -- the restriction of `σ` to `L`, as a ring homomorphism into `levelMap ϕ L`
  let τ₀ : ↥L →+* ↥(NK.Reconstruct.levelMap ϕ L) :=
    { toFun := fun x => ⟨(σ ((IntermediateField.inclusion hLE) x) : K₂'), hτmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hτ₀_apply : ∀ x : ↥L, (τ₀ x : K₂') =
      (σ ((IntermediateField.inclusion hLE) x) : K₂') := fun x => rfl
  have hτ₀_inj : Function.Injective τ₀ := by
    intro a b hab
    have h1 : (τ₀ a : K₂') = (τ₀ b : K₂') :=
      congr_arg (fun z : ↥(NK.Reconstruct.levelMap ϕ L) => (z : K₂')) hab
    rw [hτ₀_apply a, hτ₀_apply b] at h1
    have h2 : σ ((IntermediateField.inclusion hLE) a) =
        σ ((IntermediateField.inclusion hLE) b) := Subtype.ext h1
    have h3 : (IntermediateField.inclusion hLE) a = (IntermediateField.inclusion hLE) b :=
      σ.injective h2
    have h4 : (a : K₁') = (b : K₁') := by
      simpa using congr_arg (fun z : ↥E => (z : K₁')) h3
    exact Subtype.ext h4
  have hτ₀_surj : Function.Surjective τ₀ := by
    intro y
    have hy : (y : K₂') ∈ (ψE.fieldRange : Set K₂') := hML_le y.2
    rw [AlgHom.coe_fieldRange] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨σ₀.symm z, ?_⟩
    apply Subtype.ext
    rw [hτ₀_apply]
    rw [← hz, hψE_apply]
    rfl
  have hbij : Function.Bijective τ₀ := ⟨hτ₀_inj, hτ₀_surj⟩
  refine ⟨RingEquiv.ofBijective τ₀ hbij, fun x => ?_⟩
  show ((τ₀ x : ↥(NK.Reconstruct.levelMap ϕ L)) : K₂') = _
  rw [hτ₀_apply]
  rfl

end NK.ReconstructField
