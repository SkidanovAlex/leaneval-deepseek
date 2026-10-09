import Mathlib
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.ReconstructField.eq_of_isNormal_of_algEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace NK.Reconstruct

open NK.Reconstruct

/-!
# Restriction of a level isomorphism to a sublevel

The mathematical content of `NK.Reconstruct.levelIsoRestrict` is the rigidity of a level that is
normal over `ℚ`.  Two subfields of `K₂'` that are both isomorphic (over `ℚ`) to a field normal over
`ℚ` and lie in a common ambient field coincide; indeed any `ℚ`-algebra homomorphism out of a normal
extension into the ambient field lands back in the extension (`mem_of_algHom_of_isNormal`).  Applying
this to the image of `L` under the level isomorphism `τ` and to the normal level `levelMap ϕ L`, in
both directions, shows that `τ` carries `L` exactly onto `levelMap ϕ L`.
-/

/-- **Rigidity of a level normal over `ℚ`.**  Let `M ⊆ K'` be an intermediate field which is normal
over `ℚ` and let `ψ : ↥M →ₐ[ℚ] K'` be a `ℚ`-algebra homomorphism.  Then `ψ` maps `M` into itself.

Indeed, for `x ∈ M` the element `ψ x` is a root of `minpoly ℚ x` (`ψ` is a `ℚ`-algebra
homomorphism and `x` is a root of its minimal polynomial), and all roots in `K'` of `minpoly ℚ x`
already lie in `M` because `minpoly ℚ x` splits in `M`. -/
lemma mem_algHom_of_normal_over_rat {K' : Type*} [Field K'] [Algebra ℚ K']
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

/-- **The restriction of a level isomorphism to a sublevel.**  Let `L ⊆ M` be finite levels of `K₁'/K₁`
with `L` normal over `K₁`, `L` and `levelMap ϕ L` number fields, and `levelMap ϕ L` Galois over `ℚ`.
If there is *some* ring isomorphism `↥L ≃+* ↥(levelMap ϕ L)` (the level-wise weak Neukirch–Uchida
input), then any ring isomorphism `τ : ↥M ≃+* ↥(levelMap ϕ M)` carries `L` onto `levelMap ϕ L`, i.e.
its restriction to `L` lands in `levelMap ϕ L` and induces `τ' : ↥L ≃+* ↥(levelMap ϕ L)` with
`(τ' x : K₂') = τ ⟨(x : K₁'), hLM x.2⟩` for all `x : ↥L`. -/
theorem levelIsoRestrict {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (L M : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₁ M] (hLM : L ≤ M)
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)]
    (hiso : Nonempty (↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L)))
    (τ : ↥M ≃+* ↥(NK.Reconstruct.levelMap ϕ M)) :
    ∃ τ' : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L),
      ∀ x : ↥L, (τ' x : K₂') = τ ⟨(x : K₁'), hLM x.2⟩ := by
  -- `K₂'` is an extension of the number field `K₂`, hence a `ℚ`-algebra.
  haveI hchar : CharZero K₂' := ⟨fun m n h => by
    have h' : algebraMap K₂ K₂' (m : K₂) = algebraMap K₂ K₂' (n : K₂) := by simpa using h
    exact Nat.cast_injective (RingHom.injective (algebraMap K₂ K₂') h')⟩
  haveI hst : IsScalarTower ℚ K₂ K₂' := inferInstance
  -- the level `Lv := levelMap ϕ L` is normal over `ℚ`
  let Lv := ↥(NK.Reconstruct.levelMap ϕ L)
  haveI hnormLv : Normal ℚ Lv := IsGalois.to_normal
  obtain ⟨σ₀⟩ := hiso
  -- the `ℚ`-algebra homomorphism `ψE : levelMap ϕ L → K₂'`, `x ↦ τ (σ₀⁻¹ x)`
  let ψE : Lv →ₐ[ℚ] K₂' :=
    { toFun := fun x => (τ ((IntermediateField.inclusion hLM) (σ₀.symm x)) : K₂')
      map_one' := by simp
      map_mul' := by intro a b; simp
      map_zero' := by simp
      map_add' := by intro a b; simp
      commutes' := fun c => by
        show (τ ((IntermediateField.inclusion hLM) (σ₀.symm (algebraMap ℚ Lv c))) : K₂')
          = algebraMap ℚ K₂' c
        rw [show (σ₀.symm (algebraMap ℚ Lv c)) = algebraMap ℚ ↥L c by
          simpa using map_ratCast σ₀.symm c]
        rw [show ((IntermediateField.inclusion hLM) (algebraMap ℚ ↥L c)) = algebraMap ℚ ↥M c by
          exact map_ratCast (IntermediateField.inclusion hLM) c]
        simpa using map_ratCast τ c }
  have hψE_apply : ∀ x : Lv, ψE x =
      (τ ⟨((σ₀.symm x : ↥L) : K₁'), hLM (σ₀.symm x).2⟩ : K₂') := by
    intro x
    dsimp only [ψE]
    congr 3
  -- the same subfield of `K₂'`, viewed as an intermediate field of `K₂'/ℚ`
  let ML' : IntermediateField ℚ K₂' := (NK.Reconstruct.levelMap ϕ L).restrictScalars ℚ
  haveI hnormML' : Normal ℚ ↥ML' := inferInstanceAs (Normal ℚ Lv)
  -- first inclusion: `ψE` maps `levelMap ϕ L` into itself
  have hmem : ∀ x : Lv, ψE x ∈ (NK.Reconstruct.levelMap ϕ L : Set K₂') :=
    fun x => mem_algHom_of_normal_over_rat ML' ψE x
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
    fun y => mem_algHom_of_normal_over_rat ψE.fieldRange ψ₂ y
  have hψ₂ : ∀ z : ↥(ψE.fieldRange), ψ₂ z = ((ψE.equivFieldRange.symm z : Lv) : K₂') :=
    fun z => rfl
  have hML_le : ML' ≤ ψE.fieldRange := by
    intro y hy
    have hy' : y ∈ (NK.Reconstruct.levelMap ϕ L : Set K₂') := hy
    have h := h₂ (ψE.equivFieldRange ⟨y, hy'⟩)
    rw [hψ₂, AlgEquiv.symm_apply_apply] at h
    simpa using h
  -- hence `τ` maps `L` into `levelMap ϕ L`
  have hτmem : ∀ x : ↥L, (τ ((IntermediateField.inclusion hLM) x) : K₂') ∈
      (NK.Reconstruct.levelMap ϕ L : Set K₂') := by
    intro x
    have h := hmem (σ₀ x)
    rw [hψE_apply, RingEquiv.symm_apply_apply] at h
    exact h
  -- the restriction of `τ` to `L`, as a ring homomorphism into `levelMap ϕ L`
  let τr : ↥L →+* ↥(NK.Reconstruct.levelMap ϕ L) :=
    { toFun := fun x => ⟨(τ ((IntermediateField.inclusion hLM) x) : K₂'), hτmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hτr_apply : ∀ x : ↥L, (τr x : K₂') =
      (τ ((IntermediateField.inclusion hLM) x) : K₂') := fun x => rfl
  have hτr_inj : Function.Injective τr := by
    intro a b hab
    have h1 : (τr a : K₂') = (τr b : K₂') :=
      congr_arg (fun z : ↥(NK.Reconstruct.levelMap ϕ L) => (z : K₂')) hab
    rw [hτr_apply a, hτr_apply b] at h1
    have h2 : τ ((IntermediateField.inclusion hLM) a) =
        τ ((IntermediateField.inclusion hLM) b) := Subtype.ext h1
    have h3 : (IntermediateField.inclusion hLM) a = (IntermediateField.inclusion hLM) b :=
      τ.injective h2
    have h4 : (a : K₁') = (b : K₁') := by
      simpa using congr_arg (fun z : ↥M => (z : K₁')) h3
    exact Subtype.ext h4
  have hτr_surj : Function.Surjective τr := by
    intro y
    have hy : (y : K₂') ∈ (ψE.fieldRange : Set K₂') := hML_le y.2
    rw [AlgHom.coe_fieldRange] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨σ₀.symm z, ?_⟩
    apply Subtype.ext
    rw [hτr_apply]
    rw [← hz, hψE_apply]
    rfl
  have hbij : Function.Bijective τr := ⟨hτr_inj, hτr_surj⟩
  refine ⟨RingEquiv.ofBijective τr hbij, fun x => ?_⟩
  show ((τr x : ↥(NK.Reconstruct.levelMap ϕ L)) : K₂') = _
  rw [hτr_apply]
  rfl

end NK.Reconstruct
