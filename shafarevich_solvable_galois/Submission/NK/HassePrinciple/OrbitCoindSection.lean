import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.HassePrinciple.IdeleOrbitCoind
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.HassePrinciple

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The orbit of `w` and a choice of representatives -/

theorem placeOrbit_finite (w : Place L) : (placeOrbit K L w).Finite := by
  rw [placeOrbit]
  exact orbit_finite w

theorem exists_smul_eq_of_mem_placeOrbit {w v : Place L} (hv : v ∈ placeOrbit K L w) :
    ∃ γ : L ≃ₐ[K] L, γ • v = w := by
  obtain ⟨g, hg⟩ := mem_placeOrbit.mp hv
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

/-- A choice, for every place `v` in the orbit of `w`, of a Galois element `γ` with `γ • v = w`. -/
noncomputable def orbitRepr (w : Place L) (v : Place L) (hv : v ∈ placeOrbit K L w) :
    L ≃ₐ[K] L :=
  Classical.choose (exists_smul_eq_of_mem_placeOrbit (w := w) hv)

theorem orbitRepr_spec (w : Place L) (v : Place L) (hv : v ∈ placeOrbit K L w) :
    orbitRepr w v hv • v = w :=
  Classical.choose_spec (exists_smul_eq_of_mem_placeOrbit (w := w) hv)

/-! ## Elementary lemmas about the local action on `L_wˣ` -/

/-- The inverse of the decomposition-group action on the local units. -/
theorem localUnitsEquiv_inv_apply (w : Place L) (τ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (u : (Place.localField L w)ˣ) :
    localUnitsEquiv (K := K) w τ⁻¹ (localUnitsEquiv (K := K) w τ u) = u := by
  show Units.map (localAut (K := K) w τ⁻¹).toMonoidHom
      (Units.map (localAut (K := K) w τ).toMonoidHom u) = u
  rw [← MonoidHom.comp_apply]
  rw [← Units.map_comp]
  have hcomp : (localAut (K := K) w τ⁻¹).toMonoidHom.comp (localAut (K := K) w τ).toMonoidHom
      = MonoidHom.id (Place.localField L w) := by
    ext y
    show localAut (K := K) w τ⁻¹ (localAut (K := K) w τ y) = y
    have h : localAut (K := K) w τ⁻¹ * localAut (K := K) w τ = 1 := by
      have h1 : (localAutHom (K := K) w) (τ⁻¹ * τ)
          = localAutHom (K := K) w τ⁻¹ * localAutHom (K := K) w τ := map_mul _ _ _
      rw [inv_mul_cancel, map_one] at h1
      exact h1.symm
    calc localAut (K := K) w τ⁻¹ (localAut (K := K) w τ y)
        = (localAut (K := K) w τ⁻¹ * localAut (K := K) w τ) y := rfl
      _ = (1 : Place.localField L w ≃+* Place.localField L w) y := by rw [h]
      _ = y := rfl
  rw [hcomp, Units.map_id]
  rfl

/-- A local field isomorphism cancels against its inverse on units. -/
theorem units_map_ringEquiv_symm {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) (u : Rˣ) :
    Units.map e.symm.toMonoidHom (Units.map e.toMonoidHom u) = u := by
  rw [← MonoidHom.comp_apply]
  rw [← Units.map_comp (f := e.toMonoidHom) (g := e.symm.toMonoidHom)]
  have h : (e.symm.toMonoidHom).comp (e.toMonoidHom) = MonoidHom.id R := by
    ext y
    exact RingEquiv.symm_apply_apply _ _
  rw [h, Units.map_id]
  rfl

/-- The other cancellation of a local field isomorphism with its inverse, on units. -/
theorem units_map_ringEquiv_comp_symm {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S)
    (u : Sˣ) : Units.map e.toMonoidHom (Units.map e.symm.toMonoidHom u) = u := by
  have h := units_map_ringEquiv_symm (R := S) (S := R) e.symm u
  simpa using h

/-- The map induced by the inverse of a local field isomorphism is injective on units. -/
theorem units_map_symm_injective {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) :
    Function.Injective (Units.map e.symm.toMonoidHom : Sˣ → Rˣ) := by
  intro u v huv
  have h := congrArg (Units.map e.toMonoidHom) huv
  rwa [units_map_ringEquiv_comp_symm e u, units_map_ringEquiv_comp_symm e v] at h

/-- The `w`-component of the translate of an idèle by the inverse of an element of the
decomposition group. -/
theorem smul_inv_stabilizer_apply (w : Place L) (τ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (y : Idele L) :
    (τ.1⁻¹ • y) w = Units.map (localAut (K := K) w τ⁻¹).toMonoidHom (y w) := by
  have h : τ.1⁻¹ = ((τ⁻¹ : MulAction.stabilizer (L ≃ₐ[K] L) w)).1 := rfl
  rw [h, smul_apply_stabilizer]

/-! ## The unit-valued function attached to an element of the coinduced module -/

/-- The function `Γ → L_wˣ` underlying an element of `Coind_{Γ_w}^{Γ} L_wˣ`. -/
noncomputable def coindToFun (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) : (L ≃ₐ[K] L) → (Place.localField L w)ˣ :=
  fun γ => Additive.toMul (f.1 γ)

@[simp] theorem coindToFun_apply (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) (γ : L ≃ₐ[K] L) :
    coindToFun w f γ = Additive.toMul (f.1 γ) := rfl

/-- The equivariance of the underlying function of an element of the coinduced module. -/
theorem coindToFun_equivariant (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V)
    (τ : MulAction.stabilizer (L ≃ₐ[K] L) w) (γ : L ≃ₐ[K] L) :
    coindToFun w f (τ.1 * γ) = localUnitsEquiv (K := K) w τ (coindToFun w f γ) := by
  have h := congrArg Additive.toMul (f.2 τ γ)
  have h2 : Additive.toMul ((localUnitsRep K L w).ρ τ (f.1 γ))
      = localUnitsEquiv (K := K) w τ (Additive.toMul (f.1 γ)) := congrArg Additive.toMul
    (show (localUnitsRep K L w).ρ τ (f.1 γ)
        = Additive.ofMul (localUnitsEquiv (K := K) w τ (Additive.toMul (f.1 γ))) from rfl)
  rw [h2] at h
  exact h

/-! ## The coercions between `A_O` and the group `∏_{v ∈ O} L_vˣ` -/

/-- The element of `A_O` attached to an element of `∏_{v ∈ O} L_vˣ`. -/
noncomputable def mulToSupported (w : Place L) (x : ↥(supportedSubgroup (placeOrbit K L w))) :
    (supportedRep K L (orbitStable K L w)).V :=
  (Additive.ofMul x : (supportedRep K L (orbitStable K L w)).V)

/-- The element of `∏_{v ∈ O} L_vˣ` underlying an element of `A_O`. -/
noncomputable def supportedToMul (w : Place L) (x : (supportedRep K L (orbitStable K L w)).V) :
    ↥(supportedSubgroup (placeOrbit K L w)) :=
  (Additive.toMul x : ↥(supportedSubgroup (placeOrbit K L w)))

@[simp] theorem supportedToMul_mulToSupported (w : Place L)
    (x : ↥(supportedSubgroup (placeOrbit K L w))) :
    supportedToMul w (mulToSupported w x) = x := rfl

/-! ## The section idèle -/

/-- The `v`-component of the section of `f` at the place `v`. -/
noncomputable def coindToIdeleFun (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) (v : Place L) : (Place.localField L v)ˣ := by
  classical
  exact if hv : v ∈ placeOrbit K L w then
    ((orbitRepr w v hv)⁻¹ • onePlace w (coindToFun w f (orbitRepr w v hv))) v
  else 1

theorem coindToIdeleFun_eq_one (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) {v : Place L} (hv : v ∉ placeOrbit K L w) :
    coindToIdeleFun w f v = 1 := by
  rw [coindToIdeleFun, dif_neg hv]

theorem coindToIdeleFun_apply_mem (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) {v : Place L} (hv : v ∈ placeOrbit K L w) :
    coindToIdeleFun w f v
      = ((orbitRepr w v hv)⁻¹ • onePlace w (coindToFun w f (orbitRepr w v hv))) v := by
  rw [coindToIdeleFun, dif_pos hv]

/-- **The section idèle**: the idèle supported on the orbit of `w` whose component at
`γ⁻¹ • w` is the transport of `f γ`. -/
noncomputable def coindToIdele (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) : Idele L :=
  ⟨coindToIdeleFun w f, by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (placeOrbit_finite (K := K) w) ?_
    intro v hv
    by_contra hmem
    exact hv (by rw [coindToIdeleFun_eq_one w f hmem]; exact one_mem _)⟩

@[simp] theorem coindToIdele_apply (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) (v : Place L) :
    (coindToIdele w f : Idele L) v = coindToIdeleFun w f v := rfl

/-- **The section of the Shapiro map**, as an element of the idèles supported on the orbit. -/
noncomputable def coindSection (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) :
    ↥(supportedSubgroup (placeOrbit K L w)) :=
  ⟨coindToIdele w f, fun v hv => by
    rw [coindToIdele_apply, coindToIdeleFun_eq_one w f hv]⟩

@[simp] theorem coindSection_coe (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) :
    ((coindSection w f : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L)
      = coindToIdele w f := rfl

theorem coindSection_apply_mem (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) {v : Place L} (hv : v ∈ placeOrbit K L w) :
    ((coindSection w f : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L) v
      = ((orbitRepr w v hv)⁻¹ • onePlace w (coindToFun w f (orbitRepr w v hv))) v := by
  rw [coindSection_coe, coindToIdele_apply, coindToIdeleFun_apply_mem w f hv]

/-! ## The section of the Shapiro map, at the level of the additive group `A_O` -/

/-- The section of the Shapiro map, as an element of `A_O`. -/
noncomputable def coindSectionAdd (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) : (supportedRep K L (orbitStable K L w)).V :=
  mulToSupported w (coindSection w f)

@[simp] theorem supportedToMul_coindSectionAdd (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) :
    supportedToMul w (coindSectionAdd w f) = coindSection w f := rfl

/-! ## The Shapiro map on the section -/

theorem orbitCoindMapA_hom_apply_coe' (w : Place L)
    (x : (supportedRep K L (orbitStable K L w)).V) (γ : L ≃ₐ[K] L) :
    ((orbitCoindMapA K L w).hom x).1 γ
      = Additive.ofMul ((γ • ((supportedToMul w x : ↥(supportedSubgroup (placeOrbit K L w))) :
          Idele L)) w) := by
  rw [orbitCoindMapA, Rep.resCoindToHom_hom_apply_coe]
  rw [orbitCoordA]
  rfl

/-- The value at `γ` of the Shapiro map applied to the section of `f`, in idèle terms. -/
theorem orbitCoindMapA_apply_coindSection (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) (γ : L ≃ₐ[K] L) :
    coindToFun w ((orbitCoindMapA K L w).hom (coindSectionAdd w f)) γ
      = (γ • ((coindSection w f : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L)) w := by
  rw [coindToFun_apply, orbitCoindMapA_hom_apply_coe' w (coindSectionAdd w f) γ,
    supportedToMul_coindSectionAdd]
  rfl

/-- **The `w`-component of the translate of the section is `f γ`.** -/
theorem smul_coindSection_apply (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) (γ : L ≃ₐ[K] L) :
    (γ • ((coindSection w f : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L)) w
      = coindToFun w f γ := by
  rw [Idele.smul_apply]
  have hv : γ⁻¹ • w ∈ placeOrbit K L w := ⟨γ⁻¹, rfl⟩
  rw [coindSection_apply_mem w f hv]
  set γ' := orbitRepr w (γ⁻¹ • w) hv with hγ'def
  set u' := coindToFun w f γ' with hu'def
  have hτmem : γ' * γ⁻¹ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w := by
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    exact orbitRepr_spec w (γ⁻¹ • w) hv
  obtain ⟨τ, hτ⟩ : ∃ σ : MulAction.stabilizer (L ≃ₐ[K] L) w, σ.1 = γ' * γ⁻¹ :=
    ⟨⟨γ' * γ⁻¹, hτmem⟩, rfl⟩
  have hγ'eq : γ' = τ.1 * γ := by rw [hτ, mul_assoc, inv_mul_cancel, mul_one]
  have hu'eq : u' = localUnitsEquiv (K := K) w τ (coindToFun w f γ) := by
    rw [hu'def, hγ'eq, coindToFun_equivariant]
  have hact : actVal γ⁻¹ w (Units.map (localAut (K := K) w τ⁻¹).toMonoidHom u')
      = Units.map (Place.localRingEquiv γ⁻¹ w).toMonoidHom
          (Units.map (localAut (K := K) w τ⁻¹).toMonoidHom u') := rfl
  rw [show γ'⁻¹ = γ⁻¹ * τ.1⁻¹ from by rw [hγ'eq, mul_inv_rev]]
  rw [mul_smul, smul_apply_smul_place, smul_inv_stabilizer_apply, onePlace_apply_self]
  rw [hact, units_map_ringEquiv_symm]
  rw [hu'eq]
  exact localUnitsEquiv_inv_apply w τ (coindToFun w f γ)

/-- **The Shapiro map retracts onto the section**: `t (s f) = f`. -/
theorem orbitCoindMapA_comp_coindSection (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) :
    (orbitCoindMapA K L w).hom (coindSectionAdd w f) = f := by
  apply Subtype.ext
  funext γ
  exact (orbitCoindMapA_apply_coindSection w f γ).trans (smul_coindSection_apply w f γ)

/-! ## Injectivity of the Shapiro map -/

/-- The value at `γ` of the Shapiro map, for an arbitrary element of `A_O`. -/
theorem coindToFun_orbitCoindMapA (w : Place L)
    (x : (supportedRep K L (orbitStable K L w)).V) (γ : L ≃ₐ[K] L) :
    coindToFun w ((orbitCoindMapA K L w).hom x) γ
      = (γ • ((supportedToMul w x : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L)) w := by
  rw [coindToFun_apply, orbitCoindMapA_hom_apply_coe' w x γ]
  rfl

/-- Two idèles agreeing on all translates of their `w`-components agree on the orbit of `w`. -/
theorem eq_of_smul_apply_eq {w : Place L} {x' y' : Idele L}
    (h : ∀ γ : L ≃ₐ[K] L, (γ • x') w = (γ • y') w)
    {v : Place L} {γ : L ≃ₐ[K] L} (hs : γ⁻¹ • w = v) : x' v = y' v := by
  have h1 := h γ
  rw [Idele.smul_apply, Idele.smul_apply] at h1
  have h2 : x' (γ⁻¹ • w) = y' (γ⁻¹ • w) :=
    units_map_symm_injective (Place.localRingEquiv γ⁻¹ w) h1
  have h3 : (hs ▸ x' (γ⁻¹ • w) : (Place.localField L v)ˣ)
      = (hs ▸ y' (γ⁻¹ • w) : (Place.localField L v)ˣ) :=
    congrArg (fun z : (Place.localField L (γ⁻¹ • w))ˣ => (hs ▸ z : (Place.localField L v)ˣ)) h2
  rwa [units_transport hs x', units_transport hs y'] at h3

/-- **The Shapiro map `orbitCoindMapA` is injective.** -/
theorem orbitCoindMapA_injective (w : Place L) :
    Function.Injective (orbitCoindMapA K L w).hom := by
  intro x y h
  set x' : Idele L := ((supportedToMul w x : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L)
    with hx'
  set y' : Idele L := ((supportedToMul w y : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L)
    with hy'
  have hγ : ∀ γ : L ≃ₐ[K] L, (γ • x') w = (γ • y') w := by
    intro γ
    have h1 : coindToFun w ((orbitCoindMapA K L w).hom x) γ
        = coindToFun w ((orbitCoindMapA K L w).hom y) γ := by rw [h]
    rw [coindToFun_orbitCoindMapA, coindToFun_orbitCoindMapA] at h1
    exact h1
  have hmem : ∀ v ∈ placeOrbit K L w, x' v = y' v := by
    intro v hv
    obtain ⟨g, hg⟩ := mem_placeOrbit.mp hv
    exact eq_of_smul_apply_eq (w := w) hγ (v := v) (γ := g⁻¹) (by rw [inv_inv, hg])
  have hxy : x' = y' := by
    refine Idele.ext fun v => ?_
    by_cases hv : v ∈ placeOrbit K L w
    · exact hmem v hv
    · have hx1 : x' v = 1 := by
        rw [hx']; exact mem_supportedSubgroup.mp (supportedToMul w x).2 v hv
      have hy1 : y' v = 1 := by
        rw [hy']; exact mem_supportedSubgroup.mp (supportedToMul w y).2 v hv
      rw [hx1, hy1]
  have hxy' : supportedToMul w x = supportedToMul w y := Subtype.ext hxy
  exact congrArg (fun z : ↥(supportedSubgroup (placeOrbit K L w)) => mulToSupported w z) hxy'

/-! ## Additivity, linearity and equivariance of the section map -/

/-- **The section map is additive.** -/
theorem coindSectionAdd_add (w : Place L)
    (f g : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) :
    coindSectionAdd w (f + g) = coindSectionAdd w f + coindSectionAdd w g := by
  apply orbitCoindMapA_injective (w := w)
  calc (orbitCoindMapA K L w).hom (coindSectionAdd w (f + g))
      = f + g := orbitCoindMapA_comp_coindSection w (f + g)
    _ = (orbitCoindMapA K L w).hom (coindSectionAdd w f)
          + (orbitCoindMapA K L w).hom (coindSectionAdd w g) := by
        rw [orbitCoindMapA_comp_coindSection, orbitCoindMapA_comp_coindSection]
    _ = (orbitCoindMapA K L w).hom (coindSectionAdd w f + coindSectionAdd w g) :=
        ((orbitCoindMapA K L w).hom.map_add' _ _).symm

/-- **The section map is `ℤ`-linear.** -/
theorem coindSectionAdd_smul (w : Place L) (n : CoeffInt.{0})
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) :
    coindSectionAdd w (n • f) = n • coindSectionAdd w f := by
  apply orbitCoindMapA_injective (w := w)
  calc (orbitCoindMapA K L w).hom (coindSectionAdd w (n • f))
      = n • f := orbitCoindMapA_comp_coindSection w (n • f)
    _ = n • (orbitCoindMapA K L w).hom (coindSectionAdd w f) := by
        rw [orbitCoindMapA_comp_coindSection]
    _ = (orbitCoindMapA K L w).hom (n • coindSectionAdd w f) :=
        ((orbitCoindMapA K L w).hom.map_smul' n _).symm

/-- **The section map is `Gal(L/K)`-equivariant.** -/
theorem coindSectionAdd_apply_smul (w : Place L) (γ : L ≃ₐ[K] L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) :
    coindSectionAdd w ((Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
        (localUnitsRep K L w)).ρ γ f)
      = (supportedRep K L (orbitStable K L w)).ρ γ (coindSectionAdd w f) := by
  apply orbitCoindMapA_injective (w := w)
  calc (orbitCoindMapA K L w).hom (coindSectionAdd w ((Rep.coind.{0, 0, 0, 0}
          (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (localUnitsRep K L w)).ρ γ f))
      = (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (localUnitsRep K L w)).ρ γ f := orbitCoindMapA_comp_coindSection w _
    _ = (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (localUnitsRep K L w)).ρ γ ((orbitCoindMapA K L w).hom (coindSectionAdd w f)) := by
        rw [orbitCoindMapA_comp_coindSection]
    _ = (orbitCoindMapA K L w).hom
          ((supportedRep K L (orbitStable K L w)).ρ γ (coindSectionAdd w f)) :=
        (Rep.hom_comm_apply (orbitCoindMapA K L w) γ (coindSectionAdd w f)).symm

/-- **The left inverse of the Shapiro map `orbitCoindMapA`, as a morphism of
`Gal(L/K)`-representations.** -/
noncomputable def coindSectionHom (w : Place L) :
    (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (localUnitsRep K L w)) ⟶
      supportedRep K L (orbitStable K L w) :=
  Rep.ofHom
    { toFun := fun f => coindSectionAdd w f
      map_add' := fun f g => coindSectionAdd_add w f g
      map_smul' := fun n f => coindSectionAdd_smul w n f
      isIntertwining' := fun γ => by
        apply LinearMap.ext
        intro f
        exact coindSectionAdd_apply_smul w γ f }

@[simp] theorem coindSectionHom_apply (w : Place L)
    (f : (Rep.coind.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
      (localUnitsRep K L w)).V) :
    (coindSectionHom (K := K) (L := L) w) f = coindSectionAdd w f := rfl

/-- **The Shapiro map composed with its section is the identity.** -/
theorem orbitCoindMapA_comp_coindSectionHom (w : Place L) :
    CategoryTheory.CategoryStruct.comp (orbitCoindMapA K L w) (coindSectionHom w) =
      CategoryTheory.CategoryStruct.id (supportedRep K L (orbitStable K L w)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show (coindSectionHom w).hom ((orbitCoindMapA K L w).hom x) = x
  have h2 : (coindSectionHom w).hom ((orbitCoindMapA K L w).hom x)
      = coindSectionAdd w ((orbitCoindMapA K L w).hom x) := rfl
  rw [h2]
  exact orbitCoindMapA_injective (w := w)
    (orbitCoindMapA_comp_coindSection w ((orbitCoindMapA K L w).hom x))

end

end NK.HassePrinciple
