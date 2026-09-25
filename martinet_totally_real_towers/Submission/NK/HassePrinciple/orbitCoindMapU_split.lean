import Mathlib
import Submission.NK.HassePrinciple.IdeleOrbitCoind

namespace NK.HassePrinciple

open NK.GlobalCFT
open CategoryTheory Representation

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The coinduced module `Coind_{Γ_w}^{Γ} 𝒪_wˣ`, at the fixed coefficient universe. -/
noncomputable abbrev coindRep (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L) :=
  Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (localUnitsSubRep K L w)

/-! ## The orbit of a place and a choice of a Galois element producing it -/

/-- For `v` in the `Gal(L/K)`-orbit of `w`, the chosen `g : Gal(L/K)` with `g • w = v`. -/
noncomputable def orbitWitness (w : Place L) (v : Place L)
    (hv : v ∈ (orbitStable K L w).carrier) : L ≃ₐ[K] L :=
  Classical.choose (mem_placeOrbit.mp hv)

theorem orbitWitness_spec (w : Place L) (v : Place L)
    (hv : v ∈ (orbitStable K L w).carrier) :
    orbitWitness w v hv • w = v :=
  Classical.choose_spec (mem_placeOrbit.mp hv)

theorem orbitStable_smul_mem (w : Place L) (γ : L ≃ₐ[K] L) :
    γ • w ∈ (orbitStable K L w).carrier :=
  show (γ • w) ∈ placeOrbit K L w from mem_placeOrbit.mpr ⟨γ, rfl⟩

/-! ## Transport lemmas -/

theorem units_cast_mul {a b : Place L} (h : a = b) (x y : (Place.localField L a)ˣ) :
    (h ▸ (x * y) : (Place.localField L b)ˣ) = (h ▸ x) * (h ▸ y) := by
  cases h; rfl

theorem units_cast_zpow {a b : Place L} (h : a = b) (x : (Place.localField L a)ˣ) (z : ℤ) :
    (h ▸ (x ^ z) : (Place.localField L b)ˣ) = (h ▸ x) ^ z := by
  cases h; rfl

theorem units_eqRec_symm_eqRec {a b : Place L} (h : a = b) (z : (Place.localField L a)ˣ) :
    (h.symm ▸ (h ▸ z) : (Place.localField L a)ˣ) = z := by cases h; rfl

theorem units_eqRec_trans {a b c : Place L} (h₁ : a = b) (h₂ : b = c)
    (x : (Place.localField L a)ˣ) :
    (h₁.trans h₂ ▸ x : (Place.localField L c)ˣ) = (h₂ ▸ (h₁ ▸ x)) := by
  cases h₁; cases h₂; rfl

theorem actVal_zpow (g : L ≃ₐ[K] L) (v : Place L) (u : (Place.localField L v)ˣ) (n : ℤ) :
    actVal g v (u ^ n) = (actVal g v u) ^ n := by
  rw [actVal]
  exact map_zpow _ _ _

theorem Units_map_localRingEquiv_symm (g : L ≃ₐ[K] L) (v : Place L)
    (a : (Place.localField L (g • v))ˣ) :
    Units.map (Place.localRingEquiv g v).toMonoidHom
      (Units.map (Place.localRingEquiv g v).symm.toMonoidHom a) = a := by
  ext
  rw [Units.coe_map, Units.coe_map]
  exact RingEquiv.apply_symm_apply (Place.localRingEquiv g v) (a : Place.localField L (g • v))

theorem Units_map_localRingEquiv_symm_apply (g : L ≃ₐ[K] L) (v : Place L)
    (a : (Place.localField L v)ˣ) :
    Units.map (Place.localRingEquiv g v).symm.toMonoidHom
      (Units.map (Place.localRingEquiv g v).toMonoidHom a) = a := by
  ext
  rw [Units.coe_map, Units.coe_map]
  exact RingEquiv.symm_apply_apply (Place.localRingEquiv g v) (a : Place.localField L v)

/-- Transport of `actVal` along an equality of Galois elements. -/
theorem actVal_eq_of_eq (w : Place L) {σ σ' : L ≃ₐ[K] L} (h : σ = σ')
    (u : (Place.localField L w)ˣ) :
    actVal σ w u = (congrArg (fun x : L ≃ₐ[K] L => x • w) h).symm ▸ actVal σ' w u := by
  cases h; rfl

/-- Transport of `actVal` along an equality of places. -/
theorem actVal_place_cast (g : L ≃ₐ[K] L) {a b : Place L} (h : a = b)
    (u : (Place.localField L a)ˣ) :
    actVal g b (h ▸ u) = (congrArg (fun x : Place L => g • x) h) ▸ actVal g a u := by
  cases h; rfl

theorem actVal_stab_lu (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (u : (Place.localField L w)ˣ) :
    actVal σ.1 w (localUnitsEquiv (K := K) w σ⁻¹ u)
      = (MulAction.mem_stabilizer_iff.mp σ.2).symm ▸ u := by
  have h := actVal_stabilizer w σ (localUnitsEquiv (K := K) w σ⁻¹ u)
  have h2 : Units.map (localAut w σ).toMonoidHom (localUnitsEquiv (K := K) w σ⁻¹ u) = u := by
    rw [show Units.map (localAut w σ).toMonoidHom (localUnitsEquiv (K := K) w σ⁻¹ u)
        = (localUnitsEquiv (K := K) w σ * localUnitsEquiv (K := K) w (σ⁻¹)) u from rfl]
    rw [← localUnitsEquiv_mul, mul_inv_cancel, localUnitsEquiv_one]
    rfl
  rw [h2] at h
  have h3 := (units_eqRec_symm_eqRec (MulAction.mem_stabilizer_iff.mp σ.2)
    (actVal σ.1 w (localUnitsEquiv (K := K) w σ⁻¹ u))).symm
  rw [h] at h3
  exact h3

/-! ## Extracting the local unit of a cochain value -/

/-- The local unit of `L_wˣ` underlying the value at `g` of an element `f` of the coinduced
module `Coind_{Γ_w}^{Γ}(𝒪_wˣ)`. -/
noncomputable def coindUnit (w : Place L)
    (f : (coindRep K L w).V) (g : L ≃ₐ[K] L) : (Place.localField L w)ˣ :=
  ((Additive.toMul (f.1 g) : ↥(Place.localUnits L w)) : (Place.localField L w)ˣ)

theorem coindUnit_mul_stabilizer (w : Place L)
    (f : (coindRep K L w).V) (γ : L ≃ₐ[K] L)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    coindUnit w f ((γ * σ.1))⁻¹ = localUnitsEquiv (K := K) w σ⁻¹ (coindUnit w f γ⁻¹) := by
  have h : (f.1 ((γ * σ.1))⁻¹ : (localUnitsSubRep K L w).V)
      = (localUnitsSubRep K L w).ρ σ⁻¹ (f.1 γ⁻¹) := by
    have h2 : (γ * σ.1)⁻¹ = (↑(σ⁻¹) : L ≃ₐ[K] L) * γ⁻¹ := by
      rw [mul_inv_rev, Subgroup.coe_inv]
    rw [h2]
    exact f.2 (σ⁻¹) (γ⁻¹)
  rw [coindUnit, coindUnit, h, localUnitsSubRep_ρ_apply, toMul_ofMul]
  rfl

theorem coindUnit_add (w : Place L)
    (f g : (coindRep K L w).V) (σ : L ≃ₐ[K] L) :
    coindUnit w (f + g) σ = coindUnit w f σ * coindUnit w g σ := by
  rw [coindUnit, coindUnit, coindUnit]
  rw [show (f + g).1 σ = f.1 σ + g.1 σ from rfl]
  rw [toMul_add]
  rfl

theorem coindUnit_zsmul (w : Place L)
    (f : (coindRep K L w).V) (n : ℤ) (σ : L ≃ₐ[K] L) :
    coindUnit w (n • f) σ = (coindUnit w f σ) ^ n := by
  rw [coindUnit, coindUnit]
  rw [show (n • f).1 σ = n • f.1 σ from rfl]
  rw [toMul_zsmul]
  rfl

theorem coindUnit_zero (w : Place L) :
    ∀ σ : L ≃ₐ[K] L, coindUnit (K := K) w (0 :
      (coindRep K L w).V) σ = 1 := by
  intro σ
  rw [coindUnit]
  rfl

theorem coindUnit_mem (w : Place L)
    (f : (coindRep K L w).V) (σ : L ≃ₐ[K] L) :
    coindUnit w f σ ∈ Place.localUnits L w :=
  (Additive.toMul (f.1 σ) : ↥(Place.localUnits L w)).2

theorem coindUnit_injective (w : Place L)
    (g₁ g₂ : (coindRep K L w).V) (γ : L ≃ₐ[K] L)
    (h : coindUnit w g₁ γ = coindUnit w g₂ γ) : g₁.1 γ = g₂.1 γ :=
  Additive.toMul.injective (Subtype.ext h)

/-! ## Spreading a local unit on the orbit -/

/-- The component at `v` of the idèle obtained by spreading out the local unit `f` of the
coinduced module: at `v = g • w` it is the transport of `actVal g w (f g⁻¹)`. -/
noncomputable def orbitSpreadVal (w : Place L)
    (f : (coindRep K L w).V) (v : Place L) : (Place.localField L v)ˣ := by
  classical
  exact if hv : v ∈ (orbitStable K L w).carrier then
    (orbitWitness_spec w v hv) ▸ actVal (orbitWitness w v hv) w
      (coindUnit w f ((orbitWitness w v hv))⁻¹)
  else 1

/-- Computation rule for `orbitSpreadVal` at a place of the orbit. -/
theorem orbitSpreadVal_of_mem (w : Place L)
    (f : (coindRep K L w).V) {v : Place L} (hv : v ∈ (orbitStable K L w).carrier) :
    orbitSpreadVal w f v = (orbitWitness_spec w v hv) ▸ actVal (orbitWitness w v hv) w
      (coindUnit w f ((orbitWitness w v hv))⁻¹) := by
  rw [orbitSpreadVal, dif_pos hv]

/-- Computation rule for `orbitSpreadVal` away from the orbit. -/
theorem orbitSpreadVal_of_notMem (w : Place L)
    (f : (coindRep K L w).V) {v : Place L} (hv : v ∉ (orbitStable K L w).carrier) :
    orbitSpreadVal w f v = 1 := by
  rw [orbitSpreadVal, dif_neg hv]

/-- **Consistency of the choice of a representative**: two Galois elements mapping `w` to the
same place give the same local unit. -/
theorem orbitSpreadVal_actVal_of_smul_eq (w : Place L)
    (f : (coindRep K L w).V)
    {g₁ g₂ : L ≃ₐ[K] L} (h : g₁ • w = g₂ • w) :
    (h ▸ actVal g₁ w (coindUnit w f g₁⁻¹)) = actVal g₂ w (coindUnit w f g₂⁻¹) := by
  have hτ : (g₂⁻¹ * g₁) • w = w := by rw [mul_smul, h, inv_smul_smul]
  let τ : MulAction.stabilizer (L ≃ₐ[K] L) w := ⟨g₂⁻¹ * g₁, hτ⟩
  have hg₁ : g₁ = g₂ * τ.1 := by show g₁ = g₂ * (g₂⁻¹ * g₁); group
  have hc : coindUnit w f g₁⁻¹ = localUnitsEquiv (K := K) w τ⁻¹ (coindUnit w f g₂⁻¹) := by
    rw [hg₁]
    exact coindUnit_mul_stabilizer w f g₂ τ
  set V := actVal g₂ w (coindUnit w f g₂⁻¹) with hV
  set a₀ := (congrArg (fun x : L ≃ₐ[K] L => x • w) hg₁).symm with ha₀
  set b₀ := (mul_smul g₂ τ.1 w).symm with hb₀
  set c₀ := (congrArg (fun x : Place L => g₂ • x)
    (MulAction.mem_stabilizer_iff.mp τ.2).symm) with hc₀
  have hX : actVal g₁ w (coindUnit w f g₁⁻¹) = (c₀.trans (b₀.trans a₀)) ▸ V := by
    calc actVal g₁ w (coindUnit w f g₁⁻¹)
        = a₀ ▸ actVal (g₂ * τ.1) w (coindUnit w f g₁⁻¹) := actVal_eq_of_eq w hg₁ _
      _ = a₀ ▸ actVal (g₂ * τ.1) w (localUnitsEquiv (K := K) w τ⁻¹ (coindUnit w f g₂⁻¹)) :=
            by rw [hc]
      _ = a₀ ▸ (b₀ ▸ actVal g₂ (τ.1 • w)
            (actVal τ.1 w (localUnitsEquiv (K := K) w τ⁻¹ (coindUnit w f g₂⁻¹)))) :=
            by rw [actVal_comp]
      _ = a₀ ▸ (b₀ ▸ actVal g₂ (τ.1 • w)
            ((MulAction.mem_stabilizer_iff.mp τ.2).symm ▸ (coindUnit w f g₂⁻¹))) :=
            by rw [actVal_stab_lu w]
      _ = a₀ ▸ (b₀ ▸ (c₀ ▸ V)) := by rw [actVal_place_cast]
      _ = (c₀.trans (b₀.trans a₀)) ▸ V := by
            rw [← units_eqRec_trans b₀ a₀ (c₀ ▸ V),
              ← units_eqRec_trans c₀ (b₀.trans a₀) V]
  rw [hX]
  rw [← units_eqRec_trans (c₀.trans (b₀.trans a₀)) h V]

/-- **The spreading value at any place of the orbit, for any witnessing Galois element.** -/
theorem orbitSpreadVal_eq_actVal (w : Place L)
    (f : (coindRep K L w).V) {v : Place L} (hv : v ∈ (orbitStable K L w).carrier)
    (g : L ≃ₐ[K] L) (hg : g • w = v) :
    orbitSpreadVal w f v = hg ▸ actVal g w (coindUnit w f g⁻¹) := by
  rw [orbitSpreadVal_of_mem w f hv]
  have hcons := orbitSpreadVal_actVal_of_smul_eq w f (g₁ := orbitWitness w v hv) (g₂ := g)
    ((orbitWitness_spec w v hv).trans hg.symm)
  have h4 := congrArg (fun z => hg ▸ z) hcons
  rw [units_eqRec_trans (orbitWitness_spec w v hv) hg.symm _] at h4
  rw [← units_eqRec_trans hg.symm hg _] at h4
  rw [Subsingleton.elim (hg.symm.trans hg) rfl] at h4
  exact h4

theorem orbitSpreadVal_mem_localUnits (w : Place L)
    (f : (coindRep K L w).V) (v : Place L) :
    orbitSpreadVal w f v ∈ Place.localUnits L v := by
  by_cases hv : v ∈ (orbitStable K L w).carrier
  · rw [orbitSpreadVal_eq_actVal w f hv (orbitWitness w v hv) (orbitWitness_spec w v hv)]
    exact (mem_localUnits_of_eq' (orbitWitness_spec w v hv) _).mp
      ((Place.localRingEquiv_mem_localUnits (orbitWitness w v hv) w
        (coindUnit w f ((orbitWitness w v hv))⁻¹)).mp (coindUnit_mem w f _))
  · rw [orbitSpreadVal_of_notMem w f hv]
    exact Subgroup.one_mem _

/-! ## The spread-out idèle -/

/-- The idèle obtained by spreading out the local unit `f` of the coinduced module along the
orbit of `w`. -/
noncomputable def orbitSpread (w : Place L)
    (f : (coindRep K L w).V) : Idele L :=
  ⟨fun v => orbitSpreadVal w f v, by
    rw [Filter.eventually_cofinite]
    exact Set.Finite.subset Set.finite_empty
      (fun v hv => absurd (orbitSpreadVal_mem_localUnits w f v) hv)⟩

@[simp] theorem orbitSpread_apply (w : Place L)
    (f : (coindRep K L w).V) (v : Place L) :
    orbitSpread w f v = orbitSpreadVal w f v := rfl

theorem orbitSpread_mem (w : Place L)
    (f : (coindRep K L w).V) :
    orbitSpread w f ∈ orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier := by
  rw [mem_orbitUnitsSubgroup]
  exact ⟨fun v hv => orbitSpreadVal_of_notMem w f hv,
    fun v => orbitSpreadVal_mem_localUnits w f v⟩

theorem orbitSpread_zero (w : Place L) :
    orbitSpread (K := K) w (0 : (coindRep K L w).V) = 1 := by
  apply Idele.ext
  intro v
  rw [Idele.one_apply, orbitSpread_apply]
  by_cases hv : v ∈ (orbitStable K L w).carrier
  · rw [orbitSpreadVal_of_mem w (0 : (coindRep K L w).V) hv]
    rw [coindUnit_zero, actVal_one, cast_one]
  · rw [orbitSpreadVal_of_notMem w (0 : (coindRep K L w).V) hv]

theorem orbitSpreadVal_add (w : Place L)
    (f g : (coindRep K L w).V) (v : Place L) :
    orbitSpreadVal w (f + g) v = orbitSpreadVal w f v * orbitSpreadVal w g v := by
  by_cases hv : v ∈ (orbitStable K L w).carrier
  · rw [orbitSpreadVal_eq_actVal w (f + g) hv (orbitWitness w v hv) (orbitWitness_spec w v hv),
      orbitSpreadVal_eq_actVal w f hv (orbitWitness w v hv) (orbitWitness_spec w v hv),
      orbitSpreadVal_eq_actVal w g hv (orbitWitness w v hv) (orbitWitness_spec w v hv)]
    rw [coindUnit_add, actVal_mul, units_cast_mul]
  · rw [orbitSpreadVal_of_notMem w (f + g) hv, orbitSpreadVal_of_notMem w f hv,
      orbitSpreadVal_of_notMem w g hv, one_mul]

theorem orbitSpread_add (w : Place L)
    (f g : (coindRep K L w).V) :
    orbitSpread w (f + g) = orbitSpread w f * orbitSpread w g := by
  apply Idele.ext
  intro v
  rw [Idele.mul_apply, orbitSpread_apply, orbitSpread_apply, orbitSpread_apply,
    orbitSpreadVal_add]

theorem orbitSpreadVal_zsmul (w : Place L)
    (f : (coindRep K L w).V) (n : ℤ) (v : Place L) :
    orbitSpreadVal w (n • f) v = (orbitSpreadVal w f v) ^ n := by
  by_cases hv : v ∈ (orbitStable K L w).carrier
  · rw [orbitSpreadVal_eq_actVal w (n • f) hv (orbitWitness w v hv) (orbitWitness_spec w v hv),
      orbitSpreadVal_eq_actVal w f hv (orbitWitness w v hv) (orbitWitness_spec w v hv)]
    rw [coindUnit_zsmul, actVal_zpow, units_cast_zpow]
  · rw [orbitSpreadVal_of_notMem w (n • f) hv, orbitSpreadVal_of_notMem w f hv, one_zpow]

theorem orbitSpread_zsmul (w : Place L)
    (f : (coindRep K L w).V) (n : ℤ) :
    orbitSpread w (n • f) = (orbitSpread w f) ^ n := by
  apply Idele.ext
  intro v
  show orbitSpreadVal w (n • f) v = (orbitSpread w f ^ n) v
  rw [orbitSpreadVal_zsmul]
  exact (map_zpow (Idele.eval v) (orbitSpread w f) n).symm

/-! ## Reading the orbit coinduction map on idèles -/

/-- The idèle (an element of `∏_{v ∈ O} 𝒪_vˣ`) underlying an element of the orbit-units
representation. -/
noncomputable def orbitUnitsOf (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) :
    ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier) :=
  let u : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier) := x
  u

theorem orbitUnitsOf_eq (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) :
    orbitUnitsOf w x = (Additive.toMul x :
      ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) := by
  simp only [orbitUnitsOf]
  rfl

/-- The same idèle, read as an element of `𝕀_L`. -/
noncomputable def orbitUnitsVal (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) : Idele L :=
  ((orbitUnitsOf w x : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) : Idele L)

theorem orbitUnitsOf_nonmem (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) {v : Place L}
    (hv : v ∉ (orbitStable K L w).carrier) :
    orbitUnitsVal w x v = 1 :=
  (mem_orbitUnitsSubgroup.mp (orbitUnitsOf w x).property).1 v hv

/-- **The action on the orbit-units idèles is the natural action on `𝕀_L`.** -/
theorem orbitUnitsVal_action (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) (γ : L ≃ₐ[K] L) :
    orbitUnitsVal w ((orbitUnitsRep K L (orbitStable K L w)).ρ γ x)
      = γ • orbitUnitsVal w x := by
  show ((Additive.toMul ((orbitUnitsRep K L (orbitStable K L w)).ρ γ x) :
      ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) : Idele L) = _
  rw [orbitUnitsRep_ρ_apply, toMul_ofMul]
  rfl

/-- **The value of `orbitCoindMapU` at `γ`** is the `w`-component of the translate of the
underlying idèle. -/
theorem coindUnit_orbitCoindMapU (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) (γ : L ≃ₐ[K] L) :
    coindUnit w ((orbitCoindMapU K L w).hom x) γ = (γ • orbitUnitsVal w x) w := by
  have h1 : coindUnit w ((orbitCoindMapU K L w).hom x) γ
      = (orbitEvalU K L w (Additive.toMul ((orbitUnitsRep K L (orbitStable K L w)).ρ γ x)) :
          (Place.localField L w)ˣ) := by
    rw [coindUnit]
    rw [show ((orbitCoindMapU K L w).hom x).1 γ
        = orbitCoordU K L w ((orbitUnitsRep K L (orbitStable K L w)).ρ γ x) from rfl]
    rw [show orbitCoordU K L w ((orbitUnitsRep K L (orbitStable K L w)).ρ γ x)
        = Additive.ofMul (orbitEvalU K L w
            (Additive.toMul ((orbitUnitsRep K L (orbitStable K L w)).ρ γ x))) from rfl]
    rfl
  have h2 : ((Additive.toMul ((orbitUnitsRep K L (orbitStable K L w)).ρ γ x) :
        ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))) : Idele L)
      = γ • orbitUnitsVal w x := by
    show ((Additive.toMul ((orbitUnitsRep K L (orbitStable K L w)).ρ γ x) :
        ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) : Idele L) = _
    rw [orbitUnitsRep_ρ_apply, toMul_ofMul]
    rfl
  rw [h1, orbitEvalU_apply, h2]

/-- **The retraction identity on idèles**: spreading out the `γ`-values of `orbitCoindMapU`
recovers the original idèle of `∏_{v ∈ O} 𝒪_vˣ`. -/
theorem orbitSpreadVal_orbitCoindMapU (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) (v : Place L) :
    orbitSpreadVal w ((orbitCoindMapU K L w).hom x) v = orbitUnitsVal w x v := by
  by_cases hv : v ∈ (orbitStable K L w).carrier
  · rw [orbitSpreadVal_eq_actVal w _ hv (orbitWitness w v hv) (orbitWitness_spec w v hv),
      coindUnit_orbitCoindMapU]
    rw [Idele.smul_apply, inv_inv]
    rw [actVal, Units_map_localRingEquiv_symm]
    exact units_transport (orbitWitness_spec w v hv) (orbitUnitsVal w x)
  · rw [orbitSpreadVal_of_notMem w _ hv, orbitUnitsOf_nonmem w x hv]

theorem orbitSpread_orbitCoindMapU (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) :
    orbitSpread w ((orbitCoindMapU K L w).hom x) = orbitUnitsVal w x := by
  apply Idele.ext
  intro v
  rw [orbitSpread_apply, orbitSpreadVal_orbitCoindMapU]

/-! ## The left inverse of `orbitCoindMapU` -/

/-- The spreading map `Coind_{Γ_w}^{Γ} 𝒪_wˣ ⟶ ∏_{v ∈ O} 𝒪_vˣ`, as a linear map. -/
noncomputable def orbitSpreadLin (w : Place L) :
    (coindRep K L w).V →ₗ[
      CoeffInt.{0}] (orbitUnitsRep K L (orbitStable K L w)).V :=
  { toFun := fun f => Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier))
      ⟨orbitSpread w f, orbitSpread_mem w f⟩
    map_add' := fun f g => by
      show Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) (⟨orbitSpread w (f + g), orbitSpread_mem w (f + g)⟩ :
          ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier))
        = Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) (⟨orbitSpread w f, orbitSpread_mem w f⟩ : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier))
          + Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) (⟨orbitSpread w g, orbitSpread_mem w g⟩ : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier))
      rw [← ofMul_mul]
      congr 1
      exact Subtype.ext (orbitSpread_add w f g)
    map_smul' := fun c f => by
      obtain ⟨z⟩ := c
      show Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) (⟨orbitSpread w (z • f), orbitSpread_mem w (z • f)⟩ :
          ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier))
        = z • Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) (⟨orbitSpread w f, orbitSpread_mem w f⟩ : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier))
      rw [← ofMul_zpow]
      congr 1
      exact Subtype.ext (orbitSpread_zsmul w f z) }

theorem orbitSpreadLin_apply (w : Place L)
    (f : (coindRep K L w).V) :
    orbitSpreadLin w f = Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier))
      ⟨orbitSpread w f, orbitSpread_mem w f⟩ := rfl

/-- **The spreading map is a left inverse of `orbitCoindMapU`.** -/
theorem orbitSpreadLin_orbitCoindMapU (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V) :
    orbitSpreadLin w ((orbitCoindMapU K L w).hom x) = x := by
  rw [orbitSpreadLin_apply]
  rw [show x = Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) (Additive.toMul x : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) from rfl]
  congr 1
  apply Subtype.ext
  show orbitSpread w ((orbitCoindMapU K L w).hom x) = orbitUnitsVal w x
  rw [orbitSpread_orbitCoindMapU]

/-- **`orbitCoindMapU` is injective.** -/
theorem orbitCoindMapU_eq_zero (w : Place L)
    (x : (orbitUnitsRep K L (orbitStable K L w)).V)
    (hx : (orbitCoindMapU K L w).hom x = 0) : x = 0 := by
  have hfun : ∀ γ : L ≃ₐ[K] L, coindUnit w ((orbitCoindMapU K L w).hom x) γ = 1 := by
    intro γ
    rw [hx]
    exact coindUnit_zero w γ
  have hval : orbitUnitsVal w x = 1 := by
    apply Idele.ext
    intro v
    rw [Idele.one_apply]
    by_cases hv : v ∈ (orbitStable K L w).carrier
    · have hγ := hfun ((orbitWitness w v hv))⁻¹
      rw [coindUnit_orbitCoindMapU] at hγ
      rw [Idele.smul_apply, inv_inv] at hγ
      have h2 : orbitUnitsVal w x ((orbitWitness w v hv) • w) = 1 := by
        have hcongr := congrArg
          (Units.map (Place.localRingEquiv (orbitWitness w v hv) w).toMonoidHom) hγ
        rw [Units_map_localRingEquiv_symm] at hcongr
        simpa using hcongr
      rw [← units_transport (orbitWitness_spec w v hv) (orbitUnitsVal w x), h2, cast_one]
    · rw [orbitUnitsOf_nonmem w x hv]
  have hsub : orbitUnitsOf w x = 1 := by
    apply Subtype.ext
    show ((orbitUnitsOf w x : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) :
        Idele L) = 1
    exact hval
  have hx0 : (Additive.toMul x :
      ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) = 1 := by
    rw [← orbitUnitsOf_eq]
    exact hsub
  calc x = Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) (Additive.toMul x : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) := rfl
    _ = Additive.ofMul (α := ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) (1 : ↥(orbitUnitsSubgroup (K := K) (orbitStable K L w).carrier)) := by rw [hx0]
    _ = 0 := ofMul_one

theorem orbitCoindMapU_injective (w : Place L) :
    Function.Injective (orbitCoindMapU K L w).hom := by
  intro x y hxy
  have h : (orbitCoindMapU K L w).hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h0 := orbitCoindMapU_eq_zero w (x - y) h
  rwa [sub_eq_zero] at h0

/-- **The spreading map inverts `orbitCoindMapU` on the idèle level.** -/
theorem orbitUnitsVal_orbitSpreadLin (w : Place L)
    (f : (coindRep K L w).V) :
    orbitUnitsVal w (orbitSpreadLin w f) = orbitSpread w f := by
  rw [orbitUnitsVal, orbitUnitsOf_eq, orbitSpreadLin_apply, toMul_ofMul]

/-- **`orbitCoindMapU` is a left inverse of the spreading map**, on the `γ`-components. -/
theorem coindUnit_orbitSpreadLin (w : Place L)
    (f : (coindRep K L w).V) (γ : L ≃ₐ[K] L) :
    coindUnit w ((orbitCoindMapU K L w).hom (orbitSpreadLin w f)) γ = coindUnit w f γ := by
  rw [coindUnit_orbitCoindMapU, orbitUnitsVal_orbitSpreadLin, Idele.smul_apply]
  rw [orbitSpread_apply]
  rw [orbitSpreadVal_eq_actVal w f (orbitStable_smul_mem w γ⁻¹) γ⁻¹ rfl]
  rw [inv_inv, actVal, Units_map_localRingEquiv_symm_apply]

/-- **`orbitCoindMapU` is a left inverse of the spreading map.** -/
theorem orbitCoindMapU_orbitSpread (w : Place L)
    (f : (coindRep K L w).V) :
    (orbitCoindMapU K L w).hom (orbitSpreadLin w f) = f := by
  apply Subtype.ext
  funext γ
  exact coindUnit_injective w _ _ γ (coindUnit_orbitSpreadLin w f γ)

/-- **The spreading map is `Gal(L/K)`-equivariant.**  Injectivity of `orbitCoindMapU` reduces
this to the two-variable retraction identities. -/
theorem orbitSpreadLin_action (w : Place L)
    (f : (coindRep K L w).V) (γ : L ≃ₐ[K] L) :
    orbitSpreadLin w ((coindRep K L w).ρ γ f)
      = (orbitUnitsRep K L (orbitStable K L w)).ρ γ (orbitSpreadLin w f) := by
  apply orbitCoindMapU_injective w
  rw [orbitCoindMapU_orbitSpread,
    Rep.hom_comm_apply (orbitCoindMapU K L w) γ (orbitSpreadLin w f),
    orbitCoindMapU_orbitSpread]

/-- **The splitting of Shapiro's map on local units**: the `Γ`-map
`Coind_{Γ_w}^{Γ} 𝒪_wˣ ⟶ ∏_{v ∈ O} 𝒪_vˣ`. -/
noncomputable def orbitSpreadMorphism (w : Place L) :
    coindRep K L w ⟶
      orbitUnitsRep K L (orbitStable K L w) :=
  Rep.ofHom { orbitSpreadLin w with
    isIntertwining' := fun γ => by
      apply LinearMap.ext
      intro f
      exact orbitSpreadLin_action w f γ }

/-- **The orbit component of the idèle localisation (local-unit side): Shapiro's map splits.**

The local-unit analogue of `NK.HassePrinciple.orbitCoindMapA_split`: with `Γ = Gal(L/K)`,
`w : Place L`, `Γ_w = MulAction.stabilizer (L ≃ₐ[K] L) w` and `O = placeOrbit K L w`,
`NK.HassePrinciple.orbitCoindMapU K L w` is the adjunction transpose of "evaluate at `w`",
`U_O ⟶ Coind_{Γ_w}^{Γ} 𝒪_wˣ`, where `U_O = ∏_{v ∈ O} 𝒪_vˣ` is realised as
`NK.HassePrinciple.orbitUnitsRep K L (orbitStable K L w)` (the idèles supported on `O` all of
whose components are local units) and `𝒪_wˣ` as `NK.HassePrinciple.localUnitsSubRep K L w`.

The claim below says that this Shapiro map is a split monomorphism.  The construction of the left
inverse is the same as in `orbitCoindMapA_split`, with `L_vˣ` replaced by `𝒪_vˣ`; the values
`actVal γ⁻¹ w (f γ)` of a local unit are local units
(`NK.GlobalCFT.Place.localRingEquiv_mem_localUnits`), so the idèle produced lies in
`∏_{v ∈ O} 𝒪_vˣ` (`NK.HassePrinciple.orbitUnitsSubgroup`). -/
theorem orbitCoindMapU_split {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : NK.GlobalCFT.Place L) :
    ∃ s : Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
            (NK.HassePrinciple.localUnitsSubRep K L w) ⟶
          NK.HassePrinciple.orbitUnitsRep K L (NK.HassePrinciple.orbitStable K L w),
      CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.orbitCoindMapU K L w) s =
        CategoryTheory.CategoryStruct.id
          (NK.HassePrinciple.orbitUnitsRep K L (NK.HassePrinciple.orbitStable K L w)) := by
  refine ⟨orbitSpreadMorphism w, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show orbitSpreadLin w ((orbitCoindMapU K L w).hom x) = x
  exact orbitSpreadLin_orbitCoindMapU w x

end

end NK.HassePrinciple
