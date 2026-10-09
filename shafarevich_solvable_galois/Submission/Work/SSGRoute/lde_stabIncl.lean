import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E8Helpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Base-change (`stabIncl`) identifications at the fixed field

For a subgroup `P ≤ D_w = decompK (k := k) w` of the decomposition group of a place `w` of a number
field `K/k`, and `k' = K^P` its fixed field, the aim of this file is to identify the data of the
`k'`-world at a level `w' ∣ w` of an extension `L ⊇ K` with the data of the `k`-world at the
subgroup `P`:

* `place_smul_rst`: the action on places only sees the underlying function;
* `map_rst_decompK_fixedField`: the image of the `k'`-decomposition group in `Gal(K/k)` is `P`;
* `range_stabIncl`, `range_stabIncl_fixedField`, `range_stabIncl_fixedFieldL`: the range of the
  stabiliser inclusion `Work.SSGRoute.stabIncl` is, at the level `K`, the subgroup
  `P.comap (decompK (k := k) w).subtype` and, at the level `L`, the comap of that subgroup along the
  restriction map `f : D_{w'} → D_w`;
* `stabInclEquivK`, `stabInclEquivL`: the resulting group isomorphisms
  `D_w(K/k') ≃* P.comap …` and `D_{w'}(L/k') ≃* (P.comap …).comap f`, together with the key property
  `stabIncl (ψ.symm x) = x` (`stabIncl_stabInclInvK`, `stabIncl_stabInclInvL`,
  `stabInclEquivK_symm_apply`, `stabInclEquivL_symm_apply`).

Together with `Work.SSGRoute.res_stabIncl_localUnitsRep_eq` (the local units representation at the
lower level is the restriction of scalars of the local units representation at the upper level),
these are the ingredients of the base-change comparison of the two level pairings.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute

theorem place_smul_rst (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k k'] [Algebra k' K] [Algebra k K]
    [IsScalarTower k k' K] (σ : K ≃ₐ[k'] K) (w : NK.GlobalCFT.Place K) :
    (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K) σ) • w = σ • w := by
  cases w <;> rfl

section Generic
variable {k M E : Type} [Field k] [NumberField k] [Field M] [NumberField M]
  [Field E] [NumberField E] [Algebra k M] [Algebra k E] [Algebra M E] [IsScalarTower k M E]

theorem stabIncl_injective' (ŵ : NK.GlobalCFT.Place E) :
    Function.Injective (stabIncl (k := k) (M := M) ŵ) := by
  intro σ τ h
  refine Subtype.ext (AlgEquiv.ext fun x => ?_)
  have := congrArg (fun (f : MulAction.stabilizer (E ≃ₐ[k] E) ŵ) => (f : E ≃ₐ[k] E) x) h
  simpa [stabIncl] using this

theorem range_stabIncl' (ŵ : NK.GlobalCFT.Place E) :
    (stabIncl (k := k) (M := M) ŵ).range =
      ((MulAction.stabilizer (E ≃ₐ[M] E) ŵ).map
          (AlgEquiv.restrictScalarsHom (R := k) (S := M) (A := E))).comap
        (MulAction.stabilizer (E ≃ₐ[k] E) ŵ).subtype := by
  ext x
  rw [MonoidHom.mem_range, Subgroup.mem_comap, Subgroup.mem_map]
  exact ⟨fun ⟨σ, hσ⟩ => ⟨σ.1, σ.2, congrArg Subtype.val hσ⟩,
    fun ⟨τ, hτ, hτx⟩ => ⟨⟨τ, hτ⟩, Subtype.ext hτx⟩⟩

end Generic

section KLevel
variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

theorem map_rst_decompK_fixedField (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K))
    (hPD : P ≤ decompK (k := k) w) :
    (decompK (k := ↥(IntermediateField.fixedField P)) w).map
      (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P)) (A := K)) = P := by
  classical
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, -, rfl⟩
    have hmem : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
        (A := K) σ) ∈ (IntermediateField.fixedField P).fixingSubgroup :=
      ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)).symm σ).2
    rwa [IntermediateField.fixingSubgroup_fixedField P] at hmem
  · intro hx
    have hx' : x ∈ (IntermediateField.fixedField P).fixingSubgroup := by
      rwa [IntermediateField.fixingSubgroup_fixedField P]
    refine ⟨(IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)) ⟨x, hx'⟩, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      rw [← place_smul_rst k ↥(IntermediateField.fixedField P) K _ w]
      have hrst : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
          (A := K) ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P))
            ⟨x, hx'⟩)) = x :=
        AlgEquiv.ext fun y => rfl
      rw [hrst]
      exact MulAction.mem_stabilizer_iff.mp (hPD hx)
    · exact AlgEquiv.ext fun y => rfl

theorem range_stabIncl_fixedField (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K))
    (hPD : P ≤ decompK (k := k) w) :
    (stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w).range =
      P.comap (decompK (k := k) w).subtype := by
  rw [range_stabIncl', map_rst_decompK_fixedField k K w P hPD]

/-- The chosen preimage of `x` under `stabIncl`. -/
noncomputable def stabInclInvK (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K))
    (hPD : P ≤ decompK (k := k) w) (x : P.comap (decompK (k := k) w).subtype) :
    decompK (k := ↥(IntermediateField.fixedField P)) w :=
  (MonoidHom.mem_range.mp (show x.1 ∈ (stabIncl (k := k)
      (M := ↥(IntermediateField.fixedField P)) w).range from by
    rw [range_stabIncl_fixedField k K w P hPD]; exact x.2)).choose

theorem stabIncl_stabInclInvK (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K))
    (hPD : P ≤ decompK (k := k) w) (x : P.comap (decompK (k := k) w).subtype) :
    stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w
      (stabInclInvK k K w P hPD x) = ↑x :=
  (MonoidHom.mem_range.mp (show x.1 ∈ (stabIncl (k := k)
      (M := ↥(IntermediateField.fixedField P)) w).range from by
    rw [range_stabIncl_fixedField k K w P hPD]; exact x.2)).choose_spec

/-- **The `k'`-world group at `w`, as a group isomorphic to `P`.** -/
noncomputable def stabInclEquivK (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K))
    (hPD : P ≤ decompK (k := k) w) :
    decompK (k := ↥(IntermediateField.fixedField P)) w ≃* P.comap (decompK (k := k) w).subtype where
  toFun σ := ⟨stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w σ,
    by rw [← range_stabIncl_fixedField k K w P hPD]; exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩⟩
  invFun x := stabInclInvK k K w P hPD x
  left_inv σ := stabIncl_injective' w (by rw [stabIncl_stabInclInvK])
  right_inv x := Subtype.ext (stabIncl_stabInclInvK k K w P hPD x)
  map_mul' a b := Subtype.ext (map_mul _ a b)

@[simp] theorem stabInclEquivK_apply (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K))
    (hPD : P ≤ decompK (k := k) w)
    (σ : decompK (k := ↥(IntermediateField.fixedField P)) w) :
    ((stabInclEquivK k K w P hPD σ : P.comap (decompK (k := k) w).subtype) : decompK (k := k) w)
      = stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w σ := rfl

theorem stabInclEquivK_symm_apply (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K))
    (hPD : P ≤ decompK (k := k) w) (x : P.comap (decompK (k := k) w).subtype) :
    stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w
        ((stabInclEquivK k K w P hPD).symm x) = ↑x := by
  have h := MulEquiv.apply_symm_apply (stabInclEquivK k K w P hPD) x
  exact congrArg (fun y : P.comap (decompK (k := k) w).subtype => (y : decompK (k := k) w)) h

end KLevel

section LLevel
variable (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]

/-- **The `k'`-world level group at `w'` is the comap of `P` along `f`.** -/
theorem range_stabIncl_fixedFieldL (P : Subgroup (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K)
    (hPD : P ≤ decompK (k := k) w) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L)) :
    (stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w').range =
      (P.comap (decompK (k := k) w).subtype).comap f := by
  classical
  rw [range_stabIncl']
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτx⟩
    rw [Subgroup.mem_comap, Subgroup.subtype_apply]
    have hnat : galRes k K L (AlgEquiv.restrictScalarsHom (R := k)
        (S := ↥(IntermediateField.fixedField P)) (A := L) τ) =
        (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P)) (A := K))
          (galRes ↥(IntermediateField.fixedField P) K L τ) := by
      ext y
      rfl
    rw [hf x]
    rw [show (x : L ≃ₐ[k] L) = (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype x from rfl,
      ← hτx, hnat]
    have hmem : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
        (A := K)) (galRes ↥(IntermediateField.fixedField P) K L τ) ∈
        (IntermediateField.fixedField P).fixingSubgroup :=
      ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)).symm
        (galRes ↥(IntermediateField.fixedField P) K L τ)).2
    rwa [IntermediateField.fixingSubgroup_fixedField P] at hmem
  · intro hx
    rw [Subgroup.mem_comap] at hx
    have hfixmem : ((f x : decompK (k := k) w) : K ≃ₐ[k] K) ∈
        (IntermediateField.fixedField P).fixingSubgroup := by
      rwa [IntermediateField.fixingSubgroup_fixedField P]
    have hfix : ∀ e : ↥(IntermediateField.fixedField P),
        (x : L ≃ₐ[k] L) (algebraMap ↥(IntermediateField.fixedField P) L e)
          = algebraMap ↥(IntermediateField.fixedField P) L e := by
      intro e
      have h1 : ((f x : decompK (k := k) w) : K ≃ₐ[k] K)
          (algebraMap ↥(IntermediateField.fixedField P) K e)
            = algebraMap ↥(IntermediateField.fixedField P) K e :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfixmem _ e.2
      rw [show algebraMap ↥(IntermediateField.fixedField P) L e =
          algebraMap K L (algebraMap ↥(IntermediateField.fixedField P) K e) from rfl]
      rw [← AlgEquiv.restrictNormal_commutes (x : L ≃ₐ[k] L) K
        (algebraMap ↥(IntermediateField.fixedField P) K e)]
      rw [show (x : L ≃ₐ[k] L).restrictNormal K =
          ((f x : decompK (k := k) w) : K ≃ₐ[k] K) from (hf x).symm]
      rw [h1]
    let τx : L ≃ₐ[↥(IntermediateField.fixedField P)] L :=
      { (x : L ≃ₐ[k] L).toRingEquiv with commutes' := hfix }
    have hmem : τx ∈ decompK (k := ↥(IntermediateField.fixedField P)) w' := by
      rw [MulAction.mem_stabilizer_iff]
      rw [← place_smul_rst k ↥(IntermediateField.fixedField P) L _ w']
      have hrst : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
          (A := L) τx) = (x : L ≃ₐ[k] L) := AlgEquiv.ext fun y => rfl
      rw [hrst]
      exact MulAction.mem_stabilizer_iff.mp x.2
    exact ⟨τx, hmem, AlgEquiv.ext fun y => rfl⟩

noncomputable def stabInclInvL (P : Subgroup (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K)
    (hPD : P ≤ decompK (k := k) w) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (x : (P.comap (decompK (k := k) w).subtype).comap f) :
    decompK (k := ↥(IntermediateField.fixedField P)) w' :=
  (MonoidHom.mem_range.mp (show x.1 ∈ (stabIncl (k := k)
      (M := ↥(IntermediateField.fixedField P)) w').range from by
    rw [range_stabIncl_fixedFieldL k K L P w hPD w' hw' f hf]; exact x.2)).choose

theorem stabIncl_stabInclInvL (P : Subgroup (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K)
    (hPD : P ≤ decompK (k := k) w) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (x : (P.comap (decompK (k := k) w).subtype).comap f) :
    stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w'
      (stabInclInvL k K L P w hPD w' hw' f hf x) = ↑x :=
  (MonoidHom.mem_range.mp (show x.1 ∈ (stabIncl (k := k)
      (M := ↥(IntermediateField.fixedField P)) w').range from by
    rw [range_stabIncl_fixedFieldL k K L P w hPD w' hw' f hf]; exact x.2)).choose_spec

noncomputable def stabInclEquivL (P : Subgroup (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K)
    (hPD : P ≤ decompK (k := k) w) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L)) :
    decompK (k := ↥(IntermediateField.fixedField P)) w' ≃*
      (P.comap (decompK (k := k) w).subtype).comap f where
  toFun σ := ⟨stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w' σ,
    by rw [← range_stabIncl_fixedFieldL k K L P w hPD w' hw' f hf]
       exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩⟩
  invFun x := stabInclInvL k K L P w hPD w' hw' f hf x
  left_inv σ := stabIncl_injective' w' (by rw [stabIncl_stabInclInvL])
  right_inv x := Subtype.ext (stabIncl_stabInclInvL k K L P w hPD w' hw' f hf x)
  map_mul' a b := Subtype.ext (map_mul _ a b)

@[simp] theorem stabInclEquivL_apply (P : Subgroup (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K)
    (hPD : P ≤ decompK (k := k) w) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (σ : decompK (k := ↥(IntermediateField.fixedField P)) w') :
    (((stabInclEquivL k K L P w hPD w' hw' f hf) σ :
        (P.comap (decompK (k := k) w).subtype).comap f) : MulAction.stabilizer (L ≃ₐ[k] L) w')
      = stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w' σ := rfl

theorem stabInclEquivL_symm_apply (P : Subgroup (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K)
    (hPD : P ≤ decompK (k := k) w) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (x : (P.comap (decompK (k := k) w).subtype).comap f) :
    stabIncl (k := k) (M := ↥(IntermediateField.fixedField P)) w'
        ((stabInclEquivL k K L P w hPD w' hw' f hf).symm x) = ↑x := by
  have h := MulEquiv.apply_symm_apply (stabInclEquivL k K L P w hPD w' hw' f hf) x
  exact congrArg (fun y : (P.comap (decompK (k := k) w).subtype).comap f =>
    (y : MulAction.stabilizer (L ≃ₐ[k] L) w')) h

end LLevel
end Work.SSGRoute

