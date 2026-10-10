import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.PT.localDictionary_fin_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open Work.GroupCohomology

/-!
# `H¹` is an invariant of the pair (group, module) up to isomorphism

Let `Φ : G' ≃* G` be an isomorphism of groups and `Ψ : M' ≃+ M` an additive equivalence of
coefficient groups that is compatible with the actions in the sense
`Ψ (g' • m') = Φ g' • Ψ m'` (i.e. `M'` is, via `Ψ`, the `G'`-module obtained from `M` by
transporting the `G`-action along `Φ`).  Then `H¹(G', M') ≃+ H¹(G, M)`.

The isomorphism is induced at the level of inhomogeneous `1`-cochains by "push forward"
`f ↦ (g ↦ Ψ (f (Φ.symm g)))`, whose inverse is the pullback
`f ↦ (g' ↦ Ψ.symm (f (Φ g')))`.  Both directions carry crossed homomorphisms to crossed
homomorphisms and coboundaries to coboundaries, hence descend to `H¹`.
-/

section Transfer

variable {G' G : Type*} [Group G'] [Group G]
variable {M' M : Type*} [AddCommGroup M'] [AddCommGroup M]
variable [DistribMulAction G' M'] [DistribMulAction G M]

/-- Compatibility of the coefficient equivalence with the group isomorphism:
`Ψ (g' • m') = Φ g' • Ψ m'`. -/
def IsCompat (Φ : G' ≃* G) (Ψ : M' ≃+ M) : Prop :=
  ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m'

/-! ## Maps on cochains -/

/-- Push `1`-cochains forward along `Φ`, `Ψ`: `f ↦ (g ↦ Ψ (f (Φ.symm g)))`. -/
def pushCoeff (Φ : G' ≃* G) (Ψ : M' ≃+ M) : (G' → M') →+ (G → M) where
  toFun f := fun g => Ψ (f (Φ.symm g))
  map_zero' := by funext g; simp
  map_add' f f' := by funext g; simp

@[simp] theorem pushCoeff_apply (Φ : G' ≃* G) (Ψ : M' ≃+ M) (f : G' → M') (g : G) :
    pushCoeff Φ Ψ f g = Ψ (f (Φ.symm g)) := rfl

/-- Pull `1`-cochains back along `Φ`, `Ψ`: `f ↦ (g' ↦ Ψ.symm (f (Φ g')))`. -/
def pullCoeff (Φ : G' ≃* G) (Ψ : M' ≃+ M) : (G → M) →+ (G' → M') where
  toFun f := fun g' => Ψ.symm (f (Φ g'))
  map_zero' := by funext g'; simp
  map_add' f f' := by funext g'; simp

@[simp] theorem pullCoeff_apply (Φ : G' ≃* G) (Ψ : M' ≃+ M) (f : G → M) (g' : G') :
    pullCoeff Φ Ψ f g' = Ψ.symm (f (Φ g')) := rfl

/-- `Ψ.symm` transports the `G`-action on `M` (pulled back through `Φ`) to the `G'`-action on
`M'`. -/
theorem symm_smul (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (g' : G') (y : M) :
    Ψ.symm (Φ g' • y) = g' • Ψ.symm y := by
  have h : Ψ (g' • Ψ.symm y) = Φ g' • y := by
    rw [hΨ g' (Ψ.symm y), AddEquiv.apply_symm_apply]
  rw [← h, AddEquiv.symm_apply_apply]

/-! ## The maps preserve cocycles and coboundaries -/

theorem pushCoeff_mem_Z1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) {f : G' → M'}
    (hf : f ∈ Z1 G' M') : pushCoeff Φ Ψ f ∈ Z1 G M := by
  rw [mem_Z1_iff] at hf ⊢
  intro g h
  simp only [pushCoeff_apply]
  rw [map_mul Φ.symm g h, hf (Φ.symm g) (Φ.symm h), map_add, hΨ (Φ.symm g) (f (Φ.symm h)),
    Φ.apply_symm_apply]

theorem pushCoeff_mem_B1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) {f : G' → M'}
    (hf : f ∈ B1 G' M') : pushCoeff Φ Ψ f ∈ B1 G M := by
  rw [mem_B1_iff] at hf ⊢
  obtain ⟨a, rfl⟩ := hf
  refine ⟨Ψ a, ?_⟩
  funext g
  simp only [pushCoeff_apply, d0_apply, map_sub, hΨ (Φ.symm g) a, Φ.apply_symm_apply]

theorem pullCoeff_mem_Z1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) {f : G → M}
    (hf : f ∈ Z1 G M) : pullCoeff Φ Ψ f ∈ Z1 G' M' := by
  rw [mem_Z1_iff] at hf ⊢
  intro g' h'
  simp only [pullCoeff_apply]
  rw [map_mul Φ g' h', hf (Φ g') (Φ h'), map_add, symm_smul Φ Ψ hΨ g' (f (Φ h'))]

theorem pullCoeff_mem_B1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) {f : G → M}
    (hf : f ∈ B1 G M) : pullCoeff Φ Ψ f ∈ B1 G' M' := by
  rw [mem_B1_iff] at hf ⊢
  obtain ⟨a, rfl⟩ := hf
  refine ⟨Ψ.symm a, ?_⟩
  funext g'
  simp only [pullCoeff_apply, d0_apply, map_sub, symm_smul Φ Ψ hΨ g' a]

/-! ## The two maps are mutually inverse on cochains -/

theorem pushCoeff_pullCoeff (Φ : G' ≃* G) (Ψ : M' ≃+ M) (f : G → M) :
    pushCoeff Φ Ψ (pullCoeff Φ Ψ f) = f := by
  funext g
  simp only [pushCoeff_apply, pullCoeff_apply, Φ.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem pullCoeff_pushCoeff (Φ : G' ≃* G) (Ψ : M' ≃+ M) (f : G' → M') :
    pullCoeff Φ Ψ (pushCoeff Φ Ψ f) = f := by
  funext g'
  simp only [pullCoeff_apply, pushCoeff_apply, Φ.symm_apply_apply, AddEquiv.symm_apply_apply]

/-! ## The induced additive maps on `Z¹` -/

/-- Push `1`-cocycles forward from `(G', M')` to `(G, M)`. -/
def pushZ1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) : Z1 G' M' →+ Z1 G M where
  toFun f := ⟨pushCoeff Φ Ψ (f : G' → M'), pushCoeff_mem_Z1 Φ Ψ hΨ f.2⟩
  map_zero' := Subtype.ext (map_zero (pushCoeff Φ Ψ))
  map_add' f f' := Subtype.ext (map_add (pushCoeff Φ Ψ) (f : G' → M') (f' : G' → M'))

@[simp] theorem pushZ1_coe (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (f : Z1 G' M') :
    ((pushZ1 Φ Ψ hΨ f : Z1 G M) : G → M) = pushCoeff Φ Ψ (f : G' → M') := rfl

/-- Pull `1`-cocycles back from `(G, M)` to `(G', M')`. -/
def pullZ1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) : Z1 G M →+ Z1 G' M' where
  toFun f := ⟨pullCoeff Φ Ψ (f : G → M), pullCoeff_mem_Z1 Φ Ψ hΨ f.2⟩
  map_zero' := Subtype.ext (map_zero (pullCoeff Φ Ψ))
  map_add' f f' := Subtype.ext (map_add (pullCoeff Φ Ψ) (f : G → M) (f' : G → M))

@[simp] theorem pullZ1_coe (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (f : Z1 G M) :
    ((pullZ1 Φ Ψ hΨ f : Z1 G' M') : G' → M') = pullCoeff Φ Ψ (f : G → M) := rfl

theorem pullZ1_pushZ1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (f : Z1 G' M') :
    pullZ1 Φ Ψ hΨ (pushZ1 Φ Ψ hΨ f) = f :=
  Subtype.ext (pullCoeff_pushCoeff Φ Ψ (f : G' → M'))

theorem pushZ1_pullZ1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (f : Z1 G M) :
    pushZ1 Φ Ψ hΨ (pullZ1 Φ Ψ hΨ f) = f :=
  Subtype.ext (pushCoeff_pullCoeff Φ Ψ (f : G → M))

/-! ## The induced additive maps on `H¹` -/

/-- Push `H¹` forward from `(G', M')` to `(G, M)`. -/
noncomputable def pushH1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) :
    H1 G' M' →+ H1 G M :=
  QuotientAddGroup.lift ((B1 G' M').comap (Z1 G' M').subtype)
    ((H1π G M).comp (pushZ1 Φ Ψ hΨ)) (by
      intro x hx
      have hx' : ((x : Z1 G' M') : G' → M') ∈ B1 G' M' := by
        simpa using (AddSubgroup.mem_comap.mp hx)
      have hy : ((pushZ1 Φ Ψ hΨ x : Z1 G M) : G → M) ∈ B1 G M := by
        simpa using pushCoeff_mem_B1 Φ Ψ hΨ hx'
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hy)

theorem pushH1_H1π (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (f : Z1 G' M') :
    pushH1 Φ Ψ hΨ (H1π G' M' f) = H1π G M (pushZ1 Φ Ψ hΨ f) :=
  QuotientAddGroup.lift_mk' _ _ f

/-- Pull `H¹` back from `(G, M)` to `(G', M')`. -/
noncomputable def pullH1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) :
    H1 G M →+ H1 G' M' :=
  QuotientAddGroup.lift ((B1 G M).comap (Z1 G M).subtype)
    ((H1π G' M').comp (pullZ1 Φ Ψ hΨ)) (by
      intro x hx
      have hx' : ((x : Z1 G M) : G → M) ∈ B1 G M := by
        simpa using (AddSubgroup.mem_comap.mp hx)
      have hy : ((pullZ1 Φ Ψ hΨ x : Z1 G' M') : G' → M') ∈ B1 G' M' := by
        simpa using pullCoeff_mem_B1 Φ Ψ hΨ hx'
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hy)

theorem pullH1_H1π (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (f : Z1 G M) :
    pullH1 Φ Ψ hΨ (H1π G M f) = H1π G' M' (pullZ1 Φ Ψ hΨ f) :=
  QuotientAddGroup.lift_mk' _ _ f

theorem pullH1_pushH1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (x : H1 G' M') :
    pullH1 Φ Ψ hΨ (pushH1 Φ Ψ hΨ x) = x := by
  induction x using Work.GroupCohomology.H1_induction_on with
  | h f => rw [pushH1_H1π, pullH1_H1π, pullZ1_pushZ1]

theorem pushH1_pullH1 (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : IsCompat Φ Ψ) (x : H1 G M) :
    pushH1 Φ Ψ hΨ (pullH1 Φ Ψ hΨ x) = x := by
  induction x using Work.GroupCohomology.H1_induction_on with
  | h f => rw [pullH1_H1π, pushH1_H1π, pushZ1_pullZ1]

end Transfer

theorem gcH1Transfer_exists {G G' : Type} [Group G] [Group G'] {M M' : Type} [AddCommGroup M]
    [DistribMulAction G M] [AddCommGroup M'] [DistribMulAction G' M']
    (Φ : G' ≃* G) (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    Nonempty (Work.GroupCohomology.H1 G' M' ≃+ Work.GroupCohomology.H1 G M) :=
  ⟨{ toFun := pushH1 Φ Ψ hΨ
     invFun := pullH1 Φ Ψ hΨ
     left_inv := pullH1_pushH1 Φ Ψ hΨ
     right_inv := pushH1_pullH1 Φ Ψ hΨ
     map_add' := fun a b => (pushH1 Φ Ψ hΨ).map_add a b }⟩

end Work.SSGRoute.PT
