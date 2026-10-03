import Mathlib
import Submission.Work.OROneRel.weinbaumDefs

/-!
# The Magnus map: injectivity and its range

For a fixed generator `a : α` the *Magnus map*

`magnusMap a : F({x : α // x ≠ a} × ℤ) →* F(α)`,  `(x, i) ↦ a ^ i * of x * a ^ (-i)`

is injective and its range is exactly the kernel of the exponent sum in `a`
(`Work.OROneRel.expSum a : F(α) →* Multiplicative ℤ`).

* *Injectivity* is the classical Magnus embedding argument: the index shift
  `(x, i) ↦ (x, i + 1)` is an automorphism `σ` of `F({x // x ≠ a} × ℤ)`, and the
  semidirect product `F(Σ) ⋊[σ] ℤ` receives a homomorphism `magTheta` from `F(α)`
  sending `a` to the generator of the `ℤ`-factor and `x ≠ a` to `x`; then
  `magTheta (magnusMap a u) = inl u` for all `u`, and `inl` is injective.

* The *range* is the kernel: the inclusion `range ≤ ker` is the computation
  `expSum a (a ^ i * x * a ^ (-i)) = 1`, and the converse writes an arbitrary
  element of `F(α)` as `a ^ k * m` with `m` in the range (the range is invariant
  under conjugation by `a`, by the shift), whereupon membership in the kernel
  forces `k = 0`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### The index shift on the decoration -/

/-- Shifting the decoration index by `j`. -/
def magShiftBy (a : α) (j : ℤ) : ({x : α // x ≠ a} × ℤ) → ({x : α // x ≠ a} × ℤ) :=
  fun s => (s.1, s.2 + j)

/-- The homomorphism of free groups induced by the index shift. -/
noncomputable def magShiftHom (a : α) (j : ℤ) :
    FreeGroup ({x : α // x ≠ a} × ℤ) →* FreeGroup ({x : α // x ≠ a} × ℤ) :=
  FreeGroup.map (magShiftBy a j)

theorem magShiftHom_apply_of (a : α) (j : ℤ) (s : {x : α // x ≠ a} × ℤ) :
    magShiftHom a j (FreeGroup.of s) = FreeGroup.of (magShiftBy a j s) :=
  FreeGroup.map.of

theorem magShiftHom_zero (a : α) : magShiftHom a 0 = MonoidHom.id _ := by
  refine FreeGroup.ext_hom _ _ (fun s => ?_)
  simp [magShiftHom, magShiftBy]

theorem magShiftHom_comp (a : α) (j₁ j₂ : ℤ) :
    (magShiftHom a j₁).comp (magShiftHom a j₂) = magShiftHom a (j₁ + j₂) := by
  refine FreeGroup.ext_hom _ _ (fun s => ?_)
  simp only [MonoidHom.comp_apply, magShiftHom_apply_of, magShiftBy]
  abel

/-- The index shift as an automorphism of the free group. -/
noncomputable def magShiftAut (a : α) (j : ℤ) : MulAut (FreeGroup ({x : α // x ≠ a} × ℤ)) :=
  MonoidHom.toMulEquiv (magShiftHom a j) (magShiftHom a (-j))
    (by rw [magShiftHom_comp, neg_add_cancel, magShiftHom_zero])
    (by rw [magShiftHom_comp, add_neg_cancel, magShiftHom_zero])

theorem magShiftAut_apply_of (a : α) (j : ℤ) (s : {x : α // x ≠ a} × ℤ) :
    magShiftAut a j (FreeGroup.of s) = FreeGroup.of (magShiftBy a j s) :=
  magShiftHom_apply_of a j s

theorem magShiftAut_add (a : α) (j₁ j₂ : ℤ) :
    magShiftAut a (j₁ + j₂) = magShiftAut a j₁ * magShiftAut a j₂ := by
  refine MulEquiv.ext (fun x => ?_)
  show magShiftHom a (j₁ + j₂) x = magShiftHom a j₁ (magShiftHom a j₂ x)
  rw [← magShiftHom_comp, MonoidHom.comp_apply]

/-! ### The Magnus embedding -/

/-- The shift, packaged as a monoid homomorphism from the additive group `ℤ`. -/
noncomputable def magShiftPhi (a : α) :
    Multiplicative ℤ →* MulAut (FreeGroup ({x : α // x ≠ a} × ℤ)) :=
  MonoidHom.mk' (fun z => magShiftAut a (Multiplicative.toAdd z)) (by
    intro x y
    show magShiftAut a (Multiplicative.toAdd (x * y)) =
      magShiftAut a (Multiplicative.toAdd x) * magShiftAut a (Multiplicative.toAdd y)
    rw [toAdd_mul, magShiftAut_add])

theorem magShiftPhi_ofAdd (a : α) (j : ℤ) :
    magShiftPhi a (Multiplicative.ofAdd j) = magShiftAut a j := by
  simp [magShiftPhi]

/-- The semidirect product `F(Σ) ⋊ ℤ` in which the Magnus map is realised. -/
abbrev magSD (a : α) :=
  SemidirectProduct (FreeGroup ({x : α // x ≠ a} × ℤ)) (Multiplicative ℤ) (magShiftPhi a)

/-- The Magnus embedding: `a` maps to the generator of the `ℤ`-factor, `x ≠ a` to `x`
(the decoration `0`). -/
noncomputable def magTheta (a : α) : FreeGroup α →* magSD a := by
  classical
  exact FreeGroup.lift fun x =>
    if h : x = a then SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))
    else SemidirectProduct.inl (FreeGroup.of (⟨x, h⟩, (0 : ℤ)))

theorem magTheta_of_a (a : α) :
    magTheta a (FreeGroup.of a) = SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) := by
  classical
  rw [magTheta, FreeGroup.lift_apply_of, dif_pos rfl]

theorem magTheta_of_ne (a : α) (y : {x : α // x ≠ a}) :
    magTheta a (FreeGroup.of (y : α)) = SemidirectProduct.inl (FreeGroup.of (y, (0 : ℤ))) := by
  classical
  rw [magTheta, FreeGroup.lift_apply_of, dif_neg y.2]

theorem magTheta_magnusMap_of (a : α) (s : {x : α // x ≠ a} × ℤ) :
    magTheta a (magnusMap a (FreeGroup.of s)) = SemidirectProduct.inl (FreeGroup.of s) := by
  classical
  obtain ⟨y, i⟩ := s
  rw [magnusMap_apply, map_mul, map_mul, map_zpow, map_zpow, magTheta_of_a, magTheta_of_ne]
  rw [← MonoidHom.map_zpow, ← MonoidHom.map_zpow]
  rw [show (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ i = Multiplicative.ofAdd i from by
        rw [← Int.ofAdd_mul, one_mul],
      show (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ (-i) =
          (Multiplicative.ofAdd i)⁻¹ from by
        rw [← Int.ofAdd_mul, one_mul, ofAdd_neg]]
  rw [← SemidirectProduct.inl_aut, SemidirectProduct.inl_inj, magShiftPhi_ofAdd,
    magShiftAut_apply_of]
  simp [magShiftBy]

theorem magTheta_comp_magnusMap (a : α) :
    (magTheta a).comp (magnusMap a) = SemidirectProduct.inl := by
  refine FreeGroup.ext_hom _ _ (fun s => ?_)
  exact magTheta_magnusMap_of a s

/-- The Magnus map is injective. -/
theorem magMagnusMap_injective (a : α) : Function.Injective (magnusMap a) := by
  intro u v huv
  have h : (SemidirectProduct.inl u : magSD a) = SemidirectProduct.inl v := by
    rw [← magTheta_comp_magnusMap a]
    exact congrArg (magTheta a) huv
  exact SemidirectProduct.inl_injective h

/-! ### The range is the kernel of the exponent sum -/

theorem magExpSum_of_a (a : α) : expSum a (FreeGroup.of a) = Multiplicative.ofAdd (1 : ℤ) := by
  rw [expSum, FreeGroup.lift_apply_of, if_pos rfl]

theorem magExpSum_of_ne (a : α) (y : {x : α // x ≠ a}) :
    expSum a (FreeGroup.of (y : α)) = 1 := by
  rw [expSum, FreeGroup.lift_apply_of]
  exact if_neg y.2

theorem magExpSum_comp_magnusMap (a : α) : (expSum a).comp (magnusMap a) = 1 := by
  refine FreeGroup.ext_hom _ _ (fun s => ?_)
  obtain ⟨y, i⟩ := s
  show expSum a (magnusMap a (FreeGroup.of (y, i))) = 1
  rw [magnusMap_apply, map_mul, map_mul, map_zpow, map_zpow, magExpSum_of_a, magExpSum_of_ne]
  group

theorem magRange_le_ker (a : α) : (magnusMap a).range ≤ (expSum a).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  obtain ⟨u, rfl⟩ := hx
  simpa using DFunLike.congr_fun (magExpSum_comp_magnusMap a) u

theorem magExpSum_of_a_zpow (a : α) (k : ℤ) :
    expSum a (FreeGroup.of a ^ k) = Multiplicative.ofAdd k := by
  rw [map_zpow, magExpSum_of_a, ← Int.ofAdd_mul, one_mul]

theorem magOf_a_zpow_mem_ker_iff (a : α) (k : ℤ) :
    FreeGroup.of a ^ k ∈ (expSum a).ker ↔ k = 0 := by
  rw [MonoidHom.mem_ker, magExpSum_of_a_zpow, ofAdd_eq_one]

/-- Conjugation by a power of `a`, as a monoid homomorphism. -/
noncomputable def magConjHom (a : α) (k : ℤ) : FreeGroup α →* FreeGroup α where
  toFun m := FreeGroup.of a ^ k * m * (FreeGroup.of a ^ k)⁻¹
  map_one' := by simp
  map_mul' x y := by group

theorem magConj_magnusMap (a : α) (k : ℤ) :
    (magConjHom a k).comp (magnusMap a) = (magnusMap a).comp (magShiftHom a k) := by
  refine FreeGroup.ext_hom _ _ (fun s => ?_)
  obtain ⟨y, i⟩ := s
  show FreeGroup.of a ^ k * magnusMap a (FreeGroup.of (y, i)) * (FreeGroup.of a ^ k)⁻¹ =
    magnusMap a (magShiftHom a k (FreeGroup.of (y, i)))
  rw [magShiftHom_apply_of, magnusMap_apply, magnusMap_apply]
  show FreeGroup.of a ^ k * (FreeGroup.of a ^ i * FreeGroup.of (y : α) *
      FreeGroup.of a ^ (-i)) * (FreeGroup.of a ^ k)⁻¹ =
    FreeGroup.of a ^ (i + k) * FreeGroup.of (y : α) * FreeGroup.of a ^ (-(i + k))
  group

theorem magZpow_conj_mem_range (a : α) (k : ℤ) {m : FreeGroup α}
    (hm : m ∈ (magnusMap a).range) :
    FreeGroup.of a ^ k * m * (FreeGroup.of a ^ k)⁻¹ ∈ (magnusMap a).range := by
  obtain ⟨u, rfl⟩ := hm
  refine ⟨magShiftHom a k u, ?_⟩
  exact (DFunLike.congr_fun (magConj_magnusMap a k) u).symm

/-- Every element of `F(α)` is a power of `a` times an element of the range of the Magnus map. -/
theorem magExists_zpow_mul_mem_range (a : α) (w : FreeGroup α) :
    ∃ k : ℤ, ∃ m ∈ (magnusMap a).range, w = FreeGroup.of a ^ k * m := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · exact ⟨0, 1, Subgroup.one_mem _, by simp⟩
  · intro x
    by_cases hx : x = a
    · subst hx
      exact ⟨1, 1, Subgroup.one_mem _, by simp⟩
    · refine ⟨0, FreeGroup.of x, ?_, by simp⟩
      exact ⟨FreeGroup.of (⟨x, hx⟩, 0), by rw [magnusMap_apply]; simp⟩
  · intro x ih
    obtain ⟨k, m, hm, hw⟩ := ih
    refine ⟨-k, FreeGroup.of a ^ k * m⁻¹ * (FreeGroup.of a ^ k)⁻¹, ?_, ?_⟩
    · exact magZpow_conj_mem_range a k (Subgroup.inv_mem _ hm)
    · rw [hw]
      group
  · intro x y ihx ihy
    obtain ⟨k₁, m₁, hm₁, hw₁⟩ := ihx
    obtain ⟨k₂, m₂, hm₂, hw₂⟩ := ihy
    refine ⟨k₁ + k₂, FreeGroup.of a ^ (-k₂) * m₁ * (FreeGroup.of a ^ (-k₂))⁻¹ * m₂, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (magZpow_conj_mem_range a (-k₂) hm₁) hm₂
    · rw [hw₁, hw₂]
      group

theorem magKer_le_range (a : α) : (expSum a).ker ≤ (magnusMap a).range := by
  intro w hw
  obtain ⟨k, m, hm, hw'⟩ := magExists_zpow_mul_mem_range a w
  have hmK : m ∈ (expSum a).ker := magRange_le_ker a hm
  have hk : FreeGroup.of a ^ k ∈ (expSum a).ker := by
    have h : FreeGroup.of a ^ k = w * m⁻¹ := by
      rw [hw']
      group
    rw [h]
    exact Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hmK)
  have hk0 : k = 0 := (magOf_a_zpow_mem_ker_iff a k).mp hk
  rw [hw', hk0, zpow_zero, one_mul]
  exact hm

theorem magRange_eq_ker (a : α) : (magnusMap a).range = (expSum a).ker :=
  le_antisymm (magRange_le_ker a) (magKer_le_range a)

/-! ### The statement -/

theorem magnusMap_injective_range {α : Type u} (a : α) :
    Function.Injective (Work.OROneRel.magnusMap a) ∧
      (Work.OROneRel.magnusMap a).range = (Work.OROneRel.expSum a).ker :=
  ⟨magMagnusMap_injective a, magRange_eq_ker a⟩

end Work.OROneRel
