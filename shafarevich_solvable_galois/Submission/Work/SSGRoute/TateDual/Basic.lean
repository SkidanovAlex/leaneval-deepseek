import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.SSGRoute.TateDual

open scoped BigOperators

section LinearStructure

variable (p : ℕ) (G : Type u) [Group G] [Fintype G]
variable (A : Type v) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]

/-- The twisted norm `f ↦ ∑ x, x⁻¹ • f x` is `𝔽_p`-linear when the coefficients form an
`𝔽_p[G]`-module. -/
noncomputable def coindAugLin : (G → A) →ₗ[ZMod p] A where
  toFun := Work.Tate.coindAug G A
  map_add' := map_add (Work.Tate.coindAug G A)
  map_smul' c f := by
    show Work.Tate.coindAug G A (c • f) = c • Work.Tate.coindAug G A f
    rw [Work.Tate.coindAug_apply, Work.Tate.coindAug_apply]
    rw [show (∑ x : G, x⁻¹ • (c • f) x) = ∑ x : G, c • (x⁻¹ • f x) from
      Finset.sum_congr rfl (fun x _ => by rw [Pi.smul_apply, smul_comm])]
    exact (Finset.smul_sum (s := Finset.univ) (f := fun x : G => x⁻¹ • f x) (r := c)).symm

@[simp] theorem coindAugLin_apply (f : G → A) :
    coindAugLin p G A f = Work.Tate.coindAug G A f := rfl

/-- The `I_G`-twist `coindUp G A = ker(coindAug)`, as an `𝔽_p`-subspace of the coinduced
module `G → A`. -/
noncomputable def coindUpSub : Submodule (ZMod p) (G → A) := (coindAugLin p G A).ker

theorem mem_coindUpSub_iff {f : G → A} :
    f ∈ coindUpSub p G A ↔ Work.Tate.coindAug G A f = 0 := Iff.rfl

theorem coe_coindUpSub :
    ((coindUpSub p G A : Submodule (ZMod p) (G → A)) : Set (G → A))
      = (Work.Tate.coindUp G A : Set (G → A)) := by
  ext f
  show f ∈ coindUpSub p G A ↔ f ∈ Work.Tate.coindUp G A
  rw [mem_coindUpSub_iff, Work.Tate.mem_coindUp_iff]
  rfl

end LinearStructure

section ModuleInstances

variable (p : ℕ) (G : Type u) [Group G] [Fintype G]
variable (A : Type v) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]

/-- The `𝔽_p`-action on the `I_G`-twist, induced by the pointwise action on `G → A`. -/
instance instSMulZModCoindUp : SMul (ZMod p) ↥(Work.Tate.coindUp G A) where
  smul c x := ⟨c • (x : G → A), by
    have h : Work.Tate.coindAug G A (c • (x : G → A))
        = c • Work.Tate.coindAug G A (x : G → A) :=
      (coindAugLin p G A).map_smul c (x : G → A)
    have hx : Work.Tate.coindAug G A (x : G → A) = 0 :=
      Work.Tate.mem_coindUp_iff.mp x.2
    rw [Work.Tate.mem_coindUp_iff]
    change Work.Tate.coindAug G A (c • (x : G → A)) = 0
    rw [h, hx, smul_zero]⟩

@[simp] theorem coe_smul_zmod_coindUp (c : ZMod p) (x : ↥(Work.Tate.coindUp G A)) :
    ((c • x : ↥(Work.Tate.coindUp G A)) : G → A) = c • (x : G → A) := rfl

/-- The `I_G`-twist is an `𝔽_p`-module. -/
instance instModuleCoindUp : Module (ZMod p) ↥(Work.Tate.coindUp G A) where
  one_smul x := Subtype.ext (one_smul (ZMod p) (x : G → A))
  mul_smul c d x := Subtype.ext (mul_smul c d (x : G → A))
  smul_zero c := Subtype.ext (smul_zero c)
  smul_add c x y := Subtype.ext (smul_add c (x : G → A) (y : G → A))
  add_smul c d x := Subtype.ext (add_smul c d (x : G → A))
  zero_smul x := Subtype.ext (zero_smul (ZMod p) (x : G → A))

/-- The coinduced `G`-action and the `𝔽_p`-action on the `I_G`-twist commute. -/
instance instSMulCommClassCoindUp : SMulCommClass G (ZMod p) ↥(Work.Tate.coindUp G A) where
  smul_comm γ c x := Subtype.ext (by
    show γ • (c • (x : G → A)) = c • (γ • (x : G → A))
    funext t
    rw [Work.Tate.coind_smul_eq, Pi.smul_apply, Pi.smul_apply, Work.Tate.coind_smul_eq])

end ModuleInstances

section Finite

variable (p : ℕ) (G : Type u) [Group G] [Fintype G]
variable (A : Type v) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A] [Finite A]

/-- The `I_G`-twist of a finite module is a finitely generated `𝔽_p`-module. -/
instance instModuleFiniteCoindUp : Module.Finite (ZMod p) ↥(Work.Tate.coindUp G A) :=
  Module.Finite.of_finite

/-- The `I_G`-twist of a finite module is finite dimensional over `𝔽_p` for `p` prime. -/
instance instFiniteDimensionalCoindUp [Fact p.Prime] :
    FiniteDimensional (ZMod p) ↥(Work.Tate.coindUp G A) :=
  Module.Finite.of_finite

end Finite

section QuotientModule

variable (p : ℕ) (G : Type u) [Group G] [Fintype G]
variable (A : Type v) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A]

/-- The diagonal inclusion `A → Coind(A)`, `a ↦ (x ↦ x • a)`, is `𝔽_p`-linear. -/
noncomputable def coindUnitLin : A →ₗ[ZMod p] (G → A) where
  toFun := Work.Tate.coindUnit G A
  map_add' := map_add (Work.Tate.coindUnit G A)
  map_smul' c a := by
    funext x
    show x • (c • a) = c • (x • a)
    rw [smul_comm]

@[simp] theorem coindUnitLin_apply (a : A) (x : G) :
    coindUnitLin p G A a x = x • a := rfl

/-- The diagonal copy of `A` in `Coind(A)` is the range of the (linear) diagonal inclusion. -/
theorem coe_coindDiag_eq_range :
    ((Work.Tate.coindDiag G A : AddSubgroup (G → A)) : Set (G → A))
      = ((coindUnitLin p G A).range : Set (G → A)) := by
  ext φ
  show φ ∈ Work.Tate.coindDiag G A ↔ φ ∈ (coindUnitLin p G A).range
  rw [Work.Tate.mem_coindDiag_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.symm⟩

theorem smul_mem_coindDiag (c : ZMod p) {φ : G → A}
    (h : φ ∈ Work.Tate.coindDiag G A) : c • φ ∈ Work.Tate.coindDiag G A := by
  rw [Work.Tate.mem_coindDiag_iff] at h ⊢
  obtain ⟨a, rfl⟩ := h
  refine ⟨c • a, ?_⟩
  funext x
  rw [Pi.smul_apply]
  exact (smul_comm x c a).symm

/-- The `𝔽_p`-action on the shift `A^* = Coind(A)/A`, induced by the pointwise action on
`G → A`. -/
noncomputable instance instSMulZModQuotDiag : SMul (ZMod p) (Work.Tate.coindShift G A) where
  smul c := Quotient.map (fun φ : G → A => c • φ) (by
    intro φ ψ h
    have hh : -φ + ψ ∈ Work.Tate.coindDiag G A := (QuotientAddGroup.leftRel_apply).mp h
    refine (QuotientAddGroup.leftRel_apply).mpr ?_
    have hc : -(c • φ) + c • ψ = c • (-φ + ψ) := by
      rw [smul_add, smul_neg]
    rw [hc]
    exact smul_mem_coindDiag p G A c hh)

theorem quot_zmod_smul_mk (c : ZMod p) (φ : G → A) :
    (c • (QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ) : Work.Tate.coindShift G A)
      = QuotientAddGroup.mk' (Work.Tate.coindDiag G A) (c • φ) := rfl

/-- The shift `A^* = Coind(A)/A` is an `𝔽_p`-module. -/
noncomputable instance instModuleQuotDiag : Module (ZMod p) (Work.Tate.coindShift G A) where
  one_smul x := by
    refine QuotientAddGroup.induction_on x fun φ => ?_
    change (1 : ZMod p) • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ
      = QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ
    rw [quot_zmod_smul_mk, one_smul]
  mul_smul c d x := by
    refine QuotientAddGroup.induction_on x fun φ => ?_
    change (c * d) • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ
      = c • (d • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ)
    rw [quot_zmod_smul_mk, quot_zmod_smul_mk, quot_zmod_smul_mk, mul_smul]
  smul_zero c := by
    change c • (0 : Work.Tate.coindShift G A) = 0
    rw [← map_zero (QuotientAddGroup.mk' (Work.Tate.coindDiag G A)), quot_zmod_smul_mk,
      smul_zero]
  smul_add c x y := by
    refine QuotientAddGroup.induction_on x fun φ => ?_
    refine QuotientAddGroup.induction_on y fun ψ => ?_
    change c • (QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ
        + QuotientAddGroup.mk' (Work.Tate.coindDiag G A) ψ)
      = c • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ
        + c • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) ψ
    rw [← map_add, quot_zmod_smul_mk, smul_add, map_add, ← quot_zmod_smul_mk,
      ← quot_zmod_smul_mk]
  add_smul c d x := by
    refine QuotientAddGroup.induction_on x fun φ => ?_
    change (c + d) • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ
      = c • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ
        + d • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ
    rw [quot_zmod_smul_mk, add_smul, map_add, ← quot_zmod_smul_mk, ← quot_zmod_smul_mk]
  zero_smul x := by
    refine QuotientAddGroup.induction_on x fun φ => ?_
    change (0 : ZMod p) • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ = 0
    rw [quot_zmod_smul_mk, zero_smul,
      ← map_zero (QuotientAddGroup.mk' (Work.Tate.coindDiag G A))]

/-- The coinduced `G`-action and the `𝔽_p`-action on the shift `A^* = Coind(A)/A` commute. -/
noncomputable instance instSMulCommClassQuotDiag :
    SMulCommClass G (ZMod p) (Work.Tate.coindShift G A) where
  smul_comm γ c x := by
    refine QuotientAddGroup.induction_on x fun φ => ?_
    change γ • (c • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ)
      = c • (γ • QuotientAddGroup.mk' (Work.Tate.coindDiag G A) φ)
    rw [quot_zmod_smul_mk, Work.Tate.quot_smul_mk, Work.Tate.quot_smul_mk,
      quot_zmod_smul_mk]
    congr 1

end QuotientModule

section QuotientFinite

variable (p : ℕ) (G : Type u) [Group G] [Fintype G]
variable (A : Type v) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
  [SMulCommClass G (ZMod p) A] [Finite A]

/-- The shift of a finite module is a finitely generated `𝔽_p`-module. -/
instance instModuleFiniteQuotDiag : Module.Finite (ZMod p) (Work.Tate.coindShift G A) :=
  Module.Finite.of_finite

/-- The shift of a finite module is finite dimensional over `𝔽_p` for `p` prime. -/
instance instFiniteDimensionalQuotDiag [Fact p.Prime] :
    FiniteDimensional (ZMod p) (Work.Tate.coindShift G A) :=
  Module.Finite.of_finite

end QuotientFinite

section DualFinite

variable (p : ℕ) (A : Type) [AddCommGroup A] [Module (ZMod p) A]

/-- The `𝔽_p`-linear dual of a finite module is finite. -/
noncomputable instance instFintypeDualMod [NeZero p] [Fintype A] :
    Fintype (Work.SSGRoute.DualMod p A) := by
  classical
  exact Fintype.ofInjective (fun f : Work.SSGRoute.DualMod p A => (f : A → ZMod p))
    (fun f g h => LinearMap.ext fun a => congrFun h a)

instance instFiniteDualMod [NeZero p] [Finite A] : Finite (Work.SSGRoute.DualMod p A) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  exact Finite.of_injective (fun f : Work.SSGRoute.DualMod p A => (f : A → ZMod p))
    (fun f g h => LinearMap.ext fun a => congrFun h a)

end DualFinite

end Work.SSGRoute.TateDual
