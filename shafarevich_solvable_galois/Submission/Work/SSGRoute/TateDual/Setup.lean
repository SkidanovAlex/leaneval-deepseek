import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Submodule.Range
import Submission.Work.SSGRoute.TateDual.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pairing between `Coind(M)` and the `I_G`-twist of `Coind(M^∨)`

This file sets up the vocabulary for the duality of the shift sequence

`Coind(M)/coindDiag ≅ Dual(coindUp G (M^∨))`.

* `Work.SSGRoute.TateDual.coindDiagSub` is the diagonal `{x ↦ x • m} ⊆ (G → M)` as an
  `𝔽_p`-submodule whose underlying additive subgroup is *definitionally* `Work.Tate.coindDiag G M`
  (so the quotient is literally `Work.Tate.coindShift G M`);
* `Work.SSGRoute.TateDual.pairLin` is the pairing `f ↦ (g ↦ ∑ x, (g x) (f x))`,
  `(G → M) →ₗ Dual(coindUp G (M^∨))`, whose kernel is shown (in the main file) to be
  `coindDiagSub`.
-/

namespace Work.SSGRoute.TateDual

open scoped BigOperators

section DiagSub

variable (p : ℕ) (G : Type) [Group G]

/-- The diagonal `M ↪ Coind(M)`, `m ↦ (x ↦ x • m)`, as an `𝔽_p`-submodule of `G → M`.  Its
underlying additive subgroup is definitionally `Work.Tate.coindDiag G M`, so that the quotient
`(G → M) ⧸ coindDiagSub p G M` is definitionally `Work.Tate.coindShift G M`. -/
def coindDiagSub (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] : Submodule (ZMod p) (G → M) where
  carrier := Set.range fun a : M => (fun x : G => x • a : G → M)
  add_mem' := by
    rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by funext x; simp [smul_add]⟩
  zero_mem' := ⟨0, by funext x; simp⟩
  smul_mem' := by
    rintro c f ⟨a, rfl⟩
    refine ⟨c • a, ?_⟩
    funext x
    show x • (c • a) = c • (x • a)
    exact smul_comm x c a

@[simp] theorem coe_coindDiagSub_toAddSubgroup (M : Type) [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M] :
    (coindDiagSub p G M).toAddSubgroup = Work.Tate.coindDiag G M := rfl

theorem mem_coindDiagSub {M : Type} [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] {f : G → M} :
    f ∈ coindDiagSub p G M ↔ ∃ m : M, f = fun x : G => x • m := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, rfl⟩

theorem coindDiagSub_eq_range (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] :
    coindDiagSub p G M = (coindUnitLin p G M).range := by
  refine le_antisymm ?_ ?_
  · rintro f ⟨m, rfl⟩
    exact ⟨m, rfl⟩
  · rintro f ⟨m, hm⟩
    exact ⟨m, hm.symm ▸ rfl⟩

end DiagSub

section Pair

variable (p : ℕ) (G : Type) [Group G] [Fintype G]

/-- The pairing `(f, g) ↦ ∑ x, (g x) (f x)` between `Coind(M) = (G → M)` and
`Coind(M^∨)`, restricted in the second variable to the `I_G`-twist `coindUp G (M^∨)`.
It is `𝔽_p`-linear in `f`. -/
noncomputable def pairLin (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] :
    (G → M) →ₗ[ZMod p] DualMod p ↥(Work.Tate.coindUp G (DualMod p M)) where
  toFun f :=
    { toFun := fun g => ∑ x : G, ((g : G → DualMod p M) x) (f x)
      map_add' := by
        intro g h
        simp only [AddSubgroup.coe_add, Pi.add_apply, LinearMap.add_apply]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c g
        simp only [coe_smul_zmod_coindUp, Pi.smul_apply, LinearMap.smul_apply]
        exact (Finset.smul_sum (s := Finset.univ)
          (f := fun x : G => ((g : G → DualMod p M) x) (f x)) (r := c)).symm }
  map_add' := by
    intro f h
    ext g
    simp only [LinearMap.add_apply, Pi.add_apply, LinearMap.map_add]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c f
    ext g
    simp only [LinearMap.smul_apply, Pi.smul_apply, LinearMap.map_smul]
    exact (Finset.smul_sum (s := Finset.univ)
      (f := fun x : G => ((g : G → DualMod p M) x) (f x)) (r := c)).symm

@[simp] theorem pairLin_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (f : G → M)
    (g : ↥(Work.Tate.coindUp G (DualMod p M))) :
    pairLin p G M f g = ∑ x : G, ((g : G → DualMod p M) x) (f x) := rfl

end Pair

end Work.SSGRoute.TateDual

namespace Work.SSGRoute.TateDual

section QuotInstances

variable (p : ℕ) (G : Type) [Group G] [Fintype G]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]

/-- The coinduced `G`-action on the quotient `Coind(M)/coindDiag`, transported to the
`Submodule` spelling of the diagonal (the two quotients are definitionally equal). -/
noncomputable instance instSMulQuotDiagSub : SMul G ((G → M) ⧸ coindDiagSub p G M) :=
  inferInstanceAs (SMul G ((G → M) ⧸ Work.Tate.coindDiag G M))

noncomputable instance instDistribMulActionQuotDiagSub :
    DistribMulAction G ((G → M) ⧸ coindDiagSub p G M) :=
  inferInstanceAs (DistribMulAction G ((G → M) ⧸ Work.Tate.coindDiag G M))

end QuotInstances

end Work.SSGRoute.TateDual
