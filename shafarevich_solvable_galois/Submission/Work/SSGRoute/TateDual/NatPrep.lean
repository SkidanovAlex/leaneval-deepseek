/-
# Vocabulary for the *naturality* of the degree `-2` Tate duality

`Work.SSGRoute.TateDual.dual_coindUp_coindShift` states the duality of the shift sequence
`Coind(M)/M ≅ Dual(coindUp G (M^∨))` as an existence statement.  For the naturality of the
degree `(-2)` Tate duality `Ĥ⁻²(G, M^∨) ≅ H¹(G, M)^∨` one needs the *canonical* such
isomorphism, i.e. the one induced by the explicit pairing

`⟨f, g⟩ = ∑ x : G, (g x) (f x)`,  `f : G → M`,  `g ∈ coindUp G (M^∨)`

of `Work.SSGRoute.TateDual.pairLin`.  This file only provides the two maps that have to be
tracked in order to speak about naturality:

* `coindUpMapLin` — the induced map `coindUp G A → coindUp G B` of an equivariant `𝔽_p`-linear
  `f : A → B`, as an `𝔽_p`-linear map (the `Work.Tate` version is only additive);
* `shiftDual` — the canonical pairing, as an `𝔽_p`-linear map
  `coindShift G M →ₗ Dual(coindUp G (M^∨))`: the pairing `pairLin` descended along
  `(pairLin).ker = coindDiagSub` (`pairLin_ker`).
-/
import Mathlib
import Submission.Work.SSGRoute.TateDual.Defs
import Submission.Work.SSGRoute.TateDual.Setup
import Submission.Work.SSGRoute.TateDual.pairLin_ker
import Submission.Work.SSGRoute.TateDual.pairLin_equiv
import Submission.Work.SSGRoute.TateDual.finrank_coindShift_eq_finrank_dual_coindUp
import Submission.Work.Tate.CoindUp
import Submission.Work.Tate.Shift
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TateDual

open scoped BigOperators

/-! ## The linear `I_G`-twist map -/

section CoindUpLin

variable (p : ℕ) (G : Type) [Group G] [Fintype G]

/-- The map `coindUp G A → coindUp G B` induced by an equivariant `𝔽_p`-linear `f : A → B`,
as an `𝔽_p`-linear map (the `Work.Tate.coindUpMap` is only additive). -/
noncomputable def coindUpMapLin {A : Type} {B : Type} [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod p) A] [Module (ZMod p) B] [DistribMulAction G A] [DistribMulAction G B]
    [SMulCommClass G (ZMod p) A] [SMulCommClass G (ZMod p) B]
    (f : A →ₗ[ZMod p] B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    ↥(Work.Tate.coindUp G A) →ₗ[ZMod p] ↥(Work.Tate.coindUp G B) where
  toFun x := Work.Tate.coindUpMap f.toAddMonoidHom hf x
  map_add' x y := map_add (Work.Tate.coindUpMap f.toAddMonoidHom hf) x y
  map_smul' c x := by
    ext γ
    show f (((c • x : ↥(Work.Tate.coindUp G A)) : G → A) γ)
      = (c • (Work.Tate.coindUpMap f.toAddMonoidHom hf x : ↥(Work.Tate.coindUp G B)) : G → B) γ
    simp only [coe_smul_zmod_coindUp, Pi.smul_apply, map_smul]
    congr 1

variable {A : Type} {B : Type} [AddCommGroup A] [AddCommGroup B]
  [Module (ZMod p) A] [Module (ZMod p) B] [DistribMulAction G A] [DistribMulAction G B]
  [SMulCommClass G (ZMod p) A] [SMulCommClass G (ZMod p) B]

@[simp] theorem coindUpMapLin_apply (f : A →ₗ[ZMod p] B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (x : ↥(Work.Tate.coindUp G A))
    (γ : G) :
    ((coindUpMapLin p G f hf x : ↥(Work.Tate.coindUp G B)) : G → B) γ
      = f ((x : G → A) γ) :=
  Work.Tate.coindUpMap_apply f.toAddMonoidHom hf x γ

theorem coindUpMapLin_toAddMonoidHom (f : A →ₗ[ZMod p] B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    (coindUpMapLin p G f hf).toAddMonoidHom = Work.Tate.coindUpMap f.toAddMonoidHom hf :=
  AddMonoidHom.ext fun _ => rfl

theorem coindUpMapLin_equiv (f : A →ₗ[ZMod p] B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (γ : G) (x : ↥(Work.Tate.coindUp G A)) :
    coindUpMapLin p G f hf (γ • x) = γ • coindUpMapLin p G f hf x :=
  Work.Tate.coindUpMap_equiv f.toAddMonoidHom hf γ x

end CoindUpLin

/-! ## The canonical pairing `Coind(M)/M → Dual(coindUp G (M^∨))` -/

section ShiftDual

variable (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]

/-- The diagonal lies in the kernel of the pairing, in the form needed to descend `pairLin`
to the quotient `coindShift G M = Coind(M)/coindDiag`. -/
theorem coindDiag_le_pairLin_ker (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] :
    Work.Tate.coindDiag G M ≤ (pairLin p G M).toAddMonoidHom.ker := by
  intro f hf
  rw [AddMonoidHom.mem_ker]
  change pairLin p G M f = 0
  rw [← LinearMap.mem_ker, pairLin_ker p G M]
  exact hf

/-- **The canonical shift pairing** `Coind(M)/M →ₗ Dual(coindUp G (M^∨))`,
`⟨f, g⟩ = ∑ x, (g x)(f x)`, descended from `Work.SSGRoute.TateDual.pairLin` whose kernel is
the diagonal `coindDiagSub p G M` (`pairLin_ker`). -/
noncomputable def shiftDual (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] :
    Work.Tate.coindShift G M →ₗ[ZMod p]
      DualMod p ↥(Work.Tate.coindUp G (DualMod p M)) where
  toFun := QuotientAddGroup.lift (Work.Tate.coindDiag G M) (pairLin p G M).toAddMonoidHom
    (coindDiag_le_pairLin_ker p G M)
  map_add' := map_add _
  map_smul' c x := by
    induction x using QuotientAddGroup.induction_on with
    | H f =>
      rw [← QuotientAddGroup.mk'_apply (Work.Tate.coindDiag G M) f]
      rw [quot_zmod_smul_mk]
      simp only [QuotientAddGroup.mk'_apply]
      rw [QuotientAddGroup.lift_mk' (Work.Tate.coindDiag G M) (coindDiag_le_pairLin_ker p G M) (c • f),
        QuotientAddGroup.lift_mk' (Work.Tate.coindDiag G M) (coindDiag_le_pairLin_ker p G M) f]
      exact LinearMap.map_smul (pairLin p G M) c f

variable (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod p) M]

theorem shiftDual_mk' (f : G → M) :
    shiftDual p G M (QuotientAddGroup.mk' (Work.Tate.coindDiag G M) f) = pairLin p G M f :=
  QuotientAddGroup.lift_mk' (Work.Tate.coindDiag G M) (coindDiag_le_pairLin_ker p G M) f

theorem shiftDual_proj (f : G → M) :
    shiftDual p G M (Work.Tate.coindProj G M f) = pairLin p G M f :=
  shiftDual_mk' p G M f

theorem shiftDual_mk'_apply (f : G → M)
    (g : ↥(Work.Tate.coindUp G (DualMod p M))) :
    shiftDual p G M (QuotientAddGroup.mk' (Work.Tate.coindDiag G M) f) g
      = ∑ x : G, ((g : G → DualMod p M) x) (f x) := by
  rw [shiftDual_mk', pairLin_apply]

theorem shiftDual_proj_apply (f : G → M)
    (g : ↥(Work.Tate.coindUp G (DualMod p M))) :
    shiftDual p G M (Work.Tate.coindProj G M f) g
      = ∑ x : G, ((g : G → DualMod p M) x) (f x) :=
  shiftDual_mk'_apply p G M f g

theorem shiftDual_equiv (γ : G) (x : Work.Tate.coindShift G M) :
    shiftDual p G M (γ • x) = γ • shiftDual p G M x := by
  induction x using QuotientAddGroup.induction_on with
  | H f =>
    rw [← QuotientAddGroup.mk'_apply (Work.Tate.coindDiag G M) f]
    rw [Work.Tate.quot_smul_mk']
    rw [shiftDual_mk', shiftDual_mk']
    exact pairLin_equiv p G M γ f

theorem shiftDual_injective [Finite M] : Function.Injective (shiftDual p G M) := by
  intro x y h
  induction x using QuotientAddGroup.induction_on with
  | H f =>
    induction y using QuotientAddGroup.induction_on with
    | H f' =>
      rw [← QuotientAddGroup.mk'_apply (Work.Tate.coindDiag G M) f,
        ← QuotientAddGroup.mk'_apply (Work.Tate.coindDiag G M) f'] at h
      rw [shiftDual_mk', shiftDual_mk'] at h
      have hmem : f - f' ∈ Work.Tate.coindDiag G M := by
        have h2 : f - f' ∈ (pairLin p G M).ker := by
          rw [LinearMap.mem_ker, map_sub, h, sub_self]
        rw [pairLin_ker] at h2
        exact h2
      rw [QuotientAddGroup.eq_iff_sub_mem]
      exact hmem

theorem shiftDual_bijective [Finite M] : Function.Bijective (shiftDual p G M) := by
  have hinj := shiftDual_injective p G M
  refine ⟨hinj, fun y => ?_⟩
  have hfr : Module.finrank (ZMod p) (Work.Tate.coindShift G M)
      = Module.finrank (ZMod p)
          (DualMod p ↥(Work.Tate.coindUp G (DualMod p M))) :=
    finrank_coindShift_eq_finrank_dual_coindUp p G M
  have hrange : (shiftDual p G M).range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj]
    exact hfr
  exact LinearMap.mem_range.mp (by rw [hrange]; exact Submodule.mem_top)

theorem shiftDual_natural (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
    [DistribMulAction G M₂] [SMulCommClass G (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (ψ : Work.Tate.coindShift G M →+ Work.Tate.coindShift G M₂)
    (hψproj : ∀ x : G → M, ψ (QuotientAddGroup.mk' (Work.Tate.coindDiag G M) x)
      = QuotientAddGroup.mk' (Work.Tate.coindDiag G M₂) (Work.Tate.coindMap f.toAddMonoidHom x))
    (y : Work.Tate.coindShift G M) :
    shiftDual p G M₂ (ψ y)
      = (LinearMap.dualMap (coindUpMapLin p G f.dualMap
          (fun g z => by
            show f.dualMap (g • z) = g • f.dualMap z
            ext m
            simp only [LinearMap.dualMap_apply, DualMod.dualSMul_apply, hf])))
        (shiftDual p G M y) := by
  ext g
  induction y using QuotientAddGroup.induction_on with
  | H f' =>
    rw [← QuotientAddGroup.mk'_apply (Work.Tate.coindDiag G M) f'] at *
    rw [hψproj f', LinearMap.dualMap_apply, shiftDual_mk'_apply, shiftDual_mk'_apply]
    simp only [coindUpMapLin_apply, LinearMap.dualMap_apply, Work.Tate.coindMap_apply]
    rfl

end ShiftDual

/-! ## The transpose of an equivariant map is equivariant -/

section DualEquiv

variable (p : ℕ) (G : Type) [Group G] [Fintype G]
  {A : Type} {B : Type} [AddCommGroup A] [AddCommGroup B] [Module (ZMod p) A]
  [Module (ZMod p) B] [DistribMulAction G A] [DistribMulAction G B]
  [SMulCommClass G (ZMod p) A] [SMulCommClass G (ZMod p) B]

/-- The transpose of a `G`-equivariant `𝔽_p`-linear map is `G`-equivariant for the dual
actions: `u^∨ (g • ψ) = g • u^∨ ψ`. -/
theorem dualMap_equiv_of (u : A →ₗ[ZMod p] B)
    (hu : ∀ (g : G) (a : A), u (g • a) = g • u a) :
    ∀ (g : G) (ψ : DualMod p B), u.dualMap (g • ψ) = g • u.dualMap ψ := by
  intro g ψ
  ext a
  simp only [LinearMap.dualMap_apply, DualMod.dualSMul_apply]
  exact congrArg ψ (hu g⁻¹ a).symm

end DualEquiv

end Work.SSGRoute.TateDual
