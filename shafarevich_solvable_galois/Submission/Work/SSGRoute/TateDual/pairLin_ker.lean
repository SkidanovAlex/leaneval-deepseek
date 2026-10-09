import Mathlib
import Submission.Work.SSGRoute.TateDual.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel of the pairing `Coind(M) → Coind(M^∨)ᵛ`

The pairing
`⟨f, g⟩ = ∑ x : G, (g x) (f x)`,  `f : G → M`,  `g ∈ coindUp G (M^∨)`,
is `𝔽_p`-linear in `f` (`Work.SSGRoute.TateDual.pairLin`) and its kernel is exactly the
diagonal `Work.SSGRoute.TateDual.coindDiagSub p G M = {x ↦ x • m}`.

* If `f = (x ↦ x • m)` and `g ∈ coindUp G (M^∨)`, i.e. `∑ x, x⁻¹ • g x = 0`, then
  `⟨f, g⟩ = ∑ x, (x⁻¹ • g x) m = (∑ x, x⁻¹ • g x) m = 0`; so the diagonal lies in the kernel.
* Conversely, if `⟨f, g⟩ = 0` for all `g ∈ coindUp G (M^∨)`, test against the two-point
  functions `g_{x,ψ} = (y ↦ (y = x ? x • ψ : 0)) - (y ↦ (y = 1 ? ψ : 0))`: these lie in
  `coindUp G (M^∨)` because `coindAug g_{x,ψ} = x⁻¹ • (x • ψ) - 1⁻¹ • ψ = 0`, and
  `⟨f, g_{x,ψ}⟩ = (x • ψ)(f x) - ψ (f 1) = ψ (x⁻¹ • f x - f 1)`.  Hence `ψ (x⁻¹ • f x - f 1) = 0`
  for every `ψ ∈ M^∨`; as the functionals separate points (`M` is a vector space over the field
  `𝔽_p`), `x⁻¹ • f x = f 1`, i.e. `f = (x ↦ x • f 1)` is diagonal.

This is the "left kernel" half of the duality `Coind(M)/M ≅ Coind(M^∨)ᵛ`
(see `Work.SSGRoute.TateDual.dual_coindUp_coindShift`).
-/

namespace Work.SSGRoute.TateDual

open scoped BigOperators

/-! ## Auxiliary computations -/

/-- Evaluation of a functional supported at a single point:
`∑ y, (y = x ? ψ : 0) (f y) = ψ (f x)`. -/
lemma sum_ite_dual_apply {p : ℕ} {G : Type} [Fintype G] [DecidableEq G] {M : Type}
    [AddCommGroup M] [Module (ZMod p) M] (x : G) (ψ : M →ₗ[ZMod p] ZMod p) (f : G → M) :
    ∑ y : G, (if y = x then ψ else (0 : M →ₗ[ZMod p] ZMod p)) (f y) = ψ (f x) := by
  rw [show (∑ y : G, (if y = x then ψ else (0 : M →ₗ[ZMod p] ZMod p)) (f y))
      = ∑ y : G, if y = x then ψ (f y) else 0 from
    Finset.sum_congr rfl fun y _ => by split_ifs <;> simp]
  rw [Finset.sum_ite_eq']
  simp

/-- The twisted norm of a function supported at a single point:
`coindAug (y = c ? v : 0) = c⁻¹ • v`. -/
lemma coindAug_ite_smul {p : ℕ} {G : Type} [Group G] [Fintype G] [DecidableEq G]
    {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] (c : G) (v : Work.SSGRoute.DualMod p M) :
    Work.Tate.coindAug G (Work.SSGRoute.DualMod p M)
      (fun y : G => if y = c then v else 0) = c⁻¹ • v := by
  rw [Work.Tate.coindAug_apply]
  rw [show (∑ y : G, y⁻¹ • (if y = c then v else (0 : Work.SSGRoute.DualMod p M)))
      = ∑ y : G, if y = c then y⁻¹ • v else 0 from
    Finset.sum_congr rfl fun y _ => by split_ifs <;> simp]
  rw [Finset.sum_ite_eq']
  simp

/-- The value of the pairing against the two-point function
`(y = x ? x • ψ : 0) - (y = 1 ? ψ : 0)`. -/
private lemma sum_ite_pairing {p : ℕ} {G : Type} [Group G] [Fintype G] [DecidableEq G] {M : Type}
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (f : G → M) (x : G) (ψ : Work.SSGRoute.DualMod p M) :
    ∑ y : G, ((if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
        - (if y = 1 then ψ else 0)) (f y) = ψ (x⁻¹ • f x - f 1) := by
  rw [show (∑ y : G, ((if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
        - (if y = 1 then ψ else 0)) (f y))
      = ∑ y : G, (((if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M)) (f y))
          - ((if y = 1 then ψ else 0) (f y))) from
    Finset.sum_congr rfl fun y _ => rfl]
  rw [Finset.sum_sub_distrib, sum_ite_dual_apply x (x • ψ) f, sum_ite_dual_apply 1 ψ f,
    Work.SSGRoute.DualMod.dualSMul_apply, map_sub]

/-! ## The kernel computation -/

theorem pairLin_ker (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] :
    LinearMap.ker (Work.SSGRoute.TateDual.pairLin p G M)
      = Work.SSGRoute.TateDual.coindDiagSub p G M := by
  classical
  refine le_antisymm ?_ ?_
  · -- the pairing vanishes on `coindUp G (M^∨)` exactly on the diagonal
    intro f hf
    rw [LinearMap.mem_ker] at hf
    rw [mem_coindDiagSub]
    have hkey : ∀ (x : G) (ψ : Work.SSGRoute.DualMod p M), ψ (x⁻¹ • f x - f 1) = 0 := by
      intro x ψ
      have hmem : ((fun y : G => if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
          - (fun y : G => if y = 1 then ψ else (0 : Work.SSGRoute.DualMod p M)))
          ∈ Work.Tate.coindUp G (Work.SSGRoute.DualMod p M) := by
        show Work.Tate.coindAug G (Work.SSGRoute.DualMod p M)
          ((fun y : G => if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
            - (fun y : G => if y = 1 then ψ else (0 : Work.SSGRoute.DualMod p M))) = 0
        rw [map_sub, coindAug_ite_smul x (x • ψ), inv_smul_smul, coindAug_ite_smul 1 ψ]
        simp
      have h0 : (Work.SSGRoute.TateDual.pairLin p G M f)
          ⟨(fun y : G => if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
            - (fun y : G => if y = 1 then ψ else (0 : Work.SSGRoute.DualMod p M)), hmem⟩ = 0 := by
        rw [hf]; rfl
      have hpair : (Work.SSGRoute.TateDual.pairLin p G M f)
          ⟨(fun y : G => if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
            - (fun y : G => if y = 1 then ψ else (0 : Work.SSGRoute.DualMod p M)), hmem⟩
          = ψ (x⁻¹ • f x - f 1) := by
        rw [pairLin_apply]
        show (∑ y : G, (((fun y : G => if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
            - (fun y : G => if y = 1 then ψ else (0 : Work.SSGRoute.DualMod p M))) y) (f y))
          = ψ (x⁻¹ • f x - f 1)
        rw [show (∑ y : G, (((fun y : G => if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
            - (fun y : G => if y = 1 then ψ else (0 : Work.SSGRoute.DualMod p M))) y) (f y))
            = ∑ y : G, ((if y = x then x • ψ else (0 : Work.SSGRoute.DualMod p M))
              - (if y = 1 then ψ else 0)) (f y) from Finset.sum_congr rfl fun y _ => rfl]
        exact sum_ite_pairing f x ψ
      rw [← hpair]
      exact h0
    refine ⟨f 1, funext fun x => ?_⟩
    have hzero : x⁻¹ • f x - f 1 = 0 :=
      (Module.forall_dual_apply_eq_zero_iff (ZMod p) (x⁻¹ • f x - f 1)).mp (hkey x)
    have hx2 : x⁻¹ • f x = f 1 := sub_eq_zero.mp hzero
    rw [← hx2, smul_inv_smul]
  · -- the diagonal lies in the kernel
    intro f hf
    rw [mem_coindDiagSub] at hf
    obtain ⟨m, rfl⟩ := hf
    rw [LinearMap.mem_ker]
    ext g
    rw [pairLin_apply, LinearMap.zero_apply]
    have hg : (∑ x : G, x⁻¹ • (g : G → Work.SSGRoute.DualMod p M) x) = 0 :=
      Work.Tate.mem_coindUp_iff.mp g.2
    have hval : (∑ x : G, x⁻¹ • (g : G → Work.SSGRoute.DualMod p M) x) m = 0 := by
      rw [hg]; rfl
    rw [← hval, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Work.SSGRoute.DualMod.dualSMul_apply, inv_inv]

end Work.SSGRoute.TateDual
