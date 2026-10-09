/-
# Clauses (1), (2), (6) for the cup-generated local pairing

`E7Fin/cupPairing.lean` defines the pairing `pairOfInv inv` attached to a *single* invariant
functional `inv` per local group (the structure that makes clause (5), naturality in the
coefficient module, formal).  This file proves, for that pairing, the clauses of the local pairing
list that are pure algebra:

* `evCupFun_add_left`, `evCupFun_add_right` — the evaluated cup is additive in each variable;
* `pairOfInv_add_left`, `pairOfInv_add_right` — clauses (1), (2), from the additivity of `inv`;
* `pairOfInv_unramified` — clause (6): the invariant kills the classes unramified at a good place,
  and the cup of two classes vanishing on the inertia vanishes on every pair with a coordinate in
  the inertia.

The remaining clauses — (3), from `E7Fin.evCupFun_coboundary_left` (and its right-hand analogue)
plus the vanishing of `inv` on `2`-coboundaries, and (5), from `E7Fin.pairOfInv_natural` — are
proved in the companion files.  Clause (4) (perfectness) is local Tate duality in its strong form
and is *not* formal: it is the arithmetic input of the construction.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.E7Fin.cupPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct

namespace Work.SSGRoute.E7Fin

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
  (H : Subgroup (Ω ≃ₐ[k] Ω))

/-- The evaluated cup is additive in the first variable. -/
theorem evCupFun_add_left (a a' : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    evCupFun p k Ω K T M (a + a') b = evCupFun p k Ω K T M a b + evCupFun p k Ω K T M a' b := by
  funext g h
  simp only [evCupFun, Pi.add_apply, TensorProduct.add_tmul, map_add]

/-- The evaluated cup is additive in the second variable. -/
theorem evCupFun_add_right (a : (Ω ≃ₐ[k] Ω) → M)
    (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    evCupFun p k Ω K T M a (b + b') = evCupFun p k Ω K T M a b + evCupFun p k Ω K T M a b' := by
  funext g h
  have hb : SSGRoute.res k K g • (b + b') h
      = SSGRoute.res k K g • b h + SSGRoute.res k K g • b' h := by
    rw [Pi.add_apply, smul_add]
  simp only [evCupFun, Pi.add_apply, smul_add, TensorProduct.tmul_add, map_add]

/-- The evaluated cup vanishes on a pair with a coordinate in the inertia. -/
theorem evCupFun_eq_zero_of_inertia (A : ValuationSubring Ω)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha0 : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0)
    (hb0 : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0)
    (g h : Ω ≃ₐ[k] Ω) (hgh : SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) :
    evCupFun p k Ω K T M a b g h = 0 := by
  rcases hgh with hg | hh
  · simp [evCupFun, ha0 g hg]
  · have h0 : SSGRoute.res k K g • b h = 0 := by
      rw [hb0 h hh, smul_zero]
    simp [evCupFun, h0]

/-- **Clause (1)** for the cup-generated pairing: additivity in the first variable, from the
additivity of the invariant `inv` on `DualMod p T`-valued `2`-cochains. -/
theorem pairOfInv_add_left
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_add : ∀ c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      inv (c + c') = inv c + inv c')
    (a a' : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (ha' : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a')
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) :
    pairOfInv p k Ω K T inv M H (a + a') b =
      pairOfInv p k Ω K T inv M H a b + pairOfInv p k Ω K T inv M H a' b := by
  classical
  have hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) H (a + a') := by
    intro g hg h hh
    simp only [Pi.add_apply, ha.1 g hg h hh, ha'.1 g hg h hh, smul_add]
    abel
  rw [pairOfInv_of_cocycle p k Ω K T inv M H (a + a') b ⟨hsum, hb.1⟩,
    pairOfInv_of_cocycle p k Ω K T inv M H a b ⟨ha.1, hb.1⟩,
    pairOfInv_of_cocycle p k Ω K T inv M H a' b ⟨ha'.1, hb.1⟩,
    evCupFun_add_left, hinv_add]

/-- **Clause (2)** for the cup-generated pairing: additivity in the second variable. -/
theorem pairOfInv_add_right
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_add : ∀ c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      inv (c + c') = inv c + inv c')
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') :
    pairOfInv p k Ω K T inv M H a (b + b') =
      pairOfInv p k Ω K T inv M H a b + pairOfInv p k Ω K T inv M H a b' := by
  classical
  have hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) H (b + b') := by
    intro g hg h hh
    simp only [Pi.add_apply, hb.1 g hg h hh, hb'.1 g hg h hh, smul_add]
    abel
  rw [pairOfInv_of_cocycle p k Ω K T inv M H a (b + b') ⟨ha.1, hsum⟩,
    pairOfInv_of_cocycle p k Ω K T inv M H a b ⟨ha.1, hb.1⟩,
    pairOfInv_of_cocycle p k Ω K T inv M H a b' ⟨ha.1, hb'.1⟩,
    evCupFun_add_right, hinv_add]

/-- **Clause (6)** for the cup-generated pairing: if the invariant kills the `2`-cochains that
vanish on every pair with a coordinate in the inertia of a good place, then the pairing is
orthogonal on unramified classes there (the cup of two classes vanishing on the inertia vanishes on
every such pair, by `evCupFun_eq_zero_of_inertia`). -/
theorem pairOfInv_unramified
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv c = 0)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hp : ¬ A.valuation (p : Ω) < 1) (hram : ¬ SSGRoute.IsRamifiedIn k K A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hunram : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) :
    pairOfInv p k Ω K T inv M (SSGRoute.decomp k A) a b = 0 := by
  classical
  rw [pairOfInv_of_cocycle p k Ω K T inv M (SSGRoute.decomp k A) a b ⟨ha.1, hb.1⟩]
  refine hinv_unram A hA hp hram _ (fun g h hgh => ?_)
  exact evCupFun_eq_zero_of_inertia p k Ω K T M A a b
    (fun σ hσ => (hunram σ hσ).1) (fun σ hσ => (hunram σ hσ).2) g h hgh

end

end Work.SSGRoute.E7Fin
