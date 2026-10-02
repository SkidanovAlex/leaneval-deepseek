import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.tcmModelMul
import Submission.Work.Whitney.tcmF_inv_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The `Φ`-transport of the inverse coordinate identification

For the model product formula over a subsingleton base, the two sides are compared after pulling
back along the *inverse* coordinate identification `Work.Whitney.Fib.tcmF_inv`, which identifies
the pair `(Y × ℝ^{p+q}, Sph) `with the pair `(tcmX Y p q, A ∪ C)`.  The two lemmas here are the
inputs of the induction:

* `phi_F_pullback`: the `Φ`-transport of a class pulled back along `tcmF` is the class pulled back
  along the identification of the sphere bundle with the punctured bundle — i.e. `Φ ∘ F^* = jMap`;
* `phi_injective`: `Φ` is injective (equivalently, `F^*` is surjective because the punctured and the
  sphere pairs have the same relative cohomology).
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- The two coordinate identifications are inverse to each other, as continuous maps. -/
theorem tcmF_comp_tcmF_inv'' (p q : ℕ) :
    (tcmF Y p q).comp (Fib.tcmF_inv Y p q)
      = ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p + q))) :=
  ContinuousMap.ext (fun y => Fib.tcmF_tcmF_inv Y p q y)

/-- **The `Φ`-transport of an `F`-pullback is the `jMap` of the class.** -/
theorem phi_F_pullback (p q n : ℕ)
    (x : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin (p + q))) (Punct Y (p + q))) :
    (relCohMap (Fib.tcmF_inv Y p q) (Sph Y (p + q)) (tcmA Y p q ∪ tcmC Y p q)
      (tcmF_inv_mem' (Y := Y) p q) ℤ n).hom
      ((relCohMap (tcmF Y p q) (tcmA Y p q ∪ tcmC Y p q) (Punct Y (p + q))
        (tcmF_mem Y p q) ℤ n).hom x)
    = (relCohMap (ContinuousMap.id (Y × EuclideanSpace ℝ (Fin (p + q)))) (Sph Y (p + q))
        (Punct Y (p + q)) (mem_Sph_punct Y (p + q)) ℤ n).hom x := by
  rw [relCohMap_compA_apply (Sph Y (p + q)) (tcmA Y p q ∪ tcmC Y p q) (Punct Y (p + q))
    (Fib.tcmF_inv Y p q) (tcmF Y p q) (tcmF_inv_mem' (Y := Y) p q) (tcmF_mem Y p q)
    (fun x hx => tcmF_mem Y p q (Fib.tcmF_inv Y p q x) (tcmF_inv_mem' (Y := Y) p q x hx)) ℤ n x]
  rw [relCohMap_congrA (Sph Y (p + q)) (Punct Y (p + q)) (tcmF_comp_tcmF_inv'' p q)
    (fun x hx => tcmF_mem Y p q (Fib.tcmF_inv Y p q x) (tcmF_inv_mem' (Y := Y) p q x hx))
    (fun x hx => mem_Sph_punct Y (p + q) x hx) ℤ n]

/-- **The `Φ`-transport is injective.** -/
theorem phi_injective (p q n : ℕ) :
    Function.Injective
      ((relCohMap (Fib.tcmF_inv Y p q) (Sph Y (p + q)) (tcmA Y p q ∪ tcmC Y p q)
        (tcmF_inv_mem' (Y := Y) p q) ℤ n).hom) := by
  intro A B hAB
  obtain ⟨x, rfl⟩ := (bijective_relCohMap_tcmF (B := Y) p q n).2 A
  obtain ⟨y, hy⟩ := (bijective_relCohMap_tcmF (B := Y) p q n).2 B
  rw [← hy] at hAB ⊢
  have hxy : x = y := (bijective_jMap Y (p + q) n).1 (by
    rw [← phi_F_pullback (Y := Y) p q n x, ← phi_F_pullback (Y := Y) p q n y]
    exact hAB)
  exact congrArg (fun z => (relCohMap (tcmF Y p q) (tcmA Y p q ∪ tcmC Y p q) (Punct Y (p + q))
    (tcmF_mem Y p q) ℤ n).hom z) hxy

/-- **`Φ` of the model class of the sum is the sphere model class**: the round trip
`Mpun (p+q) ↦ F^* ↦ Φ` is `Mn (p+q)`. -/
theorem phi_Mpun (p q : ℕ) :
    (relCohMap (Fib.tcmF_inv Y p q) (Sph Y (p + q)) (tcmA Y p q ∪ tcmC Y p q)
      (tcmF_inv_mem' (Y := Y) p q) ℤ (p + q)).hom
      ((relCohMap (tcmF Y p q) (tcmA Y p q ∪ tcmC Y p q) (Punct Y (p + q))
        (tcmF_mem Y p q) ℤ (p + q)).hom (Mpun (p + q) Y))
    = Mn (p + q) Y := by
  rw [phi_F_pullback (Y := Y) p q (p + q) (Mpun (p + q) Y), Mpun_spec]

end

end Work.Whitney
