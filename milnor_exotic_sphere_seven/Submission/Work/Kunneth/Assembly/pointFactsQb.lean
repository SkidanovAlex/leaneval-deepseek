import Mathlib
import Submission.Work.Kunneth.Assembly.Defs
import Submission.Work.Kunneth.PointBasic
import Submission.Work.Kunneth.PointMain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The cohomology of `ℂP^{m-1} = P(ε^m over the point)`: vanishing and generators

For `Qb m = Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore m) = ℂP^{m-1}` (empty for
`m = 0`):

* `H^q(Qb m) = 0` unless `q` is even and `q < 2m` (`Work.Kunneth.subsingleton_coh_projSpace_trivCore_of_not`
  for `m = n+1`, and emptiness of `Qb 0` for `m = 0`);
* for `i < m` the class `ζ^i` is a `ℤ`-basis of the (free of rank one) module `H^{2i}(Qb m)`, i.e.
  there is a linear equivalence `H^{2i}(Qb m) ≃ₗ[ℤ] ℤ` sending `ζ^i` to `1`
  (`Work.Kunneth.keyLH` + `Work.Kunneth.smul_zetaPow_eq_zero`).
-/

namespace Work.Kunneth.Asm

open CategoryTheory Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

theorem pointFactsQb (m : ℕ) :
    (∀ q : ℕ, ¬ (Even q ∧ q < 2 * m) → Subsingleton (Coh ℤ q (Qb m))) ∧
    (∀ i : ℕ, i < m → ∃ f : Coh ℤ (2 * i) (Qb m) ≃ₗ[ℤ] ℤ,
      f (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) i) = 1) := by
  constructor
  · intro q hq
    cases m with
    | zero => exact Work.Kunneth.subsingleton_coh_trivCore_zero q
    | succ n =>
        exact Work.Kunneth.subsingleton_coh_projSpace_trivCore_of_not (n := n) (d := q)
          (fun h => hq ⟨h.1, by omega⟩)
  · intro i hi
    cases m with
    | zero => omega
    | succ n =>
        have hin : i ≤ n := by omega
        let ζ : Coh ℤ (2 * i) (Qb (n + 1)) :=
          Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) i
        let mk : ℤ →ₗ[ℤ] Coh ℤ (2 * i) (Qb (n + 1)) :=
          LinearMap.toSpanSingleton ℤ (Coh ℤ (2 * i) (Qb (n + 1))) ζ
        have hmk : ∀ a, mk a = a • Work.LerayHirsch.zetaPow
            (Work.LerayHirsch.trivCore (n + 1)) i := by
          intro a
          rw [show mk a = (LinearMap.toSpanSingleton ℤ _ ζ) a from rfl,
            LinearMap.toSpanSingleton_apply]
          exact int_smul_eq_zsmul (inferInstance : Module ℤ (Coh ℤ (2 * i) (Qb (n + 1)))) a ζ
        have hinj : Function.Injective mk := by
          intro a b hab
          rw [hmk, hmk] at hab
          exact Work.Kunneth.smul_zetaPow_injective n i hin a b hab
        have hsurj : Function.Surjective mk := by
          intro y
          obtain ⟨a, ha⟩ := (Work.Gen.ChernGen.span_singleton_eq_top_iff'
            (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) i)).mp
            (Work.Kunneth.keyLH n i hin) y
          exact ⟨a, by rw [hmk]; exact ha.symm⟩
        refine ⟨(LinearEquiv.ofBijective mk ⟨hinj, hsurj⟩).symm, ?_⟩
        have hone : mk 1 = Work.LerayHirsch.zetaPow
            (Work.LerayHirsch.trivCore (n + 1)) i := by
          rw [hmk, one_smul]
        rw [← hone]
        exact LinearEquiv.symm_apply_apply (LinearEquiv.ofBijective mk ⟨hinj, hsurj⟩) 1

end

end Work.Kunneth.Asm
