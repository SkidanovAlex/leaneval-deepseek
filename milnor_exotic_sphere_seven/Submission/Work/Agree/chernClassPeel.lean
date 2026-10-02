import Mathlib
import Submission.Work.Agree.whitneySumRAssoc
import Submission.Work.Agree.complexificationIso
import Submission.Work.Whitney.Stability

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Peeling trivial summands off a real Whitney sum

`Work.Whitney.chernClass_complexification_whitneySumR_trivial` removes *one* trivial real line
summand from the complexified Whitney sum.  Iterating it with `Work.Agree.whitneySumRAssoc` and
`Work.Agree.whitneySumRCongr` removes `n ≥ 1` of them:
`c_j(ℂ(Z ⊕ εⁿ)) = c_j(ℂ Z)`.

The case `n = 0` is a rank-`0` degenerate case and is not needed here.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- The only map `Fin 1 → Fin 1 × Fin 1`, as an equivalence. -/
def unitPairEquiv : Fin 1 ≃ Fin 1 × Fin 1 where
  toFun _ := (default, default)
  invFun _ := default
  left_inv x := Subsingleton.elim _ _
  right_inv x := Subsingleton.elim _ _

@[simp] theorem unitPairEquiv_apply (i : Fin 1) : unitPairEquiv i = (default, default) := rfl

/-- **`ε^{n+1}` is the Whitney sum of `εⁿ` and `ε¹`.** -/
theorem trivial_trivialSumR_iso {B : Type} [TopologicalSpace B] (n : ℕ) :
    Nonempty (Work.Thom.BundleIso
      (RealBundle.trivial B (EuclideanSpace ℝ (Fin (n + 1))) (Fin 1))
      (Work.Whitney.whitneySumR
        (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) (Fin 1))
        (RealBundle.trivial B (EuclideanSpace ℝ (Fin 1)) (Fin 1)))) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre
    (RealBundle.trivial B (EuclideanSpace ℝ (Fin (n + 1))) (Fin 1))
    (Work.Whitney.whitneySumR
      (RealBundle.trivial B (EuclideanSpace ℝ (Fin n)) (Fin 1))
      (RealBundle.trivial B (EuclideanSpace ℝ (Fin 1)) (Fin 1)))
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (n + 1)))) unitPairEquiv ?_ ?_ ?_
  · intro i
    simp only [Work.Whitney.whitneySumR_baseSet, RealBundle.trivial_baseSet]
    exact Set.univ_inter _
  · intro b
    simp only [Work.Whitney.whitneySumR_indexAt, RealBundle.trivial_indexAt, unitPairEquiv_apply]
  · intro i b
    apply ContinuousLinearMap.ext
    intro v
    simp only [Work.Whitney.whitneySumR_coordChange, Work.Whitney.whitneySumR_indexAt,
      RealBundle.trivial_coordChange, RealBundle.trivial_indexAt, unitPairEquiv_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.refl_apply]
    simp

/-- **`c_j(ℂ(Z ⊕ εⁿ)) = c_j(ℂ Z)`** for `n ≥ 1`: peeling off `n` trivial real line summands does
not change the Chern classes of the complexification. -/
theorem chernClassPeel {B : Type} [TopologicalSpace B] {k : ℕ} {ι : Type} [Fintype ι]
    (n j : ℕ) (hn : 1 ≤ n)
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    Work.Thom.chernClass (k + n) j
        (Work.Thom.complexificationCore (Work.Whitney.whitneySumR Z
          (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin n)) (Fin 1))))
      = Work.Thom.chernClass k j (Work.Thom.complexificationCore Z) := by
  induction n, hn using Nat.le_induction with
  | base =>
    exact Work.Whitney.chernClass_complexification_whitneySumR_trivial (ι₀ := Fin 1) Z j
  | succ n hn ih =>
    -- `Z ⊕ ε^{n+1} ≅ (Z ⊕ εⁿ) ⊕ ε¹`, as real bundles
    have hA : Nonempty (Work.Thom.BundleIso
        (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin (n + 1))) (Fin 1))
        (Work.Whitney.whitneySumR
          (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin n)) (Fin 1))
          (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) (Fin 1)))) :=
      trivial_trivialSumR_iso (B := B) n
    have hcongr := whitneySumRCongr Z Z
      (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin (n + 1))) (Fin 1))
      (Work.Whitney.whitneySumR
        (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin n)) (Fin 1))
        (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) (Fin 1)))
      ⟨Work.Thom.BundleIso.refl Z⟩ hA
    have hassoc := whitneySumRAssoc Z
      (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin n)) (Fin 1))
      (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) (Fin 1))
    obtain ⟨e1⟩ := hcongr
    obtain ⟨e2⟩ := hassoc
    have hiso : Nonempty (Work.Thom.BundleIso
        (Work.Whitney.whitneySumR Z
          (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin (n + 1))) (Fin 1)))
        (Work.Whitney.whitneySumR
          (Work.Whitney.whitneySumR Z
            (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin n)) (Fin 1)))
          (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) (Fin 1)))) :=
      ⟨e1.trans e2⟩
    rw [chernClass_complexificationCore_eq'
      (by omega : k + (n + 1) = (k + n) + 1) _ _ hiso j]
    rw [Work.Whitney.chernClass_complexification_whitneySumR_trivial (ι₀ := Fin 1)
      (Work.Whitney.whitneySumR Z
        (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin n)) (Fin 1))) j]
    exact ih

end

end Work.Agree
