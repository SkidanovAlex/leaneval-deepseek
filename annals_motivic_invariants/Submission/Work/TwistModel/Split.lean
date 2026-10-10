/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TwistModel.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The divisor-degree bridge of a twist model, split

A `TwistCurveModel D` (`Work.PointlessIndexFive.Defs`) carries two bridges: the **point bridge**
`C(𝕜) ≠ ∅ ↔ cls = 0` and the **divisor-degree bridge**
`(∃ a 𝕜-rational divisor of degree n) ↔ n • cls = 0`.

This file shows that, *given the point bridge and the presence of a `𝕜`-rational divisor of
degree `5`* (the orbit divisor of the twist construction), the divisor-degree bridge is
**equivalent to its rigid half**

  `DivisorRigidity D C : ∀ n, HasRatDivisorOfDegree 𝕜 C n → n • cls = 0`.

The other half, `n • cls = 0 → ∃ a divisor of degree n`, is then formal: the class of the twist has
exact additive order `5` (`Work.TorsorExistence.five_smul_cls`, and `Work.Twist`'s
`nsmul_cls_eq_zero_iff`/`exists_shift_eq_nsmul_iff_five_dvd` say `n • cls = 0 ↔ 5 ∣ n` for
pointless `D`), so `n • cls = 0` forces `n = 5m`, and `m` copies of the orbit divisor give a
divisor of degree `n`.  In the trivial-class case `cls = 0` the same conclusion follows from the
point bridge: a `𝕜`-point gives a degree-`1` divisor
(`Work.TwistModel.hasRatDivisorOfDegree_one_of_hasRatPoint`), hence divisors of every degree by
additivity (`Work.Arithmetic.HasRatDivisorOfDegree.add`).

So the *only* non-formal geometric input of the divisor-degree bridge is `DivisorRigidity`, and for
pointless `D` this is literally the index-`5` statement (`rigidity_iff_index_five`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace Work.TwistModel

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-! ## 1. Multiples of a divisor of degree `5` -/

omit [DecidableEq 𝕜] in
/-- A rational divisor of degree `5` gives rational divisors of all degrees divisible by `5`, by
additivity of degrees (`Work.Arithmetic.HasRatDivisorOfDegree.add`). -/
theorem hasRatDivisorOfDegree_mul_five {C : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.Scheme.Over C (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (h5 : Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C 5) (m : ℕ) :
    Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C (5 * m) := by
  induction m with
  | zero => simpa using Work.Arithmetic.hasRatDivisorOfDegree_zero 𝕜 C
  | succ k ih =>
    have h : 5 * (k + 1) = 5 * k + 5 := by ring
    rw [h]
    exact ih.add h5

/-- `5` is a period of the class of every quintic twist: `D.toTorsor.DivisorOfDegree 5`. -/
theorem toTorsor_divisorOfDegree_five (D : QuinticTwist 𝕜) :
    D.toTorsor.DivisorOfDegree 5 :=
  (Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff D 5).mpr
    (Work.TorsorExistence.five_smul_cls D)

/-! ## 2. The rigidity is the index-`5` statement -/

/-- **The rigid half of the divisor bridge is the index-`5` statement** for a pointless twist: a
`𝕜`-rational divisor of degree `n` on the model must have `5 ∣ n`.

Indeed `D.toTorsor.DivisorOfDegree n` is `n • cls = 0`
(`Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff`), and for pointless `D` the class has exact
additive order `5` (`Work.PointlessIndexFive.addOrderOf_cls_eq_five`, see also
`Work.Twist.exists_shift_eq_nsmul_iff_five_dvd`). -/
theorem rigidity_iff_index_five {D : QuinticTwist 𝕜} {C : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.Scheme.Over C (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (h : D.Pointless) :
    DivisorRigidity D C ↔
      ∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C n → 5 ∣ n := by
  constructor
  · intro hR n hn
    have hcls : n • D.cls = 0 :=
      (Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff D n).mp (hR n hn)
    rw [← Work.PointlessIndexFive.addOrderOf_cls_eq_five D h]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hcls
  · intro hR n hn
    rw [Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (by
      rw [Work.PointlessIndexFive.addOrderOf_cls_eq_five D h]
      exact hR n hn)

/-! ## 3. The divisor bridge from its rigid half (pointless case) -/

/-- **The divisor-degree bridge is equivalent to its rigid half**, for a pointless twist and in the
presence of the orbit divisor.  (The point bridge is not even needed here: `cls ≠ 0` rules out a
`𝕜`-point, and every `n • cls = 0` has `5 ∣ n`.) -/
theorem divisorBridge_iff_rigidity_of_pointless {D : QuinticTwist 𝕜}
    {C : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.Scheme.Over C (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (h : D.Pointless)
    (h5 : Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C 5) :
    DivisorBridge D C ↔ DivisorRigidity D C := by
  constructor
  · intro hB n hn
    exact (hB n).mp hn
  · intro hR n
    refine ⟨hR n, fun hn => ?_⟩
    -- `n • cls = 0`; as `cls` has exact order `5`, `5 ∣ n`, say `n = 5 * m`.
    have h5n : 5 ∣ n := by
      rw [← Work.PointlessIndexFive.addOrderOf_cls_eq_five D h]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        ((Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff D n).mpr hn)
    obtain ⟨m, rfl⟩ := h5n
    exact hasRatDivisorOfDegree_mul_five h5 m

end

end Work.TwistModel
