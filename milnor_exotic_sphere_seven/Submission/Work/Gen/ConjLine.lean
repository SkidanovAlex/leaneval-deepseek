import Mathlib
import Submission.Work.Gen.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The conjugate of the tautological line bundle of `ℂPⁿ`

`Work.Gen.conjLine n` is the complex conjugate `\overline{O(-1)}` of the tautological line bundle
`Work.Gen.tautLine n`, presented over the *same* standard cover of `ℂPⁿ`: the same base sets and
index map, with the transition functions *conjugated*.

Its purpose in this area is to give a *concrete* model of a complex line bundle whose
realification is related to that of `Work.Gen.tautLine n` by an **orientation reversing**
isomorphism (the fibrewise complex conjugation), which is what the lemma
`Work.Gen.tautDual_euler_neg` measures: the Euler classes of `O(1)` and `O(-1)` differ by a sign,
i.e. `c₁(O(1)) = −c₁(O(-1))`, equivalently `c₁(\overline O(-1)) = −c₁(O(-1))`.

We also record the two explicit isomorphisms that the sign argument uses:

* `Work.Gen.tautDual_iso_conjLine` — `O(1) ≅ \overline{O(-1)}` as **complex** line bundles, with the
  gauge `1/Fᵢ` where `Fᵢ` is the squared norm of the normalised homogeneous representative
  (`Work.Gen.chartNormSq`); by `Work.Thom.thomClassRank_eulerClass_iso` this identifies the Euler
  classes of `tautDual n` and `conjLine n`;
* `Work.Gen.conj_iso_tautLine` — `\overline{O(-1)} ≅ O(-1)` as **real** line bundles, with the
  fibrewise complex conjugation, which reverses the orientation.
-/

open Work.Projective

namespace Work.Gen

noncomputable section

variable {n : ℕ}

/-- **The conjugate `\overline{O(-1)}` of the tautological line bundle** over the standard cover of
`ℂPⁿ`: same base sets and index map as `Work.Gen.tautLine n`, transitions conjugated. -/
def conjLine (n : ℕ) :
    VectorBundleCore ℂ (CP n) (EuclideanSpace ℂ (Fin 1)) (Fin (n + 1)) where
  baseSet i := chartSet i
  isOpen_baseSet i := isOpen_chartSet i
  indexAt x := Classical.choose (exists_mem_chartSet x)
  mem_baseSet_at x := Classical.choose_spec (exists_mem_chartSet x)
  coordChange i j x := (star (homCoord n i j x)) •
    ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))
  coordChange_self i x _ v := by simp
  continuousOn_coordChange i j := by
    refine ((continuousOn_homCoord (n := n) i j).star.smul
      (continuousOn_const : ContinuousOn
        (fun _ : CP n => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)).mono ?_
    intro x hx
    exact hx.1
  coordChange_comp i j k x hx v := by
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    rw [homCoord_mul i j k hx.1.1 hx.1.2 hx.2]
    simp only [star_mul, ContinuousLinearMap.id_apply, mul_comm]

@[simp] theorem conjLine_baseSet (n : ℕ) (i : Fin (n + 1)) :
    (conjLine n).baseSet i = chartSet i := rfl

@[simp] theorem conjLine_indexAt (n : ℕ) (x : CP n) :
    (conjLine n).indexAt x = Classical.choose (exists_mem_chartSet x) := rfl

@[simp] theorem conjLine_coordChange (n : ℕ) (i j : Fin (n + 1)) (x : CP n) :
    (conjLine n).coordChange i j x = (star (homCoord n i j x)) •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := rfl

end

end Work.Gen
