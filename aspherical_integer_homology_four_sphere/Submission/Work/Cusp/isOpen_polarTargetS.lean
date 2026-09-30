/-
# Openness of the target of the shifted polar chart

`polarTargetS v c k B` (`Work.Cusp.Charts`) is the target of the `(c,k)`-th shifted polar chart
`ThetaPolarS v c`: the points of the chart box `B` whose recovered perimeter lift `uqOf v q`,
measured from the shifted cut `c`, lies in the `k`-th shifted wedge.

The defining conditions `uqOf v q - c ∈ [0,1)` and
`fract (uqOf v q - c) ∈ (k/4,(k+1)/4)` are together equivalent to the single *open* condition
`uqOf v q - c ∈ (k/4,(k+1)/4)`: for `k : Fin 4` the interval `(k/4,(k+1)/4)` is contained in
`[0,1)`, so the fractional part is the identity and the `[0,1)`-membership is automatic.

Hence `polarTargetS v c k B = B ∩ (uqOf v - c)⁻¹' (k/4,(k+1)/4)` is open as soon as `B` is,
because `uqOf v` is continuous (it is built from the linear maps `invY v` and `cuspY v` and the
inner product with the slope `σ_v`).  This is the general-`c` version of the `c = 0` statement
`Work.Cusp.polarChart_isOpen_target` (`polarTarget v k B = polarTargetS v 0 k B`).
-/
import Mathlib
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.slope_ne_zero
import Submission.Work.Cusp.invY_wOf

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open scoped Real InnerProductSpace

/-- **The target of the shifted polar chart is the open set
`{q ∈ B | uqOf v q − c ∈ (k/4,(k+1)/4)}`.**  The defining conditions
`uqOf v q − c ∈ [0,1)` and `fract (uqOf v q − c) ∈ (k/4,(k+1)/4)` of `polarTargetS` are together
equivalent to `uqOf v q − c ∈ (k/4,(k+1)/4)`, because `(k/4,(k+1)/4) ⊆ [0,1)` for `k : Fin 4`. -/
theorem polarTargetS_eq (v : Fin 5) (c : ℝ) (k : Fin 4) (B : Set E4) :
    polarTargetS v c k B
      = B ∩ {q : E4 | uqOf v q - c ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)} := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
  have hk1 : ((k : ℝ) + 1) / 4 ≤ 1 := by
    have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    linarith
  ext q
  simp only [polarTargetS, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico, Set.mem_Ioo]
  constructor
  · rintro ⟨hB, hu, hf⟩
    exact ⟨hB, by rwa [Int.fract_eq_self.mpr hu] at hf⟩
  · rintro ⟨hB, hf⟩
    have h0 : 0 ≤ uqOf v q - c := by linarith [hf.1]
    have h1 : uqOf v q - c < 1 := by linarith [hf.2, hk1]
    exact ⟨hB, ⟨h0, h1⟩, by rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]; exact hf⟩

/-- **`uqOf v` is continuous** (on all of `E4`): it is built from the linear map
`q ↦ (q 2, q 3) ↦ invY v` (whose matrix is the explicit inverse of `wOf v`), the skew torus
coordinate `cuspY v` and the inner product with the slope `σ_v`. -/
theorem polarTargetS_continuous_uqOf (v : Fin 5) : Continuous (uqOf v) := by
  unfold uqOf cuspY invY
  fun_prop

/-- **The target of the shifted polar chart is open**: by `polarTargetS_eq` it is the intersection
of the open box `B` with the preimage of the open interval `(k/4,(k+1)/4)` under the continuous map
`q ↦ uqOf v q − c`. -/
theorem isOpen_polarTargetS (v : Fin 5) (c : ℝ) (k : Fin 4) (B : Set E4) (hB : IsOpen B) :
    IsOpen (polarTargetS v c k B) := by
  rw [polarTargetS_eq]
  have hcont : Continuous (fun q : E4 => uqOf v q - c) :=
    (polarTargetS_continuous_uqOf v).sub continuous_const
  exact hB.inter (isOpen_Ioo.preimage hcont)

end Work.Cusp
