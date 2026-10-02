import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.finite_of_cyclicOrderPreserving

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The combinatorial core of `finite_type_of_orderPreserving`

The type `T = {ψ | rayAccum c φ ψ = {y}}` of a point `y` for a Böttcher coordinate `φ` carries the
second-return angle map `σ ψ = Int.fract (4^k ψ) = (angDouble)^[2k] ψ`.  The hypotheses of
`Work.LandLeaves.finite_type_of_orderPreserving` say, in the language of this file:

* `σ` maps `T` into `T` (`hmap`) and onto `K = T ∩ [0,1)` (`hpre`),
* `σ` is injective on `T` modulo `1` (`hinj`),
* `σ` preserves the cyclic betweenness `ccBet` on `T` (`hord`).

This file collects the angle-theoretic consequences of those hypotheses that are needed to prove
finiteness of `K`, in the form of small lemmas.
-/

namespace Work.LandLeaves

open Classical

/-- The second-return angle map, as a map of real angles: `σ ψ = Int.fract (4^k ψ)`. -/
noncomputable def sg (k : ℕ) (ψ : ℝ) : ℝ := Int.fract ((4 : ℝ) ^ k * ψ)

theorem sg_eq (k : ℕ) (ψ : ℝ) : sg k ψ = Int.fract ((4 : ℝ) ^ k * ψ) := rfl

theorem sg_mem_Ico (k : ℕ) (ψ : ℝ) : sg k ψ ∈ Set.Ico 0 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem sg_eq_angDouble {k : ℕ} (hk : 0 < k) (ψ : ℝ) :
    sg k ψ = (Work.Landing.angDouble)^[2 * k] ψ := by
  rw [angDouble_iterate_two_mul hk ψ, sg_eq]

/-- `Int.fract` is insensitive to removing integer parts of the arguments. -/
theorem fract_sub_fract (a b : ℝ) :
    Int.fract (Int.fract a - Int.fract b) = Int.fract (a - b) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊b⌋ - ⌊a⌋, ?_⟩
  have h1 : a - Int.fract a = (⌊a⌋ : ℝ) := Int.self_sub_fract a
  have h2 : b - Int.fract b = (⌊b⌋ : ℝ) := Int.self_sub_fract b
  push_cast
  linarith

/-- `sg k ψ` depends only on `fract ψ`. -/
theorem sg_fract (k : ℕ) (ψ : ℝ) : sg k (Int.fract ψ) = sg k ψ := by
  rw [sg_eq, sg_eq, Int.fract_eq_fract]
  refine ⟨-(((4 : ℤ) ^ k) * ⌊ψ⌋), ?_⟩
  have h : Int.fract ψ - ψ = -(⌊ψ⌋ : ℝ) := by linarith [Int.self_sub_fract ψ]
  push_cast
  linear_combination ((4 : ℝ) ^ k) * h

/-- The difference of two `sg`-values, modulo `1`. -/
theorem sg_sub_eq (k : ℕ) (x y : ℝ) :
    Int.fract (sg k x - sg k y) = Int.fract ((4 : ℝ) ^ k * (x - y)) := by
  rw [sg_eq, sg_eq, fract_sub_fract]
  congr 1
  ring

/-- `sg` on the fractional part of a difference: the "expanding" rewriting. -/
theorem sg_fract_sub (k : ℕ) (x y : ℝ) :
    Int.fract (sg k x - sg k y)
      = Int.fract ((4 : ℝ) ^ k * (Int.fract x - Int.fract y)) := by
  rw [sg_sub_eq, Int.fract_eq_fract]
  refine ⟨((4 : ℤ) ^ k) * (⌊x⌋ - ⌊y⌋), ?_⟩
  have h1 : x - Int.fract x = (⌊x⌋ : ℝ) := Int.self_sub_fract x
  have h2 : y - Int.fract y = (⌊y⌋ : ℝ) := Int.self_sub_fract y
  push_cast
  linear_combination ((4 : ℝ) ^ k) * (h1 - h2)



/-! ## The abstract set-up: an invariant set of angles modulo `1` -/

/-- The `[0,1)`-trace of the type. -/
def traceSet (T : Set ℝ) : Set ℝ := T ∩ Set.Ico 0 1

end Work.LandLeaves
