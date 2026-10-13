/-
# The order-`5` angular slot bound for the profile `θ ↦ -sin²θ`

This file proves `SinSqSlot5`: the fifth `D_θ`-iterate of the angular profile
`a(θ) = -sin²θ` (extended to `(z,θ)` by ignoring `z`) is bounded by a constant times
`sin(2θ)` on `Iθ`.  It is the order-`5` companion of
`Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq`, which treats the orders `1 ≤ i ≤ 4`
with the constant `192`.

## Route

Because the profile does not depend on `z`,
`DthIter i a 0 θ = (Lop^[i] G) θ` where `G θ = -sin²θ` and
`Lop u θ = sin(2θ)·u'(θ)` (`Work.Spaces.DthIter_eq_iterate_Lop`).  Writing `s = sin 2θ` and
`c = cos 2θ`, a direct computation gives

```
Lop G            = -s²
Lop(-s²)         = -4 s² c
Lop(-4 s² c)     = -16 s²c² + 8 s⁴
Lop(…)           = -64 s²c³ + 128 s⁴c
Lop(-64 s²c³ + 128 s⁴c) = -256 s²c⁴ + 1408 s⁴c² - 256 s⁶.
```

On `Iθ` we have `0 ≤ s ≤ 1` and `|c| ≤ 1`, so every monomial `C s^a c^b` with `a ≥ 1`
satisfies `|C s^a c^b| ≤ |C|·s`; summing the three coefficients
`256 + 1408 + 256 = 1920` gives the bound `|Lop^[5] G θ| ≤ 1920·sin(2θ)`.

Everything is `sorry`-free and uses only `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## The profile and its `Lop`-iterates -/

/-- The angular profile `θ ↦ -sin²θ`, as a function of one variable. -/
private def G : ℝ → ℝ := fun θ => -((Real.sin θ) ^ 2)

/-- The first iterate `Lop G = -sin²(2θ)`. -/
private def L1 : ℝ → ℝ := fun θ => -((Real.sin (2 * θ)) ^ 2)

/-- The second iterate `-4 sin²(2θ) cos(2θ)`. -/
private def L2 : ℝ → ℝ := fun θ => -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)

/-- The third iterate `-16 sin²(2θ) cos²(2θ) + 8 sin⁴(2θ)`. -/
private def L3 : ℝ → ℝ :=
  fun θ => -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
    + 8 * (Real.sin (2 * θ)) ^ 4

/-- The fourth iterate `-64 sin²(2θ) cos³(2θ) + 128 sin⁴(2θ) cos(2θ)`. -/
private def L4 : ℝ → ℝ :=
  fun θ => -64 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
    + 128 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)

/-- The fifth iterate `-256 sin²(2θ) cos⁴(2θ) + 1408 sin⁴(2θ) cos²(2θ) - 256 sin⁶(2θ)`. -/
private def L5 : ℝ → ℝ :=
  fun θ => -256 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4
    + 1408 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
    - 256 * (Real.sin (2 * θ)) ^ 6

/-! ## Elementary facts about `Iθ` -/

/-- On `Iθ` the number `sin(2θ)` lies in `[0,1]`. -/
private lemma sin_two_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 := by
  have h0 : 0 ≤ θ := hθ.1
  have h1 : θ ≤ Real.pi / 2 := hθ.2
  have h2 : 0 ≤ 2 * θ := by linarith
  have h3 : 2 * θ ≤ Real.pi := by linarith [Real.pi_pos]
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi h2 h3, Real.sin_le_one _⟩

/-- The monomial bound with a constant factor, in the shape `(C s^a) c^b`:
for `0 ≤ s ≤ 1`, `|c| ≤ 1` and `a ≥ 1`, `|(C s^a) c^b| ≤ |C| s`. -/
private lemma const_mono_le {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : |c| ≤ 1)
    (C : ℝ) {a b : ℕ} (ha : 1 ≤ a) : |(C * s ^ a) * c ^ b| ≤ |C| * s := by
  have hcb : |c| ^ b ≤ 1 := pow_le_one₀ (abs_nonneg c) hc
  have hsa : s ^ a ≤ s := by simpa using pow_le_pow_of_le_one hs0 hs1 ha
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs0 a), abs_pow]
  calc (|C| * s ^ a) * |c| ^ b ≤ (|C| * s ^ a) * 1 :=
        mul_le_mul_of_nonneg_left hcb (mul_nonneg (abs_nonneg C) (pow_nonneg hs0 a))
    _ = |C| * s ^ a := by ring
    _ ≤ |C| * s := mul_le_mul_of_nonneg_left hsa (abs_nonneg C)

/-! ## Derivatives of the iterates -/

/-- `d/dθ sin(2θ) = 2cos(2θ)`. -/
private lemma hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ := by
  have hlin : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  simpa using hlin.sin

/-- `d/dθ cos(2θ) = -2sin(2θ)`. -/
private lemma hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-Real.sin (2 * θ) * 2) θ := by
  have hlin : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  simpa using hlin.cos

/-- `deriv G θ = -sin(2θ)`. -/
private lemma deriv_G (θ : ℝ) : deriv G θ = -(Real.sin (2 * θ)) := by
  have hsin : HasDerivAt (fun θ : ℝ => Real.sin θ) (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have h : HasDerivAt (fun θ : ℝ => Real.sin θ * Real.sin θ)
      (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ) θ := hsin.mul hsin
  have h2 : HasDerivAt G (-(Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ)) θ := by
    convert h.neg using 1 <;> (try funext x) <;>
      (try simp only [G, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, pow_two]) <;>
      (first | ring | ring_nf)
  rw [h2.deriv, Real.sin_two_mul]
  ring

/-- `deriv (-sin²(2θ)) = -4 sin(2θ) cos(2θ)`, in raw form. -/
private lemma deriv_L1 (θ : ℝ) :
    deriv (fun θ : ℝ => -((Real.sin (2 * θ)) ^ 2)) θ
      = -((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
          + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2)) := by
  have hS := hasDerivAt_sin_two θ
  have h : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) * Real.sin (2 * θ))
      ((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
        + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2)) θ := hS.mul hS
  have h2 : HasDerivAt (fun θ : ℝ => -((Real.sin (2 * θ)) ^ 2))
      (-((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
          + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2))) θ := by
    convert h.neg using 1 <;> (try funext x) <;>
      (try simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply, pow_two]) <;>
      (first | ring | ring_nf)
  rw [h2.deriv]

/-- `deriv (-4 sin²(2θ) cos(2θ)) = -16 sin(2θ) cos²(2θ) + 8 sin³(2θ)`. -/
private lemma deriv_L2 (θ : ℝ) :
    deriv (fun θ : ℝ => -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)) θ
      = -16 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 3 := by
  have hS := hasDerivAt_sin_two θ
  have hC := hasDerivAt_cos_two θ
  have hSS : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) * Real.sin (2 * θ))
      ((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
        + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2)) θ := hS.mul hS
  have hSSC := hSS.mul hC
  have h4 := hSSC.const_mul (-4)
  have h5 : HasDerivAt (fun θ : ℝ => -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ))
      (-16 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 3) θ := by
    convert h4 using 1 <;> (try funext x) <;>
      (try simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply, pow_two]) <;>
      (first | ring | ring_nf)
  rw [h5.deriv]

/-- `deriv (-16 sin²(2θ) cos²(2θ) + 8 sin⁴(2θ)) = -64 sin(2θ) cos³(2θ) + 128 sin³(2θ) cos(2θ)`. -/
private lemma deriv_L3 (θ : ℝ) :
    deriv (fun θ : ℝ => -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 4) θ
      = -64 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 3
        + 128 * (Real.sin (2 * θ)) ^ 3 * Real.cos (2 * θ) := by
  have hS := hasDerivAt_sin_two θ
  have hC := hasDerivAt_cos_two θ
  have hSS : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) * Real.sin (2 * θ))
      ((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
        + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2)) θ := hS.mul hS
  have hCC : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ) * Real.cos (2 * θ))
      ((-Real.sin (2 * θ) * 2) * Real.cos (2 * θ)
        + Real.cos (2 * θ) * (-Real.sin (2 * θ) * 2)) θ := hC.mul hC
  have hA := (hSS.mul hCC).const_mul (-16)
  have hB := (hSS.mul hSS).const_mul 8
  have hsum := hA.add hB
  have h5 : HasDerivAt (fun θ : ℝ => -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 4)
      (-64 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 3
        + 128 * (Real.sin (2 * θ)) ^ 3 * Real.cos (2 * θ)) θ := by
    convert hsum using 1 <;> (try funext x) <;>
      (try simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply, pow_two]) <;>
      (first | ring | ring_nf)
  rw [h5.deriv]

/-- `deriv (-64 sin²(2θ)cos³(2θ) + 128 sin⁴(2θ)cos(2θ))`
` = -256 sin(2θ)cos⁴(2θ) + 1408 sin³(2θ)cos²(2θ) - 256 sin⁵(2θ)`. -/
private lemma deriv_L4 (θ : ℝ) :
    deriv (fun θ : ℝ => -64 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
        + 128 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)) θ
      = -256 * (Real.sin (2 * θ)) * (Real.cos (2 * θ)) ^ 4
        + 1408 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 2
        - 256 * (Real.sin (2 * θ)) ^ 5 := by
  have hS := hasDerivAt_sin_two θ
  have hC := hasDerivAt_cos_two θ
  have hS2 : HasDerivAt (fun x : ℝ => (Real.sin (2 * x)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := by
    have h := hS.pow 2
    convert h using 1 <;> (try funext x) <;> (try simp only [Pi.pow_apply]) <;> ring
  have hC3 : HasDerivAt (fun x : ℝ => (Real.cos (2 * x)) ^ 3)
      (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2)) θ := by
    have h := hC.pow 3
    convert h using 1 <;> (try funext x) <;> (try simp only [Pi.pow_apply]) <;> ring
  have hS4 : HasDerivAt (fun x : ℝ => (Real.sin (2 * x)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := by
    have h := hS.pow 4
    convert h using 1 <;> (try funext x) <;> (try simp only [Pi.pow_apply]) <;> ring
  have hA : HasDerivAt (fun x : ℝ => -64 * (Real.sin (2 * x)) ^ 2 * (Real.cos (2 * x)) ^ 3)
      (-64 * ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))
          * (Real.cos (2 * θ)) ^ 3
        + (Real.sin (2 * θ)) ^ 2
          * (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2)))) θ := by
    have h := (hS2.mul hC3).const_mul (-64)
    convert h using 1 <;> (try funext x) <;>
      (try simp only [Pi.mul_apply, Pi.pow_apply]) <;> ring
  have hB : HasDerivAt (fun x : ℝ => 128 * (Real.sin (2 * x)) ^ 4 * Real.cos (2 * x))
      (128 * ((4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) * Real.cos (2 * θ)
        + (Real.sin (2 * θ)) ^ 4 * (-Real.sin (2 * θ) * 2))) θ := by
    have h := (hS4.mul hC).const_mul (128 : ℝ)
    convert h using 1 <;> (try funext x) <;>
      (try simp only [Pi.mul_apply, Pi.pow_apply]) <;> ring
  have hsum := hA.add hB
  rw [show (fun x : ℝ => -64 * (Real.sin (2 * x)) ^ 2 * (Real.cos (2 * x)) ^ 3
        + 128 * (Real.sin (2 * x)) ^ 4 * Real.cos (2 * x))
      = (fun x : ℝ => -64 * (Real.sin (2 * x)) ^ 2 * (Real.cos (2 * x)) ^ 3)
        + (fun x : ℝ => 128 * (Real.sin (2 * x)) ^ 4 * Real.cos (2 * x)) from rfl]
  rw [hsum.deriv]
  ring

/-! ## The iterate identities -/

/-- `Lop G = -sin²(2θ)`. -/
private lemma Lop_G : Work.Spaces.Lop G = L1 := by
  funext θ
  show Real.sin (2 * θ) * deriv G θ = -((Real.sin (2 * θ)) ^ 2)
  rw [deriv_G θ]
  ring

/-- `Lop (-sin²(2θ)) = -4 sin²(2θ) cos(2θ)`. -/
private lemma Lop_L1 : Work.Spaces.Lop L1 = L2 := by
  funext θ
  show Real.sin (2 * θ) * deriv (fun θ : ℝ => -((Real.sin (2 * θ)) ^ 2)) θ
      = -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)
  rw [deriv_L1 θ]
  ring

/-- `Lop (-4 sin²(2θ) cos(2θ)) = -16 sin²(2θ) cos²(2θ) + 8 sin⁴(2θ)`. -/
private lemma Lop_L2 : Work.Spaces.Lop L2 = L3 := by
  funext θ
  show Real.sin (2 * θ) * deriv (fun θ : ℝ => -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)) θ
      = -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2 + 8 * (Real.sin (2 * θ)) ^ 4
  rw [deriv_L2 θ]
  ring

/-- `Lop (-16 sin²(2θ) cos²(2θ) + 8 sin⁴(2θ)) = -64 sin²(2θ) cos³(2θ) + 128 sin⁴(2θ) cos(2θ)`. -/
private lemma Lop_L3 : Work.Spaces.Lop L3 = L4 := by
  funext θ
  show Real.sin (2 * θ) * deriv (fun θ : ℝ => -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 4) θ
      = -64 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
        + 128 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
  rw [deriv_L3 θ]
  ring

/-- `Lop (-64 sin²(2θ) cos³(2θ) + 128 sin⁴(2θ) cos(2θ))`
` = -256 sin²(2θ) cos⁴(2θ) + 1408 sin⁴(2θ) cos²(2θ) - 256 sin⁶(2θ)`. -/
private lemma Lop_L4 : Work.Spaces.Lop L4 = L5 := by
  funext θ
  show Real.sin (2 * θ) * deriv (fun θ : ℝ => -64 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
        + 128 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)) θ
      = -256 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4
        + 1408 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 256 * (Real.sin (2 * θ)) ^ 6
  rw [deriv_L4 θ]
  ring

/-- The first iterate of `Lop` on `G`. -/
private lemma iter_one : Work.Spaces.Lop^[1] G = L1 := by
  rw [Function.iterate_one]
  exact Lop_G

/-- The second iterate of `Lop` on `G`. -/
private lemma iter_two : Work.Spaces.Lop^[2] G = L2 := by
  have h : Work.Spaces.Lop^[2] G = Work.Spaces.Lop (Work.Spaces.Lop^[1] G) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply']
  rw [h, iter_one, Lop_L1]

/-- The third iterate of `Lop` on `G`. -/
private lemma iter_three : Work.Spaces.Lop^[3] G = L3 := by
  have h : Work.Spaces.Lop^[3] G = Work.Spaces.Lop (Work.Spaces.Lop^[2] G) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply']
  rw [h, iter_two, Lop_L2]

/-- The fourth iterate of `Lop` on `G`. -/
private lemma iter_four : Work.Spaces.Lop^[4] G = L4 := by
  have h : Work.Spaces.Lop^[4] G = Work.Spaces.Lop (Work.Spaces.Lop^[3] G) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply']
  rw [h, iter_three, Lop_L3]

/-- The fifth iterate of `Lop` on `G`. -/
private lemma iter_five : Work.Spaces.Lop^[5] G = L5 := by
  have h : Work.Spaces.Lop^[5] G = Work.Spaces.Lop (Work.Spaces.Lop^[4] G) := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply']
  rw [h, iter_four, Lop_L4]

/-! ## The order-`5` bound on `Iθ` -/

/-- `|a + b - c| ≤ |a| + |b| + |c|`. -/
private lemma abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b - c| ≤ |a + b| + |c| := by
    have h := abs_add_le (a + b) (-c)
    rw [abs_neg] at h
    rw [sub_eq_add_neg]
    exact h
  have h2 : |a + b| ≤ |a| + |b| := abs_add_le a b
  linarith

/-- `|L5 θ| ≤ 1920 sin(2θ)` on `Iθ`. -/
private lemma bound_L5 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |L5 θ| ≤ 1920 * Real.sin (2 * θ) := by
  obtain ⟨hs0, hs1⟩ := sin_two_mem hθ
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hA : |((-256 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 4|
      ≤ 256 * Real.sin (2 * θ) := by
    have hthis := const_mono_le hs0 hs1 hc (-256) (a := 2) (b := 4) (by norm_num)
    have hc256 : |-256| = (256 : ℝ) := by
      rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 256)]
    rwa [hc256] at hthis
  have hB : |((1408 : ℝ) * (Real.sin (2 * θ)) ^ 4) * (Real.cos (2 * θ)) ^ 2|
      ≤ 1408 * Real.sin (2 * θ) := by
    have hthis := const_mono_le hs0 hs1 hc (1408) (a := 4) (b := 2) (by norm_num)
    have hc1408 : |(1408 : ℝ)| = 1408 := by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1408)]
    rwa [hc1408] at hthis
  have hC : |((256 : ℝ) * (Real.sin (2 * θ)) ^ 6) * (Real.cos (2 * θ)) ^ 0|
      ≤ 256 * Real.sin (2 * θ) := by
    have hthis := const_mono_le hs0 hs1 hc (256) (a := 6) (b := 0) (by norm_num)
    have hc256 : |(256 : ℝ)| = 256 := by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 256)]
    rwa [hc256] at hthis
  have heq : L5 θ = ((-256 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 4
      + ((1408 : ℝ) * (Real.sin (2 * θ)) ^ 4) * (Real.cos (2 * θ)) ^ 2
      - ((256 : ℝ) * (Real.sin (2 * θ)) ^ 6) * (Real.cos (2 * θ)) ^ 0 := by
    simp only [L5]
    ring
  rw [heq]
  calc |((-256 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 4
        + ((1408 : ℝ) * (Real.sin (2 * θ)) ^ 4) * (Real.cos (2 * θ)) ^ 2
        - ((256 : ℝ) * (Real.sin (2 * θ)) ^ 6) * (Real.cos (2 * θ)) ^ 0|
      ≤ |((-256 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 4|
        + |((1408 : ℝ) * (Real.sin (2 * θ)) ^ 4) * (Real.cos (2 * θ)) ^ 2|
        + |((256 : ℝ) * (Real.sin (2 * θ)) ^ 6) * (Real.cos (2 * θ)) ^ 0| :=
        abs_add_sub_le _ _ _
    _ ≤ 256 * Real.sin (2 * θ) + 1408 * Real.sin (2 * θ) + 256 * Real.sin (2 * θ) := by
        linarith [hA, hB, hC]
    _ = 1920 * Real.sin (2 * θ) := by ring

/-! ## The target -/

theorem SinSqSlot5 : ∃ B : ℝ, 0 < B ∧ ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.DthIter 5 (fun _ (θ' : ℝ) => -(Real.sin θ') ^ 2) 0 θ| ≤ B * Real.sin (2 * θ) := by
  refine ⟨1920, by norm_num, ?_⟩
  intro θ hθ
  have hit : Work.Spaces.DthIter 5 (fun _ (θ' : ℝ) => -((Real.sin θ') ^ 2)) 0 θ
      = Work.Spaces.Lop^[5] G θ := by
    have hf : (fun θ : ℝ => (fun _ (θ' : ℝ) => -((Real.sin θ') ^ 2)) 0 θ) = G := by
      funext x
      rfl
    rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop 5
      (fun _ (θ' : ℝ) => -((Real.sin θ') ^ 2)) 0) θ, hf]
  rw [hit, iter_five]
  exact bound_L5 hθ

end Work.FTS.StrongEps.H5.Atoms
