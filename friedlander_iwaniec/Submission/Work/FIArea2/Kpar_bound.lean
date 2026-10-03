import Mathlib
import Submission.Work.FIArea2.CCountPoissonDefs

set_option autoImplicit false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The elementary content of `Kpar_bound`**: if `w` lies in the box `boxM Pa` and `c² = Re(wz)`
for some `z ∈ {z₁,z₂}`, then `|c| ≤ Kpar Pa z₁ z₂`.

Indeed `c² = Re(wz) = w.re·z.re − w.im·z.im ≤ |w.re|·|z.re| + |w.im|·|z.im|
≤ radM(Pa)·(|z.re| + |z.im|)` by box membership, and `|z.re| + |z.im|` is at most the radicand's
sum `|z₁.re| + |z₁.im| + |z₂.re| + |z₂.im| + 1`.  Taking square roots and using
`Kpar Pa z₁ z₂ = ⌈√(radM(Pa)·(…))⌉₊ ≥ √(radM(Pa)·(…))` gives the claim. -/
private lemma abs_le_Kpar_of_cForm_sq (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    {w : GaussianInt} (hw : w ∈ Work.FITop.boxM Pa) {c : ℤ} {z : GaussianInt}
    (hz : z = z1 ∨ z = z2) (h : Work.FIPlan.cForm w z = c * c) :
    |c| ≤ (Kpar Pa z1 z2 : ℤ) := by
  -- the box radius is nonnegative (it is a natural number cast to `ℤ`)
  have hRnn : (0 : ℝ) ≤ (Work.FITop.radM Pa : ℝ) := by
    rw [Work.FITop.radM]; positivity
  -- the single-variable radicand is dominated by the two-variable one
  have hS : |(z.re : ℝ)| + |(z.im : ℝ)|
      ≤ |(z1.re : ℝ)| + |(z1.im : ℝ)| + |(z2.re : ℝ)| + |(z2.im : ℝ)| + 1 := by
    rcases hz with rfl | rfl
    · have h0 : (0 : ℝ) ≤ |(z2.re : ℝ)| + |(z2.im : ℝ)| := by positivity
      linarith
    · have h0 : (0 : ℝ) ≤ |(z1.re : ℝ)| + |(z1.im : ℝ)| := by positivity
      linarith
  have hbase : (Work.FIPlan.cForm w z : ℝ)
      ≤ (Work.FITop.radM Pa : ℝ) * (|(z.re : ℝ)| + |(z.im : ℝ)|) :=
    cForm_le_of_mem_gBox (z := z) (R := Work.FITop.radM Pa) hw
  have hstep : (Work.FIPlan.cForm w z : ℝ)
      ≤ (Work.FITop.radM Pa : ℝ)
        * (|(z1.re : ℝ)| + |(z1.im : ℝ)| + |(z2.re : ℝ)| + |(z2.im : ℝ)| + 1) :=
    le_trans hbase (mul_le_mul_of_nonneg_left hS hRnn)
  -- `c²` is that same real number
  have hc : (c : ℝ) ^ 2 = (Work.FIPlan.cForm w z : ℝ) := by
    rw [h]; push_cast; ring
  have hsq : (c : ℝ) ^ 2
      ≤ (Work.FITop.radM Pa : ℝ)
        * (|(z1.re : ℝ)| + |(z1.im : ℝ)| + |(z2.re : ℝ)| + |(z2.im : ℝ)| + 1) := by
    rw [hc]; exact hstep
  -- take square roots
  have hsqrt : |(c : ℝ)| ≤ Real.sqrt ((Work.FITop.radM Pa : ℝ)
      * (|(z1.re : ℝ)| + |(z1.im : ℝ)| + |(z2.re : ℝ)| + |(z2.im : ℝ)| + 1)) := by
    rw [← Real.sqrt_sq_eq_abs (c : ℝ)]
    exact Real.sqrt_le_sqrt hsq
  -- and compare with the ceiling defining `Kpar`
  have hceil : Real.sqrt ((Work.FITop.radM Pa : ℝ)
      * (|(z1.re : ℝ)| + |(z1.im : ℝ)| + |(z2.re : ℝ)| + |(z2.im : ℝ)| + 1))
      ≤ (Kpar Pa z1 z2 : ℝ) := by
    rw [Kpar]
    exact Nat.le_ceil _
  have hfinal : ((|c| : ℤ) : ℝ) ≤ ((Kpar Pa z1 z2 : ℤ) : ℝ) := by
    rw [Int.cast_abs]
    exact le_trans hsqrt hceil
  exact_mod_cast hfinal

theorem Kpar_bound (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) {w : GaussianInt}
    (hw : w ∈ Work.FITop.boxM Pa) {c1 c2 : ℤ}
    (h1 : Work.FIPlan.cForm w z1 = c1 * c1) (h2 : Work.FIPlan.cForm w z2 = c2 * c2) :
    -(Work.FIArea2.Kpar Pa z1 z2 : ℤ) ≤ c1 ∧ c1 ≤ (Work.FIArea2.Kpar Pa z1 z2 : ℤ) ∧
      -(Work.FIArea2.Kpar Pa z1 z2 : ℤ) ≤ c2 ∧ c2 ≤ (Work.FIArea2.Kpar Pa z1 z2 : ℤ) := by
  have h1' : |c1| ≤ (Kpar Pa z1 z2 : ℤ) :=
    abs_le_Kpar_of_cForm_sq Pa z1 z2 hw (z := z1) (Or.inl rfl) h1
  have h2' : |c2| ≤ (Kpar Pa z1 z2 : ℤ) :=
    abs_le_Kpar_of_cForm_sq Pa z1 z2 hw (z := z2) (Or.inr rfl) h2
  exact ⟨(abs_le.mp h1').1, (abs_le.mp h1').2, (abs_le.mp h2').1, (abs_le.mp h2').2⟩

end

end Work.FIArea2
