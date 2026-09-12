import Mathlib

/-! Trigonometry for Section 5 (paper arXiv:1907.09464v1, Observation in §5):

For odd sine frequencies `2r+1`, `r = 0..n-1`, and real `x, y`:

    4·Σ_r sin((2r+1)x)·sin((2r+1)y)
        = sin(2n(x−y))/sin(x−y) − sin(2n(x+y))/sin(x+y)          (pointwise, denominators ≠ 0)
        = sin(2n(x−y))·sin(x+y)/sin(x−y) − ...                    (multiplied-out form)

We provide BOTH the pointwise-with-denominators version and the
denominator-free polynomial identity, which is what survives integration
at points where a denominator vanishes.  Proof: both sides of the
denominator-free identity are equal (by expanding products to sums:
`2 sin a sin b = cos(a−b) − cos(a+b)` and the telescoping identity
`Σ_r 2 sin φ cos((2r+1)φ) = sin(2nφ)`), which is a standard `simp`/
`ring`-style trig proof; you may need `Real.sin_add`, `Real.sin_sub`,
`Real.cos_add`, `Real.cos_sub`, `Real.sin_two_mul`, telescoping via
`Finset.sum_range_sub` or explicit induction on `n`. -/

open scoped BigOperators
namespace Submission
namespace Trig

/-- Telescoping identity `Σ_{r=0}^{n-1} 2 sin φ cos((2r+1)φ) = sin (2n φ)`
   (denominator-free form after multiplying by `sin φ`). -/
lemma telescoping_sum_sin_mul_cos (n : ℕ) (φ : ℝ) :
    Real.sin φ * (∑ r ∈ Finset.range n, 2 * Real.cos ((2 * (r : ℕ) + 1) * φ)) =
      Real.sin ((2 * (n : ℝ)) * φ) := by
  let g : ℕ → ℝ := fun i => Real.sin ((2 * (i : ℝ)) * φ)
  have hg0 : g 0 = 0 := by
    simp [g]
  have hterm : ∀ r : ℕ,
      2 * Real.sin φ * Real.cos ((2 * (r : ℕ) + 1) * φ) = g (r + 1) - g r := by
    intro r
    unfold g
    rw [Real.sin_sub_sin]
    rw [show ((2 * ((r + 1 : ℕ) : ℝ) * φ - 2 * (r : ℝ) * φ) / 2) = φ by
      push_cast; ring_nf]
    rw [show ((2 * ((r + 1 : ℕ) : ℝ) * φ + 2 * (r : ℝ) * φ) / 2) = (2 * (r : ℝ) + 1) * φ by
      push_cast; ring_nf]
  calc
    Real.sin φ * (∑ r ∈ Finset.range n, 2 * Real.cos ((2 * (r : ℕ) + 1) * φ))
        = ∑ r ∈ Finset.range n, (2 * Real.sin φ * Real.cos ((2 * (r : ℕ) + 1) * φ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = ∑ r ∈ Finset.range n, (g (r + 1) - g r) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hterm r
    _ = g n - g 0 := by
          rw [Finset.sum_range_sub]
    _ = Real.sin ((2 * (n : ℝ)) * φ) := by
          rw [hg0]
          simp [g]

/-- Variant of `telescoping_sum_sin_mul_cos` in which the odd frequency
   `2r+1` is written as a natural number before multiplying by `φ`
   (this is the shape that appears in `odd_sine_kernel_mul`). -/
private lemma telescoping_sum_sin_mul_cos_cos (n : ℕ) (φ : ℝ) :
    Real.sin φ * (∑ r ∈ Finset.range n, 2 * Real.cos (((2 * (r : ℕ) + 1) : ℕ) * φ)) =
      Real.sin ((2 * (n : ℝ)) * φ) := by
  rw [← telescoping_sum_sin_mul_cos n φ]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  push_cast
  ring_nf

/-- Product-to-sum identity `2 sin u sin v = cos(u−v) − cos(u+v)`. -/
private lemma two_sin_mul_sin (u v : ℝ) :
    2 * Real.sin u * Real.sin v = Real.cos (u - v) - Real.cos (u + v) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- Denominator-free trig identity for the odd-sine Dirichlet kernel:

`4·(Σ_r sin((2r+1)x) sin((2r+1)y)) · sin(x−y) · sin(x+y)
   = sin(2n(x−y))·sin(x+y) − sin(2n(x+y))·sin(x−y)`. -/
lemma odd_sine_kernel_mul (n : ℕ) (x y : ℝ) :
    4 * (∑ r ∈ Finset.range n, Real.sin (((2 * (r : ℕ) + 1) : ℕ) * x) *
        Real.sin (((2 * (r : ℕ) + 1) : ℕ) * y)) * Real.sin (x - y) * Real.sin (x + y) =
      Real.sin ((2 * (n : ℝ)) * (x - y)) * Real.sin (x + y) -
        Real.sin ((2 * (n : ℝ)) * (x + y)) * Real.sin (x - y) := by
  let A : ℕ → ℝ := fun r => Real.sin (((2 * (r : ℕ) + 1) : ℕ) * x)
  let B : ℕ → ℝ := fun r => Real.sin (((2 * (r : ℕ) + 1) : ℕ) * y)
  let cA : ℕ → ℝ := fun r => Real.cos (((2 * (r : ℕ) + 1) : ℕ) * (x - y))
  let cB : ℕ → ℝ := fun r => Real.cos (((2 * (r : ℕ) + 1) : ℕ) * (x + y))
  let s : ℝ := Real.sin (x - y)
  let t : ℝ := Real.sin (x + y)
  change 4 * (∑ r ∈ Finset.range n, A r * B r) * s * t =
    Real.sin ((2 * (n : ℝ)) * (x - y)) * t -
      Real.sin ((2 * (n : ℝ)) * (x + y)) * s
  have hpush : 4 * (∑ r ∈ Finset.range n, A r * B r) * s * t =
      ∑ r ∈ Finset.range n, (4 * (A r * B r) * s * t) := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  have harg1 : ∀ r : ℕ,
      (((2 * (r : ℕ) + 1) : ℕ) * x - ((2 * (r : ℕ) + 1) : ℕ) * y) =
        ((2 * (r : ℕ) + 1) : ℕ) * (x - y) := by
    intro r
    push_cast
    ring
  have harg2 : ∀ r : ℕ,
      (((2 * (r : ℕ) + 1) : ℕ) * x + ((2 * (r : ℕ) + 1) : ℕ) * y) =
        ((2 * (r : ℕ) + 1) : ℕ) * (x + y) := by
    intro r
    push_cast
    ring
  have hab : ∀ r : ℕ, 2 * (A r * B r) = cA r - cB r := by
    intro r
    have hu := two_sin_mul_sin (((2 * (r : ℕ) + 1) : ℕ) * x) (((2 * (r : ℕ) + 1) : ℕ) * y)
    calc
      2 * (A r * B r)
          = 2 * Real.sin (((2 * (r : ℕ) + 1) : ℕ) * x) *
              Real.sin (((2 * (r : ℕ) + 1) : ℕ) * y) := by
            dsimp [A, B]
            ring
      _ = Real.cos (((2 * (r : ℕ) + 1) : ℕ) * x - ((2 * (r : ℕ) + 1) : ℕ) * y) -
          Real.cos (((2 * (r : ℕ) + 1) : ℕ) * x + ((2 * (r : ℕ) + 1) : ℕ) * y) := by
            rw [hu]
      _ = cA r - cB r := by
            dsimp [cA, cB]
            rw [harg1 r, harg2 r]
  have hterm : ∀ r : ℕ,
      4 * (A r * B r) * s * t = t * (s * (2 * cA r)) - s * (t * (2 * cB r)) := by
    intro r
    calc
      4 * (A r * B r) * s * t = 2 * s * t * (2 * (A r * B r)) := by ring
      _ = 2 * s * t * (cA r - cB r) := by rw [hab r]
      _ = t * (s * (2 * cA r)) - s * (t * (2 * cB r)) := by ring
  have hpull1 : (∑ r ∈ Finset.range n, t * (s * (2 * cA r))) =
      t * (∑ r ∈ Finset.range n, s * (2 * cA r)) := by
    rw [← Finset.mul_sum]
  have hpull2 : (∑ r ∈ Finset.range n, s * (t * (2 * cB r))) =
      s * (∑ r ∈ Finset.range n, t * (2 * cB r)) := by
    rw [← Finset.mul_sum]
  have hpull3 : (∑ r ∈ Finset.range n, s * (2 * cA r)) =
      s * (∑ r ∈ Finset.range n, 2 * cA r) := by
    rw [← Finset.mul_sum]
  have hpull4 : (∑ r ∈ Finset.range n, t * (2 * cB r)) =
      t * (∑ r ∈ Finset.range n, 2 * cB r) := by
    rw [← Finset.mul_sum]
  calc
    4 * (∑ r ∈ Finset.range n, A r * B r) * s * t
        = ∑ r ∈ Finset.range n, (4 * (A r * B r) * s * t) := hpush
    _ = ∑ r ∈ Finset.range n, (t * (s * (2 * cA r)) - s * (t * (2 * cB r))) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hterm r
    _ = (∑ r ∈ Finset.range n, t * (s * (2 * cA r))) -
        (∑ r ∈ Finset.range n, s * (t * (2 * cB r))) := by
          rw [Finset.sum_sub_distrib]
    _ = t * (∑ r ∈ Finset.range n, s * (2 * cA r)) -
        s * (∑ r ∈ Finset.range n, t * (2 * cB r)) := by
          rw [hpull1, hpull2]
    _ = t * (s * (∑ r ∈ Finset.range n, 2 * cA r)) -
        s * (t * (∑ r ∈ Finset.range n, 2 * cB r)) := by
          rw [hpull3, hpull4]
    _ = t * Real.sin ((2 * (n : ℝ)) * (x - y)) - s * Real.sin ((2 * (n : ℝ)) * (x + y)) := by
          rw [telescoping_sum_sin_mul_cos_cos n (x - y),
              telescoping_sum_sin_mul_cos_cos n (x + y)]
    _ = Real.sin ((2 * (n : ℝ)) * (x - y)) * t -
        Real.sin ((2 * (n : ℝ)) * (x + y)) * s := by ring
    _ = Real.sin ((2 * (n : ℝ)) * (x - y)) * Real.sin (x + y) -
        Real.sin ((2 * (n : ℝ)) * (x + y)) * Real.sin (x - y) := by
          dsimp [s, t]

/-- Pointwise version with nonzero denominators. -/
lemma odd_sine_kernel (n : ℕ) (x y : ℝ) (h1 : Real.sin (x - y) ≠ 0) (h2 : Real.sin (x + y) ≠ 0) :
    4 * (∑ r ∈ Finset.range n, Real.sin (((2 * (r : ℕ) + 1) : ℕ) * x) *
        Real.sin (((2 * (r : ℕ) + 1) : ℕ) * y)) =
      Real.sin ((2 * (n : ℝ)) * (x - y)) / Real.sin (x - y) -
        Real.sin ((2 * (n : ℝ)) * (x + y)) / Real.sin (x + y) := by
  set A : ℝ := 4 * (∑ r ∈ Finset.range n, Real.sin (((2 * (r : ℕ) + 1) : ℕ) * x) *
      Real.sin (((2 * (r : ℕ) + 1) : ℕ) * y)) with hA
  calc
    4 * (∑ r ∈ Finset.range n, Real.sin (((2 * (r : ℕ) + 1) : ℕ) * x) *
        Real.sin (((2 * (r : ℕ) + 1) : ℕ) * y)) = A := by
          rw [hA]
    _ = (A * Real.sin (x - y) * Real.sin (x + y)) /
          (Real.sin (x - y) * Real.sin (x + y)) := by
          field_simp [h1, h2]
    _ = (Real.sin ((2 * (n : ℝ)) * (x - y)) * Real.sin (x + y) -
          Real.sin ((2 * (n : ℝ)) * (x + y)) * Real.sin (x - y)) /
            (Real.sin (x - y) * Real.sin (x + y)) := by
          rw [hA, odd_sine_kernel_mul]
    _ = Real.sin ((2 * (n : ℝ)) * (x - y)) / Real.sin (x - y) -
          Real.sin ((2 * (n : ℝ)) * (x + y)) / Real.sin (x + y) := by
          field_simp [h1, h2]

/-- `sin` at a shifted argument, for later rewriting. -/
lemma sin_add_pi_div_two_mul (n : ℕ) (x : ℝ) :
    Real.sin (2 * (n : ℝ) * (x + Real.pi / (2 * (n : ℝ)))) = -Real.sin (2 * (n : ℝ) * x) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have h2n : (2 * (n : ℝ)) ≠ 0 := by nlinarith
    have harg : 2 * (n : ℝ) * (x + Real.pi / (2 * (n : ℝ))) =
        (2 * (n : ℝ)) * x + Real.pi := by
      rw [mul_add]
      rw [mul_div_cancel₀ Real.pi h2n]
    rw [harg]
    rw [Real.sin_add_pi]

/-- Symmetries of the odd-sine functions: `sin(j(π − x)) = sin(jx)` for odd `j`. -/
lemma sin_odd_mul_pi_sub (j : ℕ) (hj : Odd j) (x : ℝ) :
    Real.sin ((j : ℝ) * (Real.pi - x)) = Real.sin ((j : ℝ) * x) := by
  rw [mul_sub, Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, hj.neg_one_pow]
  ring

/-- `sin(j(π + x)) = -sin(jx)` for odd `j`. -/
lemma sin_odd_mul_pi_add (j : ℕ) (hj : Odd j) (x : ℝ) :
    Real.sin ((j : ℝ) * (Real.pi + x)) = -Real.sin ((j : ℝ) * x) := by
  rw [mul_add, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, hj.neg_one_pow]
  ring

/-- `sin` is `2π`-periodic: `sin(j(x + 2π)) = sin(jx)`. -/
lemma sin_odd_add_two_pi (j : ℕ) (x : ℝ) :
    Real.sin ((j : ℝ) * (x + 2 * Real.pi)) = Real.sin ((j : ℝ) * x) := by
  rw [mul_add]
  exact Real.sin_periodic.nat_mul j ((j : ℝ) * x)

end Trig
end Submission
