import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The Minkowski pairing along a geodesic segment of the hyperboloid

`Work.Mostow.mink` is the Minkowski form `⟨x,y⟩ = Σ xᵢyᵢ − x₀y₀` on `ℝ^{Fin n ⊕ Fin 1}`.
For two points `P`, `Q` of the upper sheet (`⟨P,P⟩ = ⟨Q,Q⟩ = -1`, `⟨P,Q⟩ = -cosh d`), the point

  `(sinh d)⁻¹ • (sinh ((1-s) d) • P + sinh (s d) • Q)`

is the point at parameter `s` of the geodesic from `P` to `Q`.  The lemma `minkGeoSeg` computes the
pairing of the points at parameters `s` and `t` as `-cosh ((s-t) d)`.

The proof is a direct bilinear-algebra computation: expand `mink` by bilinearity, substitute the
three pairings, and reduce the remaining hyperbolic identity to `cosh² - sinh² = 1`.

## Main results

* `minkSeg_*`: bilinearity of `mink` (additivity, homogeneity, symmetry);
* `sinhSeg_one_sub`, `segGram`: the pure hyperbolic identities;
* `minkGeoSeg`: the pairing along the segment.
-/

namespace Work.Mostow

variable {n : ℕ}

/-! ## Bilinearity of the Minkowski form -/

lemma minkSeg_comm (x y : Fin n ⊕ Fin 1 → ℝ) : mink x y = mink y x := by
  rw [mink, mink]; congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · exact mul_comm _ _

lemma minkSeg_smul (r s : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (r • x) (s • y) = r * s * mink x y := by
  rw [mink, mink]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i : Fin n, r * x (Sum.inl i) * (s * y (Sum.inl i))) =
      r * s * ∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]; ring

lemma minkSeg_add_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink (x + y) z = mink x z + mink y z := by
  simp only [mink, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring

lemma minkSeg_add_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink x (y + z) = mink x y + mink x z := by
  simp only [mink, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring

/-! ## Hyperbolic identities -/

lemma sinhSeg_one_sub (d s : ℝ) :
    Real.sinh ((1 - s) * d) = Real.sinh d * Real.cosh (s * d) - Real.cosh d * Real.sinh (s * d) := by
  rw [show (1 - s) * d = d - s * d by ring, Real.sinh_sub]

/-- The Gram identity behind the segment computation:
`⟨Ṽ_s, Ṽ_t⟩ = -sinh²d · cosh((s-t)d)` for the unnormalised combination `Ṽ`. -/
lemma segGram (d s t : ℝ) :
    Real.sinh ((1 - s) * d) * Real.sinh ((1 - t) * d)
      + Real.sinh (s * d) * Real.sinh (t * d)
      + Real.cosh d * (Real.sinh ((1 - s) * d) * Real.sinh (t * d)
          + Real.sinh (s * d) * Real.sinh ((1 - t) * d))
      = Real.sinh d ^ 2 * Real.cosh ((s - t) * d) := by
  have hcs : Real.cosh d ^ 2 - Real.sinh d ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq d
  have hct : Real.cosh (s * d) * Real.cosh (t * d) - Real.sinh (s * d) * Real.sinh (t * d)
      = Real.cosh ((s - t) * d) := by
    rw [show (s - t) * d = s * d - t * d by ring, Real.cosh_sub]
  rw [sinhSeg_one_sub d s, sinhSeg_one_sub d t, ← hct]
  linear_combination (-(Real.sinh (s * d) * Real.sinh (t * d))) * hcs

/-! ## The pairing along the geodesic segment -/

theorem minkGeoSeg {n : ℕ} (P Q : Fin n ⊕ Fin 1 → ℝ) (d s t : ℝ)
    (hP : Work.Mostow.mink P P = -1) (hQ : Work.Mostow.mink Q Q = -1)
    (hPQ : Work.Mostow.mink P Q = -Real.cosh d) (hd : d ≠ 0) :
    Work.Mostow.mink ((Real.sinh d)⁻¹ • (Real.sinh ((1 - s) * d) • P + Real.sinh (s * d) • Q))
      ((Real.sinh d)⁻¹ • (Real.sinh ((1 - t) * d) • P + Real.sinh (t * d) • Q))
      = -Real.cosh ((s - t) * d) := by
  have hS : Real.sinh d ≠ 0 := by
    intro h; exact hd (Real.sinh_eq_zero.mp h)
  have hQP : mink Q P = -Real.cosh d := by rw [minkSeg_comm]; exact hPQ
  set c : ℝ := (Real.sinh d)⁻¹ with hc
  set A1 : ℝ := Real.sinh ((1 - s) * d) with hA1
  set B1 : ℝ := Real.sinh (s * d) with hB1
  set A2 : ℝ := Real.sinh ((1 - t) * d) with hA2
  set B2 : ℝ := Real.sinh (t * d) with hB2
  -- Expand `mink` by bilinearity and substitute the three given pairings.
  have hmain : mink (c • (A1 • P + B1 • Q)) (c • (A2 • P + B2 • Q))
      = c * c * (A1 * A2 * (-1) + A1 * B2 * (-Real.cosh d) + B1 * A2 * (-Real.cosh d)
          + B1 * B2 * (-1)) := by
    rw [minkSeg_smul, minkSeg_add_left, minkSeg_add_right, minkSeg_add_right,
      minkSeg_smul, minkSeg_smul, minkSeg_smul, minkSeg_smul, hP, hQ, hPQ, hQP]
    ring
  rw [hmain, hc, hA1, hB1, hA2, hB2]
  have hcc : (Real.sinh d)⁻¹ * (Real.sinh d)⁻¹ * Real.sinh d ^ 2 = 1 := by
    rw [← sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hS)]
  have hg := segGram d s t
  have hinner : (Real.sinh ((1 - s) * d) * Real.sinh ((1 - t) * d) * (-1)
      + Real.sinh ((1 - s) * d) * Real.sinh (t * d) * (-Real.cosh d)
      + Real.sinh (s * d) * Real.sinh ((1 - t) * d) * (-Real.cosh d)
      + Real.sinh (s * d) * Real.sinh (t * d) * (-1))
      = -(Real.sinh ((1 - s) * d) * Real.sinh ((1 - t) * d)
          + Real.sinh (s * d) * Real.sinh (t * d)
          + Real.cosh d * (Real.sinh ((1 - s) * d) * Real.sinh (t * d)
              + Real.sinh (s * d) * Real.sinh ((1 - t) * d))) := by ring
  rw [hinner, hg]
  linear_combination (-(Real.cosh ((s - t) * d))) * hcc

end Work.Mostow
