import Mathlib
import Submission.Work.FIArea4.Vflip.FlipSetup
import Submission.Work.FIArea4.PairSumCommon

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The smooth near/far cutoff `nearCut` and the pair weight `pairWeight` (FI §12)

This module provides the two local notions on which the dyadic form of Friedlander–Iwaniec
Proposition 12.1 is built:

* `nearCut a b`, the smooth even cutoff `g` of the paper's separation: `1` on `a ≤ |x| ≤ b`,
  `0` for `|x| ≤ a/2` and for `|x| ≥ 2b`;
* `pairWeight D p q`, the `d`-sum `Σ_{d ≤ 3D} bump (d/D) [r₁s₂ ≡ r₂s₁ (d)] (r₁|d')(r₂|d')`
  attached to a pair of box points (the smooth-majorant form of the local variance);
* the auxiliary quantities `pairC = (r₁,r₂)`, `pairR`, `pairAbs` of the reduction of a pair by its
  common divisor (the first step of the "flipping of moduli").
-/

namespace Work.FIArea4.Vflip

noncomputable section

/-! ## The smooth near/far cutoff -/

/-- The smooth even cutoff of the near/far separation: `1` on `a ≤ |x| ≤ b`, vanishing for
`|x| ≤ a/2` and for `|x| ≥ 2b`. -/
def nearCut (a b x : ℝ) : ℝ :=
  Real.smoothTransition ((4 * x ^ 2 - a ^ 2) / a ^ 2) *
    Real.smoothTransition ((4 * b ^ 2 - x ^ 2) / b ^ 2)

lemma nearCut_nonneg (a b x : ℝ) : 0 ≤ nearCut a b x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma nearCut_le_one (a b x : ℝ) : nearCut a b x ≤ 1 := by
  have h1 := Real.smoothTransition.le_one ((4 * x ^ 2 - a ^ 2) / a ^ 2)
  have h2 := Real.smoothTransition.le_one ((4 * b ^ 2 - x ^ 2) / b ^ 2)
  have h1' := Real.smoothTransition.nonneg ((4 * x ^ 2 - a ^ 2) / a ^ 2)
  have h2' := Real.smoothTransition.nonneg ((4 * b ^ 2 - x ^ 2) / b ^ 2)
  rw [nearCut]
  nlinarith

lemma nearCut_even (a b x : ℝ) : nearCut a b (-x) = nearCut a b x := by
  rw [nearCut, nearCut]; ring_nf

lemma nearCut_eq_one {a b x : ℝ} (ha : 0 < a) (hax : a ≤ |x|) (hxb : |x| ≤ b) :
    nearCut a b x = 1 := by
  have hb : 0 < b := lt_of_lt_of_le (lt_of_lt_of_le ha hax) hxb
  rw [nearCut]
  have hx2 : a ^ 2 ≤ x ^ 2 := by
    have h := pow_le_pow_left₀ ha.le hax 2
    rwa [sq_abs] at h
  have hx2' : x ^ 2 ≤ b ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hxb 2
    rwa [sq_abs] at h
  rw [Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ (4 * x ^ 2 - a ^ 2) / a ^ 2 by
        rw [le_div_iff₀ (by positivity)]; nlinarith),
      Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ (4 * b ^ 2 - x ^ 2) / b ^ 2 by
        rw [le_div_iff₀ (by positivity)]; nlinarith),
      mul_one]

lemma nearCut_eq_zero_of_abs_le {a b x : ℝ} (ha : 0 < a) (h : |x| ≤ a / 2) :
    nearCut a b x = 0 := by
  rw [nearCut]
  have hnum : 4 * x ^ 2 - a ^ 2 ≤ 0 := by
    have h' : x ^ 2 ≤ (a / 2) ^ 2 := by
      have h2 := pow_le_pow_left₀ (abs_nonneg x) h 2
      rwa [sq_abs] at h2
    nlinarith [sq_nonneg (a / 2)]
  have hden : (0:ℝ) ≤ a ^ 2 := by positivity
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum hden), zero_mul]

lemma nearCut_eq_zero_of_abs_ge {a b x : ℝ} (hb : 0 < b) (h : 2 * b ≤ |x|) :
    nearCut a b x = 0 := by
  rw [nearCut]
  have hnum : 4 * b ^ 2 - x ^ 2 ≤ 0 := by
    have h' : (2 * b) ^ 2 ≤ x ^ 2 := by
      have h2 := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 2 * b) h 2
      rwa [sq_abs] at h2
    nlinarith
  have hden : (0:ℝ) ≤ b ^ 2 := by positivity
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum hden), mul_zero]

lemma contDiff_nearCut (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (nearCut a b) := by
  unfold nearCut
  exact ContDiff.mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop))
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop))

/-! ## The pair weight of the smooth majorant -/

/-- The pair weight of the (smoothly majorised) variance: for a pair of box points `p = (r₁,s₁)`,
`q = (r₂,s₂)` it collects the `d`-sum of the smooth majorant over the congruence
`r₁s₂ ≡ r₂s₁ (mod d)`, weighted by the product `(r₁|d')(r₂|d')` of Jacobi symbols.

The range `1 ≤ d ≤ 3D` is chosen so that the whole support `d < 5D/2` of `bump (d/D)` is
contained, so that no truncation of the divisor sums occurs in the flip identity. -/
def pairWeight (D : ℕ) (p q : ℕ × ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (3 * D), (Work.FIArea4.Vflip.bump ((d : ℝ) / D) : ℂ) *
    (if ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d) then
      Work.FIArea4.jw d p.1 * Work.FIArea4.jw d q.1 else 0)

/-- The real "difference ratio" `x_{pq} = s₁/r₁ - s₂/r₂` of a pair of box points (as a real
number; its absolute value is `|r₁s₂ - r₂s₁| / (r₁r₂)`). -/
def xPair (p q : ℕ × ℕ) : ℝ := (p.2 : ℝ) / (p.1 : ℝ) - (q.2 : ℝ) / (q.1 : ℝ)

/-- The box `(R,2R] × (S,2S]` of the paper (11.6). -/
def boxF (R S : ℕ) : Finset (ℕ × ℕ) := Finset.Ioc R (2 * R) ×ˢ Finset.Ioc S (2 * S)

/-! ## Reduction of a pair by its common divisor -/

/-- `c = gcd r₁ r₂`: the common divisor by which the pair `(r₁,r₂)` is reduced before the
reciprocity flip of FI §12. -/
def pairC (r1 r2 : ℕ) : ℕ := Nat.gcd r1 r2

/-- The reduced first modulus `r₁' = r₁/(r₁,r₂)`. -/
def pairR (r1 r2 : ℕ) : ℕ := r1 / pairC r1 r2

/-- The reduced cross difference `|r₁' s₂ - r₂' s₁|`, the quantity whose complementary divisors
appear after the flip of moduli. -/
def pairAbs (r1 r2 s1 s2 : ℕ) : ℕ :=
  ((pairR r1 r2 : ℤ) * (s2 : ℤ) - (pairR r2 r1 : ℤ) * (s1 : ℤ)).natAbs

end

end Work.FIArea4.Vflip
