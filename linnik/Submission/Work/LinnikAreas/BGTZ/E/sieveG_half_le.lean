/-
# The trivial `R (log R)^9` bound for the sieve function on the critical line

`‖G(1/2 + iτ, χ)‖ ≤ R (1 + log R)^9`, with no dependence on `q`, on the character, or on the
sifting weights beyond `IsSieveWeight`.

The proof has four inputs, all already in the workspace:

* `SieveGLePairsum`: `‖G(1/2+iτ,χ)‖ ≤ gpairsum χ₁ R`, the triangle inequality against the double
  sum `Σ_{d,e ≤ R} f([d,e])[d,e]^{-1/2}`;
* `GPairReduce`: `gpairsum χ₁ R ≤ Σ_{g ≤ R} gw χ₁ g · (gsum χ₁ (R/g))²`, the `gcd`-reindexing;
* `gsum_le_trivial`: `gsum χ₁ Y ≤ √Y (1 + log Y)³` (the single sum is `O(√R log³R)`);
* `sum_sqfree_three_pow_div_le`: `Σ_{d ≤ R, □} 3^{ω(d)}/d ≤ (1 + log R)³`;
* and the elementary pointwise bound `gw χ₁ d ≤ 3^{ω(d)}`, which turns `Σ_{g ≤ R} gw χ₁ g / g` into
  the squarefree sum above.

Indeed, with `c = (1 + log R)⁶`,

`gpairsum χ₁ R ≤ Σ_{g ≤ R} gw χ₁ g · (R/g) c ≤ c R Σ_{g ≤ R} gw χ₁ g / g ≤ c R (1 + log R)³`,

which is `R (1 + log R)⁹`.  The factor `R` (rather than the true size `R log R` or so) is exactly
why this bound only needs the `O(√R log³R)` estimate for the single sum: the bound is the trivial
one used to dispose of the `G`-term in small ranges, not the BGTZ Lemma 4.3 estimate itself.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZ.GEstimateDefs
import Submission.Work.LinnikAreas.BGTZ.GPairReduce
import Submission.Work.LinnikAreas.BGTZ.SieveGLePairsum
import Submission.Work.LinnikAreas.BGTZ.E.gsum_le_trivial
import Submission.Work.LinnikAreas.BGTZ.E.sum_sqfree_three_pow_div_le

open scoped BigOperators

namespace Work.LinnikAreas.BGTZ.E

/-- Each local sieve weight is at most `3`: the character term contributes at most `2/√p` and the
`1/p` term at most `1`, and `√p ≥ 1` for `p ≥ 1`. -/
private lemma gwt_le_three {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : 1 ≤ p) : Work.LinnikAreas.BGTZ.gwt χ₁ p ≤ 3 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hs : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hp1
  have h2 : (1 + (χ₁ p).re) / Real.sqrt (p : ℝ) ≤ 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.sqrt (p : ℝ))]
    nlinarith [Work.LinnikAreas.BGTZ.re_apply_le_one χ₁ p]
  have h1 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp0]; linarith
  simp only [Work.LinnikAreas.BGTZ.gwt]
  linarith

/-- The multiplicative weight is at most `3 ^ ω(d)`. -/
private lemma gw_le_three_pow {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (d : ℕ) :
    Work.LinnikAreas.BGTZ.gw χ₁ d ≤ (3 : ℝ) ^ d.primeFactors.card := by
  by_cases hd : Squarefree d
  · rw [Work.LinnikAreas.BGTZ.gw_of_squarefree χ₁ hd]
    calc ∏ p ∈ d.primeFactors, Work.LinnikAreas.BGTZ.gwt χ₁ p
        ≤ ∏ p ∈ d.primeFactors, (3 : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro p _; exact Work.LinnikAreas.BGTZ.gwt_nonneg χ₁ p
          · intro p hp
            exact gwt_le_three χ₁
              (le_of_lt (Nat.Prime.one_lt (Nat.mem_primeFactors.mp hp).1))
      _ = (3 : ℝ) ^ d.primeFactors.card := Finset.prod_const 3
  · rw [Work.LinnikAreas.BGTZ.gw_of_not_squarefree χ₁ hd]
    positivity

/-- `Σ_{g ≤ R} gw χ₁ g / g ≤ (1 + log R)³`: the summands with `g` non-squarefree vanish, and for
squarefree `g` the weight is at most `3^{ω(g)}`, which is handled by
`sum_sqfree_three_pow_div_le`. -/
private lemma sum_gw_div_le {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (R : ℕ) :
    ∑ g ∈ Finset.Icc 1 R, Work.LinnikAreas.BGTZ.gw χ₁ g / (g : ℝ)
      ≤ (1 + Real.log (R : ℝ)) ^ 3 := by
  have hfilter : ∑ g ∈ Finset.Icc 1 R, Work.LinnikAreas.BGTZ.gw χ₁ g / (g : ℝ)
      = ∑ g ∈ (Finset.Icc 1 R).filter Squarefree,
          Work.LinnikAreas.BGTZ.gw χ₁ g / (g : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro g _
    by_cases h : Squarefree g
    · rw [if_pos h]
    · rw [if_neg h, Work.LinnikAreas.BGTZ.gw_of_not_squarefree χ₁ h, zero_div]
  rw [hfilter]
  calc ∑ g ∈ (Finset.Icc 1 R).filter Squarefree, Work.LinnikAreas.BGTZ.gw χ₁ g / (g : ℝ)
      ≤ ∑ g ∈ (Finset.Icc 1 R).filter Squarefree, (3 : ℝ) ^ g.primeFactors.card / (g : ℝ) := by
        apply Finset.sum_le_sum
        intro g hg
        have hg1 : 1 ≤ g := (Finset.mem_Icc.mp (Finset.mem_filter.mp hg).1).1
        have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg1
        exact div_le_div_of_nonneg_right (gw_le_three_pow χ₁ g) hgpos.le
    _ ≤ (1 + Real.log (R : ℝ)) ^ 3 := sum_sqfree_three_pow_div_le R

/-- **The trivial critical-line bound for the sieve function.**  On the line `Re s = 1/2` the
sieve function `G` of BGTZ Lemma 4.3 is at most `R (1 + log R)^9`, uniformly in `q`, in the two
characters and in the sifting weights. -/
theorem sieveG_half_le {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) {R : ℕ} {θw : ℕ → ℝ} (hθ : Work.LinnikAreas.BGTZ.IsSieveWeight R θw) (τ : ℝ) : ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) χ‖ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9 := by
  have hpair : ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) χ‖
      ≤ Work.LinnikAreas.BGTZ.gpairsum χ₁ R :=
    Work.LinnikAreas.BGTZ.SieveGLePairsum χ₁ χ hχ₁ hθ τ
  have hred : Work.LinnikAreas.BGTZ.gpairsum χ₁ R
      ≤ ∑ g ∈ Finset.Icc 1 R,
          Work.LinnikAreas.BGTZ.gw χ₁ g * (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2 :=
    Work.LinnikAreas.BGTZ.GPairReduce q χ₁ hχ₁ R
  set c : ℝ := (1 + Real.log (R : ℝ)) ^ 6 with hcdef
  have hlog0 : (0 : ℝ) ≤ Real.log (R : ℝ) := Real.log_natCast_nonneg R
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hterm : ∑ g ∈ Finset.Icc 1 R,
        Work.LinnikAreas.BGTZ.gw χ₁ g * (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2
      ≤ ∑ g ∈ Finset.Icc 1 R, c * ((R : ℝ) * (Work.LinnikAreas.BGTZ.gw χ₁ g / (g : ℝ))) := by
    apply Finset.sum_le_sum
    intro g hg
    obtain ⟨hg1, hgR⟩ := Finset.mem_Icc.mp hg
    have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg1
    have hgs := gsum_le_trivial χ₁ (R / g)
    have hgs0 := Work.LinnikAreas.BGTZ.gsum_nonneg χ₁ (R / g)
    have hsq : (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2
        ≤ ((R / g : ℕ) : ℝ) * (1 + Real.log ((R / g : ℕ) : ℝ)) ^ 6 := by
      have h := pow_le_pow_left₀ hgs0 hgs 2
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((R / g : ℕ) : ℝ)),
        ← pow_mul] at h
      norm_num at h
      exact h
    have hdiv1 : 1 ≤ R / g := Nat.one_le_div_iff hg1 |>.mpr hgR
    have hdivle : R / g ≤ R := Nat.div_le_self R g
    have h6 : (1 + Real.log ((R / g : ℕ) : ℝ)) ^ 6 ≤ (1 + Real.log (R : ℝ)) ^ 6 := by
      have hlog : Real.log ((R / g : ℕ) : ℝ) ≤ Real.log (R : ℝ) :=
        Real.log_le_log (by exact_mod_cast hdiv1) (by exact_mod_cast hdivle)
      exact pow_le_pow_left₀ (by have := Real.log_natCast_nonneg (R / g); linarith)
        (by linarith) 6
    have hsq2 : (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2
        ≤ ((R / g : ℕ) : ℝ) * (1 + Real.log (R : ℝ)) ^ 6 :=
      le_trans hsq (mul_le_mul_of_nonneg_left h6 (by positivity))
    have hnat : ((R / g : ℕ) : ℝ) ≤ (R : ℝ) / (g : ℝ) := Nat.cast_div_le
    have hsq3 : (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2
        ≤ ((R : ℝ) / (g : ℝ)) * c := by
      rw [hcdef]
      exact le_trans hsq2 (mul_le_mul_of_nonneg_right hnat (by positivity))
    have hgw := Work.LinnikAreas.BGTZ.gw_nonneg χ₁ g
    calc Work.LinnikAreas.BGTZ.gw χ₁ g * (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2
        ≤ Work.LinnikAreas.BGTZ.gw χ₁ g * (((R : ℝ) / (g : ℝ)) * c) :=
          mul_le_mul_of_nonneg_left hsq3 hgw
      _ = c * ((R : ℝ) * (Work.LinnikAreas.BGTZ.gw χ₁ g / (g : ℝ))) := by ring
  have hfinal : ∑ g ∈ Finset.Icc 1 R,
        Work.LinnikAreas.BGTZ.gw χ₁ g * (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2
      ≤ c * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 3) := by
    calc ∑ g ∈ Finset.Icc 1 R,
          Work.LinnikAreas.BGTZ.gw χ₁ g * (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2
        ≤ ∑ g ∈ Finset.Icc 1 R,
            c * ((R : ℝ) * (Work.LinnikAreas.BGTZ.gw χ₁ g / (g : ℝ))) := hterm
      _ = c * ((R : ℝ) * ∑ g ∈ Finset.Icc 1 R, Work.LinnikAreas.BGTZ.gw χ₁ g / (g : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ c * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 3) := by
          have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
          have h1 := mul_le_mul_of_nonneg_left (sum_gw_div_le χ₁ R) hR0
          exact mul_le_mul_of_nonneg_left h1 hc0
  calc ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) χ‖
      ≤ Work.LinnikAreas.BGTZ.gpairsum χ₁ R := hpair
    _ ≤ ∑ g ∈ Finset.Icc 1 R,
          Work.LinnikAreas.BGTZ.gw χ₁ g * (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2 := hred
    _ ≤ c * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 3) := hfinal
    _ = (R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9 := by
        rw [hcdef]
        have h : (1 + Real.log (R : ℝ)) ^ 6 * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 3)
            = (R : ℝ) * ((1 + Real.log (R : ℝ)) ^ 6 * (1 + Real.log (R : ℝ)) ^ 3) := by ring
        rw [h, ← pow_add]

end Work.LinnikAreas.BGTZ.E
