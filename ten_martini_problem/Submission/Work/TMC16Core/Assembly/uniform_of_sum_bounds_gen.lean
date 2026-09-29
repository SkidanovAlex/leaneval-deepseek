/-
# The general (`Finset ℤ`-indexed) uniformity estimate

`Work.TMC16Core.Assembly.uniform_of_sum_bounds_gen` is the *general* form of the Lagrange
product manipulation in AJ §9, Lemma 9.10: instead of the two specific windows
`Q1s0c`/`Q2s0c` of `Assembly/uni_s0c_estimate.lean` it takes an arbitrary finite set
`S : Finset ℤ` of phase indices.

Given

* `hcos` : the phases `θ + iα`, `i ∈ S`, have pairwise distinct cosines;
* `hN`  : an upper bound for *every* "numerator" block sum `∑_{i∈S∖k} log|sin π(ξ+iα)|`;
* `hD1` : a lower bound for the "sum" block sums `∑_{i∈S∖k} log|sin π(2θ+(i+k)α)|`;
* `hD2` : a lower bound for the "difference" block sums `∑_{i∈S∖k} log|sin π((i−k)α)|`;
* the numeric budget `2A+B+C+2log(1/(2cθ))+log(1/(2csep)) < (#S−1)ε`,

we conclude that the family of phases `θ + pα`, `p ∈ S`, is `ε`-uniform in the sense of
`Work.TMC16Core.Uniform`.

The proof is the standard Lagrange computation: write
`x = cos 2πa`, factor every numerator as
`|x − cos 2π(θ+iα)| = 2|sin π((a+θ)+iα)| · |sin π((θ−a)+iα)|`
and every denominator as
`|cos 2π(θ+kα) − cos 2π(θ+iα)| = 2|sin π(2θ+(i+k)α)| · |sin π((i−k)α)|`,
take logarithms (the `(#S−1)·log 2` normalisations cancel between numerator and denominator)
and apply the three block bounds plus the budget.
-/
import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.uni_s0c_estimate

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

noncomputable section

/-- Difference of cosines factorised into sines of the half-sum and half-difference. -/
theorem abs_cos_sub_cos_factor (u v : ℝ) :
    |Real.cos (2 * Real.pi * u) - Real.cos (2 * Real.pi * v)|
      = 2 * |Real.sin (Real.pi * (u + v))| * |Real.sin (Real.pi * (u - v))| := by
  rw [Real.cos_sub_cos]
  rw [show (2 * Real.pi * u + 2 * Real.pi * v) / 2 = Real.pi * (u + v) by ring,
      show (2 * Real.pi * u - 2 * Real.pi * v) / 2 = Real.pi * (u - v) by ring]
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [abs_mul, abs_mul, h2]

/-- **The general Lagrange-product bound.**  If the phases `θ + iα`, `i ∈ S`, have pairwise
distinct cosines and the three trigonometric block sums satisfy `hN`, `hD1`, `hD2`, then every
Lagrange product of the family is `< exp ((#S−1)ε)`, as soon as the numeric budget holds. -/
theorem gen_lagrange_prod_bound {S : Finset ℤ} {α θ ε cθ csep A B C : ℝ}
    (hcos : ∀ i : ℤ, i ∈ S → ∀ j : ℤ, j ∈ S → i ≠ j →
      Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)))
    (hN : ∀ (k : ℤ), k ∈ S → ∀ ξ : ℝ,
      (∀ i ∈ S.erase k, Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -((S.card : ℝ) - 1) * Real.log 2 + A)
    (hD1 : ∀ k : ℤ, k ∈ S →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (2 * θ + ((i + k : ℤ) : ℝ) * α))|
        ≥ -((S.card : ℝ) - 1) * Real.log 2 - B + 2 * Real.log (2 * cθ))
    (hD2 : ∀ k : ℤ, k ∈ S →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        ≥ -((S.card : ℝ) - 1) * Real.log 2 - C + Real.log (2 * csep))
    (hcθ : 0 < cθ) (hcsep : 0 < csep)
    (hbudget : 2 * A + B + C + 2 * Real.log (1 / (2 * cθ)) + Real.log (1 / (2 * csep))
      < ((S.card : ℝ) - 1) * ε)
    {k : ℤ} (hk : k ∈ S) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |∏ i ∈ S.erase k,
        (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
          (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
      < Real.exp (((S.card : ℝ) - 1) * ε) := by
  classical
  by_cases hzero : ∃ i ∈ S.erase k, x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) = 0
  · obtain ⟨i, hi, hiz⟩ := hzero
    have h1 : (∏ i ∈ S.erase k,
        (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
          (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))) = 0 :=
      Finset.prod_eq_zero hi (by rw [hiz, zero_div])
    rw [h1, abs_zero]
    exact Real.exp_pos _
  · push_neg at hzero
    set a : ℝ := Real.arccos x / (2 * Real.pi) with ha
    have hxa : Real.cos (2 * Real.pi * a) = x := by
      have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      calc Real.cos (2 * Real.pi * a) = Real.cos (Real.arccos x) := by
            congr 1
            rw [ha]
            field_simp
        _ = x := Real.cos_arccos hx.1 hx.2
    have hfacN : ∀ i : ℤ, |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = 2 * |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))| *
            |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))| := by
      intro i
      rw [← hxa, abs_cos_sub_cos_factor]
      rw [show a + (θ + (i : ℝ) * α) = (a + θ) + (i : ℝ) * α by ring]
      rw [show a - (θ + (i : ℝ) * α) = -((θ - a) + (i : ℝ) * α) by ring]
      rw [show Real.pi * (-((θ - a) + (i : ℝ) * α))
            = -(Real.pi * ((θ - a) + (i : ℝ) * α)) by ring, Real.sin_neg, abs_neg]
    have hfacD : ∀ i : ℤ,
        |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = 2 * |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
            |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)| := by
      intro i
      rw [abs_cos_sub_cos_factor (θ + (k : ℝ) * α) (θ + (i : ℝ) * α)]
      rw [show (θ + (k : ℝ) * α) + (θ + (i : ℝ) * α)
            = 2 * θ + (((i + k : ℤ)) : ℝ) * α by push_cast; ring]
      rw [show (θ + (k : ℝ) * α) - (θ + (i : ℝ) * α)
            = -((((i - k : ℤ)) : ℝ) * α) by push_cast; ring]
      rw [show Real.pi * (-((((i - k : ℤ)) : ℝ) * α))
            = -(((Real.pi) * (((i - k : ℤ)) : ℝ)) * α) by ring, Real.sin_neg, abs_neg]
    have hsinN : ∀ i ∈ S.erase k,
        Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α)) ≠ 0 ∧
        Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α)) ≠ 0 := by
      intro i hi
      have h1 : 2 * |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))| *
          |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))| ≠ 0 := by
        rw [← hfacN i]
        exact (abs_pos.mpr (hzero i hi)).ne'
      constructor
      · intro h0; exact h1 (by rw [h0]; simp)
      · intro h0; exact h1 (by rw [h0]; simp)
    have hsinD : ∀ i ∈ S.erase k,
        Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α)) ≠ 0 ∧
        Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α) ≠ 0 := by
      intro i hi
      rw [Finset.mem_erase] at hi
      have h3 : Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
          ≠ Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) :=
        hcos k hk i hi.2 (fun h => hi.1 h.symm)
      have h1 : 2 * |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
          |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)| ≠ 0 := by
        rw [← hfacD i]
        exact (abs_pos.mpr (sub_ne_zero.mpr h3)).ne'
      constructor
      · intro h0; exact h1 (by rw [h0]; simp)
      · intro h0; exact h1 (by rw [h0]; simp)
    have hnum_ne : ∀ i ∈ S.erase k,
        x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ 0 := fun i hi => hzero i hi
    have hden_ne : ∀ i ∈ S.erase k,
        Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
          - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ 0 := by
      intro i hi
      rw [Finset.mem_erase] at hi
      exact sub_ne_zero.mpr (hcos k hk i hi.2 (fun h => hi.1 h.symm))
    have hlog : Real.log |∏ i ∈ S.erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = (∑ i ∈ S.erase k,
            Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|)
          - (∑ i ∈ S.erase k,
              Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
                - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) := by
      rw [Finset.abs_prod]
      have h1 : ∏ i ∈ S.erase k,
            |(x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
                - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
          = (∏ i ∈ S.erase k,
              |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) /
            (∏ i ∈ S.erase k,
              |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
                - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) := by
        rw [Finset.prod_congr rfl (fun i _ => abs_div _ _), Finset.prod_div_distrib]
      have hN0 : (∏ i ∈ S.erase k,
          |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => (abs_pos.mpr (hnum_ne i hi)).ne')
      have hD0 : (∏ i ∈ S.erase k,
          |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => (abs_pos.mpr (hden_ne i hi)).ne')
      rw [h1, Real.log_div hN0 hD0,
        Real.log_prod (fun i hi => (abs_pos.mpr (hnum_ne i hi)).ne'),
        Real.log_prod (fun i hi => (abs_pos.mpr (hden_ne i hi)).ne')]
    have htermN : ∀ i ∈ S.erase k,
        Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = Real.log 2 + (Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|
            + Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|) := by
      intro i hi
      have hs0 := (hsinN i hi).1
      have ht0 := (hsinN i hi).2
      have h1 : |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = 2 * (|Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))| *
            |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|) := by
        rw [hfacN i]; ring
      rw [h1, Real.log_mul (by norm_num)
          (mul_ne_zero (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)),
        Real.log_mul (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)]
    have htermD : ∀ i ∈ S.erase k,
        Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = Real.log 2 + (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|
            + Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
      intro i hi
      have hs0 := (hsinD i hi).1
      have ht0 := (hsinD i hi).2
      have h1 : |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = 2 * (|Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
            |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
        rw [hfacD i]; ring
      rw [h1, Real.log_mul (by norm_num)
          (mul_ne_zero (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)),
        Real.log_mul (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)]
    have hexpN : ∑ i ∈ S.erase k,
          Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = (((S.erase k).card : ℝ)) * Real.log 2
          + ∑ i ∈ S.erase k,
              (Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|
                + Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|) := by
      rw [Finset.sum_congr rfl htermN, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hexpD : ∑ i ∈ S.erase k,
          Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
            - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = (((S.erase k).card : ℝ)) * Real.log 2
          + ∑ i ∈ S.erase k,
              (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|
                + Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
      rw [Finset.sum_congr rfl htermD, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hS1 : ∑ i ∈ S.erase k,
            (Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|
              + Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
        = (∑ i ∈ S.erase k,
            Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
          + (∑ i ∈ S.erase k,
            Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|) :=
      Finset.sum_add_distrib
    have hS2 : ∑ i ∈ S.erase k,
            (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|
              + Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)
        = (∑ i ∈ S.erase k,
            Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
          + (∑ i ∈ S.erase k,
            Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) :=
      Finset.sum_add_distrib
    have hmain : Real.log |∏ i ∈ S.erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = (∑ i ∈ S.erase k,
              Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
          + (∑ i ∈ S.erase k,
              Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
          - ((∑ i ∈ S.erase k,
                Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
            + (∑ i ∈ S.erase k,
                Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)) := by
      rw [hlog, hexpN, hS1, hexpD, hS2]
      ring
    have hUp1 : (∑ i ∈ S.erase k,
          Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
        ≤ -((S.card : ℝ) - 1) * Real.log 2 + A :=
      hN k hk (a + θ) (fun i hi => (hsinN i hi).1)
    have hUp2 : (∑ i ∈ S.erase k,
          Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
        ≤ -((S.card : ℝ) - 1) * Real.log 2 + A :=
      hN k hk (θ - a) (fun i hi => (hsinN i hi).2)
    have hLo3 := hD1 k hk
    have hLo4 := hD2 k hk
    have hmid : Real.log |∏ i ∈ S.erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        ≤ 2 * A + B + C + 2 * Real.log (1 / (2 * cθ)) + Real.log (1 / (2 * csep)) := by
      have hcθ' : Real.log (2 * cθ) = -Real.log (1 / (2 * cθ)) := by
        rw [one_div, Real.log_inv, neg_neg]
      have hcsep' : Real.log (2 * csep) = -Real.log (1 / (2 * csep)) := by
        rw [one_div, Real.log_inv, neg_neg]
      rw [hmain]
      linarith [hUp1, hUp2, hLo3, hLo4, hcθ', hcsep']
    have hpos : 0 < |∏ i ∈ S.erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))| := by
      rw [Finset.abs_prod]
      refine Finset.prod_pos (fun i hi => ?_)
      rw [abs_div]
      exact div_pos (abs_pos.mpr (hnum_ne i hi)) (abs_pos.mpr (hden_ne i hi))
    calc |∏ i ∈ S.erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
        = Real.exp (Real.log |∏ i ∈ S.erase k,
            (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
                - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|) :=
          (Real.exp_log hpos).symm
      _ < Real.exp (((S.card : ℝ) - 1) * ε) :=
          Real.exp_lt_exp.mpr (lt_of_le_of_lt hmid hbudget)

/-- **The general uniformity estimate.**  The Lagrange-product bound of
`gen_lagrange_prod_bound`, packaged as `Work.TMC16Core.Uniform` for the phase family
`p ↦ θ + pα`, `p ∈ S`. -/
theorem uniform_of_sum_bounds_gen {S : Finset ℤ} {α θ ε cθ csep A B C : ℝ}
    (hcos : ∀ i : ℤ, i ∈ S → ∀ j : ℤ, j ∈ S → i ≠ j →
      Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)))
    (hN : ∀ (k : ℤ), k ∈ S → ∀ ξ : ℝ,
      (∀ i ∈ S.erase k, Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -((S.card : ℝ) - 1) * Real.log 2 + A)
    (hD1 : ∀ k : ℤ, k ∈ S →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (2 * θ + ((i + k : ℤ) : ℝ) * α))|
        ≥ -((S.card : ℝ) - 1) * Real.log 2 - B + 2 * Real.log (2 * cθ))
    (hD2 : ∀ k : ℤ, k ∈ S →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        ≥ -((S.card : ℝ) - 1) * Real.log 2 - C + Real.log (2 * csep))
    (hcθ : 0 < cθ) (hcsep : 0 < csep)
    (hbudget : 2 * A + B + C + 2 * Real.log (1 / (2 * cθ)) + Real.log (1 / (2 * csep))
      < ((S.card : ℝ) - 1) * ε) :
    Work.TMC16Core.Uniform ε (fun p : {p : ℤ // p ∈ S} => θ + (p : ℝ) * α) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i j hij hcon
    exact hcos i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) hcon
  · intro k x hx
    have hexp : ((Fintype.card {p : ℤ // p ∈ S} : ℝ) - 1) = (S.card : ℝ) - 1 := by
      rw [Fintype.card_coe]
    rw [hexp]
    have hprod : (∏ i ∈ Finset.univ.erase k,
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))))
        = ∏ i ∈ S.erase (k : ℤ),
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α))
              - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) := by
      refine Finset.prod_bij (fun (i : {p : ℤ // p ∈ S}) _ => (i : ℤ)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_erase] at hi ⊢
        exact ⟨fun hEq => hi.1 (Subtype.ext hEq), i.property⟩
      · intro i _ i' _ hEq
        exact Subtype.ext hEq
      · intro b hb
        rw [Finset.mem_erase] at hb
        refine ⟨⟨b, hb.2⟩, ?_, rfl⟩
        rw [Finset.mem_erase]
        exact ⟨fun hEq => hb.1 (congrArg Subtype.val hEq), Finset.mem_univ _⟩
      · intro i _
        rfl
    rw [hprod]
    exact gen_lagrange_prod_bound hcos hN hD1 hD2 hcθ hcsep hbudget k.2 hx

end

end Work.TMC16Core.Assembly
