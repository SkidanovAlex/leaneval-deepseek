import Mathlib
import Submission.Work.LinnikAreas.BGTZ.GEstimateDefs
import Submission.Work.LinnikAreas.BGTZ.E.sum_sqfree_three_pow_div_le

namespace Work.LinnikAreas.BGTZ.E

open scoped BigOperators

/-- The local weight is at most `3 / √p` for `p ≥ 1`: the character term contributes at most
`2/√p` and the `1/p` term is dominated by `1/√p`. -/
private lemma gwt_le_three_div_sqrt {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : 1 ≤ p) : Work.LinnikAreas.BGTZ.gwt χ₁ p ≤ 3 / Real.sqrt (p : ℝ) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (p : ℝ) ≤ (p : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hp0, by nlinarith [sq_nonneg ((p : ℝ) - 1)]⟩
  have h1 : 1 / (p : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := one_div_le_one_div_of_le hs hsq
  have h2 : (1 + (χ₁ p).re) / Real.sqrt (p : ℝ) ≤ 2 / Real.sqrt (p : ℝ) :=
    div_le_div_of_nonneg_right (by linarith [Work.LinnikAreas.BGTZ.re_apply_le_one χ₁ p]) hs.le
  have h3 : (1 + (χ₁ p).re) / Real.sqrt (p : ℝ) + 1 / (p : ℝ)
      ≤ 2 / Real.sqrt (p : ℝ) + 1 / Real.sqrt (p : ℝ) := add_le_add h2 h1
  have h4 : (2 : ℝ) / Real.sqrt (p : ℝ) + 1 / Real.sqrt (p : ℝ) = 3 / Real.sqrt (p : ℝ) := by
    ring
  rw [Work.LinnikAreas.BGTZ.gwt]
  linarith

/-- The multiplicative weight is bounded by `3 ^ ω(d) / √d`.  For squarefree `d` this is the
product of the local bounds `gwt χ₁ p ≤ 3/√p` together with `∏_{p ∣ d} p = d`; for
non-squarefree `d` the left side vanishes. -/
private lemma gw_le_three_pow_div_sqrt {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (d : ℕ) :
    Work.LinnikAreas.BGTZ.gw χ₁ d
      ≤ (3 : ℝ) ^ d.primeFactors.card / Real.sqrt (d : ℝ) := by
  by_cases hd : Squarefree d
  · rw [Work.LinnikAreas.BGTZ.gw_of_squarefree χ₁ hd]
    have hsqrt : ∏ p ∈ d.primeFactors, Real.sqrt (p : ℝ) = Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_prod d.primeFactors (fun p _ => by positivity : ∀ p ∈ d.primeFactors, (0:ℝ) ≤ (p:ℝ))]
      congr 1
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
    calc ∏ p ∈ d.primeFactors, Work.LinnikAreas.BGTZ.gwt χ₁ p
        ≤ ∏ p ∈ d.primeFactors, 3 / Real.sqrt (p : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro p _; exact Work.LinnikAreas.BGTZ.gwt_nonneg χ₁ p
          · intro p hp
            exact gwt_le_three_div_sqrt χ₁
              (le_of_lt (Nat.Prime.one_lt (Nat.mem_primeFactors.mp hp).1))
      _ = (3 : ℝ) ^ d.primeFactors.card / Real.sqrt (d : ℝ) := by
          rw [Finset.prod_div_distrib, Finset.prod_const, hsqrt]
  · rw [Work.LinnikAreas.BGTZ.gw_of_not_squarefree χ₁ hd]
    exact div_nonneg (by positivity) (Real.sqrt_nonneg _)

theorem gsum_le_trivial {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (Y : ℕ) :
    Work.LinnikAreas.BGTZ.gsum χ₁ Y ≤ Real.sqrt (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ 3 := by
  have hsqrtY : (0 : ℝ) ≤ Real.sqrt (Y : ℝ) := Real.sqrt_nonneg _
  have hfilter : Work.LinnikAreas.BGTZ.gsum χ₁ Y
      = ∑ d ∈ (Finset.Icc 1 Y).filter Squarefree, Work.LinnikAreas.BGTZ.gw χ₁ d := by
    rw [Work.LinnikAreas.BGTZ.gsum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : Squarefree d
    · rw [if_pos h]
    · rw [if_neg h, Work.LinnikAreas.BGTZ.gw_of_not_squarefree χ₁ h]
  rw [hfilter]
  calc ∑ d ∈ (Finset.Icc 1 Y).filter Squarefree, Work.LinnikAreas.BGTZ.gw χ₁ d
      ≤ ∑ d ∈ (Finset.Icc 1 Y).filter Squarefree,
          Real.sqrt (Y : ℝ) * ((3 : ℝ) ^ d.primeFactors.card / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hdmem, _⟩ := Finset.mem_filter.mp hd
        obtain ⟨hd1, hdY⟩ := Finset.mem_Icc.mp hdmem
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hsdpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
        have hsYd : Real.sqrt (d : ℝ) ≤ Real.sqrt (Y : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hdY)
        have hcard : (0 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := by positivity
        have key : (1 : ℝ) / Real.sqrt (d : ℝ) ≤ Real.sqrt (Y : ℝ) / (d : ℝ) := by
          rw [div_le_div_iff₀ hsdpos hdpos]
          calc (1 : ℝ) * (d : ℝ) = Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) := by
                rw [one_mul]
                exact (Real.sq_sqrt hdpos.le).symm.trans (by rw [pow_two])
            _ ≤ Real.sqrt (Y : ℝ) * Real.sqrt (d : ℝ) :=
                mul_le_mul_of_nonneg_right hsYd (Real.sqrt_nonneg _)
        calc Work.LinnikAreas.BGTZ.gw χ₁ d
            ≤ (3 : ℝ) ^ d.primeFactors.card / Real.sqrt (d : ℝ) := gw_le_three_pow_div_sqrt χ₁ d
          _ = (3 : ℝ) ^ d.primeFactors.card * (1 / Real.sqrt (d : ℝ)) := by rw [mul_one_div]
          _ ≤ (3 : ℝ) ^ d.primeFactors.card * (Real.sqrt (Y : ℝ) / (d : ℝ)) :=
              mul_le_mul_of_nonneg_left key hcard
          _ = Real.sqrt (Y : ℝ) * ((3 : ℝ) ^ d.primeFactors.card / (d : ℝ)) := by ring
    _ = Real.sqrt (Y : ℝ)
          * ∑ d ∈ (Finset.Icc 1 Y).filter Squarefree, (3 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left (sum_sqfree_three_pow_div_le Y) hsqrtY

end Work.LinnikAreas.BGTZ.E
