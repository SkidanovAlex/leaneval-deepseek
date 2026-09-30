import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open scoped BigOperators Interval

/-- Regroup a finite Dirichlet-type sum `∑ γᵢ · (nᵢ)^{-(1+it)}` by the value `n` of `nᵢ`,
and rewrite each complex power `n^{-(1+it)}` as `n⁻¹ · exp(i · (-log n) · t)`.

This is the algebraic step converting a Dirichlet polynomial into an exponential sum:
the inner sum `∑_{nᵢ = n} γᵢ / n` is the Dirichlet coefficient at `n`, and
`exp(i·t·(-log n)) = n^{-it}` is the multiplicative character. -/
theorem dirichlet_sum_eq_exp_sum {ι : Type} (s : Finset ι) (γ : ι → ℂ) (nn : ι → ℕ) (t : ℝ) :
    (∑ i ∈ s, γ i * (nn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = ∑ n ∈ s.image nn,
          (∑ i ∈ s.filter (fun i => nn i = n), γ i * (n : ℂ)⁻¹)
            * Complex.exp (Complex.I * ((((-(Real.log n)) : ℝ) : ℂ) * (t : ℂ))) := by
  classical
  -- The value-by-value identity `n^{-(1+it)} = n⁻¹ · exp(i·(-log n)·t)`.
  have key : ∀ n : ℕ, (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))
      = (n : ℂ)⁻¹ * Complex.exp (Complex.I * ((((-(Real.log n)) : ℝ) : ℂ) * (t : ℂ))) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hw : (-(1 + Complex.I * (t : ℂ))) ≠ 0 := by
        rw [neg_ne_zero]
        intro h
        have hre := congrArg Complex.re h
        simp at hre
      simp only [Nat.cast_zero]
      rw [Complex.zero_cpow hw]
      simp
    · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hexp : Complex.exp (((Real.log n) : ℝ) : ℂ) = (n : ℂ) := by
        rw [← Complex.ofReal_exp, Real.exp_log hpos]
        simp
      have hinv : ((n : ℂ))⁻¹ = Complex.exp (-(((Real.log n) : ℝ) : ℂ)) := by
        rw [← hexp, ← Complex.exp_neg]
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log, hinv, ← Complex.exp_add]
      congr 1
      push_cast
      ring
  -- Regroup the sum over `s` according to the value of `nn`.
  rw [← Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem nn hi)
        (fun i => γ i * (nn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
  apply Finset.sum_congr rfl
  intro n _
  -- Inside the fibre `nn i = n`, the power only depends on `n`.
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
  rw [key n, ← Finset.sum_mul, ← mul_assoc, ← Finset.sum_mul]

end Work.BMF.mr_direct
