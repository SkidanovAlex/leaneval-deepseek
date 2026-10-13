import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.EllipticEst.remov

/-- **Leibniz bound for the angular factor.**

`∂^{k+1}(sin θ · v)(θ)` is, by the general Leibniz rule, the sum
`∑_{j ≤ k+1} C(k+1,j) · sin^{(j)}(θ) · v^{(k+1-j)}(θ)`; every derivative of `sin` is bounded by
`1` in absolute value, and each `|v^{(k+1-j)}(θ)|` is bounded by the full sum
`∑_{m ≤ k+1} |v^{(m)}(θ)|`, so the whole thing is at most the product of the binomial sum and
that `v`-sum. -/
theorem slice_ang_A_leibniz (k : ℕ) (v : ℝ → ℝ)
    (hv : ContDiffOn ℝ (k + 1) v (Set.Ioo 0 (Real.pi / 2)))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |iteratedDeriv (k + 1) (fun t => Real.sin t * v t) θ|
      ≤ (∑ j ∈ Finset.range (k + 2), (((k + 1).choose j : ℕ) : ℝ))
        * (∑ m ∈ Finset.range (k + 2), |iteratedDeriv m v θ|) := by
  have hmem : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
  have hvAt : ContDiffAt ℝ (k + 1) v θ := hv.contDiffAt hmem
  have hsAt : ContDiffAt ℝ (k + 1) Real.sin θ := Real.contDiff_sin.contDiffAt
  -- the general Leibniz rule
  have hlei := iteratedDeriv_mul (n := k + 1) (x := θ) (f := Real.sin) (g := v) hsAt hvAt
  have hfun : (fun t => Real.sin t * v t) = Real.sin * v := rfl
  rw [hfun, hlei]
  -- abbreviation for the `v`-sum
  let T : ℝ := ∑ m ∈ Finset.range (k + 2), |iteratedDeriv m v θ|
  have hbT : ∀ i ∈ Finset.range (k + 2), |iteratedDeriv (k + 1 - i) v θ| ≤ T := by
    intro i hi
    have hi2 : i < k + 2 := Finset.mem_range.mp hi
    have hmem' : k + 1 - i ∈ Finset.range (k + 2) := by
      simp only [Finset.mem_range]; omega
    show |iteratedDeriv (k + 1 - i) v θ| ≤ ∑ m ∈ Finset.range (k + 2), |iteratedDeriv m v θ|
    exact Finset.single_le_sum (s := Finset.range (k + 2))
      (f := fun m => |iteratedDeriv m v θ|) (fun m _ => abs_nonneg _) hmem'
  calc |∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * iteratedDeriv i Real.sin θ
          * iteratedDeriv (k + 1 - i) v θ|
      ≤ ∑ i ∈ Finset.range (k + 2), |((k + 1).choose i : ℝ) * iteratedDeriv i Real.sin θ
          * iteratedDeriv (k + 1 - i) v θ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * T := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg ((k + 1).choose i))]
        have h1 : ((k + 1).choose i : ℝ) * |iteratedDeriv i Real.sin θ|
            ≤ ((k + 1).choose i : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_sin_le_one i θ) (Nat.cast_nonneg _)
        have h2 := mul_le_mul h1 (hbT i hi) (abs_nonneg _) (by positivity)
        rw [mul_one] at h2
        exact h2.trans_eq (by ring)
    _ = (∑ j ∈ Finset.range (k + 2), (((k + 1).choose j : ℕ) : ℝ)) * T := by
        rw [Finset.sum_mul]

end Work.FTS.EllipticEst.remov
