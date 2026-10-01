import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus

open Filter
open scoped Topology

/-- Push the real-to-complex coercion through an iterated derivative: for a real-valued
function `f`, the `n`-th derivative of `fun y ↦ (f y : ℂ)` is the coercion of the `n`-th
derivative of `f`. -/
lemma iteratedDeriv_ofReal (n : ℕ) (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ n f x) :
    iteratedDeriv n (fun y : ℝ => (f y : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) := by
  have h := iteratedDeriv_smul_const (n := n) (𝕜 := ℝ) (𝔸 := ℝ) (F := ℂ)
    (f := f) (x := x) hf (1 : ℂ)
  have hfun : (fun y : ℝ => (f y : ℂ)) = (fun y : ℝ => f y • (1 : ℂ)) := by
    funext y; simp [Algebra.smul_def]
  rw [hfun, h]
  simp [Algebra.smul_def]

/-- The norm of the iterated derivative of the complexification of a real-valued function
equals the norm of the iterated derivative of the original function. -/
lemma norm_iteratedDeriv_ofReal (n : ℕ) (f : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ n f x) :
    ‖iteratedDeriv n (fun y : ℝ => ((f y : ℝ) : ℂ)) x‖ = ‖iteratedDeriv n f x‖ := by
  rw [iteratedDeriv_ofReal n f x hf]
  simp [Real.norm_eq_abs]

/-- Sharp bound on a single term of the negative-binomial geometric series at `3/4`:
`(n+i).choose i * (3/4)^n ≤ 4^(i+1)`. -/
lemma nat_choose_mul_pow_le (i n : ℕ) :
    ((n + i).choose i : ℝ) * ((3:ℝ)/4)^n ≤ 4^(i+1) := by
  have hr : ‖((3:ℝ)/4)‖ < 1 := by norm_num
  have hsum : HasSum (fun n : ℕ => ((n + i).choose i : ℝ) * ((3:ℝ)/4)^n)
      (1/(1 - (3:ℝ)/4)^(i+1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one i hr
  have hle : ((n + i).choose i : ℝ) * ((3:ℝ)/4)^n ≤
      ∑' k, ((k + i).choose i : ℝ) * ((3:ℝ)/4)^k :=
    hsum.summable.le_tsum n (fun j _ => by positivity)
  rw [hsum.tsum_eq] at hle
  have hval : (1:ℝ)/(1 - (3:ℝ)/4)^(i+1) = 4^(i+1) := by
    have h1 : (1:ℝ) - 3/4 = (4:ℝ)⁻¹ := by norm_num
    rw [h1, one_div, inv_pow, inv_inv]
  rwa [hval] at hle

/-- Uniform (in `s`) bound on the `i`-th derivative of `y ↦ (y^s : ℂ)` on `|x| ≤ 3/4`. -/
lemma norm_iteratedDeriv_pow_le_of_abs_le (s i : ℕ) (x : ℝ) (hx : |x| ≤ (3:ℝ)/4) :
    ‖iteratedDeriv i (fun y : ℝ => ((y^s : ℝ) : ℂ)) x‖ ≤ (i.factorial : ℝ) * 4^(i+1) := by
  rw [norm_iteratedDeriv_ofReal i (fun y : ℝ => y^s) x (by fun_prop), iteratedDeriv_pow]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
  by_cases his : i ≤ s
  · have hxs : |x|^(s-i) ≤ ((3:ℝ)/4)^(s-i) := pow_le_pow_left₀ (abs_nonneg x) hx _
    calc (s.descFactorial i : ℝ) * |x|^(s-i)
        = (i.factorial : ℝ) * ((s.choose i : ℝ) * |x|^(s-i)) := by
            rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
      _ ≤ (i.factorial : ℝ) * ((s.choose i : ℝ) * ((3:ℝ)/4)^(s-i)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (i.factorial))
            exact mul_le_mul_of_nonneg_left hxs (Nat.cast_nonneg (s.choose i))
      _ ≤ (i.factorial : ℝ) * 4^(i+1) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (i.factorial))
            simpa [Nat.sub_add_cancel his] using nat_choose_mul_pow_le i (s-i)
  · have h0 : s.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [h0, Nat.cast_zero, zero_mul]
    positivity

theorem iteratedDeriv_pow_mul_le_of_bump (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : ℝ → ℝ), ContDiff ℝ (N : ℕ∞) χ →
      (∀ x : ℝ, 3 / 4 ≤ |x| → χ x = 0) →
      (∀ i ≤ N, ∀ x : ℝ, ‖iteratedDeriv i χ x‖ ≤ 1) →
      ∀ (s : ℕ) (x : ℝ),
        ‖iteratedDeriv N (fun y : ℝ => ((y ^ s : ℝ) : ℂ) * ((χ y : ℝ) : ℂ)) x‖ ≤ C := by
  let C : ℝ := (∑ i ∈ Finset.range (N+1), (N.choose i : ℝ) * ((i.factorial : ℝ) * 4^(i+1))) + 1
  have hCpos : 0 < C := by
    have hsum : 0 ≤ ∑ i ∈ Finset.range (N+1), (N.choose i : ℝ) * ((i.factorial : ℝ) * 4^(i+1)) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    dsimp [C]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro χ hχ hsupp hbound s x
  by_cases hx : |x| ≤ (3:ℝ)/4
  · have hcf : ContDiffAt ℝ N (fun y : ℝ => ((y ^ s : ℝ) : ℂ)) x := by
      have h : ContDiff ℝ N (fun y : ℝ => ((y ^ s : ℝ) : ℂ)) := by
        have h1 : ContDiff ℝ N (fun y : ℝ => y^s) := by
          have ht : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : ℝ => y^s) := contDiff_id.pow s
          exact ht.of_le le_top
        have hcomp := (Complex.ofRealCLM.contDiff (𝕜 := ℝ) (n := N)).comp h1
        convert hcomp using 1
        funext y; simp [Complex.ofRealCLM_apply]
      exact h.contDiffAt
    have hcg : ContDiffAt ℝ N (fun y : ℝ => ((χ y : ℝ) : ℂ)) x := by
      have h : ContDiff ℝ N (fun y : ℝ => ((χ y : ℝ) : ℂ)) := by
        have hcomp := (Complex.ofRealCLM.contDiff (𝕜 := ℝ) (n := N)).comp hχ
        convert hcomp using 1
        funext y; simp [Complex.ofRealCLM_apply]
      exact h.contDiffAt
    rw [show (fun y : ℝ => ((y ^ s : ℝ) : ℂ) * ((χ y : ℝ) : ℂ)) =
        ((fun y : ℝ => ((y ^ s : ℝ) : ℂ)) * (fun y : ℝ => ((χ y : ℝ) : ℂ))) from rfl]
    rw [iteratedDeriv_mul hcf hcg]
    calc ‖∑ i ∈ Finset.range (N + 1),
            ↑(N.choose i) * iteratedDeriv i (fun y : ℝ => ((y ^ s : ℝ) : ℂ)) x *
              iteratedDeriv (N - i) (fun y : ℝ => ((χ y : ℝ) : ℂ)) x‖
        ≤ ∑ i ∈ Finset.range (N + 1), ‖↑(N.choose i) *
              iteratedDeriv i (fun y : ℝ => ((y ^ s : ℝ) : ℂ)) x *
              iteratedDeriv (N - i) (fun y : ℝ => ((χ y : ℝ) : ℂ)) x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * ((i.factorial : ℝ) * 4^(i+1)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hiN : i ≤ N := by
            have := Finset.mem_range.mp hi
            omega
          have hcontχ : ContDiffAt ℝ ((N - i : ℕ) : ℕ∞) χ x :=
            (hχ.of_le (by exact_mod_cast Nat.sub_le N i)).contDiffAt
          have hb1 := norm_iteratedDeriv_pow_le_of_abs_le s i x hx
          have hb2 : ‖iteratedDeriv (N - i) (fun y : ℝ => ((χ y : ℝ) : ℂ)) x‖ ≤ 1 := by
            rw [norm_iteratedDeriv_ofReal (N-i) χ x hcontχ]
            exact hbound (N-i) (Nat.sub_le N i) x
          calc ‖↑(N.choose i) * iteratedDeriv i (fun y : ℝ => ((y ^ s : ℝ) : ℂ)) x *
                  iteratedDeriv (N - i) (fun y : ℝ => ((χ y : ℝ) : ℂ)) x‖
              = (N.choose i : ℝ) *
                  ‖iteratedDeriv i (fun y : ℝ => ((y ^ s : ℝ) : ℂ)) x‖ *
                  ‖iteratedDeriv (N - i) (fun y : ℝ => ((χ y : ℝ) : ℂ)) x‖ := by
                simp
            _ ≤ (N.choose i : ℝ) * ((i.factorial : ℝ) * 4 ^ (i+1)) * 1 := by
                gcongr
            _ = (N.choose i : ℝ) * ((i.factorial : ℝ) * 4 ^ (i+1)) := by ring
      _ ≤ C := by
          dsimp [C]; linarith
  · simp only [not_le] at hx
    have hmem : {y : ℝ | (3:ℝ)/4 < |y|} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds hx
    have heq : (fun y : ℝ => ((y ^ s : ℝ) : ℂ) * ((χ y : ℝ) : ℂ)) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hmem] with y hy
      rw [Pi.zero_apply, hsupp y hy.le]
      simp
    rw [Filter.EventuallyEq.iteratedDeriv_eq N heq]
    have hzero : iteratedDeriv N (0 : ℝ → ℂ) x = 0 := by simp
    rw [hzero, norm_zero]
    exact le_of_lt hCpos

end Commons.Analysis.Calculus