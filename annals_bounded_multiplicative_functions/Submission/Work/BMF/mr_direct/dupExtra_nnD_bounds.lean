import Mathlib
import Submission.Work.BMF.mr_direct.dupExtra_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The size of `nnD x` on `pSetD`

For `x = ⟨⟨j,p⟩,m⟩ ∈ pSetD K P Q X` the index `j` runs over `indexSet K P Q`, the prime `p`
lies in the logarithmic window `winPrimes K j = [e^{j/K}, e^{(j+1)/K}]`, and the integer `m`
lies in the window `winIdx K X j = [X e^{-(j+1)/K}, 2X e^{-j/K}]`.  Multiplying the two
window estimates gives

`X e^{-1/K} ≤ p·m ≤ 2X e^{1/K}`,

which is exactly the statement below for `nnD x = p·m`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BMF.mr_direct

theorem dupExtra_nnD_bounds (K P Q X : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∀ x ∈ Work.BMF.mrDirect.pSetD K P Q X,
      X * Real.exp (-(1 / K)) ≤ (Work.BMF.mr_direct.nnD x : ℝ) ∧
        (Work.BMF.mr_direct.nnD x : ℝ) ≤ 2 * X * Real.exp (1 / K) := by
  intro x hx
  rw [Work.BMF.mr_direct.pSetD_eq_sigma] at hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
  rw [Work.BMF.mr_direct.pairSetD_eq] at hx1
  obtain ⟨hj, hp⟩ := Finset.mem_sigma.mp hx1
  have hpw : x.1.2 ∈ Work.BMF.mrDirect.winPrimes K x.1.1 := (Finset.mem_filter.mp hp).1
  obtain ⟨hpprime, hp1, hp2⟩ := Work.BMF.mrDirect.mem_winPrimes.mp hpw
  have hnn : (0 : ℝ) ≤ 2 * X * Real.exp (-(x.1.1 : ℝ) / K) := by
    have : (0 : ℝ) < X := by linarith
    positivity
  obtain ⟨hm1, hm2⟩ :=
    (Work.BMF.mrDirect.mem_winIdx (K := K) (X := X) (j := x.1.1) (m := x.2) hnn).mp hx2
  have hkey : Real.exp ((x.1.1 : ℝ) / K) * Real.exp (-((x.1.1 : ℝ) + 1) / K)
      = Real.exp (-(1 / K)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hkey2 : Real.exp (((x.1.1 : ℝ) + 1) / K) * Real.exp (-((x.1.1 : ℝ)) / K)
      = Real.exp (1 / K) := by
    rw [← Real.exp_add]; congr 1; ring
  constructor
  · have h1 : Real.exp ((x.1.1 : ℝ) / K) * (X * Real.exp (-((x.1.1 : ℝ) + 1) / K))
        ≤ (x.1.2 : ℝ) * (x.2 : ℝ) :=
      mul_le_mul hp1 hm1 (by positivity) (Nat.cast_nonneg _)
    calc X * Real.exp (-(1 / K))
        = Real.exp ((x.1.1 : ℝ) / K) * (X * Real.exp (-((x.1.1 : ℝ) + 1) / K)) := by
          rw [← hkey]; ring
      _ ≤ (x.1.2 : ℝ) * (x.2 : ℝ) := h1
      _ = (Work.BMF.mr_direct.nnD x : ℝ) := by simp [Work.BMF.mr_direct.nnD, Nat.cast_mul]
  · have h2 : (x.1.2 : ℝ) * (x.2 : ℝ)
        ≤ Real.exp (((x.1.1 : ℝ) + 1) / K) * (2 * X * Real.exp (-((x.1.1 : ℝ)) / K)) :=
      mul_le_mul hp2 hm2 (by positivity) (le_of_lt (Real.exp_pos _))
    calc (Work.BMF.mr_direct.nnD x : ℝ)
        = (x.1.2 : ℝ) * (x.2 : ℝ) := by simp [Work.BMF.mr_direct.nnD, Nat.cast_mul]
      _ ≤ Real.exp (((x.1.1 : ℝ) + 1) / K) * (2 * X * Real.exp (-((x.1.1 : ℝ)) / K)) := h2
      _ = 2 * X * Real.exp (1 / K) := by rw [← hkey2]; ring

end Work.BMF.mr_direct
