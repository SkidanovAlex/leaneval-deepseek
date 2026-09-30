import Mathlib
import Submission.Work.BMF.mr_direct.dupExtraR_defs
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The size of `nnD x` on `pSetDR`

For `x = ⟨⟨j,p⟩,m⟩ ∈ pSetDR K P Q A B` the index `j` runs over `indexSet K P Q`, the prime `p`
lies in the logarithmic window `winPrimes K j = [e^{j/K}, e^{(j+1)/K}]`, and the integer `m`
lies in the range window `winIdxR K A B j = [A e^{-(j+1)/K}, B e^{-j/K}]`.  Multiplying the two
window estimates gives

`A e^{-1/K} ≤ p·m ≤ B e^{1/K}`,

which is exactly the statement below for `nnD x = p·m`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BMF.mr_direct

open Work.BMF.mrDirect

theorem dupExtraR_nnD_bounds (K P Q A B : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∀ x ∈ Work.BMF.mr_direct.pSetDR K P Q A B,
      A * Real.exp (-(1 / K)) ≤ (Work.BMF.mr_direct.nnD x : ℝ) ∧
        (Work.BMF.mr_direct.nnD x : ℝ) ≤ B * Real.exp (1 / K) := by
  intro x hx
  rw [pSetDR] at hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
  rw [pairSetD_eq] at hx1
  obtain ⟨hj, hp⟩ := Finset.mem_sigma.mp hx1
  have hpw : x.1.2 ∈ winPrimes K x.1.1 := (Finset.mem_filter.mp hp).1
  obtain ⟨hpprime, hp1, hp2⟩ := mem_winPrimes.mp hpw
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hBnn : (0 : ℝ) ≤ B := le_trans hApos.le hAB
  have hnn : (0 : ℝ) ≤ B * Real.exp (-(x.1.1 : ℝ) / K) :=
    mul_nonneg hBnn (Real.exp_pos _).le
  obtain ⟨hm1, hm2⟩ := (mem_winIdxR (K := K) (A := A) (B := B) (j := x.1.1)
    (m := x.2) hnn).mp hx2
  have hkey : Real.exp ((x.1.1 : ℝ) / K) * Real.exp (-((x.1.1 : ℝ) + 1) / K)
      = Real.exp (-(1 / K)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hkey2 : Real.exp (((x.1.1 : ℝ) + 1) / K) * Real.exp (-(x.1.1 : ℝ) / K)
      = Real.exp (1 / K) := by
    rw [← Real.exp_add]; congr 1; ring
  constructor
  · have h1 : Real.exp ((x.1.1 : ℝ) / K) * (A * Real.exp (-((x.1.1 : ℝ) + 1) / K))
        ≤ (x.1.2 : ℝ) * (x.2 : ℝ) :=
      mul_le_mul hp1 hm1 (mul_nonneg hApos.le (Real.exp_pos _).le) (Nat.cast_nonneg _)
    calc A * Real.exp (-(1 / K))
        = Real.exp ((x.1.1 : ℝ) / K) * (A * Real.exp (-((x.1.1 : ℝ) + 1) / K)) := by
          rw [← hkey]; ring
      _ ≤ (x.1.2 : ℝ) * (x.2 : ℝ) := h1
      _ = (nnD x : ℝ) := by simp [nnD, Nat.cast_mul]
  · have h2 : (x.1.2 : ℝ) * (x.2 : ℝ)
        ≤ Real.exp (((x.1.1 : ℝ) + 1) / K) * (B * Real.exp (-(x.1.1 : ℝ) / K)) :=
      mul_le_mul hp2 hm2 (Nat.cast_nonneg _) (le_of_lt (Real.exp_pos _))
    calc (nnD x : ℝ) = (x.1.2 : ℝ) * (x.2 : ℝ) := by simp [nnD, Nat.cast_mul]
      _ ≤ Real.exp (((x.1.1 : ℝ) + 1) / K) * (B * Real.exp (-(x.1.1 : ℝ) / K)) := h2
      _ = B * Real.exp (1 / K) := by rw [← hkey2]; ring

end Work.BMF.mr_direct
