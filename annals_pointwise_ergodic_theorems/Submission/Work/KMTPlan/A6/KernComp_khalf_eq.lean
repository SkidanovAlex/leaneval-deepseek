/-
# The composed kernel of the halved average (`KernComp_khalf_eq`)

The kernel calculus of `Work.KMTAreas.A7` composes a bilinear kernel `K` with two linear
convolution kernels `κ`, `κ'` by

  `kernComp K κ κ' a b = ∑' a' ∑' b' K (a - a') (b - b') * κ a' * κ' b'`

(see `ModelOps`).  This file evaluates `kernComp` for `K = khalf N P`, the *finite* kernel of the
halved (upper-half) average

  `khalf N P a b = N⁻¹` if `N/2 < a ≤ N` and `b = P.eval a`, and `0` otherwise.

Because `khalf N P a b` vanishes unless `b = P.eval a`, the inner sum over `b'` collapses to the
single term `b' = j - P.eval (i - a')`, and the remaining (finitely supported) sum over `a' : ℤ`
is the sum over the integers `a' = i - n`, `n ∈ Ioc (N/2) N`:

  `kernComp (khalf N P) κ κ' i j = N⁻¹ * ∑_{n ∈ Ioc (N/2) N} κ (i - n) * κ' (j - P.eval n)`.

This is the form in which the §6/§7 functional calculus
`B_{M·(ψ₁⊗ψ₂)}(u,v) = B_M(T_{ψ₁}u, T_{ψ₂}v)` is evaluated: the composed kernel of the halved
average with the two Ionescu–Wainger multiplier kernels.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.BilinOpKhalf

namespace Work.KMTPlan.A6

/-- The composed kernel `kernComp (khalf N P) κ κ'` of the halved average with the two linear
convolution kernels `κ`, `κ'`: the inner sum over the second variable collapses onto the graph
`b = P.eval a` of `P`, and the outer sum is the finite sum over `n ∈ Ioc (N/2) N`. -/
theorem KernComp_khalf_eq (κ κ' : ℤ → ℂ) (N : ℕ) (P : Polynomial ℤ) (i j : ℤ) :
    Work.KMTAreas.A7.kernComp (Work.KMTAreas.A7.khalf N P) κ κ' i j
      = ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          κ (i - (n : ℤ)) * κ' (j - P.eval (n : ℤ)) := by
  -- `khalf` at a point of the graph of `P` is the indicator of `N/2 < a ≤ N`, scaled by `N⁻¹`.
  have hk : ∀ a : ℤ, Work.KMTAreas.A7.khalf N P a (P.eval a)
      = (if (N:ℤ)/2 < a ∧ a ≤ (N:ℤ) then ((N:ℂ))⁻¹ else 0) := by
    intro a
    unfold Work.KMTAreas.A7.khalf
    by_cases h : (N:ℤ)/2 < a ∧ a ≤ (N:ℤ)
    · rw [if_pos ⟨h.1, h.2, rfl⟩, if_pos h]
    · rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩), if_neg h]
  -- Inner collapse: for fixed `a'`, only `b' = j - P.eval (i - a')` contributes.
  have hinner : ∀ a' : ℤ,
      (∑' b' : ℤ, Work.KMTAreas.A7.khalf N P (i - a') (j - b') * κ a' * κ' b')
        = (if (N:ℤ)/2 < i - a' ∧ i - a' ≤ (N:ℤ) then ((N:ℂ))⁻¹ else 0)
            * κ a' * κ' (j - P.eval (i - a')) := by
    intro a'
    rw [tsum_eq_single (j - P.eval (i - a'))]
    · have hjj : j - (j - P.eval (i - a')) = P.eval (i - a') := by ring
      rw [hjj, hk]
    · intro b' hb'
      have hc : ¬((N:ℤ)/2 < i - a' ∧ i - a' ≤ (N:ℤ) ∧ j - b' = P.eval (i - a')) := by
        rintro ⟨-, -, hjj⟩
        exact hb' (by omega)
      unfold Work.KMTAreas.A7.khalf
      rw [if_neg hc]
      ring
  rw [Work.KMTAreas.A7.kernComp]
  simp_rw [hinner]
  -- Outer sum: the (finitely supported) sum over `a' : ℤ` is the sum over the image of
  -- `n ↦ i - n`, `n ∈ Ioc (N/2) N`.
  rw [tsum_eq_sum (s := (Finset.Ioc (N / 2) N).image (fun n : ℕ => i - (n : ℤ)))]
  · rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hn' : N / 2 < n ∧ n ≤ N := Finset.mem_Ioc.mp hn
      have hcast : i - (i - (n : ℤ)) = (n : ℤ) := by ring
      rw [hcast]
      have hnd : ((N/2 : ℕ) : ℤ) = (N:ℤ)/2 := Int.natCast_div N 2
      have hcond : (N:ℤ)/2 < (n:ℤ) ∧ (n:ℤ) ≤ (N:ℤ) := by
        refine ⟨?_, ?_⟩
        · rw [← hnd]; exact_mod_cast hn'.1
        · exact_mod_cast hn'.2
      rw [if_pos hcond]
      ring
    · intro x hx y hy hxy
      have hxy' : i - (x:ℤ) = i - (y:ℤ) := hxy
      have : (x:ℤ) = (y:ℤ) := by omega
      exact_mod_cast this
  · intro a' ha'
    by_cases h : (N:ℤ)/2 < i - a' ∧ i - a' ≤ (N:ℤ)
    · exfalso
      apply ha'
      rw [Finset.mem_image]
      refine ⟨(i - a').toNat, ?_, ?_⟩
      · rw [Finset.mem_Ioc]
        have h0 : 0 ≤ i - a' :=
          le_of_lt (lt_of_le_of_lt (Int.ediv_nonneg (Int.natCast_nonneg N) (by norm_num)) h.1)
        have hcast : ((i - a').toNat : ℤ) = i - a' := Int.toNat_of_nonneg h0
        refine ⟨?_, ?_⟩
        · have hnd : ((N/2 : ℕ) : ℤ) = (N:ℤ)/2 := Int.natCast_div N 2
          have : ((N/2 : ℕ) : ℤ) < ((i - a').toNat : ℤ) := by rw [hnd, hcast]; exact h.1
          exact_mod_cast this
        · rw [Int.toNat_le]; exact h.2
      · rw [Int.toNat_of_nonneg]
        · ring
        · exact le_of_lt (lt_of_le_of_lt (Int.ediv_nonneg (Int.natCast_nonneg N) (by norm_num)) h.1)
    · rw [if_neg h]
      ring

end Work.KMTPlan.A6
