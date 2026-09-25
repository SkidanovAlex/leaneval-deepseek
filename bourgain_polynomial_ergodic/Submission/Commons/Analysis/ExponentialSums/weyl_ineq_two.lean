import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test
import Submission.Commons.Analysis.ExponentialSums.iterated_differencing_step

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
open scoped BigOperators ComplexConjugate
open Complex Finset

namespace Commons.Analysis.ExponentialSums
noncomputable section


def wdE (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

lemma wdE_norm (t : ℝ) : ‖wdE t‖ = 1 := by
  rw [wdE]
  simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)

lemma wdE_add (s t : ℝ) : wdE (s + t) = wdE s * wdE t := by
  rw [wdE, wdE, wdE, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma wdE_star (t : ℝ) : star (wdE t) = wdE (-t) := by
  rw [wdE, wdE]
  have h := Complex.exp_conj (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
  rw [show (starRingEnd ℂ) (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        = (((2 * Real.pi * -t : ℝ) : ℂ) * Complex.I) from by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring] at h
  exact h.symm

lemma wdE_mul_star (s t : ℝ) : wdE s * star (wdE t) = wdE (s - t) := by
  rw [wdE_star, ← wdE_add]
  congr 1

lemma wdE_linPhase (α : ℝ) (n : ℕ) : wdE (α * (n:ℝ)) = Submission.VanDerCorput.linPhase α n := by
  rw [wdE, Submission.VanDerCorput.linPhase]

lemma wd_sum_Icc_one_eq_sum_range {γ : Type*} [AddCommMonoid γ] (n : ℕ) (f : ℕ → γ) :
    (∑ h ∈ Finset.Icc 1 n, f h) = ∑ h ∈ Finset.range n, f (h+1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc (1:ℕ) n, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg f (by omega)

lemma wd_sum_range_sub_shift (L : ℕ) (f : ℕ → ℝ) :
    (∑ h ∈ Finset.range L, f h) - (∑ h ∈ Finset.range L, f (h+1)) = f 0 - f L := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hL)
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    ring

lemma wd_norm_sum_sq_eq (L : ℕ) (w : ℕ → ℂ) :
    ‖∑ x ∈ Finset.range L, w x‖ ^ 2
      = 2 * (∑ h ∈ Finset.range L,
              (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re)
        - ∑ x ∈ Finset.range L, ‖w x‖ ^ 2 := by
  have hW : (∑ p ∈ (Finset.range L ×ˢ Finset.range L), w p.1 * star (w p.2))
      = ((‖∑ x ∈ Finset.range L, w x‖ ^ 2 : ℝ) : ℂ) := by
    have hprod : (∑ p ∈ (Finset.range L ×ˢ Finset.range L), w p.1 * star (w p.2))
        = ∑ x ∈ Finset.range L, ∑ y ∈ Finset.range L, w x * star (w y) := by
      rw [Finset.sum_product]
    rw [hprod, ← Finset.sum_mul_sum, ← star_sum, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rfl
  have hcomplex : ((‖∑ x ∈ Finset.range L, w x‖ ^ 2 : ℝ) : ℂ)
      = (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x))
        + star (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x))
        - ∑ x ∈ Finset.range L, w x * star (w x) := by
    rw [← hW, sum_triangle_split, sum_Bge_eq, sum_Ble_eq, sum_Beq_eq]
  have hD_re : ((∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x))).re
      = ∑ h ∈ Finset.range L,
          (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re :=
    Complex.re_sum _ _
  have hC0_re : ((∑ x ∈ Finset.range L, w x * star (w x))).re
      = ∑ x ∈ Finset.range L, ‖w x‖ ^ 2 := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hx : w x * star (w x) = ((Complex.normSq (w x) : ℝ) : ℂ) := by
      simpa using Complex.mul_conj (w x)
    rw [hx, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have h1 := congrArg Complex.re hcomplex
  simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re] at h1
  have hsr : (star (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x))).re
      = (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re :=
    Complex.conj_re _
  rw [hsr, hD_re, hC0_re] at h1
  rw [h1, two_mul]

end
end Commons.Analysis.ExponentialSums

namespace Commons.Analysis.ExponentialSums
open scoped BigOperators ComplexConjugate
open Complex Finset
noncomputable section

lemma wd_mul_star_eq_one (w : ℂ) (hw : ‖w‖ = 1) : w * star w = 1 := by
  have h := Complex.mul_conj w
  rw [Complex.normSq_eq_norm_sq, hw] at h
  norm_num at h
  simpa using h

lemma wd_weyl_sq_eq (L : ℕ) (w : ℕ → ℂ) (hw : ∀ x, ‖w x‖ = 1) :
    ‖∑ x ∈ Finset.range L, w x‖ ^ 2
      = (L:ℝ) + 2 * ∑ h ∈ Finset.Icc 1 L,
          (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re := by
  have hnorm : (∑ x ∈ Finset.range L, ‖w x‖ ^ 2) = (L:ℝ) := by
    rw [show (∑ x ∈ Finset.range L, ‖w x‖ ^ 2) = ∑ _x ∈ Finset.range L, (1:ℝ) from by
      apply Finset.sum_congr rfl; intro x _; rw [hw x]; norm_num]
    simp
  have hre := wd_norm_sum_sq_eq L w
  rw [hre, hnorm]
  rw [wd_sum_Icc_one_eq_sum_range L (fun h => (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re)]
  have htel := wd_sum_range_sub_shift L (fun h => (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re)
  have hf0 : (∑ x ∈ Finset.range (L - 0), w (x + 0) * star (w x)).re = (L:ℝ) := by
    rw [Nat.sub_zero]
    have : (∑ x ∈ Finset.range L, w (x + 0) * star (w x)) = (L:ℂ) := by
      rw [show (∑ x ∈ Finset.range L, w (x + 0) * star (w x)) = ∑ _x ∈ Finset.range L, (1:ℂ) from by
        apply Finset.sum_congr rfl; intro x _; rw [Nat.add_zero]; exact wd_mul_star_eq_one (w x) (hw x)]
      simp
    rw [this]; simp
  have hfL : (∑ x ∈ Finset.range (L - L), w (x + L) * star (w x)).re = 0 := by
    rw [Nat.sub_self]; simp
  linarith [htel, hf0, hfL]

end
end Commons.Analysis.ExponentialSums

namespace Commons.Analysis.ExponentialSums
open scoped BigOperators ComplexConjugate
open Complex Finset
noncomputable section

def wdWfn (α β : ℝ) (x : ℕ) : ℂ := wdE (α * ((x:ℝ)+1) + β * ((x:ℝ)+1)^2)

example (α β : ℝ) (h x : ℕ) :
    wdWfn α β (x + h) * star (wdWfn α β x)
      = wdE ((h:ℝ) * (α + β * (h:ℝ)))
          * (wdE (2 * β * (h:ℝ)) * Submission.VanDerCorput.linPhase (2 * β * (h:ℝ)) x) := by
  unfold wdWfn
  rw [wdE_mul_star, ← wdE_linPhase]
  rw [← wdE_add, ← wdE_add]
  congr 1
  push_cast
  ring

end
end Commons.Analysis.ExponentialSums

namespace Commons.Analysis.ExponentialSums
open scoped BigOperators ComplexConjugate
open Complex Finset
noncomputable section

lemma wdWfn_mul_star (α β : ℝ) (h x : ℕ) :
    wdWfn α β (x + h) * star (wdWfn α β x)
      = wdE ((h:ℝ) * (α + β * (h:ℝ)))
          * (wdE (2 * β * (h:ℝ)) * Submission.VanDerCorput.linPhase (2 * β * (h:ℝ)) x) := by
  unfold wdWfn
  rw [wdE_mul_star, ← wdE_linPhase]
  rw [← wdE_add, ← wdE_add]
  congr 1
  push_cast
  ring

lemma wdDeq (α β : ℝ) (h M : ℕ) :
    (∑ x ∈ Finset.range (M - h), wdWfn α β (x + h) * star (wdWfn α β x))
      = wdE ((h:ℝ) * (α + β * (h:ℝ)))
          * (wdE (2 * β * (h:ℝ))
              * ∑ x ∈ Finset.range (M - h), Submission.VanDerCorput.linPhase (2 * β * (h:ℝ)) x) := by
  rw [Finset.sum_congr rfl (fun x _ => wdWfn_mul_star α β h x)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

lemma wdDnorm (α β : ℝ) (h M : ℕ) :
    ‖∑ x ∈ Finset.range (M - h), wdWfn α β (x + h) * star (wdWfn α β x)‖
      = ‖∑ x ∈ Finset.range (M - h), Submission.VanDerCorput.linPhase (2 * β * (h:ℝ)) x‖ := by
  rw [wdDeq, norm_mul, norm_mul, wdE_norm, wdE_norm]
  simp

lemma wdD_le (α β : ℝ) (h M : ℕ) :
    ‖∑ x ∈ Finset.range (M - h), wdWfn α β (x + h) * star (wdWfn α β x)‖
      ≤ (if Submission.VanDerCorput.intDist (2 * β * (h:ℝ)) = 0 then (M:ℝ)
          else min (M:ℝ) ((1/2)/Submission.VanDerCorput.intDist (2 * β * (h:ℝ)))) := by
  rw [wdDnorm]
  have htriv := Submission.VanDerCorput.linPhase_trivial (2 * β * (h:ℝ)) (M-h)
  have hMh : ((M-h:ℕ):ℝ) ≤ (M:ℝ) := by exact_mod_cast Nat.sub_le M h
  by_cases h0 : Submission.VanDerCorput.intDist (2 * β * (h:ℝ)) = 0
  · rw [if_pos h0]
    exact le_trans htriv hMh
  · rw [if_neg h0]
    have hpos : 0 < Submission.VanDerCorput.intDist (2 * β * (h:ℝ)) :=
      lt_of_le_of_ne' (Submission.VanDerCorput.intDist_nonneg _) h0
    have hgeom := Submission.UnitCircle.geom_sum_bound_of_intDist_pos
      (α := 2 * β * (h:ℝ)) (L := M-h) hpos
    exact le_min (le_trans htriv hMh) hgeom

end
end Commons.Analysis.ExponentialSums

namespace Commons.Analysis.ExponentialSums
open scoped BigOperators ComplexConjugate
open Complex Finset
noncomputable section

theorem weyl_ineq_two (M : ℕ) (hM : 1 ≤ M) (α β : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 M,
        Complex.exp (((2 * Real.pi * (α * (m : ℝ) + β * (m : ℝ) ^ 2) : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ (M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 M,
          (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 then (M : ℝ)
           else min (M : ℝ) ((1 / 2) / Submission.VanDerCorput.intDist (2 * β * (h : ℝ)))) := by
  have hw : ∀ x : ℕ, ‖wdWfn α β x‖ = 1 := fun x => by rw [wdWfn]; exact wdE_norm _
  have hreindex : (∑ m ∈ Finset.Icc 1 M,
        Complex.exp (((2 * Real.pi * (α * (m : ℝ) + β * (m : ℝ) ^ 2) : ℝ) : ℂ) * Complex.I))
      = ∑ x ∈ Finset.range M, wdWfn α β x := by
    rw [wd_sum_Icc_one_eq_sum_range M
      (fun m => Complex.exp (((2 * Real.pi * (α * (m : ℝ) + β * (m : ℝ) ^ 2) : ℝ) : ℂ) * Complex.I))]
    apply Finset.sum_congr rfl
    intro x _
    simp only [wdWfn, wdE]
    congr 1
    push_cast
    ring
  rw [hreindex]
  rw [wd_weyl_sq_eq M (wdWfn α β) hw]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro h hh
  exact le_trans (Complex.re_le_norm _) (wdD_le α β h M)

end
end Commons.Analysis.ExponentialSums
