import Mathlib
import Submission.Work.FIArea4.geom_sum_bound
import Submission.Work.FIArea4.pv_geom_bound
import Submission.Work.FIArea4.norm_stdAddChar_sub_one_lower
import Submission.Work.FIArea4.sum_filter_ne_zero_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Work.FIArea4

/-- Sum over the non-trivial additive characters of `ZMod q` of the exponential partial sums:
`∑_{j ≠ 0} ‖∑_{n=1}^{X} stdAddChar (j * n)‖ ≤ q * (2 + log q)`. -/
theorem pv_exp_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q) (X : ℕ) :
    ∑ j ∈ Finset.univ.filter (fun j : ZMod q => j ≠ 0),
        ‖∑ n ∈ Finset.Icc 1 X, ZMod.stdAddChar (j * (n : ZMod q))‖
      ≤ (q : ℝ) * (2 + Real.log q) := by
  rw [sum_filter_ne_zero_eq q (fun j => ‖∑ n ∈ Finset.Icc 1 X, ZMod.stdAddChar (j * (n : ZMod q))‖)]
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hterm : ∀ a ∈ Finset.Icc 1 (q - 1),
      ‖∑ n ∈ Finset.Icc 1 X, ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖
        ≤ (q : ℝ) / (2 * ((min a (q - a) : ℕ) : ℝ)) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have haq : a ≤ q := by omega
    have hlt : a < q := by omega
    have haz : (a : ZMod q) ≠ 0 := by
      rw [← ZMod.val_ne_zero, ZMod.val_cast_of_lt hlt]
      omega
    have hg := pv_geom_bound (a : ZMod q) haz X
    have hl := norm_stdAddChar_sub_one_lower (q := q) haq
    have hMpos : (0:ℝ) < ((min a (q - a) : ℕ) : ℝ) := by
      have h1 : 1 ≤ min a (q-a) := le_min ha1 (by omega)
      exact_mod_cast (by omega : 0 < min a (q-a))
    have step1 : 2 / ‖ZMod.stdAddChar (a : ZMod q) - 1‖
        ≤ 2 / (4 * ((min a (q - a) : ℕ) : ℝ) / q) := by
      apply div_le_div_of_nonneg_left (by norm_num) _ hl
      positivity
    have step2 : 2 / (4 * ((min a (q - a) : ℕ) : ℝ) / q)
        = (q:ℝ) / (2 * ((min a (q - a) : ℕ) : ℝ)) := by
      have hm : ((min a (q - a) : ℕ) : ℝ) ≠ 0 := ne_of_gt hMpos
      have hqn : (q:ℝ) ≠ 0 := ne_of_gt hq0
      field_simp
      ring
    exact le_trans hg (le_trans step1 (le_of_eq step2))
  have hT : ∑ a ∈ Finset.Icc 1 (q-1), (1:ℝ)/((min a (q-a):ℕ):ℝ) ≤ 2 * (1 + Real.log q) := by
    have hpoint : ∀ a ∈ Finset.Icc 1 (q-1),
        (1:ℝ)/((min a (q-a):ℕ):ℝ) ≤ (1:ℝ)/(a:ℝ) + 1/((q-a:ℕ):ℝ) := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      obtain ⟨ha1, ha2⟩ := ha
      rcases le_total a (q - a) with h | h
      · have hmin : min a (q - a) = a := Nat.min_eq_left h
        rw [hmin]
        have hpos : (0:ℝ) ≤ 1/((q-a:ℕ):ℝ) := by
          have h1 : (0:ℝ) < ((q-a:ℕ):ℝ) := by
            have : 0 < q - a := by omega
            exact_mod_cast this
          positivity
        linarith
      · have hmin : min a (q - a) = q - a := Nat.min_eq_right h
        rw [hmin]
        have hpos : (0:ℝ) ≤ 1/(a:ℝ) := by positivity
        linarith
    have hreflect : ∑ a ∈ Finset.Icc 1 (q-1), (1:ℝ)/((q-a:ℕ):ℝ)
        = ∑ b ∈ Finset.Icc 1 (q-1), (1:ℝ)/(b:ℝ) := by
      refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
      · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
      · intro a1 ha1 a2 ha2 h; rw [Finset.mem_Icc] at ha1 ha2; omega
      · intro b hb
        rw [Finset.mem_Icc] at hb
        exact ⟨q - b, by rw [Finset.mem_Icc]; omega, by omega⟩
      · intro a ha; rfl
    have hH : ∑ a ∈ Finset.Icc 1 (q-1), (1:ℝ)/(a:ℝ) = (harmonic (q-1) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      simp [one_div]
    have hlog : Real.log ((q-1:ℕ):ℝ) ≤ Real.log q := by
      apply Real.log_le_log
      · exact_mod_cast (by omega : 0 < (q-1:ℕ))
      · exact_mod_cast (by omega : (q-1:ℕ) ≤ q)
    calc ∑ a ∈ Finset.Icc 1 (q-1), (1:ℝ)/((min a (q-a):ℕ):ℝ)
        ≤ ∑ a ∈ Finset.Icc 1 (q-1), ((1:ℝ)/(a:ℝ) + 1/((q-a:ℕ):ℝ)) := Finset.sum_le_sum hpoint
      _ = ∑ a ∈ Finset.Icc 1 (q-1), (1:ℝ)/(a:ℝ) + ∑ a ∈ Finset.Icc 1 (q-1), (1:ℝ)/((q-a:ℕ):ℝ) := Finset.sum_add_distrib
      _ = ∑ a ∈ Finset.Icc 1 (q-1), (1:ℝ)/(a:ℝ) + ∑ b ∈ Finset.Icc 1 (q-1), (1:ℝ)/(b:ℝ) := by rw [hreflect]
      _ = 2 * (harmonic (q-1) : ℝ) := by rw [hH]; ring
      _ ≤ 2 * (1 + Real.log q) := by
          have h1 := harmonic_le_one_add_log (q-1)
          linarith
  calc ∑ a ∈ Finset.Icc 1 (q - 1), ‖∑ n ∈ Finset.Icc 1 X, ZMod.stdAddChar ((a:ZMod q) * (n:ZMod q))‖
      ≤ ∑ a ∈ Finset.Icc 1 (q - 1), (q:ℝ)/(2 * ((min a (q-a):ℕ):ℝ)) := Finset.sum_le_sum hterm
    _ = (q:ℝ)/2 * ∑ a ∈ Finset.Icc 1 (q - 1), (1:ℝ)/((min a (q-a):ℕ):ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        field_simp
    _ ≤ (q:ℝ)/2 * (2 * (1 + Real.log q)) := by
        apply mul_le_mul_of_nonneg_left hT
        positivity
    _ ≤ (q:ℝ) * (2 + Real.log q) := by
        have hlq : (0:ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
        nlinarith

end Work.FIArea4
