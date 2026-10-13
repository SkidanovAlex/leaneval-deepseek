/-
# `Work.FTS.PhiStar.FlatWAux.QmDeriv.Sup` — sup bounds for `gC`, `gC'` and `Qm`

Support module for `QmDerivBound`: the sup bound `|gC (2m+1) x| ≤ Npsi m/2` on `[-1,1]`
(from the trig expansion, all coefficients being nonnegative), the Schur–Gegenbauer bound
`|gC' (x)| ≤ Npsi m/(1-x)` on `[0,1)`, and the resulting sup bound `|Qm m θ| ≤ 100 (2m+1)²`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.FlatWAux.QmDeriv.Trig
import Submission.Work.FTS.PhiStar.Series.Deleg.psiAngDefs
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.FlatWAux.gC_eq_famTrig

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

open Set Filter MeasureTheory

theorem gC_abs_le_half_Npsi {m : ℕ} {x : ℝ} (hx : |x| ≤ 1) :
    |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x|
      ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m / 2 := by
  have hx1 : -1 ≤ x := by linarith [neg_abs_le x, hx]
  have hx2 : x ≤ 1 := by linarith [le_abs_self x, hx]
  have hcos : Real.cos (Real.pi / 2 - Real.arcsin x) = x := by
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sin_arcsin hx1 hx2]
    ring
  rw [← hcos, gC_eq_famTrig, Work.FTS.PhiStar.famTrig]
  have hsum : (∑ j ∈ Finset.range (2 * m + 1 + 1),
        Work.FTS.PhiStar.famC (j : ℤ)
          * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ)))
      = Work.FTS.PhiStar.Series.Deleg.Npsi m / 2 := by
    have h1 : Work.FTS.PhiStar.famTrig (2 * m + 1) 0
        = ∑ j ∈ Finset.range (2 * m + 1 + 1),
            Work.FTS.PhiStar.famC (j : ℤ)
              * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ)) := by
      rw [Work.FTS.PhiStar.famTrig]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_zero, Real.cos_zero, mul_one]
    rw [← h1, ← gC_eq_famTrig (2 * m + 1) 0, Real.cos_zero,
      Work.FTS.PhiStar.Series.Deleg.gC_one]
    unfold Work.FTS.PhiStar.Series.Deleg.Npsi
    push_cast
    ring
  calc |∑ j ∈ Finset.range (2 * m + 1 + 1),
        Work.FTS.PhiStar.famC (j : ℤ)
          * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ))
          * Real.cos (((2 : ℝ) * (j : ℝ) - (((2 * m + 1 : ℕ) : ℝ)))
              * (Real.pi / 2 - Real.arcsin x))|
      ≤ ∑ j ∈ Finset.range (2 * m + 1 + 1),
          |Work.FTS.PhiStar.famC (j : ℤ)
            * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ))
            * Real.cos (((2 : ℝ) * (j : ℝ) - (((2 * m + 1 : ℕ) : ℝ)))
                * (Real.pi / 2 - Real.arcsin x))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (2 * m + 1 + 1),
          Work.FTS.PhiStar.famC (j : ℤ)
            * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (famC_nonneg _), abs_of_nonneg (famC_nonneg _)]
        exact mul_le_of_le_one_right (mul_nonneg (famC_nonneg _) (famC_nonneg _))
          (abs_cos_le_one' _)
    _ = Work.FTS.PhiStar.Series.Deleg.Npsi m / 2 := hsum

theorem gC_deriv_le {m : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x|
      ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m / (1 - x) := by
  have hNp := Work.FTS.PhiStar.Series.Deleg.Npsi_pos m
  have hdu : |deriv (Work.FTS.PhiStar.Series.Deleg.ug m) x|
      ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m := by
    have h := Work.FTS.PhiStar.Series.Deleg.du_bound m ⟨hx0, le_of_lt hx1⟩
    have h2 : Real.sqrt ((deriv (Work.FTS.PhiStar.Series.Deleg.ug m) x) ^ 2)
        ≤ Real.sqrt (Work.FTS.PhiStar.Series.Deleg.Npsi m ^ 2) := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (le_of_lt hNp)] at h2
  have hg : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x|
      ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m / 2 :=
    gC_abs_le_half_Npsi (by rw [abs_of_nonneg hx0]; exact le_of_lt hx1)
  have hden : 0 < 1 - x := by linarith
  have hkey : (1 - x ^ 2) * deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x
      = deriv (Work.FTS.PhiStar.Series.Deleg.ug m) x
        + 2 * x * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x := by
    rw [Work.FTS.PhiStar.Series.Deleg.deriv_ug m x]
    ring
  have hbound : (1 - x ^ 2) * |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x|
      ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m * (1 + x) := by
    rw [← abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 1 - x ^ 2), ← abs_mul, hkey]
    calc |deriv (Work.FTS.PhiStar.Series.Deleg.ug m) x
          + 2 * x * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x|
        ≤ |deriv (Work.FTS.PhiStar.Series.Deleg.ug m) x|
          + |2 * x * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x| := abs_add_le _ _
      _ ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m
          + 2 * x * (Work.FTS.PhiStar.Series.Deleg.Npsi m / 2) := by
          refine add_le_add hdu ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hx0]
          exact mul_le_mul_of_nonneg_left hg (by positivity)
      _ = Work.FTS.PhiStar.Series.Deleg.Npsi m * (1 + x) := by ring
  rw [le_div_iff₀ hden]
  have hfac : (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) := by ring
  have hpos : 0 < 1 + x := by linarith
  have h4 : (1 - x) * |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x|
      ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m := by
    have h := hbound
    rw [hfac] at h
    rw [show (1 - x) * (1 + x) * |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x|
          = ((1 - x) * |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x|) * (1 + x) from by
      ring] at h
    by_contra hcon
    push_neg at hcon
    nlinarith [h, hpos, hcon]
  rwa [mul_comm] at h4

theorem gC_abs_le_mul {m : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ Real.sqrt 2 / 2) :
    |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) y|
      ≤ 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * y := by
  have hquarter : (1 : ℝ) / 4 ≤ 1 - Real.sqrt 2 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsq : Real.sqrt 2 / 2 < 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hM : ∀ z ∈ Icc (0 : ℝ) (Real.sqrt 2 / 2),
      |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) z|
        ≤ 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m := by
    intro z hz
    have hz1 : z < 1 := by linarith [hz.2, hsq]
    have h1 : |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) z|
        ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m / (1 - z) := gC_deriv_le hz.1 hz1
    have hden : 0 < 1 - z := by linarith [hz.2, hsq]
    have hz4 : (1 : ℝ) / 4 ≤ 1 - z := by linarith [hz.2, hquarter]
    have h2 : Work.FTS.PhiStar.Series.Deleg.Npsi m / (1 - z)
        ≤ 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m := by
      rw [div_le_iff₀ hden]
      nlinarith [Work.FTS.PhiStar.Series.Deleg.Npsi_pos m, hz4]
    linarith
  have hG0 : Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0 = 0 :=
    Work.FTS.PhiStar.Series.gC_odd_zero m
  have hGdiff : Differentiable ℝ (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) :=
    Work.FTS.PhiStar.Series.Deleg.differentiable_gC (2 * m + 1)
  have hmono1 : MonotoneOn (fun z : ℝ => 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * z
      - Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) z) (Icc 0 (Real.sqrt 2 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact ((continuous_const.mul continuous_id).sub hGdiff.continuous).continuousOn
    · exact ((differentiable_const _).mul differentiable_id |>.sub hGdiff).differentiableOn
    · intro z hz
      have hz' : z ∈ Icc (0 : ℝ) (Real.sqrt 2 / 2) := interior_subset hz
      have hd : HasDerivAt (fun z' : ℝ => 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * z'
          - Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) z')
          (4 * Work.FTS.PhiStar.Series.Deleg.Npsi m
            - deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) z) z := by
        have h1 : HasDerivAt (fun z' : ℝ => 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * z')
            (4 * Work.FTS.PhiStar.Series.Deleg.Npsi m) z := by
          simpa using (hasDerivAt_id z).const_mul (4 * Work.FTS.PhiStar.Series.Deleg.Npsi m)
        exact h1.sub hGdiff.differentiableAt.hasDerivAt
      rw [hd.deriv]
      have h := hM z hz'
      rw [abs_le] at h
      linarith [h.2]
  have hmono2 : MonotoneOn (fun z : ℝ => 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * z
      + Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) z) (Icc 0 (Real.sqrt 2 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact ((continuous_const.mul continuous_id).add hGdiff.continuous).continuousOn
    · exact ((differentiable_const _).mul differentiable_id |>.add hGdiff).differentiableOn
    · intro z hz
      have hz' : z ∈ Icc (0 : ℝ) (Real.sqrt 2 / 2) := interior_subset hz
      have hd : HasDerivAt (fun z' : ℝ => 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * z'
          + Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) z')
          (4 * Work.FTS.PhiStar.Series.Deleg.Npsi m
            + deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) z) z := by
        have h1 : HasDerivAt (fun z' : ℝ => 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * z')
            (4 * Work.FTS.PhiStar.Series.Deleg.Npsi m) z := by
          simpa using (hasDerivAt_id z).const_mul (4 * Work.FTS.PhiStar.Series.Deleg.Npsi m)
        exact h1.add hGdiff.differentiableAt.hasDerivAt
      rw [hd.deriv]
      have h := hM z hz'
      rw [abs_le] at h
      linarith [h.1]
  have hy : y ∈ Icc (0 : ℝ) (Real.sqrt 2 / 2) := ⟨hy0, hy1⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.sqrt 2 / 2) := ⟨le_refl 0, by positivity⟩
  have h1 : Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) y
      ≤ 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * y := by
    have h := hmono1 h0 hy hy0
    change 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * 0
        - Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0
      ≤ 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * y
        - Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) y at h
    rw [hG0, mul_zero, sub_zero] at h
    linarith [h]
  have h2 : -Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) y
      ≤ 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * y := by
    have h := hmono2 h0 hy hy0
    change 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * 0
        + Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0
      ≤ 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * y
        + Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) y at h
    rw [hG0, mul_zero, add_zero] at h
    linarith [h]
  rw [abs_le]
  exact ⟨by linarith [h2], h1⟩

theorem Qm_sup_bound {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    |Qm m θ| ≤ 100 * (2 * (m : ℝ) + 1) ^ 2 := by
  have hN : Work.FTS.PhiStar.Series.Deleg.Npsi m ≤ 4 * (2 * (m : ℝ) + 1) ^ 2 := by
    unfold Work.FTS.PhiStar.Series.Deleg.Npsi
    have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hNpos := Work.FTS.PhiStar.Series.Deleg.Npsi_pos m
  have hnn : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by positivity
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  rw [Qm_eq hθ, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.sin θ)]
  by_cases hcase : Real.sqrt 2 / 2 ≤ Real.sin θ
  · have h1 : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)|
        ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m / 2 :=
      gC_abs_le_half_Npsi (by rw [abs_of_nonneg (le_of_lt hsin)]; exact Real.sin_le_one θ)
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have h3 : (1 : ℝ) / 2 ≤ 2 * Real.sin θ := by linarith
    have h4 : Work.FTS.PhiStar.Series.Deleg.Npsi m / 2
        ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m * (2 * Real.sin θ) := by
      have := mul_le_mul_of_nonneg_left h3 (le_of_lt hNpos)
      linarith [this]
    have h5 : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)|
          / (2 * Real.sin θ) ≤ Work.FTS.PhiStar.Series.Deleg.Npsi m := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Real.sin θ)]
      linarith [h1, h4]
    linarith [h5, hN, hnn]
  · have hlt : Real.sin θ ≤ Real.sqrt 2 / 2 := le_of_lt (lt_of_not_ge hcase)
    have h1 : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)|
        ≤ 4 * Work.FTS.PhiStar.Series.Deleg.Npsi m * Real.sin θ :=
      gC_abs_le_mul (le_of_lt hsin) hlt
    have h2 : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| / (2 * Real.sin θ)
        ≤ 2 * Work.FTS.PhiStar.Series.Deleg.Npsi m := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Real.sin θ)]
      nlinarith [h1, hsin]
    linarith [h2, hN, hnn, hNpos]

end Work.FTS.PhiStar.FlatWAux
