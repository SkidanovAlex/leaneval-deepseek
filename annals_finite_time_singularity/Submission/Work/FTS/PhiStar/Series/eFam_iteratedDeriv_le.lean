import Mathlib
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.FlatWAux.gC_eq_famTrig
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.QmDeriv.Expansion =====
section

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

theorem Qm_expansion {m : ℕ} {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    Qm m θ = (1 / 2) * ∑ j ∈ Finset.range (2 * m + 1 + 1),
        Work.FTS.PhiStar.famC (j : ℤ)
          * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ))
          * (Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2))
              * (Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * θ) / Real.sin θ)) := by
  have hcos : Real.cos (Real.pi / 2 - θ) = Real.sin θ := by
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hL : Qm m θ
      = Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.cos (Real.pi / 2 - θ))
        / (2 * Real.cos (Real.pi / 2 - θ)) := by
    rw [Qm_eq hθ, ← hcos]
  rw [hL, gC_eq_famTrig, Work.FTS.PhiStar.famTrig]
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (2 : ℝ) * (j : ℝ) - (((2 * m + 1 : ℕ) : ℝ)) = 2 * (j : ℝ) - (2 * (m : ℝ) + 1) from by
    rw [cast_two_mul_add_one m]]
  rw [cos_shift_eq m j θ, hcos]
  field_simp

theorem Qm_expansion_Kern {m : ℕ} {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    Qm m θ = (1 / 2) * ∑ j ∈ Finset.range (2 * m + 1 + 1),
        (Work.FTS.PhiStar.famC (j : ℤ)
          * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ))
          * (Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2))
              * (if j ≤ m then -(1 : ℝ) else 1)))
        * Kern (if j ≤ m then m - j else j - m - 1) θ := by
  rw [Qm_expansion hθ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [sin_div_sin_Kern m j hθ]
  ring

theorem differentiableAt_iteratedDeriv_Kern (l t : ℕ) (θ : ℝ) :
    DifferentiableAt ℝ (iteratedDeriv l (Kern t)) θ := by
  rw [iteratedDeriv_Kern]
  have h2 : DifferentiableAt ℝ (fun θ' : ℝ => ∑ i ∈ Finset.range t,
      (2 * ((i : ℝ) + 1)) ^ l
        * Real.cos (2 * ((i : ℝ) + 1) * θ' + (l : ℝ) * (Real.pi / 2))) θ :=
    differentiableAt_sum_of _ _ θ (fun i _ => (differentiableAt_cos_affine _ _ _).const_mul _)
  exact (differentiableAt_const (if l = 0 then (1 : ℝ) else 0)).add (h2.const_mul 2)

theorem iteratedDeriv_sum_Kern (l : ℕ) (s : Finset ℕ) (d : ℕ → ℝ) (t : ℕ → ℕ) (θ : ℝ) :
    iteratedDeriv l (fun θ' : ℝ => ∑ j ∈ s, d j * Kern (t j) θ') θ
      = ∑ j ∈ s, d j * iteratedDeriv l (Kern (t j)) θ := by
  induction l generalizing θ with
  | zero => simp
  | succ l ih =>
      rw [iteratedDeriv_succ]
      have hcongr : iteratedDeriv l (fun θ' : ℝ => ∑ j ∈ s, d j * Kern (t j) θ')
          = fun θ' : ℝ => ∑ j ∈ s, d j * iteratedDeriv l (Kern (t j)) θ' :=
        funext (fun θ' => ih θ')
      rw [hcongr]
      rw [deriv_sum_of (fun j θ' => d j * iteratedDeriv l (Kern (t j)) θ')
        (fun j => d j * deriv (iteratedDeriv l (Kern (t j))) θ) s θ
        (fun j _ => (differentiableAt_iteratedDeriv_Kern l (t j) θ).hasDerivAt.const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [← iteratedDeriv_succ]

theorem iteratedDeriv_sum_Kern_le (l N : ℕ) (D : ℕ → ℝ) (t : ℕ → ℕ) (θ : ℝ) :
    |iteratedDeriv l (fun θ' : ℝ => ∑ j ∈ Finset.range N, D j * Kern (t j) θ') θ|
      ≤ ∑ j ∈ Finset.range N,
          |D j| * (2 ^ (2 * l + 2) * (2 * (t j : ℝ) + 1) ^ (l + 1)) := by
  rw [iteratedDeriv_sum_Kern]
  calc |∑ j ∈ Finset.range N, D j * iteratedDeriv l (Kern (t j)) θ|
      ≤ ∑ j ∈ Finset.range N, |D j * iteratedDeriv l (Kern (t j)) θ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N,
          |D j| * (2 ^ (2 * l + 2) * (2 * (t j : ℝ) + 1) ^ (l + 1)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (Kern_bound l (t j) θ) (abs_nonneg _)

theorem Qm_iteratedDeriv_bound {m l : ℕ} (hm : 1 ≤ m) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    |iteratedDeriv l (Qm m) θ| ≤ 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 3) := by
  let D : ℕ → ℝ := fun j => Work.FTS.PhiStar.famC (j : ℤ)
      * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ))
      * (Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2))
          * (if j ≤ m then -(1 : ℝ) else 1))
  let t : ℕ → ℕ := fun j => if j ≤ m then m - j else j - m - 1
  let cc : ℕ → ℝ := fun j => Work.FTS.PhiStar.famC (j : ℤ)
      * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ))
  have hev : Qm m =ᶠ[𝓝 θ] fun θ' : ℝ =>
      (1 / 2) * ∑ j ∈ Finset.range (2 * m + 1 + 1), D j * Kern (t j) θ' := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Qm_expansion_Kern hθ'
  have hD : ∀ j, |D j| ≤ cc j := by
    intro j
    have hfac : |Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2))
        * (if j ≤ m then -(1 : ℝ) else 1)| ≤ 1 := by
      rw [abs_mul]
      have h1 : |Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2))| ≤ 1 :=
        Real.abs_sin_le_one _
      have h2 : |(if j ≤ m then -(1 : ℝ) else 1)| ≤ 1 := by
        split_ifs <;> norm_num
      nlinarith [h1, h2,
        abs_nonneg (Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2)))]
    simp only [D, cc]
    rw [abs_mul, abs_mul, abs_of_nonneg (famC_nonneg _), abs_of_nonneg (famC_nonneg _)]
    exact mul_le_of_le_one_right (mul_nonneg (famC_nonneg _) (famC_nonneg _)) hfac
  have ht : ∀ j ∈ Finset.range (2 * m + 1 + 1), 2 * (t j : ℝ) + 1 ≤ 2 * (m : ℝ) + 1 := by
    intro j hj
    have hjle : j ≤ 2 * m + 1 := by
      have := Finset.mem_range.mp hj
      omega
    simp only [t]
    split_ifs with hjm
    · have hcast : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by rw [Nat.cast_sub hjm]
      rw [hcast]
      linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]
    · have hjm' : m + 1 ≤ j := by omega
      have hcast : ((j - m - 1 : ℕ) : ℝ) = (j : ℝ) - (m : ℝ) - 1 := by
        rw [show j - m - 1 = (j - m) - 1 from by omega,
          Nat.cast_sub (show 1 ≤ j - m by omega),
          Nat.cast_sub (show m ≤ j by omega), Nat.cast_one]
      rw [hcast]
      have hjle' : (j : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hjle
      linarith
  have hsum : ∑ j ∈ Finset.range (2 * m + 1 + 1),
        |D j| * (2 ^ (2 * l + 2) * (2 * (t j : ℝ) + 1) ^ (l + 1))
      ≤ 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1)
          * (∑ j ∈ Finset.range (2 * m + 1 + 1), cc j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcj := hD j
    have hc0 : (0 : ℝ) ≤ cc j := by
      simp only [cc]
      exact mul_nonneg (famC_nonneg _) (famC_nonneg _)
    have htj := ht j hj
    have hpow : (0 : ℝ) ≤ 2 ^ (2 * l + 2) := by positivity
    have h3 : (2 * (t j : ℝ) + 1) ^ (l + 1) ≤ (2 * (m : ℝ) + 1) ^ (l + 1) := by
      apply pow_le_pow_left₀ (by positivity)
      exact htj
    have h2 : 2 ^ (2 * l + 2) * (2 * (t j : ℝ) + 1) ^ (l + 1)
        ≤ 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1) :=
      mul_le_mul_of_nonneg_left h3 hpow
    calc |D j| * (2 ^ (2 * l + 2) * (2 * (t j : ℝ) + 1) ^ (l + 1))
        ≤ cc j * (2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1)) :=
          mul_le_mul hcj h2 (by positivity) hc0
      _ = 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1) * cc j := by ring
  have hcc : (∑ j ∈ Finset.range (2 * m + 1 + 1), cc j)
      = Work.FTS.PhiStar.Series.Deleg.Npsi m / 2 := by
    have h1 : Work.FTS.PhiStar.famTrig (2 * m + 1) 0
        = ∑ j ∈ Finset.range (2 * m + 1 + 1),
            Work.FTS.PhiStar.famC (j : ℤ)
              * Work.FTS.PhiStar.famC (((2 * m + 1 : ℕ) : ℤ) - (j : ℤ)) := by
      rw [Work.FTS.PhiStar.famTrig]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_zero, Real.cos_zero, mul_one]
    simp only [cc]
    rw [← h1, ← gC_eq_famTrig (2 * m + 1) 0, Real.cos_zero,
      Work.FTS.PhiStar.Series.Deleg.gC_one]
    unfold Work.FTS.PhiStar.Series.Deleg.Npsi
    push_cast
    ring
  have hNle : Work.FTS.PhiStar.Series.Deleg.Npsi m ≤ 4 * (2 * (m : ℝ) + 1) ^ 2 := by
    unfold Work.FTS.PhiStar.Series.Deleg.Npsi
    have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hmain : |iteratedDeriv l (Qm m) θ|
      ≤ (1 / 2) * ∑ j ∈ Finset.range (2 * m + 1 + 1),
          |D j| * (2 ^ (2 * l + 2) * (2 * (t j : ℝ) + 1) ^ (l + 1)) := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq l hev, iteratedDeriv_const_mul_field]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    exact mul_le_mul_of_nonneg_left (iteratedDeriv_sum_Kern_le l _ D t θ) (by norm_num)
  have hpos : (0 : ℝ) ≤ 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1) := by positivity
  have hpos2 : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ (l + 1) := by positivity
  calc |iteratedDeriv l (Qm m) θ|
      ≤ (1 / 2) * ∑ j ∈ Finset.range (2 * m + 1 + 1),
          |D j| * (2 ^ (2 * l + 2) * (2 * (t j : ℝ) + 1) ^ (l + 1)) := hmain
    _ ≤ (1 / 2) * (2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1)
          * (∑ j ∈ Finset.range (2 * m + 1 + 1), cc j)) := by
        linarith [hsum, hpos]
    _ = (1 / 2) * (2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1)
          * (Work.FTS.PhiStar.Series.Deleg.Npsi m / 2)) := by rw [hcc]
    _ = 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1)
          * (Work.FTS.PhiStar.Series.Deleg.Npsi m / 4) := by ring
    _ ≤ 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1) * (2 * (m : ℝ) + 1) ^ 2 := by
        have hstep2 : Work.FTS.PhiStar.Series.Deleg.Npsi m / 4 ≤ (2 * (m : ℝ) + 1) ^ 2 := by
          linarith [hNle]
        have hstep3 : (0 : ℝ) ≤ 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 1) := by positivity
        exact mul_le_mul_of_nonneg_left hstep2 hstep3
    _ = 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 3) := by
        rw [show l + 3 = (l + 1) + 2 from by ring, pow_add]
        ring

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.QmDeriv.Sup =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.eFam_iteratedDeriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Finset

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- Every iterated derivative of `Real.cos` is bounded by `1` in absolute value. -/
lemma abs_iteratedDeriv_cos_le_one (l : ℕ) (θ : ℝ) : |iteratedDeriv l Real.cos θ| ≤ 1 := by
  have h := congrFun (Work.FTS.PhiStar.FlatWAux.iteratedDeriv_cos_affine 1 0 l) θ
  have hfun : (fun θ : ℝ => Real.cos (1 * θ + 0)) = Real.cos := by funext x; simp
  rw [hfun] at h
  rw [h]
  simpa using Work.FTS.PhiStar.FlatWAux.abs_cos_le_one' (1 * θ + 0 + (l : ℝ) * (Real.pi / 2))

/-- **Derivative bound for the trigonometric Gegenbauer sum.**  For every `l`, `n` and `θ`, the
`l`-th derivative of `θ ↦ famTrig n (π/2 - θ)` is bounded by the total coefficient mass
`(n+1)(n+2)/2 = famTrig n 0` of `famTrig n`, times `(n+1)^l`. -/
lemma abs_iteratedDeriv_famTrig_sub (l n : ℕ) (θ : ℝ) :
    |iteratedDeriv l (fun θ : ℝ => Work.FTS.PhiStar.famTrig n (Real.pi / 2 - θ)) θ|
      ≤ (((n : ℝ) + 1) * (((n : ℝ) + 1) + 1) / 2) * ((n : ℝ) + 1) ^ l := by
  have hfun : (fun θ : ℝ => Work.FTS.PhiStar.famTrig n (Real.pi / 2 - θ))
      = fun θ : ℝ => ∑ k ∈ Finset.range (n + 1),
          (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
              * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
            * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
                + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2)) := by
    funext θ'
    rw [Work.FTS.PhiStar.famTrig]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring_nf
  have hterm : ∀ k ∈ Finset.range (n + 1),
      |iteratedDeriv l (fun θ : ℝ => (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
          * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2))) θ|
        ≤ (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ))) * ((n : ℝ) + 1) ^ l := by
    intro k hk
    rw [iteratedDeriv_const_mul_field]
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Work.FTS.PhiStar.FlatWAux.famC_nonneg _)
      (Work.FTS.PhiStar.FlatWAux.famC_nonneg _))]
    have hcos : iteratedDeriv l (fun θ : ℝ => Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
            + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2))) θ
        = (-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) ^ l
          * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2)
              + (l : ℝ) * (Real.pi / 2)) :=
      congrFun (Work.FTS.PhiStar.FlatWAux.iteratedDeriv_cos_affine
        (-(2 * ((k : ℕ) : ℝ) - (n : ℝ)))
        ((2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2)) l) θ
    rw [hcos, abs_mul, abs_pow, abs_neg]
    have hk' : ((k : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have hknn : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg k
    have hbk : |2 * ((k : ℕ) : ℝ) - (n : ℝ)| ≤ (n : ℝ) + 1 :=
      abs_le.mpr ⟨by linarith, by linarith [hk']⟩
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Work.FTS.PhiStar.FlatWAux.famC_nonneg _)
      (Work.FTS.PhiStar.FlatWAux.famC_nonneg _))
    calc |2 * ((k : ℕ) : ℝ) - (n : ℝ)| ^ l
          * |Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2)
              + (l : ℝ) * (Real.pi / 2))|
        ≤ ((n : ℝ) + 1) ^ l * 1 := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hbk l)
          (Work.FTS.PhiStar.FlatWAux.abs_cos_le_one' _) (abs_nonneg _) (by positivity)
      _ = ((n : ℝ) + 1) ^ l := mul_one _
  have hsum : (∑ k ∈ Finset.range (n + 1),
      Work.FTS.PhiStar.famC ((k : ℕ) : ℤ) * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
      = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
    have h1 : Work.FTS.PhiStar.famTrig n 0 = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
      have h := Work.FTS.PhiStar.FamLopAux.TrigGegen n 0
      rw [Real.cos_zero] at h
      rw [← h, Work.FTS.PhiStar.Series.Deleg.gCAtOne n]
    rw [← h1, Work.FTS.PhiStar.famTrig]
    apply Finset.sum_congr rfl
    intro k hk
    simp
  rw [hfun, iteratedDeriv_fun_sum (I := Finset.range (n + 1)) (x := θ)
    (by intro k hk; fun_prop)]
  calc |∑ k ∈ Finset.range (n + 1),
          iteratedDeriv l (fun θ : ℝ => (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
          * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2))) θ|
      ≤ ∑ k ∈ Finset.range (n + 1),
          |iteratedDeriv l (fun θ : ℝ => (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ)))
          * Real.cos ((-(2 * ((k : ℕ) : ℝ) - (n : ℝ))) * θ
              + (2 * ((k : ℕ) : ℝ) - (n : ℝ)) * (Real.pi / 2))) θ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
          * Work.FTS.PhiStar.famC ((n : ℤ) - ((k : ℕ) : ℤ))) * ((n : ℝ) + 1) ^ l :=
        Finset.sum_le_sum hterm
    _ = (((n : ℝ) + 1) * (((n : ℝ) + 1) + 1) / 2) * ((n : ℝ) + 1) ^ l := by
        rw [← Finset.sum_mul, hsum]
        ring

/-- The bound of `eFam_iteratedDeriv_le` in the family index `n = 2j+1`: the analysis of
`abs_iteratedDeriv_famTrig_sub` plus the Leibniz rule in `cos θ` shows

    `|∂_θ^m (eFam j) θ| ≤ 2^m · (n+1)^{m+2}`,   `n = 2j+1`. -/
lemma eFam_iteratedDeriv_le_base (m j : ℕ) (θ : ℝ) :
    |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
      ≤ (2 : ℝ) ^ m * ((((2 * j + 1 : ℕ) : ℝ)) + 1) ^ (m + 2) := by
  have he : Work.FTS.PhiStar.Gegenbauer.eFam j
      = Real.cos * (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) := by
    funext θ'
    simp only [Pi.mul_apply]
    rw [Work.FTS.PhiStar.Gegenbauer.eFam, ← Real.cos_pi_div_two_sub θ',
      Work.FTS.PhiStar.FamLopAux.TrigGegen]
  have hG : ContDiffAt ℝ (m : ℕ∞)
      (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) θ := by
    rw [show (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ))
        = fun θ : ℝ => ∑ k ∈ Finset.range (2 * j + 1 + 1),
            (Work.FTS.PhiStar.famC ((k : ℕ) : ℤ)
                * Work.FTS.PhiStar.famC (((2 * j + 1 : ℕ) : ℤ) - ((k : ℕ) : ℤ)))
              * Real.cos ((-(2 * ((k : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ))) * θ
                  + (2 * ((k : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) * (Real.pi / 2)) from ?_]
    · fun_prop
    · funext θ'
      rw [Work.FTS.PhiStar.famTrig]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring_nf
  rw [he, iteratedDeriv_mul (Real.contDiff_cos (n := (m : ℕ∞))).contDiffAt hG]
  set N : ℝ := ((2 * j + 1 : ℕ) : ℝ) + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hN]
    have hcast : ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * ((j : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hFnn : (0 : ℝ) ≤ N * (N + 1) / 2 := by nlinarith [hN0]
  have hgoal : |∑ i ∈ Finset.range (m + 1), ↑(m.choose i) * iteratedDeriv i Real.cos θ
        * iteratedDeriv (m - i)
            (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) θ|
      ≤ (2 : ℝ) ^ m * (N * (N + 1) / 2 * N ^ m) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have step1 : ∑ i ∈ Finset.range (m + 1), |↑(m.choose i) * iteratedDeriv i Real.cos θ
          * iteratedDeriv (m - i)
              (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) θ|
        ≤ ∑ i ∈ Finset.range (m + 1),
            ↑(m.choose i) * (N * (N + 1) / 2 * N ^ (m - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose i))]
      have h1 := abs_iteratedDeriv_cos_le_one i θ
      have h2 := abs_iteratedDeriv_famTrig_sub (m - i) (2 * j + 1) θ
      calc ↑(m.choose i) * |iteratedDeriv i Real.cos θ|
            * |iteratedDeriv (m - i)
                (fun θ : ℝ => Work.FTS.PhiStar.famTrig (2 * j + 1) (Real.pi / 2 - θ)) θ|
          ≤ ↑(m.choose i) * 1 * (N * (N + 1) / 2 * N ^ (m - i)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (m.choose i))) h2
              (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg (m.choose i)) zero_le_one)
        _ = ↑(m.choose i) * (N * (N + 1) / 2 * N ^ (m - i)) := by ring
    refine le_trans step1 ?_
    have step2 : ∑ i ∈ Finset.range (m + 1), ↑(m.choose i) * (N * (N + 1) / 2 * N ^ (m - i))
        ≤ ∑ i ∈ Finset.range (m + 1), ↑(m.choose i) * (N * (N + 1) / 2 * N ^ m) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle : N ^ (m - i) ≤ N ^ m := pow_le_pow_right₀ hN1 (Nat.sub_le m i)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hFnn) (Nat.cast_nonneg _)
    refine le_trans step2 ?_
    rw [← Finset.sum_mul]
    have hchoose : (∑ i ∈ Finset.range (m + 1), (↑(m.choose i) : ℝ)) = (2 : ℝ) ^ m := by
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
      norm_num
    rw [hchoose]
  refine le_trans hgoal ?_
  have hFN : N * (N + 1) / 2 * N ^ m ≤ N ^ (m + 2) := by
    have hle : N * (N + 1) / 2 ≤ N ^ 2 := by nlinarith [hN1]
    calc N * (N + 1) / 2 * N ^ m ≤ N ^ 2 * N ^ m :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg hN0.le m)
      _ = N ^ (m + 2) := by rw [← pow_add, Nat.add_comm]
  calc (2 : ℝ) ^ m * (N * (N + 1) / 2 * N ^ m) ≤ (2 : ℝ) ^ m * N ^ (m + 2) :=
        mul_le_mul_of_nonneg_left hFN (by positivity)
    _ = (2 : ℝ) ^ m * ((((2 * j + 1 : ℕ) : ℝ)) + 1) ^ (m + 2) := by rw [hN]

theorem eFam_iteratedDeriv_le (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
        ≤ C * ((j : ℝ) + 1) ^ (4 * m + 4) := by
  refine ⟨(2 : ℝ) ^ (2 * m + 2), by positivity, ?_⟩
  intro j θ hθ
  have hbase := eFam_iteratedDeriv_le_base m j θ
  refine le_trans hbase ?_
  have hcast : (((2 * j + 1 : ℕ) : ℝ)) + 1 = 2 * ((j : ℝ) + 1) := by push_cast; ring
  have hpow : (2 : ℝ) ^ m * 2 ^ (m + 2) = 2 ^ (2 * m + 2) := by
    rw [← pow_add, show m + (m + 2) = 2 * m + 2 from by omega]
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  calc (2 : ℝ) ^ m * ((((2 * j + 1 : ℕ) : ℝ)) + 1) ^ (m + 2)
      = 2 ^ m * (2 ^ (m + 2) * ((j : ℝ) + 1) ^ (m + 2)) := by rw [hcast, mul_pow]
    _ = 2 ^ (2 * m + 2) * ((j : ℝ) + 1) ^ (m + 2) := by rw [← mul_assoc, hpow]
    _ ≤ 2 ^ (2 * m + 2) * ((j : ℝ) + 1) ^ (4 * m + 4) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj1 (by omega)) (by positivity)

end Work.FTS.PhiStar.Series
end
end
