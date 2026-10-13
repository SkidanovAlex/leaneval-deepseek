/-
# `Work.FTS.PhiStar.FlatWAux.QmDeriv.Expansion` — the mode expansion and the `l ≥ 1` bound

Support module for `QmDerivBound`: the trigonometric expansion of `Qm m` on `(0, π/2)` obtained
from the trig form of the Gegenbauer polynomial, its rewriting as a finite sum of Dirichlet-type
kernels, and the resulting crude bound on `iteratedDeriv l (Qm m)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.QmDeriv.Trig
import Submission.Work.FTS.PhiStar.Series.Deleg.psiAngDefs
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
