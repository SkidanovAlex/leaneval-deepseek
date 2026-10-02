import Mathlib
import Submission.Work.PARIMPL2.Direct.oidDefs
import Submission.Work.PARIMPL2.Direct.inbound_bounds
import Submission.Work.PARIMPL2.Direct.ecalPt_im_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct
open Complex

noncomputable section


theorem ocA_eq_ecalPt_re (lam : ℝ) (hlam : 0 < lam) (x y : ℕ → ℝ) (j : ℕ)
    (hE : (Work.Implosion.ecalE ((lam:ℂ)*Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)) ≠ 1) :
    (Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)).re
      = ocA lam x y j := by
  have h1 : (((x j : ℂ) + (y j : ℂ) * Complex.I)).re = x j := by simp
  have h2 : (((x j : ℂ) + (y j : ℂ) * Complex.I)).im = y j := by simp
  have h3 := normSq_sin_eq_ocDen lam ((x j : ℂ) + (y j : ℂ) * Complex.I)
  rw [h1, h2] at h3
  rw [inbound_ecalPt_re lam hlam _ hE, h1, h3, ocA, ocDen]
  ring

theorem ocA_eq_ecalPt_re' (lam : ℝ) (hlam : 0 < lam) (x y : ℕ → ℝ) (j : ℕ)
    (hE : (Work.Implosion.ecalE ((lam:ℂ)*Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)) ≠ 1) :
    ocA lam x y j = (Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)).re :=
  (ocA_eq_ecalPt_re lam hlam x y j hE).symm

theorem ecalPt_im_eq' (lam : ℝ) (x y : ℕ → ℝ) (j : ℕ) :
    (Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)).im
      = -(lam * Real.sinh (lam * y j) * Real.cosh (lam * y j)) / ocDen lam x y j := by
  have h1 : (((x j : ℂ) + (y j : ℂ) * Complex.I)).re = x j := by simp
  have h2 : (((x j : ℂ) + (y j : ℂ) * Complex.I)).im = y j := by simp
  have hE : ocDen lam x y j
      = Real.sin (lam * (((x j : ℂ) + (y j : ℂ) * Complex.I)).re) ^ 2
        + Real.sinh (lam * (((x j : ℂ) + (y j : ℂ) * Complex.I)).im) ^ 2 := by
    rw [ocDen, h1, h2]
  rw [ecalPt_im_eq lam _ (ocDen lam x y j) hE, h2]

/-- `ζ_j = ecalPt (iλ) (x j + i y j)`. -/
def oidZeta (lam : ℝ) (x y : ℕ → ℝ) (j : ℕ) : ℂ :=
  Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)

/-- The growth coefficient of the imaginary recurrence: `C'_j = -c.re·(ζ_j).im / y_j`. -/
def oidCf (lam cr : ℝ) (x y : ℕ → ℝ) (j : ℕ) : ℝ :=
  -cr * (oidZeta lam x y j).im / y j

theorem oidZeta_re (lam : ℝ) (hlam : 0 < lam) (x y : ℕ → ℝ) (j : ℕ)
    (hE : (Work.Implosion.ecalE ((lam:ℂ)*Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)) ≠ 1) :
    (oidZeta lam x y j).re = ocA lam x y j :=
  ocA_eq_ecalPt_re lam hlam x y j hE

theorem oidZeta_im (lam : ℝ) (x y : ℕ → ℝ) (j : ℕ) :
    (oidZeta lam x y j).im
      = -(lam * Real.sinh (lam * y j) * Real.cosh (lam * y j)) / ocDen lam x y j :=
  ecalPt_im_eq' lam x y j

/-- `sinh t ≤ t·cosh t` for `t ≥ 0`. -/
theorem sinh_le_mul_cosh (t : ℝ) (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t := by
  have h : ∀ x ∈ Set.Icc (0:ℝ) t,
      HasDerivAt (fun y => y * Real.cosh y - Real.sinh y) (x * Real.sinh x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y * Real.cosh y) (1 * Real.cosh x + x * Real.sinh x) x :=
      (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
    have h2 : HasDerivAt (fun y : ℝ => Real.sinh y) (Real.cosh x) x := Real.hasDerivAt_sinh x
    have h3 := h1.sub h2
    convert h3 using 1
    ring
  have hcont : ContinuousOn (fun y => y * Real.cosh y - Real.sinh y) (Set.Icc 0 t) := by fun_prop
  have hmono : MonotoneOn (fun y => y * Real.cosh y - Real.sinh y) (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (h x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(h x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).deriv]
      exact mul_nonneg (le_of_lt hx.1) (Real.sinh_nonneg_iff.mpr (le_of_lt hx.1))
  have h0 : (0:ℝ)*Real.cosh 0 - Real.sinh 0 = 0 := by simp
  have := hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
  simp only [h0] at this
  linarith


theorem ocDen_nonneg (lam : ℝ) (x y : ℕ → ℝ) (j : ℕ) : 0 ≤ ocDen lam x y j := by
  rw [ocDen]; positivity

theorem oidZeta_im_zero_of (lam : ℝ) (x y : ℕ → ℝ) (j : ℕ) (h : y j = 0) :
    (oidZeta lam x y j).im = 0 := by
  rw [oidZeta_im, h]; simp

theorem oidZeta_im_zero_of_den (lam : ℝ) (x y : ℕ → ℝ) (j : ℕ)
    (h : ocDen lam x y j = 0) : (oidZeta lam x y j).im = 0 := by
  rw [oidZeta_im, h]; simp

theorem oidCf_mul (lam cr : ℝ) (x y : ℕ → ℝ) (j : ℕ) :
    oidCf lam cr x y j * y j = -cr * (oidZeta lam x y j).im := by
  by_cases h : y j = 0
  · rw [h, oidZeta_im_zero_of lam x y j h, mul_zero, mul_zero]
  · rw [oidCf, div_mul_cancel₀ _ h]


theorem normSq_sin_eq_ocDen' (lam : ℝ) (x y : ℕ → ℝ) (j : ℕ) :
    ‖Complex.sin ((lam:ℂ) * ((x j : ℂ) + (y j : ℂ) * Complex.I))‖ ^ 2 = ocDen lam x y j := by
  rw [normSq_sin_eq_ocDen, ocDen]; simp

theorem ecalE_ne_one_of_den (lam : ℝ) (x y : ℕ → ℝ) (j : ℕ)
    (h : ocDen lam x y j ≠ 0) :
    (Work.Implosion.ecalE ((lam:ℂ)*Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)) ≠ 1 := by
  intro he
  have hsin : Complex.sin ((lam:ℂ) * ((x j : ℂ) + (y j : ℂ) * Complex.I)) = 0 := by
    have h1 := inbound_ecalE_sub_one ((lam:ℂ)*Complex.I) ((x j : ℂ) + (y j : ℂ) * Complex.I)
    rw [he, sub_self] at h1
    have h2 : Complex.sinh (((lam:ℂ)*Complex.I) * ((x j : ℂ) + (y j : ℂ) * Complex.I)) = 0 := by
      rcases mul_eq_zero.mp h1.symm with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd h4 (by norm_num)
        · exact h4
      · exact absurd h3 (Complex.exp_ne_zero _)
    have h5 : (((lam:ℂ)*Complex.I) * ((x j : ℂ) + (y j : ℂ) * Complex.I))
        = ((lam:ℂ) * ((x j : ℂ) + (y j : ℂ) * Complex.I)) * Complex.I := by ring
    rw [h5, Complex.sinh_mul_I] at h2
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact h4
    · exact absurd h4 Complex.I_ne_zero
  have h4 : ‖Complex.sin ((lam:ℂ) * ((x j : ℂ) + (y j : ℂ) * Complex.I))‖^2 = ocDen lam x y j :=
    normSq_sin_eq_ocDen' lam x y j
  rw [hsin, norm_zero] at h4
  simp at h4
  exact h h4.symm

/-- Solution of a first-order linear recurrence with variable coefficients. -/
theorem linear_rec_sol (w g C : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n, w (j + 1) = (1 + C j) * w j + g j) :
    w n = (∏ i ∈ Finset.range n, (1 + C i)) * w 0
      + ∑ j ∈ Finset.range n, g j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' : ∀ j < n, w (j + 1) = (1 + C j) * w j + g j := fun j hj => h j (Nat.lt_succ_of_lt hj)
    rw [h n (Nat.lt_succ_self n), ih h', Finset.prod_range_succ, Finset.sum_range_succ]
    have hstep : ∀ j ∈ Finset.range n,
        g j * ∏ i ∈ Finset.Ico (j + 1) (n + 1), (1 + C i)
          = (1 + C n) * (g j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i)) := by
      intro j hj
      have hj' : j + 1 ≤ n := by
        have := Finset.mem_range.mp hj; omega
      rw [Finset.prod_Ico_succ_top hj']
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum,
      Finset.Ico_self, Finset.prod_empty, mul_one]
    ring

end
end Work.PARIMPL2.Direct
