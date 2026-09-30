import Mathlib
import Submission.Work.BMF.adi_descent
import Submission.Work.BMF.abs_tay_sub_log_le
import Submission.Work.BMF.step_geom
import Submission.Work.BMF.step_tval_bound
import Submission.Work.BMF.step_tay_diff
import Submission.Work.BMF.step_dgrow_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset
theorem step_bound (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    ∀ t ∈ Set.Icc (p.x / (p.a : ℝ)) ((p.x + p.L) / (p.a : ℝ)),
      |(dstep p s).E.eval t| ≤ (dstep p s).A := by
  intro t ht
  have hs' := hs
  have hp' := hp
  obtain ⟨hjk, hPd, hEd, hGd, hrel, hEb, hA0, hAlev, hInt, hP0, hTb, hmub⟩ := hs'
  obtain ⟨hC0, hP0d, hL2, hN100, hQm1, hx0, hNL, hxNL, hb1, hba, hNa, hNa2⟩ := hp'
  have hLpos : 0 < p.L := by linarith
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨hLx2, h3Lx2, hgeom⟩ := step_geom p hp
  obtain ⟨hat, hbt⟩ := hgeom t ht
  set Td : ℝ := (Tay s.j p.x).eval ((p.a : ℝ) * t) - (Tay s.j p.x).eval ((p.b : ℝ) * t) with hTd
  set Lg : ℝ := Real.log ((p.a : ℝ) / (p.b : ℝ)) with hLg
  set c : ℝ := Tval p s / (2 * Real.pi) with hc
  set nv : ℝ := (nval p s : ℝ) with hnv
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    have h := abs_add_le a (-b)
    simpa [sub_eq_add_neg, abs_neg] using h
  have hEeval : (dstep p s).E.eval t = s.E.eval t - (c * Td - nv) := by
    rw [hc, hTd, hnv]
    rw [dstep_E]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      dil, Polynomial.eval_comp, Polynomial.eval_X]
    ring
  have hc_bound : |c| ≤
      s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j := by
    rw [hc, abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
    have htb := step_tval_bound p s hp hs hj
    have heq : (s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j) * (2 * Real.pi)
        = 2 * Real.pi * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j := by
      ring
    rw [heq]
    exact htb
  have hBnn : 0 ≤ s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j := by
    have h1 : 0 ≤ (p.x / p.L) ^ s.j :=
      pow_nonneg (div_nonneg (le_of_lt hx0) (le_of_lt hLpos)) _
    have h2 : 0 ≤ p.N := le_trans (by positivity : (0:ℝ) ≤ 100 * p.C₀ ^ 4) hN100
    have h3 : 0 ≤ (s.j : ℝ) ^ (s.j + 1) := pow_nonneg (Nat.cast_nonneg _) _
    have h4 : 0 ≤ (s.j : ℝ) + 1 := by positivity
    have h5 : 0 ≤ p.C₀ := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA0 h4) h3) h5) h2) h1
  have hD_bound : |Td - Lg| ≤
      2 * (p.L / p.x) ^ (s.j + 1) + 2 * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (s.j + 1) := by
    rw [hTd, hLg]
    exact step_tay_diff p hp s.j t ht
  have hnval' : |nv - c * Lg| ≤ 1/2 := by
    rw [hnv, hc, hLg]
    have h1 : (nval p s : ℝ) ≤ (Tval p s / (2 * Real.pi)) * Real.log ((p.a : ℝ) / (p.b : ℝ)) + 1/2 := by
      simp only [nval]
      exact Int.floor_le _
    have h2 : (Tval p s / (2 * Real.pi)) * Real.log ((p.a : ℝ) / (p.b : ℝ)) + 1/2 < (nval p s : ℝ) + 1 := by
      simp only [nval]
      exact Int.lt_floor_add_one _
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hxne : p.x ≠ 0 := ne_of_gt hx0
  have hLne : p.L ≠ 0 := ne_of_gt hLpos
  have hpq : (p.x / p.L) ^ s.j * (p.L / p.x) ^ (s.j + 1) = p.L / p.x := by
    have h1 : p.x / p.L * (p.L / p.x) = 1 := by field_simp
    rw [pow_succ, ← mul_assoc, ← mul_pow, h1, one_pow, one_mul]
  have hpq2 : (p.x / p.L) ^ s.j * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (s.j + 1)
      = (3 * p.C₀ ^ 2) ^ (s.j + 1) * (p.L / p.x) := by
    have hsplit : 3 * p.C₀ ^ 2 * p.L / p.x = (3 * p.C₀ ^ 2) * (p.L / p.x) := by ring
    rw [hsplit, mul_pow]
    calc (p.x / p.L) ^ s.j * ((3 * p.C₀ ^ 2) ^ (s.j + 1) * (p.L / p.x) ^ (s.j + 1))
        = (3 * p.C₀ ^ 2) ^ (s.j + 1) * ((p.x / p.L) ^ s.j * (p.L / p.x) ^ (s.j + 1)) := by ring
      _ = (3 * p.C₀ ^ 2) ^ (s.j + 1) * (p.L / p.x) := by rw [hpq]
  have he1 : s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j
        * (2 * (p.L / p.x) ^ (s.j + 1))
      = 2 * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.L / p.x) := by
    rw [show s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j
          * (2 * (p.L / p.x) ^ (s.j + 1))
        = 2 * (s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N)
          * ((p.x / p.L) ^ s.j * (p.L / p.x) ^ (s.j + 1)) from by ring]
    rw [hpq]
    ring
  have he2 : s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j
        * (2 * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (s.j + 1))
      = 2 * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N
          * ((3 * p.C₀ ^ 2) ^ (s.j + 1) * (p.L / p.x)) := by
    rw [show s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j
          * (2 * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (s.j + 1))
        = 2 * (s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N)
          * ((p.x / p.L) ^ s.j * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (s.j + 1)) from by ring]
    rw [hpq2]
    ring
  have hrewrite : s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j
        * (2 * (p.L / p.x) ^ (s.j + 1) + 2 * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (s.j + 1))
      = 2 * s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * (p.N * p.L / p.x) * p.C₀
        * (1 + (3 * p.C₀ ^ 2) ^ (s.j + 1)) := by
    rw [mul_add, he1, he2]
    ring
  have hkey : |c * Td - nv| ≤ s.A * Dgrow p.k p.C₀ + 1/2 := by
    have hdecomp : c * Td - nv = c * (Td - Lg) - (nv - c * Lg) := by ring
    rw [hdecomp]
    refine le_trans (htri _ _) ?_
    have hcD : |c * (Td - Lg)| ≤
        (s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j)
          * (2 * (p.L / p.x) ^ (s.j + 1) + 2 * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (s.j + 1)) := by
      rw [abs_mul]
      exact mul_le_mul hc_bound hD_bound (abs_nonneg _) hBnn
    have hfin : (s.A * ((s.j : ℝ) + 1) * (s.j : ℝ) ^ (s.j + 1) * p.C₀ * p.N * (p.x / p.L) ^ s.j)
          * (2 * (p.L / p.x) ^ (s.j + 1) + 2 * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (s.j + 1))
        ≤ s.A * Dgrow p.k p.C₀ := by
      rw [hrewrite]
      exact step_dgrow_bound p.k s.j p.C₀ s.A p.N p.x p.L hC0 hA0 hx0 hjk hNL
    linarith [hcD, hfin, hnval']
  rw [hEeval]
  calc |s.E.eval t - (c * Td - nv)| ≤ |s.E.eval t| + |c * Td - nv| := htri _ _
    _ ≤ s.A + (s.A * Dgrow p.k p.C₀ + 1/2) := add_le_add (hEb t ht) hkey
    _ ≤ (dstep p s).A := by rw [dstep_A]; linarith


end Work.BMF
