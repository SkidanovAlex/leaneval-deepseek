import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.gridIdx_ratio_mem_V
import Submission.Work.EKLC6Route.dev_estimates
import Submission.Work.EKLC6Route.VtSet_mul_inv
import Submission.Work.EKLC6Route.aDiag_conj_mem_V_of_mem_VtSet
import Submission.Work.EKLC6Route.aDiag_conj_mem_V_of_mem_uminus
import Submission.Work.EKLC6Route.uminus_inv_dev_le

namespace Work.EKLC6Route

open Work.EKLContract

/-! ## Helper lemmas for `track_conj_mem_V` -/

/-- `betaExp t ≥ 0`. -/
theorem betaExp_nonneg (t : Fin 3 → ℝ) : 0 ≤ betaExp t := by
  rw [betaExp]
  calc (0 : ℝ) = |t 0 - t 0| := by simp
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|) :=
        Finset.le_sup' (fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|) (Finset.mem_univ (0, 0))

/-- Membership in `Uball U r` gives membership in the ambient displacement ball `V r`. -/
theorem mem_V_of_mem_Uball {U : Subgroup SL3} {r : ℝ} {u : SL3}
    (hu : u ∈ Work.EKLComp.Uball U r) : u ∈ V r := fun i j => hu.2 i j

/-- Conjugating any `v ∈ V s` by `aDiag t ^ n` scales the radius by at most `exp (n * betaExp t)`.

The `(i,j)` entry of the conjugate is `exp (n (t i - t j)) * v i j`; the diagonal factor is `1` on
the diagonal, at most `1 ≤ exp (n * betaExp t)` when `t i < t j`, and at most
`exp (n * betaExp t)` when `t i > t j`. -/
theorem aDiag_conj_mem_V_exp {t : Fin 3 → ℝ} (n : ℕ) {s : ℝ} {v : SL3}
    (hv : v ∈ V s) :
    aDiag t ^ n * v * (aDiag t ^ n)⁻¹ ∈ V (Real.exp ((n : ℝ) * betaExp t) * s) := by
  have hs : 0 < s := pos_of_mem_V hv
  have hb0 : 0 ≤ betaExp t := betaExp_nonneg t
  have hexp1 : (1 : ℝ) ≤ Real.exp ((n : ℝ) * betaExp t) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (Nat.cast_nonneg n) hb0)
  intro i j
  rw [Work.EKLC6Core.boxi_conj_pow_apply]
  by_cases hij : i = j
  · subst hij
    rw [sub_self, mul_zero, Real.exp_zero, one_mul, Matrix.one_apply_eq]
    have h := hv i i
    rw [Matrix.one_apply_eq] at h
    calc |(v : Matrix (Fin 3) (Fin 3) ℝ) i i - 1| < s := h
      _ ≤ Real.exp ((n : ℝ) * betaExp t) * s := by nlinarith [hexp1, hs]
  · rw [Matrix.one_apply_ne hij, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hfac : Real.exp ((n : ℝ) * (t i - t j)) ≤ Real.exp ((n : ℝ) * betaExp t) := by
      rw [Real.exp_le_exp]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
      calc t i - t j ≤ |t i - t j| := le_abs_self _
        _ ≤ betaExp t := by
            rw [betaExp]
            exact Finset.le_sup' (fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|)
              (Finset.mem_univ (i, j))
    have hvij : |(v : Matrix (Fin 3) (Fin 3) ℝ) i j| < s := by
      have h := hv i j
      rwa [Matrix.one_apply_ne hij, sub_zero] at h
    have h1 : Real.exp ((n : ℝ) * (t i - t j)) * |(v : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ Real.exp ((n : ℝ) * betaExp t) * |(v : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
      mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
    have h2 : Real.exp ((n : ℝ) * betaExp t) * |(v : Matrix (Fin 3) (Fin 3) ℝ) i j|
        < Real.exp ((n : ℝ) * betaExp t) * s :=
      mul_lt_mul_of_pos_left hvij (Real.exp_pos _)
    linarith

/-- If `u ∈ Uminus t` lies in `V r` with `r ≤ 1/3`, then `u⁻¹ ∈ V (2 r)`.

This is `uminus_inv_dev_le` (`dev u⁻¹ ≤ dev u + 3 dev u²`) together with `dev u < r` and
`r + 3 r² ≤ 2 r`. -/
theorem inv_mem_V_of_mem_uminus {t : Fin 3 → ℝ} {r : ℝ} {u : SL3}
    (hu : u ∈ Work.EKLC6Core.Uminus t) (huV : u ∈ V r) (hr1 : r ≤ 1 / 3) :
    u⁻¹ ∈ V (2 * r) := by
  have hr : 0 < r := pos_of_mem_V huV
  rw [mem_V_iff_dev_lt]
  have hdev : dev u < r := (mem_V_iff_dev_lt u r).mp huV
  have hdev0 : 0 ≤ dev u := le_trans (abs_nonneg _) (abs_dev_entry u 0 0)
  have hinv : dev u⁻¹ ≤ dev u + 3 * dev u ^ 2 := uminus_inv_dev_le hu
  have hstep : dev u + 3 * dev u ^ 2 < r + 3 * r ^ 2 := by nlinarith [hdev, hdev0]
  have hr2 : r + 3 * r ^ 2 ≤ 2 * r := by
    have h3 : 3 * r ≤ 1 := by linarith
    nlinarith [hr, h3]
  linarith

/-- First-order product estimate in terms of `dev`: `dev (g * h) ≤ dev g + dev h + 3 dev g dev h`
with the individual `dev`s replaced by `V`-radii. -/
theorem mul_V_mem_V_of_dev {a b : ℝ} {g h : SL3} (hg : g ∈ V a) (hh : h ∈ V b) :
    dev (g * h) ≤ a + b + 3 * a * b := by
  have hga : dev g < a := (mem_V_iff_dev_lt g a).mp hg
  have hhb : dev h < b := (mem_V_iff_dev_lt h b).mp hh
  have hga0 : 0 ≤ dev g := le_trans (abs_nonneg _) (abs_dev_entry g 0 0)
  have hhb0 : 0 ≤ dev h := le_trans (abs_nonneg _) (abs_dev_entry h 0 0)
  calc dev (g * h) ≤ dev g + dev h + 3 * dev g * dev h := dev_mul_le g h
    _ ≤ a + b + 3 * a * b := by nlinarith [hga, hhb, hga0, hhb0]

/-- Product of three small displacements: if `g ∈ V a`, `h ∈ V b`, `k ∈ V c` and
`a + b + c + 3bc + 3ab + 3ac + 9abc < D`, then `g * h * k ∈ V D`. -/
theorem mul3_mem_V {a b c D : ℝ} {g h k : SL3}
    (hg : g ∈ V a) (hh : h ∈ V b) (hk : k ∈ V c)
    (hD : a + b + c + 3 * b * c + 3 * a * b + 3 * a * c + 9 * a * b * c < D) :
    g * h * k ∈ V D := by
  rw [mem_V_iff_dev_lt]
  have h1 : dev (g * h) ≤ a + b + 3 * a * b := mul_V_mem_V_of_dev hg hh
  have h1nn : 0 ≤ dev (g * h) := le_trans (abs_nonneg _) (abs_dev_entry (g * h) 0 0)
  have hkc : dev k < c := (mem_V_iff_dev_lt k c).mp hk
  have hkc0 : 0 ≤ dev k := le_trans (abs_nonneg _) (abs_dev_entry k 0 0)
  have h2 : dev ((g * h) * k) ≤ (a + b + 3 * a * b) + c + 3 * (a + b + 3 * a * b) * c := by
    calc dev ((g * h) * k) ≤ dev (g * h) + dev k + 3 * dev (g * h) * dev k := dev_mul_le (g * h) k
      _ ≤ (a + b + 3 * a * b) + c + 3 * (a + b + 3 * a * b) * c := by
          nlinarith [h1, hkc, h1nn, hkc0]
  have h3 : (a + b + 3 * a * b) + c + 3 * (a + b + 3 * a * b) * c
      = a + b + c + 3 * b * c + 3 * a * b + 3 * a * c + 9 * a * b * c := by ring
  rw [h3] at h2
  linarith

/-- Numerical bookkeeping for `track_conj_mem_V`: the three radii `r`, `100 ρ`, `2 r` of the
factors, combined through `mul3_mem_V`, stay below `δ` given `r, ρ ≤ δ/4000` and `δ ≤ 1/100`. -/
theorem track_arith {r ρ δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hrδ : 4000 * r ≤ δ) (hρδ : 4000 * ρ ≤ δ) :
    r + 100 * ρ + 2 * r + 3 * (100 * ρ) * (2 * r) + 3 * r * (100 * ρ) + 3 * r * (2 * r)
      + 9 * r * (100 * ρ) * (2 * r) < δ := by
  have hr0 : 0 ≤ r := le_of_lt hr
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  have hr' : r ≤ δ / 4000 := by linarith
  have hρ' : ρ ≤ δ / 4000 := by linarith
  have hδ2 : δ ^ 2 ≤ δ / 100 := by nlinarith [hδ, hδ1]
  have hδ3 : δ ^ 3 ≤ δ / 10000 := by nlinarith [hδ, hδ1, hδ2]
  -- bound each monomial of `E - δ`
  have hA : 900 * ρ * r ≤ 900 * (δ / 4000) * (δ / 4000) := by nlinarith [hr', hρ', hr0, hρ0]
  have hB : 6 * r ^ 2 ≤ 6 * (δ / 4000) ^ 2 := by nlinarith [hr', hr0]
  have hC : 1800 * ρ * r ^ 2 ≤ 1800 * (δ / 4000) ^ 3 := by
    nlinarith [hr', hρ', hr0, hρ0]
  have hE : r + 100 * ρ + 2 * r + 3 * (100 * ρ) * (2 * r) + 3 * r * (100 * ρ) + 3 * r * (2 * r)
      + 9 * r * (100 * ρ) * (2 * r) = 3 * r + 100 * ρ + 900 * ρ * r + 6 * r ^ 2 + 1800 * ρ * r ^ 2 := by
    ring
  rw [hE]
  nlinarith [hr', hρ', hr0, hρ0, hA, hB, hC, hδ, hδ1, hδ2, hδ3]

theorem track_conj_mem_V {μ : MeasureTheory.Measure Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (w : Work.EKLC6Route.Window μ t) {i L : ℕ} {u u' k k' : Work.EKLContract.SL3}
    (hu : u ∈ Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) w.r)
    (hu' : u' ∈ Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) w.r)
    (hk : k ∈ Work.EKLC6Route.VtSet t ∩ Work.EKLContract.V w.ρ)
    (hk' : k' ∈ Work.EKLC6Route.VtSet t ∩ Work.EKLContract.V w.ρ)
    (hgrid : Work.EKLC6Route.gridIdx w.ρ L k = Work.EKLC6Route.gridIdx w.ρ L k')
    (hLev : (1 / 2 : ℝ) ^ L * Real.exp ((i : ℝ) * Work.EKLC6Route.betaExp t) ≤ 1) :
    Work.EKLContract.aDiag t ^ i * (u' * (k' * k⁻¹) * u⁻¹) * (Work.EKLContract.aDiag t ^ i)⁻¹ ∈
      Work.EKLContract.V w.δ := by
  have hr : 0 < w.r := w.hr
  have hρ : 0 < w.ρ := w.hρ
  have hδ : 0 < w.δ := w.hδ
  have hδ1 : w.δ ≤ 1 / 100 := w.hδ1
  have hrδ : 4000 * w.r ≤ w.δ := w.hrδ
  have hρδ : 4000 * w.ρ ≤ w.δ := w.hρδ
  have hρ1 : w.ρ ≤ 1 := by linarith
  have hw : k' * k⁻¹ ∈ V (100 * (1 / 2 : ℝ) ^ L * w.ρ) :=
    gridIdx_ratio_mem_V hρ hρ1 hk.2 hk'.2 hgrid
  have hf2 : aDiag t ^ i * (k' * k⁻¹) * (aDiag t ^ i)⁻¹ ∈ V (100 * w.ρ) := by
    refine V_subset_of_le ?_ (aDiag_conj_mem_V_exp (t := t) i hw)
    have heq : Real.exp ((i : ℝ) * betaExp t) * (100 * (1 / 2 : ℝ) ^ L * w.ρ)
        = 100 * w.ρ * ((1 / 2 : ℝ) ^ L * Real.exp ((i : ℝ) * betaExp t)) := by ring
    rw [heq]
    calc 100 * w.ρ * ((1 / 2 : ℝ) ^ L * Real.exp ((i : ℝ) * betaExp t))
        ≤ 100 * w.ρ * 1 := mul_le_mul_of_nonneg_left hLev (by positivity)
      _ = 100 * w.ρ := by ring
  have hf1 : aDiag t ^ i * u' * (aDiag t ^ i)⁻¹ ∈ V w.r :=
    aDiag_conj_mem_V_of_mem_uminus i hu'.1 (mem_V_of_mem_Uball hu')
  have hr13 : w.r ≤ 1 / 3 := by linarith
  have h3 : u⁻¹ ∈ V (2 * w.r) :=
    inv_mem_V_of_mem_uminus hu.1 (mem_V_of_mem_Uball hu) hr13
  have hf3 : aDiag t ^ i * u⁻¹ * (aDiag t ^ i)⁻¹ ∈ V (2 * w.r) :=
    aDiag_conj_mem_V_of_mem_uminus i (Subgroup.inv_mem _ hu.1) h3
  have hEq : aDiag t ^ i * (u' * (k' * k⁻¹) * u⁻¹) * (aDiag t ^ i)⁻¹
      = (aDiag t ^ i * u' * (aDiag t ^ i)⁻¹)
        * (aDiag t ^ i * (k' * k⁻¹) * (aDiag t ^ i)⁻¹)
        * (aDiag t ^ i * u⁻¹ * (aDiag t ^ i)⁻¹) := by group
  rw [hEq]
  exact mul3_mem_V hf1 hf2 hf3 (track_arith hr hρ hδ hδ1 hrδ hρδ)

end Work.EKLC6Route
