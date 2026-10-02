import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.logSin_second_order
import Submission.Work.PARIMPL2.Direct.logSin_endpoints_le
import Submission.Work.PARIMPL2.Direct.sum_min_inv_sq_le
import Submission.Work.PARIMPL2.Direct.modelDisp_im_decomp
import Submission.Work.PARIMPL2.Direct.jordan_sin_min
import Submission.Work.PARIMPL2.Direct.inbound_bounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option autoImplicit false

namespace Work.PARIMPL2.Direct

open Complex
open scoped BigOperators

/-- Lower bound for `‖sin (λ w)‖` in terms of `Re w` alone (Jordan's inequality
fed into `‖sin‖ ≥ |Re sin|`). -/
private lemma sin_lam_lower (lam : ℝ) (hlam : 0 < lam) (w : ℂ)
    (h1 : 0 < lam * w.re) (h2 : lam * w.re < Real.pi) :
    (2 * lam / Real.pi) * min w.re (Real.pi / lam - w.re) ≤ ‖Complex.sin ((lam : ℂ) * w)‖ := by
  have hsinpos : 0 < Real.sin (lam * w.re) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hcosh : 1 ≤ Real.cosh (lam * w.im) := Real.one_le_cosh _
  have hre : (Complex.sin ((lam : ℂ) * w)).re = Real.sin (lam * w.re) * Real.cosh (lam * w.im) :=
    inbound_sin_re lam w
  have hle : Real.sin (lam * w.re) ≤ ‖Complex.sin ((lam : ℂ) * w)‖ := by
    calc Real.sin (lam * w.re) ≤ Real.sin (lam * w.re) * Real.cosh (lam * w.im) := by
          nlinarith [hsinpos.le, hcosh]
      _ = (Complex.sin ((lam : ℂ) * w)).re := hre.symm
      _ ≤ ‖Complex.sin ((lam : ℂ) * w)‖ := Complex.re_le_norm _
  have hj := jordan_sin_min lam w.re hlam h1 h2
  have hminmul : min (lam * w.re) (lam * (Real.pi / lam - w.re))
      = lam * min w.re (Real.pi / lam - w.re) := by
    rcases le_total w.re (Real.pi / lam - w.re) with hh | hh
    · rw [min_eq_left hh, min_eq_left (mul_le_mul_of_nonneg_left hh hlam.le)]
    · rw [min_eq_right hh, min_eq_right (mul_le_mul_of_nonneg_left hh hlam.le)]
  have hmul : (2 / Real.pi) * min (lam * w.re) (Real.pi - lam * w.re)
      = (2 * lam / Real.pi) * min w.re (Real.pi / lam - w.re) := by
    have hp : Real.pi - lam * w.re = lam * (Real.pi / lam - w.re) := by field_simp
    rw [hp, hminmul]
    ring
  calc (2 * lam / Real.pi) * min w.re (Real.pi / lam - w.re)
      = (2 / Real.pi) * min (lam * w.re) (Real.pi - lam * w.re) := hmul.symm
    _ ≤ Real.sin (lam * w.re) := hj
    _ ≤ ‖Complex.sin ((lam : ℂ) * w)‖ := hle

/-- Pointwise second-order Taylor bound for one model step. -/
private lemma rem_pw (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (u δ : ℂ) (hu1 : R / 4 + 2 ≤ u.re) (hu2 : R / 4 + 2 ≤ (u + δ).re)
    (hx2 : u.re ≤ Real.pi / lam - R / 4) (hdec : (u + δ).re ≤ u.re - 1 / 3) :
    ‖Complex.log (Complex.sin ((lam : ℂ) * (u + δ))) - Complex.log (Complex.sin ((lam : ℂ) * u))
        - δ * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖
      ≤ (Real.pi ^ 2 / 4) * ‖δ‖ ^ 2 / (min (u + δ).re (Real.pi / lam - u.re)) ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  set m : ℝ := min (u + δ).re (Real.pi / lam - u.re) with hmdef
  have hm1 : (0 : ℝ) < R / 4 := by linarith
  have hm2 : R / 4 ≤ Real.pi / lam - u.re := by linarith
  have hmpos : 0 < m := by rw [hmdef]; exact lt_min (by linarith) (by linarith)
  set c : ℝ := (2 * lam / Real.pi) * m with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact mul_pos (by positivity) hmpos
  have hred : δ.re = (u + δ).re - u.re := by simp [Complex.add_re]
  have htw : ∀ t : ℝ, (u + (t : ℂ) * δ).re = u.re + t * ((u + δ).re - u.re) := by
    intro t
    have h1 : (u + (t : ℂ) * δ).re = u.re + t * δ.re := by simp [Complex.add_re, Complex.mul_re]
    rw [h1, hred]
  have hup : lam * u.re ≤ Real.pi - lam * (R / 4) := by
    have h := mul_le_mul_of_nonneg_left hx2 hlam.le
    have he : lam * (Real.pi / lam - R / 4) = Real.pi - lam * (R / 4) := by field_simp
    linarith [h, he.le, he.ge]
  have hRp : 0 < lam * (R / 4) := by positivity
  have hkey := logSin_second_order lam c hlam hcpos u δ
    (fun t ht => by
      have h1 := htw t
      have ht' : (0 : ℝ) ≤ t := ht.1
      have ht'' : t ≤ 1 := ht.2
      have hlow : (u + δ).re ≤ (u + (t : ℂ) * δ).re := by nlinarith [ht', ht'', h1, hdec]
      nlinarith [hlam, le_trans hu2 hlow])
    (fun t ht => by
      have h1 := htw t
      have ht' : (0 : ℝ) ≤ t := ht.1
      have ht'' : t ≤ 1 := ht.2
      have hhigh : (u + (t : ℂ) * δ).re ≤ u.re := by nlinarith [ht', ht'', h1, hdec]
      have h2 := mul_le_mul_of_nonneg_left hhigh hlam.le
      linarith [h2, hup, hRp])
    (fun t ht => by
      have h1 := htw t
      have ht' : (0 : ℝ) ≤ t := ht.1
      have ht'' : t ≤ 1 := ht.2
      have hlow : (u + δ).re ≤ (u + (t : ℂ) * δ).re := by nlinarith [ht', ht'', h1, hdec]
      have hhigh : (u + (t : ℂ) * δ).re ≤ u.re := by nlinarith [ht', ht'', h1, hdec]
      have hgr1 : 0 < lam * (u + (t : ℂ) * δ).re := by nlinarith [hlam, le_trans hu2 hlow]
      have hgr2 : lam * (u + (t : ℂ) * δ).re < Real.pi := by
        have h2 := mul_le_mul_of_nonneg_left hhigh hlam.le
        linarith [h2, hup, hRp]
      have hlow2 := sin_lam_lower lam hlam (u + (t : ℂ) * δ) hgr1 hgr2
      have hmin : m ≤ min (u + (t : ℂ) * δ).re (Real.pi / lam - (u + (t : ℂ) * δ).re) := by
        rw [hmdef]
        exact min_le_min hlow (by linarith [hhigh])
      have hc : c ≤ (2 * lam / Real.pi)
          * min (u + (t : ℂ) * δ).re (Real.pi / lam - (u + (t : ℂ) * δ).re) := by
        rw [hcdef]
        exact mul_le_mul_of_nonneg_left hmin (by positivity)
      linarith [hlow2, hc])
  have hsq : lam ^ 2 / c ^ 2 = (Real.pi ^ 2 / 4) / m ^ 2 := by
    rw [hcdef]
    field_simp
    ring
  rw [hsq] at hkey
  calc ‖Complex.log (Complex.sin ((lam : ℂ) * (u + δ))) - Complex.log (Complex.sin ((lam : ℂ) * u))
        - δ * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖
      ≤ (Real.pi ^ 2 / 4 / m ^ 2) * ‖δ‖ ^ 2 := hkey
    _ = (Real.pi ^ 2 / 4) * ‖δ‖ ^ 2 / m ^ 2 := by ring

theorem sum_re_ecalPt_30 (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hrr : 16 ≤ R * r)
    (hτpi : (Real.pi / lam) * ‖τ - 1‖ ≤ 1 / (8 * R))
    (n : ℕ) (u : ℕ → ℂ)
    (hu : ∀ j < n, u (j + 1) = u j + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j))
    (htop : Real.pi / lam - 2 * R ≤ (u 0).re)
    (hxn : (u n).re ≤ R / 4 + 4)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3)
    (hzn : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ≤ 4 / R)
    (hzr : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ < r)
    (hy0 : |(u 0).im| ≤ R / 4 + 4 + Real.log R)
    (hstep : ∀ j ≤ n, (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).re
          ≤ -1 + 35 * lam ^ 2 + (B + 8) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖
            - (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
                - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
            + 35 * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
        ∧ -1 - 35 * lam ^ 2 - (B + 2) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖
            - (A + 35) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
          ≤ (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).re)
    (hS : ∑ j ∈ Finset.range n,
        ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2 ≤ 24 / R) :
    |∑ j ∈ Finset.range n, (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re|
      ≤ 30 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg h1) hh1
  have hBle : B ≤ 3 * R / 32 := by
    have h2 : 4 * B / R ≤ 3 / 8 := by
      have : (0 : ℝ) ≤ 16 * A / R ^ 2 := by positivity
      linarith
    rw [div_le_iff₀ hRpos] at h2
    linarith
  have hAle : A ≤ 3 * R ^ 2 / 128 := by
    have h2 : 16 * A / R ^ 2 ≤ 3 / 8 := by
      have : (0 : ℝ) ≤ 4 * B / R := by positivity
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2)] at h2
    linarith
  have hτle : ‖τ - 1‖ ≤ lam / (8 * Real.pi * R) := by
    have h2 : (lam / Real.pi) * ((Real.pi / lam) * ‖τ - 1‖) = ‖τ - 1‖ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left hτpi (by positivity : (0 : ℝ) ≤ lam / Real.pi)
    have h4 : (lam / Real.pi) * (1 / (8 * R)) = lam / (8 * Real.pi * R) := by
      field_simp
    linarith [h2.le, h2.ge, h3, h4.le, h4.ge]
  have hτ2 : ‖h1 - τ ^ 2‖ ≤ B + 1 := by
    have h1' := norm_sub_le h1 (τ ^ 2)
    rw [norm_pow] at h1'
    rw [hb.2.1, one_pow] at h1'
    linarith
  have hlogR : Real.log R ≤ R / 4 + 3 := log_quarter_add_three R (by linarith)
  set ζ : ℕ → ℂ := fun j => Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j) with hζ
  set δ : ℕ → ℂ := fun j => Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j) with hδ
  set Ω : ℕ → ℂ := fun j => 1 + δ j with hΩ
  set Rj : ℕ → ℂ := fun j => Complex.log (Complex.sin ((lam : ℂ) * (u (j + 1))))
      - Complex.log (Complex.sin ((lam : ℂ) * (u j))) - δ j * ζ j with hRj
  set ee : ℕ → ℝ := fun j => (δ j).im + (τ + (h1 - τ ^ 2) * ζ j).im with hee
  set Ψ : ℂ := ∑ j ∈ Finset.range n, ζ j with hΨ
  have hzn' : ∀ j ≤ n, ‖ζ j‖ ≤ 4 / R := by intro j hj; rw [hζ]; exact hzn j hj
  have hzr' : ∀ j ≤ n, ‖ζ j‖ < r := by intro j hj; rw [hζ]; exact hzr j hj
  have hS' : ∑ j ∈ Finset.range n, ‖ζ j‖ ^ 2 ≤ 24 / R := by rw [hζ]; exact hS
  -- number of steps
  have hnle : (n : ℝ) ≤ 3 * (Real.pi / lam) := by
    have h5 : ∀ k ≤ n, (u k).re + (k : ℝ) * (1 / 3) ≤ (u 0).re := by
      intro k hk
      induction k with
      | zero => simp
      | succ j ihj =>
        have hj : j ≤ n := le_trans (Nat.le_succ j) hk
        have ihj' := ihj hj
        have hjlt : j < n := lt_of_lt_of_le (Nat.lt_succ_self j) hk
        have hd := hdec j hjlt
        have hgoal : (u (j + 1)).re + ((j : ℝ) + 1) * (1 / 3) ≤ (u 0).re := by
          have h6 : ((j : ℝ) + 1) * (1 / 3) = (j : ℝ) * (1 / 3) + 1 / 3 := by ring
          rw [h6]; linarith
        simpa [Nat.cast_add, Nat.cast_one] using hgoal
    have h6 := h5 n le_rfl
    have h7 : (u 0).re ≤ Real.pi / lam - R / 4 := hx2 0 (Nat.zero_le n)
    have h8 : R / 4 + 2 ≤ (u n).re := hx1 n le_rfl
    have h9 : (n : ℝ) * (1 / 3) ≤ Real.pi / lam - R / 2 - 2 := by linarith
    have h10 : (n : ℝ) * (1 / 3) ≤ Real.pi / lam := by linarith
    nlinarith [h10]
  -- basic sums
  have hsumZ : ∑ j ∈ Finset.range n, ‖ζ j‖ ≤ 12 * Real.pi / (lam * R) := by
    calc ∑ j ∈ Finset.range n, ‖ζ j‖ ≤ ∑ j ∈ Finset.range n, (4 / R) :=
          Finset.sum_le_sum (fun j hj => hzn' j (le_of_lt (Finset.mem_range.mp hj)))
      _ = (n : ℝ) * (4 / R) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (3 * (Real.pi / lam)) * (4 / R) :=
          mul_le_mul_of_nonneg_right hnle (by apply div_nonneg (by norm_num) hRpos.le)
      _ = 12 * Real.pi / (lam * R) := by ring_nf
  have hsumZ3 : ∑ j ∈ Finset.range n, ‖ζ j‖ ^ 3 ≤ 96 / R ^ 2 := by
    calc ∑ j ∈ Finset.range n, ‖ζ j‖ ^ 3
        = ∑ j ∈ Finset.range n, ‖ζ j‖ ^ 2 * ‖ζ j‖ := by
          apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ ∑ j ∈ Finset.range n, ‖ζ j‖ ^ 2 * (4 / R) := by
          apply Finset.sum_le_sum; intro j hj
          exact mul_le_mul_of_nonneg_left (hzn' j (le_of_lt (Finset.mem_range.mp hj)))
            (by positivity)
      _ = (4 / R) * ∑ j ∈ Finset.range n, ‖ζ j‖ ^ 2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ (4 / R) * (24 / R) := mul_le_mul_of_nonneg_left hS' (by positivity)
      _ = 96 / R ^ 2 := by ring_nf
  -- the plain second-order decomposition of `δ j`
  have hdecomp : ∀ j < n, ‖δ j + (τ + (h1 - τ ^ 2) * ζ j)‖
      ≤ 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2 := by
    intro j hj
    have hdev := modelDisp_im_decomp lam R hlam hR hlamR h τ h1 A r hA hr hb hτ1 (u j)
      (hzn' j (le_of_lt hj)) (hzr' j (le_of_lt hj))
    simp only [hδ, hζ] at hdev ⊢
    have hh1 : (2 + 4 * ‖h1‖ + 2 * A) ≤ (2 + 4 * B + 2 * A) := by linarith
    have hnn : (0 : ℝ) ≤ ‖(Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j))‖ ^ 2 := by
      positivity
    nlinarith [hdev, hnn, hh1]
  -- modulus bound on the displacement
  have hdelta3 : ∀ j < n, ‖δ j‖ ≤ 3 := by
    intro j hj
    have hdec' := hdecomp j hj
    have ht2 : ‖τ + (h1 - τ ^ 2) * ζ j‖ ≤ 1 + (B + 1) * (4 / R) := by
      have h1' : ‖τ + (h1 - τ ^ 2) * ζ j‖ ≤ ‖τ‖ + ‖(h1 - τ ^ 2) * ζ j‖ := norm_add_le _ _
      have h2' : ‖(h1 - τ ^ 2) * ζ j‖ ≤ (B + 1) * (4 / R) := by
        rw [norm_mul]
        exact mul_le_mul hτ2 (hzn' j (le_of_lt hj)) (norm_nonneg _) (by linarith)
      have h3' : ‖τ‖ = 1 := hb.2.1
      linarith [h1', h2', h3'.le, h3'.ge]
    have htri : ‖δ j‖ ≤ ‖δ j + (τ + (h1 - τ ^ 2) * ζ j)‖ + ‖τ + (h1 - τ ^ 2) * ζ j‖ := by
      have h := norm_add_le (δ j + (τ + (h1 - τ ^ 2) * ζ j)) (-(τ + (h1 - τ ^ 2) * ζ j))
      have he : δ j + (τ + (h1 - τ ^ 2) * ζ j) + -(τ + (h1 - τ ^ 2) * ζ j) = δ j := by ring
      rwa [he, norm_neg] at h
    have hnum : 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2 ≤ 11 / 10 := by
      have hζ2 : ‖ζ j‖ ^ 2 ≤ 16 / R ^ 2 := by
        have h := hzn' j (le_of_lt hj)
        have h0 : (0 : ℝ) ≤ 4 / R := by apply div_nonneg (by norm_num) hRpos.le
        have h9 : (16 : ℝ) / R ^ 2 = (4 / R) ^ 2 := by field_simp; ring
        nlinarith [h, norm_nonneg (ζ j), h0, h9]
      have h1' : (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2 ≤ (2 + 3 * R / 8 + 3 * R ^ 2 / 64) * (16 / R ^ 2) := by
        apply mul_le_mul _ hζ2 (by positivity)
          (by linarith : (0 : ℝ) ≤ 2 + 3 * R / 8 + 3 * R ^ 2 / 64)
        linarith
      have h3' : (2 + 3 * R / 8 + 3 * R ^ 2 / 64) * (16 / R ^ 2) ≤ 1 := by
        rw [← mul_div_assoc, div_le_iff₀ (pow_pos hRpos 2)]
        nlinarith [hR]
      have h4' : 100 * lam ^ 2 ≤ 1 / 10 := by
        have h6' : lam ≤ 1 / R ^ 2 := by
          rw [le_div_iff₀ (pow_pos hRpos 2)]; linarith
        have h32 : (32 : ℝ) ≤ R ^ 2 := by nlinarith [hR]
        have h7' : (1 : ℝ) / R ^ 2 ≤ 1 / 32 := by
          rw [div_le_div_iff₀ (pow_pos hRpos 2) (by norm_num : (0 : ℝ) < 32)]
          linarith
        have h8' : lam ≤ 1 / 32 := le_trans h6' h7'
        nlinarith [h8', hlam.le]
      linarith [h1', h3', h4']
    have h4'' : 1 + (B + 1) * (4 / R) ≤ 3 / 2 := by
      have h5' : (B + 1) * (4 / R) ≤ (3 * R / 32 + 1) * (4 / R) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h6' : (3 * R / 32 + 1) * (4 / R) ≤ 1 / 2 := by
        rw [← mul_div_assoc, div_le_iff₀ hRpos]; linarith
      linarith [h5', h6']
    linarith [htri, ht2, hdec', hnum, h4'']
  -- the remainder sum
  have hRjsum : ∑ j ∈ Finset.range n, ‖Rj j‖ ≤ 576 / R := by
    have hper : ∀ j ∈ Finset.range n, ‖Rj j‖
        ≤ 9 * ((Real.pi ^ 2 / 4) / (min ((u (j + 1)).re) (Real.pi / lam - (u j).re)) ^ 2) := by
      intro j hj
      have hjlt : j < n := Finset.mem_range.mp hj
      have huj : u j + δ j = u (j + 1) := by rw [hδ]; exact (hu j hjlt).symm
      have h1 := rem_pw lam R hlam hR hlamR (u j) (δ j) (hx1 j (le_of_lt hjlt))
        (by rw [huj]; exact hx1 (j + 1) (Nat.succ_le_of_lt hjlt)) (hx2 j (le_of_lt hjlt))
        (by rw [huj]; exact hdec j hjlt)
      rw [huj] at h1
      have hd3 : ‖δ j‖ ≤ 3 := hdelta3 j hjlt
      have hden : 0 < (min ((u (j + 1)).re) (Real.pi / lam - (u j).re)) ^ 2 := by
        apply pow_pos
        rw [lt_min_iff]
        exact ⟨by linarith [hx1 (j + 1) (Nat.succ_le_of_lt hjlt)],
          by linarith [hx2 j (le_of_lt hjlt)]⟩
      have hRjval : Rj j = Complex.log (Complex.sin ((lam : ℂ) * (u (j + 1))))
          - Complex.log (Complex.sin ((lam : ℂ) * (u j))) - δ j * ζ j := by rw [hRj, hζ]
      rw [hRjval]
      calc ‖Complex.log (Complex.sin ((lam : ℂ) * (u (j + 1))))
            - Complex.log (Complex.sin ((lam : ℂ) * (u j))) - δ j * ζ j‖
          ≤ (Real.pi ^ 2 / 4) * ‖δ j‖ ^ 2
              / (min ((u (j + 1)).re) (Real.pi / lam - (u j).re)) ^ 2 := h1
        _ ≤ (Real.pi ^ 2 / 4) * 9
              / (min ((u (j + 1)).re) (Real.pi / lam - (u j).re)) ^ 2 := by
            apply div_le_div_of_nonneg_right _ hden.le
            have h9 : ‖δ j‖ ^ 2 ≤ 9 := by nlinarith [hd3, norm_nonneg (δ j)]
            exact mul_le_mul_of_nonneg_left h9 (by positivity)
        _ = 9 * ((Real.pi ^ 2 / 4) / (min ((u (j + 1)).re) (Real.pi / lam - (u j).re)) ^ 2) := by
            ring
    calc ∑ j ∈ Finset.range n, ‖Rj j‖
        ≤ ∑ j ∈ Finset.range n, 9 * ((Real.pi ^ 2 / 4)
            / (min ((u (j + 1)).re) (Real.pi / lam - (u j).re)) ^ 2) := Finset.sum_le_sum hper
      _ = 9 * ∑ j ∈ Finset.range n, ((Real.pi ^ 2 / 4)
            / (min ((u (j + 1)).re) (Real.pi / lam - (u j).re)) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 9 * (64 / R) := by
          have h := sum_min_inv_sq_le lam R (fun j => (u j).re) n hlam hR hlamR hx1 hx2 hdec
          linarith
      _ = 576 / R := by ring

  -- ### the telescoping identity
  have htel : Ψ = -(Complex.log (Complex.sin ((lam : ℂ) * (u n)))
          - Complex.log (Complex.sin ((lam : ℂ) * (u 0))))
        + ∑ j ∈ Finset.range n, Rj j + ∑ j ∈ Finset.range n, Ω j * ζ j := by
    have hsumF : ∑ j ∈ Finset.range n, (Complex.log (Complex.sin ((lam : ℂ) * (u (j + 1))))
        - Complex.log (Complex.sin ((lam : ℂ) * (u j))))
        = Complex.log (Complex.sin ((lam : ℂ) * (u n)))
          - Complex.log (Complex.sin ((lam : ℂ) * (u 0))) :=
      Finset.sum_range_sub (fun j => Complex.log (Complex.sin ((lam : ℂ) * (u j)))) n
    have hRs : ∑ j ∈ Finset.range n, Rj j
        = (Complex.log (Complex.sin ((lam : ℂ) * (u n)))
            - Complex.log (Complex.sin ((lam : ℂ) * (u 0))))
          - ∑ j ∈ Finset.range n, δ j * ζ j := by
      calc ∑ j ∈ Finset.range n, Rj j
          = ∑ j ∈ Finset.range n, ((Complex.log (Complex.sin ((lam : ℂ) * (u (j + 1))))
              - Complex.log (Complex.sin ((lam : ℂ) * (u j)))) - δ j * ζ j) := by
            apply Finset.sum_congr rfl; intro j _; rw [hRj]
        _ = (∑ j ∈ Finset.range n, (Complex.log (Complex.sin ((lam : ℂ) * (u (j + 1))))
              - Complex.log (Complex.sin ((lam : ℂ) * (u j)))))
            - ∑ j ∈ Finset.range n, δ j * ζ j := by rw [Finset.sum_sub_distrib]
        _ = (Complex.log (Complex.sin ((lam : ℂ) * (u n)))
            - Complex.log (Complex.sin ((lam : ℂ) * (u 0))))
          - ∑ j ∈ Finset.range n, δ j * ζ j := by rw [hsumF]
    have hωs : ∑ j ∈ Finset.range n, δ j * ζ j
        = -Ψ + ∑ j ∈ Finset.range n, Ω j * ζ j := by
      have h1 : ∀ j ∈ Finset.range n, δ j * ζ j = -(ζ j) + Ω j * ζ j := by
        intro j _; rw [hΩ]; ring
      calc ∑ j ∈ Finset.range n, δ j * ζ j
          = ∑ j ∈ Finset.range n, (-(ζ j) + Ω j * ζ j) := Finset.sum_congr rfl h1
        _ = (∑ j ∈ Finset.range n, -(ζ j)) + ∑ j ∈ Finset.range n, Ω j * ζ j := by
            rw [Finset.sum_add_distrib]
        _ = -(∑ j ∈ Finset.range n, ζ j) + ∑ j ∈ Finset.range n, Ω j * ζ j := by
            rw [Finset.sum_neg_distrib]
        _ = -Ψ + ∑ j ∈ Finset.range n, Ω j * ζ j := by rw [hΨ]
    rw [hRs, hωs]
    ring
  -- ### the `‖Ω j‖ ‖ζ j‖` sum
  have hQ : ∑ j ∈ Finset.range n, ‖Ω j‖ * ‖ζ j‖ ≤ 12 := by
    have hper : ∀ j ∈ Finset.range n, ‖Ω j‖ * ‖ζ j‖
        ≤ ‖τ - 1‖ * ‖ζ j‖ + (B + 1) * ‖ζ j‖ ^ 2 + 100 * lam ^ 2 * ‖ζ j‖
          + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 3 := by
      intro j hj
      have hjlt : j < n := Finset.mem_range.mp hj
      have h3 : ‖Ω j - (1 - τ - (h1 - τ ^ 2) * ζ j)‖
          ≤ 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2 := by
        have he : Ω j - (1 - τ - (h1 - τ ^ 2) * ζ j) = δ j + (τ + (h1 - τ ^ 2) * ζ j) := by
          rw [hΩ]; ring
        rw [he]; exact hdecomp j hjlt
      have h4 : ‖1 - τ - (h1 - τ ^ 2) * ζ j‖ ≤ ‖τ - 1‖ + (B + 1) * ‖ζ j‖ := by
        have h5 : ‖1 - τ - (h1 - τ ^ 2) * ζ j‖ ≤ ‖1 - τ‖ + ‖(h1 - τ ^ 2) * ζ j‖ :=
          norm_sub_le _ _
        have h6 : ‖(h1 - τ ^ 2) * ζ j‖ ≤ (B + 1) * ‖ζ j‖ := by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right hτ2 (norm_nonneg _)
        have h7 : ‖1 - τ‖ = ‖τ - 1‖ := by rw [← norm_neg]; ring_nf
        linarith [h5, h6, h7.le, h7.ge]
      have hsplit : Ω j = (Ω j - (1 - τ - (h1 - τ ^ 2) * ζ j)) + (1 - τ - (h1 - τ ^ 2) * ζ j) := by
        ring
      have h2 : ‖Ω j‖ ≤ ‖τ - 1‖ + (B + 1) * ‖ζ j‖ + 100 * lam ^ 2
          + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2 := by
        have hb : ‖Ω j‖ ≤ ‖Ω j - (1 - τ - (h1 - τ ^ 2) * ζ j)‖
            + ‖1 - τ - (h1 - τ ^ 2) * ζ j‖ := by
          have h := norm_add_le (Ω j - (1 - τ - (h1 - τ ^ 2) * ζ j))
            (1 - τ - (h1 - τ ^ 2) * ζ j)
          have he : (Ω j - (1 - τ - (h1 - τ ^ 2) * ζ j))
              + (1 - τ - (h1 - τ ^ 2) * ζ j) = Ω j := by ring
          rwa [he] at h
        linarith [hb, h3, h4]
      calc ‖Ω j‖ * ‖ζ j‖ ≤ (‖τ - 1‖ + (B + 1) * ‖ζ j‖ + 100 * lam ^ 2
            + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2) * ‖ζ j‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖τ - 1‖ * ‖ζ j‖ + (B + 1) * ‖ζ j‖ ^ 2 + 100 * lam ^ 2 * ‖ζ j‖
            + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 3 := by ring
    have hsum_v : ∑ j ∈ Finset.range n, (‖τ - 1‖ * ‖ζ j‖ + (B + 1) * ‖ζ j‖ ^ 2
          + 100 * lam ^ 2 * ‖ζ j‖ + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 3)
        = ‖τ - 1‖ * (∑ j ∈ Finset.range n, ‖ζ j‖)
          + (B + 1) * (∑ j ∈ Finset.range n, ‖ζ j‖ ^ 2)
          + 100 * lam ^ 2 * (∑ j ∈ Finset.range n, ‖ζ j‖)
          + (2 + 4 * B + 2 * A) * (∑ j ∈ Finset.range n, ‖ζ j‖ ^ 3) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    have hp1 : ‖τ - 1‖ * (∑ j ∈ Finset.range n, ‖ζ j‖) ≤ 1 := by
      have hden : (0 : ℝ) < lam / (8 * Real.pi * R) :=
        div_pos hlam (by positivity : (0 : ℝ) < 8 * Real.pi * R)
      have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, ‖ζ j‖ :=
        Finset.sum_nonneg (fun j _ => norm_nonneg _)
      have h2 := mul_le_mul hτle hsumZ hsum0 (le_of_lt hden)
      have h3 : (lam / (8 * Real.pi * R)) * (12 * Real.pi / (lam * R)) = 3 / (2 * R ^ 2) := by
        field_simp; ring
      have h4 : (3 : ℝ) / (2 * R ^ 2) ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R ^ 2)]
        nlinarith [hR]
      linarith [h2, h3.le, h3.ge, h4]
    have hp2 : (B + 1) * (∑ j ∈ Finset.range n, ‖ζ j‖ ^ 2) ≤ 3 := by
      have h3 := mul_le_mul_of_nonneg_left hS' (by linarith : (0 : ℝ) ≤ B + 1)
      have h4 : (B + 1) * (24 / R) ≤ (3 * R / 32 + 1) * (24 / R) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h5 : (3 * R / 32 + 1) * (24 / R) ≤ 3 := by
        rw [← mul_div_assoc, div_le_iff₀ hRpos]; linarith
      linarith [h3, h4, h5]
    have hp3 : 100 * lam ^ 2 * (∑ j ∈ Finset.range n, ‖ζ j‖) ≤ 1 := by
      have h4 := mul_le_mul_of_nonneg_left hsumZ (by positivity : (0 : ℝ) ≤ 100 * lam ^ 2)
      have h5 : 100 * lam ^ 2 * (12 * Real.pi / (lam * R)) = 1200 * Real.pi * lam / R := by
        field_simp; ring
      have h6 : 1200 * Real.pi * lam / R ≤ 1 := by
        rw [div_le_iff₀ hRpos]
        have hl : lam ≤ 1 / R ^ 2 := by
          rw [le_div_iff₀ (pow_pos hRpos 2)]; exact hlamR
        have hR2' : (48 : ℝ) ≤ R ^ 2 := by nlinarith [hR]
        have hR3 : (4800 : ℝ) ≤ R ^ 3 := by nlinarith [hR2', hR, sq_nonneg R]
        have hpi : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
        have h1 : 1200 * Real.pi * lam ≤ 4800 * (1 / R ^ 2) := by
          have h0 : (0 : ℝ) ≤ 1200 * Real.pi := by positivity
          nlinarith [hl, hpi, hlam]
        have h2 : 4800 * (1 / R ^ 2) ≤ R := by
          rw [mul_one_div, div_le_iff₀ (pow_pos hRpos 2)]
          nlinarith [hR3, hR]
        linarith [h1, h2]
      linarith [h4, h5.le, h5.ge, h6]
    have hp4 : (2 + 4 * B + 2 * A) * (∑ j ∈ Finset.range n, ‖ζ j‖ ^ 3) ≤ 6 := by
      have h5 : 2 + 4 * B + 2 * A ≤ 2 + 3 * R / 8 + 3 * R ^ 2 / 64 := by linarith
      have h6 := mul_le_mul h5 hsumZ3 (by positivity)
        (by linarith : (0 : ℝ) ≤ 2 + 3 * R / 8 + 3 * R ^ 2 / 64)
      have h7 : (2 + 3 * R / 8 + 3 * R ^ 2 / 64) * (96 / R ^ 2) ≤ 6 := by
        rw [← mul_div_assoc, div_le_iff₀ (pow_pos hRpos 2)]
        nlinarith [hR]
      linarith [h6, h7]
    calc ∑ j ∈ Finset.range n, ‖Ω j‖ * ‖ζ j‖
        ≤ ∑ j ∈ Finset.range n, (‖τ - 1‖ * ‖ζ j‖ + (B + 1) * ‖ζ j‖ ^ 2
            + 100 * lam ^ 2 * ‖ζ j‖ + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 3) := Finset.sum_le_sum hper
      _ = _ := hsum_v
      _ ≤ 1 + 3 + 1 + 6 := by linarith [hp1, hp2, hp3, hp4]
      _ ≤ 12 := by norm_num

  -- ### the boundary term `F = log sin(λ u_n) - log sin(λ u_0)`
  set F : ℂ := Complex.log (Complex.sin ((lam : ℂ) * (u n)))
      - Complex.log (Complex.sin ((lam : ℂ) * (u 0))) with hFdef
  have hFre : F.re = Real.log ‖Complex.sin ((lam : ℂ) * (u n))‖
      - Real.log ‖Complex.sin ((lam : ℂ) * (u 0))‖ := by
    rw [hFdef, Complex.sub_re, Complex.log_re, Complex.log_re]
  have hFre_abs : |F.re| ≤ 10 + Real.log (1 + Real.sinh (lam * |(u n).im|) / (lam * R)) := by
    rw [hFre]
    exact logSin_endpoints_le lam R hlam hR hlamR (u n) (u 0) (hx1 n le_rfl) hxn htop
      (hx2 0 (Nat.zero_le n)) hy0
  have hFim_abs : |F.im| ≤ 2 * Real.pi := by
    have h2 : F.im = (Complex.log (Complex.sin ((lam : ℂ) * (u n)))).im
        - (Complex.log (Complex.sin ((lam : ℂ) * (u 0)))).im := by rw [hFdef, Complex.sub_im]
    rw [h2, Complex.log_im, Complex.log_im]
    have h1 := Complex.neg_pi_lt_arg (Complex.sin ((lam : ℂ) * (u n)))
    have h2' := Complex.arg_le_pi (Complex.sin ((lam : ℂ) * (u n)))
    have h3 := Complex.neg_pi_lt_arg (Complex.sin ((lam : ℂ) * (u 0)))
    have h4 := Complex.arg_le_pi (Complex.sin ((lam : ℂ) * (u 0)))
    rw [abs_le]; constructor <;> linarith
  have htel' : Ψ = -F + ∑ j ∈ Finset.range n, Rj j + ∑ j ∈ Finset.range n, Ω j * ζ j := by
    rw [hFdef]; exact htel
  have h576 : 576 / R ≤ 4.5 := by
    rw [div_le_iff₀ hRpos]; linarith [hR]
  have hΩsum : ∑ j ∈ Finset.range n, ‖Ω j * ζ j‖ ≤ 12 := by
    calc ∑ j ∈ Finset.range n, ‖Ω j * ζ j‖ = ∑ j ∈ Finset.range n, ‖Ω j‖ * ‖ζ j‖ := by
          apply Finset.sum_congr rfl; intro j _; rw [norm_mul]
      _ ≤ 12 := hQ
  have hSbound : |Ψ.re| ≤ 10 + Real.log (1 + Real.sinh (lam * |(u n).im|) / (lam * R))
      + 576 / R + 12 := by
    have h2 : Ψ.re = -(F.re) + (∑ j ∈ Finset.range n, Rj j).re
        + (∑ j ∈ Finset.range n, Ω j * ζ j).re := by
      rw [htel']; simp only [Complex.add_re, Complex.neg_re]
    have h3 : |(∑ j ∈ Finset.range n, Rj j).re| ≤ 576 / R :=
      le_trans (Complex.abs_re_le_norm _) (le_trans (norm_sum_le _ _) hRjsum)
    have h4 : |(∑ j ∈ Finset.range n, Ω j * ζ j).re| ≤ 12 :=
      le_trans (Complex.abs_re_le_norm _) (le_trans (norm_sum_le _ _) hΩsum)
    rw [h2]
    have ha := abs_add_le (-(F.re) + (∑ j ∈ Finset.range n, Rj j).re)
      ((∑ j ∈ Finset.range n, Ω j * ζ j).re)
    have hb := abs_add_le (-(F.re)) ((∑ j ∈ Finset.range n, Rj j).re)
    have hc : |-(F.re)| = |F.re| := abs_neg _
    linarith [ha, hb, hc.le, hc.ge, h3, h4, hFre_abs]
  have hTbound : |Ψ.im| ≤ 2 * Real.pi + 576 / R + 12 := by
    have h2 : Ψ.im = -(F.im) + (∑ j ∈ Finset.range n, Rj j).im
        + (∑ j ∈ Finset.range n, Ω j * ζ j).im := by
      rw [htel']; simp only [Complex.add_im, Complex.neg_im]
    have h3 : |(∑ j ∈ Finset.range n, Rj j).im| ≤ 576 / R :=
      le_trans (Complex.abs_im_le_norm _) (le_trans (norm_sum_le _ _) hRjsum)
    have h4 : |(∑ j ∈ Finset.range n, Ω j * ζ j).im| ≤ 12 :=
      le_trans (Complex.abs_im_le_norm _) (le_trans (norm_sum_le _ _) hΩsum)
    rw [h2]
    have ha := abs_add_le (-(F.im) + (∑ j ∈ Finset.range n, Rj j).im)
      ((∑ j ∈ Finset.range n, Ω j * ζ j).im)
    have hb := abs_add_le (-(F.im)) ((∑ j ∈ Finset.range n, Rj j).im)
    have hc : |-(F.im)| = |F.im| := abs_neg _
    linarith [ha, hb, hc.le, hc.ge, h3, h4, hFim_abs]
  -- ### the height (imaginary part) drift
  have hiter0 : ∀ m ≤ n, u m = u 0
      + ∑ j ∈ Finset.range m, Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkn : k ≤ n := le_trans (Nat.le_succ k) hk
      have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [hu k hklt, ih hkn, Finset.sum_range_succ]
      rw [ih hkn]
      ring
  have hiter : ∀ m ≤ n, u m = u 0 + ∑ j ∈ Finset.range m, δ j := by
    intro m hm
    simpa only [hδ] using hiter0 m hm
  have himu : (u n).im = (u 0).im + ∑ j ∈ Finset.range n, (δ j).im := by
    rw [hiter n le_rfl, Complex.add_im]
    congr 1
    simpa using map_sum Complex.imAddGroupHom δ (Finset.range n)
  have heeb : ∀ j < n, |ee j| ≤ 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2 := by
    intro j hj
    have h5 : |(δ j + (τ + (h1 - τ ^ 2) * ζ j)).im|
        ≤ ‖δ j + (τ + (h1 - τ ^ 2) * ζ j)‖ := Complex.abs_im_le_norm _
    have h6 : (δ j + (τ + (h1 - τ ^ 2) * ζ j)).im
        = (δ j).im + (τ + (h1 - τ ^ 2) * ζ j).im := Complex.add_im _ _
    have h7 : |(δ j).im + (τ + (h1 - τ ^ 2) * ζ j).im|
        ≤ ‖δ j + (τ + (h1 - τ ^ 2) * ζ j)‖ := by rw [← h6]; exact h5
    show |(δ j).im + (τ + (h1 - τ ^ 2) * ζ j).im|
        ≤ 100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2
    linarith [h7, hdecomp j hj]
  have hsumim : ∑ j ∈ Finset.range n, (δ j).im
      = -((n : ℝ) * τ.im) - ((h1 - τ ^ 2) * Ψ).im + ∑ j ∈ Finset.range n, ee j := by
    have hpt : ∀ j ∈ Finset.range n, (δ j).im
        = (-τ.im) + (-(((h1 - τ ^ 2) * ζ j).im)) + ee j := by
      intro j _
      have h2 : (τ + (h1 - τ ^ 2) * ζ j).im = τ.im + ((h1 - τ ^ 2) * ζ j).im :=
        Complex.add_im _ _
      show (δ j).im = (-τ.im) + (-(((h1 - τ ^ 2) * ζ j).im))
        + ((δ j).im + (τ + (h1 - τ ^ 2) * ζ j).im)
      linarith [h2]
    have hlin : ∑ j ∈ Finset.range n, ((h1 - τ ^ 2) * ζ j).im = ((h1 - τ ^ 2) * Ψ).im := by
      have hA : (∑ j ∈ Finset.range n, (h1 - τ ^ 2) * ζ j).im
          = ∑ j ∈ Finset.range n, ((h1 - τ ^ 2) * ζ j).im := by
        simpa using map_sum Complex.imAddGroupHom (fun j => (h1 - τ ^ 2) * ζ j)
          (Finset.range n)
      rw [← hA, ← Finset.mul_sum, hΨ]
    calc ∑ j ∈ Finset.range n, (δ j).im
        = ∑ j ∈ Finset.range n, ((-τ.im) + (-(((h1 - τ ^ 2) * ζ j).im)) + ee j) :=
          Finset.sum_congr rfl hpt
      _ = (∑ j ∈ Finset.range n, ((-τ.im) + (-(((h1 - τ ^ 2) * ζ j).im))))
            + ∑ j ∈ Finset.range n, ee j := by rw [Finset.sum_add_distrib]
      _ = ((∑ j ∈ Finset.range n, (-τ.im))
            + ∑ j ∈ Finset.range n, (-(((h1 - τ ^ 2) * ζ j).im)))
            + ∑ j ∈ Finset.range n, ee j := by rw [Finset.sum_add_distrib]
      _ = -((n : ℝ) * τ.im) - ∑ j ∈ Finset.range n, ((h1 - τ ^ 2) * ζ j).im
            + ∑ j ∈ Finset.range n, ee j := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_neg_distrib]
          ring
      _ = -((n : ℝ) * τ.im) - ((h1 - τ ^ 2) * Ψ).im + ∑ j ∈ Finset.range n, ee j := by
          rw [hlin]
  have hdrift : lam * |(u n).im| ≤ lam * |(u 0).im| + lam * ((n : ℝ) * |τ.im|)
      + lam * ((B + 1) * ‖Ψ‖)
      + lam * ∑ j ∈ Finset.range n, (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2) := by
    have hexp : (u n).im = (u 0).im + (-((n : ℝ) * τ.im))
        + (-((h1 - τ ^ 2) * Ψ).im) + ∑ j ∈ Finset.range n, ee j := by
      rw [himu, hsumim]; ring
    have hsum_ee : |∑ j ∈ Finset.range n, ee j|
        ≤ ∑ j ∈ Finset.range n, (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum (fun j hj => heeb j (Finset.mem_range.mp hj)))
    have hnτ : |(n : ℝ) * τ.im| = (n : ℝ) * |τ.im| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have hΨim : |((h1 - τ ^ 2) * Ψ).im| ≤ (B + 1) * ‖Ψ‖ := by
      calc |((h1 - τ ^ 2) * Ψ).im| ≤ ‖(h1 - τ ^ 2) * Ψ‖ := Complex.abs_im_le_norm _
        _ = ‖h1 - τ ^ 2‖ * ‖Ψ‖ := norm_mul _ _
        _ ≤ (B + 1) * ‖Ψ‖ := mul_le_mul_of_nonneg_right hτ2 (norm_nonneg _)
    have h0 : |(u n).im| ≤ |(u 0).im| + (n : ℝ) * |τ.im| + (B + 1) * ‖Ψ‖
        + ∑ j ∈ Finset.range n, (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2) := by
      rw [hexp]
      have ha1 := abs_add_le ((u 0).im + (-((n : ℝ) * τ.im)) + (-((h1 - τ ^ 2) * Ψ).im))
        (∑ j ∈ Finset.range n, ee j)
      have ha2 : |(u 0).im + (-((n : ℝ) * τ.im)) + (-((h1 - τ ^ 2) * Ψ).im)|
          ≤ |(u 0).im + (-((n : ℝ) * τ.im))| + |((h1 - τ ^ 2) * Ψ).im| := by
        have h := abs_add_le ((u 0).im + (-((n : ℝ) * τ.im))) (-((h1 - τ ^ 2) * Ψ).im)
        rw [abs_neg] at h
        exact h
      have ha3 : |(u 0).im + (-((n : ℝ) * τ.im))| ≤ |(u 0).im| + (n : ℝ) * |τ.im| := by
        have h := abs_add_le ((u 0).im) (-((n : ℝ) * τ.im))
        rw [abs_neg, hnτ] at h
        linarith [h]
      linarith [ha1, ha2, ha3, hsum_ee, hΨim]
    calc lam * |(u n).im| ≤ lam * (|(u 0).im| + (n : ℝ) * |τ.im| + (B + 1) * ‖Ψ‖
            + ∑ j ∈ Finset.range n, (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h0 hlam.le
      _ = lam * |(u 0).im| + lam * ((n : ℝ) * |τ.im|) + lam * ((B + 1) * ‖Ψ‖)
            + lam * ∑ j ∈ Finset.range n,
                (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2) := by ring

  -- ### the numeric drift bound
  have hτim : |τ.im| ≤ ‖τ - 1‖ := by
    have h := Complex.abs_im_le_norm (τ - 1)
    rwa [Complex.sub_im, Complex.one_im, sub_zero] at h
  have hdrift2 : lam * |(u n).im| ≤ (lam * R) * (2.3 + 0.103 * ‖Ψ‖) := by
    have h1 : lam * |(u 0).im| ≤ lam * R * 1 := by
      have h1' : |(u 0).im| ≤ R := by linarith [hy0, hlogR, hR]
      calc lam * |(u 0).im| ≤ lam * R := mul_le_mul_of_nonneg_left h1' hlam.le
        _ = lam * R * 1 := by ring
    have h2 : lam * ((n : ℝ) * |τ.im|) ≤ lam * R * (1 / 100) := by
      have h3 : (n : ℝ) * |τ.im| ≤ R * (1 / 100) := by
        have h4 : (n : ℝ) * |τ.im| ≤ (3 * (Real.pi / lam)) * (lam / (8 * Real.pi * R)) := by
          have h2' : (0 : ℝ) ≤ |τ.im| := abs_nonneg _
          have h3' : (0 : ℝ) < lam / (8 * Real.pi * R) :=
            div_pos hlam (by positivity : (0 : ℝ) < 8 * Real.pi * R)
          have hπpos : (0 : ℝ) ≤ 3 * (Real.pi / lam) := by
            have hπ : 0 < Real.pi / lam := div_pos Real.pi_pos hlam
            positivity
          exact mul_le_mul hnle (hτim.trans hτle) h2' hπpos
        have h5 : (3 * (Real.pi / lam)) * (lam / (8 * Real.pi * R)) = 3 / (8 * R) := by
          field_simp
        rw [h5] at h4
        have h6 : (3 : ℝ) / (8 * R) ≤ R * (1 / 100) := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * R)]
          nlinarith [hR]
        linarith [h4, h6]
      calc lam * ((n : ℝ) * |τ.im|) ≤ lam * (R * (1 / 100)) :=
            mul_le_mul_of_nonneg_left h3 hlam.le
        _ = lam * R * (1 / 100) := by ring
    have h2b : lam * ((B + 1) * ‖Ψ‖) ≤ lam * R * (0.103 * ‖Ψ‖) := by
      have hB : B + 1 ≤ 0.103 * R := by linarith [hBle, hR]
      have hΨ0 : (0 : ℝ) ≤ ‖Ψ‖ := norm_nonneg _
      calc lam * ((B + 1) * ‖Ψ‖) ≤ lam * ((0.103 * R) * ‖Ψ‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hΨ0) hlam.le
        _ = lam * R * (0.103 * ‖Ψ‖) := by ring
    have h3b : lam * (∑ j ∈ Finset.range n,
        (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2)) ≤ lam * R * (1.26) := by
      have hsplit : ∑ j ∈ Finset.range n, (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2)
          ≤ (n : ℝ) * (100 * lam ^ 2) + (2 + 4 * B + 2 * A) * (24 / R) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum]
        have h := mul_le_mul_of_nonneg_left hS' (by linarith : (0 : ℝ) ≤ 2 + 4 * B + 2 * A)
        linarith [h]
      have hnlam : (n : ℝ) * lam ≤ 3 * Real.pi := by
        have h := mul_le_mul_of_nonneg_right hnle hlam.le
        rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hlam)] at h
        linarith [h]
      have hA : lam * ((n : ℝ) * (100 * lam ^ 2)) ≤ lam * R * (1 / 100) := by
        have h4 : (n : ℝ) * (100 * lam ^ 2) ≤ 300 * Real.pi * lam := by
          have h5 : (n : ℝ) * (100 * lam ^ 2) = 100 * ((n : ℝ) * lam) * lam := by ring
          rw [h5]
          have h6 : 100 * ((n : ℝ) * lam) ≤ 100 * (3 * Real.pi) := by linarith [hnlam]
          nlinarith [h6, hlam.le, Real.pi_pos]
        have h8 : 300 * Real.pi * lam ≤ R * (1 / 100) := by
          have hp : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
          have hl : lam ≤ 1 / R ^ 2 := by
            rw [le_div_iff₀ (pow_pos hRpos 2)]; exact hlamR
          have hR2 : (16384 : ℝ) ≤ R ^ 2 := by nlinarith [hR]
          have h1 : 300 * Real.pi * lam ≤ 1200 * (1 / R ^ 2) := by
            nlinarith [hp, hl, hlam, Real.pi_pos]
          have h2 : 1200 * (1 / R ^ 2) ≤ R * (1 / 100) := by
            have h3 : 1200 * (1 / (16384 : ℝ)) ≤ 128 * (1 / 100) := by norm_num
            have h4 : 1200 * (1 / R ^ 2) ≤ 1200 * (1 / 16384) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact one_div_le_one_div_of_le (by norm_num) hR2
            have h5 : (128 : ℝ) * (1 / 100) ≤ R * (1 / 100) := by nlinarith [hR]
            linarith [h3, h4, h5]
          linarith [h1, h2]
        calc lam * ((n : ℝ) * (100 * lam ^ 2)) ≤ lam * (R * (1 / 100)) :=
              mul_le_mul_of_nonneg_left (le_trans h4 h8) hlam.le
          _ = lam * R * (1 / 100) := by ring
      have hB1 : lam * ((2 + 4 * B + 2 * A) * (24 / R)) ≤ lam * R * (5 / 4) := by
        have h4 : (2 + 4 * B + 2 * A) * (24 / R) ≤ R * (5 / 4) := by
          have h5 : 2 + 4 * B + 2 * A ≤ 2 + 3 * R / 8 + 3 * R ^ 2 / 64 := by linarith
          have h6 : (2 + 3 * R / 8 + 3 * R ^ 2 / 64) * (24 / R) ≤ R * (5 / 4) := by
            rw [← mul_div_assoc, div_le_iff₀ hRpos]
            nlinarith [hR]
          exact le_trans (mul_le_mul_of_nonneg_right h5 (by positivity)) h6
        calc lam * ((2 + 4 * B + 2 * A) * (24 / R)) ≤ lam * (R * (5 / 4)) :=
              mul_le_mul_of_nonneg_left h4 hlam.le
          _ = lam * R * (5 / 4) := by ring
      calc lam * (∑ j ∈ Finset.range n,
            (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2))
          ≤ lam * ((n : ℝ) * (100 * lam ^ 2) + (2 + 4 * B + 2 * A) * (24 / R)) :=
            mul_le_mul_of_nonneg_left hsplit hlam.le
        _ = lam * ((n : ℝ) * (100 * lam ^ 2)) + lam * ((2 + 4 * B + 2 * A) * (24 / R)) := by ring
        _ ≤ lam * R * (1 / 100) + lam * R * (5 / 4) := by linarith [hA, hB1]
        _ ≤ lam * R * (1.26) := by
            have h0 : (0 : ℝ) < lam * R := mul_pos hlam hRpos
            nlinarith [h0]
    have hsum : lam * |(u 0).im| + lam * ((n : ℝ) * |τ.im|) + lam * ((B + 1) * ‖Ψ‖)
        + lam * ∑ j ∈ Finset.range n, (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2)
        ≤ lam * R * 1 + lam * R * (1 / 100) + lam * R * (0.103 * ‖Ψ‖) + lam * R * (1.26) := by
      linarith [h1, h2, h2b, h3b]
    calc lam * |(u n).im| ≤ lam * |(u 0).im| + lam * ((n : ℝ) * |τ.im|)
          + lam * ((B + 1) * ‖Ψ‖)
          + lam * ∑ j ∈ Finset.range n, (100 * lam ^ 2 + (2 + 4 * B + 2 * A) * ‖ζ j‖ ^ 2) := hdrift
      _ ≤ lam * R * 1 + lam * R * (1 / 100) + lam * R * (0.103 * ‖Ψ‖) + lam * R * (1.26) := hsum
      _ ≤ (lam * R) * (2.3 + 0.103 * ‖Ψ‖) := by
          have h0 : (0 : ℝ) < lam * R := mul_pos hlam hRpos
          have h1' : (0 : ℝ) ≤ 0.103 * ‖Ψ‖ := by positivity
          nlinarith [h0, h1']

  -- ### the final numeric squeeze
  have hIm22 : |Ψ.im| ≤ 23 := by
    have h1 : 2 * Real.pi ≤ 6.5 := by linarith [Real.pi_lt_d2]
    linarith [hTbound, h576, h1]
  have hu_bound : lam * |(u n).im| ≤ 0.05 + 0.001 * |Ψ.re| := by
    have h2 : ‖Ψ‖ ≤ |Ψ.re| + |Ψ.im| := Complex.norm_le_abs_re_add_abs_im Ψ
    have h3 : lam * |(u n).im| ≤ (lam * R) * (2.3 + 0.103 * (|Ψ.re| + 23)) := by
      have h4 : 2.3 + 0.103 * ‖Ψ‖ ≤ 2.3 + 0.103 * (|Ψ.re| + 23) := by linarith [h2, hIm22]
      calc lam * |(u n).im| ≤ (lam * R) * (2.3 + 0.103 * ‖Ψ‖) := hdrift2
        _ ≤ (lam * R) * (2.3 + 0.103 * (|Ψ.re| + 23)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
    have h5 : lam * R ≤ 1 / 128 := by
      have h6 : lam * R ≤ 1 / R := by
        rw [le_div_iff₀ hRpos]; nlinarith [hlamR]
      have h7 : (1 : ℝ) / R ≤ 1 / 128 := one_div_le_one_div_of_le (by norm_num) hR
      linarith [h6, h7]
    have h8 : (lam * R) * (2.3 + 0.103 * (|Ψ.re| + 23))
        ≤ (1 / 128) * (2.3 + 0.103 * (|Ψ.re| + 23)) :=
      mul_le_mul_of_nonneg_right h5 (by have := abs_nonneg Ψ.re; have := abs_nonneg Ψ.im; linarith)
    have h9 : 0 ≤ |Ψ.re| := abs_nonneg _
    linarith [h3, h8, h9]
  have hSinh : Real.sinh (lam * |(u n).im|) / (lam * R)
      ≤ Real.exp (0.05 + 0.001 * |Ψ.re|) * (4.7 + 0.104 * |Ψ.re|) := by
    have h0 : 0 ≤ lam * |(u n).im| := by positivity
    have hs := sinh_le_mul_exp (lam * |(u n).im|) h0
    have hV : (lam * |(u n).im|) / (lam * R) ≤ 2.3 + 0.103 * ‖Ψ‖ := by
      rw [div_le_iff₀ (mul_pos hlam hRpos)]
      linarith [hdrift2]
    have hV2 : 2.3 + 0.103 * ‖Ψ‖ ≤ 4.7 + 0.104 * |Ψ.re| := by
      have h2 : ‖Ψ‖ ≤ |Ψ.re| + |Ψ.im| := Complex.norm_le_abs_re_add_abs_im Ψ
      linarith [h2, hIm22, abs_nonneg Ψ.re]
    have he : Real.exp (lam * |(u n).im|) ≤ Real.exp (0.05 + 0.001 * |Ψ.re|) :=
      Real.exp_le_exp.mpr hu_bound
    have hc0 : 0 ≤ (lam * |(u n).im|) / (lam * R) :=
      div_nonneg (by positivity) (le_of_lt (mul_pos hlam hRpos))
    calc Real.sinh (lam * |(u n).im|) / (lam * R)
        ≤ ((lam * |(u n).im|) * Real.exp (lam * |(u n).im|)) / (lam * R) :=
          div_le_div_of_nonneg_right hs (le_of_lt (mul_pos hlam hRpos))
      _ = Real.exp (lam * |(u n).im|) * ((lam * |(u n).im|) / (lam * R)) := by ring
      _ ≤ Real.exp (0.05 + 0.001 * |Ψ.re|) * (2.3 + 0.103 * ‖Ψ‖) :=
          mul_le_mul he hV hc0 (le_of_lt (Real.exp_pos _))
      _ ≤ Real.exp (0.05 + 0.001 * |Ψ.re|) * (4.7 + 0.104 * |Ψ.re|) :=
          mul_le_mul_of_nonneg_left hV2 (le_of_lt (Real.exp_pos _))
  have hsig : |Ψ.re| ≤ 26.5 + Real.log (1 + Real.exp (0.05 + 0.001 * |Ψ.re|)
      * (4.7 + 0.104 * |Ψ.re|)) := by
    have hlogb : Real.log (1 + Real.sinh (lam * |(u n).im|) / (lam * R))
        ≤ Real.log (1 + Real.exp (0.05 + 0.001 * |Ψ.re|) * (4.7 + 0.104 * |Ψ.re|)) := by
      apply Real.log_le_log
      · have h1 : 0 ≤ Real.sinh (lam * |(u n).im|) / (lam * R) :=
          div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hlam.le (abs_nonneg _)))
            (le_of_lt (mul_pos hlam hRpos))
        linarith
      · linarith [hSinh]
    linarith [hSbound, hlogb, h576]
  have hlog8 : Real.log 8 ≤ 2.1 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    linarith [Real.log_two_lt_d9]
  have hlog2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hfinal : |Ψ.re| ≤ 30 := by
    by_contra hcon
    push_neg at hcon
    have hσ30 : 30 ≤ |Ψ.re| := le_of_lt hcon
    have hσpos : 0 < |Ψ.re| := by linarith
    set x : ℝ := Real.exp (0.05 + 0.001 * |Ψ.re|) * (4.7 + 0.104 * |Ψ.re|) with hx
    have hx1 : 1 ≤ x := by
      rw [hx]
      have h1 : 1 ≤ Real.exp (0.05 + 0.001 * |Ψ.re|) := Real.one_le_exp (by positivity)
      have h2 : (1 : ℝ) ≤ 4.7 + 0.104 * |Ψ.re| := by linarith
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Real.exp (0.05 + 0.001 * |Ψ.re|) * (4.7 + 0.104 * |Ψ.re|) :=
            mul_le_mul h1 h2 (by norm_num) (le_of_lt (Real.exp_pos _))
    have hxpos : 0 < x := by
      rw [hx]; exact mul_pos (Real.exp_pos _) (by linarith)
    have hlog1 : Real.log (1 + x) ≤ Real.log 2 + (0.05 + 0.001 * |Ψ.re|)
        + Real.log (4.7 + 0.104 * |Ψ.re|) := by
      have h2 : 1 + x ≤ 2 * x := by linarith [hx1]
      have h3 : (0 : ℝ) < 4.7 + 0.104 * |Ψ.re| := by linarith
      calc Real.log (1 + x) ≤ Real.log (2 * x) := Real.log_le_log (by linarith [hx1]) h2
        _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (ne_of_gt hxpos)
        _ = Real.log 2 + (Real.log (Real.exp (0.05 + 0.001 * |Ψ.re|))
              + Real.log (4.7 + 0.104 * |Ψ.re|)) := by
            rw [hx, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt h3)]
        _ = Real.log 2 + ((0.05 + 0.001 * |Ψ.re|) + Real.log (4.7 + 0.104 * |Ψ.re|)) := by
            rw [Real.log_exp]
        _ = Real.log 2 + (0.05 + 0.001 * |Ψ.re|) + Real.log (4.7 + 0.104 * |Ψ.re|) := by ring
    have hlogb2 : Real.log (4.7 + 0.104 * |Ψ.re|) ≤ 0.261 * |Ψ.re| / 8 + 1.1 := by
      have h1 : 4.7 + 0.104 * |Ψ.re| ≤ 0.261 * |Ψ.re| := by linarith
      have h4 : Real.log (0.261 * |Ψ.re| / 8) ≤ 0.261 * |Ψ.re| / 8 - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      rw [Real.log_div (ne_of_gt (by linarith)) (by norm_num)] at h4
      calc Real.log (4.7 + 0.104 * |Ψ.re|) ≤ Real.log (0.261 * |Ψ.re|) :=
            Real.log_le_log (by linarith) h1
        _ ≤ 0.261 * |Ψ.re| / 8 + 1.1 := by linarith [h4, hlog8]
    linarith [hsig, hlog1, hlogb2, hlog2]
  have hlogR4 : 4 ≤ Real.log R := by
    have he4 : Real.exp 4 ≤ 128 := by
      have h1 : Real.exp 4 = (Real.exp 1) ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num]
        exact Real.exp_nat_mul (1 : ℝ) 4
      rw [h1]
      have h2 : (Real.exp 1) ^ 4 ≤ (3 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_three) 4
      have h3 : ((3 : ℝ)) ^ 4 = 81 := by norm_num
      linarith [h2, h3]
    have h1 : 4 ≤ Real.log 128 := (Real.le_log_iff_exp_le (by norm_num)).mpr he4
    exact le_trans h1 (Real.log_le_log (by norm_num) hR)
  have hgoal : |∑ j ∈ Finset.range n,
      (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re| = |Ψ.re| := by
    have h1 : (∑ j ∈ Finset.range n,
        (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re)
        = (∑ j ∈ Finset.range n, ζ j).re := by
      have h2 : (∑ j ∈ Finset.range n, ζ j).re = ∑ j ∈ Finset.range n, (ζ j).re := by
        simpa using map_sum Complex.reAddGroupHom ζ (Finset.range n)
      rw [h2]
    rw [h1, hΨ]
  rw [hgoal]
  exact hfinal
