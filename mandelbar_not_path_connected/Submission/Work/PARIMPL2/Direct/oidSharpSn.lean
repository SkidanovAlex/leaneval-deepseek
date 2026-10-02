import Mathlib
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidArcNegCotTail
import Submission.Work.PARIMPL2.Direct.oidSharpSinSharp
import Submission.Work.PARIMPL2.Direct.oidSharpArith

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

namespace Work.PARIMPL2.Direct

open Finset

/-! ## Sharp bound for the partial sums of the drift terms `ocA`

`ocA lam x y j = λ sin(λx_j) cos(λx_j) / D_j`, `D_j = sin²(λx_j) + sinh²(λy_j) ≥ sin²(λx_j)`, so
writing `t_j = λ x_j` and `κ_j = sin²(t_j)/D_j ∈ (0,1]`,

  `ocA_j = λ cot(t_j) · κ_j`  and  `ocA_j = -λ cot(π - t_j) · κ_j`.

Thus `∑ ocA_j ≤ λ ∑ cot⁺(t_j)` and `-∑ ocA_j ≤ λ ∑ cot⁺(π - t_j)`.  Since `cot` is antitone on
`(0,π)`, the clamped logarithmic identity `F = log ∘ sin` telescopes along a `h`-separated
sequence: for `x + h ≤ y`, `h cot⁺ y ≤ F(min y π/2) - F(min x π/2)`, so

  `h ∑_{j<n} cot⁺(t_j) ≤ F(min t_0 π/2) - F(min t_n π/2)`,  and
  `h ∑_{j<n} cot⁺(π - t_j) ≤ h cot⁺(π - t_0) + F(min (π - t_{n-1}) π/2) - F(min (π - t_0) π/2)`.

With `t_j ∈ [λ(R/4+2), π - λR/4]` this gives the two bounds `3 log(2π/(λR))`. -/

/-- Tangent-type inequality: for `0 < x ≤ y ≤ π/2`,
`(y - x) cot y ≤ log sin y - log sin x`. -/
theorem oidSharp_tangent (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ Real.pi / 2) :
    (y - x) * Real.cot y ≤ Real.log (Real.sin y) - Real.log (Real.sin x) := by
  rw [Real.cot_eq_cos_div_sin]
  exact aux_logSin_tangent x y hx hxy hy

/-- One-step comparison with clamping at `π/2`: for `0 < h`, `0 < x`, `x + h ≤ y < π`,
`h · cot⁺ y ≤ log sin (min y (π/2)) - log sin (min x (π/2))`. -/
theorem oidSharp_step (h x y : ℝ) (hh : 0 < h) (hx : 0 < x) (hxy : x + h ≤ y)
    (hyπ : y < Real.pi) :
    h * max (Real.cot y) 0
      ≤ Real.log (Real.sin (min y (Real.pi / 2)))
        - Real.log (Real.sin (min x (Real.pi / 2))) := by
  have hy0 : 0 < y := by linarith
  have hsinpos : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy0 hyπ
  rcases le_or_gt y (Real.pi / 2) with hy | hy
  · have hxle : x ≤ Real.pi / 2 := by linarith
    have hcotnn : 0 ≤ Real.cot y := by
      rw [Real.cot_eq_cos_div_sin]
      exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hy⟩) hsinpos.le
    have hxh : x ≤ y - h := by linarith
    have hpos : 0 < y - h := lt_of_lt_of_le hx hxh
    have htang := oidSharp_tangent (y - h) y hpos (by linarith) hy
    have hone : h * Real.cot y ≤ Real.log (Real.sin y) - Real.log (Real.sin (y - h)) := by
      have hyh : y - (y - h) = h := by ring
      rwa [hyh] at htang
    have hmono : Real.log (Real.sin x) ≤ Real.log (Real.sin (y - h)) :=
      Real.log_le_log (Real.sin_pos_of_pos_of_lt_pi hx (by linarith [hy, hh]))
        (Real.sin_le_sin_of_le_of_le_pi_div_two (x := x) (y := y - h)
          (by linarith [hx, Real.pi_pos]) (by linarith [hy, hh]) hxh)
    rw [max_eq_left hcotnn, min_eq_left hy, min_eq_left hxle]
    linarith
  · have hcotnp : Real.cot y ≤ 0 := by
      rw [Real.cot_eq_cos_div_sin]
      exact div_nonpos_of_nonpos_of_nonneg
        (Real.cos_nonpos_of_pi_div_two_le_of_le hy.le (by linarith [Real.pi_pos])) hsinpos.le
    rw [max_eq_right hcotnp]
    have hmin : min x (Real.pi / 2) ≤ min y (Real.pi / 2) := min_le_min (le_of_lt (by linarith)) le_rfl
    have hxpos : 0 < min x (Real.pi / 2) := lt_min hx (by linarith [Real.pi_pos])
    have hltπ : min x (Real.pi / 2) < Real.pi :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
    have hsinx : 0 < Real.sin (min x (Real.pi / 2)) :=
      Real.sin_pos_of_pos_of_lt_pi hxpos hltπ
    have hle : Real.sin (min x (Real.pi / 2)) ≤ Real.sin (min y (Real.pi / 2)) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (x := min x (Real.pi / 2))
        (y := min y (Real.pi / 2)) (by linarith [hxpos, Real.pi_pos]) (min_le_right _ _) hmin
    have hlog := Real.log_le_log hsinx hle
    linarith [hh, hlog]

/-- Telescoping along a decreasing `h`-separated sequence. -/
theorem oidSharp_decSum (h : ℝ) (hh : 0 < h) (w : ℕ → ℝ) (m : ℕ)
    (hpos : ∀ k ≤ m, 0 < w k) (hlt : ∀ k ≤ m, w k < Real.pi)
    (hdec : ∀ k < m, w (k + 1) + h ≤ w k) :
    h * (∑ k ∈ Finset.range m, max (Real.cot (w k)) 0)
      ≤ Real.log (Real.sin (min (w 0) (Real.pi / 2)))
        - Real.log (Real.sin (min (w m) (Real.pi / 2))) := by
  rw [Finset.mul_sum]
  have hkey : ∀ k ∈ Finset.range m,
      h * max (Real.cot (w k)) 0
        ≤ Real.log (Real.sin (min (w k) (Real.pi / 2)))
          - Real.log (Real.sin (min (w (k + 1)) (Real.pi / 2))) := by
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    exact oidSharp_step h (w (k + 1)) (w k) hh (hpos (k + 1) (by omega)) (hdec k hk')
      (hlt k (le_of_lt hk'))
  calc ∑ k ∈ Finset.range m, h * max (Real.cot (w k)) 0
      ≤ ∑ k ∈ Finset.range m, (Real.log (Real.sin (min (w k) (Real.pi / 2)))
          - Real.log (Real.sin (min (w (k + 1)) (Real.pi / 2)))) := Finset.sum_le_sum hkey
    _ = Real.log (Real.sin (min (w 0) (Real.pi / 2)))
          - Real.log (Real.sin (min (w m) (Real.pi / 2))) :=
        Finset.sum_range_sub' (fun j => Real.log (Real.sin (min (w j) (Real.pi / 2)))) m

/-- Telescoping along an increasing `h`-separated sequence (the first term is left out). -/
theorem oidSharp_incSum (h : ℝ) (hh : 0 < h) (w : ℕ → ℝ) (m : ℕ)
    (hpos : ∀ k ≤ m, 0 < w k) (hlt : ∀ k ≤ m, w k < Real.pi)
    (hinc : ∀ k < m, w k + h ≤ w (k + 1)) :
    h * (∑ k ∈ Finset.range m, max (Real.cot (w (k + 1))) 0)
      ≤ Real.log (Real.sin (min (w m) (Real.pi / 2)))
        - Real.log (Real.sin (min (w 0) (Real.pi / 2))) := by
  rw [Finset.mul_sum]
  have hkey : ∀ k ∈ Finset.range m,
      h * max (Real.cot (w (k + 1))) 0
        ≤ Real.log (Real.sin (min (w (k + 1)) (Real.pi / 2)))
          - Real.log (Real.sin (min (w k) (Real.pi / 2))) := by
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    exact oidSharp_step h (w k) (w (k + 1)) hh (hpos k (le_of_lt hk')) (hinc k hk')
      (hlt (k + 1) (by omega))
  calc ∑ k ∈ Finset.range m, h * max (Real.cot (w (k + 1))) 0
      ≤ ∑ k ∈ Finset.range m, (Real.log (Real.sin (min (w (k + 1)) (Real.pi / 2)))
          - Real.log (Real.sin (min (w k) (Real.pi / 2)))) := Finset.sum_le_sum hkey
    _ = Real.log (Real.sin (min (w m) (Real.pi / 2)))
          - Real.log (Real.sin (min (w 0) (Real.pi / 2))) :=
        Finset.sum_range_sub (fun j => Real.log (Real.sin (min (w j) (Real.pi / 2)))) m

/-- `cot s ≤ 1/s` for `0 < s`. -/
theorem oidSharp_cot_le_inv (s : ℝ) (h0 : 0 < s) (hπ : s < Real.pi) :
    Real.cot s ≤ 1 / s := by
  rw [Real.cot_eq_cos_div_sin]
  rcases lt_or_ge s (Real.pi / 2) with hs | hs
  · have hcos : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hs⟩
    have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi h0 hπ
    have htan : s ≤ Real.sin s / Real.cos s := by
      have := Real.le_tan h0.le hs
      rwa [Real.tan_eq_sin_div_cos] at this
    rw [div_le_div_iff₀ hsin h0]
    have h2 : s * Real.cos s ≤ Real.sin s := by
      have := mul_le_mul_of_nonneg_right htan hcos.le
      rwa [div_mul_cancel₀ _ hcos.ne'] at this
    linarith
  · have hcos : Real.cos s ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hs (by linarith [Real.pi_pos])
    have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi h0 hπ
    have h1 : Real.cos s / Real.sin s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcos hsin.le
    have h2 : 0 < 1 / s := by positivity
    linarith

theorem oidSharpSn_aux (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n : ℕ) (x y : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hSinSharp : lam * R / (2 * Real.pi) ≤ Real.sin (lam * R / 4) ∧
      (5 / 6) * (lam * R / 4) ≤ Real.sin (lam * R / 4) ∧
      0 < lam * R / 4 ∧ lam * R / 4 ≤ Real.pi / 2 ∧ 0 < Real.sin (lam * R / 4))
    (hArith : 4 / R + 3 * Real.log (24 / (5 * (lam * R)))
      ≤ 3 * Real.log (2 * Real.pi / (lam * R))) :
    |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j|
      ≤ 3 * Real.log (2 * Real.pi / (lam * R)) := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hlamRpos : 0 < lam * R := mul_pos hlam hRpos
  have hsRle : lam * R ≤ 1 / R := by
    rw [le_div_iff₀ hRpos]
    nlinarith [hlamR]
  have hs128 : lam * R ≤ 1 / 128 := by
    have h1 : 1 / R ≤ 1 / 128 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 128) hR
    linarith
  have hlogpos : 0 ≤ Real.log (2 * Real.pi / (lam * R)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hlamRpos]
    nlinarith [hs128, Real.pi_gt_three]
  set h : ℝ := lam / 3 with hhdef
  have hhpos : 0 < h := by rw [hhdef]; linarith
  have h3h : 3 * h = lam := by rw [hhdef]; ring
  set t : ℕ → ℝ := fun j => lam * x j with htdef
  have ht_eq : ∀ j, t j = lam * x j := fun j => rfl
  have ht1 : ∀ j ≤ n, lam * (R / 4 + 2) ≤ t j := by
    intro j hj
    rw [ht_eq j]
    exact mul_le_mul_of_nonneg_left (hx1 j hj) hlam.le
  have ht2 : ∀ j ≤ n, t j ≤ Real.pi - lam * R / 4 := by
    intro j hj
    rw [ht_eq j]
    have h1 := mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
    have he : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by
      field_simp
    rwa [he] at h1
  have htpos : ∀ j ≤ n, 0 < t j := by
    intro j hj
    have h1 := ht1 j hj
    have h2 : 0 < lam * (R / 4 + 2) := by positivity
    linarith
  have htlt : ∀ j ≤ n, t j < Real.pi := by
    intro j hj
    have h1 := ht2 j hj
    have h2 : 0 < lam * R / 4 := by positivity
    linarith
  have htstep : ∀ j < n, t (j + 1) + h ≤ t j := by
    intro j hj
    have h1 := hdec j hj
    have h2 := mul_le_mul_of_nonneg_left h1 hlam.le
    have he : lam * (x j - 1 / 3) = lam * x j - lam / 3 := by ring
    rw [he] at h2
    rw [ht_eq, ht_eq, hhdef]
    linarith
  have hsinpos : ∀ j ≤ n, 0 < Real.sin (t j) := fun j hj =>
    Real.sin_pos_of_pos_of_lt_pi (htpos j hj) (htlt j hj)
  -- the two shape identities
  have hA : ∀ j ≤ n, ocA lam x y j
      = lam * Real.cot (t j) * (Real.sin (t j) ^ 2 / ocDen lam x y j) := by
    intro j hj
    have hden : ocDen lam x y j = Real.sin (t j) ^ 2 + Real.sinh (lam * y j) ^ 2 := by
      rw [ocDen, ht_eq j]
    rw [ocA, hden, ht_eq j, Real.cot_eq_cos_div_sin]
    field_simp
  set u : ℕ → ℝ := fun j => Real.pi - t j with hudef
  have hu_eq : ∀ j, u j = Real.pi - t j := fun j => rfl
  have hBeq : ∀ j ≤ n, -ocA lam x y j
      = lam * Real.cot (u j) * (Real.sin (u j) ^ 2 / ocDen lam x y j) := by
    intro j hj
    have hden : ocDen lam x y j = Real.sin (u j) ^ 2 + Real.sinh (lam * y j) ^ 2 := by
      rw [ocDen, hu_eq j, ht_eq j, Real.sin_pi_sub]
    rw [ocA, hden, hu_eq j, Real.cot_eq_cos_div_sin, Real.sin_pi_sub, Real.cos_pi_sub]
    field_simp
    ring
  have hkappa : ∀ j ≤ n, 0 ≤ Real.sin (t j) ^ 2 / ocDen lam x y j ∧
      Real.sin (t j) ^ 2 / ocDen lam x y j ≤ 1 := by
    intro j hj
    have hden : ocDen lam x y j = Real.sin (t j) ^ 2 + Real.sinh (lam * y j) ^ 2 := by
      rw [ocDen, ht_eq j]
    rw [hden]
    have hpos : 0 < Real.sin (t j) ^ 2 + Real.sinh (lam * y j) ^ 2 := by
      have := hsinpos j hj
      positivity
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hpos]
    nlinarith [sq_nonneg (Real.sinh (lam * y j))]
  have hkappaU : ∀ j ≤ n, 0 ≤ Real.sin (u j) ^ 2 / ocDen lam x y j ∧
      Real.sin (u j) ^ 2 / ocDen lam x y j ≤ 1 := by
    intro j hj
    have hsu : 0 < Real.sin (u j) := by
      rw [hu_eq j, Real.sin_pi_sub]
      exact hsinpos j hj
    have hden : ocDen lam x y j = Real.sin (u j) ^ 2 + Real.sinh (lam * y j) ^ 2 := by
      rw [ocDen, hu_eq j, ht_eq j, Real.sin_pi_sub]
    rw [hden]
    have hpos : 0 < Real.sin (u j) ^ 2 + Real.sinh (lam * y j) ^ 2 := by positivity
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hpos]
    nlinarith [sq_nonneg (Real.sinh (lam * y j))]
  -- ============ the two one-sided bounds ============
  have hstep1 : ∑ j ∈ Finset.range n, ocA lam x y j
      ≤ lam * ∑ j ∈ Finset.range n, max (Real.cot (t j)) 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
    have hκ := hkappa j hjn
    rw [hA j hjn]
    rcases le_or_gt 0 (Real.cot (t j)) with hc | hc
    · rw [max_eq_left hc]
      have hle := mul_le_mul_of_nonneg_left hκ.2 (mul_nonneg hlam.le hc)
      linarith
    · rw [max_eq_right (le_of_lt hc)]
      have h1 : lam * Real.cot (t j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le (le_of_lt hc)
      have h2 := mul_nonpos_of_nonpos_of_nonneg h1 hκ.1
      linarith
  have hstep2 : -(∑ j ∈ Finset.range n, ocA lam x y j)
      ≤ lam * ∑ j ∈ Finset.range n, max (Real.cot (u j)) 0 := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
    have hκ := hkappaU j hjn
    rw [hBeq j hjn]
    rcases le_or_gt 0 (Real.cot (u j)) with hc | hc
    · rw [max_eq_left hc]
      have hle := mul_le_mul_of_nonneg_left hκ.2 (mul_nonneg hlam.le hc)
      linarith
    · rw [max_eq_right (le_of_lt hc)]
      have h1 : lam * Real.cot (u j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le (le_of_lt hc)
      have h2 := mul_nonpos_of_nonpos_of_nonneg h1 hκ.1
      linarith
  -- the Jordan-type bound: sin(lam*R/4) ≥ lam*R/(2π)
  have hJordan : -Real.log (Real.sin (lam * R / 4)) ≤ Real.log (2 * Real.pi / (lam * R)) := by
    have hlog := Real.log_le_log (by positivity : 0 < lam * R / (2 * Real.pi)) hSinSharp.1
    rw [Real.log_div hlamRpos.ne' (by positivity : (2 : ℝ) * Real.pi ≠ 0)] at hlog
    rw [Real.log_div (by positivity : (2 : ℝ) * Real.pi ≠ 0) hlamRpos.ne']
    linarith
  -- the sharp bound: sin(lam*R/4) ≥ (5/6)*(lam*R/4)
  have hSharpLog : -Real.log (Real.sin (lam * R / 4)) ≤ Real.log (24 / (5 * (lam * R))) := by
    have hlog := Real.log_le_log (by positivity : 0 < (5 : ℝ) / 6 * (lam * R / 4)) hSinSharp.2.1
    have hA1 : Real.log (24 / (5 * (lam * R))) = Real.log 24 - Real.log 5 - Real.log (lam * R) := by
      rw [Real.log_div (by norm_num : (24 : ℝ) ≠ 0) (by positivity : (5 : ℝ) * (lam * R) ≠ 0),
        Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hlamRpos.ne']
      ring
    have hB1 : Real.log ((5 : ℝ) / 6 * (lam * R / 4))
        = Real.log 5 - Real.log 6 + Real.log (lam * R) - Real.log 4 := by
      rw [Real.log_mul (by norm_num : ((5 : ℝ) / 6) ≠ 0) (by positivity : lam * R / 4 ≠ 0),
        Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0),
        Real.log_div hlamRpos.ne' (by norm_num : (4 : ℝ) ≠ 0)]
      ring
    rw [hB1] at hlog
    rw [hA1]
    have h64 : Real.log 24 = Real.log 6 + Real.log 4 := by
      have h1 := Real.log_mul (show (6 : ℝ) ≠ 0 by norm_num) (show (4 : ℝ) ≠ 0 by norm_num)
      rw [show (6 : ℝ) * 4 = 24 by norm_num] at h1
      exact h1
    linarith
  -- ============ upper bound ============
  have hPbound : lam * ∑ j ∈ Finset.range n, max (Real.cot (t j)) 0
      ≤ 3 * Real.log (2 * Real.pi / (lam * R)) := by
    have htel := oidSharp_decSum h hhpos t n (fun k hk => htpos k hk) (fun k hk => htlt k hk) htstep
    have h1 : Real.log (Real.sin (min (t 0) (Real.pi / 2))) ≤ 0 := by
      refine Real.log_nonpos ?_ (Real.sin_le_one _)
      refine (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).le
      · exact lt_min (htpos 0 (Nat.zero_le n)) (by linarith [Real.pi_pos])
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_gt_three])
    have h2 : Real.log (Real.sin (lam * R / 4)) ≤ Real.log (Real.sin (min (t n) (Real.pi / 2))) := by
      refine Real.log_le_log hSinSharp.2.2.2.2 ?_
      refine Real.sin_le_sin_of_le_of_le_pi_div_two (x := lam * R / 4)
        (y := min (t n) (Real.pi / 2)) (by linarith [Real.pi_pos, hSinSharp.2.2.1]) (min_le_right _ _) ?_
      refine le_min ?_ hSinSharp.2.2.2.1
      have htn := ht1 n le_rfl
      have hl : lam * R / 4 ≤ lam * (R / 4 + 2) := by
        have : lam * (R / 4 + 2) = lam * R / 4 + 2 * lam := by ring
        rw [this]; linarith
      linarith
    have h3 : h * ∑ j ∈ Finset.range n, max (Real.cot (t j)) 0
        ≤ -Real.log (Real.sin (lam * R / 4)) := by linarith [htel, h1, h2]
    have h4 : lam * ∑ j ∈ Finset.range n, max (Real.cot (t j)) 0
        = 3 * (h * ∑ j ∈ Finset.range n, max (Real.cot (t j)) 0) := by
      rw [← h3h]; ring
    linarith [h3, hJordan, h4]
  -- ============ lower bound ============
  have hNbound : lam * ∑ j ∈ Finset.range n, max (Real.cot (u j)) 0
      ≤ 3 * Real.log (2 * Real.pi / (lam * R)) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0]
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
      linarith [hlogpos]
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
      rw [hm, Finset.sum_range_succ']
      have hu_pos : ∀ j ≤ n, 0 < u j := by
        intro j hj
        rw [hu_eq j]
        have := htlt j hj
        linarith
      have hu_lt : ∀ j ≤ n, u j < Real.pi := by
        intro j hj
        rw [hu_eq j]
        have := htpos j hj
        linarith
      have hu_step : ∀ j < n, u j + h ≤ u (j + 1) := by
        intro j hj
        have h1 := htstep j hj
        rw [hu_eq j, hu_eq (j + 1)]
        linarith
      have hterm0 : lam * max (Real.cot (u 0)) 0 ≤ 4 / R := by
        have hu0_low : lam * R / 4 ≤ u 0 := by
          have h1 := ht2 0 (Nat.zero_le n)
          rw [hu_eq 0]
          linarith
        have hu0_pos : 0 < u 0 := hu_pos 0 (Nat.zero_le n)
        have hu0_lt : u 0 < Real.pi := hu_lt 0 (Nat.zero_le n)
        have hcot : Real.cot (u 0) ≤ 1 / u 0 := oidSharp_cot_le_inv _ hu0_pos hu0_lt
        have h1 : (1 : ℝ) / u 0 ≤ 4 / (lam * R) := by
          rw [div_le_div_iff₀ hu0_pos hlamRpos]
          linarith [hu0_low]
        have hmax : max (Real.cot (u 0)) 0 ≤ 4 / (lam * R) :=
          max_le (le_trans hcot h1) (by positivity)
        calc lam * max (Real.cot (u 0)) 0 ≤ lam * (4 / (lam * R)) :=
              mul_le_mul_of_nonneg_left hmax hlam.le
          _ = 4 / R := by field_simp
      have hrest : lam * ∑ k ∈ Finset.range m, max (Real.cot (u (k + 1))) 0
          ≤ 3 * -Real.log (Real.sin (lam * R / 4)) := by
        have hinc : ∀ k < m, u k + h ≤ u (k + 1) := fun k hk => hu_step k (by omega)
        have htel := oidSharp_incSum h hhpos u m (fun k hk => hu_pos k (by omega))
          (fun k hk => hu_lt k (by omega)) hinc
        have h1 : Real.log (Real.sin (min (u m) (Real.pi / 2))) ≤ 0 := by
          refine Real.log_nonpos ?_ (Real.sin_le_one _)
          refine (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).le
          · exact lt_min (hu_pos m (by omega)) (by linarith [Real.pi_pos])
          · exact lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_gt_three])
        have h2 : Real.log (Real.sin (lam * R / 4)) ≤ Real.log (Real.sin (min (u 0) (Real.pi / 2))) := by
          refine Real.log_le_log hSinSharp.2.2.2.2 ?_
          refine Real.sin_le_sin_of_le_of_le_pi_div_two (x := lam * R / 4)
            (y := min (u 0) (Real.pi / 2)) (by linarith [Real.pi_pos, hSinSharp.2.2.1])
            (min_le_right _ _) ?_
          refine le_min ?_ hSinSharp.2.2.2.1
          have h1 := ht2 0 (Nat.zero_le n)
          rw [hu_eq 0]
          linarith
        have h3 : h * ∑ k ∈ Finset.range m, max (Real.cot (u (k + 1))) 0
            ≤ -Real.log (Real.sin (lam * R / 4)) := by linarith [htel, h1, h2]
        have h4 : lam * ∑ k ∈ Finset.range m, max (Real.cot (u (k + 1))) 0
            = 3 * (h * ∑ k ∈ Finset.range m, max (Real.cot (u (k + 1))) 0) := by
          rw [← h3h]; ring
        linarith [h3, h4]
      have hcomb : lam * (∑ k ∈ Finset.range m, max (Real.cot (u (k + 1))) 0
            + max (Real.cot (u 0)) 0)
          ≤ 4 / R + 3 * -Real.log (Real.sin (lam * R / 4)) := by
        rw [mul_add]
        linarith [hterm0, hrest]
      linarith [hcomb, hSharpLog, hArith]
  rw [abs_le]
  exact ⟨by linarith [hstep2, hNbound], by linarith [hstep1, hPbound]⟩

theorem oidSharpSn (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n : ℕ) (x y : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3) :
    |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j|
      ≤ 3 * Real.log (2 * Real.pi / (lam * R)) :=
  oidSharpSn_aux lam R hlam hR hlamR n x y hx1 hx2 hdec
    (oidSharpSinSharp lam R hlam hR hlamR) (oidSharpArith lam R hlam hR hlamR)

end Work.PARIMPL2.Direct
