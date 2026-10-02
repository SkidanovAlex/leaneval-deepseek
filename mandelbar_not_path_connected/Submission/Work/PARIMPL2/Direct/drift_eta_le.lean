import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.norm_modelDisp_add_rational_le
import Submission.Work.PARIMPL2.Direct.modelDisp_re_im_bounds
import Submission.Work.PARIMPL2.Direct.norm_ecalPt_sq_le
import Submission.Work.PARIMPL2.Direct.one_term_le
import Submission.Work.PARIMPL2.Direct.sum_inv_sq_le_of_sep
import Submission.Work.PARIMPL2.Direct.sumInvSqLe

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.PARIMPL2.Direct

open Complex

theorem modelDisp_re_le_five (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8)
    (u : ℂ) (hzn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hzr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r) :
    (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ≤ -(2 / 5) + 100 * lam ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg h1) hh1
  have hlam8 : lam ≤ 1 / 8 := by
    have h1 : lam ≤ 1 / R ^ 2 := by rw [le_div_iff₀ (pow_pos hRpos 2)]; linarith [hlamR]
    have h2 : (1 : ℝ) / R ^ 2 ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (pow_pos hRpos 2) (by norm_num : (0 : ℝ) < 8)]
      nlinarith only [hR]
    linarith
  set ζ : ℂ := Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u with hζdef
  set H : ℂ := h ζ with hHdef
  set t : ℝ := ‖ζ‖ with htdef
  set g : ℝ := B * t + A * t ^ 2 with hgdef
  have ht0 : 0 ≤ t := by rw [htdef]; exact norm_nonneg ζ
  have ht32 : t ≤ 1 / 32 := by
    have h1 : (4 : ℝ) / R ≤ 1 / 32 := by
      rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 32)]
      linarith
    rw [htdef, hζdef]
    linarith [hzn, h1]
  have hg0 : 0 ≤ g := by rw [hgdef]; positivity
  have hg38 : g ≤ 3 / 8 := by
    rw [hgdef, htdef, hζdef]
    have h1 : B * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 * B / R := by
      have h2 := mul_le_mul_of_nonneg_left hzn hB0
      calc B * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ B * (4 / R) := h2
        _ = 4 * B / R := by ring
    have h2 : A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 ≤ 16 * A / R ^ 2 := by
      have h3 : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 ≤ (4 / R) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hzn 2
      calc A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 ≤ A * (4 / R) ^ 2 :=
            mul_le_mul_of_nonneg_left h3 hA
        _ = 16 * A / R ^ 2 := by ring
    linarith [hAr, h1, h2]
  have hHτ : ‖H - τ‖ ≤ g := by
    rw [hHdef, hgdef, htdef]
    have hgerm := hb.2.2.1 ζ (by simpa only [hζdef] using hzr)
    have htri : ‖h ζ - τ‖ ≤ ‖h ζ - τ - h1 * ζ‖ + ‖h1 * ζ‖ := by
      have hna := norm_add_le (h ζ - τ - h1 * ζ) (h1 * ζ)
      have he : (h ζ - τ - h1 * ζ) + h1 * ζ = h ζ - τ := by ring
      rwa [he] at hna
    have hmm : ‖h1 * ζ‖ ≤ B * ‖ζ‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hh1 (norm_nonneg ζ)
    linarith [htri, hgerm, hmm]
  have hH2 : ‖H‖ ≤ 2 := by
    rw [hHdef]
    exact hb.2.2.2.1 ζ (by simpa only [hζdef] using hzr)
  have hζ4 : ‖ζ‖ ≤ 1 / 4 := by
    have h1 : (4 : ℝ) / R ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 4)]
      linarith
    have h2 : ‖ζ‖ ≤ 4 / R := by rw [hζdef]; exact hzn
    linarith
  obtain ⟨hQbot, -, -⟩ :=
    div_one_add_mul_small_bounds τ H ζ t g hb.2.1 hτ1 hHτ (le_of_eq htdef.symm) ht0 hg0 ht32 hg38
  have hrat : ‖Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u + H / (1 + ζ * H)‖
      ≤ 100 * lam ^ 2 := by
    have h := norm_modelDisp_add_rational_le lam hlam hlam8 h u (by simpa only [hζdef] using hζ4)
      (by simpa only [hHdef, hζdef] using hH2)
    simpa only [hζdef, hHdef] using h
  have hre : (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re
      = (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u + H / (1 + ζ * H)).re
        - (H / (1 + ζ * H)).re := by
    rw [Complex.add_re]; ring
  rw [hre]
  have h1 : (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u
      + H / (1 + ζ * H)).re ≤ 100 * lam ^ 2 := le_trans (Complex.re_le_norm _) hrat
  linarith [h1, hQbot]

private lemma nat_mul_lam_sq_le (lam R : ℝ) (u : ℕ → ℂ) (n : ℕ)
    (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3) :
    (n : ℝ) * lam ^ 2 ≤ 3 * Real.pi / R ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hmono : ∀ k ≤ n, (u k).re + (k : ℝ) * (1 / 3) ≤ (u 0).re := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkn : k ≤ n := le_trans (Nat.le_succ k) hk
      have ih' := ih hkn
      have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hd := hdec k hklt
      have hgoal : (u (k + 1)).re + ((k : ℝ) + 1) * (1 / 3) ≤ (u 0).re := by
        have h2 : ((k : ℝ) + 1) * (1 / 3) = (k : ℝ) * (1 / 3) + 1 / 3 := by ring
        rw [h2]; linarith [ih', hd]
      simpa [Nat.cast_add, Nat.cast_one] using hgoal
  have hnb : (n : ℝ) * (1 / 3) ≤ Real.pi / lam - R / 2 - 2 := by
    have h1 : (u 0).re - (u n).re ≤ Real.pi / lam - R / 4 - (R / 4 + 2) := by
      have a := hx2 0 (Nat.zero_le n)
      have b := hx1 n le_rfl
      linarith
    have c := hmono n le_rfl
    linarith
  have hn : (n : ℝ) ≤ 3 * (Real.pi / lam) := by linarith
  have hl : 3 * (Real.pi / lam) * lam ^ 2 ≤ 3 * Real.pi / R ^ 2 := by
    have hle : lam ≤ 1 / R ^ 2 := by rw [le_div_iff₀ (pow_pos hRpos 2)]; linarith [hlamR]
    have h1 : 3 * (Real.pi / lam) * lam ^ 2 = 3 * Real.pi * lam := by field_simp
    have h2 : 3 * Real.pi * lam ≤ 3 * Real.pi * (1 / R ^ 2) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have h3 : 3 * Real.pi * (1 / R ^ 2) = 3 * Real.pi / R ^ 2 := by ring
    linarith [h1.symm.le, h1.le, h2, h3.le, h3.ge]
  calc (n : ℝ) * lam ^ 2 ≤ (3 * (Real.pi / lam)) * lam ^ 2 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ 3 * Real.pi / R ^ 2 := hl

private lemma drift_arith (δ R : ℝ) (hR : 128 ≤ R) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 100 / R ^ 4) :
    1 / ((2 / 5 - δ) * (R / 4 + 2)) + 16 / R ^ 2 + 1 / ((2 / 5 - δ) * (R / 4))
        + 3 * Real.pi / R ^ 2 ≤ 20 / R + 29 / R ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hδ1 : δ ≤ 1 / 5 := by
    have hR4big : (500 : ℝ) ≤ R ^ 4 := by
      have h1 : (128 : ℝ) ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ (by norm_num) hR 4
      norm_num at h1
      linarith
    have h : 100 / R ^ 4 ≤ 1 / 5 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 4) (by norm_num : (0 : ℝ) < 5)]
      linarith
    linarith
  have hspos : 0 < 2 / 5 - δ := by linarith
  have hδ5 : 0 ≤ δ * (1 - 5 * δ) := mul_nonneg hδ0 (by linarith)
  have hkey1 : 1 / ((2 / 5 - δ) * (R / 4 + 2)) ≤ 10 * (1 + 5 * δ) / (R + 8) := by
    rw [div_le_div_iff₀ (mul_pos hspos (by linarith : (0 : ℝ) < R / 4 + 2))
      (by linarith : (0 : ℝ) < R + 8)]
    nlinarith only [hδ5, hRpos, hδ0]
  have hkey2 : 1 / ((2 / 5 - δ) * (R / 4)) ≤ 10 * (1 + 5 * δ) / R := by
    rw [div_le_div_iff₀ (mul_pos hspos (by linarith : (0 : ℝ) < R / 4)) hRpos]
    nlinarith only [hδ5, hRpos, hδ0]
  have hkey3 : 10 * (1 + 5 * δ) / (R + 8) ≤ 10 * (1 + 5 * δ) / R := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < R + 8) hRpos]
    nlinarith only [hδ0]
  have hkey4 : 10 * (1 + 5 * δ) / R + 10 * (1 + 5 * δ) / R = 20 / R + 100 * δ / R := by
    field_simp
    ring
  have hδR : 100 * δ / R ≤ 1 / R ^ 2 := by
    rw [div_le_div_iff₀ hRpos (by positivity : (0 : ℝ) < R ^ 2)]
    have hδ' := hδ
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 4)] at hδ'
    have hR3big : (100 * 100 : ℝ) ≤ R ^ 3 := by
      have h1 : (128 : ℝ) ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (by norm_num) hR 3
      norm_num at h1
      linarith
    nlinarith only [hδ', hR3big, hRpos]
  have hfin : 1 / R ^ 2 + 16 / R ^ 2 + 3 * Real.pi / R ^ 2 ≤ 29 / R ^ 2 := by
    have e : 1 / R ^ 2 + 16 / R ^ 2 + 3 * Real.pi / R ^ 2 = (17 + 3 * Real.pi) / R ^ 2 := by
      field_simp
      ring
    rw [e]
    have h : 17 + 3 * Real.pi ≤ 29 := by linarith [Real.pi_lt_four]
    exact div_le_div_of_nonneg_right h (by positivity)
  have h1 : 1 / ((2 / 5 - δ) * (R / 4 + 2)) + 16 / R ^ 2 + 1 / ((2 / 5 - δ) * (R / 4))
      + 3 * Real.pi / R ^ 2
      ≤ 10 * (1 + 5 * δ) / (R + 8) + 16 / R ^ 2 + 10 * (1 + 5 * δ) / R
        + 3 * Real.pi / R ^ 2 := by
    linarith [hkey1, hkey2]
  have h2 : 10 * (1 + 5 * δ) / (R + 8) + 16 / R ^ 2 + 10 * (1 + 5 * δ) / R
      + 3 * Real.pi / R ^ 2 ≤ 20 / R + 1 / R ^ 2 + 16 / R ^ 2 + 3 * Real.pi / R ^ 2 := by
    linarith [hkey3, hkey4, hδR]
  have h3 : 20 / R + 1 / R ^ 2 + 16 / R ^ 2 + 3 * Real.pi / R ^ 2 ≤ 20 / R + 29 / R ^ 2 := by
    linarith [hfin]
  linarith [h1, h2, h3]

private lemma sum_zeta_sq_le_sharp (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (u : ℕ → ℂ) (n : ℕ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3)
    (hspace : ∀ j < n, (u (j + 1)).re ≤ (u j).re - (2 / 5 - 100 * lam ^ 2)) :
    ∑ j ∈ Finset.range n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
      ≤ 20 / R + 29 / R ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hδ0 : 0 ≤ 100 * lam ^ 2 := by positivity
  have hδ : 100 * lam ^ 2 ≤ 100 / R ^ 4 := by
    have hle : lam ≤ 1 / R ^ 2 := by rw [le_div_iff₀ (pow_pos hRpos 2)]; linarith [hlamR]
    have h1 : lam ^ 2 ≤ (1 / R ^ 2) ^ 2 := pow_le_pow_left₀ (le_of_lt hlam) hle 2
    have h2 : (1 / R ^ 2) ^ 2 = 1 / R ^ 4 := by ring
    rw [h2] at h1
    calc 100 * lam ^ 2 ≤ 100 * (1 / R ^ 4) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 100 / R ^ 4 := by ring
  have hspos : 0 < 2 / 5 - 100 * lam ^ 2 := by
    have h : 100 * lam ^ 2 ≤ 1 / 5 := by
      have h4 : (0 : ℝ) < R ^ 4 := by positivity
      have hR4big : (500 : ℝ) ≤ R ^ 4 := by
        have h1 : (128 : ℝ) ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ (by norm_num) hR 4
        norm_num at h1
        linarith
      have h5 : 100 / R ^ 4 ≤ 1 / 5 := by
        rw [div_le_div_iff₀ h4 (by norm_num : (0 : ℝ) < 5)]
        linarith
      linarith
    linarith
  have hpt : ∀ j ∈ Finset.range n,
      ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
        ≤ 1 / ((u j).re) ^ 2 + 1 / (Real.pi / lam - (u j).re) ^ 2 + lam ^ 2 := by
    intro j hj
    have hjle : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
    have hx1j := hx1 j hjle
    have hx2j := hx2 j hjle
    have h1 : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
        ≤ lam ^ 2 / (Real.sin (lam * (u j).re)) ^ 2 :=
      norm_ecalPt_sq_le lam (u j) hlam (by linarith) (by linarith)
    have h2 : lam ^ 2 / (Real.sin (lam * (u j).re)) ^ 2
        ≤ 1 / ((u j).re) ^ 2 + 1 / (Real.pi / lam - (u j).re) ^ 2 + lam ^ 2 := by
      have h := one_term_le lam R ((u j).re) 0 hlam hR hx1j hx2j
      simpa using h
    exact le_trans h1 h2
  have hxsum : ∑ j ∈ Finset.range n, 1 / ((u j).re) ^ 2
      ≤ 1 / ((2 / 5 - 100 * lam ^ 2) * (R / 4 + 2)) :=
    sum_inv_sq_le_of_sep (fun j => (u j).re) (R / 4 + 2) (2 / 5 - 100 * lam ^ 2) n
      (by linarith) hspos (fun j hj => hx1 j hj) hspace
  have hdlow : ∀ j ≤ n, R / 4 + (j : ℝ) * (2 / 5 - 100 * lam ^ 2)
      ≤ Real.pi / lam - (u j).re := by
    intro j hj
    induction j with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]; linarith [hx2 0 (Nat.zero_le n)]
    | succ k ih =>
      have hk : k ≤ n := le_trans (Nat.le_succ k) hj
      have ih' := ih hk
      have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hj
      have hd := hspace k hklt
      have hgoal : R / 4 + ((k : ℝ) + 1) * (2 / 5 - 100 * lam ^ 2)
          ≤ Real.pi / lam - (u (k + 1)).re := by
        have h2 : ((k : ℝ) + 1) * (2 / 5 - 100 * lam ^ 2)
            = (k : ℝ) * (2 / 5 - 100 * lam ^ 2) + (2 / 5 - 100 * lam ^ 2) := by ring
        rw [h2]; linarith [ih', hd]
      simpa [Nat.cast_add, Nat.cast_one] using hgoal
  have hdsum : ∑ j ∈ Finset.range n, 1 / (Real.pi / lam - (u j).re) ^ 2
      ≤ 16 / R ^ 2 + 1 / ((2 / 5 - 100 * lam ^ 2) * (R / 4)) := by
    have h1 : ∑ j ∈ Finset.range n, 1 / (Real.pi / lam - (u j).re) ^ 2
        ≤ ∑ j ∈ Finset.range n, 1 / (R / 4 + (j : ℝ) * (2 / 5 - 100 * lam ^ 2)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt := Finset.mem_range.mp hj
      have hge := hdlow j (le_of_lt hjlt)
      have hpos : 0 < R / 4 + (j : ℝ) * (2 / 5 - 100 * lam ^ 2) := by
        have h0 : 0 ≤ (j : ℝ) * (2 / 5 - 100 * lam ^ 2) := mul_nonneg (by positivity) hspos.le
        linarith
      have hdpos : 0 < Real.pi / lam - (u j).re := lt_of_lt_of_le hpos hge
      rw [one_div, one_div, inv_le_inv₀ (pow_pos hdpos 2) (pow_pos hpos 2)]
      exact pow_le_pow_left₀ hpos.le hge 2
    refine le_trans h1 ?_
    have h := sumInvSqLe (R / 4) (2 / 5 - 100 * lam ^ 2) n (by linarith) hspos
    have e1 : (1 : ℝ) / (R / 4) ^ 2 = 16 / R ^ 2 := by field_simp; ring
    rw [e1] at h
    exact h
  have hlams : ∑ j ∈ Finset.range n, lam ^ 2 ≤ 3 * Real.pi / R ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact nat_mul_lam_sq_le lam R u n hlam hR hlamR hx1 hx2 hdec
  calc ∑ j ∈ Finset.range n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
      ≤ ∑ j ∈ Finset.range n,
          (1 / ((u j).re) ^ 2 + 1 / (Real.pi / lam - (u j).re) ^ 2 + lam ^ 2) :=
        Finset.sum_le_sum hpt
    _ = (∑ j ∈ Finset.range n, 1 / ((u j).re) ^ 2)
          + (∑ j ∈ Finset.range n, 1 / (Real.pi / lam - (u j).re) ^ 2)
          + (∑ j ∈ Finset.range n, lam ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 1 / ((2 / 5 - 100 * lam ^ 2) * (R / 4 + 2))
          + (16 / R ^ 2 + 1 / ((2 / 5 - 100 * lam ^ 2) * (R / 4))) + 3 * Real.pi / R ^ 2 := by
        linarith [hxsum, hdsum, hlams]
    _ ≤ 20 / R + 29 / R ^ 2 := by
        have h := drift_arith (100 * lam ^ 2) R hR hδ0 hδ
        linarith [h]

theorem drift_eta_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hrr : 16 ≤ R * r)
    (hτpi : (Real.pi / lam) * ‖τ - 1‖ ≤ 1 / (8 * R))
    (n : ℕ) (u : ℕ → ℂ)
    (hu : ∀ j < n, u (j + 1) = u j + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j))
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3)
    (hzn : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ≤ 4 / R)
    (hzr : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ < r)
    (hstep : ∀ j ≤ n, (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).re
        ≤ -1 + 35 * lam ^ 2 + (B + 8) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖
          - (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
              - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
          + 35 * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2) :
    ∑ j ∈ Finset.range n,
        |(h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im| ≤ 20 * A / R + 8 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg h1) hh1
  have hAub : A ≤ 3 * R ^ 2 / 128 := by
    have h1 : 16 * A / R ^ 2 ≤ 3 / 8 := by
      have h2 : 0 ≤ 4 * B / R := by
        apply div_nonneg (mul_nonneg (by norm_num) hB0) (le_of_lt hRpos)
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2)] at h1
    linarith
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  have hzn' : ∀ j ≤ n, ‖Work.Implosion.ecalPt a (u j)‖ ≤ 4 / R :=
    fun j hj => by simpa only [ha] using hzn j hj
  have hzr' : ∀ j ≤ n, ‖Work.Implosion.ecalPt a (u j)‖ < r :=
    fun j hj => by simpa only [ha] using hzr j hj
  have hu' : ∀ j < n, u (j + 1) = u j + Work.Implosion.modelDisp a h (u j) :=
    fun j hj => by simpa only [ha] using hu j hj
  have hspace : ∀ j < n, (u (j + 1)).re ≤ (u j).re - (2 / 5 - 100 * lam ^ 2) := by
    intro j hj
    have hone := modelDisp_re_le_five lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr
      (u j) (hzn' j (le_of_lt hj)) (hzr' j (le_of_lt hj))
    have hsucc : (u (j + 1)).re = (u j).re + (Work.Implosion.modelDisp a h (u j)).re := by
      rw [hu' j hj, Complex.add_re]
    rw [hsucc]; linarith
  have hsum : ∑ j ∈ Finset.range n, ‖Work.Implosion.ecalPt a (u j)‖ ^ 2 ≤ 20 / R + 29 / R ^ 2 := by
    have h := sum_zeta_sq_le_sharp lam R hlam hR hlamR u n hx1 hx2 hdec hspace
    simpa only [ha] using h
  have hpoint : ∀ j ∈ Finset.range n,
      |(h (Work.Implosion.ecalPt a (u j)) - τ - h1 * Work.Implosion.ecalPt a (u j)).im|
        ≤ A * ‖Work.Implosion.ecalPt a (u j)‖ ^ 2 := by
    intro j hj
    have hjle : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
    exact le_trans (Complex.abs_im_le_norm _) (hb.2.2.1 _ (hzr' j hjle))
  have hlast : A * (20 / R + 29 / R ^ 2) ≤ 20 * A / R + 8 := by
    have h1 : A / R ^ 2 ≤ 3 / 128 := by
      have h3 : A / R ^ 2 ≤ (3 * R ^ 2 / 128) / R ^ 2 :=
        div_le_div_of_nonneg_right hAub (by positivity)
      have h4 : (3 * R ^ 2 / 128) / R ^ 2 = 3 / 128 := by rw [div_div]; field_simp
      linarith [h3, h4.le, h4.ge]
    have h5 : A * (29 / R ^ 2) ≤ 8 := by
      have h6 : A * (29 / R ^ 2) = 29 * (A / R ^ 2) := by ring
      rw [h6]
      linarith [h1]
    have h6 : A * (20 / R + 29 / R ^ 2) = 20 * A / R + A * (29 / R ^ 2) := by ring
    rw [h6]
    linarith [h5]
  calc ∑ j ∈ Finset.range n,
        |(h (Work.Implosion.ecalPt a (u j)) - τ - h1 * Work.Implosion.ecalPt a (u j)).im|
      ≤ ∑ j ∈ Finset.range n, A * ‖Work.Implosion.ecalPt a (u j)‖ ^ 2 :=
        Finset.sum_le_sum hpoint
    _ = A * ∑ j ∈ Finset.range n, ‖Work.Implosion.ecalPt a (u j)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ A * (20 / R + 29 / R ^ 2) := mul_le_mul_of_nonneg_left hsum hA
    _ ≤ 20 * A / R + 8 := hlast

end Work.PARIMPL2.Direct
