import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.lemma_9_2

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-! ### Green's function estimate with a decay threshold

`l92_green_bound_notA` assumes the bound on the continuants `pd` for *every* `n ≤ k`.  In the
application (AJ Lemma 9.2) the bound is only available for `n ≥ k/40`, because the interval
`[x₁,x₂]` is only known to be long and `y` only known to be at distance `≥ k/40` from its
endpoints.  The proof below is the proof of `l92_green_bound_notA` with the two uses of the
hypothesis restricted to their (large) indices. -/

set_option maxHeartbeats 1000000 in
theorem l92_green_bound_notA_win {α lam : ℝ} {E : ℂ} {θ r L ε₁ : ℝ} {k : ℕ} {x₁ x₂ y : ℤ}
    {n₀ : ℕ}
    (hbd : ∀ n : ℕ, n₀ ≤ n → n ≤ k → ∀ ζ : ℝ,
        ‖pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hn₁ : n₀ ≤ (x₂ - y).toNat) (hn₂ : n₀ ≤ (y - x₁).toNat)
    (hx : x₂ = x₁ + (k : ℤ) - 1) (h1 : x₁ ≤ y) (h2 : y ≤ x₂)
    (hnot : Real.exp (((k : ℝ) + 1) * r) < ‖pd α lam (θ + (x₁ : ℝ) * α) E (k + 1)‖) :
    ‖G α lam θ E x₁ x₂ y x₁‖ < Real.exp ((L + ε₁) * ((x₂ - y : ℤ) : ℝ) - ((k : ℝ) + 1) * r) ∧
    ‖G α lam θ E x₁ x₂ y x₂‖ < Real.exp ((L + ε₁) * ((y - x₁ : ℤ) : ℝ) - ((k : ℝ) + 1) * r) := by
  have hk1 : (x₂ - x₁ + 1).toNat = k := by
    have h : x₂ - x₁ + 1 = (k:ℤ) := by omega
    rw [h]; exact Int.toNat_natCast k
  have hane : 0 ≤ y - x₁ := by omega
  have hbne : 0 ≤ x₂ - y := by omega
  have hkpos : 0 < k := by omega
  have hpdne : pd α lam (θ + (x₁:ℝ)*α) E (k+1) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnot
    exact absurd (Real.exp_pos _) (not_lt.mpr hnot.le)
  have hR : ((-1:ℂ)^k * pd α lam (θ + (x₁:ℝ)*α) E (k+1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hpdne
  have hcast_a : (((y-x₁).toNat : ℕ) : ℝ) = (y:ℝ) - (x₁:ℝ) := by
    have h : (((y-x₁).toNat : ℕ) : ℤ) = y - x₁ := Int.toNat_of_nonneg hane
    exact_mod_cast h
  have hcast_b : (((x₂-y).toNat : ℕ) : ℝ) = (x₂:ℝ) - (y:ℝ) := by
    have h : (((x₂-y).toNat : ℕ) : ℤ) = x₂ - y := Int.toNat_of_nonneg hbne
    exact_mod_cast h
  have hka : k - (y-x₁).toNat = (x₂-y).toNat + 1 := by
    have ha : ((y-x₁).toNat : ℤ) = y - x₁ := Int.toNat_of_nonneg hane
    have hb : ((x₂-y).toNat : ℤ) = x₂ - y := Int.toNat_of_nonneg hbne
    omega
  have hyx_lt : (y-x₁).toNat < k := (Int.toNat_lt hane).mpr (by omega)
  have hxx : (x₁-x₁).toNat < k := by
    rw [show x₁ - x₁ = (0:ℤ) by ring]; exact hkpos
  have hxx2 : (x₂-x₁).toNat < k := by
    rw [hx, show x₁ + (k:ℤ) - 1 - x₁ = (k:ℤ) - 1 by ring]
    have h : ((k:ℤ)-1).toNat = k - 1 := by
      have h' : ((((k:ℤ)-1).toNat : ℕ) : ℤ) = (k:ℤ) - 1 := Int.toNat_of_nonneg (by omega)
      omega
    rw [h]; omega
  -- first Green entry
  have hEq1 : G α lam θ E x₁ x₂ y x₁
      = ((-1:ℂ)^k * pd α lam (θ+(x₁:ℝ)*α) E (k+1))⁻¹ * l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((y-x₁).toNat) 0 := by
    rw [l92_G_eq α lam θ E k x₁ x₂ hk1 hR y x₁, dif_pos ⟨hyx_lt, hxx⟩]
    rw [show (x₁-x₁).toNat = 0 by rw [show x₁ - x₁ = (0:ℤ) by ring]; rfl]
  have hadj1 : l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((y-x₁).toNat) 0
      = (-1:ℂ)^(k-1) * pd α lam (θ + ((y:ℝ)+1)*α) E (k - (y-x₁).toNat) := by
    rw [l92_adjF_ge (α:=α) (lam:=lam) (θ:=θ+(x₁:ℝ)*α) (E:=E) (n:=k) (p:=(y-x₁).toNat) (q:=0) (by omega)]
    rw [show (0:ℕ) + 1 = 1 from rfl, show pd α lam (θ + (x₁:ℝ)*α) E 1 = 1 from rfl, mul_one]
    congr 1
    rw [show (θ + (x₁:ℝ)*α) + ((((y-x₁).toNat) + 1 : ℕ) : ℝ) * α = θ + ((y:ℝ)+1)*α by
      push_cast; rw [hcast_a]; ring]
  have hnorm1 : ‖pd α lam (θ + ((y:ℝ)+1)*α) E (k - (y-x₁).toNat)‖
      ≤ Real.exp (((x₂-y:ℤ):ℝ) * (L + ε₁)) := by
    have hidx : k - (y-x₁).toNat - 1 = (x₂-y).toNat := by omega
    have h := hbd (k - (y-x₁).toNat - 1) (by rw [hidx]; exact hn₁) (by omega) (θ + ((y:ℝ)+1)*α)
    rw [show k - (y-x₁).toNat - 1 + 1 = k - (y-x₁).toNat by omega] at h
    have hN : ((k - (y-x₁).toNat - 1 : ℕ) : ℝ) = ((x₂-y:ℤ):ℝ) := by
      rw [hidx]
      have h2' : (((x₂-y).toNat : ℕ) : ℤ) = x₂ - y := Int.toNat_of_nonneg hbne
      exact_mod_cast h2'
    rwa [hN] at h
  have hinv : (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ < Real.exp (-(((k:ℝ)+1) * r)) := by
    have h := one_div_lt_one_div_of_lt (Real.exp_pos (((k:ℝ)+1) * r)) hnot
    rw [one_div, one_div, ← Real.exp_neg] at h
    exact h
  have hG1b : ‖G α lam θ E x₁ x₂ y x₁‖
      < Real.exp ((L + ε₁) * ((x₂ - y : ℤ) : ℝ) - ((k : ℝ) + 1) * r) := by
    rw [hEq1, hadj1]
    simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hpos : (0:ℝ) < Real.exp (((x₂-y:ℤ):ℝ) * (L + ε₁)) := Real.exp_pos _
    calc (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ * ‖pd α lam (θ + ((y:ℝ)+1)*α) E (k - (y-x₁).toNat)‖
        ≤ (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ * Real.exp (((x₂-y:ℤ):ℝ) * (L + ε₁)) :=
          mul_le_mul_of_nonneg_left hnorm1 (by positivity)
      _ < Real.exp (-(((k:ℝ)+1) * r)) * Real.exp (((x₂-y:ℤ):ℝ) * (L + ε₁)) :=
          mul_lt_mul_of_pos_right hinv hpos
      _ = Real.exp ((L + ε₁) * ((x₂-y:ℤ):ℝ) - ((k:ℝ)+1) * r) := by
          rw [← Real.exp_add]; congr 1; ring
  -- second Green entry
  have hEq2 : G α lam θ E x₁ x₂ y x₂
      = ((-1:ℂ)^k * pd α lam (θ+(x₁:ℝ)*α) E (k+1))⁻¹
          * l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((y-x₁).toNat) ((x₂-x₁).toNat) := by
    rw [l92_G_eq α lam θ E k x₁ x₂ hk1 hR y x₂, dif_pos ⟨hyx_lt, hxx2⟩]
  have hx2n : (x₂-x₁).toNat = k - 1 := by
    rw [hx, show x₁ + (k:ℤ) - 1 - x₁ = (k:ℤ) - 1 by ring]
    have h' : ((((k:ℤ)-1).toNat : ℕ) : ℤ) = (k:ℤ) - 1 := Int.toNat_of_nonneg (by omega)
    omega
  have hadj2 : l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((y-x₁).toNat) ((x₂-x₁).toNat)
      = (-1:ℂ)^(k-1) * pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1) := by
    rw [hx2n,
      l92_adjF_le (α:=α) (lam:=lam) (θ:=θ+(x₁:ℝ)*α) (E:=E) (n:=k) (p:=(y-x₁).toNat) (q:=k-1) (by omega)]
    rw [show k - (k-1) = 1 by omega]
    rw [show pd α lam (θ + (x₁:ℝ)*α + (((k-1:ℕ)+1 : ℕ) : ℝ) * α) E 1 = 1 from rfl, mul_one]
  have hnorm2 : ‖pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1)‖
      ≤ Real.exp (((y-x₁:ℤ):ℝ) * (L + ε₁)) := by
    have h := hbd ((y-x₁).toNat) hn₂ (by omega) (θ + (x₁:ℝ)*α)
    rw [show (((y-x₁).toNat : ℕ) : ℝ) = ((y-x₁:ℤ):ℝ) by
      have h' : (((y-x₁).toNat : ℕ) : ℤ) = y - x₁ := Int.toNat_of_nonneg hane
      exact_mod_cast h'] at h
    exact h
  have hG2b : ‖G α lam θ E x₁ x₂ y x₂‖
      < Real.exp ((L + ε₁) * ((y - x₁ : ℤ) : ℝ) - ((k : ℝ) + 1) * r) := by
    rw [hEq2, hadj2]
    simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hpos : (0:ℝ) < Real.exp (((y-x₁:ℤ):ℝ) * (L + ε₁)) := Real.exp_pos _
    calc (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ * ‖pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1)‖
        ≤ (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ * Real.exp (((y-x₁:ℤ):ℝ) * (L + ε₁)) :=
          mul_le_mul_of_nonneg_left hnorm2 (by positivity)
      _ < Real.exp (-(((k:ℝ)+1) * r)) * Real.exp (((y-x₁:ℤ):ℝ) * (L + ε₁)) :=
          mul_lt_mul_of_pos_right hinv hpos
      _ = Real.exp ((L + ε₁) * ((y-x₁:ℤ):ℝ) - ((k:ℝ)+1) * r) := by
          rw [← Real.exp_add]; congr 1; ring
  exact ⟨hG1b, hG2b⟩

/-- **AJ Lemma 9.2, threshold form**: a `(L-ε,k)`-singular point forces a whole stretch of the
rotation orbit into `A_{k,L-εδ+ε₁}`, assuming the continuant bound only from index `k/40` on
(which is what the singular-window search actually provides). -/
theorem lemma_9_2_win {α lam : ℝ} {E : ℂ} {θ L ε ε₁ δ : ℝ} {k : ℕ} {y : ℤ}
    (hL : 0 ≤ L) (hεL : ε ≤ L) (hε : 0 < ε) (hε₁ : 0 < ε₁)
    (hδ1 : 1 / 40 ≤ δ) (hδ2 : δ ≤ 1 / 2) (hk40 : 40 ≤ k)
    (hkδ : 1 ≤ (k : ℝ) * (δ - 1 / 40))
    (hbd : ∀ n : ℕ, k / 40 ≤ n → n ≤ k → ∀ ζ : ℝ,
        ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hs : Work.TMC16Core.IsSingular α lam θ E (L - ε) k y)
    (x : ℤ) (hx1 : y - (1 - δ) * (k : ℝ) ≤ (x : ℝ)) (hx2 : (x : ℝ) ≤ y - δ * (k : ℝ)) :
    θ + ((x : ℝ) + (((k : ℝ) - 1) / 2)) * α ∈ Work.TMC16Core.AkSet α lam E k (L - ε * δ + ε₁) := by
  rw [Work.TMC16Core.mem_AkSet_iff_shift]
  by_contra hcon
  push Not at hcon
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hdk : (1 : ℝ) ≤ (k : ℝ) * δ := by nlinarith [hkδ, hkpos]
  have hxy : (x : ℝ) ≤ (y : ℝ) := by nlinarith [hx2, hδ0, hkpos]
  have hyx : (y : ℝ) ≤ (x : ℝ) + (k : ℝ) - 1 := by nlinarith [hx1, hdk]
  have hxyZ : x ≤ y := by exact_mod_cast hxy
  have hyxZ : y ≤ x + (k : ℤ) - 1 := by exact_mod_cast hyx
  have hcast1 : (((y - x : ℤ) : ℝ)) = (y : ℝ) - (x : ℝ) := by push_cast; ring
  have hcast2 : (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) = (x : ℝ) + (k : ℝ) - 1 - (y : ℝ) := by
    push_cast; ring
  have hdist1 : (k : ℤ) ≤ 40 * (y - x) := by
    have hreal : ((k : ℤ) : ℝ) ≤ ((40 * (y - x) : ℤ) : ℝ) := by
      push_cast
      have h1 : δ * (k : ℝ) ≤ (y : ℝ) - (x : ℝ) := by linarith [hx2]
      nlinarith [h1, mul_nonneg (sub_nonneg.mpr hδ1) hkpos.le]
    exact_mod_cast hreal
  have hdist2 : (k : ℤ) ≤ 40 * ((x + (k : ℤ) - 1) - y) := by
    have hreal : ((k : ℤ) : ℝ) ≤ ((40 * ((x + (k : ℤ) - 1) - y) : ℤ) : ℝ) := by
      push_cast
      have h1 : δ * (k : ℝ) - 1 ≤ (x : ℝ) + (k : ℝ) - 1 - (y : ℝ) := by linarith [hx1]
      nlinarith [h1, hkδ, hkpos]
    exact_mod_cast hreal
  have hpdne : Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (k + 1) ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hcon
    exact absurd (Real.exp_pos _) (not_lt.mpr hcon.le)
  have hdet : (Work.TMC16Core.dirMat α lam (θ + (x : ℝ) * α) E k).det ≠ 0 :=
    l92_dirMat_det_ne_zero α lam (θ + (x : ℝ) * α) E k
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) hpdne)
  have ha' : δ * (k : ℝ) ≤ ((y - x : ℤ) : ℝ) := by rw [hcast1]; linarith [hx2]
  have hb' : δ * (k : ℝ) - 1 ≤ (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) := by rw [hcast2]; linarith [hx1]
  have hab' : ((y - x : ℤ) : ℝ) + (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) = (k : ℝ) - 1 := by
    rw [hcast1, hcast2]; ring
  have hbnd := l92_exp_bound (k := k) (L := L) (ε := ε) (ε₁ := ε₁) (δ := δ)
    (a := ((y - x : ℤ) : ℝ)) (b := (((x + (k : ℤ) - 1) - y : ℤ) : ℝ))
    hL hε hεL hε₁ hδ1 hδ2 ha' hb' hab'
  have hw2 : k / 40 ≤ (y - x).toNat := by
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 40)]
    have hnat : k ≤ 40 * (y - x).toNat := by
      have hz : ((40 * (y - x).toNat : ℕ) : ℤ) = 40 * (y - x) := by
        push_cast
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ y - x)]
      have hkz : ((k : ℕ) : ℤ) ≤ ((40 * (y - x).toNat : ℕ) : ℤ) := by rw [hz]; exact hdist1
      exact_mod_cast hkz
    omega
  have hw1 : k / 40 ≤ ((x + (k : ℤ) - 1) - y).toNat := by
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 40)]
    have hnat : k ≤ 40 * ((x + (k : ℤ) - 1) - y).toNat := by
      have hz : ((40 * ((x + (k : ℤ) - 1) - y).toNat : ℕ) : ℤ)
          = 40 * ((x + (k : ℤ) - 1) - y) := by
        push_cast
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (x + (k : ℤ) - 1) - y)]
      have hkz : ((k : ℕ) : ℤ) ≤ ((40 * ((x + (k : ℤ) - 1) - y).toNat : ℕ) : ℤ) := by
        rw [hz]; exact hdist2
      exact_mod_cast hkz
    omega
  have hgb := l92_green_bound_notA_win (α := α) (lam := lam) (E := E) (θ := θ)
    (r := L - ε * δ + ε₁) (L := L) (ε₁ := ε₁) (k := k)
    (x₁ := x) (x₂ := x + (k : ℤ) - 1) (y := y) (n₀ := k / 40) hbd hw1 hw2 rfl hxyZ hyxZ hcon
  have hnonneg1 : (0 : ℝ) ≤ ((y - x : ℤ) : ℝ) := by rw [hcast1]; linarith [hxy]
  have hnonneg2 : (0 : ℝ) ≤ (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) := by rw [hcast2]; linarith [hyx]
  have hG1 : ‖Work.TMC16Core.G α lam θ E x (x + (k : ℤ) - 1) y x‖ <
      Real.exp (-((L - ε) * |((y - x : ℤ) : ℝ)|)) := by
    refine lt_of_lt_of_le hgb.1 ?_
    rw [Real.exp_le_exp, abs_of_nonneg hnonneg1]
    linarith [hbnd.1]
  have hG2 : ‖Work.TMC16Core.G α lam θ E x (x + (k : ℤ) - 1) y (x + (k : ℤ) - 1)‖ <
      Real.exp (-((L - ε) * |((y - (x + (k : ℤ) - 1) : ℤ) : ℝ)|)) := by
    refine lt_of_lt_of_le hgb.2 ?_
    rw [Real.exp_le_exp]
    have habs : |((y - (x + (k : ℤ) - 1) : ℤ) : ℝ)| = (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) := by
      rw [abs_of_nonpos]
      · push_cast; ring
      · push_cast; linarith [hyx]
    rw [habs]
    linarith [hbnd.2]
  exact hs ⟨x, x + (k : ℤ) - 1, rfl, hxyZ, hyxZ, hdist1, hdist2, hdet, hG1, hG2⟩

end Work.TMC16Core.Basic
