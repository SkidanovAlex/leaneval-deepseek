import Mathlib
import Submission.Commons.Geometry.LowerHull.exists_lower_hull_chain

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Commons.Geometry.LowerHull

-- =====================================================================
-- Real-valued lemmas about chords.
-- =====================================================================

/-- Difference of two chords through the common point `(b, yb)`, evaluated at `x`. -/
lemma vbc_chord_adj_sub (a b c ya yb yc x : ℝ) (hb : b - a ≠ 0) (hc : c - b ≠ 0) :
    chord (a, ya) (b, yb) x - chord (b, yb) (c, yc) x =
      (x - b) * ((yb - ya) / (b - a) - (yc - yb) / (c - b)) := by
  unfold chord
  field_simp [hb, hc]
  ring

/-- At `x ≤ b`, increasing slopes force the left-hand chord above the right-hand one. -/
lemma vbc_chord_adj_le_left {a b c ya yb yc x : ℝ}
    (hab : a < b) (hbc : b < c) (hxb : x ≤ b)
    (hsl : (yb - ya) / (b - a) ≤ (yc - yb) / (c - b)) :
    chord (b, yb) (c, yc) x ≤ chord (a, ya) (b, yb) x := by
  have hb' : b - a ≠ 0 := by linarith
  have hc' : c - b ≠ 0 := by linarith
  have hsub := vbc_chord_adj_sub a b c ya yb yc x hb' hc'
  have h1 : 0 ≤ (x - b) * ((yb - ya) / (b - a) - (yc - yb) / (c - b)) := by
    have hx : x - b ≤ 0 := by linarith
    have hs : (yb - ya) / (b - a) - (yc - yb) / (c - b) ≤ 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos hx hs
  linarith

/-- At `x ≥ b`, increasing slopes force the right-hand chord above the left-hand one. -/
lemma vbc_chord_adj_le_right {a b c ya yb yc x : ℝ}
    (hab : a < b) (hbc : b < c) (hxb : b ≤ x)
    (hsl : (yb - ya) / (b - a) ≤ (yc - yb) / (c - b)) :
    chord (a, ya) (b, yb) x ≤ chord (b, yb) (c, yc) x := by
  have hb' : b - a ≠ 0 := by linarith
  have hc' : c - b ≠ 0 := by linarith
  have hsub := vbc_chord_adj_sub a b c ya yb yc x hb' hc'
  have h1 : (x - b) * ((yb - ya) / (b - a) - (yc - yb) / (c - b)) ≤ 0 := by
    have hx : 0 ≤ x - b := by linarith
    have hs : (yb - ya) / (b - a) - (yc - yb) / (c - b) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hx hs
  linarith

/-- chord through `(a,ya),(b,yb)` expressed from the right endpoint. -/
lemma vbc_chord_affine_right {a b ya yb x : ℝ} (hne : b - a ≠ 0) :
    chord (a, ya) (b, yb) x = yb + ((yb - ya) / (b - a)) * (x - b) := by
  unfold chord
  field_simp [hne]
  ring

/-- chord through `(a,ya),(b,yb)` expressed from the left endpoint. -/
lemma vbc_chord_affine_left {a b ya yb x : ℝ} (hne : b - a ≠ 0) :
    chord (a, ya) (b, yb) x = ya + ((yb - ya) / (b - a)) * (x - a) := by
  unfold chord
  field_simp [hne]

/-- Strict corner: with supporting lines of slopes `mL < mR` at abscissa `r`, the chord
between the two points at `c` and `d` lies strictly above the vertex value `Y`. -/
lemma vbc_lt_of_support_lines {c r d Y yc yd mL mR : ℝ}
    (hcr : c < r) (hrd : r < d)
    (hL : Y + mL * (c - r) ≤ yc) (hR : Y + mR * (d - r) ≤ yd)
    (hsl : mL < mR) :
    Y < yc + (yd - yc) * ((r - c) / (d - c)) := by
  have hdc : 0 < d - c := by linarith
  have hdr : 0 < d - r := by linarith
  have hrc : 0 < r - c := by linarith
  have h1 : Y * (d - c) < yc * (d - r) + yd * (r - c) := by
    have hyc : Y * (d - r) + mL * (c - r) * (d - r) ≤ yc * (d - r) := by
      have hm := mul_le_mul_of_nonneg_right hL (le_of_lt hdr)
      linarith
    have hyd : Y * (r - c) + mR * (d - r) * (r - c) ≤ yd * (r - c) := by
      have hm := mul_le_mul_of_nonneg_right hR (le_of_lt hrc)
      linarith
    have hsum : Y * (d - r) + Y * (r - c) + mL * (c - r) * (d - r) +
          mR * (d - r) * (r - c) ≤ yc * (d - r) + yd * (r - c) := by
      linarith
    have hpos : 0 < (r - c) * (d - r) * (mR - mL) := by
      have h1' : 0 < (r - c) * (d - r) := mul_pos hrc hdr
      exact mul_pos h1' (sub_pos.mpr hsl)
    have hmain : Y * (d - c) + (r - c) * (d - r) * (mR - mL) ≤
          yc * (d - r) + yd * (r - c) := by
      calc
        Y * (d - c) + (r - c) * (d - r) * (mR - mL)
            = Y * (d - r) + Y * (r - c) + mL * (c - r) * (d - r) +
                mR * (d - r) * (r - c) := by ring
        _ ≤ yc * (d - r) + yd * (r - c) := hsum
    linarith
  have hdiv : Y < (yc * (d - r) + yd * (r - c)) / (d - c) := by
    rw [lt_div_iff₀ hdc]
    exact h1
  have hdcn : d - c ≠ 0 := ne_of_gt hdc
  have hrew : yc + (yd - yc) * ((r - c) / (d - c)) =
        (yc * (d - r) + yd * (r - c)) / (d - c) := by
    field_simp [hdcn]
    ring
  rwa [hrew]

-- =====================================================================
-- Hull hypotheses rewritten at natural indices.
-- =====================================================================

/-- Consecutive-increase of abscissae at natural index `t` (`(t,t+1)`). -/
lemma vbc_hinc_nat {N k : ℕ} {v : Fin (k + 1) → Fin (N + 1)} {t : ℕ} (ht : t < k)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val) :
    (v ⟨t, by omega⟩).val < (v ⟨t + 1, by omega⟩).val := by
  let j : Fin k := ⟨t, ht⟩
  have hfe_c : Fin.castSucc j = (⟨t, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j]
  have hfe_s : Fin.succ j = (⟨t + 1, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j]
  rw [← hfe_c, ← hfe_s]
  exact hinc j

/-- Consecutive-increase ending at `M`: pair `(M-1, M)`. -/
lemma vbc_hinc_prev {N k : ℕ} {v : Fin (k + 1) → Fin (N + 1)} {M : ℕ}
    (hM : M < k) (hM1 : 1 ≤ M)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val) :
    (v ⟨M - 1, by omega⟩).val < (v ⟨M, by omega⟩).val := by
  have h := vbc_hinc_nat (t := M - 1) (by omega : M - 1 < k) hinc
  have hfe : (⟨(M - 1) + 1, by omega⟩ : Fin (k + 1)) = (⟨M, by omega⟩ : Fin (k + 1)) := by
    apply Fin.ext <;> simp <;> omega
  rwa [hfe] at h

/-- Slope increase at natural index `t`: slope(t,t+1) < slope(t+1,t+2). -/
lemma vbc_hslope_pair {N k : ℕ} {y : Fin (N + 1) → ℝ} {v : Fin (k + 1) → Fin (N + 1)} {t : ℕ}
    (ht : t + 1 < k)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
        ((y (v (Fin.succ j)) - y (v (Fin.castSucc j))) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) <
          ((y (v ⟨j.val + 2, by omega⟩) - y (v (Fin.succ j))) /
            (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))) :
    ((y (v ⟨t + 1, by omega⟩) - y (v ⟨t, by omega⟩)) /
        (((v ⟨t + 1, by omega⟩).val : ℝ) - ((v ⟨t, by omega⟩).val : ℝ))) <
      ((y (v ⟨t + 2, by omega⟩) - y (v ⟨t + 1, by omega⟩)) /
        (((v ⟨t + 2, by omega⟩).val : ℝ) - ((v ⟨t + 1, by omega⟩).val : ℝ))) := by
  have ht0 : t < k := by omega
  let j : Fin k := ⟨t, ht0⟩
  have hj : j.val + 1 < k := by
    simpa [j] using ht
  have hsl := hslope j hj
  have hfe_c : Fin.castSucc j = (⟨t, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j]
  have hfe_s : Fin.succ j = (⟨t + 1, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j]
  have hfe_t : (⟨j.val + 2, by omega⟩ : Fin (k + 1)) = (⟨t + 2, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j]
  rw [hfe_c, hfe_s, hfe_t] at hsl
  exact hsl

/-- Slope increase for the pair ending at vertex `M`: slope(M-1,M) < slope(M,M+1). -/
lemma vbc_slope_inc {N k : ℕ} {y : Fin (N + 1) → ℝ} {v : Fin (k + 1) → Fin (N + 1)} {M : ℕ}
    (hM : M < k) (hM1 : 1 ≤ M)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
        ((y (v (Fin.succ j)) - y (v (Fin.castSucc j))) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) <
          ((y (v ⟨j.val + 2, by omega⟩) - y (v (Fin.succ j))) /
            (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))) :
    ((y (v ⟨M, by omega⟩) - y (v ⟨M - 1, by omega⟩)) /
        (((v ⟨M, by omega⟩).val : ℝ) - ((v ⟨M - 1, by omega⟩).val : ℝ))) <
      ((y (v ⟨M + 1, by omega⟩) - y (v ⟨M, by omega⟩)) /
        (((v ⟨M + 1, by omega⟩).val : ℝ) - ((v ⟨M, by omega⟩).val : ℝ))) := by
  have h := vbc_hslope_pair (y := y) (v := v) (t := M - 1) (by omega : (M - 1) + 1 < k) hslope
  have hfe1 : (⟨(M - 1) + 1, by omega⟩ : Fin (k + 1)) = (⟨M, by omega⟩ : Fin (k + 1)) := by
    apply Fin.ext <;> simp <;> omega
  have hfe2 : (⟨(M - 1) + 2, by omega⟩ : Fin (k + 1)) = (⟨M + 1, by omega⟩ : Fin (k + 1)) := by
    apply Fin.ext <;> simp <;> omega
  rwa [hfe1, hfe2] at h

/-- Chord-form segment-below at natural index `t`. -/
lemma vbc_hseg_nat {N k : ℕ} {y : Fin (N + 1) → ℝ} {v : Fin (k + 1) → Fin (N + 1)} {t : ℕ}
    (ht : t < k)
    (hseg : ∀ (j : Fin k) (i : Fin (N + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          chord (((v (Fin.castSucc j)).val : ℝ), y (v (Fin.castSucc j)))
                (((v (Fin.succ j)).val : ℝ), y (v (Fin.succ j))) ((i.val : ℝ)) ≤ y i) :
    ∀ i : Fin (N + 1), (v ⟨t, by omega⟩).val ≤ i.val → i.val ≤ (v ⟨t + 1, by omega⟩).val →
      chord (((v ⟨t, by omega⟩).val : ℝ), y (v ⟨t, by omega⟩))
            (((v ⟨t + 1, by omega⟩).val : ℝ), y (v ⟨t + 1, by omega⟩)) ((i.val : ℝ)) ≤ y i := by
  let j : Fin k := ⟨t, ht⟩
  intro i h1 h2
  have hfe_c : Fin.castSucc j = (⟨t, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j]
  have hfe_s : Fin.succ j = (⟨t + 1, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j]
  have h1' : (v (Fin.castSucc j)).val ≤ i.val := by
    rw [hfe_c]
    exact h1
  have h2' : i.val ≤ (v (Fin.succ j)).val := by
    rw [hfe_s]
    exact h2
  have res := hseg j i h1' h2'
  rw [hfe_c, hfe_s] at res
  exact res


-- =====================================================================
-- Left supporting claim: for `x ≤ A_M` the point `(x, y x)` lies at or
-- above the left supporting chord of vertex `M` (slope of segment M-1).
-- =====================================================================

/-- Base of the left claim at vertex 1. -/
lemma vbc_hull_left_base {N k : ℕ} (y : Fin (N + 1) → ℝ) {v : Fin (k + 1) → Fin (N + 1)}
    (hv0 : v 0 = 0)
    (hseg : ∀ (j : Fin k) (i : Fin (N + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          chord (((v (Fin.castSucc j)).val : ℝ), y (v (Fin.castSucc j)))
                (((v (Fin.succ j)).val : ℝ), y (v (Fin.succ j))) ((i.val : ℝ)) ≤ y i)
    (hk : 1 ≤ k) :
    ∀ x : Fin (N + 1), x.val ≤ (v ⟨1, by omega⟩).val →
      chord (((v ⟨0, by omega⟩).val : ℝ), y (v ⟨0, by omega⟩))
            (((v ⟨1, by omega⟩).val : ℝ), y (v ⟨1, by omega⟩)) ((x.val : ℝ)) ≤ y x := by
  intro x hx
  have h0k : 0 < k := by omega
  let s0 : Fin k := ⟨0, h0k⟩
  have hcast : Fin.castSucc s0 = (0 : Fin (k + 1)) := by
    apply Fin.ext <;> simp [s0]
  have hsuccE : Fin.succ s0 = (⟨1, by omega⟩ : Fin (k + 1)) := by
    apply Fin.ext <;> simp [s0]
  have hcs0v : (v (Fin.castSucc s0)).val ≤ x.val := by
    rw [hcast, hv0]
    simp
  have hsucc : x.val ≤ (v (Fin.succ s0)).val := by
    rw [hsuccE]
    exact hx
  have hs := hseg s0 x hcs0v hsucc
  rw [hcast, hsuccE] at hs
  simpa [s0] using hs

/-- Left supporting bound for the vertex at natural index `M` (`1 ≤ M ≤ k`). -/
lemma vbc_hull_left_claim {N k : ℕ} (y : Fin (N + 1) → ℝ) {v : Fin (k + 1) → Fin (N + 1)}
    (hv0 : v 0 = 0)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (N + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          chord (((v (Fin.castSucc j)).val : ℝ), y (v (Fin.castSucc j)))
                (((v (Fin.succ j)).val : ℝ), y (v (Fin.succ j))) ((i.val : ℝ)) ≤ y i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
        ((y (v (Fin.succ j)) - y (v (Fin.castSucc j))) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) <
          ((y (v ⟨j.val + 2, by omega⟩) - y (v (Fin.succ j))) /
            (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ))))
    {M : ℕ} (hM1 : 1 ≤ M) (hMk : M ≤ k) :
    ∀ x : Fin (N + 1), x.val ≤ (v ⟨M, by omega⟩).val →
      chord (((v ⟨M - 1, by omega⟩).val : ℝ), y (v ⟨M - 1, by omega⟩))
            (((v ⟨M, by omega⟩).val : ℝ), y (v ⟨M, by omega⟩)) ((x.val : ℝ)) ≤ y x := by
  induction M with
  | zero => omega
  | succ M ih =>
      intro x hx
      by_cases hM0 : M = 0
      · have hk1 : 1 ≤ k := by omega
        have hb := vbc_hull_left_base y hv0 hseg hk1 x (by simpa [hM0] using hx)
        simpa [hM0] using hb
      · have hM1c : 1 ≤ M := by omega
        have hMkc : M ≤ k := by omega
        by_cases hbig : (v ⟨M, by omega⟩).val ≤ x.val
        · have hMk' : M < k := by omega
          exact vbc_hseg_nat (y := y) (v := v) (t := M) hMk' hseg x hbig hx
        · have hxM : x.val ≤ (v ⟨M, by omega⟩).val := by omega
          have hih := ih hM1c hMkc x hxM
          have hMk' : M < k := by omega
          have hincL := vbc_hinc_prev (M := M) hMk' hM1c hinc
          have hincR := vbc_hinc_nat (t := M) hMk' hinc
          have hsl := vbc_slope_inc (y := y) (v := v) (M := M) hMk' hM1c hslope
          have hcmp := vbc_chord_adj_le_left
              (a := ((v ⟨M - 1, by omega⟩).val : ℝ)) (b := ((v ⟨M, by omega⟩).val : ℝ))
              (c := ((v ⟨M + 1, by omega⟩).val : ℝ))
              (ya := y (v ⟨M - 1, by omega⟩)) (yb := y (v ⟨M, by omega⟩))
              (yc := y (v ⟨M + 1, by omega⟩)) (x := (x.val : ℝ))
              (by exact_mod_cast hincL) (by exact_mod_cast hincR)
              (by exact_mod_cast (le_of_lt (by omega : x.val < (v ⟨M, by omega⟩).val)))
              (le_of_lt hsl)
          exact le_trans hcmp hih

-- =====================================================================
-- Right supporting claim: for `x ≥ A_M` the point `(x, y x)` lies at or
-- above the right supporting chord of vertex `M` (slope of segment M).
-- =====================================================================

/-- Base of the right claim at segment `k-1`. -/
lemma vbc_hull_right_base {N k : ℕ} (y : Fin (N + 1) → ℝ) {v : Fin (k + 1) → Fin (N + 1)}
    (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨N, Nat.lt_succ_self N⟩)
    (hseg : ∀ (j : Fin k) (i : Fin (N + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          chord (((v (Fin.castSucc j)).val : ℝ), y (v (Fin.castSucc j)))
                (((v (Fin.succ j)).val : ℝ), y (v (Fin.succ j))) ((i.val : ℝ)) ≤ y i)
    (hk : 1 ≤ k) :
    ∀ x : Fin (N + 1), (v ⟨k - 1, by omega⟩).val ≤ x.val →
      chord (((v ⟨k - 1, by omega⟩).val : ℝ), y (v ⟨k - 1, by omega⟩))
            (((v ⟨k, by omega⟩).val : ℝ), y (v ⟨k, by omega⟩)) ((x.val : ℝ)) ≤ y x := by
  intro x hx
  have hkj : k - 1 < k := by omega
  let j : Fin k := ⟨k - 1, hkj⟩
  have hfe_c : Fin.castSucc j = (⟨k - 1, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j]
  have hfe_s : Fin.succ j = (⟨k, by omega⟩ : Fin (k + 1)) := by
    congr 1 <;> apply Fin.ext <;> simp [j] <;> omega
  have h1 : (v (Fin.castSucc j)).val ≤ x.val := by
    rw [hfe_c]
    exact hx
  have h2 : x.val ≤ (v (Fin.succ j)).val := by
    rw [hfe_s]
    have hvk : (v (⟨k, by omega⟩ : Fin (k + 1))).val = N := by
      have hfe : (⟨k, by omega⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ := by
        apply Fin.ext <;> simp
      rw [hfe, hvN]
    rw [hvk]
    have hxN : x.val ≤ N := by
      have := x.isLt
      omega
    exact hxN
  have hs := hseg j x h1 h2
  rw [hfe_c, hfe_s] at hs
  exact hs

/-- Right supporting bound for segment index `M` (`M ≤ k-1`). -/
lemma vbc_hull_right_claim {N k : ℕ} (y : Fin (N + 1) → ℝ) {v : Fin (k + 1) → Fin (N + 1)}
    (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨N, Nat.lt_succ_self N⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (N + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          chord (((v (Fin.castSucc j)).val : ℝ), y (v (Fin.castSucc j)))
                (((v (Fin.succ j)).val : ℝ), y (v (Fin.succ j))) ((i.val : ℝ)) ≤ y i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
        ((y (v (Fin.succ j)) - y (v (Fin.castSucc j))) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) <
          ((y (v ⟨j.val + 2, by omega⟩) - y (v (Fin.succ j))) /
            (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ))))
    {M : ℕ} (hk : 1 ≤ k) (hMk : M ≤ k - 1) :
    ∀ x : Fin (N + 1), (v ⟨M, by omega⟩).val ≤ x.val →
      chord (((v ⟨M, by omega⟩).val : ℝ), y (v ⟨M, by omega⟩))
            (((v ⟨M + 1, by omega⟩).val : ℝ), y (v ⟨M + 1, by omega⟩)) ((x.val : ℝ)) ≤ y x := by
  let claim : (s : ℕ) → s ≤ k - 1 → Prop := fun s hs =>
    ∀ x : Fin (N + 1), (v ⟨s, by omega⟩).val ≤ x.val →
      chord (((v ⟨s, by omega⟩).val : ℝ), y (v ⟨s, by omega⟩))
            (((v ⟨s + 1, by omega⟩).val : ℝ), y (v ⟨s + 1, by omega⟩)) ((x.val : ℝ)) ≤ y x
  have hself : claim (k - 1) (by omega) := by
    intro x hx
    -- base: segment k-1 with endpoints ⟨k-1⟩⟨k⟩; glue ⟨k⟩ ↔ ⟨(k-1)+1⟩
    have hb := vbc_hull_right_base y hvN hseg hk x hx
    have hfe : (⟨k, by omega⟩ : Fin (k + 1)) = (⟨(k - 1) + 1, by omega⟩ : Fin (k + 1)) := by
      apply Fin.ext <;> simp <;> omega
    rwa [hfe] at hb
  have hstep : ∀ (s : ℕ) (hs : s < k - 1), claim (s + 1) (by omega) → claim s (by omega) := by
    intro s hs hnext x hx
    -- claim at segment s
    by_cases hbig : (v ⟨s + 1, by omega⟩).val ≤ x.val
    · have h1 := hnext x hbig
      -- h1: chord over ⟨s+1⟩⟨(s+1)+1⟩ at x ≤ y x
      have hs' : s + 1 < k := by omega
      have hincL := vbc_hinc_nat (t := s) (by omega : s < k) hinc
      have hincR := vbc_hinc_nat (t := s + 1) hs' hinc
      have hsl := vbc_hslope_pair (y := y) (v := v) (t := s) hs' hslope
      have hcmp := vbc_chord_adj_le_right
          (a := ((v ⟨s, by omega⟩).val : ℝ)) (b := ((v ⟨s + 1, by omega⟩).val : ℝ))
          (c := ((v ⟨s + 2, by omega⟩).val : ℝ))
          (ya := y (v ⟨s, by omega⟩)) (yb := y (v ⟨s + 1, by omega⟩))
          (yc := y (v ⟨s + 2, by omega⟩)) (x := (x.val : ℝ))
          (by exact_mod_cast hincL) (by exact_mod_cast hincR)
          (by exact_mod_cast hbig) (le_of_lt hsl)
      -- hcmp: chord ⟨s⟩⟨s+1⟩ ≤ chord ⟨s+1⟩⟨s+2⟩; glue ⟨s+2⟩ ↔ ⟨(s+1)+1⟩ in h1
      have hfe : (⟨s + 2, by omega⟩ : Fin (k + 1)) = (⟨(s + 1) + 1, by omega⟩ : Fin (k + 1)) := by
        apply Fin.ext <;> simp <;> omega
      have h1' : chord (((v ⟨s + 1, by omega⟩).val : ℝ), y (v ⟨s + 1, by omega⟩))
            (((v ⟨s + 2, by omega⟩).val : ℝ), y (v ⟨s + 2, by omega⟩)) ((x.val : ℝ)) ≤ y x := by
        rwa [hfe] at h1
      exact le_trans hcmp h1'
    · -- x < A_{s+1} : x in segment s
      have hx2 : x.val ≤ (v ⟨s + 1, by omega⟩).val := by omega
      have hs0 : s < k := by omega
      exact vbc_hseg_nat (y := y) (v := v) (t := s) hs0 hseg x hx hx2
  exact Nat.decreasingInduction (n := k - 1) (motive := claim) hstep hself (m := M) hMk
-- =====================================================================
-- Main theorem.
-- =====================================================================

theorem vertex_below_chord {N : ℕ} (y : Fin (N + 1) → ℝ)
    {k : ℕ} {v : Fin (k + 1) → Fin (N + 1)}
    (hv0 : v 0 = 0) (hvN : v ⟨k, Nat.lt_succ_self k⟩ = ⟨N, Nat.lt_succ_self N⟩)
    (hinc : ∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val)
    (hseg : ∀ (j : Fin k) (i : Fin (N + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          y (v (Fin.castSucc j)) +
              (y (v (Fin.succ j)) - y (v (Fin.castSucc j))) *
                (((i.val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) /
                  (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) ≤
            y i)
    (hslope : ∀ (j : Fin k) (hj : j.val + 1 < k),
        ((y (v (Fin.succ j)) - y (v (Fin.castSucc j))) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) <
          ((y (v ⟨j.val + 2, by omega⟩) - y (v (Fin.succ j))) /
            (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ))))
    {r c d : Fin (N + 1)} (hcr : c.val < r.val) (hrd : r.val < d.val)
    (hvert : ∃ j : Fin (k + 1), (v j).val = r.val) :
    y r < y c + (y d - y c) * (((r.val : ℝ) - (c.val : ℝ)) / (((d.val : ℝ) - (c.val : ℝ)))) := by
  rcases hvert with ⟨jr, hjr⟩
  let jn : ℕ := jr.val
  have hjn1 : 1 ≤ jn := by
    by_contra h
    have h0 : jn = 0 := by omega
    have hfe : jr = (⟨0, by omega⟩ : Fin (k + 1)) := by
      apply Fin.ext <;> simp [jn, h0]
    have hr0 : r.val = 0 := by
      rw [← hjr]
      rw [hfe]
      have hz : (⟨0, by omega⟩ : Fin (k + 1)) = (0 : Fin (k + 1)) := by
        apply Fin.ext <;> simp
      rw [hz, hv0] <;> rfl
    omega
  have hjnk : jn < k := by
    by_contra h
    have hjk : k ≤ jn := by omega
    have hjnk' : jn = k := by omega
    have hfe : jr = (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
      apply Fin.ext <;> simp [jn, hjnk']
    have hrN : r.val = N := by
      rw [← hjr]
      rw [hfe, hvN] <;> rfl
    have hxN : d.val ≤ N := by
      have := d.isLt
      omega
    omega
  have hk1 : 1 ≤ k := by omega
  -- chord form of hseg
  have hsegC : ∀ (j : Fin k) (i : Fin (N + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          chord (((v (Fin.castSucc j)).val : ℝ), y (v (Fin.castSucc j)))
                (((v (Fin.succ j)).val : ℝ), y (v (Fin.succ j))) ((i.val : ℝ)) ≤ y i := by
    intro j i h1 h2
    exact hseg j i h1 h2
  -- v ⟨jn⟩ = r
  have hfe_jr : (⟨jn, by omega⟩ : Fin (k + 1)) = jr := by
    apply Fin.ext <;> simp [jn]
  have hvjn : v (⟨jn, by omega⟩ : Fin (k + 1)) = r := by
    rw [hfe_jr]
    exact Fin.ext hjr
  have hvjnval : (v (⟨jn, by omega⟩ : Fin (k + 1))).val = r.val := by
    rw [hvjn]
  -- left supporting bound for c
  have hcL : chord (((v ⟨jn - 1, by omega⟩).val : ℝ), y (v ⟨jn - 1, by omega⟩))
        (((v ⟨jn, by omega⟩).val : ℝ), y (v ⟨jn, by omega⟩)) ((c.val : ℝ)) ≤ y c := by
    have hcl := vbc_hull_left_claim y hv0 hinc hsegC hslope (M := jn) hjn1 (by omega : jn ≤ k) c
    exact hcl (by
      rw [hvjnval]
      exact le_of_lt hcr)
  -- right supporting bound for d
  have hcR : chord (((v ⟨jn, by omega⟩).val : ℝ), y (v ⟨jn, by omega⟩))
        (((v ⟨jn + 1, by omega⟩).val : ℝ), y (v ⟨jn + 1, by omega⟩)) ((d.val : ℝ)) ≤ y d := by
    have hcrgt := vbc_hull_right_claim y hvN hinc hsegC hslope (M := jn) hk1 (by omega : jn ≤ k - 1) d
    exact hcrgt (by
      rw [hvjnval]
      exact le_of_lt hrd)
  let Y : ℝ := y r
  let mL : ℝ := (y (v ⟨jn, by omega⟩) - y (v ⟨jn - 1, by omega⟩)) /
        (((v ⟨jn, by omega⟩).val : ℝ) - ((v ⟨jn - 1, by omega⟩).val : ℝ))
  let mR : ℝ := (y (v ⟨jn + 1, by omega⟩) - y (v ⟨jn, by omega⟩)) /
        (((v ⟨jn + 1, by omega⟩).val : ℝ) - ((v ⟨jn, by omega⟩).val : ℝ))
  have hyv : y (v (⟨jn, by omega⟩ : Fin (k + 1))) = Y := by
    dsimp [Y]
    rw [hvjn]
  -- translate hcL into a supporting-line lower bound
  have hneL : ((v ⟨jn, by omega⟩).val : ℝ) - ((v ⟨jn - 1, by omega⟩).val : ℝ) ≠ 0 := by
    have hlt := vbc_hinc_prev (M := jn) (by omega : jn < k) hjn1 hinc
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hlt))
  have hLchord_aff : chord (((v ⟨jn - 1, by omega⟩).val : ℝ), y (v ⟨jn - 1, by omega⟩))
        (((v ⟨jn, by omega⟩).val : ℝ), y (v ⟨jn, by omega⟩)) ((c.val : ℝ)) =
      y (v (⟨jn, by omega⟩ : Fin (k + 1))) +
        mL * ((c.val : ℝ) - ((v (⟨jn, by omega⟩ : Fin (k + 1))).val : ℝ)) := by
    rw [vbc_chord_affine_right (a := ((v ⟨jn - 1, by omega⟩).val : ℝ))
        (b := ((v ⟨jn, by omega⟩).val : ℝ))
        (ya := y (v ⟨jn - 1, by omega⟩)) (yb := y (v ⟨jn, by omega⟩)) (x := (c.val : ℝ)) hneL]
  have hrewL : chord (((v ⟨jn - 1, by omega⟩).val : ℝ), y (v ⟨jn - 1, by omega⟩))
        (((v ⟨jn, by omega⟩).val : ℝ), y (v ⟨jn, by omega⟩)) ((c.val : ℝ)) =
      Y + mL * ((c.val : ℝ) - (r.val : ℝ)) := by
    rw [hLchord_aff, hyv, hvjnval]
  have hL' : Y + mL * ((c.val : ℝ) - (r.val : ℝ)) ≤ y c := by
    rwa [hrewL] at hcL
  -- translate hcR into a supporting-line lower bound
  have hneR : ((v ⟨jn + 1, by omega⟩).val : ℝ) - ((v ⟨jn, by omega⟩).val : ℝ) ≠ 0 := by
    have hlt := vbc_hinc_nat (t := jn) (by omega : jn < k) hinc
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hlt))
  have hRchord_aff : chord (((v ⟨jn, by omega⟩).val : ℝ), y (v ⟨jn, by omega⟩))
        (((v ⟨jn + 1, by omega⟩).val : ℝ), y (v ⟨jn + 1, by omega⟩)) ((d.val : ℝ)) =
      y (v (⟨jn, by omega⟩ : Fin (k + 1))) +
        mR * ((d.val : ℝ) - ((v (⟨jn, by omega⟩ : Fin (k + 1))).val : ℝ)) := by
    rw [vbc_chord_affine_left (a := ((v ⟨jn, by omega⟩).val : ℝ))
        (b := ((v ⟨jn + 1, by omega⟩).val : ℝ))
        (ya := y (v ⟨jn, by omega⟩)) (yb := y (v ⟨jn + 1, by omega⟩)) (x := (d.val : ℝ)) hneR]
  have hrewR : chord (((v ⟨jn, by omega⟩).val : ℝ), y (v ⟨jn, by omega⟩))
        (((v ⟨jn + 1, by omega⟩).val : ℝ), y (v ⟨jn + 1, by omega⟩)) ((d.val : ℝ)) =
      Y + mR * ((d.val : ℝ) - (r.val : ℝ)) := by
    rw [hRchord_aff, hyv, hvjnval]
  have hR' : Y + mR * ((d.val : ℝ) - (r.val : ℝ)) ≤ y d := by
    rwa [hrewR] at hcR
  -- slopes strictly increase
  have hsl : mL < mR := by
    have h := vbc_slope_inc (y := y) (v := v) (M := jn) (by omega : jn < k) hjn1 hslope
    simpa [mL, mR] using h
  -- final strict combination
  have hfinal := vbc_lt_of_support_lines (c := (c.val : ℝ)) (r := (r.val : ℝ)) (d := (d.val : ℝ))
      (Y := Y) (yc := y c) (yd := y d) (mL := mL) (mR := mR)
      (by exact_mod_cast hcr) (by exact_mod_cast hrd) hL' hR' hsl
  simpa [Y] using hfinal

end Commons.Geometry.LowerHull
