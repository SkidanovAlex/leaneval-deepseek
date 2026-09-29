import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.chirpTabWordBnd
import Submission.Work.Transform.chirpTabKit
import Submission.Work.Transform.chirpSetupWord
import Submission.Work.Transform.blendWord
import Submission.Work.Transform.conjVecWord
import Submission.Work.Transform.chirpPostWord
import Submission.Work.Transform.chirpCostArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Work.Transform

open HvdH

/-! ## Small helpers -/

/-- Fixed-point representation of the complex number `1`: the pair `(2^p, 0)`. -/
def cwB2_seedZ (p : ℕ) : ℤ × ℤ := ((2 : ℤ) ^ p, 0)

theorem cwB2_fxC_seed (p : ℕ) : fxC p (cwB2_seedZ p) = 1 := by
  rw [cwB2_seedZ, fxC]
  have h1 : ((((2 : ℤ) ^ p : ℤ)) : ℂ) = (2 : ℂ) ^ p := by push_cast; ring
  rw [h1]
  norm_num

theorem cwB2_inDisc_seed (p : ℕ) : inDisc p (cwB2_seedZ p) := by
  rw [cwB2_seedZ, inDisc]
  rw [two_pow_sq p]
  simp

/-- `IsPow2 t` implies `2 ≤ t`. -/
theorem cwB2_two_le_isPow2 {t : ℕ} (h : HvdH.IsPow2 t) : 2 ≤ t := by
  obtain ⟨k, hk, rfl⟩ := h
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- A product of naturals all `≥ 1` is `≥ 1`. -/
theorem cwB2_one_le_prod (ts : List ℕ) (h : ∀ t ∈ ts, 1 ≤ t) : 1 ≤ ts.prod := by
  induction ts with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a := h a (by simp)
    have hl : ∀ t ∈ l, 1 ≤ t := fun t ht => h t (by simp [ht])
    show 1 ≤ a * l.prod
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp ha) (Nat.one_le_iff_ne_zero.mp (ih hl)))

/-- Each element of a list of naturals all `≥ 1` is at most the product. -/
theorem cwB2_le_prod (ts : List ℕ) (h : ∀ t ∈ ts, 1 ≤ t) {t : ℕ} (ht : t ∈ ts) : t ≤ ts.prod := by
  induction ts with
  | nil => simp at ht
  | cons a l ih =>
    have ha : 1 ≤ a := h a (by simp)
    have hl : ∀ s ∈ l, 1 ≤ s := fun s hs => h s (by simp [hs])
    rcases List.mem_cons.mp ht with hta | htl
    · rw [hta]
      show a ≤ a * l.prod
      exact Nat.le_mul_of_pos_right a (lt_of_lt_of_le Nat.zero_lt_one (cwB2_one_le_prod l hl))
    · calc t ≤ l.prod := ih hl htl
        _ ≤ a * l.prod := Nat.le_mul_of_pos_left l.prod (lt_of_lt_of_le Nat.zero_lt_one ha)

/-- A sub-product `(ts.drop k).prod` is at most `ts.prod`. -/
theorem cwB2_drop_prod_le (ts : List ℕ) (h : ∀ t ∈ ts, 1 ≤ t) (k : ℕ) : (ts.drop k).prod ≤ ts.prod := by
  induction ts generalizing k with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a := h a (by simp)
    have hl : ∀ t ∈ l, 1 ≤ t := fun t ht => h t (by simp [ht])
    rcases k with _ | k'
    · simp
    · have hd : (a :: l).drop (k' + 1) = l.drop k' := by simp
      rw [hd]
      show (l.drop k').prod ≤ a * l.prod
      exact le_trans (ih hl k') (Nat.le_mul_of_pos_left l.prod (lt_of_lt_of_le Nat.zero_lt_one ha))

/-- `1 ≤ (ts.drop k).prod` when all entries are `≥ 1`. -/
theorem cwB2_one_le_drop_prod (ts : List ℕ) (h : ∀ t ∈ ts, 1 ≤ t) (k : ℕ) :
    1 ≤ (ts.drop k).prod := by
  induction ts generalizing k with
  | nil => simp
  | cons a l ih =>
    have hl : ∀ t ∈ l, 1 ≤ t := fun t ht => h t (by simp [ht])
    rcases k with _ | k'
    · exact cwB2_one_le_prod _ h
    · have hd : (a :: l).drop (k' + 1) = l.drop k' := by simp
      rw [hd]
      exact ih hl k'

/-- The maximum of a list of naturals is at most its sum. -/
theorem cwB2_foldr_max_le_sum (ts : List ℕ) : ts.foldr max 0 ≤ ts.sum := by
  induction ts with
  | nil => simp
  | cons a l ih =>
    show max a (l.foldr max 0) ≤ a + l.sum
    refine max_le (Nat.le_add_right _ _) ?_
    exact le_trans ih (Nat.le_add_left _ _)

/-- The maximum of a list of naturals all `≥ 1` is at most the product. -/
theorem cwB2_foldr_max_le_prod (ts : List ℕ) (h : ∀ t ∈ ts, 1 ≤ t) :
    ts.foldr max 0 ≤ ts.prod := by
  induction ts with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a := h a (by simp)
    have hl : ∀ t ∈ l, 1 ≤ t := fun t ht => h t (by simp [ht])
    show max a (l.foldr max 0) ≤ a * l.prod
    refine max_le ?_ ?_
    · exact Nat.le_mul_of_pos_right a (lt_of_lt_of_le Nat.zero_lt_one (cwB2_one_le_prod l hl))
    · exact le_trans (ih hl) (Nat.le_mul_of_pos_left l.prod (lt_of_lt_of_le Nat.zero_lt_one ha))

/-- An element of a list is at most the list maximum. -/
theorem cwB2_le_foldr_max (ts : List ℕ) {t : ℕ} (ht : t ∈ ts) : t ≤ ts.foldr max 0 := by
  induction ts with
  | nil => simp at ht
  | cons a l ih =>
    show t ≤ max a (l.foldr max 0)
    rcases List.mem_cons.mp ht with hta | htl
    · rw [hta]; exact le_max_left _ _
    · exact le_trans (ih htl) (le_max_right _ _)

/-- `2 ^ ts.length ≤ ts.prod` when every entry is `≥ 2`. -/
theorem cwB2_pow_length_le_prod (ts : List ℕ) (h : ∀ t ∈ ts, 2 ≤ t) :
    2 ^ ts.length ≤ ts.prod := by
  induction ts with
  | nil => simp
  | cons a l ih =>
    have ha : 2 ≤ a := h a (by simp)
    have hl : ∀ t ∈ l, 2 ≤ t := fun t ht => h t (by simp [ht])
    show 2 ^ (l.length + 1) ≤ a * l.prod
    rw [pow_succ]
    calc 2 ^ l.length * 2 = 2 * 2 ^ l.length := by ring
      _ ≤ a * l.prod := Nat.mul_le_mul ha (ih hl)

/-- An element of a value vector in the disc is itself in the disc. -/
theorem cwB2_inDisc_at {p n : ℕ} {u : List (ℤ × ℤ)} (h : HvdH.InDiscVec p n u) {b : ℕ}
    (hb : b < u.length) : inDisc p (u.getD b (0, 0)) := by
  have hb' : b < n := by rw [← h.1]; exact hb
  exact inDiscVec_getD h b hb'

/-- Entries of an `InDiscVec` have modulus `≤ 1`. -/
theorem cwB2_norm_le_one {p n : ℕ} {u : List (ℤ × ℤ)} (h : HvdH.InDiscVec p n u)
    {b : ℕ} (hb : b < u.length) : ‖fxC p (u.getD b (0, 0))‖ ≤ 1 :=
  chirpAux_norm_fxC_le_one (cwB2_inDisc_at h hb)

/-- The conjugate of a fixed point differs from `star` by the same amount. -/
theorem cwB2_star_sub_norm (p : ℕ) (z : ℤ × ℤ) (c : ℂ) :
    ‖fxC p (z.1, -z.2) - star c‖ = ‖fxC p z - c‖ := by
  rw [← chirpAux_star_fxC p z, ← star_sub, norm_star]

/-- `ts.drop (ts.length - (i+1)) = ts[i] :: ts.drop (ts.length - i)`. -/
theorem cwB2_drop_sub_eq_cons_getD (ts : List ℕ) {i : ℕ} (hi : i < ts.length) :
    ts.drop (ts.length - (i + 1)) = ts.getD (ts.length - (i + 1)) 0 :: ts.drop (ts.length - i) := by
  have hk : ts.length - (i + 1) < ts.length := by omega
  have hidx : ts.length - (i + 1) + 1 = ts.length - i := by omega
  rw [List.drop_eq_getElem_cons hk, hidx, List.getD_eq_getElem _ _ hk]

/-- Error propagation for one fixed-point complex product (non-strict error for the second factor). -/
theorem cwB2_err_step_le {p : ℕ} {w A B U V : ℂ} {e : ℝ}
    (h1 : (2 : ℝ) ^ p * ‖w - A * B‖ < 2) (h2 : (2 : ℝ) ^ p * ‖A - U‖ < 2)
    (h3 : (2 : ℝ) ^ p * ‖B - V‖ ≤ e) (hB : ‖B‖ ≤ 1) (hU : ‖U‖ ≤ 1) :
    (2 : ℝ) ^ p * ‖w - U * V‖ < 4 + e := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hkey : w - U * V = (w - A * B) + ((A - U) * B + U * (B - V)) := by ring
  have htri : ‖w - U * V‖ ≤ ‖w - A * B‖ + (‖A - U‖ * ‖B‖ + ‖U‖ * ‖B - V‖) := by
    rw [hkey]
    calc ‖(w - A * B) + ((A - U) * B + U * (B - V))‖
        ≤ ‖w - A * B‖ + ‖(A - U) * B + U * (B - V)‖ := norm_add_le _ _
      _ ≤ ‖w - A * B‖ + (‖(A - U) * B‖ + ‖U * (B - V)‖) := by
          have := norm_add_le ((A - U) * B) (U * (B - V))
          linarith
      _ = ‖w - A * B‖ + (‖A - U‖ * ‖B‖ + ‖U‖ * ‖B - V‖) := by rw [norm_mul, norm_mul]
  have hbb : 0 ≤ ‖B - V‖ := norm_nonneg _
  have h4 : (2 : ℝ) ^ p * (‖A - U‖ * ‖B‖) ≤ (2 : ℝ) ^ p * ‖A - U‖ := by
    have h5 : ‖A - U‖ * ‖B‖ ≤ ‖A - U‖ * 1 := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    calc (2 : ℝ) ^ p * (‖A - U‖ * ‖B‖) ≤ (2 : ℝ) ^ p * (‖A - U‖ * 1) :=
          mul_le_mul_of_nonneg_left h5 (le_of_lt hp)
      _ = (2 : ℝ) ^ p * ‖A - U‖ := by ring
  have h5 : (2 : ℝ) ^ p * (‖U‖ * ‖B - V‖) ≤ (2 : ℝ) ^ p * ‖B - V‖ := by
    have h6 : ‖U‖ * ‖B - V‖ ≤ 1 * ‖B - V‖ := mul_le_mul_of_nonneg_right hU hbb
    calc (2 : ℝ) ^ p * (‖U‖ * ‖B - V‖) ≤ (2 : ℝ) ^ p * (1 * ‖B - V‖) :=
          mul_le_mul_of_nonneg_left h6 (le_of_lt hp)
      _ = (2 : ℝ) ^ p * ‖B - V‖ := by ring
  have hstep : (2 : ℝ) ^ p * ‖w - U * V‖
      ≤ (2 : ℝ) ^ p * ‖w - A * B‖ + ((2 : ℝ) ^ p * ‖A - U‖ + (2 : ℝ) ^ p * ‖B - V‖) := by
    calc (2 : ℝ) ^ p * ‖w - U * V‖
        ≤ (2 : ℝ) ^ p * (‖w - A * B‖ + (‖A - U‖ * ‖B‖ + ‖U‖ * ‖B - V‖)) :=
          mul_le_mul_of_nonneg_left htri (le_of_lt hp)
      _ = (2 : ℝ) ^ p * ‖w - A * B‖ + ((2 : ℝ) ^ p * (‖A - U‖ * ‖B‖)
            + (2 : ℝ) ^ p * (‖U‖ * ‖B - V‖)) := by ring
      _ ≤ (2 : ℝ) ^ p * ‖w - A * B‖ + ((2 : ℝ) ^ p * ‖A - U‖ + (2 : ℝ) ^ p * ‖B - V‖) := by
          linarith
  linarith

/-- **The numerical induction step of the chirp fold.** -/
theorem cwB2_chirpStepNum (p t i : ℕ) (tail : List ℕ) (c u w : List (ℤ × ℤ))
    (hc_len : c.length = t)
    (hc_disc : HvdH.InDiscVec p t c)
    (hc_err : ∀ m < t, (2 : ℝ) ^ p * ‖HvdH.fxC p (c.getD m (0, 0)) - Work.Transform.zeta t (m * m)‖ < 2)
    (hu_len : u.length = tail.prod)
    (hu_disc : HvdH.InDiscVec p tail.prod u)
    (hu_err : ∀ b < tail.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (u.getD b (0, 0)) - Work.Transform.chirp tail b‖ ≤ 4 * i)
    (hw_len : w.length = t * tail.prod)
    (hw_disc : HvdH.InDiscVec p (t * tail.prod) w)
    (hw_err : ∀ a < t, ∀ b < tail.prod,
      (2 : ℝ) ^ p * ‖HvdH.fxC p (w.getD (a * tail.prod + b) (0, 0)) -
        HvdH.fxC p (c.getD a (0, 0)) * HvdH.fxC p (u.getD b (0, 0))‖ < 2) :
    (∀ j < t * tail.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (w.getD j (0, 0)) - Work.Transform.chirp (t :: tail) j‖ ≤ 4 * (i + 1)) ∧
    (∀ j < t * tail.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (w.getD j (0, 0)) - Work.Transform.chirp (t :: tail) j‖ < 4 * (i + 1)) := by
  have hstrict : ∀ j < t * tail.prod,
      (2 : ℝ) ^ p * ‖fxC p (w.getD j (0, 0)) - chirp (t :: tail) j‖ < 4 * (i + 1) := by
    intro j hj
    have hPpos : 0 < tail.prod := by
      by_contra h
      have h0 : tail.prod = 0 := by omega
      rw [h0, Nat.mul_zero] at hj
      omega
    set a := j / tail.prod with hadef
    set b := j % tail.prod with hbdef
    have hj_eq : j = a * tail.prod + b := by
      rw [hadef, hbdef, Nat.mul_comm]
      exact (Nat.div_add_mod j tail.prod).symm
    have ha : a < t := by
      rw [hadef, Nat.div_lt_iff_lt_mul hPpos]
      exact hj
    have hb : b < tail.prod := by
      rw [hbdef]; exact Nat.mod_lt _ hPpos
    have h1 : (2 : ℝ) ^ p * ‖fxC p (w.getD (a * tail.prod + b) (0, 0)) -
        fxC p (c.getD a (0, 0)) * fxC p (u.getD b (0, 0))‖ < 2 := hw_err a ha b hb
    have h2 : (2 : ℝ) ^ p * ‖fxC p (c.getD a (0, 0)) - zeta t (a * a)‖ < 2 := hc_err a ha
    have h3 : (2 : ℝ) ^ p * ‖fxC p (u.getD b (0, 0)) - chirp tail b‖ ≤ 4 * i := hu_err b hb
    have hB : ‖fxC p (u.getD b (0, 0))‖ ≤ 1 :=
      cwB2_norm_le_one hu_disc (by rw [hu_len]; exact hb)
    have hU : ‖zeta t (a * a)‖ ≤ 1 := by rw [chirpAux_norm_zeta]
    have hmain := cwB2_err_step_le (p := p) (w := fxC p (w.getD (a * tail.prod + b) (0, 0)))
      (A := fxC p (c.getD a (0, 0))) (B := fxC p (u.getD b (0, 0)))
      (U := zeta t (a * a)) (V := chirp tail b) (e := 4 * i) h1 h2 h3 hB hU
    rw [hj_eq, chirp_kron t tail a b ha hb]
    have : (4 : ℝ) + 4 * i = 4 * (i + 1) := by push_cast; ring
    linarith [hmain, this]
  exact ⟨fun j hj => le_of_lt (hstrict j hj), hstrict⟩

/-- **Cost arithmetic of one fold round.** -/
theorem cwB2_foldCostLe (p T tmax t P Kr Kt Kb : ℕ) (hp : 100 ≤ p) (hT : 1 ≤ T)
    (htmax : t ≤ tmax) (hP1 : 1 ≤ P) (hPT : P ≤ T) (htP : t * P ≤ T) :
    Kr * 3 * (P * (2 * p + 9) + 2 * p + 6)
      + (Kt * (t * (p + 1) ^ Kt) + Kt)
      + Kr * 2 * (t * (2 * p + 9) + p + 4)
      + (Kb * (t * P * p ^ 2) + Kb)
    ≤ (Kr * 3 + Kb + 1) * (T * p ^ 2 + p + 1) + (Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb) := by
  have htT : t ≤ T := by
    have h1 : t * 1 ≤ t * P := Nat.mul_le_mul_left t hP1
    simpa using le_trans h1 htP
  have hZ : 5 * (2 * p + 9) + (5 * p + 23) ≤ 3 * p ^ 2 := by nlinarith [hp]
  have hmain : T * (5 * (2 * p + 9)) + (5 * p + 23) ≤ T * (3 * p ^ 2) := by
    have h1 : T * (5 * (2 * p + 9)) + T * (5 * p + 23) ≤ T * (3 * p ^ 2) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left T hZ
    have h2 : 5 * p + 23 ≤ T * (5 * p + 23) := Nat.le_mul_of_pos_left (5 * p + 23) hT
    exact le_trans (Nat.add_le_add_left h2 _) h1
  have key : 5 * (T * (2 * p + 9)) + 8 * p + 26 ≤ 3 * (T * p ^ 2 + p + 1) := by
    have e1 : 5 * (T * (2 * p + 9)) = T * (5 * (2 * p + 9)) := by ring
    have e2 : 3 * (T * p ^ 2 + p + 1) = T * (3 * p ^ 2) + 3 * p + 3 := by ring
    rw [e1, e2]
    omega
  have hcomb : 3 * (P * (2 * p + 9) + 2 * p + 6) + 2 * (t * (2 * p + 9) + p + 4)
      ≤ 3 * (T * p ^ 2 + p + 1) := by
    have h1 : 3 * (P * (2 * p + 9) + 2 * p + 6) ≤ 3 * (T * (2 * p + 9) + 2 * p + 6) := by
      have h : P * (2 * p + 9) ≤ T * (2 * p + 9) := Nat.mul_le_mul_right (2 * p + 9) hPT
      have h' : P * (2 * p + 9) + 2 * p + 6 ≤ T * (2 * p + 9) + 2 * p + 6 := by omega
      exact Nat.mul_le_mul_left 3 h'
    have h2 : 2 * (t * (2 * p + 9) + p + 4) ≤ 2 * (T * (2 * p + 9) + p + 4) := by
      have h : t * (2 * p + 9) ≤ T * (2 * p + 9) := Nat.mul_le_mul_right (2 * p + 9) htT
      have h' : t * (2 * p + 9) + p + 4 ≤ T * (2 * p + 9) + p + 4 := by omega
      exact Nat.mul_le_mul_left 2 h'
    have h3 : 3 * (T * (2 * p + 9) + 2 * p + 6) + 2 * (T * (2 * p + 9) + p + 4)
        = 5 * (T * (2 * p + 9)) + 8 * p + 26 := by ring
    linarith [h1, h2, h3, key]
  have hKr : Kr * 3 * (P * (2 * p + 9) + 2 * p + 6) + Kr * 2 * (t * (2 * p + 9) + p + 4)
      ≤ Kr * 3 * (T * p ^ 2 + p + 1) := by
    have e : Kr * 3 * (P * (2 * p + 9) + 2 * p + 6) + Kr * 2 * (t * (2 * p + 9) + p + 4)
        = Kr * (3 * (P * (2 * p + 9) + 2 * p + 6) + 2 * (t * (2 * p + 9) + p + 4)) := by ring
    rw [e]
    calc Kr * (3 * (P * (2 * p + 9) + 2 * p + 6) + 2 * (t * (2 * p + 9) + p + 4))
        ≤ Kr * (3 * (T * p ^ 2 + p + 1)) := Nat.mul_le_mul_left Kr hcomb
      _ = Kr * 3 * (T * p ^ 2 + p + 1) := by ring
  have hKb : Kb * (t * P * p ^ 2) + Kb ≤ Kb * (T * p ^ 2 + p + 1) := by
    have h1 : t * P * p ^ 2 ≤ T * p ^ 2 := by
      have h := Nat.mul_le_mul_right (p ^ 2) htP
      simpa [mul_assoc] using h
    have h2 : Kb * (t * P * p ^ 2) ≤ Kb * (T * p ^ 2) := Nat.mul_le_mul_left Kb h1
    have h3 : Kb * (T * p ^ 2) + Kb ≤ Kb * (T * p ^ 2 + p + 1) := by
      have hp1 : 1 ≤ p + 1 := by omega
      have h4 : Kb * 1 ≤ Kb * (p + 1) := Nat.mul_le_mul_left Kb hp1
      calc Kb * (T * p ^ 2) + Kb ≤ Kb * (T * p ^ 2) + Kb * (p + 1) := by
            simpa using Nat.add_le_add_left h4 (Kb * (T * p ^ 2))
        _ = Kb * (T * p ^ 2 + p + 1) := by ring
    linarith [h2, h3]
  have hKt : Kt * (t * (p + 1) ^ Kt) + Kt ≤ Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb := by
    have h := Nat.mul_le_mul_left Kt (Nat.mul_le_mul_right ((p + 1) ^ Kt) htmax)
    omega
  have hRHS : (Kr * 3 + Kb + 1) * (T * p ^ 2 + p + 1) + (Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb)
      = Kr * 3 * (T * p ^ 2 + p + 1)
        + ((Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb) + Kb * (T * p ^ 2 + p + 1))
        + (T * p ^ 2 + p + 1) := by ring
  calc Kr * 3 * (P * (2 * p + 9) + 2 * p + 6)
      + (Kt * (t * (p + 1) ^ Kt) + Kt)
      + Kr * 2 * (t * (2 * p + 9) + p + 4)
      + (Kb * (t * P * p ^ 2) + Kb)
      = (Kr * 3 * (P * (2 * p + 9) + 2 * p + 6) + Kr * 2 * (t * (2 * p + 9) + p + 4))
        + ((Kt * (t * (p + 1) ^ Kt) + Kt) + (Kb * (t * P * p ^ 2) + Kb)) := by ring
    _ ≤ Kr * 3 * (T * p ^ 2 + p + 1)
        + ((Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb) + Kb * (T * p ^ 2 + p + 1)) :=
          add_le_add hKr (add_le_add hKt hKb)
    _ ≤ (Kr * 3 + Kb + 1) * (T * p ^ 2 + p + 1) + (Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb) := by
          rw [hRHS]; exact Nat.le_add_right _ _

/-! ## The fold invariant -/

/-- Invariant of the chirp fold: the accumulator is a disc vector approximating the chirp of the
"tail" `tail` of dimensions, with scaled error `≤ 4 i` (and `< 4 i` for `i > 0`). -/
def FoldInv (p : ℕ) (R : List Val) (i : ℕ) (tail : List ℕ) (acc : List Val) : Prop :=
  ∃ u : List (ℤ × ℤ),
    acc = cvecVal u :: Val.int (p : ℤ) :: R ∧
    u.length = tail.prod ∧ HvdH.InDiscVec p u.length u ∧
    (∀ b < u.length, (2 : ℝ) ^ p * ‖fxC p (u.getD b (0, 0)) - chirp tail b‖ ≤ 4 * i) ∧
    (0 < i → ∀ b < u.length, (2 : ℝ) ^ p * ‖fxC p (u.getD b (0, 0)) - chirp tail b‖ < 4 * i)

/-! ## The chirp word (assembly) -/

theorem chirpWordB2 : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p : ℕ) (ts : List ℕ) (R : List HvdH.Val),
      100 ≤ p → (∀ t ∈ ts, HvdH.IsPow2 t) → ts.length = HvdH.D → ts.prod < 2 ^ p →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.intList ts :: R)
        (fun vs out => ∃ (a ab : List (ℤ × ℤ)),
          out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int p :: R ∧
          a.length = ts.prod ∧ ab.length = ts.prod ∧
          HvdH.InDiscVec p ts.prod a ∧ HvdH.InDiscVec p ts.prod ab ∧
          (∀ j < ts.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (a.getD j (0, 0)) -
            Work.Transform.chirp ts j‖ < 4 * HvdH.D) ∧
          (∀ j < ts.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (ab.getD j (0, 0)) -
            star (Work.Transform.chirp ts j)‖ < 4 * HvdH.D))
        (fun _ => K * (ts.prod * p ^ 2 + ts.sum * (p + 1) ^ K) + K) := by
  intro hK hI hL hF
  obtain ⟨setupP, Ks, hsetup⟩ := chirpSetupWord hK hI hL hF
  obtain ⟨tabP, Kt, htab⟩ := chirpTabWordBnd hK hI hL hF
  obtain ⟨blendP, Kb, hblend⟩ := blendWord hK hI hL hF
  obtain ⟨conjP, Kc, hconj⟩ := conjVecWord hK hI
  obtain ⟨pickP, Kpick, hpick⟩ := hK.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hK.roll
  obtain ⟨foldP, Kf, hfold⟩ := hK.foldList
  let body : HvdH.Cmd := .seq (rollP 2) (.seq tabP (.seq (rollP 1) blendP))
  let postProg : HvdH.Cmd := .seq (pickP 0) (.seq (rollP 2) (.seq conjP (rollP 2)))
  let prog : HvdH.Cmd := .seq (.seq setupP (foldP body)) postProg
  let KK : ℕ := 1000000 * (HvdH.D + 2) * (Ks + Kt + Kb + Kc + Kpick + Kf + Kroll + 2)
  refine ⟨prog, KK, ?_⟩
  intro main p ts R hp hisPow hlen hprod
  have hne : ts ≠ [] := by
    intro h
    have h0 : ([] : List ℕ).length = HvdH.D := by rw [← h]; exact hlen
    simp [HvdH.D] at h0
  have h2le : ∀ t ∈ ts, 2 ≤ t := fun t ht => cwB2_two_le_isPow2 (hisPow t ht)
  have h1le : ∀ t ∈ ts, 1 ≤ t := fun t ht => le_trans (by norm_num) (h2le t ht)
  have hTle : 2 ^ HvdH.D ≤ ts.prod := by
    rw [← hlen]
    exact cwB2_pow_length_le_prod ts h2le
  have hT1 : 1 ≤ ts.prod := le_trans (Nat.one_le_two_pow) hTle
  have hDpos : 0 < ts.length := by rw [hlen]; norm_num [HvdH.D]
  have htS : HvdH.lmax ts ≤ ts.sum := cwB2_foldr_max_le_sum ts
  have htT : HvdH.lmax ts ≤ ts.prod := cwB2_foldr_max_le_prod ts h1le
  have hmapEq : ts.reverse.map Val.int = ts.reverse.map (fun q : ℕ => Val.int (q : ℤ)) := by
    rw [cs_coeL_eq_map, List.map_map]
    rfl
  have hlenXS : (ts.reverse.map (fun q : ℕ => Val.int (q : ℤ))).length = HvdH.D := by
    rw [List.length_map, List.length_reverse]; exact hlen
  let cRound : ℕ := (Kroll * 3 + Kb + 1) * (ts.prod * p ^ 2 + p + 1)
    + (Kt * (HvdH.lmax ts * (p + 1) ^ Kt) + Kt + Kb)
  let postCost : ℕ := Kpick * (ts.prod * (2 * p + 9) + 2) +
    (Kroll * 3 * (ts.prod * (2 * p + 9) * 2 + 3 * (p + 2) + 2) +
      (Kc * (ts.prod * p ^ 2) + Kc
        + Kroll * 3 * (ts.prod * (2 * p + 9) * 2 + 3 * (p + 2) + 2)))
  -- ## the numerical induction step of the fold
  have foldStepW : ∀ (i : ℕ) (acc : List Val),
      i < (ts.reverse.map (fun q : ℕ => Val.int (q : ℤ))).length →
      FoldInv p R i (ts.drop (ts.length - i)) acc →
      WordR main body
        (fun vs => vs = (ts.reverse.map (fun q : ℕ => Val.int (q : ℤ))).getD i .nil :: acc)
        (fun _ out => FoldInv p R (i + 1) (ts.drop (ts.length - (i + 1))) out)
        (fun _ => cRound) := by
    intro i acc hi hinv
    obtain ⟨u, hacc, hulen, hudisc, huerr, huerr'⟩ := hinv
    have hiR : i < ts.reverse.length := by simpa [List.length_map] using hi
    have hiT : i < ts.length := by simpa [List.length_reverse] using hiR
    set t : ℕ := ts.reverse.getD i 0 with htdef
    have hgetD : (ts.reverse.map (fun q : ℕ => Val.int (q : ℤ))).getD i .nil = Val.int t := by
      rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using hi),
        List.getElem_map, ← List.getD_eq_getElem _ _ hiR, htdef]
    have htmem : t ∈ ts := by
      rw [← List.mem_reverse, htdef, List.getD_eq_getElem _ _ hiR]
      exact List.getElem_mem hiR
    have htp : t < 2 ^ p := lt_of_le_of_lt (cwB2_le_prod ts h1le htmem) hprod
    have httmax : t ≤ HvdH.lmax ts := cwB2_le_foldr_max ts htmem
    have ht2 : 2 ≤ t := cwB2_two_le_isPow2 (hisPow t htmem)
    have ht1 : 1 ≤ t := le_trans (by norm_num) ht2
    have hP1 : 1 ≤ (ts.drop (ts.length - i)).prod := cwB2_one_le_drop_prod ts h1le _
    have hPT : (ts.drop (ts.length - i)).prod ≤ ts.prod := cwB2_drop_prod_le ts h1le _
    have hidx : ts.length - (i + 1) = ts.length - 1 - i := by omega
    have hrev : ts.reverse.getD i 0 = ts.getD (ts.length - 1 - i) 0 := by
      rw [List.getD_eq_getElem _ _ hiR, List.getElem_reverse hiR,
        List.getD_eq_getElem _ _ (by omega)]
    have htval : ts.getD (ts.length - (i + 1)) 0 = t := by
      rw [hidx, htdef, hrev]
    have htailEq : ts.drop (ts.length - (i + 1)) = t :: ts.drop (ts.length - i) := by
      rw [cwB2_drop_sub_eq_cons_getD ts hiT, htval]
    have htP : t * (ts.drop (ts.length - i)).prod ≤ ts.prod := by
      have h := cwB2_drop_prod_le ts h1le (ts.length - (i + 1))
      rw [htailEq] at h
      exact h
    -- stage 1: `roll 2`
    have h1 : WordR main (rollP 2)
        (fun vs => vs = Val.int t :: cvecVal u :: Val.int (p : ℤ) :: R)
        (fun _ out => out = Val.int (p : ℤ) :: Val.int t :: cvecVal u :: R)
        (fun _ => Kroll * 3 * ((ts.drop (ts.length - i)).prod * (2 * p + 9) + 2 * p + 6)) := by
      refine hK.conseq main (rollP 2) _ _ _ _ _ _ (hroll main 2) ?_ ?_ ?_
      · intro vs hvs; rw [hvs]; simp
      · intro vs out hvs hout; rw [hvs] at hout; simpa using hout
      · intro vs hvs
        rw [hvs]
        have hsum : ((List.take (2 + 1)
              (Val.int t :: cvecVal u :: Val.int (p : ℤ) :: R)).map vsz).sum
            = vsz (Val.int t) + (vsz (cvecVal u) + vsz (Val.int (p : ℤ))) := by simp
        rw [hsum]
        have hAt : vsz (Val.int t) ≤ p + 2 := by
          rw [chirpAux_vsz_int]; exact isz_natCast_le htp
        have hAu : vsz (cvecVal u) ≤ (ts.drop (ts.length - i)).prod * (2 * p + 9) + 1 := by
          have h := chirpAux_vsz_cvecVal_le hudisc
          rw [hulen] at h
          calc vsz (cvecVal u) ≤ (ts.drop (ts.length - i)).prod * (2 * p + 8)
                + (ts.drop (ts.length - i)).prod + 1 := h
            _ = (ts.drop (ts.length - i)).prod * (2 * p + 9) + 1 := by ring
        have hAp : vsz (Val.int (p : ℤ)) ≤ p + 2 := cs_vsz_int_natCast_le p
        have hbound : vsz (Val.int t) + (vsz (cvecVal u) + vsz (Val.int (p : ℤ))) + 1
            ≤ (ts.drop (ts.length - i)).prod * (2 * p + 9) + 2 * p + 6 := by omega
        calc Kroll * (2 + 1) * ((vsz (Val.int t) + (vsz (cvecVal u)
              + vsz (Val.int (p : ℤ)))) + 1)
            ≤ Kroll * (2 + 1) * ((ts.drop (ts.length - i)).prod * (2 * p + 9) + 2 * p + 6) :=
              Nat.mul_le_mul_left (Kroll * (2 + 1)) hbound
          _ = Kroll * 3 * ((ts.drop (ts.length - i)).prod * (2 * p + 9) + 2 * p + 6) := by ring
    -- stage 2: the table
    have h2 : WordR main tabP
        (fun vs => vs = Val.int (p : ℤ) :: Val.int t :: cvecVal u :: R)
        (fun _ out => ∃ c : List (ℤ × ℤ),
          out = cvecVal c :: Val.int (p : ℤ) :: cvecVal u :: R ∧
          c.length = t ∧ HvdH.InDiscVec p t c ∧
          ∀ m < t, (2 : ℝ) ^ p * ‖fxC p (c.getD m (0, 0)) - zeta t (m * m)‖ < 2)
        (fun _ => Kt * (t * (p + 1) ^ Kt) + Kt) := by
      refine hK.conseq main tabP _ _ _ _ _ _ (htab main p t (cvecVal u :: R) hp ht2 htp) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hq; exact hq.2
      · intro vs hvs; exact le_refl _
    -- stage 3: `roll 1`
    have h3 : ∀ c : List (ℤ × ℤ), c.length = t → HvdH.InDiscVec p t c → WordR main (rollP 1)
        (fun vs => vs = cvecVal c :: Val.int (p : ℤ) :: cvecVal u :: R)
        (fun _ out => out = Val.int (p : ℤ) :: cvecVal c :: cvecVal u :: R)
        (fun _ => Kroll * 2 * (t * (2 * p + 9) + p + 4)) := by
      intro c hclen hcdisc
      refine hK.conseq main (rollP 1) _ _ _ _ _ _ (hroll main 1) ?_ ?_ ?_
      · intro vs hvs; rw [hvs]; simp
      · intro vs out hvs hout; rw [hvs] at hout; simpa using hout
      · intro vs hvs
        rw [hvs]
        have hsum : ((List.take (1 + 1)
              (cvecVal c :: Val.int (p : ℤ) :: cvecVal u :: R)).map vsz).sum
            = vsz (cvecVal c) + vsz (Val.int (p : ℤ)) := by simp
        rw [hsum]
        have hAc : vsz (cvecVal c) ≤ t * (2 * p + 9) + 1 := by
          have h := chirpAux_vsz_cvecVal_le hcdisc
          calc vsz (cvecVal c) ≤ t * (2 * p + 8) + t + 1 := h
            _ = t * (2 * p + 9) + 1 := by ring
        have hAp : vsz (Val.int (p : ℤ)) ≤ p + 2 := cs_vsz_int_natCast_le p
        have hbound : vsz (cvecVal c) + vsz (Val.int (p : ℤ)) + 1 ≤ t * (2 * p + 9) + p + 4 := by
          omega
        calc Kroll * (1 + 1) * (vsz (cvecVal c) + vsz (Val.int (p : ℤ)) + 1)
            ≤ Kroll * (1 + 1) * (t * (2 * p + 9) + p + 4) :=
              Nat.mul_le_mul_left (Kroll * (1 + 1)) hbound
          _ = Kroll * 2 * (t * (2 * p + 9) + p + 4) := by ring
    -- stage 4: the blend
    have h4 : ∀ c : List (ℤ × ℤ), c.length = t → HvdH.InDiscVec p t c → WordR main blendP
        (fun vs => vs = Val.int (p : ℤ) :: cvecVal c :: cvecVal u :: R)
        (fun _ out => ∃ w : List (ℤ × ℤ), out = cvecVal w :: Val.int (p : ℤ) :: R ∧
          w.length = t * u.length ∧ HvdH.InDiscVec p (t * u.length) w ∧
          ∀ a < t, ∀ b < u.length, (2 : ℝ) ^ p * ‖fxC p (w.getD (a * u.length + b) (0, 0)) -
            fxC p (c.getD a (0, 0)) * fxC p (u.getD b (0, 0))‖ < 2)
        (fun _ => Kb * (t * (ts.drop (ts.length - i)).prod * p ^ 2) + Kb) := by
      intro c hclen hcdisc
      have hP1' : 1 ≤ u.length := by rw [hulen]; exact hP1
      refine hK.conseq main blendP _ _ _ _ _ _
        (hblend main p t u.length c u R hp ht1 hP1' hclen rfl hcdisc hudisc) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hq
        obtain ⟨-, w, hw, hwl, hwd, hwerr⟩ := hq
        exact ⟨w, hw, hwl, hwd, hwerr⟩
      · intro vs hvs
        exact le_of_eq (by rw [hulen])
    -- composition of the four stages, run by hand
    intro vs hvs s Rg hRg
    rw [hvs, hgetD, hacc] at hRg
    obtain ⟨o1, s1, n1, ho1, he1, hn1, hs1, hoth1⟩ := h1 _ rfl s Rg hRg
    obtain ⟨o2, s2, n2, ⟨c, ho2, hclen, hcdisc, hcerr⟩, he2, hn2, hs2, hoth2⟩ :=
      h2 o1 ho1 s1 Rg hs1
    obtain ⟨o3, s3, n3, ho3, he3, hn3, hs3, hoth3⟩ :=
      h3 c hclen hcdisc o2 ho2 s2 Rg hs2
    obtain ⟨o4, s4, n4, ⟨w, ho4, hwl, hwd, hwerr⟩, he4, hn4, hs4, hoth4⟩ :=
      h4 c hclen hcdisc o3 ho3 s3 Rg hs3
    obtain ⟨hle, hlt⟩ := cwB2_chirpStepNum p t i (ts.drop (ts.length - i)) c u w hclen hcdisc hcerr
      hulen (by rw [← hulen]; exact hudisc)
      (fun b hb => huerr b (by rw [hulen]; exact hb))
      (by rw [hwl, hulen]) (by rw [← hulen]; exact hwd)
      (by intro a ha b hb; rw [← hulen]; exact hwerr a ha b (by rw [hulen]; exact hb))
    have h4c : (4 : ℝ) * ((i : ℝ) + 1) = 4 * ((i + 1 : ℕ) : ℝ) := by push_cast; ring
    refine ⟨o4, s4, n1 + (n2 + (n3 + n4)), ⟨w, ho4, ?_, ?_, ?_, ?_⟩,
      Eval.seq he1 (Eval.seq he2 (Eval.seq he3 he4)), ?_, hs4, ?_⟩
    · rw [htailEq, List.prod_cons, hwl, hulen]
    · exact ⟨rfl, hwd.2⟩
    · intro b hb
      have hb' : b < t * (ts.drop (ts.length - i)).prod := by rw [← hulen, ← hwl]; exact hb
      rw [htailEq]
      exact le_of_lt (h4c ▸ hlt b hb')
    · intro _ b hb
      have hb' : b < t * (ts.drop (ts.length - i)).prod := by rw [← hulen, ← hwl]; exact hb
      rw [htailEq]
      exact h4c ▸ hlt b hb'
    · have hcost := cwB2_foldCostLe p ts.prod (HvdH.lmax ts) t (ts.drop (ts.length - i)).prod
        Kroll Kt Kb hp hT1 httmax hP1 hPT htP
      have hsum : n1 + (n2 + (n3 + n4)) ≤
          Kroll * 3 * ((ts.drop (ts.length - i)).prod * (2 * p + 9) + 2 * p + 6)
            + ((Kt * (t * (p + 1) ^ Kt) + Kt)
            + (Kroll * 2 * (t * (2 * p + 9) + p + 4)
            + (Kb * (t * (ts.drop (ts.length - i)).prod * p ^ 2) + Kb))) :=
        add_le_add hn1 (add_le_add hn2 (add_le_add hn3 hn4))
      have hring : Kroll * 3 * ((ts.drop (ts.length - i)).prod * (2 * p + 9) + 2 * p + 6)
            + ((Kt * (t * (p + 1) ^ Kt) + Kt)
            + (Kroll * 2 * (t * (2 * p + 9) + p + 4)
            + (Kb * (t * (ts.drop (ts.length - i)).prod * p ^ 2) + Kb)))
          = Kroll * 3 * ((ts.drop (ts.length - i)).prod * (2 * p + 9) + 2 * p + 6)
            + (Kt * (t * (p + 1) ^ Kt) + Kt)
            + Kroll * 2 * (t * (2 * p + 9) + p + 4)
            + (Kb * (t * (ts.drop (ts.length - i)).prod * p ^ 2) + Kb) := by ring
      exact le_trans (hring ▸ hsum) hcost
    · intro k hk
      rw [hoth4 k hk, hoth3 k hk, hoth2 k hk, hoth1 k hk]
  -- ## the fold
  have hsz : ∀ x ∈ ts.reverse.map (fun q : ℕ => Val.int (q : ℤ)), vsz x ≤ p + 2 := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hx
    have hmem : q ∈ ts := List.mem_reverse.mp hq
    have hlt : q < 2 ^ p := lt_of_le_of_lt (cwB2_le_prod ts h1le hmem) hprod
    rw [← hqx, chirpAux_vsz_int]
    exact isz_natCast_le hlt
  have hfoldRaw := hfold main body (ts.reverse.map (fun q : ℕ => Val.int (q : ℤ)))
    (fun i acc => FoldInv p R i (ts.drop (ts.length - i)) acc) cRound (p + 2) hsz foldStepW
  have hfoldW : WordR main (foldP body)
      (fun vs => ∃ acc, vs = ofList (ts.reverse.map (fun q : ℕ => Val.int (q : ℤ))) :: acc
        ∧ FoldInv p R 0 [] acc)
      (fun _ out => FoldInv p R ts.length ts out)
      (fun _ => HvdH.D * (cRound + Kf * (p + 3)) + Kf) := by
    refine hK.conseq main (foldP body) _ _ _ _ _ _ hfoldRaw ?_ ?_ ?_
    · intro vs hvs
      obtain ⟨acc, hvs', hinv⟩ := hvs
      exact ⟨acc, hvs', by simpa using hinv⟩
    · intro vs out hvs hq
      simpa using hq
    · intro vs hvs
      exact le_of_eq (by rw [hlenXS])
  -- ## the initial invariant
  have hinit : FoldInv p R 0 [] (cvecVal [cwB2_seedZ p] :: Val.int (p : ℤ) :: R) := by
    refine ⟨[cwB2_seedZ p], rfl, ?_, ?_, ?_, ?_⟩
    · show ([cwB2_seedZ p]).length = ([] : List ℕ).prod
      simp
    · show HvdH.InDiscVec p ([cwB2_seedZ p]).length [cwB2_seedZ p]
      refine ⟨by simp, ?_⟩
      intro z hz
      rw [List.mem_singleton] at hz
      subst hz
      exact cwB2_inDisc_seed p
    · intro b hb
      have hb1 : b < 1 := by simpa using hb
      have hb0 : b = 0 := by omega
      subst hb0
      simp [cwB2_fxC_seed, chirp_zero]
    · intro h
      omega
  -- ## setup ;;; fold
  have hsetupW : WordR main setupP (fun vs => vs = Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = ofList (ts.reverse.map (fun q : ℕ => Val.int (q : ℤ)))
        :: cvecVal [cwB2_seedZ p] :: Val.int (p : ℤ) :: R)
      (fun _ => Ks * (ts.sum * (p + 1) ^ Ks) + Ks) := by
    refine hK.conseq main setupP _ _ _ _ _ _ (hsetup main p ts R hp hne h2le) ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hq
      have hseed : cvecVal [(2 ^ p, 0)] = cvecVal [cwB2_seedZ p] := by
        rw [cwB2_seedZ]
        try rfl
      rw [hq.2, hmapEq, hseed]
    · intro vs hvs; exact le_refl _
  have hcomp1 : WordR main (.seq setupP (foldP body))
      (fun vs => vs = Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => FoldInv p R ts.length ts out)
      (fun _ => (Ks * (ts.sum * (p + 1) ^ Ks) + Ks)
        + (HvdH.D * (cRound + Kf * (p + 3)) + Kf)) := by
    have hraw := hK.seq main setupP (foldP body) _ _ _ _ _ _ _
      hsetupW hfoldW
      (fun vs mid hv hq =>
        ⟨⟨cvecVal [cwB2_seedZ p] :: Val.int (p : ℤ) :: R, hq, hinit⟩, le_refl _⟩)
    refine hK.conseq main (.seq setupP (foldP body)) _ _ _ _ _ _ hraw
      (fun vs hvs => hvs) ?_ (fun vs _ => le_refl _)
    intro vs out hvs hq
    obtain ⟨mid, hmid, hpost⟩ := hq
    exact hpost
  -- ## the post-processing word
  have hpostW : WordR main postProg
      (fun vs => ∃ a : List (ℤ × ℤ), vs = cvecVal a :: Val.int (p : ℤ) :: R ∧
        a.length = ts.prod ∧ HvdH.InDiscVec p ts.prod a ∧
        ∀ j < ts.prod, (2 : ℝ) ^ p * ‖fxC p (a.getD j (0, 0)) - chirp ts j‖ < 4 * HvdH.D)
      (fun _ out => ∃ a ab : List (ℤ × ℤ),
        out = cvecVal a :: cvecVal ab :: Val.int (p : ℤ) :: R ∧
        a.length = ts.prod ∧ ab.length = ts.prod ∧
        HvdH.InDiscVec p ts.prod a ∧ HvdH.InDiscVec p ts.prod ab ∧
        (∀ j < ts.prod, (2 : ℝ) ^ p * ‖fxC p (a.getD j (0, 0)) - chirp ts j‖ < 4 * HvdH.D) ∧
        (∀ j < ts.prod, (2 : ℝ) ^ p * ‖fxC p (ab.getD j (0, 0)) - star (chirp ts j)‖ < 4 * HvdH.D))
      (fun _ => postCost) := by
    intro vs hpre s Rg hRg
    obtain ⟨a, rfl, halen, hadisc, haerr⟩ := hpre
    obtain ⟨o1, s1, n1, ho1, he1, hn1, hs1, hoth1⟩ :=
      hpick main 0 (cvecVal a :: Val.int (p : ℤ) :: R) (by simp) s Rg hRg
    have ho1' : o1 = cvecVal a :: cvecVal a :: Val.int (p : ℤ) :: R := by rw [ho1]; simp
    obtain ⟨o2, s2, n2, ho2, he2, hn2, hs2, hoth2⟩ :=
      hroll main 2 o1 (by simp only [ho1', List.length_cons]; omega) s1 Rg hs1
    have ho2' : o2 = Val.int (p : ℤ) :: cvecVal a :: cvecVal a :: R := by rw [ho2, ho1']; simp
    obtain ⟨o3, s3, n3, ⟨-, ab, ho3, hablen, habdisc, habconj⟩, he3, hn3, hs3, hoth3⟩ :=
      hconj main p ts.prod a (cvecVal a :: R) hp hT1 halen hadisc o2 ho2' s2 Rg hs2
    have ho3' : o3 = cvecVal ab :: Val.int (p : ℤ) :: cvecVal a :: R := by rw [ho3]
    obtain ⟨o4, s4, n4, ho4, he4, hn4, hs4, hoth4⟩ :=
      hroll main 2 o3 (by simp only [ho3', List.length_cons]; omega) s3 Rg hs3
    have ho4' : o4 = cvecVal a :: cvecVal ab :: Val.int (p : ℤ) :: R := by rw [ho4, ho3']; simp
    have hn1' : n1 ≤ Kpick * (vsz (cvecVal a) + 1) := by
      have e1 : (fun vs : List Val => Kpick * (0 + 1)
            * ((List.map vsz (List.take (0 + 1) vs)).sum + 1))
            (cvecVal a :: Val.int (p : ℤ) :: R) = Kpick * (vsz (cvecVal a) + 1) := by simp
      rw [e1] at hn1
      exact hn1
    have hn2' : n2 ≤ Kroll * 3 * (2 * vsz (cvecVal a) + vsz (Val.int (p : ℤ)) + 1) := by
      rw [ho1'] at hn2
      have e2 : (fun vs : List Val => Kroll * (2 + 1)
            * ((List.map vsz (List.take (2 + 1) vs)).sum + 1))
            (cvecVal a :: cvecVal a :: Val.int (p : ℤ) :: R)
          = Kroll * 3 * (vsz (cvecVal a) + (vsz (cvecVal a) + vsz (Val.int (p : ℤ))) + 1) := by
        simp
      rw [e2] at hn2
      calc n2 ≤ Kroll * 3 * (vsz (cvecVal a)
            + (vsz (cvecVal a) + vsz (Val.int (p : ℤ))) + 1) := hn2
        _ = Kroll * 3 * (2 * vsz (cvecVal a) + vsz (Val.int (p : ℤ)) + 1) := by ring
    have hn4' : n4 ≤ Kroll * 3 * (vsz (cvecVal ab) + vsz (Val.int (p : ℤ)) + vsz (cvecVal a) + 1) := by
      rw [ho3'] at hn4
      have e4 : (fun vs : List Val => Kroll * (2 + 1)
            * ((List.map vsz (List.take (2 + 1) vs)).sum + 1))
            (cvecVal ab :: Val.int (p : ℤ) :: cvecVal a :: R)
          = Kroll * 3 * (vsz (cvecVal ab) + (vsz (Val.int (p : ℤ)) + vsz (cvecVal a)) + 1) := by
        simp
      rw [e4] at hn4
      calc n4 ≤ Kroll * 3 * (vsz (cvecVal ab)
            + (vsz (Val.int (p : ℤ)) + vsz (cvecVal a)) + 1) := hn4
        _ = Kroll * 3 * (vsz (cvecVal ab) + vsz (Val.int (p : ℤ)) + vsz (cvecVal a) + 1) := by ring
    have hsz_a : vsz (cvecVal a) ≤ ts.prod * (2 * p + 9) + 1 := by
      have h := chirpAux_vsz_cvecVal_le hadisc
      calc vsz (cvecVal a) ≤ ts.prod * (2 * p + 8) + ts.prod + 1 := h
        _ = ts.prod * (2 * p + 9) + 1 := by ring
    have hsz_ab : vsz (cvecVal ab) ≤ ts.prod * (2 * p + 9) + 1 := by
      have h := chirpAux_vsz_cvecVal_le habdisc
      calc vsz (cvecVal ab) ≤ ts.prod * (2 * p + 8) + ts.prod + 1 := h
        _ = ts.prod * (2 * p + 9) + 1 := by ring
    have hsz_p : vsz (Val.int (p : ℤ)) ≤ p + 2 := cs_vsz_int_natCast_le p
    have hcost : n1 + (n2 + (n3 + n4)) ≤ postCost := by
      have hb1 : n1 ≤ Kpick * (ts.prod * (2 * p + 9) + 2) := by
        have h : vsz (cvecVal a) + 1 ≤ ts.prod * (2 * p + 9) + 2 := by omega
        exact le_trans hn1' (Nat.mul_le_mul_left _ h)
      have hb2 : n2 ≤ Kroll * 3 * (ts.prod * (2 * p + 9) * 2 + 3 * (p + 2) + 2) := by
        have h : 2 * vsz (cvecVal a) + vsz (Val.int (p : ℤ)) + 1
            ≤ ts.prod * (2 * p + 9) * 2 + 3 * (p + 2) + 2 := by omega
        exact le_trans hn2' (Nat.mul_le_mul_left _ h)
      have hb3 : n3 ≤ Kc * (ts.prod * p ^ 2) + Kc := hn3
      have hb4 : n4 ≤ Kroll * 3 * (ts.prod * (2 * p + 9) * 2 + 3 * (p + 2) + 2) := by
        have h : vsz (cvecVal ab) + vsz (Val.int (p : ℤ)) + vsz (cvecVal a) + 1
            ≤ ts.prod * (2 * p + 9) * 2 + 3 * (p + 2) + 2 := by omega
        exact le_trans hn4' (Nat.mul_le_mul_left _ h)
      exact add_le_add hb1 (add_le_add hb2 (add_le_add hb3 hb4))
    refine ⟨o4, s4, n1 + (n2 + (n3 + n4)), ⟨a, ab, ho4', halen, hablen, hadisc, habdisc, haerr, ?_⟩,
      Eval.seq he1 (Eval.seq he2 (Eval.seq he3 he4)), hcost, hs4, ?_⟩
    · intro j hj
      rw [habconj j hj, cwB2_star_sub_norm]
      exact haerr j hj
    · intro k hk
      rw [hoth4 k hk, hoth3 k hk, hoth2 k hk, hoth1 k hk]
  -- ## fold ;;; post
  have hcomp2 : WordR main (.seq (.seq setupP (foldP body)) postProg)
      (fun vs => vs = Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => ∃ a ab : List (ℤ × ℤ),
        out = cvecVal a :: cvecVal ab :: Val.int (p : ℤ) :: R ∧
        a.length = ts.prod ∧ ab.length = ts.prod ∧
        HvdH.InDiscVec p ts.prod a ∧ HvdH.InDiscVec p ts.prod ab ∧
        (∀ j < ts.prod, (2 : ℝ) ^ p * ‖fxC p (a.getD j (0, 0)) - chirp ts j‖ < 4 * HvdH.D) ∧
        (∀ j < ts.prod, (2 : ℝ) ^ p * ‖fxC p (ab.getD j (0, 0)) - star (chirp ts j)‖ < 4 * HvdH.D))
      (fun _ => (Ks * (ts.sum * (p + 1) ^ Ks) + Ks)
        + (HvdH.D * (cRound + Kf * (p + 3)) + Kf) + postCost) := by
    have hraw := hK.seq main (.seq setupP (foldP body)) postProg _ _ _ _ _ _ _
      hcomp1 hpostW
      (fun vs mid hv hq => by
        obtain ⟨a, hmid, halen, hdisc, herr, herr'⟩ := hq
        refine ⟨⟨a, hmid, halen, ?_, ?_⟩, le_refl _⟩
        · rw [← halen]; exact hdisc
        · intro j hj
          have h := herr' hDpos j (by rw [halen]; exact hj)
          rwa [hlen] at h)
    refine hK.conseq main (.seq (.seq setupP (foldP body)) postProg) _ _ _ _ _ _ hraw
      (fun vs hvs => hvs) ?_ (fun vs _ => le_refl _)
    intro vs out hvs hq
    obtain ⟨mid, hmid, hpost⟩ := hq
    exact hpost
  -- ## final assembly
  refine hK.conseq main prog _ _ _ _ _ _ hcomp2 (fun vs hvs => hvs) ?_ ?_
  · intro vs out hvs hq; exact hq
  · intro vs hvs
    exact chirpCostArith HvdH.D ts.prod ts.sum (HvdH.lmax ts) p Ks Kt Kb Kc Kpick Kf Kroll KK
      rfl hp hTle htS htT (le_refl _)

end Work.Transform
