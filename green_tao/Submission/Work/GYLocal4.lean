import Submission.Work.GYLocal3

/-!
# The localisation step of Green–Tao §9, part 4: sufficient conditions for the numeric bundle

`Submission/Work/GYLocal3.lean` proves Green–Tao Proposition 9.8 (`LinFormsCond` for `ν`) from
`BoxAvgGood` and the numeric bundle `LocalConsts`, a list of inequalities involving
`Q`, `R`, `ε_box`, `εw`, `ε`, `ε_bad`.  This file shows that the bundle follows from *explicit*,
`m`- and `t`-free inequalities — the form in which it will be instantiated at the end
(`Q` large, `R` large, `ε_box`/`ε_bad` small): see `localConsts_of_bounds`.
-/

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace GYMaj
namespace Local

variable {m t p Q : ℕ}

/-- `p/Q ≥ 1` when `1 ≤ Q ≤ p`. -/
lemma one_le_div_of_le {p Q : ℕ} (hQ : 0 < Q) (hQp : Q ≤ p) : 1 ≤ p / Q := by
  rw [Nat.le_div_iff_mul_le hQ]
  simpa using hQp

/-- The volume bound in terms of the real quotient: `volBd p Q t ≤ (2 p / Q)^t` for `Q ≤ p`. -/
lemma volBd_le {p Q : ℕ} (hQ : 0 < Q) (hQp : Q ≤ p) (t : ℕ) :
    volBd p Q t ≤ (2 * ((p : ℝ) / Q)) ^ t := by
  rw [volBd]
  have hcast : (((p / Q + 1 : ℕ)) : ℝ) = ((p / Q : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast]
  have h2 : (1 : ℝ) ≤ ((p / Q : ℕ) : ℝ) := by
    exact_mod_cast one_le_div_of_le (p := p) hQ hQp
  have h3 : ((p / Q : ℕ) : ℝ) ≤ (p : ℝ) / Q := Nat.cast_div_le
  have h4 : ((p / Q : ℕ) : ℝ) + 1 ≤ 2 * ((p : ℝ) / Q) := by linarith
  exact pow_le_pow_left₀ (by positivity) h4 t

/-- The range bound `Δ = t · Amax · (p/Q + 1)` is at most `2 t Amax p/Q`. -/
lemma Deltaloc_le {p Q k t : ℕ} [NeZero Q] (hQp : Q ≤ p) :
    ((Deltaloc p Q k t : ℤ) : ℝ) ≤ 2 * (t : ℝ) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q) := by
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast NeZero.pos Q
  have hcast : (((p / Q + 1 : ℕ)) : ℝ) = ((p / Q : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have h2 : (1 : ℝ) ≤ ((p / Q : ℕ) : ℝ) := by
    exact_mod_cast one_le_div_of_le (p := p) (Q := Q) (NeZero.pos Q) hQp
  have h3 : ((p / Q : ℕ) : ℝ) ≤ (p : ℝ) / Q := Nat.cast_div_le
  have hD : ((Dloc p Q : ℤ) : ℝ) = ((p / Q : ℕ) : ℝ) + 1 := by
    rw [Dloc, Int.cast_add, Int.cast_one, Int.cast_natCast]
  have hDle : ((Dloc p Q : ℤ) : ℝ) ≤ 2 * ((p : ℝ) / Q) := by
    rw [hD]; linarith
  have hΔ : ((Deltaloc p Q k t : ℤ) : ℝ)
      = (t : ℝ) * (AmaxLoc k : ℝ) * ((Dloc p Q : ℤ) : ℝ) := by
    rw [Deltaloc]; push_cast; ring
  rw [hΔ]
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ (AmaxLoc k : ℝ) := Nat.cast_nonneg _
  calc (t : ℝ) * (AmaxLoc k : ℝ) * ((Dloc p Q : ℤ) : ℝ)
      ≤ (t : ℝ) * (AmaxLoc k : ℝ) * (2 * ((p : ℝ) / Q)) := by
        refine mul_le_mul_of_nonneg_left hDle ?_
        positivity
    _ = 2 * (t : ℝ) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q) := by ring

/-- The bad-box constant is at most `5 t Amax` when `Q ≤ p`. -/
lemma Kbad_le {p Q : ℕ} {Δ : ℤ} {Amax t : ℕ} [NeZero Q] (hQp : Q ≤ p)
    (hΔ : (Δ : ℝ) ≤ 2 * (t : ℝ) * (Amax : ℝ) * ((p : ℝ) / Q)) :
    Kbad p Q Δ Amax t ≤ 5 * t * (Amax : ℝ) := by
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast NeZero.pos Q
  have hp : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hQ (by exact_mod_cast hQp)
  have hQpR : (Q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hQp
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ (Amax : ℝ) := Nat.cast_nonneg _
  rw [Kbad]
  have h1 : 2 * (Δ : ℝ) + (t : ℝ) * (Amax : ℝ)
      ≤ 4 * (t : ℝ) * (Amax : ℝ) * ((p : ℝ) / Q) + (t : ℝ) * (Amax : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_left hΔ (by norm_num : (0:ℝ) ≤ 2)
    linarith [h2]
  have h1' : (2 * (Δ : ℝ) + (t : ℝ) * (Amax : ℝ)) * (Q : ℝ) / (p : ℝ)
      ≤ (4 * (t : ℝ) * (Amax : ℝ) * ((p : ℝ) / Q) + (t : ℝ) * (Amax : ℝ)) * (Q : ℝ) / (p : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (le_of_lt hQ)) (le_of_lt hp)
  have h2 : (4 * (t : ℝ) * (Amax : ℝ) * ((p : ℝ) / Q) + (t : ℝ) * (Amax : ℝ)) * (Q : ℝ) / (p : ℝ)
      = 4 * (t : ℝ) * (Amax : ℝ) + (t : ℝ) * (Amax : ℝ) * (Q : ℝ) / (p : ℝ) := by
    field_simp
  have h3 : (t : ℝ) * (Amax : ℝ) * (Q : ℝ) / (p : ℝ) ≤ (t : ℝ) * (Amax : ℝ) := by
    rw [div_le_iff₀ hp]
    exact mul_le_mul_of_nonneg_left hQpR (by positivity)
  linarith [h1', h2, h3]


/-- `Δ ≤ εw p` from the `t`-free inequality `6 k Amax ≤ εw Q`. -/
lemma Deltaloc_le_eps {p Q k t : ℕ} {εw : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p) (hεw : 0 < εw)
    (ht : t ≤ 3 * k) (hΔ1 : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) ≤ εw * (Q : ℝ)) :
    ((Deltaloc p Q k t : ℤ) : ℝ) ≤ εw * (p : ℝ) := by
  haveI : NeZero Q := NeZero.of_pos hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hpR : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hQpos (by exact_mod_cast hQp)
  have hΔle := Deltaloc_le (p := p) (Q := Q) (k := k) (t := t) hQp
  have ht3 : (t : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast ht
  have hA0 : (0 : ℝ) ≤ (AmaxLoc k : ℝ) := Nat.cast_nonneg _
  have hstep1 : 2 * (t : ℝ) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q)
      ≤ 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q) := by
    have hnn : (0 : ℝ) ≤ (AmaxLoc k : ℝ) * ((p : ℝ) / Q) := by positivity
    have := mul_le_mul_of_nonneg_right ht3 hnn
    nlinarith [this]
  have hstep2 : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q) ≤ εw * (p : ℝ) := by
    calc 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q)
        = (2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * (p : ℝ)) / (Q : ℝ) := by ring
      _ ≤ (εw * (Q : ℝ) * (p : ℝ)) / (Q : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hΔ1 (le_of_lt hpR)) (le_of_lt hQpos)
      _ = εw * (p : ℝ) := by field_simp
  linarith [hΔle, hstep1, hstep2]

/-- `Δ + 2 εw p < p` from the `t`-free inequality `6 k Amax < (1 - 2 εw) Q`. -/
lemma Deltaloc_add_lt {p Q k t : ℕ} {εw : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (ht : t ≤ 3 * k) (hΔ2 : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) < (1 - 2 * εw) * (Q : ℝ)) :
    ((Deltaloc p Q k t : ℤ) : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ) := by
  haveI : NeZero Q := NeZero.of_pos hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hpR : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hQpos (by exact_mod_cast hQp)
  have hΔle := Deltaloc_le (p := p) (Q := Q) (k := k) (t := t) hQp
  have ht3 : (t : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast ht
  have hstep1 : 2 * (t : ℝ) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q)
      ≤ 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q) := by
    have hnn : (0 : ℝ) ≤ (AmaxLoc k : ℝ) * ((p : ℝ) / Q) := by positivity
    have := mul_le_mul_of_nonneg_right ht3 hnn
    nlinarith [this]
  have hpq : (0 : ℝ) < (p : ℝ) / (Q : ℝ) := by positivity
  have hstep2 : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q) < (1 - 2 * εw) * (p : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hΔ2 hpq
    calc 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * ((p : ℝ) / Q)
        = (2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ)) * ((p : ℝ) / Q) := by ring
      _ < ((1 - 2 * εw) * (Q : ℝ)) * ((p : ℝ) / Q) := hmul
      _ = (1 - 2 * εw) * (p : ℝ) := by field_simp
  linarith [hΔle, hstep1, hstep2]

/-- **The bad-box count, evaluated.**  In terms of the real quotient `p/Q`,
`BadCnt · volBd ≤ 2 m (10 t Amax + 1) Amax 2^t p^t / Q`. -/
lemma BadCnt_mul_volBd_le {p Q k t m : ℕ} (hQ : 0 < Q) (hQp : Q ≤ p) (hm : 1 ≤ m)
    (ht : 1 ≤ t) (ht3 : t ≤ 3 * k) :
    (BadCnt p Q k t m : ℝ) * volBd p Q t
      ≤ 2 * (m : ℝ) * (10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ) * 2 ^ t
          * (p : ℝ) ^ t / (Q : ℝ) := by
  haveI : NeZero Q := NeZero.of_pos hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hpR : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hQpos (by exact_mod_cast hQp)
  have hKbad := Kbad_le (p := p) (Q := Q) (Δ := Deltaloc p Q k t) (Amax := AmaxLoc k)
    (t := t) hQp (Deltaloc_le (p := p) (Q := Q) (k := k) (t := t) hQp)
  have hceil : ⌈2 * Kbad p Q (Deltaloc p Q k t) (AmaxLoc k) t⌉₊ ≤ 10 * t * AmaxLoc k := by
    rw [Nat.ceil_le]
    push_cast
    linarith
  have hnat : BadCnt p Q k t m
      ≤ 2 * m * (Q ^ (t - 1) * ((10 * t * AmaxLoc k + 1) * AmaxLoc k)) := by
    rw [BadCnt]
    refine Nat.mul_le_mul_left (2 * m) ?_
    exact Nat.mul_le_mul_left (Q ^ (t - 1))
      (Nat.mul_le_mul_right (AmaxLoc k) (Nat.add_le_add_right hceil 1))
  have hstep : (BadCnt p Q k t m : ℝ)
      ≤ 2 * (m : ℝ) * ((Q : ℝ) ^ (t - 1)
          * ((10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ))) := by
    exact_mod_cast hnat
  have hvol := volBd_le (p := p) (Q := Q) hQ hQp t
  have h1 : (BadCnt p Q k t m : ℝ) * volBd p Q t
      ≤ (2 * (m : ℝ) * ((Q : ℝ) ^ (t - 1)
          * ((10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ))))
        * (2 * ((p : ℝ) / Q)) ^ t := by
    calc (BadCnt p Q k t m : ℝ) * volBd p Q t
        ≤ (2 * (m : ℝ) * ((Q : ℝ) ^ (t - 1)
            * ((10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ)))) * volBd p Q t :=
          mul_le_mul_of_nonneg_right hstep (by rw [volBd]; positivity)
      _ ≤ (2 * (m : ℝ) * ((Q : ℝ) ^ (t - 1)
            * ((10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ))))
            * (2 * ((p : ℝ) / Q)) ^ t :=
          mul_le_mul_of_nonneg_left hvol (by positivity)
  refine le_trans h1 (le_of_eq ?_)
  rw [mul_pow, div_pow]
  have htsplit : t = (t - 1) + 1 := by omega
  have hQpow : (Q : ℝ) ^ t = (Q : ℝ) ^ (t - 1) * (Q : ℝ) := by
    conv_lhs => rw [htsplit]
    rw [pow_add, pow_one]
  rw [hQpow]
  field_simp


/-- **Sufficient conditions for the numeric bundle `LocalConsts`.**  Everything is `m`- and
`t`-free: `Q` is large, `R` is large, `ε_box` and `ε_bad` are small. -/
theorem localConsts_of_bounds {p k R W Q : ℕ} {ε_box εw ε εbad : ℝ}
    (hQ0 : 1 ≤ Q) (hQp : Q ≤ p) (hW : 0 < W) (hR1 : 1 ≤ R) (hR : 1 < R)
    (hε0 : 0 ≤ ε_box) (hε1 : ε_box ≤ 1) (hεw : 0 < εw) (hεw2 : 2 * εw < 1)
    (hεbad0 : 0 ≤ εbad) (hε : 0 < ε)
    (hsideQR : (R : ℤ) ^ (10 * k * 2 ^ (k - 1)) ≤ (p / Q : ℕ))
    (hΔ1 : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) ≤ εw * (Q : ℝ))
    (hΔ2 : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) < (1 - 2 * εw) * (Q : ℝ))
    (hsp1 : ε_box * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * 2 ^ (k * 2 ^ (k - 1)) ≤ ε / 3)
    (hsp2 : ε_box * ((k * 2 ^ (k - 1) : ℕ) : ℝ) ≤ ε / 3)
    (hsp3 : (3 : ℝ) ^ (k * 2 ^ (k - 1)) * εbad ≤ ε / 3)
    (hbadQ : 2 * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1)
              * (AmaxLoc k : ℝ) * 2 ^ (3 * k) ≤ εbad * (Q : ℝ)) :
    LocalConsts p k R W Q ε_box εw ε εbad := by
  have hQpos : 0 < Q := by omega
  refine ⟨hQpos, hQp, hW, hR1, hR, hε0, hε1, hεw, hsideQR, hεbad0, hε, ?_⟩
  intro m hm1 hmM t ht1 ht2
  haveI : NeZero Q := NeZero.of_pos hQpos
  have ht3k : t ≤ 3 * k := by omega
  have hA0 : (0 : ℝ) ≤ (AmaxLoc k : ℝ) := Nat.cast_nonneg _
  refine ⟨Deltaloc_le_eps hQpos hQp hεw ht3k hΔ1, Deltaloc_add_lt hQpos hQp ht3k hΔ2,
    ?_, ?_, ?_, ?_⟩
  · -- ε_box · m · 2^m ≤ ε/3
    have hmM' : (m : ℝ) ≤ ((k * 2 ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hmM
    have h2m : (2 : ℝ) ^ m ≤ 2 ^ (k * 2 ^ (k - 1)) :=
      pow_le_pow_right₀ (by norm_num) hmM
    calc ε_box * (m : ℝ) * 2 ^ m
        ≤ ε_box * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * 2 ^ (k * 2 ^ (k - 1)) := by
          gcongr
      _ ≤ ε / 3 := hsp1
  · -- ε_box · m ≤ ε/3
    have hmM' : (m : ℝ) ≤ ((k * 2 ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hmM
    calc ε_box * (m : ℝ) ≤ ε_box * ((k * 2 ^ (k - 1) : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hmM' hε0
      _ ≤ ε / 3 := hsp2
  · -- 3^m εbad ≤ ε/3
    have h3m : (3 : ℝ) ^ m ≤ 3 ^ (k * 2 ^ (k - 1)) :=
      pow_le_pow_right₀ (by norm_num) hmM
    calc (3 : ℝ) ^ m * εbad ≤ 3 ^ (k * 2 ^ (k - 1)) * εbad :=
          mul_le_mul_of_nonneg_right h3m hεbad0
      _ ≤ ε / 3 := hsp3
  · -- the bad-box count
    have hQposR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
    have hbad := BadCnt_mul_volBd_le (p := p) (Q := Q) (k := k) (t := t) (m := m)
      hQpos hQp hm1 ht1 ht3k
    have htR : (t : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast ht3k
    have hmMR : (m : ℝ) ≤ ((k * 2 ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hmM
    have hpow : (2 : ℝ) ^ t ≤ 2 ^ (3 * k) := pow_le_pow_right₀ (by norm_num) ht3k
    have hstep2 : 2 * (m : ℝ) * (10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ) * 2 ^ t
        ≤ εbad * (Q : ℝ) := by
      have hmono : 2 * (m : ℝ) * (10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ) * 2 ^ t
          ≤ 2 * ((k * 2 ^ (k - 1) : ℕ) : ℝ)
              * (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ) * 2 ^ (3 * k) := by
        gcongr
      linarith [hmono, hbadQ]

    have hstep3 : 2 * (m : ℝ) * (10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ) * 2 ^ t
          * (p : ℝ) ^ t / (Q : ℝ) ≤ εbad * (p : ℝ) ^ t := by
      rw [div_le_iff₀ hQposR]
      have hpt : (0 : ℝ) ≤ (p : ℝ) ^ t := by positivity
      calc 2 * (m : ℝ) * (10 * (t : ℝ) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ) * 2 ^ t
            * (p : ℝ) ^ t
          ≤ (εbad * (Q : ℝ)) * (p : ℝ) ^ t := mul_le_mul_of_nonneg_right hstep2 hpt
        _ = εbad * (p : ℝ) ^ t * (Q : ℝ) := by ring
    linarith [hbad, hstep3]


/-- **Green–Tao Proposition 9.8, final form.**  The Goldston–Yıldırım measurement `ν` satisfies
the linear forms condition with the parameters of `KPseudorandom`, from Green–Tao's box-average
asymptotic `BoxAvgGood` and explicit, `m`- and `t`-free numeric conditions on `p, R, W, Q` and the
small parameters. -/
theorem linFormsCond_nuGT_of_bounds {p : ℕ} [Fact p.Prime] {k R W Q : ℕ}
    {ε_box εw ε εbad : ℝ}
    (hk : k.factorial < p) (hbox : BoxAvgGood k R W ε_box)
    (hQ0 : 1 ≤ Q) (hQp : Q ≤ p) (hW : 0 < W) (hR1 : 1 ≤ R) (hR : 1 < R)
    (hε0 : 0 ≤ ε_box) (hε1 : ε_box ≤ 1) (hεw : 0 < εw) (hεw2 : 2 * εw < 1)
    (hεbad0 : 0 ≤ εbad) (hε : 0 < ε)
    (hsideQR : (R : ℤ) ^ (10 * k * 2 ^ (k - 1)) ≤ (p / Q : ℕ))
    (hΔ1 : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) ≤ εw * (Q : ℝ))
    (hΔ2 : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) < (1 - 2 * εw) * (Q : ℝ))
    (hsp1 : ε_box * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * 2 ^ (k * 2 ^ (k - 1)) ≤ ε / 3)
    (hsp2 : ε_box * ((k * 2 ^ (k - 1) : ℕ) : ℝ) ≤ ε / 3)
    (hsp3 : (3 : ℝ) ^ (k * 2 ^ (k - 1)) * εbad ≤ ε / 3)
    (hbadQ : 2 * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1)
              * (AmaxLoc k : ℝ) * 2 ^ (3 * k) ≤ εbad * (Q : ℝ)) :
    Commons.NumberTheory.Sieve.LinFormsCond p (nuGT R W p εw) (k * 2 ^ (k - 1)) (3 * k - 4) k ε :=
  linFormsCond_nuGT (p := p) (k := k) (R := R) (W := W) (Q := Q) (ε_box := ε_box)
    (εw := εw) (ε := ε) (εbad := εbad) hk hbox
    (localConsts_of_bounds hQ0 hQp hW hR1 hR hε0 hε1 hεw hεw2 hεbad0 hε hsideQR hΔ1 hΔ2
      hsp1 hsp2 hsp3 hbadQ)

end Local
end GYMaj
