import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# The certified deficit bound `t - θ t ≤ 2.3 √t` on `[173, 10^5]`

`θ` (Chebyshev's first function) is a step function that jumps exactly at the primes.  Between two
consecutive primes `a < b` the deficit `t ↦ t - θ t` is *maximal just before* `b`, where it takes the
value `b - θ a`.  The certificate below verifies, for every consecutive pair of the list `CL`
(every prime `≤ 100003`, each carrying the rational lower bound `Σ_{q ≤ p} ⌊10^9 log q⌋` for
`10^9 θ p`), that

`b - θ a ≤ 2.3 √(b-1)`.

Since `t ↦ 2.3 √t - t` is antitone on `[173, ∞)` (its "slope" `2.3/(2√t)` is `< 1`), this single
finite check controls the whole interval, and the extra factor `√(b/n) ≥ 1` together with the
integrality of `n` absorbs the half-open nature of the step.
-/

namespace Work.RHContract.A.regionII

open Commons.NumberTheory.Chebyshev
open Commons.NumberTheory.Chebyshev.ThetaBracket

/-! ## The finite gap certificate -/

/-- One prime gap of `CL` as a decidable `Bool`.  `pr.1` is the lower end of the gap (a prime `a`),
`pr.2` the upper end (the next prime `b`); the check asks that `b - (10^{-9} θ a) ≤ 2.3 √(b-1)`,
written in integer form after clearing denominators.  Gaps with `b < 174` are ignored (they are
only the pairs `(2,3),…,(167,173)`). -/
def gapCheck (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (pr.2.1 < 174) ||
    (decide (pr.2.2 ≤ pr.2.1 * 10 ^ 9) &&
      decide ((pr.2.1 * 10 ^ 9 - pr.2.2) ^ 2 ≤ 529 * (pr.2.1 - 1) * 10 ^ 16))

theorem gapCheck_all : (CL.zip CL.tail).all gapCheck = true := by decide

lemma gapCheck_spec (pr : (ℕ × ℕ) × (ℕ × ℕ)) (h : pr ∈ CL.zip CL.tail) :
    gapCheck pr = true := List.all_eq_true.mp gapCheck_all pr h

/-- The real content of one gap certificate. -/
lemma gap_deficit_bound (pr : (ℕ × ℕ) × (ℕ × ℕ)) (h : pr ∈ CL.zip CL.tail)
    (hb : 174 ≤ pr.2.1) :
    (pr.2.1 : ℝ) - (pr.2.2 : ℝ) / 10 ^ 9 ≤ 2.3 * Real.sqrt ((pr.2.1 : ℝ) - 1) := by
  have hchk := gapCheck_spec pr h
  rw [gapCheck, Bool.or_eq_true] at hchk
  rcases hchk with hbad | hgood
  · simp only [decide_eq_true_eq] at hbad
    omega
  · rw [Bool.and_eq_true] at hgood
    obtain ⟨hg1, hg2⟩ := hgood
    simp only [decide_eq_true_eq] at hg1 hg2
    have hA1 : (1 : ℝ) ≤ (pr.2.1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ pr.2.1)
    -- the integer quantity whose square is controlled
    have hDc : ((pr.2.1 * 10 ^ 9 - pr.2.2 : ℕ) : ℝ)
        = (pr.2.1 : ℝ) * 10 ^ 9 - (pr.2.2 : ℝ) := by
      rw [Nat.cast_sub hg1]; push_cast; ring
    have hD2 : ((pr.2.1 * 10 ^ 9 - pr.2.2 : ℕ) : ℝ) ^ 2
        ≤ (23 * 10 ^ 8) ^ 2 * ((pr.2.1 : ℝ) - 1) := by
      have h0 : ((pr.2.1 * 10 ^ 9 - pr.2.2 : ℕ) : ℝ) ^ 2
          ≤ ((529 * (pr.2.1 - 1) * 10 ^ 16 : ℕ) : ℝ) := by
        rw [← Nat.cast_pow]; exact_mod_cast hg2
      have h1 : ((529 * (pr.2.1 - 1) * 10 ^ 16 : ℕ) : ℝ)
          = (23 * 10 ^ 8) ^ 2 * ((pr.2.1 : ℝ) - 1) := by
        rw [show ((529 * (pr.2.1 - 1) * 10 ^ 16 : ℕ) : ℝ)
              = 529 * ((pr.2.1 - 1 : ℕ) : ℝ) * 10 ^ 16 by push_cast; ring]
        rw [Nat.cast_sub (by omega : 1 ≤ pr.2.1)]
        push_cast
        ring
      rw [h1] at h0
      exact h0
    have hDle : ((pr.2.1 * 10 ^ 9 - pr.2.2 : ℕ) : ℝ)
        ≤ 23 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1) := by
      have hsqrt : Real.sqrt ((23 * 10 ^ 8) ^ 2 * ((pr.2.1 : ℝ) - 1))
          = 23 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (23 * 10 ^ 8) ^ 2),
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 23 * 10 ^ 8)]
      calc ((pr.2.1 * 10 ^ 9 - pr.2.2 : ℕ) : ℝ)
          ≤ Real.sqrt ((23 * 10 ^ 8) ^ 2 * ((pr.2.1 : ℝ) - 1)) :=
            Real.le_sqrt_of_sq_le hD2
        _ = 23 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1) := hsqrt
    have hDle' : (pr.2.1 : ℝ) * 10 ^ 9 - (pr.2.2 : ℝ)
        ≤ 23 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1) := by
      rw [← hDc]; exact hDle
    have hdiv : ((pr.2.1 : ℝ) * 10 ^ 9 - (pr.2.2 : ℝ)) / 10 ^ 9
        ≤ (23 / 10 : ℝ) * Real.sqrt ((pr.2.1 : ℝ) - 1) := by
      have h10 : (0 : ℝ) ≤ 10 ^ 9 := by norm_num
      have hstep : (23 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1)) / 10 ^ 9
          = (23 / 10 : ℝ) * Real.sqrt ((pr.2.1 : ℝ) - 1) := by ring
      have hd := div_le_div_of_nonneg_right hDle' h10
      rwa [hstep] at hd
    have hfin : (pr.2.1 : ℝ) - (pr.2.2 : ℝ) / 10 ^ 9
        = ((pr.2.1 : ℝ) * 10 ^ 9 - (pr.2.2 : ℝ)) / 10 ^ 9 := by ring
    have h23 : (2.3 : ℝ) = 23 / 10 := by norm_num
    rw [h23]
    rw [hfin]
    exact hdiv

/-! ## Antitonicity of `t ↦ 2.3 √t - t` -/

lemma sqrt_antitone_aux {s t : ℝ} (hs : 173 ≤ s) (hst : s ≤ t) :
    (2.3 : ℝ) * Real.sqrt t - t ≤ 2.3 * Real.sqrt s - s := by
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hst' : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hst
  have hdiff : 0 ≤ Real.sqrt t - Real.sqrt s := by linarith
  have hsum : (2.3 : ℝ) ≤ Real.sqrt t + Real.sqrt s := by
    have h13 : (13 : ℝ) ≤ Real.sqrt 173 := by
      have h : Real.sqrt ((13 : ℝ) ^ 2) ≤ Real.sqrt 173 := Real.sqrt_le_sqrt (by norm_num)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 13)] at h
    have h173s : Real.sqrt 173 ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
    have htn : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    linarith
  have hsq : (Real.sqrt t - Real.sqrt s) * (Real.sqrt t + Real.sqrt s) = t - s := by
    have h1 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have h2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
    nlinarith [h1, h2]
  have hkey : (2.3 : ℝ) * (Real.sqrt t - Real.sqrt s)
      ≤ (Real.sqrt t + Real.sqrt s) * (Real.sqrt t - Real.sqrt s) :=
    mul_le_mul_of_nonneg_right hsum hdiff
  rw [mul_comm (Real.sqrt t + Real.sqrt s) (Real.sqrt t - Real.sqrt s), hsq] at hkey
  linarith

/-! ## The integer statement -/

lemma theta_int_deficit (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 10 ^ 5) :
    ((n : ℝ) + 1) - Chebyshev.theta (n : ℝ) ≤ 2.3 * Real.sqrt (n : ℝ) := by
  have hsent : sentCL ∈ CL := List.mem_append_right _ (by simp)
  have hlt : n < sentCL.1 := by rw [sentCL]; simp; omega
  have hex : ∃ e ∈ CL, n < e.1 := ⟨sentCL, hsent, hlt⟩
  have hhead : ∀ e, CL.head? = some e → e.1 ≤ n := by
    intro e he
    rw [CL_head] at he
    simp only [Option.some.injEq] at he
    subst he
    omega
  have hisSome : (bnd2 CL n).isSome = true := bnd2_isSome_of CL n hhead hex
  obtain ⟨⟨a, b⟩, hc⟩ := Option.isSome_iff_exists.mp hisSome
  obtain ⟨hmem, ha_le, hn_lt⟩ := bnd2_spec CL n hc
  have hbnd : ThetaFinite.bnd CL n = some b := bnd2_snd_eq_bnd CL n hc
  have hbspec : b.2 = (CL.head?.map Prod.snd).getD 0 + psumF ltOf CL n :=
    bnd_spec_gen ltOf CL n CL_chain hbnd
  rw [CL_head] at hbspec
  simp only [Option.map_some, Option.getD_some, Nat.zero_add] at hbspec
  -- `b` is the first entry of `CL` beyond `n`, so `b.2` bounds `10^9 θ n`.
  have hb174 : 174 ≤ b.1 := by omega
  have hgap := gap_deficit_bound (a, b) hmem hb174
  have hth : (psumF ltOf CL n : ℝ) ≤ 10 ^ 9 * Chebyshev.theta (n : ℝ) := psumL_le_theta n h2
  have hc0 : (b.2 : ℝ) / 10 ^ 9 ≤ Chebyshev.theta (n : ℝ) := by
    rw [hbspec, div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 9)]
    linarith [hth]
  have hle_interval : (n : ℝ) ≤ (b.1 : ℝ) - 1 := by
    have h : n + 1 ≤ b.1 := by omega
    have h' : ((n : ℕ) : ℝ) + 1 ≤ (b.1 : ℝ) := by exact_mod_cast h
    linarith
  have hanti := sqrt_antitone_aux (s := (n : ℝ)) (t := (b.1 : ℝ) - 1)
    (by exact_mod_cast h1) hle_interval
  have hnn : 0 ≤ (2.3 : ℝ) * Real.sqrt (n : ℝ) - ((n : ℝ) + 1) + (b.2 : ℝ) / 10 ^ 9 := by
    linarith [hanti, hgap]
  calc ((n : ℝ) + 1) - Chebyshev.theta (n : ℝ)
      ≤ ((n : ℝ) + 1) - (b.2 : ℝ) / 10 ^ 9 := by linarith [hc0]
    _ ≤ 2.3 * Real.sqrt (n : ℝ) := by linarith [hnn]

/-! ## The target -/

theorem theta_deficit_bound (t : ℝ) (h1 : 173 ≤ t) (h2 : t ≤ 100000) :
    t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hn173 : 173 ≤ ⌊t⌋₊ := Nat.le_floor h1
  have hn_le : ⌊t⌋₊ ≤ 10 ^ 5 := by
    have hnt : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
    have h : ((⌊t⌋₊ : ℕ) : ℝ) ≤ ((10 ^ 5 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have htheta : Chebyshev.theta t = Chebyshev.theta ((⌊t⌋₊ : ℕ) : ℝ) := by
    simp only [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  have hint := theta_int_deficit ⌊t⌋₊ hn173 hn_le
  have hfl : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hsle : Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.sqrt t := Real.sqrt_le_sqrt (Nat.floor_le ht0)
  calc t - Chebyshev.theta t
      = t - Chebyshev.theta ((⌊t⌋₊ : ℕ) : ℝ) := by rw [htheta]
    _ ≤ (((⌊t⌋₊ : ℕ) : ℝ) + 1) - Chebyshev.theta ((⌊t⌋₊ : ℕ) : ℝ) := by linarith
    _ ≤ 2.3 * Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ) := hint
    _ ≤ 2.3 * Real.sqrt t := mul_le_mul_of_nonneg_left hsle (by norm_num)

end Work.RHContract.A.regionII
