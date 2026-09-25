import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Work.NumberTheory.Chebyshev

open Commons.NumberTheory.Chebyshev
open Commons.NumberTheory.Chebyshev.ThetaBracket

/-!
# The certified Chebyshev deficit bound `n - (21/10)√n ≤ θ n` on `[430, 14000]`

`θ` jumps exactly at the primes, so on a prime gap `(a, b)` the function `t ↦ t - θ t` is
`t ↦ t - θ a`, increasing in `t`; a comparison with `t ↦ (21/10)√t` (whose slope `21/(20√t)`
is `< 1` on the range) shows that the quantity `t - (21/10)√t - θ t` is also increasing on the
gap, so it suffices to check the right endpoint `t = b - 1`.

The certificate `CL` of `theta_bracket_finite_range` carries, at each prime `b`, the integer
`b.2 = Σ_{q < b} ⌊10^9 log q⌋ ≤ 10^9 θ (b-1)`.  The check

`((b-1) * 10^9 - b.2)^2 ≤ 441 * (b-1) * 10^16`

is exactly `(b-1) - b.2/10^9 ≤ (21/10)√(b-1)`, i.e. the deficit bound at the right endpoint of the
gap ending at `b`.  It is verified by `decide` over the whole table; the sharp constant on the
range is about `2.029`, so `21/10` has comfortable slack.
-/

/-- One prime gap of `CL` as a decidable `Bool`: with `pr` a pair of consecutive table entries
`(a, b)`, it asks that `(b - 1) - (10^{-9} b.2) ≤ (21/10)√(b-1)`, written in integer form after
clearing denominators. -/
def gapCheck21 (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (pr.2.2 ≤ (pr.2.1 - 1) * 10 ^ 9) &&
    decide (((pr.2.1 - 1) * 10 ^ 9 - pr.2.2) ^ 2 ≤ 441 * (pr.2.1 - 1) * 10 ^ 16)

theorem gapCheck21_all : (CL.zip CL.tail).all gapCheck21 = true := by decide

lemma gapCheck21_spec (pr : (ℕ × ℕ) × (ℕ × ℕ)) (h : pr ∈ CL.zip CL.tail) :
    gapCheck21 pr = true := List.all_eq_true.mp gapCheck21_all pr h

/-- The real content of one gap certificate. -/
lemma gap_deficit_bound21 (pr : (ℕ × ℕ) × (ℕ × ℕ)) (h : pr ∈ CL.zip CL.tail)
    (hb : 1 ≤ pr.2.1) :
    (pr.2.1 : ℝ) - 1 - (pr.2.2 : ℝ) / 10 ^ 9
      ≤ (21 / 10) * Real.sqrt ((pr.2.1 : ℝ) - 1) := by
  have hchk := gapCheck21_spec pr h
  rw [gapCheck21, Bool.and_eq_true] at hchk
  obtain ⟨hg1, hg2⟩ := hchk
  simp only [decide_eq_true_eq] at hg1 hg2
  have hDc : ((((pr.2.1 - 1) * 10 ^ 9 - pr.2.2 : ℕ)) : ℝ)
      = ((pr.2.1 : ℝ) - 1) * 10 ^ 9 - (pr.2.2 : ℝ) := by
    rw [Nat.cast_sub hg1, Nat.cast_mul, Nat.cast_sub hb]
    push_cast
    ring
  have hD2 : ((((pr.2.1 - 1) * 10 ^ 9 - pr.2.2 : ℕ)) : ℝ) ^ 2
      ≤ (21 * 10 ^ 8) ^ 2 * ((pr.2.1 : ℝ) - 1) := by
    have h0 : ((((pr.2.1 - 1) * 10 ^ 9 - pr.2.2 : ℕ)) : ℝ) ^ 2
        ≤ ((441 * (pr.2.1 - 1) * 10 ^ 16 : ℕ) : ℝ) := by
      exact_mod_cast hg2
    have h1 : ((441 * (pr.2.1 - 1) * 10 ^ 16 : ℕ) : ℝ)
        = (21 * 10 ^ 8) ^ 2 * ((pr.2.1 : ℝ) - 1) := by
      rw [show ((441 * (pr.2.1 - 1) * 10 ^ 16 : ℕ) : ℝ)
            = 441 * ((pr.2.1 - 1 : ℕ) : ℝ) * 10 ^ 16 by push_cast; ring]
      rw [Nat.cast_sub hb]
      push_cast
      ring
    rw [h1] at h0
    exact h0
  have hDle : ((((pr.2.1 - 1) * 10 ^ 9 - pr.2.2 : ℕ)) : ℝ)
      ≤ 21 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1) := by
    have hsqrt : Real.sqrt ((21 * 10 ^ 8) ^ 2 * ((pr.2.1 : ℝ) - 1))
        = 21 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (21 * 10 ^ 8) ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 21 * 10 ^ 8)]
    calc ((((pr.2.1 - 1) * 10 ^ 9 - pr.2.2 : ℕ)) : ℝ)
        ≤ Real.sqrt ((21 * 10 ^ 8) ^ 2 * ((pr.2.1 : ℝ) - 1)) :=
          Real.le_sqrt_of_sq_le hD2
      _ = 21 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1) := hsqrt
  have hfin : (pr.2.1 : ℝ) - 1 - (pr.2.2 : ℝ) / 10 ^ 9
      = ((((pr.2.1 - 1) * 10 ^ 9 - pr.2.2 : ℕ)) : ℝ) / 10 ^ 9 := by
    rw [hDc]
    ring
  rw [hfin, div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 9)]
  have hstep : (21 / 10 : ℝ) * Real.sqrt ((pr.2.1 : ℝ) - 1) * 10 ^ 9
      = 21 * 10 ^ 8 * Real.sqrt ((pr.2.1 : ℝ) - 1) := by ring
  rw [hstep]
  exact hDle

/-! ## Monotonicity of `t - (21/10)√t` on `[400, ∞)` -/

lemma deficit_mono {s t : ℝ} (hs : 400 ≤ s) (hst : s ≤ t) :
    s - (21 / 10) * Real.sqrt s ≤ t - (21 / 10) * Real.sqrt t := by
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hst' : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hst
  have hdiff : 0 ≤ Real.sqrt t - Real.sqrt s := by linarith
  have hsum : (21 / 10 : ℝ) ≤ Real.sqrt t + Real.sqrt s := by
    have h20 : (20 : ℝ) ≤ Real.sqrt s := by
      have h : Real.sqrt (400 : ℝ) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
      rwa [show Real.sqrt (400 : ℝ) = 20 by
        rw [show (400 : ℝ) = 20 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 20)] at h
    have ht : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    linarith
  have hprod : (Real.sqrt t + Real.sqrt s) * (Real.sqrt t - Real.sqrt s) = t - s := by
    have h1 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have h2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
    nlinarith [h1, h2]
  have hkey : (21 / 10 : ℝ) * (Real.sqrt t - Real.sqrt s) ≤ t - s := by
    have := mul_le_mul_of_nonneg_right hsum hdiff
    rwa [hprod] at this
  linarith [hkey]

/-! ## The target -/

theorem theta_deficit_upper (n : ℕ) (h1 : 430 ≤ n) (h2 : n ≤ 14000) :
    (n : ℝ) - (21 / 10) * Real.sqrt (n : ℝ) ≤ Chebyshev.theta (n : ℝ) := by
  have hn105 : n ≤ 10 ^ 5 := by omega
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
  have hth : (psumF ltOf CL n : ℝ) ≤ 10 ^ 9 * Chebyshev.theta (n : ℝ) := psumL_le_theta n hn105
  have hb2le : (b.2 : ℝ) ≤ 10 ^ 9 * Chebyshev.theta (n : ℝ) := by
    rw [hbspec]; exact hth
  have htheta_lb : (b.2 : ℝ) / 10 ^ 9 ≤ Chebyshev.theta (n : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 9)]
    linarith [hb2le]
  have hb1 : 1 ≤ b.1 := by omega
  have hgap := gap_deficit_bound21 (a, b) hmem hb1
  have hbm1 : (n : ℝ) ≤ (b.1 : ℝ) - 1 := by
    have h : n + 1 ≤ b.1 := by omega
    have h' : (n : ℝ) + 1 ≤ (b.1 : ℝ) := by exact_mod_cast h
    linarith
  have hn400 : (400 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 400 ≤ n)
  have hmono := deficit_mono hn400 hbm1
  calc (n : ℝ) - (21 / 10) * Real.sqrt (n : ℝ)
      ≤ ((b.1 : ℝ) - 1) - (21 / 10) * Real.sqrt ((b.1 : ℝ) - 1) := hmono
    _ ≤ (b.2 : ℝ) / 10 ^ 9 := by linarith [hgap]
    _ ≤ Chebyshev.theta (n : ℝ) := htheta_lb

end Work.NumberTheory.Chebyshev
