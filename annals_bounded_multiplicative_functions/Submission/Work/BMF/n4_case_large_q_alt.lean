import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.tuple_setup
import Submission.Work.BMF.primesIn_card_le_pi0
import Submission.Work.BMF.n4_torsion_bound
import Submission.Work.BMF.n4_case_large_q
import Submission.Work.BMF.n4_pow_congr_count
import Submission.Work.BMF.n4_num_diag
import Submission.Work.BMF.n4_num_sqrt_bound
import Submission.Work.BMF.n4_num_window_bound
import Submission.Work.BMF.n4_omega_rpow
import Submission.Work.BMF.n4_omega_sqrt_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N4, Case A (`q ≥ C (log P)^{ℓ+3}`), with proved sub-lemmas

Same statement and proof as `Submission.Work.BMF.n4_case_large_q`, but using the proved
`n4_pow_congr_count`, `n4_num_diag` and `n4_omega_rpow` in place of the (unproved)
`n4_pow_congr_card`, `n4_num_diag_bound` and `n4_omega_rpow_bound`; the auxiliary counting
lemmas (`n4_pair_card_le`, `n4_fiber_card_le`, ...) are imported from `n4_case_large_q`.
-/

namespace Work.BMF

open Finset Real

/-- **N4, the elementary case: large `q`.**  Say `π₀(P) = P/log P`.  If `q` is at least a
sufficiently large constant times `(log P)^{ℓ+3}`, then the number of nearby pairs of
`ℓ`-tuples of primes in `[P, 2P]` not dividing `q` whose products are congruent modulo `q`
after raising to the `m`-th power is `≤ C C₀ π₀(P)^{2ℓ}/N · (1/log N)`.

Route (MRT Lemma 2.6, "count integers instead of products"), for a fixed `v₁` with product `A`:
each admissible tuple `v₂` has product `B`, and at most `(ℓ+1)^ℓ` tuples give the same `B`
(`fiber_card_le`), so `#v₂ ≤ (ℓ+1)^ℓ * #{B : ℕ | |B - A| ≤ C₀P^ℓ/N ∧ B^m ≡ A^m [MOD q]}`
(`n4_pair_card_le`). The integers `B` in a window of length `2C₀P^ℓ/N` with `B^m ≡ A^m (mod q)`
lie in at most `r_m = #(m-torsion of (ZMod q)ˣ)` residue classes mod `q`, so number at most
`r_m (2C₀P^ℓ/(Nq) + 1)` (`n4_pow_congr_count`), and `#tup ≤ (C π₀(P))^ℓ`
(`primesIn_card_le_pi0`).

Case analysis.  (i) If `q > (2P)^{ℓm}` then `A^m, B^m < q` forces `A = B`, and `case_diagonal`
gives `#pairs ≤ #tup·(ℓ+1)^ℓ`, which is `≤ C C₀ π₀(P)^{2ℓ}/(N log N)` (`n4_num_diag`).
(ii) If `q ≤ (2P)^{ℓm}`: the `2C₀P^ℓ/(Nq)` part is estimated with the sub-polynomial bound
`r_m ≤ q^{1/(2ℓ)}` for `q ≥ q₀(ℓ,m)` (`n4_omega_rpow`) and `n4_num_window_bound`, and the
`+1` part with `r_m ≤ P^{1/2}` (`n4_omega_sqrt_bound`) and `n4_num_sqrt_bound`.
The case `ℓ = 1` is vacuous (`N ≤ P^0 = 1` contradicts `3 ≤ N`). -/
theorem n4_case_large_q_alt (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (P N C₀ : ℝ) (q : ℕ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
      1 / Real.log P ≤ C₀ → 1 ≤ q → C * Real.log P ^ (ℓ + 3) ≤ q →
      ((((tup P q ℓ) ×ˢ (tup P q ℓ)).filter
        (fun v ↦ |((tprod v.2 : ℕ) : ℝ) - ((tprod v.1 : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N ∧
          (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q])).card : ℝ)
        ≤ C * C₀ * pi0 P ^ (2 * ℓ) / N * (1 / Real.log N) := by
  obtain ⟨C₁, P₁, hC₁pos, hC₁bd⟩ := primesIn_card_le_pi0
  by_cases hℓ1 : ℓ = 1
  · refine ⟨1, 3, one_pos, ?_⟩
    intro P N C₀ q hP hN hNP hC₀ hq1 hq
    exfalso
    subst hℓ1
    rw [pow_zero] at hNP
    linarith
  · have hℓ2 : 2 ≤ ℓ := by omega
    obtain ⟨Cd, hCd⟩ := n4_num_diag ℓ hℓ2 C₁ 1 hC₁pos one_pos
    obtain ⟨Cv, hCv⟩ := n4_num_sqrt_bound ℓ hℓ2 C₁ (1/2) hC₁pos (by norm_num)
    obtain ⟨Cw, hCw⟩ := n4_num_window_bound ℓ hℓ2 C₁ (1/2) hC₁pos (by norm_num)
    obtain ⟨q₀, hq₀⟩ := n4_omega_rpow ℓ m hℓ hm
    obtain ⟨Cω, hCω⟩ := n4_omega_sqrt_bound ℓ m hℓ hm
    refine ⟨4, max ((2:ℝ)^ℓ + 1) (max 3 (max P₁ (max Cd (max Cv (max Cw (max Cω
      (Real.exp ((q₀:ℝ)+1)))))))), by norm_num, ?_⟩
    intro P N C₀ q hP hN hNP hC₀ hq1 hq
    have hP0 := hP
    rw [max_le_iff] at hP0
    obtain ⟨h2l, hP0⟩ := hP0
    rw [max_le_iff] at hP0
    obtain ⟨h3, hP0⟩ := hP0
    rw [max_le_iff] at hP0
    obtain ⟨hP1, hP0⟩ := hP0
    rw [max_le_iff] at hP0
    obtain ⟨hCdP, hP0⟩ := hP0
    rw [max_le_iff] at hP0
    obtain ⟨hCvP, hP0⟩ := hP0
    rw [max_le_iff] at hP0
    obtain ⟨hCwP, hP0⟩ := hP0
    rw [max_le_iff] at hP0
    obtain ⟨hCωP, hq0P⟩ := hP0
    have hP1' : 1 ≤ P := by linarith
    have h2l' : (2:ℝ)^ℓ ≤ P := by linarith
    have hPpos : 0 < P := by linarith
    have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show (0:ℕ) < q by omega)
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
    have hC₀pos : 0 < C₀ := lt_of_lt_of_le (one_div_pos.mpr hlogP) hC₀
    have hpi0 : 0 < pi0 P := by rw [pi0]; positivity
    have hZnn : 0 ≤ C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) := by
      apply mul_nonneg
      · apply div_nonneg
        · exact mul_nonneg hC₀pos.le (pow_nonneg hpi0.le _)
        · linarith
      · positivity
    have htup : ((tup P q ℓ).card : ℝ) ≤ (C₁ * pi0 P)^ℓ := by
      have h1 : (tup P q ℓ).card ≤ ((primesIn P (2*P)).card)^ℓ := card_tup_le
      have h2 : ((primesIn P (2*P)).card : ℝ) ≤ C₁ * pi0 P := hC₁bd P hP1
      calc ((tup P q ℓ).card : ℝ) ≤ (((primesIn P (2*P)).card)^ℓ : ℕ) := by exact_mod_cast h1
        _ = ((primesIn P (2*P)).card : ℝ)^ℓ := by push_cast; ring
        _ ≤ (C₁ * pi0 P)^ℓ := pow_le_pow_left₀ (by positivity) h2 ℓ
    have hgoal_form : 4 * (C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N)) =
        4 * C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) := by ring
    have hX4 : C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) ≤
        4 * (C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N)) := by nlinarith [hZnn]
    rw [← hgoal_form]
    by_cases hcase : (2*P)^(ℓ*m) < (q:ℝ)
    · -- Case (i): `q > (2P)^{ℓm}`, the `m`-th power congruence forces equal products.
      have hcd := case_diagonal (P := P) (N := N) (C₀ := C₀) (q := q) hℓ hm hP1' h2l' hcase
      have hcd'' : ((((tup P q ℓ) ×ˢ (tup P q ℓ)).filter (fun v ↦
          |((tprod v.2 : ℕ) : ℝ) - ((tprod v.1 : ℕ) : ℝ)| ≤ C₀ * P^ℓ/N ∧
          (tprod v.2)^m ≡ (tprod v.1)^m [MOD q])).card : ℝ) ≤
          (((tup P q ℓ).card * (ℓ+1)^ℓ : ℕ) : ℝ) := by exact_mod_cast hcd
      have hpowcast : (((tup P q ℓ).card * (ℓ+1)^ℓ : ℕ) : ℝ) =
          ((tup P q ℓ).card : ℝ) * (((ℓ+1:ℕ):ℝ)^ℓ) := by push_cast; ring
      rw [hpowcast] at hcd''
      have hstep : ((tup P q ℓ).card : ℝ) * (((ℓ+1:ℕ):ℝ)^ℓ) ≤
          1 * C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) :=
        le_trans (mul_le_mul_of_nonneg_right htup (by positivity))
          (hCd P N C₀ hCdP hN hNP hC₀)
      have h1X : (1:ℝ) * C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) =
          C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) := by ring
      rw [h1X] at hstep
      linarith [hcd'', hstep, hX4]
    · -- Case (ii): `q ≤ (2P)^{ℓm}`, count the integers in the window.
      have hcase' : (q:ℝ) ≤ (2*P)^(ℓ*m) := not_lt.mp hcase
      haveI : NeZero q := ⟨by omega⟩
      have hlogP_big : (q₀ : ℝ) + 1 ≤ Real.log P := by
        have h := Real.log_le_log (Real.exp_pos _) hq0P
        rwa [Real.log_exp] at h
      have hlogPge1 : 1 ≤ Real.log P := by
        have h0 : (0:ℝ) ≤ (q₀ : ℝ) := Nat.cast_nonneg q₀
        linarith
      have hlogpow_ge : Real.log P ≤ Real.log P ^ (ℓ+3) := by
        have h := pow_le_pow_right₀ hlogPge1 (show 1 ≤ ℓ + 3 by omega)
        simpa using h
      have hlogpow_le_q : Real.log P ^ (ℓ+3) ≤ (q:ℝ) := by
        have hnn : 0 ≤ Real.log P ^ (ℓ+3) := pow_nonneg hlogP.le _
        linarith [hq, hnn]
      have hqq : q₀ ≤ q := by
        have h1 : ((q₀:ℕ):ℝ) ≤ (q:ℝ) := by linarith [hlogP_big, hlogpow_ge, hlogpow_le_q]
        exact_mod_cast h1
      set R : ℝ := (((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ^m = 1)).card : ℝ)
        with hRdef
      have hr1 : R ≤ (((2*m:ℕ):ℝ)^q.primeFactors.card) := by
        rw [hRdef]; exact n4_torsion_bound q m hm
      have hqr : R ≤ (q:ℝ)^((1:ℝ)/(2*(ℓ:ℝ))) := le_trans hr1 (hq₀ q hqq)
      have hqs : R ≤ P^((1:ℝ)/2) := le_trans hr1 (hCω P hCωP q hcase')
      have hW0 : 0 ≤ C₀ * P^ℓ / N := by
        apply div_nonneg
        · exact mul_nonneg hC₀pos.le (pow_nonneg hPpos.le _)
        · linarith
      have hcard := n4_pair_card_le (P := P) (W := C₀ * P^ℓ/N) (q := q) hℓ hq1 hP1' h2l' hW0
        (fun A hA S h1 h2 => n4_pow_congr_count hq1 hm hA hW0 h1 h2)
      rw [← hRdef] at hcard
      have hfac : 0 ≤ ((((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (R*(2*(C₀*P^ℓ/N)/(q:ℝ)+1))) := by
        apply mul_nonneg
        · positivity
        · apply mul_nonneg
          · exact Nat.cast_nonneg _
          · have : 0 ≤ 2*(C₀*P^ℓ/N)/(q:ℝ) := by
              apply div_nonneg
              · linarith [hW0]
              · linarith [hqpos]
            linarith
      have hcard2 : ((((tup P q ℓ) ×ˢ (tup P q ℓ)).filter
          (fun v ↦ n4_pairCond (C₀ * P^ℓ/N) q m v)).card : ℝ) ≤
          (C₁*pi0 P)^ℓ * ((((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (R*(2*(C₀*P^ℓ/N)/(q:ℝ)+1))) :=
        le_trans hcard (mul_le_mul_of_nonneg_right htup hfac)
      have hsplit : (C₁*pi0 P)^ℓ * ((((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (R*(2*(C₀*P^ℓ/N)/(q:ℝ)+1)))
          = (C₁*pi0 P)^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * R * (2*C₀*P^ℓ/(N*(q:ℝ)))
            + (C₁*pi0 P)^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * R := by ring
      have hhalf : (1/2 : ℝ) * C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) ≤
          C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) := by
        have h1 : (1/2 : ℝ) * C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N)
            = (1/2) * (C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N)) := by ring
        rw [h1]; nlinarith [hZnn]
      have hA' : (C₁*pi0 P)^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * R * (2*C₀*P^ℓ/(N*(q:ℝ))) ≤
          C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) :=
        le_trans (hCw P N C₀ R q hCwP hN hNP hC₀ hq1 hlogpow_le_q hqr) hhalf
      have hB' : (C₁*pi0 P)^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * R ≤
          C₀ * pi0 P^(2*ℓ)/N*(1/Real.log N) :=
        le_trans (hCv P N C₀ R hCvP hN hNP hC₀ hqs) hhalf
      rw [hsplit] at hcard2
      linarith [hcard2, hA', hB', hX4]


end Work.BMF
