import Mathlib
import Submission.Work.LinnikBurgess.a1_sum_bound_guarded
import Submission.Work.LinnikBurgess.frame_step_defs
import Submission.Work.LinnikBurgess.frame_step_card_d_nohb
import Submission.Work.LinnikBurgess.frame_count_prov_defs

/-!
# The call site of `a1_sum_bound`: the frame count, and the `frameMod` bridge

`frame_count_prov` (Theorem F) fixes a pivot `a 0`, a second entry `a 1` and the whole second
triple `b`, counts the admissible third entries `a2`, and sums the weights
`wg m (a 0) (a 1) = √(gcd m |a 0 - a 1|)`.  At that call site:

* the anchoring hypothesis of `a1_sum_bound_guarded` holds automatically, because the pivot comes
  from `box3 H = [1,H]³` (`box3_anchor`), and
* the guard `a1 ≠ a0` holds automatically, because `condAB` contains `a 0 ≠ a 1`
  (`condAB_shift_ne`).

What is *not* automatic is the passage from the frame step `frame_step_card_d` — which confines the
third entry to `3^ω(d)·(H / frameMod d a0 a1 + 1)` classes — to the arithmetic-progression factor
`(H/d)·gcd(d, |a0-a1|) + 1` of `a1_sum_bound_guarded`.  That passage is the inequality
`frameMod_mul_gcd_ge`, whose real-valued form `frameMod_arith_prov` is exactly the statement of the
(until now unproved) `frameMod_arith` of `frameMod_arith.lean`.
-/

open Finset

namespace Work.LinnikBurgess

/-! ### The `frameMod` bridge -/

/-- Arithmetic core, the `p = 2` case of the bridge. -/
private lemma arith_t1 (e s ω : ℕ) (hω : 1 ≤ ω) : e ≤ max 0 (e - 1 - s) + min e s + ω := by omega

/-- Arithmetic core, the `p ≠ 2` case of the bridge. -/
private lemma arith_t0 (e s ω : ℕ) : e ≤ max 0 (e - s) + min e s + ω := by omega

private lemma padicValNat_self_prime {p : ℕ} (hp : Nat.Prime p) : padicValNat p p = 1 := by
  rw [← Nat.factorization_def p hp, Nat.Prime.factorization_self hp]

private lemma padicValNat_eq_factorization (n p : ℕ) (hp : Nat.Prime p) :
    padicValNat p n = n.factorization p := (Nat.factorization_def n hp).symm

private lemma padicValNat_two_eq_zero {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    padicValNat p 2 = 0 := by
  refine padicValNat.eq_zero_of_not_dvd ?_
  intro hdvd
  have h1 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 : 2 ≤ p := hp.two_le
  omega

/-- **The frame modulus is not too small.**  With
`frameMod d a0 a1 = ∏_{p ∣ d} p^(max 0 (v_p d - v_p 2 - v_p (a0-a1)))`,

`d ≤ frameMod d a0 a1 * gcd(d, |a0 - a1|) * 2^(d.primeFactors.card)`.

Proof: compare `p`-adic valuations.  For a prime `p ∣ d` put `e = v_p d`, `t = v_p 2`,
`s = v_p |a0-a1|`.  If `s + t < e` the first factor contributes exactly `e - s - t` at `p` and `gcd`
contributes `s`; if `s + t ≥ e` the first factor contributes `0`, `gcd` contributes `min e s ≥ e - t`
and `2^(ω d)` contributes `t` (which is `0` unless `p = 2`, when `ω d ≥ 1`).  Either way the
`p`-exponent of the right-hand side is at least `e`. -/
theorem frameMod_mul_gcd_ge {d a0 a1 : ℕ} (hd : 0 < d) :
    d ≤ frameMod d a0 a1 * Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) * 2 ^ d.primeFactors.card := by
  set N := (((a0 : ℤ) - (a1 : ℤ)).natAbs) with hN
  set G := Nat.gcd d N with hG
  set W := 2 ^ d.primeFactors.card with hW
  have hMpos : 0 < frameMod d a0 a1 := by
    rw [frameMod]
    exact Finset.prod_pos (fun p hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _)
  have hGpos : 0 < G := by rw [hG]; exact Nat.gcd_pos_of_pos_left N hd
  have hWpos : 0 < W := by rw [hW]; positivity
  have hXpos : 0 < frameMod d a0 a1 * G * W := by positivity
  refine Nat.le_of_dvd hXpos ?_
  refine (Nat.factorization_le_iff_dvd (ne_of_gt hd) (ne_of_gt hXpos)).mp ?_
  rw [Finsupp.le_def]
  intro p
  have hXfac : (frameMod d a0 a1 * G * W).factorization p
      = (frameMod d a0 a1).factorization p + G.factorization p + W.factorization p := by
    rw [Nat.factorization_mul (by positivity) (ne_of_gt hWpos),
      Nat.factorization_mul (ne_of_gt hMpos) (ne_of_gt hGpos)]
    simp [Finsupp.add_apply]
  rw [hXfac]
  by_cases hp : p ∈ d.primeFactors
  · obtain ⟨hpp, hpdvd, hdne⟩ := Nat.mem_primeFactors.mp hp
    have hMlb : max 0 (d.factorization p - padicValNat p 2 - padicValNat p N)
        ≤ (frameMod d a0 a1).factorization p := by
      refine (Nat.Prime.pow_dvd_iff_le_factorization hpp (ne_of_gt hMpos)).mp ?_
      rw [frameMod]
      exact Finset.dvd_prod_of_mem _ hp
    have hGlb : min (d.factorization p) (N.factorization p) ≤ G.factorization p := by
      by_cases hN0 : N = 0
      · have hz : N.factorization p = 0 := by simp [hN0, Nat.factorization_zero]
        rw [hz]
        simp
      · rw [hG, Nat.factorization_gcd (ne_of_gt hd) hN0]
        simp [Finsupp.inf_apply]
    have hWlb : (if p = 2 then d.primeFactors.card else 0) ≤ W.factorization p := by
      rcases eq_or_ne p 2 with rfl | hp2
      · rw [if_pos rfl, hW, Nat.factorization_pow]
        simp [Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num : Nat.Prime 2)]
      · rw [if_neg hp2]
        exact Nat.zero_le _
    rcases eq_or_ne p 2 with rfl | hp2
    · rw [padicValNat_self_prime (by norm_num : Nat.Prime 2),
        padicValNat_eq_factorization N 2 (by norm_num : Nat.Prime 2)] at hMlb
      rw [if_pos rfl] at hWlb
      have hω : 1 ≤ d.primeFactors.card := Finset.card_pos.mpr ⟨2, hp⟩
      have harith := arith_t1 (d.factorization 2) (N.factorization 2) d.primeFactors.card hω
      linarith
    · rw [padicValNat_two_eq_zero hpp hp2,
        padicValNat_eq_factorization N p hpp, Nat.sub_zero] at hMlb
      rw [if_neg hp2] at hWlb
      have harith := arith_t0 (d.factorization p) (N.factorization p) 0
      linarith
  · have hz : d.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_cases hpp : p.Prime
      · right; left
        intro hdvd
        exact hp (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, ne_of_gt hd⟩)
      · left; exact hpp
    rw [hz]
    exact Nat.zero_le _

/-- **`frameMod` bridge, real form** — the statement of `frameMod_arith` (whose proof was still
missing) as a corollary of `frameMod_mul_gcd_ge`:

`H / frameMod d a0 a1 + 1 ≤ H · gcd(d, |a0-a1|) · 2^ω(d) / d + 1`.

This is what turns the frame step `frame_step_card_d`, `#(frameStepSetD …) ≤ 3^ω(d)·(H/frameMod + 1)`,
into the arithmetic-progression factor `(H/d)·gcd(d,|a0-a1|) + 1` of `a1_sum_bound_guarded`. -/
theorem frameMod_arith_prov {d H a0 a1 : ℕ} (hd : 0 < d) (_h01 : a0 ≠ a1) :
    (H : ℝ) / (frameMod d a0 a1 : ℝ) + 1
      ≤ (H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
          * (2 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) + 1 := by
  have hcore := frameMod_mul_gcd_ge (a0 := a0) (a1 := a1) hd
  have hMpos : (0 : ℝ) < (frameMod d a0 a1 : ℝ) := by
    have h : 0 < frameMod d a0 a1 := by
      rw [frameMod]
      exact Finset.prod_pos (fun p hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _)
    exact_mod_cast h
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcoreR : (d : ℝ) ≤ (frameMod d a0 a1 : ℝ)
      * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
      * (2 : ℝ) ^ (d.primeFactors.card) := by
    exact_mod_cast hcore
  have hkey : (1 : ℝ) / (frameMod d a0 a1 : ℝ)
      ≤ ((Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) * (2 : ℝ) ^ (d.primeFactors.card))
          / (d : ℝ) := by
    rw [div_le_iff₀ hMpos, div_mul_eq_mul_div, le_div_iff₀ hdR]
    linarith [hcoreR]
  have hH : (0 : ℝ) ≤ (H : ℝ) := by positivity
  calc (H : ℝ) / (frameMod d a0 a1 : ℝ) + 1
      ≤ (H : ℝ) * (((Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
            * (2 : ℝ) ^ (d.primeFactors.card)) / (d : ℝ)) + 1 := by
        have := mul_le_mul_of_nonneg_left hkey hH
        rw [mul_one_div] at this
        linarith
    _ = (H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
          * (2 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) + 1 := by ring

/-! ### The call-site witnesses -/

/-- **The anchoring holds at the call site.**  In `frame_count_prov` the pivot is `a 0` with
`a ∈ box3 H = [1,H]³`, hence `1 ≤ a 0 ≤ H`: the hypothesis `ha0`/`ha0H` of
`a1_sum_bound_guarded` is automatic there. -/
theorem box3_anchor {H : ℕ} {a : Fin 3 → ℕ} (ha : a ∈ box3 H) : 1 ≤ a 0 ∧ a 0 ≤ H := by
  have h : a 0 ∈ Finset.Icc 1 H := by
    have h1 : a ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 H) := ha
    exact (Fintype.mem_piFinset.mp h1) 0
  exact Finset.mem_Icc.mp h

/-- **The guard holds at the call site.**  `condAB` contains `a 0 ≠ a 1`, so the index set
`(Icc 1 H).filter (· ≠ a 0)` of `a1_sum_bound_guarded` is exactly the range of the second entry
`a 1` under `condAB`. -/
theorem condAB_shift_ne {d g : ℕ} {a b : Fin 3 → ℕ} (h : condAB d g a b) : a 0 ≠ a 1 := h.2.1

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- **The `a1`-sum at the frame-count call site.**  Suppose the frame step confines the admissible
third entries to at most `3^ω(d)·(H / frameMod d a0 a1 + 1)` possibilities for every `a1 ≠ a0` —
which is exactly what `frame_step_card_d` gives, with `a 0 ≠ a 1` supplied by `condAB`
(`condAB_shift_ne`) and `a 1 ∉ b` by the case hypotheses.  Then the `a1`-sum of that count against
the weight `wg m a0 a1 = √(gcd m |a0-a1|)` is at most `6^ω(d)` times the arithmetic-progression
bound of `a1_sum_bound_guarded`.

The hypothesis `hstep` is taken as an assumption here so that this lemma stays independent of
`frame_step_card_d` (whose current proof still rests on `sorryAx`). -/
theorem frameStepSum_le {H m d a0 : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : Nat.Coprime m d)
    (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) (b : Fin 3 → ℕ)
    (hstep : ∀ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
      (frameStepSetD d H a0 a1 b).card
        ≤ 3 ^ d.primeFactors.card * (H / frameMod d a0 a1 + 1)) :
    (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
        ((frameStepSetD d H a0 a1 b).card : ℝ) * wg m a0 a1)
      ≤ (6 : ℝ) ^ (d.primeFactors.card)
          * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
              * ((m.divisors.card : ℝ))) := by
  have hpt : ∀ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
      ((frameStepSetD d H a0 a1 b).card : ℝ) * wg m a0 a1
        ≤ (6 : ℝ) ^ (d.primeFactors.card)
            * (((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1) * wg m a0 a1) := by
    intro a1 ha1
    have hne : a1 ≠ a0 := (Finset.mem_filter.mp ha1).2
    have h01 : a0 ≠ a1 := fun h => hne h.symm
    have hbrid := frameMod_arith_prov (a0 := a0) (a1 := a1) (H := H) hd h01
    have hcast : ((frameStepSetD d H a0 a1 b).card : ℝ)
        ≤ (3 : ℝ) ^ (d.primeFactors.card)
            * (((H / frameMod d a0 a1 : ℕ) : ℝ) + 1) := by
      have h := hstep a1 ha1
      have h' : ((frameStepSetD d H a0 a1 b).card : ℝ)
          ≤ ((3 ^ d.primeFactors.card * (H / frameMod d a0 a1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at h'
      linarith [h']
    have hfloor : ((H / frameMod d a0 a1 : ℕ) : ℝ) ≤ (H : ℝ) / (frameMod d a0 a1 : ℝ) :=
      Nat.cast_div_le
    have hwg : (0 : ℝ) ≤ wg m a0 a1 := wg_nonneg m a0 a1
    have h3 : (3 : ℝ) ^ (d.primeFactors.card) ≤ (6 : ℝ) ^ (d.primeFactors.card) := by
      have h36 : (3 : ℝ) ≤ 6 := by norm_num
      exact pow_le_pow_left₀ (by norm_num) h36 _
    have hkey : ((frameStepSetD d H a0 a1 b).card : ℝ)
        ≤ (6 : ℝ) ^ (d.primeFactors.card)
            * (((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1)) := by
      have hcomb : (3 : ℝ) ^ (d.primeFactors.card)
          * ((H : ℝ) / (frameMod d a0 a1 : ℝ) + 1)
          ≤ (6 : ℝ) ^ (d.primeFactors.card)
            * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1) := by
        have h1 : (H : ℝ) / (frameMod d a0 a1 : ℝ) + 1
            ≤ (H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
                * (2 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) + 1 := hbrid
        have h2 : (H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
              * (2 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) + 1
            = (H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ)
                * (2 : ℝ) ^ (d.primeFactors.card) + 1 := by
          simp only [a1Shift]
          ring
        rw [h2] at h1
        have h3' : (3 : ℝ) ^ (d.primeFactors.card)
            * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ)
                * (2 : ℝ) ^ (d.primeFactors.card) + 1)
            = (6 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1)
              - (6 : ℝ) ^ (d.primeFactors.card)
              + (3 : ℝ) ^ (d.primeFactors.card) := by
          rw [show (6 : ℝ) ^ (d.primeFactors.card)
              = (3 : ℝ) ^ (d.primeFactors.card) * (2 : ℝ) ^ (d.primeFactors.card) from by
            rw [show (6 : ℝ) = 3 * 2 by norm_num, mul_pow]]
          ring
        have hnon : (0 : ℝ) ≤ (H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) := by positivity
        have hsplit : (3 : ℝ) ^ (d.primeFactors.card)
            * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ)
                * (2 : ℝ) ^ (d.primeFactors.card) + 1)
            ≤ (6 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1) := by
          rw [h3']
          have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (d.primeFactors.card) := by positivity
          have : (0 : ℝ) ≤ (6 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1)
              - (3 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1)
              + (3 : ℝ) ^ (d.primeFactors.card)
              - (6 : ℝ) ^ (d.primeFactors.card) := by
            have := mul_le_mul_of_nonneg_right h3 hnon
            nlinarith [h2pos, hnon, h3]
          linarith
        calc (3 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (frameMod d a0 a1 : ℝ) + 1)
            ≤ (3 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ)
                  * (2 : ℝ) ^ (d.primeFactors.card) + 1) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (6 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1) := hsplit
      calc ((frameStepSetD d H a0 a1 b).card : ℝ)
          ≤ (3 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (frameMod d a0 a1 : ℝ) + 1) := by
            exact hcast.trans (mul_le_mul_of_nonneg_left (by linarith [hfloor]) (by positivity))
        _ ≤ (6 : ℝ) ^ (d.primeFactors.card)
              * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1) := hcomb
    calc ((frameStepSetD d H a0 a1 b).card : ℝ) * wg m a0 a1
        ≤ (6 : ℝ) ^ (d.primeFactors.card)
            * ((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1) * wg m a0 a1 :=
          mul_le_mul_of_nonneg_right hkey hwg
      _ = (6 : ℝ) ^ (d.primeFactors.card)
            * (((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1) * wg m a0 a1) := by ring
  have hE := sum_gcdMulSqrtGcd_guarded_le (m := m) (d := d) (a0 := a0) (H := H) hm hd hmd ha0 ha0H
  have hD := sum_sqrtGcd_guarded_le (m := m) (a0 := a0) (H := H) hm ha0 ha0H
  have h6 : (0 : ℝ) ≤ (6 : ℝ) ^ (d.primeFactors.card) := by positivity
  calc (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
        ((frameStepSetD d H a0 a1 b).card : ℝ) * wg m a0 a1)
      ≤ ∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
          (6 : ℝ) ^ (d.primeFactors.card)
            * (((H : ℝ) / (d : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) + 1) * wg m a0 a1) :=
        Finset.sum_le_sum hpt
    _ = (6 : ℝ) ^ (d.primeFactors.card)
          * ((H : ℝ) / (d : ℝ) * (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
              (Nat.gcd d (a1Shift a0 a1) : ℝ) * wg m a0 a1)
            + ∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0), wg m a0 a1) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun a1 _ => by ring)
    _ ≤ (6 : ℝ) ^ (d.primeFactors.card)
          * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) * ((m.divisors.card : ℝ))
            + (H : ℝ) * ((m.divisors.card : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ h6
        have hE' : (H : ℝ) / (d : ℝ)
            * (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
                (Nat.gcd d (a1Shift a0 a1) : ℝ) * wg m a0 a1)
            ≤ ((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) * ((m.divisors.card : ℝ)) := hE
        have hD' : (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0), wg m a0 a1)
            ≤ (H : ℝ) * ((m.divisors.card : ℝ)) := hD
        linarith
    _ ≤ (6 : ℝ) ^ (d.primeFactors.card)
          * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
              * ((m.divisors.card : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ h6
        have hA : (0 : ℝ) ≤ (H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ) := by positivity
        have hτ : (0 : ℝ) ≤ ((m.divisors.card : ℝ)) := by positivity
        have hH : (0 : ℝ) ≤ (H : ℝ) := by positivity
        nlinarith [hA, hτ, hH]

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- **Unconditional form of `frameStepSum_le`.**  The frame-step count bound `hstep` is discharged
by `frame_step_card_d_nohb` (the sorry-free variant, which needs only `0 < d` and `a0 ≠ a1` — both
available here: the second from the filter).  So for `1 ≤ a0 ≤ H` the `a1`-sum of the frame-step
count against the weight `wg m a0 a1` is bounded outright by `6^ω(d)` times the repaired
arithmetic-progression bound. -/
theorem frameStepSum_le_uncond {H m d a0 : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : Nat.Coprime m d)
    (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) (b : Fin 3 → ℕ) :
    (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
        ((frameStepSetD d H a0 a1 b).card : ℝ) * wg m a0 a1)
      ≤ (6 : ℝ) ^ (d.primeFactors.card)
          * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
              * ((m.divisors.card : ℝ))) := by
  refine frameStepSum_le hm hd hmd ha0 ha0H b (fun a1 ha1 => ?_)
  have hne : a1 ≠ a0 := (Finset.mem_filter.mp ha1).2
  have h01 : a0 ≠ a1 := fun h => hne h.symm
  have h := frame_step_card_d_nohb (d := d) (a0 := a0) (a1 := a1) (b := b) (H := H) hd h01
  simpa [frameMod] using h

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The second guard carried by `condAB`: `a 0 ≠ a 2` (companion of `condAB_shift_ne`). -/
theorem condAB_shift_ne₂ {d g : ℕ} {a b : Fin 3 → ℕ} (h : condAB d g a b) : a 0 ≠ a 2 := h.2.2.1

/-- **The `a1`-half of Case I.**  Fix the pivot `a 0 = a0 ∈ [1,H]` and the second triple `b`.  The
double sum over the second entry `a1 ≠ a0` of `wg m a0 a1` against the admissible third entries
`a2` — here the frame set `frameStepSetD d H a0 a1 b` restricted to `a2 ≠ a0`, which is how the
Case-I sum presents it, since the admissible triples satisfy the conjunct `a 0 ≠ a 2` of `condAB`
— weighted by `wg m a0 a2`, is at most `√H` times the hypothesis-free frame-count input
`frameStepSum_le_uncond`.  (The restriction to `a2 ≠ a0` is what makes `wg m a0 a2 ≤ √H` available
via `wg_le_sqrt_H`.) -/
theorem a1_half_caseI {H m d a0 : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : Nat.Coprime m d)
    (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) (b : Fin 3 → ℕ) :
    (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
        ∑ a2 ∈ (frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0),
          wg m a0 a1 * wg m a0 a2)
      ≤ Real.sqrt (H : ℝ) * ((6 : ℝ) ^ (d.primeFactors.card)
          * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
              * ((m.divisors.card : ℝ)))) := by
  classical
  set S := (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0) with hS
  have hinner : ∀ a1 ∈ S,
      (∑ a2 ∈ (frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0), wg m a0 a2)
      ≤ (((frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0)).card : ℝ)
          * Real.sqrt (H : ℝ) := by
    intro a1 _
    have hpt : ∀ a2 ∈ (frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0),
        wg m a0 a2 ≤ Real.sqrt (H : ℝ) := by
      intro a2 ha2
      obtain ⟨ha2', hne⟩ := Finset.mem_filter.mp ha2
      have ha2I : a2 ∈ Finset.Icc 1 H := by
        have h := ha2'
        unfold frameStepSetD at h
        exact (Finset.mem_filter.mp h).1
      exact wg_le_sqrt_H ha0H (Finset.mem_Icc.mp ha2I).2 hne.symm
    calc (∑ a2 ∈ (frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0), wg m a0 a2)
        ≤ ∑ a2 ∈ (frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0), Real.sqrt (H : ℝ) :=
          Finset.sum_le_sum hpt
      _ = (((frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0)).card : ℝ)
            * Real.sqrt (H : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ a1 ∈ S, ∑ a2 ∈ (frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0),
          wg m a0 a1 * wg m a0 a2)
      = ∑ a1 ∈ S, wg m a0 a1
          * (∑ a2 ∈ (frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0), wg m a0 a2) := by
        refine Finset.sum_congr rfl (fun a1 _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ a1 ∈ S, wg m a0 a1
          * ((((frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0)).card : ℝ)
              * Real.sqrt (H : ℝ)) := by
        refine Finset.sum_le_sum (fun a1 ha1 => ?_)
        exact mul_le_mul_of_nonneg_left (hinner a1 ha1) (wg_nonneg m a0 a1)
    _ = Real.sqrt (H : ℝ) * (∑ a1 ∈ S,
          ((((frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0)).card : ℝ) * wg m a0 a1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a1 _ => by ring)
    _ ≤ Real.sqrt (H : ℝ) * ((6 : ℝ) ^ (d.primeFactors.card)
          * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
              * ((m.divisors.card : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        refine le_trans (Finset.sum_le_sum (fun a1 _ => ?_))
          (frameStepSum_le_uncond hm hd hmd ha0 ha0H b)
        have hcard : ((((frameStepSetD d H a0 a1 b).filter (fun a2 => a2 ≠ a0)).card : ℕ) : ℝ)
            ≤ (((frameStepSetD d H a0 a1 b).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_filter_le (frameStepSetD d H a0 a1 b) (fun a2 => a2 ≠ a0)
        exact mul_le_mul_of_nonneg_right hcard (wg_nonneg m a0 a1)

/-- **The `a1`-half of Case I, at the call site.**  `a1_half_caseI` with the anchoring read off
`a ∈ box3 H` — the hypothesis available in the body of the Case-I sum of `sumI_le`, whose outer
sums are over `a ∈ box3 H`, `b ∈ box3 H` with `condAB d g a b ∧ CaseI a b`. -/
theorem a1_half_caseI' {H m d : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : Nat.Coprime m d)
    {a : Fin 3 → ℕ} (ha : a ∈ box3 H) (b : Fin 3 → ℕ) :
    (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a 0),
        ∑ a2 ∈ (frameStepSetD d H (a 0) a1 b).filter (fun a2 => a2 ≠ a 0),
          wg m (a 0) a1 * wg m (a 0) a2)
      ≤ Real.sqrt (H : ℝ) * ((6 : ℝ) ^ (d.primeFactors.card)
          * (4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
              * ((m.divisors.card : ℝ)))) := by
  classical
  obtain ⟨ha01, ha0H⟩ := box3_anchor ha
  exact a1_half_caseI hm hd hmd (a0 := a 0) ha01 ha0H b

end Work.LinnikBurgess
