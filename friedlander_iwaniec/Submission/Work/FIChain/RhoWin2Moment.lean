/-
# `Submission.Work.FIChain.RhoWin2Moment`

The `τ⁶`-moment of the `Π`-restricted window sum `Xpg`:

  `Σ_{c ≤ x} τ(c)⁶ |Xpg x Pz c σ u| ≤ C₆ · Ã(x) · (log x)^{262144}`

for every `x ≥ x₀`, every `Pz` and every `σ, u : ℝ`.  This is the input the endgame
`Submission/Work/FIChain/RhoWindowIntegrated2.lean` consumes when it passes from the
`n₁`-split of the companion's §10 (`Submission.Work.FIChain.RhoWin2Ident`) to the
`τ`-weighted mass of the Friedlander–Iwaniec sequence.

The whole content is the `τ⁸`-mass theorem `Work.FITop.AseqTauEightBound`
(`Σ_{n ≤ x} ã(n)τ(n)⁸ ≤ C·Ã(x)(log x)^{262144}`, itself proved from the single-modulus
congruence bound `Ad_le_tau_sq_div_of_cubefree` and the divisor sums): the pointwise
domination `|Xpg| ≤ Σ τ(n)ã(cn)` (`abs_Xpg_le_mass`), the elementary inequality

  `τ(c)⁶ τ(n) ≤ τ(cn)⁷`     (`tau_pow_six_mul_tau_le`)

and the regrouping of the double sum `Σ_{cn ≤ x}` by the value `m = cn`, each `m` contributing
at most `τ(m)` (`= #divisors of m`) pairs — the *fibre* count that turns `τ⁷` into `τ⁸`.
Everything here is elementary: no `Prop41`-type input is used, and the two `τ`-powers match
by construction (the exponent `262144 = 2¹⁸` is the one of `AseqTauEightBound`).
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FITop.AseqTauEightBound

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The pointwise inequality `τ(c)⁶ τ(n) ≤ τ(cn)⁷` -/

/-- `τ(c)⁶·τ(n) ≤ τ(cn)⁷` for all `c, n`:  both `c` and `n` divide `cn`, so both divisor
functions are dominated by `τ(cn)`, and `τ(c)⁶τ(n) ≤ τ(cn)⁶τ(cn) = τ(cn)⁷`. -/
lemma tau_pow_six_mul_tau_le (c n : ℕ) :
    ((c.divisors.card : ℝ)) ^ 6 * ((n.divisors.card : ℝ)) ≤ (((c * n).divisors.card : ℝ)) ^ 7 := by
  rcases Nat.eq_zero_or_pos (c * n) with h0 | hpos
  · -- `cn = 0` forces `c = 0` or `n = 0`, and `τ(0) = #∅ = 0`
    have hcn : c * n = 0 := h0
    rcases Nat.mul_eq_zero.mp hcn with hc | hn
    · rw [hc, Nat.divisors_zero]; norm_num
    · rw [hn, Nat.divisors_zero]; norm_num
  · have hm0 : c * n ≠ 0 := by omega
    have h1 : ((c.divisors.card : ℝ)) ≤ ((c * n).divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hm0 (dvd_mul_right c n))
    have h2 : ((n.divisors.card : ℝ)) ≤ ((c * n).divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hm0 (dvd_mul_left n c))
    calc ((c.divisors.card : ℝ)) ^ 6 * ((n.divisors.card : ℝ))
        ≤ (((c * n).divisors.card : ℝ)) ^ 6 * ((c * n).divisors.card : ℝ) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) h1 6) h2 (by positivity) (by positivity)
      _ = (((c * n).divisors.card : ℝ)) ^ 7 := by ring

/-! ## 2. The `τ⁶`-weighted double sum is dominated by the `τ⁸`-mass -/

/-- **Regrouping of the `τ⁶`-weighted double sum.**  For every `x`,

  `Σ_{c ≤ x} Σ_{n ≤ x, cn ≤ x} τ(c)⁶ τ(n) ã(cn) ≤ Σ_{m ≤ x} ã(m) τ(m)⁸`.

The reindexing is by the value `m = cn`: the pairs `(c,n)` with `cn = m`, `c,n ≥ 1` are the
divisors `c` of `m` together with `n = m/c`, so there are `τ(m)` of them and each contributes
at most `τ(m)⁷ ã(m)` by `tau_pow_six_mul_tau_le`. -/
lemma double_sum_le_tau_eight (x : ℕ) :
    (∑ c ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
        (if c * n ≤ x then ((c.divisors.card : ℝ)) ^ 6 * (((n.divisors.card : ℝ)) * atilc (c * n)) else 0))
      ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 8 := by
  -- the iterated sum is a sum over the `Σ`-set of pairs `(c,n)`, with a `cn ≤ x` indicator
  have h1 : (∑ c ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
        (if c * n ≤ x then ((c.divisors.card : ℝ)) ^ 6 * (((n.divisors.card : ℝ)) * atilc (c * n)) else 0))
      = ∑ p ∈ ((Finset.Icc 1 x).sigma (fun _ => Finset.Icc 1 x)).filter (fun p => p.1 * p.2 ≤ x),
          ((p.1.divisors.card : ℝ)) ^ 6 * (((p.2.divisors.card : ℝ)) * atilc (p.1 * p.2)) := by
    have h : (∑ c ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
          (if c * n ≤ x then ((c.divisors.card : ℝ)) ^ 6 * (((n.divisors.card : ℝ)) * atilc (c * n)) else 0))
        = ∑ p ∈ ((Finset.Icc 1 x).sigma (fun _ => Finset.Icc 1 x)),
            (if p.1 * p.2 ≤ x then ((p.1.divisors.card : ℝ)) ^ 6 * (((p.2.divisors.card : ℝ)) * atilc (p.1 * p.2)) else 0) := by
      rw [Finset.sum_sigma]
    rw [h, ← Finset.sum_filter]
  -- the bijection `(c,n) ↦ (cn, c)` onto the pairs `(m, c)` with `c ∣ m`
  have h2 : (∑ p ∈ ((Finset.Icc 1 x).sigma (fun _ => Finset.Icc 1 x)).filter (fun p => p.1 * p.2 ≤ x),
        ((p.1.divisors.card : ℝ)) ^ 6 * (((p.2.divisors.card : ℝ)) * atilc (p.1 * p.2)))
      = ∑ a ∈ (Finset.Icc 1 x).sigma (fun m => m.divisors),
          ((a.2.divisors.card : ℝ)) ^ 6 * ((((a.1 / a.2).divisors.card : ℝ)) * atilc a.1) := by
    refine Finset.sum_nbij' (fun p : Sigma fun _ : ℕ => ℕ => ⟨p.1 * p.2, p.1⟩)
      (fun a : Sigma fun _ : ℕ => ℕ => ⟨a.2, a.1 / a.2⟩) ?_ ?_ ?_ ?_ ?_
    · -- `(c,n) ↦ (cn,c)` lands in the `Σ`-set of divisors
      intro a ha
      rw [Finset.mem_filter, Finset.mem_sigma] at ha
      obtain ⟨⟨ha1, ha2⟩, ham⟩ := ha
      rw [Finset.mem_sigma]
      have h1' : 1 ≤ a.fst := (Finset.mem_Icc.mp ha1).1
      have h2' : 1 ≤ a.snd := (Finset.mem_Icc.mp ha2).1
      have hpos : 0 < a.fst * a.snd := Nat.mul_pos (by omega) (by omega)
      have hne : a.fst * a.snd ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      constructor
      · show a.fst * a.snd ∈ Finset.Icc 1 x
        rw [Finset.mem_Icc]
        exact ⟨by omega, ham⟩
      · show a.fst ∈ (a.fst * a.snd).divisors
        rw [Nat.mem_divisors]
        exact ⟨dvd_mul_right _ _, hne⟩
    · -- the inverse `(m,c) ↦ (c, m/c)`
      intro a ha
      rw [Finset.mem_sigma] at ha
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp ha2
      rw [Finset.mem_filter, Finset.mem_sigma]
      have hmx : a.fst ≤ x := (Finset.mem_Icc.mp ha1).2
      have hcpos : 0 < a.snd :=
        Nat.pos_of_dvd_of_pos hdvd (by have := (Finset.mem_Icc.mp ha1).1; omega)
      have hcle : a.snd ≤ a.fst := Nat.le_of_dvd (by omega) hdvd
      have hdq : 0 < a.fst / a.snd := Nat.div_pos hcle hcpos
      have hdl : a.fst / a.snd ≤ a.fst := Nat.div_le_self a.fst a.snd
      constructor
      · constructor
        · show a.snd ∈ Finset.Icc 1 x
          rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
        · show a.fst / a.snd ∈ Finset.Icc 1 x
          rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
      · show a.snd * (a.fst / a.snd) ≤ x
        rw [Nat.mul_div_cancel' hdvd]; exact hmx
    · -- `(m/c, c) ↦ (c, m/c) = (c, n)`
      intro a ha
      rw [Finset.mem_filter, Finset.mem_sigma] at ha
      obtain ⟨⟨ha1, ha2⟩, ham⟩ := ha
      have hm : 0 < a.fst := by have := (Finset.mem_Icc.mp ha1).1; omega
      rw [Sigma.mk.inj_iff]
      exact ⟨rfl, heq_of_eq (Nat.mul_div_right a.snd hm)⟩
    · -- `(cn, c) ↦ (c, m/c) = (c, n)`
      intro a ha
      rw [Finset.mem_sigma] at ha
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp ha2
      rw [Sigma.mk.inj_iff]
      exact ⟨Nat.mul_div_cancel' hdvd, heq_of_eq rfl⟩
    · -- the weights agree: `τ(c)⁶τ(n)ã(cn) = τ(c)⁶τ((cn)/c)ã(cn)`
      intro a ha
      rw [Finset.mem_filter, Finset.mem_sigma] at ha
      obtain ⟨⟨ha1, ha2⟩, ham⟩ := ha
      have hm : 0 < a.fst := by have := (Finset.mem_Icc.mp ha1).1; omega
      show ((a.fst.divisors.card : ℝ)) ^ 6 * ((a.snd.divisors.card : ℝ) * atilc (a.fst * a.snd)) =
        ((a.fst.divisors.card : ℝ)) ^ 6 * ((((a.fst * a.snd) / a.fst).divisors.card : ℝ) * atilc (a.fst * a.snd))
      rw [Nat.mul_div_right a.snd hm]
  have h3 : (∑ a ∈ (Finset.Icc 1 x).sigma (fun m => m.divisors),
        ((a.2.divisors.card : ℝ)) ^ 6 * ((((a.1 / a.2).divisors.card : ℝ)) * atilc a.1))
      = ∑ m ∈ Finset.Icc 1 x, ∑ c ∈ m.divisors,
          ((c.divisors.card : ℝ)) ^ 6 * ((((m / c).divisors.card : ℝ)) * atilc m) := by
    rw [Finset.sum_sigma]
  -- each `m` contributes at most `τ(m)` terms, each of size `≤ τ(m)⁷ ã(m)`
  have h4 : (∑ m ∈ Finset.Icc 1 x, ∑ c ∈ m.divisors,
        ((c.divisors.card : ℝ)) ^ 6 * ((((m / c).divisors.card : ℝ)) * atilc m))
      ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 8 := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    have hpt : ∀ c ∈ m.divisors,
        ((c.divisors.card : ℝ)) ^ 6 * ((((m / c).divisors.card : ℝ)) * atilc m)
          ≤ ((m.divisors.card : ℝ)) ^ 7 * atilc m := by
      intro c hc
      obtain ⟨hcdvd, hmne⟩ := Nat.mem_divisors.mp hc
      have hmain : ((c.divisors.card : ℝ)) ^ 6 * ((((m / c).divisors.card : ℝ)))
          ≤ ((m.divisors.card : ℝ)) ^ 7 := by
        have h := tau_pow_six_mul_tau_le c (m / c)
        rwa [Nat.mul_div_cancel' hcdvd] at h
      have ha0 : 0 ≤ atilc m := Work.FITop.atilFIa_nonneg m
      calc ((c.divisors.card : ℝ)) ^ 6 * ((((m / c).divisors.card : ℝ)) * atilc m)
          = (((c.divisors.card : ℝ)) ^ 6 * (((m / c).divisors.card : ℝ))) * atilc m := by ring
        _ ≤ ((m.divisors.card : ℝ)) ^ 7 * atilc m := mul_le_mul_of_nonneg_right hmain ha0
    calc (∑ c ∈ m.divisors, ((c.divisors.card : ℝ)) ^ 6 * ((((m / c).divisors.card : ℝ)) * atilc m))
        ≤ m.divisors.card • (((m.divisors.card : ℝ)) ^ 7 * atilc m) :=
          Finset.sum_le_card_nsmul _ _ _ hpt
      _ = atilc m * ((m.divisors.card : ℝ)) ^ 8 := by
          rw [nsmul_eq_mul]; ring
  calc (∑ c ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
        (if c * n ≤ x then ((c.divisors.card : ℝ)) ^ 6 * (((n.divisors.card : ℝ)) * atilc (c * n)) else 0))
      = ∑ m ∈ Finset.Icc 1 x, ∑ c ∈ m.divisors,
          ((c.divisors.card : ℝ)) ^ 6 * ((((m / c).divisors.card : ℝ)) * atilc m) := h1.trans (h2.trans h3)
    _ ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 8 := h4

/-! ## 3. The moment bound -/

/-- The `τ⁶`-moment of the `Π`-restricted window sum, bounded by the `τ⁸`-mass of `ã`. -/
theorem RhoWin2Moment : ∃ C₆ : ℝ, 0 < C₆ ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ Pz : ℕ, ∀ σ u : ℝ,
    (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 * |Xpg x Pz c σ u|)
      ≤ C₆ * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ) := by
  obtain ⟨C, X₀, hC, hbound⟩ := Work.FITop.AseqTauEightBound
  refine ⟨(C : ℝ), by exact_mod_cast hC, X₀, ?_⟩
  intro x hx Pz σ u
  -- Step 1: `|Xpg| ≤ Σ_n τ(n)ã(cn)` and the `cn ≤ x` indicator
  have hstep : (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 * |Xpg x Pz c σ u|)
      ≤ ∑ c ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
          (if c * n ≤ x then ((c.divisors.card : ℝ)) ^ 6 * (((n.divisors.card : ℝ)) * atilc (c * n)) else 0) := by
    refine Finset.sum_le_sum (fun c hc => ?_)
    have hτ : (0 : ℝ) ≤ ((c.divisors.card : ℝ)) ^ 6 := by positivity
    calc ((c.divisors.card : ℝ)) ^ 6 * |Xpg x Pz c σ u|
        ≤ ((c.divisors.card : ℝ)) ^ 6 * (∑ n ∈ (Finset.Icc 1 x).filter
            (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u),
            ((n.divisors.card : ℝ)) * atilc (c * n)) :=
          mul_le_mul_of_nonneg_left (abs_Xpg_le_mass x Pz c σ u) hτ
      _ = ∑ n ∈ (Finset.Icc 1 x).filter
            (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u),
            ((c.divisors.card : ℝ)) ^ 6 * (((n.divisors.card : ℝ)) * atilc (c * n)) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x),
            ((c.divisors.card : ℝ)) ^ 6 * (((n.divisors.card : ℝ)) * atilc (c * n)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n hn _ => ?_)
          · intro n hn
            rw [Finset.mem_filter] at hn ⊢
            exact ⟨hn.1, hn.2.1⟩
          · exact mul_nonneg (by positivity)
              (mul_nonneg (by positivity) (Work.FITop.atilFIa_nonneg _))
      _ = ∑ n ∈ Finset.Icc 1 x,
            (if c * n ≤ x then ((c.divisors.card : ℝ)) ^ 6 * (((n.divisors.card : ℝ)) * atilc (c * n)) else 0) := by
          rw [Finset.sum_filter]
  -- Steps 2–3: the `τ⁸`-mass of `ã`, i.e. `AseqTauEightBound`
  calc (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 * |Xpg x Pz c σ u|)
      ≤ ∑ m ∈ Finset.Icc 1 x, atilc m * ((m.divisors.card : ℝ)) ^ 8 :=
        le_trans hstep (double_sum_le_tau_eight x)
    _ ≤ (C : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ) := hbound x hx

end

end Work.FIChain
