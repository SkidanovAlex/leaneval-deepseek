import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.R6.count_mul_sq_range_clean
import Submission.Work.FIArea2.R6.sum_gcd_zPz_le
import Submission.Work.FIArea2.R6.sum_gcd_div_sqrt_zPz_le
import Submission.Work.FIArea2.R6.four_pow_primeFactors_le_divisors_sq
import Submission.Work.FIArea2.R6.gcd_mul_natAbs_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Elementary helpers for the lossy local-density bound

The proof of `LD_lossy` combines

* `card_zmod_filter_eq_card_range` — the count of `z : ZMod c` with `A z² = B` is the number of
  representatives `z ∈ {0, …, c-1}` with `c ∣ A z² - B`;
* `count_mul_sq_range` — the lossy one-variable congruence count
  `#{z < c : c ∣ A z² - B} ≤ gcd(A,c) · 4^{ω(c)} · √(gcd(B,c))`;
* `four_pow_primeFactors_le_divisors_sq` — `4^{ω(c)} ≤ τ(c)²`;
* `sum_gcd_zPz_le`, `sum_gcd_div_sqrt_zPz_le` — the two divisor sums over the boxes;
* `gcd_mul_natAbs_le` — `gcd(xy,c) ≤ gcd(x,c)gcd(y,c)`;
* the AM–GM factorisation `1/max(|v₁|,|v₂|) ≤ 1/(√|v₁| √|v₂|)`.
-/

/-- The `ZMod c`-count of `z` with `A * z ^ 2 = B` equals the number of representatives
`z ∈ {0, …, c-1}` with `c ∣ A * z ^ 2 - B` (the bijection `z ↦ z.val`). -/
private lemma card_zmod_filter_eq_card_range (c : ℕ) [NeZero c] (A B : ℤ) :
    ((Finset.univ : Finset (ZMod c)).filter (fun z => (A : ZMod c) * z ^ 2 = (B : ZMod c))).card
      = ((Finset.range c).filter (fun z : ℕ => (c : ℤ) ∣ A * (z : ℤ) ^ 2 - B)).card := by
  refine Finset.card_bij (fun (z : ZMod c) _ => z.val) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt z, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (A * (z.val : ℤ) ^ 2 - B) c]
    have hcast : ((A * (z.val : ℤ) ^ 2 - B : ℤ) : ZMod c)
        = (A : ZMod c) * z ^ 2 - (B : ZMod c) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hcast, hz, sub_self]
  · intro z1 _ z2 _ h
    exact ZMod.val_injective c h
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_range] at hz
    refine ⟨(z : ZMod c), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hcast : ((A * (z : ℤ) ^ 2 - B : ℤ) : ZMod c)
          = (A : ZMod c) * (z : ZMod c) ^ 2 - (B : ZMod c) := by
        push_cast
        rfl
      have hz0 : ((A * (z : ℤ) ^ 2 - B : ℤ) : ZMod c) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hz.2
      rw [← sub_eq_zero, ← hcast]
      exact hz0
    · exact ZMod.val_cast_of_lt hz.1

/-- `gcd(x y², c) ≤ gcd(x, c) · gcd(y, c)²`. -/
private lemma gcd_mul_sq_natAbs_le (c : ℕ) (x y : ℤ) :
    Nat.gcd (x * y ^ 2).natAbs c ≤ Nat.gcd x.natAbs c * (Nat.gcd y.natAbs c) ^ 2 := by
  calc Nat.gcd (x * y ^ 2).natAbs c
      ≤ Nat.gcd x.natAbs c * Nat.gcd (y ^ 2).natAbs c := gcd_mul_natAbs_le c x (y ^ 2)
    _ = Nat.gcd x.natAbs c * Nat.gcd (y.natAbs ^ 2) c := by rw [Int.natAbs_pow]
    _ ≤ Nat.gcd x.natAbs c * (Nat.gcd y.natAbs c) ^ 2 := by
        refine Nat.mul_le_mul_left _ ?_
        have h := gcd_mul_natAbs_le c (y.natAbs : ℤ) (y.natAbs : ℤ)
        have h2 : (((y.natAbs : ℤ) * (y.natAbs : ℤ)).natAbs) = y.natAbs ^ 2 := by
          simp [Int.natAbs_mul, pow_two]
        have h3 : ((y.natAbs : ℤ)).natAbs = y.natAbs := Int.natAbs_natCast y.natAbs
        rw [h2, h3] at h
        simpa [pow_two] using h

/-- `√(gcd(x y², c)) ≤ √(gcd(x, c)) · gcd(y, c)`. -/
private lemma sqrt_gcd_mul_sq_le (c : ℕ) (x y : ℤ) :
    Real.sqrt (Nat.gcd (x * y ^ 2).natAbs c : ℝ)
      ≤ Real.sqrt (Nat.gcd x.natAbs c : ℝ) * (Nat.gcd y.natAbs c : ℝ) := by
  have hg := gcd_mul_sq_natAbs_le c x y
  have hstep : Real.sqrt (Nat.gcd (x * y ^ 2).natAbs c : ℝ)
      ≤ Real.sqrt ((Nat.gcd x.natAbs c * (Nat.gcd y.natAbs c) ^ 2 : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hg
  refine le_trans hstep ?_
  rw [Nat.cast_mul, Nat.cast_pow]
  rw [Real.sqrt_mul (by positivity)]
  rw [Real.sqrt_sq (by positivity)]

/-- `(Nat.sqrt n : ℝ) ≤ Real.sqrt n`. -/
private lemma natSqrt_cast_le (n : ℕ) : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast Nat.sqrt_le' n

/-- AM–GM: `1/max(a,b) ≤ 1/(√a √b)` for positive naturals. -/
private lemma div_max_le_div_sqrt_mul (C : ℝ) (hC : 0 ≤ C) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    C / (((max a b : ℕ)) : ℝ) ≤ C / (Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ)) := by
  have hpa : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos_of_pos (by exact_mod_cast ha)
  have hpb : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos_of_pos (by exact_mod_cast hb)
  refine div_le_div_of_nonneg_left hC (mul_pos hpa hpb) ?_
  have hmul : Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ) = Real.sqrt ((a : ℝ) * (b : ℝ)) :=
    (Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (a : ℝ)) _).symm
  rw [hmul]
  have h2 : (a : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_left a b
  have h3 : (b : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_right a b
  calc Real.sqrt ((a : ℝ) * b) ≤ Real.sqrt ((((max a b : ℕ)) : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc (a : ℝ) * b ≤ (((max a b : ℕ)) : ℝ) * (((max a b : ℕ)) : ℝ) :=
              mul_le_mul h2 h3 (by positivity) (by positivity)
          _ = (((max a b : ℕ)) : ℝ) ^ 2 := by ring
    _ = (((max a b : ℕ)) : ℝ) := Real.sqrt_sq (by positivity)

/-- **Pointwise (per-`(h₁,v₁,v₂)`) lossy local-density bound.**  For `v₁, v₂ ≠ 0` and `c ≥ 1`,

`#{z : ZMod c // v₂ z² = v₁ h₁²} / max(|v₁|,|v₂|) ≤ τ(c)² · gcd(h₁,c) · (√gcd(v₁,c)/√|v₁|) ·
(gcd(v₂,c)/√|v₂|)`. -/
private lemma term_le (c : ℕ) [NeZero c] (hc : 1 ≤ c) (h1 v1 v2 : ℤ) (hv1 : v1 ≠ 0)
    (hv2 : v2 ≠ 0) :
    ((((Finset.univ : Finset (ZMod c)).filter
        (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * (h1 : ZMod c) ^ 2)).card : ℝ)
        / ((max v1.natAbs v2.natAbs : ℕ) : ℝ))
      ≤ (c.divisors.card : ℝ) ^ 2
        * ((Nat.gcd h1.natAbs c : ℝ)
          * ((Real.sqrt (Nat.gcd v1.natAbs c : ℝ) / Real.sqrt (v1.natAbs : ℝ))
            * ((Nat.gcd v2.natAbs c : ℝ) / Real.sqrt (v2.natAbs : ℝ)))) := by
  have hfilter : (Finset.univ.filter
        (fun z : ZMod c => (v2 : ZMod c) * z ^ 2 = ((v1 * h1 ^ 2 : ℤ) : ZMod c)))
      = (Finset.univ.filter
        (fun z : ZMod c => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * (h1 : ZMod c) ^ 2)) := by
    refine Finset.filter_congr ?_
    intro z _
    rw [show ((v1 * h1 ^ 2 : ℤ) : ZMod c) = (v1 : ZMod c) * (h1 : ZMod c) ^ 2 from by
      push_cast; ring]
  have hbridge : ((Finset.univ : Finset (ZMod c)).filter
        (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * (h1 : ZMod c) ^ 2)).card
      = ((Finset.range c).filter
        (fun z : ℕ => (c : ℤ) ∣ v2 * (z : ℤ) ^ 2 - v1 * h1 ^ 2)).card := by
    rw [← hfilter]
    exact card_zmod_filter_eq_card_range c v2 (v1 * h1 ^ 2)
  have hcount : ((((Finset.univ : Finset (ZMod c)).filter
        (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * (h1 : ZMod c) ^ 2)).card : ℝ))
      ≤ (Nat.gcd v2.natAbs c : ℝ) * (c.divisors.card : ℝ) ^ 2
        * (Real.sqrt (Nat.gcd v1.natAbs c : ℝ) * (Nat.gcd h1.natAbs c : ℝ)) := by
    have hbnd := count_mul_sq_range_clean c hc v2 hv2 (v1 * h1 ^ 2)
    have hbndR : ((((Finset.range c).filter
        (fun z : ℕ => (c : ℤ) ∣ v2 * (z : ℤ) ^ 2 - v1 * h1 ^ 2)).card : ℕ) : ℝ)
        ≤ ((Nat.gcd v2.natAbs c * 4 ^ c.primeFactors.card
            * Nat.sqrt (Nat.gcd (v1 * h1 ^ 2).natAbs c) : ℕ) : ℝ) := by
      exact_mod_cast hbnd
    have h4 : (4 : ℝ) ^ c.primeFactors.card ≤ (c.divisors.card : ℝ) ^ 2 := by
      have := four_pow_primeFactors_le_divisors_sq c (Nat.pos_of_ne_zero (NeZero.ne c))
      exact_mod_cast this
    have hsqrt := sqrt_gcd_mul_sq_le c v1 h1
    have hsqrt' := natSqrt_cast_le (Nat.gcd (v1 * h1 ^ 2).natAbs c)
    calc ((((Finset.univ : Finset (ZMod c)).filter
            (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * (h1 : ZMod c) ^ 2)).card : ℝ))
        = ((((Finset.range c).filter
            (fun z : ℕ => (c : ℤ) ∣ v2 * (z : ℤ) ^ 2 - v1 * h1 ^ 2)).card : ℕ) : ℝ) := by
          exact_mod_cast hbridge
      _ ≤ ((Nat.gcd v2.natAbs c * 4 ^ c.primeFactors.card
            * Nat.sqrt (Nat.gcd (v1 * h1 ^ 2).natAbs c) : ℕ) : ℝ) := hbndR
      _ = (Nat.gcd v2.natAbs c : ℝ) * (4 : ℝ) ^ c.primeFactors.card
            * ((Nat.sqrt (Nat.gcd (v1 * h1 ^ 2).natAbs c) : ℕ) : ℝ) := by
          push_cast
          ring
      _ ≤ (Nat.gcd v2.natAbs c : ℝ) * (c.divisors.card : ℝ) ^ 2
            * (Real.sqrt (Nat.gcd v1.natAbs c : ℝ) * (Nat.gcd h1.natAbs c : ℝ)) := by
          calc (Nat.gcd v2.natAbs c : ℝ) * (4 : ℝ) ^ c.primeFactors.card
                * ((Nat.sqrt (Nat.gcd (v1 * h1 ^ 2).natAbs c) : ℕ) : ℝ)
              ≤ (Nat.gcd v2.natAbs c : ℝ) * (4 : ℝ) ^ c.primeFactors.card
                * (Real.sqrt (Nat.gcd v1.natAbs c : ℝ) * (Nat.gcd h1.natAbs c : ℝ)) :=
                mul_le_mul_of_nonneg_left (le_trans hsqrt' hsqrt) (by positivity)
            _ ≤ (Nat.gcd v2.natAbs c : ℝ) * (c.divisors.card : ℝ) ^ 2
                * (Real.sqrt (Nat.gcd v1.natAbs c : ℝ) * (Nat.gcd h1.natAbs c : ℝ)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h4 (by positivity)) (by positivity)
  have hv1pos : 0 < v1.natAbs := Int.natAbs_pos.mpr hv1
  have hv2pos : 0 < v2.natAbs := Int.natAbs_pos.mpr hv2
  have hmax := div_max_le_div_sqrt_mul
    ((((Finset.univ : Finset (ZMod c)).filter
        (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * (h1 : ZMod c) ^ 2)).card : ℝ))
    (by positivity) v1.natAbs v2.natAbs hv1pos hv2pos
  have hgoal : ((Nat.gcd v2.natAbs c : ℝ) * (c.divisors.card : ℝ) ^ 2
        * (Real.sqrt (Nat.gcd v1.natAbs c : ℝ) * (Nat.gcd h1.natAbs c : ℝ)))
        / (Real.sqrt (v1.natAbs : ℝ) * Real.sqrt (v2.natAbs : ℝ))
      = (c.divisors.card : ℝ) ^ 2
        * ((Nat.gcd h1.natAbs c : ℝ)
          * ((Real.sqrt (Nat.gcd v1.natAbs c : ℝ) / Real.sqrt (v1.natAbs : ℝ))
            * ((Nat.gcd v2.natAbs c : ℝ) / Real.sqrt (v2.natAbs : ℝ)))) := by
    have hs1 : (0 : ℝ) < Real.sqrt (v1.natAbs : ℝ) :=
      Real.sqrt_pos_of_pos (by exact_mod_cast hv1pos)
    have hs2 : (0 : ℝ) < Real.sqrt (v2.natAbs : ℝ) :=
      Real.sqrt_pos_of_pos (by exact_mod_cast hv2pos)
    field_simp
  refine le_trans hmax ?_
  refine le_trans (div_le_div_of_nonneg_right hcount (by positivity)) ?_
  rw [hgoal]

/-- **Lossy local-density bound for the square-roots-mod-`c` count.**

`Work.FIArea2.R6.zPz S` is `([-S,S] : Finset ℤ)` with `0` removed (from
`Submission/Work/FIArea2/R6/BSBoxDefs.lean`); `ZMod c` is the residue ring.

For every `c ≥ 1` (given as `[NeZero c]` so that `Finset.univ : Finset (ZMod c)` exists),

  `Σ_{h₁∈zPz X} Σ_{v₁∈zPz S} Σ_{v₂∈zPz S}
      #{z : ZMod c // v₂·z² = v₁·h₁²} / max(|v₁|,|v₂|)  ≤  64·X·S·τ(c)^5`.

This is the `τ(c)^5`-lossy substitute for the sharp local-density estimate (Friedlander-Iwaniec
§9, the count `(10.8)+(10.9)`), used only in the *periodic* regime `max(X,Y) ≥ c`, where the outer
sum over moduli `c` supplies the polylog, so the sharp `τ(c)` is not needed.

PROOF ROUTE (all elementary; constants checked numerically — worst observed ratio 0.23):
* **Helper fact (prove it first as a private helper in the same file).**  For `m ≥ 1` and `a : ℤ`,
  `#{z : ZMod m // z² = a} ≤ 4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd a.natAbs m)`.
  (Verified numerically for every `m ≤ 300` and every residue.)  By CRT reduce to `m = p^k` and
  put `j = v_p(a)`: if `j ≥ k` the solutions are `p^{⌈k/2⌉} ∣ z`, i.e. `p^{⌊k/2⌋} ≤ Nat.sqrt (p^k)`
  of them; if `j < k` is odd there are none; if `j < k` is even then `z = p^{j/2}z'` with `z'` a
  unit and there are at most 2 unit roots for odd `p` (4 for `p = 2`), so `≤ 4·Nat.sqrt (p^j)`.
* Put `e = Nat.gcd v₂.natAbs c`, `c' = c / e`.  As `gcd(v₂/e, c') = 1`, the congruence
  `(v₂ : ZMod c)·z² = (v₁ : ZMod c)·h₁²` forces `e ∣ v₁h₁²` and reduces to `z² = a` in `ZMod c'`
  for a single `a`; each solution mod `c'` lifts to exactly `e` solutions mod `c`, so the count is
  `≤ e·(helper for c') ≤ Nat.gcd v₂.natAbs c · τ(c)² · √(gcd(v₁,c)·gcd(h₁,c))`
  (use the helper twice with `4^{ω(m)} ≤ τ(c)` and `Nat.sqrt` multiplicativity).
* `Σ_{h₁∈zPz X} Nat.gcd h₁.natAbs c ≤ 2X·τ(c)` (expand `gcd = Σ_{e ∣ ·} φ(e)` via
  `Nat.gcd_eq_sum_totient`/`gcd_eq_sum_totient`, then `Σ_{e∣c} φ(e)/e ≤ τ(c)`), and likewise
  `Σ_{|v|≤S} gcd(v,c)/√|v| ≤ 4τ(c)√S` (write `gcd(v,c) = Σ_{e ∣ gcd} φ(e)`, use
  `Σ_{k≤S/e}(ek)^{-1/2} ≤ 2√S/e`, so each `e` contributes `≤ 2√S`).
* `1/max(|v₁|,|v₂|) ≤ 1/√(|v₁|·|v₂|)` (AM–GM) factorises the `v`-double-sum into a square.
The product of these is `≤ 64·X·S·τ(c)^5`. -/
theorem LD_lossy (c X S : ℕ) [NeZero c] :
    (∑ h1 ∈ Work.FIArea2.R6.zPz X, ∑ v1 ∈ Work.FIArea2.R6.zPz S,
        ∑ v2 ∈ Work.FIArea2.R6.zPz S,
      (((Finset.univ : Finset (ZMod c)).filter
          (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
        / ((max v1.natAbs v2.natAbs : ℕ) : ℝ))
      ≤ 64 * (X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5 := by
  have hc : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (NeZero.ne c)
  have hcpos : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := by positivity
  let T : ℝ := (c.divisors.card : ℝ)
  let F : ℤ → ℝ := fun h1 => (Nat.gcd h1.natAbs c : ℝ)
  let G : ℤ → ℝ := fun v => Real.sqrt (Nat.gcd v.natAbs c : ℝ) / Real.sqrt (v.natAbs : ℝ)
  let K : ℤ → ℝ := fun v => (Nat.gcd v.natAbs c : ℝ) / Real.sqrt (v.natAbs : ℝ)
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hpt : ∀ h1 ∈ zPz X, ∀ v1 ∈ zPz S, ∀ v2 ∈ zPz S,
      (((Finset.univ : Finset (ZMod c)).filter
          (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
        / ((max v1.natAbs v2.natAbs : ℕ) : ℝ) ≤ T ^ 2 * (F h1 * (G v1 * K v2)) := by
    intro h1 _ v1 hv1 v2 hv2
    have hv1ne : v1 ≠ 0 := (Finset.mem_filter.mp hv1).2
    have hv2ne : v2 ≠ 0 := (Finset.mem_filter.mp hv2).2
    simpa [T, F, G, K] using term_le c hc h1 v1 v2 hv1ne hv2ne
  have hF : ∑ h1 ∈ zPz X, F h1 ≤ 2 * (X : ℝ) * T := by
    have h := sum_gcd_zPz_le c X hc
    simpa [F, T] using h
  have hK : ∑ v ∈ zPz S, K v ≤ 4 * Real.sqrt (S : ℝ) * T := by
    have h := sum_gcd_div_sqrt_zPz_le c S hc
    simpa [K, T] using h
  have hG : ∑ v ∈ zPz S, G v ≤ 4 * Real.sqrt (S : ℝ) * T := by
    refine le_trans (Finset.sum_le_sum ?_) hK
    intro v hv
    have hvne : v ≠ 0 := (Finset.mem_filter.mp hv).2
    have hpos : (0 : ℝ) < (v.natAbs : ℝ) := by
      exact_mod_cast Int.natAbs_pos.mpr hvne
    have hspos : (0 : ℝ) < Real.sqrt (v.natAbs : ℝ) := Real.sqrt_pos_of_pos hpos
    have hge : (1 : ℝ) ≤ (Nat.gcd v.natAbs c : ℝ) := by
      have hpos' : 0 < Nat.gcd v.natAbs c := Nat.gcd_pos_of_pos_right _ hcpos
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpos'.ne'
    have h1 : Real.sqrt (Nat.gcd v.natAbs c : ℝ) ≤ (Nat.gcd v.natAbs c : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr hge)
    simp only [G, K]
    exact div_le_div_of_nonneg_right h1 hspos.le
  have hfac : ∀ h1 ∈ zPz X,
      (∑ v1 ∈ zPz S, ∑ v2 ∈ zPz S, T ^ 2 * (F h1 * (G v1 * K v2)))
        = T ^ 2 * F h1 * ((∑ v1 ∈ zPz S, G v1) * (∑ v2 ∈ zPz S, K v2)) := by
    intro h1 _
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro v1 _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro v2 _
    ring
  calc (∑ h1 ∈ zPz X, ∑ v1 ∈ zPz S, ∑ v2 ∈ zPz S,
        (((Finset.univ : Finset (ZMod c)).filter
            (fun z => (v2 : ZMod c) * z ^ 2 = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
          / ((max v1.natAbs v2.natAbs : ℕ) : ℝ))
      ≤ ∑ h1 ∈ zPz X, ∑ v1 ∈ zPz S, ∑ v2 ∈ zPz S, T ^ 2 * (F h1 * (G v1 * K v2)) :=
        Finset.sum_le_sum (fun h1 hh1 => Finset.sum_le_sum (fun v1 hv1 =>
          Finset.sum_le_sum (fun v2 hv2 => hpt h1 hh1 v1 hv1 v2 hv2)))
    _ = ∑ h1 ∈ zPz X, T ^ 2 * F h1 * ((∑ v1 ∈ zPz S, G v1) * (∑ v2 ∈ zPz S, K v2)) :=
        Finset.sum_congr rfl hfac
    _ = T ^ 2 * (∑ h1 ∈ zPz X, F h1) * ((∑ v1 ∈ zPz S, G v1) * (∑ v2 ∈ zPz S, K v2)) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ T ^ 2 * (2 * (X : ℝ) * T)
          * ((4 * Real.sqrt (S : ℝ) * T) * (4 * Real.sqrt (S : ℝ) * T)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hF (by positivity))
          (mul_le_mul hG hK (by positivity) (by positivity)) (by positivity) (by positivity)
    _ = 32 * (X : ℝ) * (S : ℝ) * T ^ 5 := by
        rw [show (4 * Real.sqrt (S : ℝ) * T) * (4 * Real.sqrt (S : ℝ) * T)
            = 16 * (Real.sqrt (S : ℝ)) ^ 2 * T ^ 2 from by ring]
        rw [Real.sq_sqrt hS0]
        ring
    _ ≤ 64 * (X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5 := by
        have hT : T = (c.divisors.card : ℝ) := rfl
        rw [hT]
        have h0 : (0 : ℝ) ≤ (X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5 := by positivity
        calc 32 * (X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5
            = 32 * ((X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5) := by ring
          _ ≤ 64 * ((X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5) :=
              mul_le_mul_of_nonneg_right (by norm_num) h0
          _ = 64 * (X : ℝ) * (S : ℝ) * ((c.divisors.card : ℝ)) ^ 5 := by ring

end

end Work.FIArea2.R6
