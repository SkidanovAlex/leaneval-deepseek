import Mathlib
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.Core.blk_sep_base

/-!
# `uni_nonres3_havoid`

The "avoidance" (separation) bound for the difference set `Dnr` of `uni_nonres3`.

For `d ≠ k` in `Dnr q n s a' b' y`, the distance of `(k - d) α` to the nearest integer is at
least `Δ (n-1) / 16`.  Since `Δ (n-1) = fracDist (q (n-1) · α)` and `Δ (n-1) < 1 / q n`, it
suffices to prove

* `1 / (2 q n) ≤ fracDist (m α)` whenever `0 < |m| < q n` — the CF-rigidity bound, whose
  low range `|m| < q 0` is `blk_sep_base` and whose high range comes from `hbest`+`hΔlo`;
* in the remaining range `q n ≤ |m|`, the Euclidean decomposition `m = M q n + t` reduces the
  distance to that of the nonzero remainder `t = m % q n ∈ (0, q n)`, at the cost
  `(|m| / q n + 1) Δ n ≤ 1/(4 q n) + 3/(2 q(n+1))` produced by `hyr`/`hTn`/`hΔup`; the
  elementary `max`-arithmetic then yields `1/(16 q n)`.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core

noncomputable section

/-- Subadditivity of `fracDist` (distance to the nearest integer). -/
theorem fracDist_add_le (a b : ℝ) : fracDist (a + b) ≤ fracDist a + fracDist b := by
  have := Basic.nn_add_le a b
  simpa [Basic.nn, fracDist] using this

/-- Reverse triangle inequality: `fracDist (a + b) - fracDist b ≤ fracDist a`. -/
theorem fracDist_sub_le (a b : ℝ) : fracDist (a + b) - fracDist b ≤ fracDist a := by
  linarith [fracDist_add_le a b]

/-- `fracDist (n * u) ≤ n * fracDist u` for `n : ℕ`. -/
theorem fracDist_nsmul_le (n : ℕ) (u : ℝ) :
    fracDist ((n : ℝ) * u) ≤ (n : ℝ) * fracDist u := by
  induction n with
  | zero => simp [fracDist]
  | succ k ih =>
    have hcast : (((k + 1 : ℕ) : ℝ)) * u = (k : ℝ) * u + u := by push_cast; ring
    rw [hcast]
    calc fracDist ((k : ℝ) * u + u) ≤ fracDist ((k : ℝ) * u) + fracDist u := fracDist_add_le _ _
      _ ≤ (k : ℝ) * fracDist u + fracDist u := by linarith [ih]
      _ = ((k + 1 : ℕ) : ℝ) * fracDist u := by push_cast; ring

/-- `fracDist` is even: `|(-u) - round (-u)| = |u - round u|` (the two nearest integers
differ by a sign; ties are harmless for the distance). -/
theorem fracDist_neg (x : ℝ) : fracDist (-x) = fracDist x := by
  have hL : |-x - (round (-x) : ℝ)| ≤ |x - (round x : ℝ)| := by
    have h := round_le (-x) (-(round x))
    rwa [show -x - ((-(round x) : ℤ) : ℝ) = -(x - (round x : ℝ)) by push_cast; ring, abs_neg] at h
  have hR : |x - (round x : ℝ)| ≤ |-x - (round (-x) : ℝ)| := by
    have h := round_le x (-(round (-x)))
    rwa [show x - ((-(round (-x)) : ℤ) : ℝ) = -(-x - (round (-x) : ℝ)) by push_cast; ring,
      abs_neg] at h
  simpa only [fracDist] using le_antisymm hL hR

/-- `fracDist (M * u) ≤ |M| * fracDist u` for `M : ℤ` (from the `ℕ` case and evenness). -/
theorem fracDist_zmul_le (M : ℤ) (u : ℝ) :
    fracDist ((M : ℝ) * u) ≤ |(M : ℝ)| * fracDist u := by
  cases M with
  | ofNat n =>
    rw [show ((Int.ofNat n : ℤ) : ℝ) = (n : ℝ) from rfl, abs_of_nonneg (by positivity)]
    exact fracDist_nsmul_le n u
  | negSucc n =>
    have hcast : ((Int.negSucc n : ℤ) : ℝ) = -(((n : ℕ) : ℝ) + 1) := by
      push_cast [Int.negSucc]; ring
    have hneg : -(((n : ℕ) : ℝ) + 1) < 0 := by
      have hn := Nat.cast_nonneg n (α := ℝ); linarith
    rw [hcast, abs_of_neg hneg, neg_mul, fracDist_neg]
    have h2 : (((n : ℕ) : ℝ) + 1) = (((n + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [h2, neg_neg]
    exact fracDist_nsmul_le (n + 1) u

/-- The lower bound half of the triangle inequality for `fracDist`:
`fracDist a - fracDist b ≤ fracDist (a + b)`. -/
theorem le_fracDist_add (a b : ℝ) : fracDist a - fracDist b ≤ fracDist (a + b) := by
  have h := fracDist_add_le (a + b) (-b)
  rw [add_neg_cancel_right, fracDist_neg] at h
  linarith

/-- **The digit decomposition.**  If `m = M * qₙ + t` then
`fracDist (t α) - |M| · fracDist (qₙ α) ≤ fracDist (m α)`: the `ℤ`-multiples of `qₙ α` are the
coarse corrections to `t α`. -/
theorem fracDist_int_decomp {α : ℝ} {qn : ℤ} {m M t : ℤ} (h : m = M * qn + t) :
    fracDist ((t : ℝ) * α) - |(M : ℝ)| * fracDist ((qn : ℝ) * α)
      ≤ fracDist ((m : ℝ) * α) := by
  have hm : (m : ℝ) * α = (t : ℝ) * α + (M : ℝ) * ((qn : ℝ) * α) := by
    rw [h]; push_cast; ring
  rw [hm]
  linarith [le_fracDist_add ((t : ℝ) * α) ((M : ℝ) * ((qn : ℝ) * α)),
    fracDist_zmul_le M ((qn : ℝ) * α)]

/-- **Cases (a)+(b) of the difference bound.**  If `q m' ≤ k < q (m'+1)` with `m' + 1 ≤ n`,
then `fracDist (k α) ≥ 1/(2 q n)`: `hbest` gives `Δ m'`, `hΔlo` turns `Δ m'` into
`1/(q(m'+1) + q m')`, and `hmono` compares `q (m'+1)` with `q n`.  This covers every nonzero
difference `1 ≤ k < q n` whose scale index `m'` exists (i.e. `k ≥ q 0`). -/
theorem fracDist_nat_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n m' k : ℕ} (hm' : m' + 1 ≤ n) (h1 : q m' ≤ k) (h2 : k < q (m' + 1)) :
    1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((k : ℝ) * α) := by
  have hbest' : Δ m' ≤ Work.TMC16Core.fracDist ((k : ℝ) * α) := hbest m' k h1 h2
  have hlo : 1 / (((q (m' + 1) : ℝ)) + (q m' : ℝ)) < Δ m' := hΔlo m'
  have hle : ((q (m' + 1) : ℕ) : ℝ) ≤ ((q n : ℕ) : ℝ) := by
    exact_mod_cast hmono.monotone hm'
  have hpos : (0 : ℝ) < ((q (m' + 1) : ℕ) : ℝ) := by exact_mod_cast hqpos (m' + 1)
  have hposn : (0 : ℝ) < ((q n : ℕ) : ℝ) := by exact_mod_cast hqpos n
  have hmono' : ((q m' : ℕ) : ℝ) ≤ ((q (m' + 1) : ℕ) : ℝ) := by
    exact_mod_cast (hmono (Nat.lt_succ_self m')).le
  have hkey1 : 1 / (2 * ((q n : ℕ) : ℝ)) ≤ 1 / (2 * ((q (m' + 1) : ℕ) : ℝ)) :=
    one_div_le_one_div_of_le (by linarith [hpos]) (by linarith [hle])
  have hkey2 : 1 / (2 * ((q (m' + 1) : ℕ) : ℝ)) ≤
      1 / (((q (m' + 1) : ℕ) : ℝ) + ((q m' : ℕ) : ℝ)) :=
    one_div_le_one_div_of_le (by linarith [hpos, hmono']) (by linarith [hmono'])
  calc 1 / (2 * ((q n : ℕ) : ℝ)) ≤ 1 / (2 * ((q (m' + 1) : ℕ) : ℝ)) := hkey1
    _ ≤ 1 / (((q (m' + 1) : ℕ) : ℝ) + ((q m' : ℕ) : ℝ)) := hkey2
    _ ≤ Δ m' := le_of_lt hlo
    _ ≤ Work.TMC16Core.fracDist ((k : ℝ) * α) := hbest'

/-- **The quotient bound of the `ediv`/`emod` split.**  Writing `m = M qₙ + t` with
`M = m / qₙ` and `t = m % qₙ ∈ [0, qₙ)`, one has `|M| ≤ |m|/qₙ + 1`: indeed
`|M| · qₙ = |M qₙ| = |m − t| ≤ |m| + |t| ≤ |m| + qₙ`. -/
theorem ediv_abs_le {qn : ℕ} (hqn : 0 < qn) (m : ℤ) :
    |(((m / (qn : ℤ)) : ℤ) : ℝ)| ≤ |(m : ℝ)| / (qn : ℝ) + 1 := by
  set M : ℤ := m / (qn : ℤ) with hMdef
  set t : ℤ := m % (qn : ℤ) with htdef
  have hdec : m = M * (qn : ℤ) + t := by
    rw [hMdef, htdef]
    exact (Int.ediv_mul_add_emod m (qn : ℤ)).symm
  have ht0 : 0 ≤ t := by rw [htdef]; exact Int.emod_nonneg m (by exact_mod_cast hqn.ne')
  have htq : t < (qn : ℤ) := by
    rw [htdef]; exact Int.emod_lt_of_pos m (by exact_mod_cast hqn)
  have hqnpos : (0 : ℝ) < (qn : ℝ) := by exact_mod_cast hqn
  have hMqn : (M : ℝ) * (qn : ℝ) = (m : ℝ) - (t : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hdec
    push_cast at h
    linarith
  have htabs : |(t : ℝ)| ≤ (qn : ℝ) := by
    have h0 : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
    have h1 : (t : ℝ) ≤ (qn : ℝ) := by exact_mod_cast htq.le
    rw [abs_of_nonneg h0]; exact h1
  have htri : |(m : ℝ) - (t : ℝ)| ≤ |(m : ℝ)| + |(t : ℝ)| := by
    refine abs_le.2 ⟨?_, ?_⟩
    · have h1 := neg_le_abs (m : ℝ)
      have h2 := le_abs_self (t : ℝ)
      linarith
    · have h1 := le_abs_self (m : ℝ)
      have h2 := neg_le_abs (t : ℝ)
      linarith
  have h2 : |(M : ℝ)| * (qn : ℝ) ≤ |(m : ℝ)| + (qn : ℝ) := by
    have habs : |(M : ℝ)| * (qn : ℝ) = |(m : ℝ) - (t : ℝ)| := by
      rw [← hMqn, abs_mul, abs_of_pos hqnpos]
    rw [habs]
    linarith
  have h3 : |(M : ℝ)| ≤ (|(m : ℝ)| + (qn : ℝ)) / (qn : ℝ) := by
    rw [le_div_iff₀ hqnpos]; linarith
  rwa [add_div, div_self (ne_of_gt hqnpos)] at h3

/-- **Case (c) of the difference bound.**  With `m = M qₙ + t`, `|M| ≤ B` and `Δ(n) ≤ D`
(`0 ≤ D`), the digit decomposition replaces the quotient part `|M| · Δ(n)` by `B · D`:
`fracDist (t α) - B · D ≤ fracDist (m α)`. -/
theorem fracDist_cross_bound {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    {n : ℕ} {m M t : ℤ} {B D : ℝ} (hdec : m = M * (q n : ℤ) + t)
    (hM : |(M : ℝ)| ≤ B) (hΔ : Δ n ≤ D) (hD0 : 0 ≤ D) :
    fracDist ((t : ℝ) * α) - B * D ≤ fracDist ((m : ℝ) * α) := by
  have hcast : (((q n : ℕ) : ℤ) : ℝ) = ((q n : ℕ) : ℝ) := by push_cast; ring
  have h1 : fracDist ((t : ℝ) * α) - |(M : ℝ)| * Δ n ≤ fracDist ((m : ℝ) * α) := by
    have h := fracDist_int_decomp (α := α) (qn := ((q n : ℕ) : ℤ)) (m := m) (M := M) (t := t) hdec
    rw [hcast, ← hΔeq n] at h
    exact h
  have hΔn0 : 0 ≤ Δ n := by rw [hΔeq n]; simp only [fracDist]; exact abs_nonneg _
  have h2 : |(M : ℝ)| * Δ n ≤ B * D := by
    nlinarith [abs_nonneg (M : ℝ)]
  linarith
/-- **The arithmetic core of the `X`-max step.**  With `δ ≥ 1/(2 qn)`, `Δn ≥ 1/(2 qn1)` and
`D ≤ 1/(4 qn) + 3/(2 qn1)` (the coefficient produced by `ediv_abs_le`), the larger of the crude
bound `Δn` and the decomposed bound `δ - D` is at least `1/(16 qn)`.

The regimes are `qn1 < 8 qn`, where the crude bound alone wins, and `qn1 ≥ 8 qn`, where the two
bounds cannot both be small.  All the algebra is done by multiplying by the positive variables
`qn` then `qn1` and cancelling (`mul_div_mul_left`), since every expression is a reciprocal of a
variable and `linarith` alone cannot handle those. -/
theorem max_delta_arith {qn qn1 δ Δn D : ℝ}
    (hqn : 0 < qn) (hqn1 : 0 < qn1)
    (hδ : 1 / (2 * qn) ≤ δ) (hΔ1 : 1 / (2 * qn1) ≤ Δn)
    (hD : D ≤ 1 / (4 * qn) + 3 / (2 * qn1)) :
    1 / (16 * qn) ≤ max Δn (δ - D) := by
  have hmaxδ : δ - D ≤ max Δn (δ - D) := le_max_right _ _
  have hmaxΔ : Δn ≤ max Δn (δ - D) := le_max_left _ _
  by_cases h : 8 * qn ≤ qn1
  · by_contra hcon
    rw [not_le] at hcon
    have hb2 : δ - D < 1 / (16 * qn) := lt_of_le_of_lt hmaxδ hcon
    have h1 : δ < 1 / (16 * qn) + (1 / (4 * qn) + 3 / (2 * qn1)) := by linarith
    have h2 : 1 / (2 * qn) < 1 / (16 * qn) + (1 / (4 * qn) + 3 / (2 * qn1)) :=
      lt_of_le_of_lt hδ h1
    have hcontra : qn1 < 8 * qn := by
      -- multiply by qn
      have hmul := mul_lt_mul_of_pos_left h2 hqn
      rw [mul_add, mul_add] at hmul
      have a1 : qn * (1 / (2 * qn)) = 1 / 2 := by
        rw [mul_one_div, mul_comm 2 qn]
        simpa using mul_div_mul_left (1 : ℝ) (2 : ℝ) (ne_of_gt hqn)
      have a2 : qn * (1 / (16 * qn)) = 1 / 16 := by
        rw [mul_one_div, mul_comm 16 qn]
        simpa using mul_div_mul_left (1 : ℝ) (16 : ℝ) (ne_of_gt hqn)
      have a3 : qn * (1 / (4 * qn)) = 1 / 4 := by
        rw [mul_one_div, mul_comm 4 qn]
        simpa using mul_div_mul_left (1 : ℝ) (4 : ℝ) (ne_of_gt hqn)
      rw [a1, a2, a3] at hmul
      -- hmul : 1/2 < 1/16 + (1/4 + qn * (3/(2 qn1)))
      have h3 : 3 / 16 < qn * (3 / (2 * qn1)) := by linarith
      -- multiply by qn1
      have hmul2 := mul_lt_mul_of_pos_left h3 hqn1
      have b1 : qn1 * (3 / 16) = 3 * qn1 / 16 := by ring
      have b2 : qn1 * (qn * (3 / (2 * qn1))) = 3 * qn / 2 := by
        rw [show qn1 * (qn * (3 / (2 * qn1))) = (3 * qn) * qn1 / (2 * qn1) by ring,
          mul_div_mul_right (3 * qn) 2 (ne_of_gt hqn1)]
      rw [b1, b2] at hmul2
      linarith
    linarith
  · rw [not_le] at h
    have h16 : 1 / (16 * qn) < 1 / (2 * qn1) := by
      apply one_div_lt_one_div_of_lt (by positivity : (0:ℝ) < 2 * qn1)
      linarith
    exact le_trans h16.le (le_trans hΔ1 hmaxΔ)

/-- **The ℤ→ℕ bridge.**  `fracDist (m α)` depends only on `|m|`, so every bound proved for a
natural number `k` applies to the integer difference `±k`. -/
theorem fracDist_int_abs (α : ℝ) (m : ℤ) :
    fracDist ((m : ℝ) * α) = fracDist (((m.natAbs : ℕ) : ℝ) * α) := by
  cases m with
  | ofNat n => rfl
  | negSucc n =>
    have hnat : (((Int.negSucc n).natAbs : ℕ) : ℝ) = ((n : ℝ) + 1) := by
      rw [show (Int.negSucc n).natAbs = n + 1 from rfl]
      push_cast
      ring
    have hcast : ((Int.negSucc n : ℤ) : ℝ) = -(((n : ℕ) : ℝ) + 1) := by
      push_cast [Int.negSucc]; ring
    rw [hcast, hnat]
    rw [show -(((n : ℕ) : ℝ) + 1) * α = -((((n : ℕ) : ℝ) + 1) * α) by ring, fracDist_neg]

/-- `1/(2 q(n+1)) ≤ Δ n`, from `hΔlo` and `q n ≤ q(n+1)`. -/
theorem half_q_succ_le_Delta {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ}
    (hq1 : 0 < q (n + 1))
    (hΔlo : 1 / (((q (n + 1) : ℝ)) + (q n : ℝ)) < Δ n)
    (hle : ((q n : ℕ) : ℝ) ≤ ((q (n + 1) : ℕ) : ℝ)) :
    1 / (2 * (q (n + 1) : ℝ)) ≤ Δ n := by
  have hpos2 : (0 : ℝ) < ((q (n + 1) : ℕ) : ℝ) + ((q n : ℕ) : ℝ) := by
    have := hq1; positivity
  have h1 : 1 / (2 * ((q (n + 1) : ℕ) : ℝ)) ≤
      1 / (((q (n + 1) : ℕ) : ℝ) + ((q n : ℕ) : ℝ)) := by
    apply one_div_le_one_div_of_le hpos2
    linarith
  exact le_trans h1 hΔlo.le
/-- **The difference bound for `|m| ≥ qₙ`.**  Assembled from `ediv_abs_le` (the quotient bound
of the `ediv`/`emod` split), `fracDist_cross_bound` (the digit bound) and `max_delta_arith` (the
`X`-max step).  The caller supplies the remainder bound `hδ`, the crude bound `hcrude`
(`Δ n ≤ fracDist (m α)` when `qₙ ≤ |m| < q(n+1)`) and the coefficient bound `hD`. -/
theorem fracDist_large_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hmono : StrictMono q)
    (hΔeq : ∀ k, Δ k = fracDist ((q k : ℝ) * α))
    {n : ℕ} (hqn : 0 < q n) (hqn1 : 0 < q (n + 1))
    (hΔlo : 1 / (((q (n + 1) : ℝ)) + (q n : ℝ)) < Δ n)
    {m : ℤ}
    (hδ : 1 / (2 * (q n : ℝ)) ≤ fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α))
    (hcrude : Δ n ≤ fracDist ((m : ℝ) * α))
    (hD : (|(m : ℝ)| / (q n : ℝ) + 1) * Δ n ≤
      1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ))) :
    1 / (16 * (q n : ℝ)) ≤ fracDist ((m : ℝ) * α) := by
  have hle : ((q n : ℕ) : ℝ) ≤ ((q (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast (hmono (Nat.lt_succ_self n)).le
  have hΔn1 : 1 / (2 * (q (n + 1) : ℝ)) ≤ Δ n := half_q_succ_le_Delta hqn1 hΔlo hle
  have hΔn0 : 0 ≤ Δ n := by
    rw [hΔeq n]; simp only [fracDist]; exact abs_nonneg _
  have hdec : m = (m / (q n : ℤ)) * (q n : ℤ) + m % (q n : ℤ) :=
    (Int.ediv_mul_add_emod m (q n : ℤ)).symm
  have hM : |(((m / (q n : ℤ)) : ℤ) : ℝ)| ≤ |(m : ℝ)| / (q n : ℝ) + 1 := ediv_abs_le hqn m
  have hcross : fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α) -
      (|(m : ℝ)| / (q n : ℝ) + 1) * Δ n ≤ fracDist ((m : ℝ) * α) :=
    fracDist_cross_bound hΔeq hdec hM le_rfl hΔn0
  have hmax : 1 / (16 * (q n : ℝ)) ≤
      (max (Δ n) (fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α) -
        (1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ)))) : ℝ) :=
    max_delta_arith (by exact_mod_cast hqn) (by exact_mod_cast hqn1) hδ hΔn1 le_rfl
  have h2 : fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α) -
      (1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ))) ≤ fracDist ((m : ℝ) * α) := by
    have hBD : (|(m : ℝ)| / (q n : ℝ) + 1) * Δ n ≤
        1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ)) := hD
    have hc := hcross
    linarith
  have hmax2 : max (Δ n) (fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α) -
      (1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ)))) ≤ fracDist ((m : ℝ) * α) :=
    max_le hcrude h2
  linarith [hmax, hmax2]

/-- **Discharge of `hδ` in `fracDist_large_ge`.**  The remainder `t = m % qₙ` (with `0 < t`)
obeys the `1/(2 qₙ)` bound as soon as its scale index `m'` is known: `fracDist_int_abs` moves
`t` to the natural number `t.toNat` and `fracDist_nat_ge` does the rest. -/
theorem emod_bound_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n : ℕ} {t : ℤ} (ht0 : 0 < t)
    {m' : ℕ} (hm' : m' + 1 ≤ n) (h1 : q m' ≤ t.toNat) (h2 : t.toNat < q (m' + 1)) :
    1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((t : ℝ) * α) := by
  rw [fracDist_int_abs α t]
  have htoNat : t.natAbs = t.toNat := by
    have h1' : ((t.natAbs : ℕ) : ℤ) = t := Int.natAbs_of_nonneg ht0.le
    have h2' : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht0.le
    exact_mod_cast (h1'.trans h2'.symm)
  rw [htoNat]
  exact fracDist_nat_ge hqpos hmono hΔlo hbest hm' h1 h2
/-- **Discharge of `hD` in `fracDist_large_ge`** (the coefficient bound).  From `hyr`
(`4|y| ≤ q(n+1)`), `hTn` (`2 s q(n-1) ≤ qₙ`), `hΔup` (`Δ n < 1/q(n+1)`) and
`|m| ≤ |y| + s q(n-1)`: `(|m|/qₙ + 1)·Δ n ≤ 1/(4qₙ) + 3/(2q(n+1))`. -/
theorem coeff_bound {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n s : ℕ} {m y : ℤ}
    (hqn : 0 < q n) (hqn1 : 0 < q (n + 1))
    (hΔup : Δ n < 1 / ((q (n + 1) : ℝ))) (hΔn0 : 0 ≤ Δ n)
    (hTn : 2 * s * q (n - 1) ≤ q n)
    (hyr : 4 * |y| ≤ (q (n + 1) : ℤ))
    (hm : |(m : ℝ)| ≤ |(y : ℝ)| + (s : ℝ) * (q (n - 1) : ℝ)) :
    (|(m : ℝ)| / (q n : ℝ) + 1) * Δ n ≤
      1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ)) := by
  have hy : |(y : ℝ)| ≤ (q (n + 1) : ℝ) / 4 := by
    have hcast : (4 : ℝ) * |(y : ℝ)| ≤ ((q (n + 1) : ℕ) : ℝ) := by exact_mod_cast hyr
    linarith
  have hT : (s : ℝ) * (q (n - 1) : ℝ) ≤ (q n : ℝ) / 2 := by
    have hcast : 2 * (s : ℝ) * (q (n - 1) : ℝ) ≤ ((q n : ℕ) : ℝ) := by exact_mod_cast hTn
    linarith
  have hm' : |(m : ℝ)| ≤ (q (n + 1) : ℝ) / 4 + (q n : ℝ) / 2 := by linarith
  have hcoef : |(m : ℝ)| / (q n : ℝ) + 1 ≤
      (q (n + 1) : ℝ) / (4 * (q n : ℝ)) + 3 / 2 := by
    have h1 : |(m : ℝ)| / (q n : ℝ) ≤
        ((q (n + 1) : ℝ) / 4 + (q n : ℝ) / 2) / (q n : ℝ) :=
      div_le_div_of_nonneg_right hm' (by positivity : (0 : ℝ) ≤ ((q n : ℕ) : ℝ))
    have h2 : ((q (n + 1) : ℝ) / 4 + (q n : ℝ) / 2) / (q n : ℝ) =
        (q (n + 1) : ℝ) / (4 * (q n : ℝ)) + 1 / 2 := by
      field_simp
    linarith
  have hkey : (|(m : ℝ)| / (q n : ℝ) + 1) * Δ n ≤
      ((q (n + 1) : ℝ) / (4 * (q n : ℝ)) + 3 / 2) * (1 / (q (n + 1) : ℝ)) :=
    mul_le_mul hcoef (le_of_lt hΔup) hΔn0 (by positivity)
  have hval : ((q (n + 1) : ℝ) / (4 * (q n : ℝ)) + 3 / 2) * (1 / (q (n + 1) : ℝ)) =
      1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ)) := by
    field_simp
  linarith

/-- **Discharge of `hcrude` in `fracDist_large_ge`.**  In the regime `qₙ ≤ |m| < q(n+1)`,
`hbest` at scale `n` bounds `Δ n` by `fracDist (k α)` for `k = |m|`, and `fracDist_int_abs`
transfers that to the integer `m`. -/
theorem delta_le_fracDist {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n : ℕ} {m : ℤ} (h1 : q n ≤ m.natAbs) (h2 : m.natAbs < q (n + 1)) :
    Δ n ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) := by
  have h := hbest n m.natAbs h1 h2
  rwa [fracDist_int_abs α m]

/-- **The `|m| < qₙ` case of the difference bound**, in the regime where the scale index `m'` of
`|m|` exists (`q m' ≤ |m| < q(m'+1)`, `m' + 1 ≤ n`): `fracDist_nat_ge` gives `1/(2 qₙ)` for the
natural number `m.natAbs` and `fracDist_int_abs` transfers it to the integer `m`; then
`1/(16 qₙ) ≤ 1/(2 qₙ)`.  (The differences with `|m| < q(0)` are covered by the base case.) -/
theorem fracDist_small_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n m' : ℕ} (hm' : m' + 1 ≤ n) {m : ℤ}
    (h1 : q m' ≤ m.natAbs) (h2 : m.natAbs < q (m' + 1)) :
    1 / (16 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) := by
  have h := fracDist_nat_ge hqpos hmono hΔlo hbest hm' h1 h2
  rw [← fracDist_int_abs α m] at h
  have hq : (0 : ℝ) < ((q n : ℕ) : ℝ) := by
    have := hqpos n; exact_mod_cast this
  have h16 : 1 / (16 * ((q n : ℕ) : ℝ)) ≤ 1 / (2 * ((q n : ℕ) : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  linarith
/-- **Structural bound on the differences.**  For `t, d ∈ Dnr` the difference obeys
`|t - d| ≤ |y| + s q(n-1)`: the two windows have half-width `a' q(n-1)` and `b' q(n-1)` about
`-1/2` and `y-1/2`, and `a' + b' = s`. -/
theorem Dnr_sub_abs_le {q : ℕ → ℕ} {n s a' b' : ℕ} {y d t : ℤ}
    (hab : a' + b' = s) (hy : (s : ℤ) * (q (n - 1) : ℤ) ≤ y)
    (hd : d ∈ Dnr q n s a' b' y) (ht : t ∈ Dnr q n s a' b' y) :
    |t - d| ≤ |y| + (s : ℤ) * (q (n - 1) : ℤ) := by
  have hy0 : 0 ≤ y := le_trans (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) hy
  have habZ : ((a' : ℤ) + (b' : ℤ)) = (s : ℤ) := by exact_mod_cast hab
  have hL : (0 : ℤ) ≤ (q (n - 1) : ℤ) := Int.natCast_nonneg _
  have ha' : (a' : ℤ) ≤ (s : ℤ) := by omega
  have hb' : (b' : ℤ) ≤ (s : ℤ) := by omega
  have haL : (a' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right ha' hL
  have hbL : (b' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right hb' hL
  have hbL0 : (0 : ℤ) ≤ (b' : ℤ) * (q (n - 1) : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) hL
  have hsum : (a' : ℤ) * (q (n - 1) : ℤ) + (b' : ℤ) * (q (n - 1) : ℤ) =
      (s : ℤ) * (q (n - 1) : ℤ) := by
    rw [← add_mul, habZ]
  simp only [Dnr, Finset.mem_union, Finset.mem_Icc] at hd ht
  rw [abs_of_nonneg hy0, abs_le]
  rcases hd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩ <;>
    rcases ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩ <;> constructor <;> omega

/-- **Second structural bound on the differences**: `|t - d| < q(n+1)` for `t, d ∈ Dnr`, from
`|t-d| ≤ |y| + s q(n-1)`, `4|y| ≤ q(n+1)` (`hyr`), `2 s q(n-1) ≤ q n` (`hTn`) and `q n < q(n+1)`. -/
theorem Dnr_sub_lt_qsucc {q : ℕ → ℕ} {n s a' b' : ℕ} {y d t : ℤ}
    (hmono : StrictMono q) (hqn1 : 0 < q (n + 1))
    (hTn : 2 * s * q (n - 1) ≤ q n)
    (hyr : 4 * |y| ≤ (q (n + 1) : ℤ))
    (hab : a' + b' = s) (hy : (s : ℤ) * (q (n - 1) : ℤ) ≤ y)
    (hd : d ∈ Dnr q n s a' b' y) (ht : t ∈ Dnr q n s a' b' y) :
    |t - d| < (q (n + 1) : ℤ) := by
  have habs := Dnr_sub_abs_le hab hy hd ht
  have h4 : 4 * |y| ≤ (q (n + 1) : ℤ) := hyr
  have h2s : 2 * (s : ℤ) * (q (n - 1) : ℤ) ≤ (q n : ℤ) := by exact_mod_cast hTn
  have h2s' : 4 * ((s : ℤ) * (q (n - 1) : ℤ)) ≤ 2 * (q n : ℤ) := by linarith
  have hmono' : q n < q (n + 1) := hmono (Nat.lt_succ_self n)
  have hQ : (0 : ℤ) < (q (n + 1) : ℤ) := by exact_mod_cast hqn1
  have hkey : 4 * |t - d| < 4 * (q (n + 1) : ℤ) := by
    have h := habs
    nlinarith [h4, h2s', hmono']
  linarith
/-- The bridge between the rate produced by the difference bound (`1/(16 qₙ)`) and the step
scale used by `blkmin_sum_step` (`Δ(n-1)/16`): `hΔup` (`Δ(n-1) < 1/qₙ`) gives it. -/
theorem delta_pred_div_le {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ}
    (hΔup : Δ (n - 1) < 1 / ((q n : ℝ))) :
    Δ (n - 1) / 16 ≤ 1 / (16 * (q n : ℝ)) := by
  have h1 : Δ (n - 1) / 16 ≤ (1 / ((q n : ℝ))) / 16 :=
    div_le_div_of_nonneg_right hΔup.le (by norm_num)
  have h2 : (1 / ((q n : ℝ))) / 16 = 1 / (16 * (q n : ℝ)) := by
    rw [div_div, mul_comm]
  linarith

/-- **Window bound**: for a natural `z` lying in the window `[q 0, q N)` the distance
`fracDist (z α)` is at least `1/(2 q N)`: choose the block index `m'` with
`q m' ≤ z < q (m'+1)`; then `m' + 1 ≤ N`, `hΔlo` bounds `Δ m'` below by
`1/(q(m'+1)+q(m'))` and `hmono` bounds `q(m'+1) + q(m') ≤ 2 q N`. -/
theorem fracDist_window_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {N z : ℕ} (h0 : q 0 ≤ z) (hz : z < q N) :
    1 / (2 * (q N : ℝ)) ≤ Work.TMC16Core.fracDist ((z : ℝ) * α) := by
  obtain ⟨m', h1, h2⟩ := exists_block hmono h0
  have hm' : m' + 1 ≤ N := by
    have hlt : m' < N := by
      by_contra h
      push_neg at h
      have := hmono.monotone h
      omega
    omega
  have hbest' : Δ m' ≤ Work.TMC16Core.fracDist ((z : ℝ) * α) := hbest m' z h1 h2
  have hlo : 1 / (((q (m' + 1) : ℝ)) + (q m' : ℝ)) < Δ m' := hΔlo m'
  have hle : ((q (m' + 1) : ℕ) : ℝ) ≤ ((q N : ℕ) : ℝ) := by
    exact_mod_cast hmono.monotone hm'
  have hle' : ((q m' : ℕ) : ℝ) ≤ ((q N : ℕ) : ℝ) := by
    exact_mod_cast hmono.monotone (le_trans (Nat.le_succ m') hm')
  have hpos : (0 : ℝ) < ((q N : ℕ) : ℝ) := by
    have := hqpos N; exact_mod_cast this
  have hpos' : (0 : ℝ) < ((q (m' + 1) : ℕ) : ℝ) := by
    have := hqpos (m' + 1); exact_mod_cast this
  have hkey : 1 / (2 * ((q N : ℕ) : ℝ)) ≤
      1 / (((q (m' + 1) : ℕ) : ℝ) + ((q m' : ℕ) : ℝ)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  calc 1 / (2 * ((q N : ℕ) : ℝ))
      ≤ 1 / (((q (m' + 1) : ℕ) : ℝ) + ((q m' : ℕ) : ℝ)) := hkey
    _ ≤ Δ m' := le_of_lt hlo
    _ ≤ Work.TMC16Core.fracDist ((z : ℝ) * α) := hbest'

/-- **Small differences**: for `1 ≤ |m| < q(n-1)` the distance `fracDist (m α)` is at least
`1/(2 q(n-1))`.  For `|m| < q 0` this is the base case `blk_sep_base`; for `q 0 ≤ |m|` it is
`fracDist_window_ge` with `N := n - 1`. -/
theorem small_diff_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n : ℕ} (hn : 2 ≤ n) {m : ℤ} (hm0 : m ≠ 0) (hmlt : m.natAbs < q (n - 1)) :
    1 / (2 * (q (n - 1) : ℝ)) ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) := by
  have hz1 : 1 ≤ m.natAbs := by
    rcases Nat.eq_zero_or_pos m.natAbs with h | h
    · exact absurd (Int.natAbs_eq_zero.mp h) hm0
    · exact h
  rw [fracDist_int_abs α m]
  have hN : 1 ≤ n - 1 := by omega
  have hq0lt : q 0 < q (n - 1) := by
    have := hmono (show 0 < n - 1 by omega)
    exact this
  by_cases hzq : m.natAbs < q 0
  · have hb := blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest m.natAbs hz1 hzq
    have hle : 1 / (2 * (q (n - 1) : ℝ)) ≤ 1 / (2 * (q 0 : ℝ)) := by
      apply one_div_le_one_div_of_le (by have h := hqpos 0; push_cast; positivity)
      have : ((q 0 : ℕ) : ℝ) ≤ ((q (n - 1) : ℕ) : ℝ) := by
        exact_mod_cast (le_of_lt hq0lt)
      linarith
    exact le_trans hle hb
  · push_neg at hzq
    exact fracDist_window_ge hqpos hmono hΔlo hbest hzq hmlt

/-- **The difference `t - d` is never a multiple of `qₙ`** for `t, d ∈ Dnr`, `t ≠ d`: within one
window `|t-d| ≤ 2a'q(n-1) - 1 < qₙ` (resp. `2b'q(n-1) - 1`) by `hTn`, so `M qₙ = t - d` forces
`M = 0` and `t = d`; across the windows `t - d = y + (β - α)` with `|β - α| ≤ s q(n-1) - 1`, so a
multiple of `qₙ` would put `y` within `s q(n-1)` of the lattice, contradicting `hnonres`. -/
theorem sub_not_multiple {q : ℕ → ℕ} {n s a' b' : ℕ} {y d t : ℤ}
    (hab : a' + b' = s) (hTn : 2 * s * q (n - 1) ≤ q n)
    (hqn : (0 : ℤ) < (q n : ℤ))
    (hnonres : ∀ j : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - j * (q n : ℤ)|)
    (hd : d ∈ Dnr q n s a' b' y) (ht : t ∈ Dnr q n s a' b' y) (hne : t ≠ d) :
    ∀ M : ℤ, t - d ≠ M * (q n : ℤ) := by
  intro M hcon
  have habZ : ((a' : ℤ) + (b' : ℤ)) = (s : ℤ) := by exact_mod_cast hab
  have hTnZ : 2 * (s : ℤ) * (q (n - 1) : ℤ) ≤ (q n : ℤ) := by exact_mod_cast hTn
  have hL0 : (0 : ℤ) ≤ (q (n - 1) : ℤ) := Int.natCast_nonneg _
  have ha' : (a' : ℤ) ≤ (s : ℤ) := by omega
  have hb' : (b' : ℤ) ≤ (s : ℤ) := by omega
  have haL : (a' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right ha' hL0
  have hbL : (b' : ℤ) * (q (n - 1) : ℤ) ≤ (s : ℤ) * (q (n - 1) : ℤ) :=
    mul_le_mul_of_nonneg_right hb' hL0
  have hsum : (a' : ℤ) * (q (n - 1) : ℤ) + (b' : ℤ) * (q (n - 1) : ℤ) =
      (s : ℤ) * (q (n - 1) : ℤ) := by rw [← add_mul, habZ]
  have hsum_le : (a' : ℤ) * (q (n - 1) : ℤ) + (b' : ℤ) * (q (n - 1) : ℤ) ≤
      (s : ℤ) * (q (n - 1) : ℤ) := le_of_eq hsum
  have hsum_ge : (s : ℤ) * (q (n - 1) : ℤ) ≤
      (a' : ℤ) * (q (n - 1) : ℤ) + (b' : ℤ) * (q (n - 1) : ℤ) := ge_of_eq hsum
  have key : |M| * (q n : ℤ) = |t - d| := by
    rw [hcon, abs_mul, abs_of_pos hqn]
  have hzerocase : ∀ hlt : |t - d| < (q n : ℤ), False := by
    intro hlt
    have h1 : |M| * (q n : ℤ) < (q n : ℤ) := by rw [key]; exact hlt
    have h1' : |M| * (q n : ℤ) < 1 * (q n : ℤ) := by simpa using h1
    have h2 : |M| < 1 := by
      by_contra hb
      push_neg at hb
      have hmon : (1 : ℤ) * (q n : ℤ) ≤ |M| * (q n : ℤ) :=
        mul_le_mul_of_nonneg_right hb (le_of_lt hqn)
      omega
    have h3 : M = 0 := by
      have h4 := abs_lt.mp h2
      omega
    rw [h3, zero_mul] at hcon
    exact hne (by omega)
  simp only [Dnr, Finset.mem_union, Finset.mem_Icc] at hd ht
  rcases hd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩ <;> rcases ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
  · -- both in D1
    have hsmall : |t - d| ≤ 2 * ((a' : ℤ) * (q (n - 1) : ℤ)) - 1 := by
      rw [abs_le]; constructor <;> linarith
    have hle : 2 * ((a' : ℤ) * (q (n - 1) : ℤ)) - 1 < (q n : ℤ) := by linarith
    exact hzerocase (lt_of_le_of_lt hsmall hle)
  · -- d ∈ D1, t ∈ D2
    have hlow : -((s : ℤ) * (q (n - 1) : ℤ) - 1) ≤ d - (t - y) := by
      linarith [hd1, hd2, ht1, ht2, hsum_le, hsum_ge]
    have hup : d - (t - y) ≤ (s : ℤ) * (q (n - 1) : ℤ) - 1 := by
      linarith [hd1, hd2, ht1, ht2, hsum_le, hsum_ge]
    have habs : |d - (t - y)| ≤ (s : ℤ) * (q (n - 1) : ℤ) - 1 := abs_le.2 ⟨hlow, hup⟩
    have heq : y - M * (q n : ℤ) = d - (t - y) := by linarith [hcon]
    have hfin : |y - M * (q n : ℤ)| ≤ (s : ℤ) * (q (n - 1) : ℤ) - 1 := by
      rw [heq]; exact habs
    have := hnonres M
    omega
  · -- d ∈ D2, t ∈ D1
    have hlow : -((s : ℤ) * (q (n - 1) : ℤ) - 1) ≤ t - (d - y) := by
      linarith [hd1, hd2, ht1, ht2, hsum_le, hsum_ge]
    have hup : t - (d - y) ≤ (s : ℤ) * (q (n - 1) : ℤ) - 1 := by
      linarith [hd1, hd2, ht1, ht2, hsum_le, hsum_ge]
    have habs : |t - (d - y)| ≤ (s : ℤ) * (q (n - 1) : ℤ) - 1 := abs_le.2 ⟨hlow, hup⟩
    have heq : y + M * (q n : ℤ) = t - (d - y) := by linarith [hcon]
    have hfin : |y + M * (q n : ℤ)| ≤ (s : ℤ) * (q (n - 1) : ℤ) - 1 := by
      rw [heq]; exact habs
    have hfin' : |y - (-M) * (q n : ℤ)| ≤ (s : ℤ) * (q (n - 1) : ℤ) - 1 := by
      simpa using hfin
    have := hnonres (-M)
    omega
  · -- both in D2
    have hsmall : |t - d| ≤ 2 * ((b' : ℤ) * (q (n - 1) : ℤ)) - 1 := by
      rw [abs_le]; constructor <;> linarith
    have hle : 2 * ((b' : ℤ) * (q (n - 1) : ℤ)) - 1 < (q n : ℤ) := by linarith
    exact hzerocase (lt_of_le_of_lt hsmall hle)

/-- **The remainder of the difference is nonzero**: for `k, d ∈ Dnr`, `k ≠ d`, the Euclidean
remainder `(k - d) % qₙ` cannot vanish, since that would make `k - d` a multiple of `qₙ`
(`sub_not_multiple`). -/
theorem emod_sub_ne_zero {q : ℕ → ℕ} {n s a' b' : ℕ} {y d k : ℤ}
    (hab : a' + b' = s) (hTn : 2 * s * q (n - 1) ≤ q n)
    (hqn : (0 : ℤ) < (q n : ℤ))
    (hnonres : ∀ j : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - j * (q n : ℤ)|)
    (hd : d ∈ Dnr q n s a' b' y) (hk : k ∈ Dnr q n s a' b' y) (hne : k ≠ d) :
    (k - d) % (q n : ℤ) ≠ 0 := by
  intro hz
  have hdec : k - d = ((k - d) / (q n : ℤ)) * (q n : ℤ) := by
    have h := Int.ediv_mul_add_emod (k - d) (q n : ℤ)
    rw [hz, add_zero] at h
    linarith [h]
  exact sub_not_multiple hab hTn hqn hnonres hd hk hne ((k - d) / (q n : ℤ)) hdec

/-- **The remainder obeys the `1/(2 qₙ)` bound**: with `t = (k - d) % qₙ ∈ (0, qₙ)` the
distance `fracDist (t α)` is at least `1/(2 qₙ)`, either from the base case `blk_sep_base`
(`t < q 0`) or from the window bound `fracDist_window_ge` with `N := n`. -/
theorem emod_sub_ge {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n : ℕ} {t : ℤ} (ht0 : 0 < t) (htn : t < (q n : ℤ)) :
    1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((t : ℝ) * α) := by
  rw [fracDist_int_abs α t]
  have htoNat : t.natAbs = t.toNat := by
    have h1 : ((t.natAbs : ℕ) : ℤ) = t := Int.natAbs_of_nonneg ht0.le
    have h2 : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht0.le
    exact_mod_cast (h1.trans h2.symm)
  rw [htoNat]
  have hlt : t.toNat < q n := by
    have : (t.toNat : ℤ) < (q n : ℤ) := by rw [Int.toNat_of_nonneg ht0.le]; exact htn
    exact_mod_cast this
  by_cases hzq : t.toNat < q 0
  · have hz1 : 1 ≤ t.toNat := by
      have : (0:ℤ) < (t.toNat : ℤ) := by rw [Int.toNat_of_nonneg ht0.le]; exact ht0
      omega
    have hb := blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest t.toNat hz1 hzq
    have hq0 : (0:ℝ) < (q 0 : ℝ) := by have := hqpos 0; exact_mod_cast this
    have hle : ((q 0 : ℕ) : ℝ) ≤ ((q n : ℕ) : ℝ) := by
      exact_mod_cast (hmono.monotone (Nat.zero_le n))
    have hkey : 1 / (2 * (q n : ℝ)) ≤ 1 / (2 * (q 0 : ℝ)) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    exact le_trans hkey hb
  · push_neg at hzq
    exact fracDist_window_ge hqpos hmono hΔlo hbest hzq hlt
/-! ## The avoidance bound -/

/-- **`uni_nonres3` separation of the difference set.**  Two distinct points `d ≠ k` of `Dnr`
cannot be separated by a multiple of `q n` (`emod_sub_ne_zero`); the nonzero remainder of
`k - d` modulo `q n` is therefore at distance `≥ 1/(2 q n)` from `0` (`emod_sub_ge`), and the
Euclidean decomposition `k - d = M q n + t` converts this into the bound `1/(16 q n)`; finally
`hΔup` at `n-1` gives `Δ (n-1) / 16 < 1/(16 q n)`.  For `|k - d| < q n` the bound
`1/(2 q n) ≤ fracDist ((k-d) α)` is `emod_sub_ge` itself. -/
theorem uni_nonres3_havoid {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    {n s a' b' : ℕ} {y d k : ℤ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    (hn : 2 ≤ n) (hs : 1 ≤ s) (hab : a' + b' = s)
    (hTn : 2 * s * q (n - 1) ≤ q n)
    (hy : Work.TMC16Core.Core.Tnr q n s ≤ y)
    (hnonres : ∀ m : ℤ, Work.TMC16Core.Core.Tnr q n s ≤ |y - m * (q n : ℤ)|)
    (hyr : 4 * |y| ≤ (q (n + 1) : ℤ))
    (hd : d ∈ Work.TMC16Core.Core.Dnr q n s a' b' y)
    (hk : k ∈ Work.TMC16Core.Core.Dnr q n s a' b' y) (hne : k ≠ d) :
    Δ (n - 1) / 16 ≤ Work.TMC16Core.fracDist (((k - d : ℤ) : ℝ) * α) := by
  set m : ℤ := k - d with hm
  have hm0 : m ≠ 0 := by
    intro h
    exact hne (by omega)
  have hn1 : 1 ≤ n := by omega
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  have hqnR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  have hqnI : (0 : ℤ) < (q n : ℤ) := by exact_mod_cast hqpos n
  -- `hΔup` at `n-1`
  have hup : Δ (n - 1) < 1 / ((q n : ℝ)) := by
    have h := hΔup (n - 1)
    rwa [hsub] at h
  have hrate : Δ (n - 1) / 16 < 1 / (16 * (q n : ℝ)) := by
    have h1 : Δ (n - 1) / 16 < (1 / ((q n : ℝ))) / 16 :=
      div_lt_div_of_pos_right hup (by norm_num)
    have h2 : (1 / ((q n : ℝ))) / 16 = 1 / (16 * (q n : ℝ)) := by
      rw [div_div]; ring_nf
    linarith
  by_cases hsmall : |m| < (q n : ℤ)
  · -- `|m| < q n`
    have hge : 1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) := by
      rcases lt_trichotomy m 0 with hlt | heq | hgt
      · have ht0 : (0 : ℤ) < -m := by omega
        have htlt : -m < (q n : ℤ) := by
          have habs : |m| = -m := abs_of_neg hlt
          rw [← habs]; exact hsmall
        have h := emod_sub_ge hqpos hmono hΔpos hΔeq hΔup hΔlo hbest ht0 htlt
        have he : (m : ℝ) * α = - ((((-m : ℤ) : ℝ)) * α) := by push_cast; ring
        rw [he, fracDist_neg]
        exact h
      · exact absurd heq hm0
      · have htlt : m < (q n : ℤ) := by
          have habs : |m| = m := abs_of_pos hgt
          rw [← habs]; exact hsmall
        exact emod_sub_ge hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hgt htlt
    have h16 : 1 / (16 * (q n : ℝ)) ≤ 1 / (2 * (q n : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  · -- `q n ≤ |m|`
    push_neg at hsmall
    have hy' : (s : ℤ) * (q (n - 1) : ℤ) ≤ y := hy
    have hnonres' : ∀ j : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - j * (q n : ℤ)| :=
      fun j => hnonres j
    have hgeom : |k - d| ≤ |y| + (s : ℤ) * (q (n - 1) : ℤ) :=
      Dnr_sub_abs_le hab hy' hd hk
    have hgeom2 : |k - d| < (q (n + 1) : ℤ) :=
      Dnr_sub_lt_qsucc hmono (hqpos (n + 1)) hTn hyr hab hy' hd hk
    have hm_le : |(m : ℝ)| ≤ |(y : ℝ)| + (s : ℝ) * (q (n - 1) : ℝ) := by
      have h1 : ((|m| : ℤ) : ℝ) ≤ ((|y| : ℤ) : ℝ) + ((s : ℤ) : ℝ) * ((q (n - 1) : ℤ) : ℝ) := by
        have he : |k - d| = |m| := by rw [hm]
        rw [← he] at hgeom
        exact_mod_cast hgeom
      rw [Int.cast_abs, Int.cast_abs] at h1
      push_cast at h1
      exact h1
    have hm_lt : |m| < (q (n + 1) : ℤ) := by
      have he : |k - d| = |m| := by rw [hm]
      rwa [← he] at hgeom2
    have hqn_le : q n ≤ m.natAbs := by
      have h1 : (m.natAbs : ℤ) = |m| := Int.natCast_natAbs m
      have h2 : (q n : ℤ) ≤ (m.natAbs : ℤ) := by rw [h1]; exact hsmall
      exact_mod_cast h2
    have hlt_succ : m.natAbs < q (n + 1) := by
      have h1 : (m.natAbs : ℤ) = |m| := Int.natCast_natAbs m
      have h2 : (m.natAbs : ℤ) < (q (n + 1) : ℤ) := by rw [h1]; exact hm_lt
      exact_mod_cast h2
    -- crude bound
    have hcrude : Δ n ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) :=
      delta_le_fracDist hbest hqn_le hlt_succ
    -- the remainder is nonzero
    have ht_ne : m % (q n : ℤ) ≠ 0 := by
      have h := emod_sub_ne_zero hab hTn hqnI hnonres' hd hk hne
      simpa [hm] using h
    have ht0 : 0 < m % (q n : ℤ) := by
      have hnn := Int.emod_nonneg m (ne_of_gt hqnI)
      omega
    have htlt : m % (q n : ℤ) < (q n : ℤ) := Int.emod_lt_of_pos m hqnI
    have hδ : 1 / (2 * (q n : ℝ)) ≤
        Work.TMC16Core.fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α) :=
      emod_sub_ge hqpos hmono hΔpos hΔeq hΔup hΔlo hbest ht0 htlt
    have hΔn0 : 0 ≤ Δ n := by
      rw [hΔeq n]; simp only [fracDist]; exact abs_nonneg _
    have hD : (|(m : ℝ)| / (q n : ℝ) + 1) * Δ n ≤
        1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ)) :=
      coeff_bound (hqpos n) (hqpos (n + 1)) (hΔup n) hΔn0 hTn hyr hm_le
    have hdec : m = (m / (q n : ℤ)) * (q n : ℤ) + m % (q n : ℤ) :=
      (Int.ediv_mul_add_emod m (q n : ℤ)).symm
    have hM : |(((m / (q n : ℤ)) : ℤ) : ℝ)| ≤ |(m : ℝ)| / (q n : ℝ) + 1 :=
      ediv_abs_le (hqpos n) m
    have hcross : Work.TMC16Core.fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α)
        - (|(m : ℝ)| / (q n : ℝ) + 1) * Δ n
        ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) :=
      fracDist_cross_bound hΔeq hdec hM le_rfl hΔn0
    have hhalf : 1 / (2 * (q (n + 1) : ℝ)) ≤ Δ n :=
      half_q_succ_le_Delta (hqpos (n + 1)) (hΔlo n)
        (by exact_mod_cast (hmono (Nat.lt_succ_self n)).le)
    have h2 : Work.TMC16Core.fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α)
        - (1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ)))
        ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) := by
      linarith [hcross, hD]
    have hmax : 1 / (16 * (q n : ℝ)) ≤ max (Δ n)
        (Work.TMC16Core.fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α)
          - (1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ)))) :=
      max_delta_arith (by exact_mod_cast hqpos n) (by exact_mod_cast hqpos (n + 1)) hδ hhalf le_rfl
    have hmax2 : max (Δ n)
        (Work.TMC16Core.fracDist ((((m % (q n : ℤ)) : ℤ) : ℝ) * α)
          - (1 / (4 * (q n : ℝ)) + 3 / (2 * (q (n + 1) : ℝ))))
        ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) :=
      max_le hcrude h2
    have hbound : 1 / (16 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((m : ℝ) * α) :=
      le_trans hmax hmax2
    linarith [hrate, hbound]

end

end Work.TMC16Core.Core
