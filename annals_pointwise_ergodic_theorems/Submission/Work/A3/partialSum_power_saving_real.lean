import Mathlib
import Submission.Work.A3.completeSum_power_saving
import Submission.Work.A3.weyl_poly
import Submission.Work.A3.partialSum_weyl_bracket

/-!
# Power saving for *incomplete* (partial) exponential sums (Area A3) — corrected form

The statement requested as `Work.A3.partialSum_power_saving` is written

`∃ δ > 0, ∃ C > 0, ∀ q a t, ... ‖∑_{r<t} e(-2πi aQ(r)/q)‖ ≤ C * (q : ℝ) ^ (1 - δ)`

**without a type ascription for `δ`**.  The numeral `1` in `1 - δ` defaults to `Nat`, so Lean
elaborates the binder as `δ : Nat` and the subtraction as *truncated* `Nat` subtraction
(`#print Work.A3.partialSum_power_saving` shows `@Exists Nat fun δ => ...` and
`@HSub.hSub Nat Nat Nat instSubNat 1 δ`, with `@HPow.hPow Real Nat Real` for the power).
Since `δ > 0` for a natural number means `δ ≥ 1`, the exponent `1 - δ` is `0`, so the bound
reads `‖∑_{r<t} e(-2πi aQ(r)/q)‖ ≤ C * 1`: it asserts that the incomplete exponential sums are
*uniformly bounded*, which is false.  For `Q = X²`, `q = p` a prime, `a = 1` and `t = p` the sum
is the complete quadratic Gauss sum, whose modulus is `√p` (elementary proof: with `ζ = e(-2πi/p)`
one substitutes `u = r + s`, `v = r - s` in
`|∑_r ζ^{r²}|² = ∑_{r,s} ζ^{r²-s²} = ∑_{u,v} ζ^{uv} = p`);
taking `p > C²` violates the bound.

The intended statement — the one the consumers `Work.A3.csPhase_partial_sums` and
`Work.A3.coherentArc_bound` use, both of which carry an explicit `{δ : ℝ}` — is the `ℝ`-version,
and it is **true**.  This module proves it under the corrected name
(`Work.A3.partialSum_power_saving_real`, and the normalised `…_inv_degree`), so that the corrected
statement is available as a separately verified work item.  The misspelled request itself lives,
verbatim, in `Submission/Work/A3/partialSum_power_saving.lean`.

## The proof

The sum over `r < t` is `e(-2πi aQ(0)/q)` (a single unimodular term) plus the polynomial
exponential sum `Work.A3.expSum Q (t-1) (a/q)` of `Circle.lean`
(`norm_partSum_le`, from `∑_{r<t} = f(0) + ∑_{n=1}^{t-1} f(n)`).

Weyl's inequality `Work.A3.weyl_poly` — applied with the *exact* rational `θ = a/q`, so that its
Dirichlet hypothesis `|θ - a/q| ≤ 1/q²` is an identity — then gives

`‖expSum Q (t-1) (a/q)‖ ≤ Cw · N^{1+ε} · (q⁻¹ + N⁻¹ + q·N^{-d})^σ`,  `N = t-1`, `σ = 2^{-(d-1)}`.

Since `1 ≤ N ≤ q`, the real-inequality core `Work.A3.partialSum_weyl_bracket` (with `ε = σ/4`)
turns the right-hand side into `3·Cw·q^{1-3σ/8}`, and `‖partSum‖ ≤ 1 + ‖expSum‖ ≤ 1 + 3Cw·q^{1-δ}`
finishes, as `q^{1-δ} ≥ 1`.  The cases `t = 0, 1` are immediate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.A3

open Polynomial Finset
open scoped Real

noncomputable section

/-- The summand `e(-2πi a Q(r)/q)` of the incomplete exponential sum. -/
def partTerm (Q : Polynomial ℤ) (a : ℤ) (q : ℕ) (r : ℕ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I *
    ((a : ℝ) * (((Q.eval (r : ℤ)) : ℤ) : ℝ) / (q : ℝ))))

/-- The incomplete exponential sum `∑_{r < t} e(-2πi a Q(r)/q)`. -/
def partSum (Q : Polynomial ℤ) (a : ℤ) (q : ℕ) (t : ℕ) : ℂ :=
  ∑ r ∈ Finset.range t, partTerm Q a q r

/-- Splitting off the term `r = 0`: `∑_{r<t} f r = f 0 + ∑_{1 ≤ n ≤ t-1} f n` for `t ≥ 1`. -/
lemma sum_range_eq_zero_add_Icc (f : ℕ → ℂ) {t : ℕ} (ht : 1 ≤ t) :
    ∑ r ∈ Finset.range t, f r = f 0 + ∑ n ∈ Finset.Icc 1 (t - 1), f n := by
  have hIcc : Finset.Icc 1 (t - 1) = Finset.Ico 1 t := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.range_eq_Ico t, Finset.sum_Ico_eq_sum_range f 0 t,
      Finset.sum_Ico_eq_sum_range f 1 t]
  rw [← Nat.sub_add_cancel ht]
  simp only [Nat.sub_zero, zero_add, Nat.add_sub_cancel]
  rw [Finset.sum_range_succ']
  simp [add_comm]

/-- The first summand has modulus one. -/
lemma norm_partTerm_zero (Q : Polynomial ℤ) (a : ℤ) (q : ℕ) : ‖partTerm Q a q 0‖ = 1 := by
  have h : partTerm Q a q 0 = Complex.exp
      (Complex.ofReal (-(2 * Real.pi *
        ((a : ℝ) * (((Q.eval (0 : ℤ)) : ℤ) : ℝ) / (q : ℝ)))) * Complex.I) := by
    rw [partTerm]
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The incomplete sum is bounded by `1` plus the polynomial exponential sum `expSum Q (t-1)`. -/
lemma norm_partSum_le (Q : Polynomial ℤ) (a : ℤ) (q : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    ‖partSum Q a q t‖ ≤ 1 + ‖expSum Q (t - 1) ((a : ℝ) / (q : ℝ))‖ := by
  have hsplit := sum_range_eq_zero_add_Icc (partTerm Q a q) ht
  have hexp : expSum Q (t - 1) ((a : ℝ) / (q : ℝ))
      = ∑ n ∈ Finset.Icc 1 (t - 1), partTerm Q a q n := by
    rw [expSum]
    apply Finset.sum_congr rfl
    intro n _
    rw [partTerm]
    congr 1
    push_cast
    ring
  rw [partSum, hsplit, ← hexp]
  calc ‖partTerm Q a q 0 + expSum Q (t - 1) ((a : ℝ) / (q : ℝ))‖
      ≤ ‖partTerm Q a q 0‖ + ‖expSum Q (t - 1) ((a : ℝ) / (q : ℝ))‖ := norm_add_le _ _
    _ = 1 + ‖expSum Q (t - 1) ((a : ℝ) / (q : ℝ))‖ := by rw [norm_partTerm_zero]

/-- **The partial sums are power-saving (with `δ : ℝ`), in the normalised form
`δ · deg Q ≤ 1`** used by the major-arc statements of the area (cf.
`Work.A3.completeSum_saving_le_inv_degree`).  The saving obtained here is
`δ = 3·2^{-(d-1)}/8`, which automatically satisfies `δ·d ≤ 1` for `d ≥ 2`. -/
theorem partialSum_power_saving_inv_degree (Q : Polynomial ℤ)
    (hd : 2 ≤ Polynomial.natDegree Q) :
    ∃ (δ : ℝ), δ > 0 ∧ ∃ (C : ℝ), C > 0 ∧ δ * (Polynomial.natDegree Q : ℝ) ≤ 1 ∧
      ∀ (q : ℕ) (a : ℤ) (t : ℕ), 1 ≤ q → IsCoprime a (q : ℤ) → t ≤ q →
      ‖partSum Q a q t‖ ≤ C * (q : ℝ) ^ (1 - δ) := by
  classical
  set σ : ℝ := (1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  have hσhalf : σ ≤ 1 / 2 := by
    rw [hσdef]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (Polynomial.natDegree Q - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨Cw, hCwpos, hCw⟩ := weyl_poly Q hd (ε := σ / 4) (by positivity)
  -- rewrite Weyl's inequality in terms of `σ`
  have hCw' : ∀ (N : ℕ) (a q : ℤ) (θ : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a q →
      |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
      ‖expSum Q N θ‖ ≤ Cw * (N : ℝ) ^ (1 + σ / 4) *
        ((q : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q : ℝ) * (N : ℝ) ^ (-((Polynomial.natDegree Q : ℤ)))) ^ σ := by
    intro N a q θ hN hq hcop hθ
    have h := hCw N a q θ hN hq hcop hθ
    rwa [← hσdef] at h
  -- the saving is already small enough: `3σ/8 · d ≤ 1`
  have hDelta : 3 * σ / 8 * (Polynomial.natDegree Q : ℝ) ≤ 1 := by
    rw [hσdef]
    have hd1 : (Polynomial.natDegree Q : ℝ) ≤ (2 : ℝ) ^ (Polynomial.natDegree Q - 1) := by
      have h := Nat.lt_two_pow_self (n := Polynomial.natDegree Q - 1)
      have h1 : Polynomial.natDegree Q ≤ 2 ^ (Polynomial.natDegree Q - 1) := by
        have heq : Polynomial.natDegree Q = (Polynomial.natDegree Q - 1) + 1 := by omega
        calc Polynomial.natDegree Q = (Polynomial.natDegree Q - 1) + 1 := heq
          _ ≤ 2 ^ (Polynomial.natDegree Q - 1) := by omega
      exact_mod_cast h1
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (Polynomial.natDegree Q - 1) := by positivity
    have hratio : (Polynomial.natDegree Q : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1)
        ≤ 1 := by
      rw [div_le_one hpos]; exact hd1
    calc 3 * (1 / (2 : ℝ) ^ (Polynomial.natDegree Q - 1)) / 8 * (Polynomial.natDegree Q : ℝ)
        = (3 / 8) * ((Polynomial.natDegree Q : ℝ) /
            (2 : ℝ) ^ (Polynomial.natDegree Q - 1)) := by ring
      _ ≤ (3 / 8) * 1 := by linarith
      _ ≤ 1 := by norm_num
  refine ⟨3 * σ / 8, by positivity, 1 + Cw * 3, by positivity, hDelta, ?_⟩
  have hδnn : 0 ≤ 1 - 3 * σ / 8 := by linarith
  -- the main case `t ≥ 2`
  have key : ∀ (q : ℕ) (a : ℤ) (t : ℕ), 1 ≤ q → IsCoprime a (q : ℤ) → t ≤ q → 2 ≤ t →
      ‖partSum Q a q t‖ ≤ (1 + Cw * 3) * (q : ℝ) ^ (1 - 3 * σ / 8) := by
    intro q a t hq ha htq ht2
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hN1 : 1 ≤ t - 1 := by omega
    have hNR : (1 : ℝ) ≤ ((t - 1 : ℕ) : ℝ) := by exact_mod_cast hN1
    have hNqR : ((t - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
      have : t - 1 ≤ q := by omega
      exact_mod_cast this
    have hqZ : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
    have hqcast : (((q : ℤ)) : ℝ) = (q : ℝ) := by push_cast; ring
    have hθ : |((a : ℝ) / (q : ℝ)) - (a : ℝ) / (((q : ℤ)) : ℝ)| ≤
        1 / ((((q : ℤ)) : ℝ) ^ 2) := by
      rw [hqcast, sub_self, abs_zero]
      apply div_nonneg zero_le_one
      positivity
    have hw := hCw' (t - 1) a (q : ℤ) ((a : ℝ) / (q : ℝ)) hN1 hqZ ha hθ
    -- convert the integer power `N ^ (-(d : ℤ))` into the real power `N ^ (-(d : ℝ))`
    have hbase : (q : ℝ)⁻¹ + (((t - 1 : ℕ)) : ℝ)⁻¹ +
          (q : ℝ) * (((t - 1 : ℕ)) : ℝ) ^ (-((Polynomial.natDegree Q : ℤ)))
        = (q : ℝ)⁻¹ + (((t - 1 : ℕ)) : ℝ)⁻¹ +
          (q : ℝ) * (((t - 1 : ℕ)) : ℝ) ^ (-((Polynomial.natDegree Q : ℝ))) := by
      have hpow : (((t - 1 : ℕ)) : ℝ) ^ (-((Polynomial.natDegree Q : ℤ)))
          = (((t - 1 : ℕ)) : ℝ) ^ (-((Polynomial.natDegree Q : ℝ))) := by
        rw [← Real.rpow_intCast]
        congr 1
        push_cast
        ring
      rw [hpow]
    have hbr := partialSum_weyl_bracket (Polynomial.natDegree Q) hd hNR hNqR hq1
    rw [← hσdef] at hbr
    have hstep : ‖expSum Q (t - 1) ((a : ℝ) / (q : ℝ))‖
        ≤ Cw * (3 * (q : ℝ) ^ (1 - 3 * σ / 8)) := by
      calc ‖expSum Q (t - 1) ((a : ℝ) / (q : ℝ))‖
          ≤ Cw * ((t - 1 : ℕ) : ℝ) ^ (1 + σ / 4) *
              ((q : ℝ)⁻¹ + (((t - 1 : ℕ)) : ℝ)⁻¹ +
                (q : ℝ) * (((t - 1 : ℕ)) : ℝ) ^ (-((Polynomial.natDegree Q : ℤ)))) ^ σ := hw
        _ = Cw * (((t - 1 : ℕ) : ℝ) ^ (1 + σ / 4) *
              ((q : ℝ)⁻¹ + (((t - 1 : ℕ)) : ℝ)⁻¹ +
                (q : ℝ) * (((t - 1 : ℕ)) : ℝ) ^ (-((Polynomial.natDegree Q : ℝ)))) ^ σ) := by
              rw [hbase]; ring
        _ ≤ Cw * (3 * (q : ℝ) ^ (1 - 3 * σ / 8)) :=
              mul_le_mul_of_nonneg_left hbr (le_of_lt hCwpos)
    calc ‖partSum Q a q t‖ ≤ 1 + ‖expSum Q (t - 1) ((a : ℝ) / (q : ℝ))‖ :=
          norm_partSum_le Q a q (by omega)
      _ ≤ 1 + Cw * (3 * (q : ℝ) ^ (1 - 3 * σ / 8)) := by linarith [hstep]
      _ ≤ (1 + Cw * 3) * (q : ℝ) ^ (1 - 3 * σ / 8) := by
          have hr1 : 1 ≤ (q : ℝ) ^ (1 - 3 * σ / 8) := Real.one_le_rpow hq1 hδnn
          calc (1 : ℝ) + Cw * (3 * (q : ℝ) ^ (1 - 3 * σ / 8))
              ≤ (q : ℝ) ^ (1 - 3 * σ / 8) + Cw * (3 * (q : ℝ) ^ (1 - 3 * σ / 8)) := by linarith
            _ = (1 + Cw * 3) * (q : ℝ) ^ (1 - 3 * σ / 8) := by ring
  intro q a t hq ha htq
  rcases lt_or_ge t 2 with ht2 | ht2
  · rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · have h0 : partSum Q a q 0 = 0 := by simp [partSum]
      rw [h0, norm_zero]
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hr1 : 1 ≤ (q : ℝ) ^ (1 - 3 * σ / 8) := Real.one_le_rpow hq1 hδnn
      exact mul_nonneg (by positivity) (le_trans zero_le_one hr1)
    · have h1 : partSum Q a q 1 = partTerm Q a q 0 := by simp [partSum]
      rw [h1, norm_partTerm_zero]
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hr1 : 1 ≤ (q : ℝ) ^ (1 - 3 * σ / 8) := Real.one_le_rpow hq1 hδnn
      have hC : 1 ≤ 1 + Cw * 3 := by linarith [hCwpos]
      exact one_le_mul_of_one_le_of_one_le hC hr1
  · exact key q a t hq ha htq ht2

/-- **The partial sums are power-saving (with `δ : ℝ`).**  For a polynomial `Q ∈ ℤ[X]` of degree
`d ≥ 2` there are `δ > 0` and `C > 0` with

`‖∑_{r<t} e(-2πi a Q(r)/q)‖ ≤ C · q^{1-δ}`

for all `q ≥ 1`, all `a` coprime to `q` and every `t ≤ q`.  This is the statement intended by
`Work.A3.partialSum_power_saving`; the explicit ascription `(δ : ℝ)` is essential, since without
it Lean's numeral defaulting makes the binder a `Nat` and truncates the exponent `1 - δ` to `0`
(see the module docstring). -/
theorem partialSum_power_saving_real (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q) :
    ∃ (δ : ℝ), δ > 0 ∧ ∃ (C : ℝ), C > 0 ∧
      ∀ (q : ℕ) (a : ℤ) (t : ℕ), 1 ≤ q → IsCoprime a (q : ℤ) → t ≤ q →
      ‖∑ r ∈ Finset.range t,
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((a : ℝ) * (((Q.eval (r : ℤ)) : ℤ) : ℝ) / (q : ℝ))))‖
      ≤ C * (q : ℝ) ^ (1 - δ) := by
  obtain ⟨δ, hδ, C, hC, _, H⟩ := partialSum_power_saving_inv_degree Q hd
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro q a t hq ha htq
  change ‖partSum Q a q t‖ ≤ C * (q : ℝ) ^ (1 - δ)
  exact H q a t hq ha htq

end

end Work.A3
