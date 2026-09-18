import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Submission.Commons.NumberTheory.Mertens.exp_primeZetaLog_eq_riemannZeta_re
import Submission.Commons.NumberTheory.Mertens.primeZetaSum_eq_primeZetaLog_sub
import Submission.Commons.Analysis.ExpLog.log_one_sub_le

open Filter
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-! # The pole of the prime zeta function at `s = 1`

We prove `primeZeta_pole`:

`P(s) + log(s - 1) → -Σ_p (log(p/(p-1)) - 1/p)` as `s → 1⁺`,
where `P(s) = Σ_p p⁻ˢ` is the prime zeta function.

Strategy: from Mathlib's Euler-product formula one gets, for real `s > 1`,
`Σ_p -log(1 - p⁻ˢ) = log Re ζ(s)` (see `exp_primeZetaLog_eq_riemannZeta_re`),
and Mathlib's asymptotic `log Re ζ(s) + log(s-1) → 0`.  Writing
`-log(1 - p⁻ˢ) = p⁻ˢ + corrTail p s` with
`corrTail p s = -log(1 - p⁻ˢ) - p⁻ˢ`, the sum over primes of the correction
converges, as `s → 1⁺`, to `Σ_p corrTail p 1 = Σ_p (log(p/(p-1)) - 1/p)`
(a dominated-convergence argument, `Tannery`). -/

/-- The prime zeta function `Σ_p p^(-s)` (real `rpow`). -/
def primeZetaSum (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s)

/-- `Σ_p -log(1 - p^(-s))` (the logarithm of the Euler product). -/
def primeZetaLogSum (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))

/-- Per-prime correction `-log(1 - x) - x` with `x = p^(-s)`. -/
def corrTailPrime (p : ℕ) (s : ℝ) : ℝ :=
  -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) - ((p : ℕ) : ℝ) ^ (-s)

/-- Sum over primes of the per-prime correction. -/
def corrTailPrimeSum (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, corrTailPrime (p : ℕ) s

/-- The absolute constant `Σ_p (log(p/(p-1)) - 1/p)` from the statement. -/
def primeCorrConst : ℝ :=
  ∑' p : Nat.Primes,
    (Real.log (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) - (1 : ℝ) / ((p : ℕ) : ℝ))

/-! ## Elementary bounds for `g(x) = -log(1-x) - x` on `[0, 1/2]` -/

lemma g_nonneg {x : ℝ} (hx1 : x < 1) : 0 ≤ -Real.log (1 - x) - x := by
  have h1x : 0 < 1 - x := by linarith
  have hle : Real.log (1 - x) ≤ (1 - x) - 1 := Real.log_le_sub_one_of_pos h1x
  nlinarith

lemma g_le_two_sq {x : ℝ} (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) :
    -Real.log (1 - x) - x ≤ 2 * x ^ 2 := by
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · simp
  · have hx1 : x < 1 := by linarith
    have hlog := Commons.Analysis.ExpLog.log_one_sub_le hxpos hx1
    have h1x : 0 < 1 - x := by linarith
    have hsub : x / (1 - x) - x = x ^ 2 / (1 - x) := by
      field_simp [h1x.ne']
      ring
    have hle2 : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ h1x]
      nlinarith [hx12]
    calc
      -Real.log (1 - x) - x ≤ x / (1 - x) - x := sub_le_sub_right hlog x
      _ = x ^ 2 / (1 - x) := hsub
      _ ≤ 2 * x ^ 2 := hle2

lemma rpow_neg_lt_one_of_one_lt {x : ℝ} (hx : 1 < x) {a : ℝ} (ha : a < 0) : x ^ a < 1 := by
  simpa using Real.rpow_lt_one_of_one_lt_of_neg hx ha

lemma prime_rpow_le_half {p : ℕ} (hp : Nat.Prime p) {s : ℝ} (hs : 1 ≤ s) :
    ((p : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.Prime.one_lt hp).le
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp.two_le
  have h1 : ((p : ℕ) : ℝ) ^ (-s) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have h2 : ((p : ℕ) : ℝ) ^ (-1 : ℝ) = ((p : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one ((p : ℕ) : ℝ)
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.pos
  have h3 : ((p : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
    have hinv : ((p : ℕ) : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).2 hp2
    simpa using hinv
  calc
    ((p : ℕ) : ℝ) ^ (-s) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) := h1
    _ = ((p : ℕ) : ℝ)⁻¹ := h2
    _ ≤ 1 / 2 := h3

lemma corrTailPrime_nonneg {p : ℕ} (hp : Nat.Prime p) {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ corrTailPrime p s := by
  unfold corrTailPrime
  have hxpos : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-s) := by
    simpa using Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) (-s)
  have hs' : -s < 0 := by linarith
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.Prime.one_lt hp)
  have hx1 : ((p : ℕ) : ℝ) ^ (-s) < 1 := rpow_neg_lt_one_of_one_lt hp1 hs'
  exact g_nonneg hx1

lemma corrTailPrime_le {p : ℕ} (hp : Nat.Prime p) {s : ℝ} (hs : 1 ≤ s) :
    corrTailPrime p s ≤ 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  unfold corrTailPrime
  let x : ℝ := ((p : ℕ) : ℝ) ^ (-s)
  have hx0 : (0 : ℝ) ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (by exact_mod_cast (le_of_lt hp.pos)) (-s)
  have hx12 : x ≤ 1 / 2 := by
    dsimp [x]
    exact prime_rpow_le_half hp hs
  have hle1 : -Real.log (1 - x) - x ≤ 2 * x ^ 2 := g_le_two_sq hx0 hx12
  have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (le_of_lt hp.pos)
  have hsq : x ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    dsimp [x]
    have hsq' : (((p : ℕ) : ℝ) ^ (-s)) ^ 2 = ((p : ℕ) : ℝ) ^ ((-s) * (2 : ℕ)) := by
      rw [← Real.rpow_mul_natCast hp0 (-s) 2]
    rw [hsq']
    have hleE : (-s) * ((2 : ℕ) : ℝ) ≤ -2 := by
      norm_num
      linarith
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.Prime.one_lt hp).le) hleE
  calc
    -Real.log (1 - x) - x ≤ 2 * x ^ 2 := hle1
    _ ≤ 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- The uniform bound `p ↦ 2 p^(-2)` is summable over primes. -/
lemma summable_corrTailBound :
    Summable (fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  have h : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    (Nat.Primes.summable_rpow (r := (-2 : ℝ))).mpr (by norm_num)
  simpa using h.mul_left (2 : ℝ)

/-- Per-prime function `s ↦ corrTailPrime p s` is continuous at `s = 1`. -/
lemma continuousAt_corrTailPrime (p : ℕ) (hp : Nat.Prime p) :
    ContinuousAt (fun s : ℝ => corrTailPrime p s) 1 := by
  have hpne : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp.pos)
  have hcr : Continuous (fun s : ℝ => ((p : ℕ) : ℝ) ^ (-s)) :=
    (Real.continuous_const_rpow (a := ((p : ℕ) : ℝ)) hpne).comp continuous_neg
  have hArgT : Tendsto (fun s : ℝ => 1 - ((p : ℕ) : ℝ) ^ (-s)) (𝓝 1)
      (𝓝 (1 - ((p : ℕ) : ℝ) ^ (-1 : ℝ))) := by
    exact ((continuous_const.sub hcr).continuousAt).tendsto
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.Prime.one_lt hp)
  have hpown : ((p : ℕ) : ℝ) ^ (-1 : ℝ) < 1 :=
    rpow_neg_lt_one_of_one_lt hp1 (by norm_num : (-1 : ℝ) < 0)
  have harg1 : (1 : ℝ) - ((p : ℕ) : ℝ) ^ (-1 : ℝ) ≠ 0 := by linarith
  have hlog : ContinuousAt (fun s : ℝ => Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) 1 := by
    have hlogT : Tendsto (fun s : ℝ => Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))) (𝓝 1)
        (𝓝 (Real.log (1 - ((p : ℕ) : ℝ) ^ (-1 : ℝ)))) := by
      exact (Real.continuousAt_log harg1).tendsto.comp hArgT
    exact hlogT
  have hC : ContinuousAt (fun s : ℝ =>
      -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) - ((p : ℕ) : ℝ) ^ (-s)) 1 :=
    hlog.neg.sub hcr.continuousAt
  simpa [corrTailPrime] using hC

/-- Per-prime correction tends to its value at `s = 1` from the right. -/
lemma tendsto_corrTailPrime_one (p : ℕ) (hp : Nat.Prime p) :
    Tendsto (fun s : ℝ => corrTailPrime p s) (𝓝[>] (1 : ℝ)) (𝓝 (corrTailPrime p 1)) := by
  exact (continuousAt_corrTailPrime p hp).tendsto.mono_left nhdsWithin_le_nhds

/-- The correction sum is continuous at `s = 1` from the right (dominated convergence). -/
lemma corrTailPrimeSum_tendsto_right_one :
    Tendsto (fun s : ℝ => corrTailPrimeSum s) (𝓝[>] (1 : ℝ)) (𝓝 (corrTailPrimeSum 1)) := by
  let 𝓕 : Filter ℝ := 𝓝[>] (1 : ℝ)
  have hbound : ∀ᶠ s in 𝓕, ∀ p : Nat.Primes,
      ‖corrTailPrime (p : ℕ) s‖ ≤ 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    intro p
    have hsle : 1 ≤ s := le_of_lt hs
    have hnon : 0 ≤ corrTailPrime (p : ℕ) s := corrTailPrime_nonneg p.property hsle
    have hle : corrTailPrime (p : ℕ) s ≤ 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
      corrTailPrime_le p.property hsle
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact hle
  simpa [corrTailPrimeSum] using
    (tendsto_tsum_of_dominated_convergence
      (α := ℝ) (β := Nat.Primes) (𝓕 := 𝓕) (G := ℝ)
      (f := fun (s : ℝ) (p : Nat.Primes) => corrTailPrime (p : ℕ) s)
      (g := fun (p : Nat.Primes) => corrTailPrime (p : ℕ) 1)
      (bound := fun (p : Nat.Primes) => 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ))
      summable_corrTailBound
      (fun p => tendsto_corrTailPrime_one (p : ℕ) p.property)
      hbound)

/-- Value of the per-prime correction at `s = 1`. -/
lemma corrTailPrime_one_eq (p : ℕ) (hp : Nat.Prime p) :
    corrTailPrime p 1 =
      Real.log (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) - (1 : ℝ) / ((p : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp0' : ((p : ℕ) : ℝ) ≠ 0 := ne_of_gt hp0
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.one_lt hp)
  have hp0m1 : 0 < (p : ℝ) - 1 := by linarith
  unfold corrTailPrime
  have hpown : ((p : ℕ) : ℝ) ^ (-1 : ℝ) = ((p : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one ((p : ℕ) : ℝ)
  rw [hpown]
  have hsub1 : (1 : ℝ) - ((p : ℕ) : ℝ)⁻¹ = (((p : ℕ) : ℝ) - 1) / ((p : ℕ) : ℝ) := by
    field_simp [hp0']
  rw [hsub1]
  have hldiv : Real.log ((((p : ℕ) : ℝ) - 1) / ((p : ℕ) : ℝ)) =
      Real.log (((p : ℕ) : ℝ) - 1) - Real.log ((p : ℕ) : ℝ) :=
    Real.log_div (ne_of_gt hp0m1) (ne_of_gt hp0)
  rw [hldiv]
  have hldiv2 : Real.log (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) =
      Real.log ((p : ℕ) : ℝ) - Real.log (((p : ℕ) : ℝ) - 1) :=
    Real.log_div (ne_of_gt hp0) (ne_of_gt hp0m1)
  rw [hldiv2]
  ring

/-- The value of the correction sum at `s = 1` is the constant in the statement. -/
lemma corrTailPrimeSum_one_eq : corrTailPrimeSum 1 = primeCorrConst := by
  unfold corrTailPrimeSum primeCorrConst
  apply tsum_congr
  intro p
  exact corrTailPrime_one_eq (p : ℕ) p.property

/-- `Σ_p -log(1-p⁻ˢ) + log(s-1) → 0` as `s → 1⁺` (from the Riemann zeta asymptotics). -/
lemma tendsto_primeZetaLogSum_add_log_sub :
    Tendsto (fun s : ℝ => primeZetaLogSum s + Real.log (s - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hlim : Tendsto (fun s : ℝ => Real.log ((riemannZeta (s : ℂ)).re) + Real.log (s - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    exact (Asymptotics.isLittleO_one_iff ℝ).1 log_riemannZeta_add_log_sub_isLittleO_ofReal
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have he : Real.exp (primeZetaLogSum s) = (riemannZeta (s : ℂ)).re := by
    simpa [primeZetaLogSum] using exp_primeZetaLog_eq_riemannZeta_re hs
  have hlog : primeZetaLogSum s = Real.log ((riemannZeta (s : ℂ)).re) := by
    calc
      primeZetaLogSum s = Real.log (Real.exp (primeZetaLogSum s)) := by rw [Real.log_exp]
      _ = Real.log ((riemannZeta (s : ℂ)).re) := by rw [he]
  rw [hlog]

/-- Pointwise identity `P(s) = logΣ(s) - corrΣ(s)` for `s > 1`. -/
lemma primeZetaSum_eq_primeZetaLogSum_sub {s : ℝ} (hs : 1 < s) :
    primeZetaSum s = primeZetaLogSum s - corrTailPrimeSum s := by
  simpa [primeZetaSum, primeZetaLogSum, corrTailPrimeSum, corrTailPrime]
    using primeZetaSum_eq_primeZetaLog_sub hs

/-- The pole of the prime zeta function at `s = 1`. -/
theorem primeZeta_pole :
    Filter.Tendsto (fun s : ℝ =>
      (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1))
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)))
      (nhds (- (∑' p : Nat.Primes,
        (Real.log (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) - (1 : ℝ) / ((p : ℕ) : ℝ))))) := by
  change Filter.Tendsto (fun s : ℝ => primeZetaSum s + Real.log (s - 1))
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (- primeCorrConst))
  have h1 : Tendsto (fun s : ℝ => primeZetaLogSum s + Real.log (s - 1))
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (𝓝 (0 : ℝ)) :=
    tendsto_primeZetaLogSum_add_log_sub
  have h2 : Tendsto (fun s : ℝ => corrTailPrimeSum s)
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (𝓝 primeCorrConst) := by
    have h := corrTailPrimeSum_tendsto_right_one
    have hval : corrTailPrimeSum 1 = primeCorrConst := corrTailPrimeSum_one_eq
    simpa [hval] using h
  have hsub := h1.sub h2
  have hfin : Tendsto (fun s : ℝ => primeZetaSum s + Real.log (s - 1))
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (𝓝 (0 - primeCorrConst)) := by
    refine hsub.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsplit := primeZetaSum_eq_primeZetaLogSum_sub (s := s) hs
    rw [hsplit]
    ring
  simpa using hfin

end

end Commons.NumberTheory.Mertens