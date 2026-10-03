/-
# `Submission.Work.FIArea6V.tau_le_tauMax_of_noSmallPrimes` — the τ-vacuity of the raised datum

This lemma is the arithmetic content of the *τ-vacuity* hypothesis `Work.FIArea6V.TauVac` of the
clean area-6 lane (`Submission/Work/FIArea6V/Defs.lean`): at the raised datum `tauMax Pa`
(whose only change is `τ := x^{η/3}`, the maximal admissible value allowed by (5.23)), the
divisor restriction (5.9) of the paper is satisfied at **every** point of the polar box (5.14)
that is free of small primes (5.8).

The mathematics is the standard `τ(n) = n^{o(1)}` bound in the precise form the paper's data
provide.  For `z` in the polar box and free of primes `≤ P = Pz`:

* `n = |z|² = gnorm z ≤ (1+θ)N ≤ 2N < 2 x^{1/2}`, since (4.12) gives `gnorm z ≤ (1+θ)N`,
  `θ = (log x)^{-A'} ≤ 1` and (4.6) gives `N < x^{1/2}(log x)^{-B}`;
* hence `log n ≤ log 2 + (1/2) log x`;
* `τ(n) ≤ 2^{Ω(n)}` where `Ω(n) = n.factorization.sum (fun _ e => e)` counts prime factors with
  multiplicity;
* every prime factor of `n` is `> P` ((5.8) is `NoSmallPrimes`), so `(P+1)^{Ω(n)} ≤ n` and
  `Ω(n) ≤ log n / log(P+1)`;
* (4.4) gives `log P ≥ (log log x)²`, so `log(P+1) ≥ (log log x)²`, and for `x ≥ x₀(η)`
  the elementary comparison
  `(log 2 + (1/2)log x)·log 2 / (log log x)² ≤ (η/3) log x`
  holds, i.e. `τ(n) ≤ exp((η/3) log x) = x^{η/3}`.

The only quantified constants are `log 2`, `η` and the threshold `x₀(η)`: nothing here depends on
the (many) numerical parameters of `Work.FITop.Params` beyond (4.4), (4.6), (4.12), (5.8) and
`θ ≤ 1`.
-/
import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Defs4
import Submission.Work.FIArea6V.tau_le_two_pow_cardFactors

namespace Work.FIArea6V

/-- **The number of prime factors with multiplicity of a `P`-free integer.**  If every prime
factor of `n` exceeds `P` (the `NoSmallPrimes` condition (5.8)) then
`Ω(n) ≤ log n / log(P+1)`.

Indeed all the prime factors of `n` are `≥ P + 1`, so `(P+1)^{Ω n} ≤ n`.  (Together with the
delegated `tau_le_two_pow_cardFactors` this gives `τ(n) ≤ 2^{Ω n}`.) -/
theorem cardFactors_cast_le_log_div_log {n P : ℕ} (hn : 1 ≤ n) (hP : 2 ≤ P)
    (hfree : ∀ q : ℕ, q.Prime → q ≤ P → ¬ q ∣ n) :
    ((n.factorization.sum fun _ e => e : ℕ) : ℝ) ≤ Real.log (n : ℝ) / Real.log ((P : ℝ) + 1) := by
  have hn0 : n ≠ 0 := by omega
  have hlen : n.factorization.sum (fun _ e => e) = n.primeFactorsList.length := by
    rw [← ArithmeticFunction.cardFactors_eq_sum_factorization, ArithmeticFunction.cardFactors_apply]
  have hmem : ∀ p ∈ n.primeFactorsList, P + 1 ≤ p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
    have : ¬ (p ≤ P) := fun h => hfree p hpp h hdvd
    omega
  have hlist : ∀ l : List ℕ, (∀ p ∈ l, P + 1 ≤ p) → (P + 1) ^ l.length ≤ l.prod := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro hl
      have ha : P + 1 ≤ a := hl a (List.mem_cons_self)
      have ht : ∀ p ∈ t, P + 1 ≤ p := fun p hp => hl p (List.mem_cons_of_mem a hp)
      have h1 : (P + 1) ^ (t.length + 1) ≤ t.prod * a := by
        rw [pow_succ]
        exact Nat.mul_le_mul (ih ht) ha
      rw [List.length_cons, List.prod_cons]
      calc (P + 1) ^ (t.length + 1) ≤ t.prod * a := h1
        _ = a * t.prod := by ring
  have hpow : (P + 1) ^ (n.factorization.sum (fun _ e => e)) ≤ n := by
    have h := hlist n.primeFactorsList hmem
    rw [Nat.prod_primeFactorsList hn0, ← hlen] at h
    exact h
  have hPr : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hP1 : (0 : ℝ) < (P : ℝ) + 1 := by linarith
  have hlogpos : 0 < Real.log ((P : ℝ) + 1) := Real.log_pos (by linarith)
  have hcast : ((P : ℝ) + 1) ^ (n.factorization.sum (fun _ e => e)) ≤ (n : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos hP1 _) hcast
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ hlogpos).mpr hlog

/-- **The size of the polar box in logarithmic form.**  For `z` in the polar box (5.14) and
`log x ≥ 1` one has `log |z|² ≤ log 2 + (log x)/2`.

Indeed `|z|² ≤ (1+θ)N ≤ 2N`, `N ≥ 1` and `N < x^{1/2}(log x)^{-B}` with `B > 0` and `log x ≥ 1`,
so `log N < (1/2) log x - B·log log x ≤ (1/2) log x`. -/
theorem log_gnorm_le_of_polarBox (Pa : Work.FITop.Params) (φ : ℝ) (z : GaussianInt)
    (hx : Real.exp 1 ≤ (Pa.x : ℝ)) (hbox : Work.FITop4.InPolarBox Pa φ z) :
    Real.log (Work.FIPlan.gnorm z : ℝ) ≤ Real.log 2 + Real.log (Pa.x : ℝ) / 2 := by
  obtain ⟨-, hNlt, hNle, -⟩ := hbox
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hlogx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at h
  have hlogxpos : 0 < Real.log (Pa.x : ℝ) := by linarith
  have hA'pos : 0 < Pa.A' := by
    have h2A : 0 < 2 * Pa.A := by linarith [Pa.hA]
    have h220 : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by norm_num
    linarith [Pa.hA', h2A, h220]
  have hθle1 : Pa.θ ≤ 1 := by
    rw [Pa.hθ]
    exact Real.rpow_le_one_of_one_le_of_nonpos hlogx1 (by linarith)
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hlogN : Real.log Pa.N ≤ Real.log (Pa.x : ℝ) / 2 := by
    have h1 : Real.log Pa.N
        < Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)) :=
      Real.log_lt_log hNpos Pa.hNhi
    have h2 : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B))
        = (1 / 2) * Real.log (Pa.x : ℝ) + (-Pa.B) * Real.log (Real.log (Pa.x : ℝ)) := by
      rw [Real.log_mul (by positivity)
            (ne_of_gt (Real.rpow_pos_of_pos hlogxpos _)),
          Real.log_rpow hxpos, Real.log_rpow hlogxpos]
    have h3 : (-Pa.B) * Real.log (Real.log (Pa.x : ℝ)) ≤ 0 := by
      have h4 : 0 ≤ Real.log (Real.log (Pa.x : ℝ)) := Real.log_nonneg hlogx1
      nlinarith [Pa.hB]
    rw [h2] at h1
    linarith
  have h2N : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
    have h : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [hθle1, hNpos]
    linarith
  have hngt0 : 0 < (Work.FIPlan.gnorm z : ℝ) := by linarith
  have hfin := Real.log_le_log hngt0 h2N
  rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at hfin
  linarith

/-- **The threshold of the τ-bound.**  For every `η > 0` there is `x₀` such that for `x ≥ x₀`,
`Pz ≥ 2`, `log Pz ≥ (log log x)²` and `log n ≤ log 2 + (log x)/2` one has
`(log n / log Pz) · log 2 ≤ (η/3) log x`.

The threshold is `exp(exp((3 log 2 + 6 (log 2)²)/η + 2))`: for `x ≥ x₀` one has both
`log x ≥ K := (3 log 2 + 6 (log 2)²)/η + 2` and `log log x ≥ K`, whence
`(log log x)² ≥ K ≥ 1`, `K·η ≥ 3 log 2` and `K·η ≥ 6 (log 2)²`.  The two elementary
inequalities `6 (log 2)² ≤ (log x)·η` (multiplied by `1 ≤ (log log x)²`) and
`3 log 2 ≤ (log log x)²·η` (multiplied by `log x ≥ 0`) then give
`(log 2 + (log x)/2)·log 2 ≤ (η/3)(log x)(log log x)² ≤ (η/3)(log x) log Pz`. -/
theorem exists_threshold_log_div_bound (η : ℝ) (hη : 0 < η) :
    ∃ x0 : ℝ, ∀ x Pz n : ℝ, x0 ≤ x → 2 ≤ Pz →
      (Real.log (Real.log x)) ^ 2 ≤ Real.log Pz →
      Real.log n ≤ Real.log 2 + Real.log x / 2 →
      (Real.log n / Real.log Pz) * Real.log 2 ≤ (η / 3) * Real.log x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.exp (Real.exp ((3 * Real.log 2 + 6 * (Real.log 2) ^ 2) / η + 2)), ?_⟩
  intro x Pz n hx hPz hPlo hlogn
  set K : ℝ := (3 * Real.log 2 + 6 * (Real.log 2) ^ 2) / η + 2 with hKdef
  have hKmul : K * η = 3 * Real.log 2 + 6 * (Real.log 2) ^ 2 + 2 * η := by
    rw [hKdef]; field_simp
  have hKpos : 0 < K := by
    have h1 : 0 ≤ (3 * Real.log 2 + 6 * (Real.log 2) ^ 2) / η :=
      div_nonneg (by positivity) hη.le
    rw [hKdef]; linarith
  have hKge1 : 1 ≤ K := by
    have h1 : 0 ≤ (3 * Real.log 2 + 6 * (Real.log 2) ^ 2) / η :=
      div_nonneg (by positivity) hη.le
    rw [hKdef]; linarith
  have hKη1 : 3 * Real.log 2 ≤ K * η := by
    rw [hKmul]; nlinarith [sq_nonneg (Real.log 2), hlog2.le, hη.le]
  have hKη2 : 6 * (Real.log 2) ^ 2 ≤ K * η := by
    rw [hKmul]; nlinarith [hlog2.le, hη.le]
  have hxpos : 0 < x := by
    have : 0 < Real.exp (Real.exp K) := Real.exp_pos _
    linarith
  have hLge : Real.exp K ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp K)) hx
    rwa [Real.log_exp] at h
  have hexpK_ge : K ≤ Real.exp K := by
    have := Real.add_one_le_exp K
    linarith
  have hL : K ≤ Real.log x := le_trans hexpK_ge hLge
  have hM : K ≤ Real.log (Real.log x) := by
    have h := Real.log_le_log (Real.exp_pos K) hLge
    rwa [Real.log_exp] at h
  have hLpos : 0 < Real.log x := lt_of_lt_of_le hKpos hL
  have hM2ge1 : 1 ≤ (Real.log (Real.log x)) ^ 2 := by nlinarith [hM, hKge1]
  have hLη : 6 * (Real.log 2) ^ 2 ≤ Real.log x * η := by
    have h : K * η ≤ Real.log x * η := mul_le_mul_of_nonneg_right hL hη.le
    linarith [hKη2]
  have hMη : 3 * Real.log 2 ≤ (Real.log (Real.log x)) ^ 2 * η := by
    have hK2 : K ≤ K ^ 2 := by nlinarith [hKge1]
    have h : K * η ≤ (Real.log (Real.log x)) ^ 2 * η :=
      mul_le_mul_of_nonneg_right (le_trans hK2 (by nlinarith [hM, hKpos])) hη.le
    linarith [hKη1]
  have hlogPzpos : 0 < Real.log Pz := lt_of_lt_of_le (by linarith [hM2ge1]) hPlo
  rw [div_mul_eq_mul_div, div_le_iff₀ hlogPzpos]
  have step1 : Real.log n * Real.log 2 ≤ (Real.log 2 + Real.log x / 2) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hlogn hlog2.le
  have step2 : (Real.log 2 + Real.log x / 2) * Real.log 2
      ≤ (η / 3) * Real.log x * Real.log Pz := by
    nlinarith [hPlo, hLη, hMη, hM2ge1, hlog2, hLpos, hη]
  linarith

/-- **The lemma.**  At any datum `Pa` with `η = Pa.η` and `x` large enough (in terms of `η`),
every point `z` of the polar box (5.14) free of small primes (5.8) satisfies the (5.9) divisor
bound at the *maximal* admissible cutoff `τ = x^{η/3}` of (5.23):

  `τ(|z|²) ≤ x^{η/3}`,

which is precisely `TauVac Pa φ` for `Pa` replaced by `tauMax Pa`. -/
theorem tau_le_tauMax_of_noSmallPrimes : ∀ η : ℝ, 0 < η → ∃ x0 : ℝ,
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η → ∀ (φ : ℝ) (z : GaussianInt),
      Work.FITop4.InPolarBox Pa φ z → Work.FITop4.NoSmallPrimes Pa z →
      (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ (Pa.x : ℝ) ^ (Pa.η / 3) := by
  intro η hη
  obtain ⟨x0n, hx0n⟩ := exists_threshold_log_div_bound η hη
  refine ⟨max x0n (Real.exp 1), ?_⟩
  intro Pa hx hηeq φ z hbox hns
  rw [hηeq]
  set N : ℕ := Work.FIPlan.gnorm z with hNdef
  have hx' : Real.exp 1 ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
  have hx0' : x0n ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the small-prime condition transferred to `N`
  have hfree : ∀ q : ℕ, q.Prime → q ≤ Pa.Pz → ¬ q ∣ N := by
    intro q hq hle
    rw [hNdef]
    exact hns q hq hle
  have hN1 : 1 ≤ N := by
    have h := hbox.2.1
    rw [← hNdef] at h
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by
      have h2 : (1 : ℝ) ≤ Pa.N := Pa.hN1
      linarith
    exact_mod_cast h1
  -- `τ(N) ≤ 2^{Ω N}`
  have hdiv : N.divisors.card ≤ 2 ^ N.factorization.sum (fun _ e => e) :=
    tau_le_two_pow_cardFactors N
  -- `Ω N ≤ log N / log(P+1)`
  have hΩ : ((N.factorization.sum fun _ e => e : ℕ) : ℝ)
      ≤ Real.log (N : ℝ) / Real.log ((Pa.Pz : ℝ) + 1) :=
    cardFactors_cast_le_log_div_log hN1 Pa.hP2 hfree
  -- `log N ≤ log 2 + (log x)/2`
  have hlogn : Real.log (N : ℝ) ≤ Real.log 2 + Real.log (Pa.x : ℝ) / 2 := by
    rw [hNdef]
    exact log_gnorm_le_of_polarBox Pa φ z hx' hbox
  -- the threshold comparison
  have hnum := hx0n (Pa.x : ℝ) (Pa.Pz : ℝ) (N : ℝ) hx0' (by exact_mod_cast Pa.hP2) Pa.hPlo hlogn
  -- `log(P+1) ≥ log P`, so `P + 1` may be replaced by `P`
  have hAB : Real.log (N : ℝ) / Real.log ((Pa.Pz : ℝ) + 1)
      ≤ Real.log (N : ℝ) / Real.log (Pa.Pz : ℝ) := by
    have hPz2 : (2 : ℝ) ≤ (Pa.Pz : ℝ) := by exact_mod_cast Pa.hP2
    have hlogNnn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
    have hlogPzpos : 0 < Real.log (Pa.Pz : ℝ) := Real.log_pos (by linarith)
    have hle : Real.log (Pa.Pz : ℝ) ≤ Real.log ((Pa.Pz : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    exact div_le_div_of_nonneg_left hlogNnn hlogPzpos hle
  -- the exponential form of the divisor count
  have hA2 : (((2 : ℕ) ^ N.factorization.sum (fun _ e => e) : ℕ) : ℝ)
      = Real.exp (Real.log 2 * ((N.factorization.sum (fun _ e => e) : ℕ) : ℝ)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast (2 : ℝ) (N.factorization.sum (fun _ e => e)),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have key : ((N.divisors.card : ℕ) : ℝ)
      ≤ Real.exp (Real.log (Pa.x : ℝ) * (η / 3)) :=
    calc ((N.divisors.card : ℕ) : ℝ)
        ≤ (((2 : ℕ) ^ N.factorization.sum (fun _ e => e) : ℕ) : ℝ) := by
          exact_mod_cast hdiv
      _ = Real.exp (Real.log 2 * ((N.factorization.sum (fun _ e => e) : ℕ) : ℝ)) := hA2
      _ ≤ Real.exp (Real.log 2 * (Real.log (N : ℝ) / Real.log (Pa.Pz : ℝ))) := by
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hlog2pos.le)
          exact le_trans hΩ hAB
      _ ≤ Real.exp (Real.log (Pa.x : ℝ) * (η / 3)) := by
          refine Real.exp_le_exp.mpr ?_
          rw [mul_comm (Real.log 2) (Real.log (N : ℝ) / Real.log (Pa.Pz : ℝ)),
            mul_comm (Real.log (Pa.x : ℝ)) (η / 3)]
          exact hnum
  rw [Real.rpow_def_of_pos hxpos]
  exact key

end Work.FIArea6V
