/-
# `Submission.Work.FIArea6.S16.truncation_regroup`

***FI* (16.30), the truncation regroup** — the `P·Q` half of the identity `Z(s) = M(s)·P(s)·Q(s)`
whose `M` half is `Submission.Work.FIArea6.S16.moebius_hecke_eulerProduct` (proved).

## The identity

With `Rad = ∏_{p ≤ Pz} p` and `λ = heckeLam χ k` (multiplicative, `‖χ z‖ ≤ 1`), in `Re s > 1`:

  `Σ'_n [n ⟂ Rad] μ(n)·γ(n;C)·λ(n)·n^{−s}`
  ` = Σ_{d ≤ C, d ⟂ Rad} [d squarefree]·λ(d)·d^{−s}·( Σ'_m [m ⟂ Rad, (m,d)=1] μ(m)·λ(m)·m^{−s} )`,

where `γ(n;C) = Σ_{d|n, d≤C} μ(d)` (*FI* (2.12)).

## Why the `[d squarefree]` restriction is part of the statement

This is the one place where the paper's compressed notation `Σ♭_{c≤C} λ(c)(…)c^{−s}` hides a real
restriction.  Expanding `γ` and writing `n = d·m` (so `m = n/d`, `d | n`), the LHS term is

  `μ(n)·λ(n)·n^{−s}·μ(d) = μ(d)μ(m)·λ(d)λ(m)·d^{−s}m^{−s}·μ(d)   =   μ(d)²·λ(d)λ(m)·d^{−s}m^{−s}`

(for `(d,m) = 1`; if `(d,m) ≠ 1` then `dm = n` is not squarefree and `μ(n) = 0`, so those terms
vanish and the coprime restriction on `m` loses nothing).  So the outer coefficient is `μ(d)²λ(d)`,
i.e. nonzero only for squarefree `d`, where it equals `λ(d)`.  Writing a bare `μ(d)λ(d)` would be a
*different, false* identity (it would pick up spurious `λ(4)·4^{−s}·(…)` terms).  Hence the
`Squarefree d` filter below — verified by the reviewer of this statement.

## Roadmap for the proof (the remaining work)

Only the order of summation has to be rearranged; the bijection is on *pairs*:

* `Σ'_n Σ_{d ∈ n.divisors.filter (· ≤ C)} (…)  =  Σ'_{(n,d) : d | n, d ≤ C} (…)` — pull the finite
  divisor sum inside the `tsum` (`Summable.tsum_finsetSum`/`tsum_sum`).
* Swap the two `tsum`s by `Summable.tsum_comm`, using absolute convergence in `Re s > 1`:
  `‖μ(n)γ(n;C)λ(n)n^{−s}‖ ≤ τ(n)·τ(n)·n^{−σ}` (`abs_gammaTrunc_le` for `γ`, `heckeLam_bound` for
  `λ`) and `Σ_n τ(n)²n^{−σ} < ∞` for `σ > 1` (`summable_card_divisors_mul_rpow_neg`).
* For each `d`, reindex `n ↦ m = n/d`: the map `m ↦ d·m` is a bijection onto `{n : d | n}`, and
  `[dm ⟂ Rad] = [d ⟂ Rad][m ⟂ Rad]`, `μ(dm) = μ(d)μ(m)`, `λ(dm) = λ(d)λ(m)` for `(d,m) = 1`
  (`ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime`,
  `Work.FIArea5.S16Hecke.heckeLam_mul`), `(dm)^{−s} = d^{−s}m^{−s}` (`mul_cpow`).
* Collect the `d`-sum: the conditions `d ∈ n.divisors`, `d ≤ C` become
  `d ∈ (Finset.Icc 1 ⌊C⌋₊).filter (· ⟂ Rad ∧ Squarefree ·)` (with `d = 1` the term `d = 0` never
  arises), and the `μ(d)²` becomes `1` on squarefree `d`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FITop3.Defs3
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea6.S16

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `∑_{j < m+1} (2j+1) = (m+1)^2` — the telescoping of the odd numbers. -/
private lemma sum_range_two_mul_add_one (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (2 * j + 1) = (m + 1) ^ 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- `n ↦ τ(n)²` as an arithmetic function. -/
private def tauSqF : ArithmeticFunction ℕ := ⟨fun n => n.divisors.card ^ 2, by simp⟩

/-- `n ↦ ∑_{d ∣ n} τ(d²)` as an arithmetic function. -/
private def tauSqG : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ n.divisors, (d ^ 2).divisors.card, by simp⟩

private lemma tauSqF_mult : tauSqF.IsMultiplicative := by
  refine ⟨by simp [tauSqF], ?_⟩
  intro m n hmn
  show (m * n).divisors.card ^ 2 = m.divisors.card ^ 2 * n.divisors.card ^ 2
  rw [Nat.Coprime.card_divisors_mul hmn]
  ring

/-- The divisor sum of a multiplicative-in-the-coprime-sense function is multiplicative: this is
`(ζ * H)(a b) = (ζ * H) a · (ζ * H) b` for `a ⟂ b`. -/
private lemma sum_divisors_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) (H : ℕ → ℕ)
    (hH : ∀ {x y : ℕ}, x.Coprime y → H (x * y) = H x * H y) :
    ∑ d ∈ (a * b).divisors, H d = (∑ d ∈ a.divisors, H d) * (∑ d ∈ b.divisors, H d) := by
  rw [Nat.divisors_mul, Finset.mul_def]
  rw [Finset.sum_image (hab.mul_injOn_divisors)]
  rw [Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  exact hH ((hab.coprime_dvd_left (Nat.mem_divisors.mp hx).1).coprime_dvd_right
    (Nat.mem_divisors.mp hy).1)

private lemma tauSqG_mult : tauSqG.IsMultiplicative := by
  refine ⟨by simp [tauSqG], ?_⟩
  intro m n hmn
  show (∑ d ∈ (m * n).divisors, (d ^ 2).divisors.card)
      = (∑ d ∈ m.divisors, (d ^ 2).divisors.card)
          * (∑ d ∈ n.divisors, (d ^ 2).divisors.card)
  exact sum_divisors_mul_of_coprime hmn (fun d => (d ^ 2).divisors.card) (fun {x y} hxy => by
    rw [← ArithmeticFunction.sigma_zero_apply, ← ArithmeticFunction.sigma_zero_apply,
      ← ArithmeticFunction.sigma_zero_apply]
    rw [mul_pow]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hxy.pow 2 2))

/-- **The divisor-count square identity** `τ(n)² = Σ_{d ∣ n} τ(d²)`, `τ(n) = n.divisors.card`
(*FI* uses it only through the consequent `Σ_n τ(n)²n^{−σ} < ∞` for `σ > 1`).

Both sides are multiplicative in `n` and agree on prime powers, where the content is the telescoping
identity `(a+1)² = Σ_{j=0}^{a} (2j+1)`: `τ(p^a)² = (a+1)²` and `Σ_{j} τ((p^j)²) = Σ_j (2j+1)`.
Hence the statement is an *equality*, not merely a bound.  Proof route in Mathlib terms: `τ` is
multiplicative and `n ↦ Σ_{d ∣ n} τ(d²)` is the divisor sum of the multiplicative function
`n ↦ τ(n²)`, so both are multiplicative
(`ArithmeticFunction.IsMultiplicative` + `ArithmeticFunction.IsMultiplicative.sum_divisors`), and a
multiplicative function is determined by its values on prime powers, which are computed with
`Nat.card_divisors` (`n.divisors.card = ∏ p ∈ n.primeFactors, (n.factorization p + 1)`). -/

lemma card_divisors_sq_eq_sum_card_divisors_sq (n : ℕ) :
    n.divisors.card ^ 2 = ∑ d ∈ n.divisors, (d ^ 2).divisors.card := by
  have hFG : tauSqF = tauSqG := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers tauSqF tauSqF_mult
      tauSqG tauSqG_mult]
    intro p i hp
    have hterm : ∀ j : ℕ, ((p ^ j) ^ 2).divisors.card = 2 * j + 1 := by
      intro j
      rw [← ArithmeticFunction.sigma_zero_apply]
      have hpj : (p ^ j) ^ 2 = p ^ (2 * j) := by rw [← pow_mul, Nat.mul_comm]
      rw [hpj]
      exact ArithmeticFunction.sigma_zero_apply_prime_pow hp
    have hL : (p ^ i).divisors.card = i + 1 := by
      rw [← ArithmeticFunction.sigma_zero_apply]
      exact ArithmeticFunction.sigma_zero_apply_prime_pow hp
    have hR : ∑ d ∈ (p ^ i).divisors, (d ^ 2).divisors.card = (i + 1) ^ 2 := by
      rw [Nat.divisors_prime_pow hp i, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk]
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      exact sum_range_two_mul_add_one i
    show (p ^ i).divisors.card ^ 2 = ∑ d ∈ (p ^ i).divisors, (d ^ 2).divisors.card
    rw [hL, hR]
  have hfun : (tauSqF : ℕ → ℕ) = tauSqG :=
    congrArg (fun f : ArithmeticFunction ℕ => (f : ℕ → ℕ)) hFG
  have hn := congrFun hfun n
  simpa [tauSqF, tauSqG] using hn

/-- **Step 1 of the truncation regroup**: the truncated Möbius factor `γ(n;C) = Σ_{d|n, d≤C} μ(d)`
(*FI* (2.12)) written as a sum over the index range `1 ≤ d ≤ ⌊C⌋₊`.

The hypothesis `n ≠ 0` is **necessary**: `Nat.divisors` is defined as `{d ∈ Ico 1 (n+1) | d ∣ n}`,
so `Nat.divisors 0 = ∅`, whereas `(Icc 1 ⌊C⌋₊).filter (· ∣ 0)` is all of `Icc 1 ⌊C⌋₊`; the
equivalence of the two index sets turns exactly on `Nat.le_of_dvd`, which needs `n ≠ 0`.  The
`μ`-weighted version consumed by the regroup holds for **all** `n`, because `μ 0 = 0` annihilates
both sides — that is how the `n = 0` term of the `tsum` dies.

Proof: rewrite both sides with `Finset.sum_filter` (resp. `unfold Nat.divisors`) and compare both to
the sum over the union `T = Ico 1 (n+1) ∪ Icc 1 ⌊C⌋₊` of `g d = if d ∣ n ∧ (d:ℝ) ≤ C then ↑(μ d)
else 0`, using `Finset.sum_subset` twice; `g` vanishes off `Ico 1 (n+1)` by `Nat.le_of_dvd` and off
`Icc 1 ⌊C⌋₊` by `Nat.le_floor_iff`. -/
lemma gammaTrunc_eq_sum_Icc (C : ℝ) (hC : 0 ≤ C) {n : ℕ} (hn : n ≠ 0) :
    Work.FIPlan.gammaTrunc C n
      = ∑ d ∈ (Finset.Icc 1 ⌊C⌋₊).filter (fun d => d ∣ n),
          (ArithmeticFunction.moebius d : ℝ) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  set T : Finset ℕ := Finset.Ico 1 (n + 1) ∪ Finset.Icc 1 ⌊C⌋₊ with hT
  set g : ℕ → ℝ :=
    fun d => if d ∣ n ∧ (d : ℝ) ≤ C then (ArithmeticFunction.moebius d : ℝ) else 0 with hg
  have hmemT1 : ∀ d : ℕ, d ∈ Finset.Ico 1 (n + 1) → d ∈ T := fun d hd => by
    rw [hT]; exact Finset.mem_union.mpr (Or.inl hd)
  have hmemT2 : ∀ d : ℕ, d ∈ Finset.Icc 1 ⌊C⌋₊ → d ∈ T := fun d hd => by
    rw [hT]; exact Finset.mem_union.mpr (Or.inr hd)
  have hzeroIco : ∀ d : ℕ, d ∈ T →
      d ∉ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n) → g d = 0 := by
    intro d hd hnf
    rw [hg]
    by_cases hcase : d ∣ n ∧ (d : ℝ) ≤ C
    · exfalso
      have hdIcc : d ∈ Finset.Icc 1 ⌊C⌋₊ := by
        rcases Finset.mem_union.mp (by rw [← hT]; exact hd) with h | h
        · exact absurd (Finset.mem_filter.mpr ⟨h, hcase.1⟩) hnf
        · exact h
      have hle : d ≤ n := Nat.le_of_dvd hnpos hcase.1
      exact hnf (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
        ⟨(Finset.mem_Icc.mp hdIcc).1, Nat.lt_succ_of_le hle⟩, hcase.1⟩)
    · simp [hcase]
  have hzeroIcc : ∀ d : ℕ, d ∈ T → d ∉ Finset.Icc 1 ⌊C⌋₊ → g d = 0 := by
    intro d hd hdn
    have hd' : d ∈ Finset.Ico 1 (n + 1) := by
      rcases Finset.mem_union.mp (by rw [← hT]; exact hd) with h | h
      · exact h
      · exact absurd h hdn
    rw [hg]
    by_cases hcase : d ∣ n ∧ (d : ℝ) ≤ C
    · exfalso
      exact hdn (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hd').1,
        (Nat.le_floor_iff hC).mpr hcase.2⟩)
    · simp [hcase]
  have hL : Work.FIPlan.gammaTrunc C n = ∑ d ∈ T, g d := by
    unfold Work.FIPlan.gammaTrunc Nat.divisors
    rw [Finset.sum_filter]
    rw [show (∑ d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n),
            (if (d : ℝ) ≤ C then (ArithmeticFunction.moebius d : ℝ) else 0))
          = ∑ d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n), g d from
        Finset.sum_congr rfl fun d hd => by
          have hdn : d ∣ n := (Finset.mem_filter.mp hd).2
          rw [hg]; simp only [hdn, true_and]]
    exact Finset.sum_subset (fun d hd => hmemT1 d (Finset.mem_filter.mp hd).1) hzeroIco
  have hR : (∑ d ∈ (Finset.Icc 1 ⌊C⌋₊).filter (fun d => d ∣ n),
          (ArithmeticFunction.moebius d : ℝ)) = ∑ d ∈ T, g d := by
    rw [Finset.sum_filter]
    rw [show (∑ d ∈ Finset.Icc 1 ⌊C⌋₊,
            (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0))
          = ∑ d ∈ Finset.Icc 1 ⌊C⌋₊, g d from
        Finset.sum_congr rfl fun d hd => by
          have hdle : (d : ℝ) ≤ C := (Nat.le_floor_iff hC).mp (Finset.mem_Icc.mp hd).2
          rw [hg]; by_cases hdvd : d ∣ n <;> simp [hdvd, hdle]]
    exact Finset.sum_subset (fun d hd => hmemT2 d hd) hzeroIcc
  rw [hL, hR]

/-- **Reindexing core of the truncation regroup.**  For `d ≥ 1`, the sum over the multiples of `d`
(with the divisibility indicator made explicit) is the sum of `g (d * m)` over `m`.  The bijection
`m ↦ d * m` is an equivalence onto the subtype of multiples of `d`; this is the one infinite
reindexing the regroup needs (the non-uniqueness of the factorisation `n = d·m` is harmless because
the bijection is on *pairs*). -/
lemma tsum_multiples_eq (d : ℕ) (hd : 1 ≤ d) (g : ℕ → ℂ) :
    (∑' n : ℕ, (if d ∣ n then g n else 0)) = ∑' m : ℕ, g (d * m) := by
  have hd0 : 0 < d := by omega
  let s : Set ℕ := {n : ℕ | d ∣ n}
  have hmem : ∀ n : ℕ, n ∈ s ↔ d ∣ n := fun n => Iff.rfl
  let e : ℕ ≃ s :=
    { toFun := fun m => ⟨d * m, (hmem (d * m)).mpr (dvd_mul_right d m)⟩
      invFun := fun n => (n : ℕ) / d
      left_inv := fun m => by
        show d * m / d = m
        rw [mul_comm d m]
        exact Nat.mul_div_left m hd0
      right_inv := fun n => by
        refine Subtype.ext ?_
        show d * ((n : ℕ) / d) = (n : ℕ)
        exact Nat.mul_div_cancel' ((hmem (n : ℕ)).mp n.2) }
  have hpoint : ∀ n : ℕ, (if d ∣ n then g n else 0) = Set.indicator s g n := by
    intro n
    by_cases hn : d ∣ n
    · rw [if_pos hn, Set.indicator_of_mem ((hmem n).mpr hn)]
    · rw [if_neg hn, Set.indicator_of_notMem (fun h => hn ((hmem n).mp h))]
  rw [show (∑' n : ℕ, (if d ∣ n then g n else 0))
      = ∑' n : ℕ, Set.indicator s g n from tsum_congr hpoint,
    ← tsum_subtype s g]
  exact (Equiv.tsum_eq e (fun n : s => g (n : ℕ))).symm

lemma summable_card_divisors_sq_mul_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ((n.divisors.card : ℝ) ^ 2) * (n : ℝ) ^ (-σ)) := by
  set e : ℝ := (σ - 1) / 4 with he
  have hepos : 0 < e := by rw [he]; linarith
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow e hepos
  have hexp : 2 * e - σ < -1 := by rw [he]; linarith
  have hmaj : Summable (fun n : ℕ => C ^ 2 * (n : ℝ) ^ (2 * e - σ)) :=
    (Real.summable_nat_rpow.mpr hexp).mul_left (C ^ 2)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Nat.divisors_zero, Real.zero_rpow (by linarith : (-σ) ≠ 0),
      Real.zero_rpow (by linarith : (2 * e - σ) ≠ 0)]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hτ0 : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
    have h1 : ((n.divisors.card : ℝ)) ^ 2 ≤ (C * (n : ℝ) ^ e) ^ 2 :=
      pow_le_pow_left₀ hτ0 (hC n) 2
    have hkey : ((n : ℝ) ^ e) ^ 2 * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (2 * e - σ) := by
      have h2 : ((n : ℝ) ^ e) ^ 2 = ((n : ℝ) ^ e) ^ (2 : ℝ) :=
        (Real.rpow_natCast ((n : ℝ) ^ e) 2).symm
      rw [h2, ← Real.rpow_mul (le_of_lt hnpos) e 2, ← Real.rpow_add hnpos]
      rw [show e * 2 + -σ = 2 * e - σ by ring]
    calc ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)
        ≤ (C * (n : ℝ) ^ e) ^ 2 * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = C ^ 2 * (n : ℝ) ^ (2 * e - σ) := by
          rw [mul_pow, mul_assoc, hkey]

/-- The Möbius-twisted Hecke sum of the truncation regroup is absolutely convergent for
`Re s > 1`: the term is bounded by `4 τ(n)² n^{-σ}`. -/
lemma summable_moebius_gammaTrunc_heckeLam
    (chi : GaussianInt → ℂ) (k : ℤ) (C : ℝ) (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)
      * (Work.FIPlan.gammaTrunc C n : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k n
      * (n : ℂ) ^ (-s)) := by
  have hbase : Summable (fun n : ℕ =>
      (4 : ℝ) * (((n.divisors.card : ℝ) ^ 2) * (n : ℝ) ^ (-s.re))) :=
    (summable_card_divisors_sq_mul_rpow_neg hs).mul_left 4
  refine Summable.of_norm_bounded hbase (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Nat.divisors_zero, Real.zero_rpow (ne_of_lt (by linarith : -s.re < 0))]
  · have hn1 : 1 ≤ n := hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    have hγ : ‖((Work.FIPlan.gammaTrunc C n : ℝ) : ℂ)‖ ≤ (n.divisors.card : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.FITop3.abs_gammaTrunc_le C n
    have hlam : ‖Work.FIArea5.S16Hecke.heckeLam chi k n‖ ≤ 4 * (n.divisors.card : ℝ) :=
      Work.FIArea5.S16Hecke.heckeLam_bound chi k hchi hn1
    have hns : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
    calc ‖(ArithmeticFunction.moebius n : ℂ) * (Work.FIPlan.gammaTrunc C n : ℂ)
            * Work.FIArea5.S16Hecke.heckeLam chi k n * (n : ℂ) ^ (-s)‖
        = ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖(Work.FIPlan.gammaTrunc C n : ℂ)‖
            * ‖Work.FIArea5.S16Hecke.heckeLam chi k n‖ * ‖(n : ℂ) ^ (-s)‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ 1 * (n.divisors.card : ℝ) * (4 * (n.divisors.card : ℝ)) * (n : ℝ) ^ (-s.re) := by
          rw [hns]
          have hAB : ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖(Work.FIPlan.gammaTrunc C n : ℂ)‖
              ≤ 1 * (n.divisors.card : ℝ) :=
            mul_le_mul hμ hγ (by positivity) (by norm_num)
          have hABD : ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖(Work.FIPlan.gammaTrunc C n : ℂ)‖
              * ‖Work.FIArea5.S16Hecke.heckeLam chi k n‖
              ≤ 1 * (n.divisors.card : ℝ) * (4 * (n.divisors.card : ℝ)) :=
            mul_le_mul hAB hlam (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hABD (by positivity)
      _ = 4 * (((n.divisors.card : ℝ) ^ 2) * (n : ℝ) ^ (-s.re)) := by ring


/-- The `μ`-weighted truncated Möbius factor as a divisor sum over `Icc 1 ⌊C⌋₊`, valid for **all**
`n` (at `n = 0` both sides vanish because `μ 0 = 0`). -/
lemma moebius_mul_gammaTrunc_eq_sum_Icc (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    (ArithmeticFunction.moebius n : ℂ) * (Work.FIPlan.gammaTrunc C n : ℂ)
      = (ArithmeticFunction.moebius n : ℂ) *
          ∑ d ∈ (Finset.Icc 1 ⌊C⌋₊).filter (fun d => d ∣ n),
            (ArithmeticFunction.moebius d : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [gammaTrunc_eq_sum_Icc C hC hn]
    push_cast
    ring

/-- `‖μ(m)·λ(m)·m^{-s}‖ ≤ 4·τ(m)²·m^{-σ}`. -/
lemma norm_moebius_heckeLam_le (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
        * (m : ℂ) ^ (-s)‖
      ≤ 4 * (((m.divisors.card : ℝ) ^ 2) * (m : ℝ) ^ (-s.re)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [ArithmeticFunction.map_zero, Nat.divisors_zero,
      Real.zero_rpow (show (-s.re) ≠ 0 by linarith)]
  · have hm1 : 1 ≤ m := hm
    have hμ : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
    have hlam : ‖Work.FIArea5.S16Hecke.heckeLam chi k m‖ ≤ 4 * (m.divisors.card : ℝ) :=
      Work.FIArea5.S16Hecke.heckeLam_bound chi k hchi hm1
    have hns : ‖(m : ℂ) ^ (-s)‖ = (m : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hm, Complex.neg_re]
    have hτ1 : (1 : ℝ) ≤ (m.divisors.card : ℝ) := by
      have h : 0 < m.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      exact_mod_cast h
    rw [norm_mul, norm_mul, hns]
    have hx : 0 ≤ (m : ℝ) ^ (-s.re) := by positivity
    have hτ2 : (m.divisors.card : ℝ) ≤ (m.divisors.card : ℝ) ^ 2 := by nlinarith [hτ1]
    calc ‖(ArithmeticFunction.moebius m : ℂ)‖ * ‖Work.FIArea5.S16Hecke.heckeLam chi k m‖
            * (m : ℝ) ^ (-s.re)
        ≤ 1 * (4 * (m.divisors.card : ℝ)) * (m : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hμ hlam (by positivity) (by norm_num)) hx
      _ = 4 * ((m.divisors.card : ℝ) * (m : ℝ) ^ (-s.re)) := by ring
      _ ≤ 4 * (((m.divisors.card : ℝ) ^ 2) * (m : ℝ) ^ (-s.re)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hτ2 hx

/-- The same bound with the extra factor `μ(d)` (of modulus `≤ 1`). -/
lemma norm_moebius_mul_moebius_heckeLam_le (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) (d m : ℕ) :
    ‖(ArithmeticFunction.moebius m : ℂ) * (ArithmeticFunction.moebius d : ℂ)
        * Work.FIArea5.S16Hecke.heckeLam chi k m * (m : ℂ) ^ (-s)‖
      ≤ 4 * (((m.divisors.card : ℝ) ^ 2) * (m : ℝ) ^ (-s.re)) := by
  have hB : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hEq : (ArithmeticFunction.moebius m : ℂ) * (ArithmeticFunction.moebius d : ℂ)
        * Work.FIArea5.S16Hecke.heckeLam chi k m * (m : ℂ) ^ (-s)
      = ((ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
          * (m : ℂ) ^ (-s)) * (ArithmeticFunction.moebius d : ℂ) := by ring
  rw [hEq, norm_mul]
  calc ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
          * (m : ℂ) ^ (-s)‖ * ‖(ArithmeticFunction.moebius d : ℂ)‖
      ≤ ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
          * (m : ℂ) ^ (-s)‖ * 1 := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
          * (m : ℂ) ^ (-s)‖ := mul_one _
    _ ≤ 4 * (((m.divisors.card : ℝ) ^ 2) * (m : ℝ) ^ (-s.re)) :=
        norm_moebius_heckeLam_le chi k hchi hs m

/-- Absolute convergence of the `P`-side coefficients, with an arbitrary decidable restriction. -/
lemma summable_if_moebius_heckeLam (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (P : ℕ → Prop) [DecidablePred P] :
    Summable (fun m : ℕ => if P m then
      (ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
        * (m : ℂ) ^ (-s) else 0) := by
  refine Summable.of_norm_bounded ((summable_card_divisors_sq_mul_rpow_neg hs).mul_left 4)
    (fun m => ?_)
  by_cases hP : P m
  · rw [if_pos hP]
    exact norm_moebius_heckeLam_le chi k hchi (by linarith) m
  · rw [if_neg hP, norm_zero]
    positivity

/-- Absolute convergence of the summands of the truncated-`γ` expansion at fixed `d`. -/
lemma summable_truncSummand (chi : GaussianInt → ℂ) (k : ℤ) (Pz : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) (d : ℕ) :
    Summable (fun n : ℕ => if d ∣ n then (if n.Coprime
        (∏ p ∈ Nat.primesBelow (Pz + 1), p) then
      (ArithmeticFunction.moebius n : ℂ) * (ArithmeticFunction.moebius d : ℂ)
        * Work.FIArea5.S16Hecke.heckeLam chi k n * (n : ℂ) ^ (-s) else 0) else 0) := by
  refine Summable.of_norm_bounded ((summable_card_divisors_sq_mul_rpow_neg hs).mul_left 4)
    (fun n => ?_)
  by_cases hd : d ∣ n
  · rw [if_pos hd]
    by_cases hn : n.Coprime (∏ p ∈ Nat.primesBelow (Pz + 1), p)
    · rw [if_pos hn]
      exact norm_moebius_mul_moebius_heckeLam_le chi k hchi (by linarith) d n
    · rw [if_neg hn, norm_zero]; positivity
  · rw [if_neg hd, norm_zero]; positivity
/-- ***FI* (16.30), the truncation regroup (the `P·Q` half of `Z = M·P·Q`).** -/
theorem truncation_regroup (chi : GaussianInt → ℂ) (k : ℤ) (Pz : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hchi1 : chi 1 = 1) (hchi : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchi_bd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (if n.Coprime (∏ p ∈ Nat.primesBelow (Pz + 1), p) then
        (ArithmeticFunction.moebius n : ℂ) * (Work.FIPlan.gammaTrunc C n : ℂ)
          * Work.FIArea5.S16Hecke.heckeLam chi k n * (n : ℂ) ^ (-s) else 0))
      = ∑ d ∈ (Finset.Icc 1 ⌊C⌋₊).filter
            (fun d => d.Coprime (∏ p ∈ Nat.primesBelow (Pz + 1), p) ∧ Squarefree d),
          (Work.FIArea5.S16Hecke.heckeLam chi k d : ℂ) * (d : ℂ) ^ (-s) *
            (∑' m : ℕ, (if m.Coprime (∏ p ∈ Nat.primesBelow (Pz + 1), p) ∧ d.Coprime m then
              (ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
                * (m : ℂ) ^ (-s) else 0)) := by
  classical
  set Rad : ℕ := ∏ p ∈ Nat.primesBelow (Pz + 1), p with hRad
  set D : Finset ℕ := Finset.Icc 1 ⌊C⌋₊ with hD
  set H : ℕ → ℕ → ℂ := fun d n => if d ∣ n then (if n.Coprime Rad then
      (ArithmeticFunction.moebius n : ℂ) * (ArithmeticFunction.moebius d : ℂ)
        * Work.FIArea5.S16Hecke.heckeLam chi k n * (n : ℂ) ^ (-s) else 0) else 0 with hH
  set inner : ℕ → ℂ := fun d => ∑' m : ℕ, (if m.Coprime Rad ∧ d.Coprime m then
      (ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
        * (m : ℂ) ^ (-s) else 0) with hinner
  -- auxiliary convergence facts
  have hsummand : ∀ d, Summable (fun n => H d n) := by
    intro d
    simp only [hH]
    exact summable_truncSummand chi k Pz hchi_bd hs d
  have hinner_summ : ∀ d : ℕ, Summable (fun m : ℕ => if m.Coprime Rad ∧ d.Coprime m then
      (ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
        * (m : ℂ) ^ (-s) else 0) := by
    intro d
    exact summable_if_moebius_heckeLam chi k hchi_bd hs
      (fun m => m.Coprime Rad ∧ d.Coprime m)
  -- step 1: expand the truncated Möbius factor
  have hstep1 : (∑' n : ℕ, (if n.Coprime Rad then
        (ArithmeticFunction.moebius n : ℂ) * (Work.FIPlan.gammaTrunc C n : ℂ)
          * Work.FIArea5.S16Hecke.heckeLam chi k n * (n : ℂ) ^ (-s) else 0))
      = ∑' n : ℕ, ∑ d ∈ D, H d n := by
    refine tsum_congr (fun n => ?_)
    by_cases hn : n.Coprime Rad
    · rw [if_pos hn, moebius_mul_gammaTrunc_eq_sum_Icc C hC n]
      simp only [hH]
      rw [← Finset.sum_filter]
      rw [Finset.sum_congr rfl (fun d _ => if_pos hn)]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    · rw [if_neg hn]
      simp only [hH]
      refine (Finset.sum_eq_zero (fun d _ => ?_)).symm
      by_cases hd : d ∣ n
      · rw [if_pos hd, if_neg hn]
      · rw [if_neg hd]
  -- step 2: swap the finite `d`-sum and the `n`-sum
  have hswap : (∑' n : ℕ, ∑ d ∈ D, H d n) = ∑ d ∈ D, ∑' n : ℕ, H d n :=
    Summable.tsum_finsetSum (s := D) (f := H) (fun d _ => hsummand d)
  -- step 3: reindex `n = d * m` and collapse the Möbius factor
  have hK : ∀ d m : ℕ, (if (d * m).Coprime Rad then
        (ArithmeticFunction.moebius (d * m) : ℂ) * (ArithmeticFunction.moebius d : ℂ)
          * Work.FIArea5.S16Hecke.heckeLam chi k (d * m) * ((d * m : ℕ) : ℂ) ^ (-s) else 0)
      = (if d.Coprime Rad ∧ Squarefree d then
            Work.FIArea5.S16Hecke.heckeLam chi k d * (d : ℂ) ^ (-s) else 0)
        * (if m.Coprime Rad ∧ d.Coprime m then
            (ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
              * (m : ℂ) ^ (-s) else 0) := by
    intro d m
    by_cases h : (d.Coprime Rad ∧ Squarefree d) ∧ (m.Coprime Rad ∧ d.Coprime m)
    · obtain ⟨⟨hdP, hds⟩, ⟨hmP, hdm⟩⟩ := h
      have hdmP : (d * m).Coprime Rad := Nat.Coprime.mul_left hdP hmP
      rw [if_pos hdmP, if_pos ⟨hdP, hds⟩, if_pos ⟨hmP, hdm⟩]
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        simp [ArithmeticFunction.map_zero]
      · have hd0 : 0 < d := Nat.pos_of_ne_zero hds.ne_zero
        have h1 : (ArithmeticFunction.moebius (d * m) : ℂ)
            = (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.moebius m : ℂ) := by
          rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hdm]
          push_cast
          ring
        have h2 : Work.FIArea5.S16Hecke.heckeLam chi k (d * m)
            = Work.FIArea5.S16Hecke.heckeLam chi k d
              * Work.FIArea5.S16Hecke.heckeLam chi k m :=
          Work.FIArea5.S16Hecke.heckeLam_mul chi k hchi hd0 hm0 hdm
        have h3 : ((d * m : ℕ) : ℂ) ^ (-s) = (d : ℂ) ^ (-s) * (m : ℂ) ^ (-s) := by
          rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        rw [h1, h2, h3]
        have hμd : (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.moebius d : ℂ) = 1 := by
          have hh := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hds
          rw [pow_two] at hh
          exact_mod_cast hh
        linear_combination (ArithmeticFunction.moebius m : ℂ)
          * Work.FIArea5.S16Hecke.heckeLam chi k d * Work.FIArea5.S16Hecke.heckeLam chi k m
          * (d : ℂ) ^ (-s) * (m : ℂ) ^ (-s) * hμd
    · have hL0 : (if (d * m).Coprime Rad then
          (ArithmeticFunction.moebius (d * m) : ℂ) * (ArithmeticFunction.moebius d : ℂ)
            * Work.FIArea5.S16Hecke.heckeLam chi k (d * m) * ((d * m : ℕ) : ℂ) ^ (-s) else 0) = 0 := by
        by_cases hdmP : (d * m).Coprime Rad
        · rw [if_pos hdmP]
          have hdP : d.Coprime Rad := Nat.Coprime.coprime_dvd_left (dvd_mul_right d m) hdmP
          have hmP : m.Coprime Rad := Nat.Coprime.coprime_dvd_left (dvd_mul_left m d) hdmP
          by_cases hds : Squarefree d
          · have hdm : ¬ d.Coprime m := fun hdm => h ⟨⟨hdP, hds⟩, ⟨hmP, hdm⟩⟩
            have hnsq : ¬ Squarefree (d * m) := by
              obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd (show d.gcd m ≠ 1 from hdm)
              have hpd : p ∣ d := (Nat.dvd_gcd_iff.mp hpgcd).1
              have hpm : p ∣ m := (Nat.dvd_gcd_iff.mp hpgcd).2
              rw [Nat.squarefree_iff_prime_squarefree]
              push_neg
              refine ⟨p, hp, ?_⟩
              obtain ⟨d', rfl⟩ := hpd
              obtain ⟨m', rfl⟩ := hpm
              exact ⟨d' * m', by ring⟩
            rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
            ring
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hds]
            ring
        · rw [if_neg hdmP]
      have hR0 : (if d.Coprime Rad ∧ Squarefree d then
            Work.FIArea5.S16Hecke.heckeLam chi k d * (d : ℂ) ^ (-s) else 0)
          * (if m.Coprime Rad ∧ d.Coprime m then
            (ArithmeticFunction.moebius m : ℂ) * Work.FIArea5.S16Hecke.heckeLam chi k m
              * (m : ℂ) ^ (-s) else 0) = 0 := by
        by_cases hA : d.Coprime Rad ∧ Squarefree d
        · rw [if_pos hA, if_neg (fun hB => h ⟨hA, hB⟩), mul_zero]
        · rw [if_neg hA, zero_mul]
      rw [hL0, hR0]
  have hreindex : ∀ d ∈ D, (∑' n : ℕ, H d n) = ∑' m : ℕ, (if (d * m).Coprime Rad then
        (ArithmeticFunction.moebius (d * m) : ℂ) * (ArithmeticFunction.moebius d : ℂ)
          * Work.FIArea5.S16Hecke.heckeLam chi k (d * m) * ((d * m : ℕ) : ℂ) ^ (-s) else 0) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (by rw [hD] at hd; exact hd)).1
    simp only [hH]
    exact tsum_multiples_eq d hd1 (fun n => if n.Coprime Rad then
      (ArithmeticFunction.moebius n : ℂ) * (ArithmeticFunction.moebius d : ℂ)
        * Work.FIArea5.S16Hecke.heckeLam chi k n * (n : ℂ) ^ (-s) else 0)
  calc (∑' n : ℕ, (if n.Coprime Rad then
        (ArithmeticFunction.moebius n : ℂ) * (Work.FIPlan.gammaTrunc C n : ℂ)
          * Work.FIArea5.S16Hecke.heckeLam chi k n * (n : ℂ) ^ (-s) else 0))
      = ∑' n : ℕ, ∑ d ∈ D, H d n := hstep1
    _ = ∑ d ∈ D, ∑' n : ℕ, H d n := hswap
    _ = ∑ d ∈ D, (if d.Coprime Rad ∧ Squarefree d then
          Work.FIArea5.S16Hecke.heckeLam chi k d * (d : ℂ) ^ (-s) else 0) * inner d := by
        refine Finset.sum_congr rfl (fun d hd => ?_)
        rw [hreindex d hd]
        rw [tsum_congr (fun m => hK d m)]
        rw [Summable.tsum_mul_left _ (hinner_summ d)]
    _ = ∑ d ∈ D, (if d.Coprime Rad ∧ Squarefree d then
          Work.FIArea5.S16Hecke.heckeLam chi k d * (d : ℂ) ^ (-s) * inner d else 0) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        by_cases hp : d.Coprime Rad ∧ Squarefree d <;> simp [hp]
    _ = ∑ d ∈ D.filter (fun d => d.Coprime Rad ∧ Squarefree d),
          Work.FIArea5.S16Hecke.heckeLam chi k d * (d : ℂ) ^ (-s) * inner d := by
        rw [← Finset.sum_filter]

end

end Work.FIArea6.S16
