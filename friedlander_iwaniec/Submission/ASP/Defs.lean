/-
  Companion paper ("Asymptotic sieve for primes", Friedlander–Iwaniec,
  Ann. of Math. 148 (1998) 1041–1065): definitions and the combinatorial layer of §3.

  Everything here is stated for an abstract sequence `a : ℕ → ℝ` and an abstract
  upper-bound sieve `λ : ℕ → ℝ` with `ρ n = ∑_{ν ∣ n} λ ν`; the concrete instantiation
  `a n = #{p ∈ ℤ² : p₁² + p₂⁴ = n}` lives in the main paper's development.
-/
import Mathlib
import Submission.Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_log_eq

namespace Submission.ASP

open Finset

noncomputable section

/-- `A(x) = ∑_{n ≤ x} a n` — the counting function (1.3) of the companion paper. -/
def Acount (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

/-- `A_d(x) = ∑_{n ≤ x, d ∣ n} a n` — the congruence sum (1.5). -/
def Ad (a : ℕ → ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => d ∣ n), a n

/-- The density hypothesis (1.7) of the companion paper: `A_d(x) = g(d)·A(x) + r_d(x)`
for every modulus `d` and every scale `m ≤ ⌊x⌋₊` (for `d > m` this says `r_d(m) = −g(d)A(m)`,
which is the convention used in §4). -/
def Approx (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ d m : ℕ, Ad a d m = g d * Acount a m + r d m

/-- The `(R′)`-type remainder hypothesis of §§2 and 4: `∑_{d ≤ D, ♭} τ(d)^5 |r_d(m)|`.
The companion's (R′) reads `∑_{d ≤ D} μ²(d)τ(d)^5|r_d(m)| ≪ A(x)(log x)^{-3}`, i.e. the sum is
restricted to **squarefree** `d`; this restriction is what §4 can actually use, since only
squarefree `ν, b` occur there (the sieve weight `λ` is squarefree-supported and the `b`-sum carries
`μ`).  The unrestricted sum `∑_{d ≤ D} τ(d)^5|r_d(m)|` is *not* implied by (R′). -/
def RemainderSum (r : ℕ → ℕ → ℝ) (D m : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, ((d.divisors.card : ℝ)) ^ 5 * |r d m|

/-- The upper-bound-sieve weight `ρ n = ∑_{ν ∣ n} λ ν`; the companion requires `ρ n ≥ 0`,
`λ 1 = 1` and `|λ ν| ≤ 1` with `λ` supported on `[1, Δ]` (see §3). -/
def rhoOf (lam : ℕ → ℝ) (n : ℕ) : ℝ := ∑ ν ∈ n.divisors, lam ν

/-- `L(n; y) = ∑_{b ∣ n, b ≤ y} μ(b)·(log n − log b)`, the truncated logarithm arising
from `L(n; Y) = ∑_{b ∣ n} μ(b ≤ Y)·L(n/b)` in §3 with `L = log`. -/
def logWeight (n : ℕ) (y : ℝ) : ℝ :=
  ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
    (ArithmeticFunction.moebius b : ℝ) * (Real.log (n : ℝ) - Real.log (b : ℝ))

/-- `V_b(x) = ∑_{n ≤ x, b ∣ n} a n · ρ n`. -/
def Vb (a : ℕ → ℝ) (lam : ℕ → ℝ) (b : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => b ∣ n), a n * rhoOf lam n

/-- `V_b(x) · log x`-type sum: `∑_{n ≤ x, b ∣ n} a n ρ n log n`. -/
def VbLog (a : ℕ → ℝ) (lam : ℕ → ℝ) (b : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => b ∣ n), a n * rhoOf lam n * Real.log n

/-- `T(x; y) = ∑_{n ≤ x} a n ρ n L(n; y)` — the first sum of (3.4). -/
def Tsum (a : ℕ → ℝ) (lam : ℕ → ℝ) (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * rhoOf lam n * logWeight n y

/-- `T(x; y, z) = ∑_{b ≤ y} μ(b) ∑_{c ≤ z} Λ(c) ∑_{n ≤ x} a n ρ n L(n; bc)` (5.1). -/
def Tsum2 (a : ℕ → ℝ) (lam : ℕ → ℝ) (x y z : ℝ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
    (ArithmeticFunction.moebius b : ℝ) *
      ∑ c ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun c => ((c : ℕ) : ℝ) ≤ z),
        ArithmeticFunction.vonMangoldt c * Vb a lam (b * c) x


/-! ### The Möbius/divisor reshuffle underlying (4.1) -/

/-- For `n ∈ Icc 1 N`, the divisors of `n` filtered by `b ≤ y` sit inside `Icc 1 N` and
can be written as the intersection of that interval with `{b : b ∣ n, b ≤ y}`. -/
lemma divisors_filter_eq {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) (y : ℝ) :
    n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y)
      = (Finset.Icc 1 N).filter (fun b => b ∣ n ∧ ((b : ℕ) : ℝ) ≤ y) := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hn0 : n ≠ 0 := by omega
  ext b
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hbd, _⟩, hby⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hbd (by omega),
      le_trans (Nat.le_of_dvd (by omega) hbd) hnN⟩, hbd, hby⟩
  · rintro ⟨_, hbd, hby⟩
    exact ⟨⟨hbd, hn0⟩, hby⟩

/-- Exchange the order of summation in `∑_{n ≤ N} ∑_{b ∣ n, b ≤ y}`. -/
theorem sum_divisors_filter_swap {N : ℕ} (y : ℝ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y), F n b)
      = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n), F n b := by
  have hL : (∑ n ∈ Finset.Icc 1 N,
        ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y), F n b)
      = ∑ n ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          (if b ∣ n ∧ ((b : ℕ) : ℝ) ≤ y then F n b else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [divisors_filter_eq hn y, Finset.sum_filter]
  rw [hL, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : ((b : ℕ) : ℝ) ≤ y
  · rw [if_pos hb]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hbn : b ∣ n <;> simp [hbn, hb]
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro n _
    by_cases hbn : b ∣ n <;> simp [hbn, hb]

/-! ### The identity `T = T₁ + T₂` of §4, equations (4.1)–(4.4) -/

/-- **(4.1)–(4.4)**: `T(x; y) = T₁(x;y) + T₂(x;y)` with
`T₁ = ∑_{b ≤ y} μ(b) ∑_{b ∣ n ≤ x} aₙρₙ log n` and
`T₂ = −∑_{b ≤ y} μ(b) log b ∑_{b ∣ n ≤ x} aₙρₙ`. -/
theorem Tsum_eq (a lam : ℕ → ℝ) (x y : ℝ) :
    Tsum a lam x y
      = (∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ) * VbLog a lam b x)
        - ∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ) * Vb a lam b x := by
  have hexp : Tsum a lam x y
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
          a n * rhoOf lam n * ((ArithmeticFunction.moebius b : ℝ)
            * (Real.log (n : ℝ) - Real.log (b : ℝ))) := by
    rw [Tsum]
    apply Finset.sum_congr rfl
    intro n _
    rw [logWeight, Finset.mul_sum]
  have hsplit : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
          a n * rhoOf lam n * ((ArithmeticFunction.moebius b : ℝ)
            * (Real.log (n : ℝ) - Real.log (b : ℝ))))
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
          a n * rhoOf lam n * ((ArithmeticFunction.moebius b : ℝ) * Real.log (n : ℝ)))
        - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
          a n * rhoOf lam n * ((ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hexp, hsplit]
  congr 1
  · rw [sum_divisors_filter_swap y (fun n b =>
        a n * rhoOf lam n * ((ArithmeticFunction.moebius b : ℝ) * Real.log (n : ℝ)))]
    apply Finset.sum_congr rfl
    intro b _
    rw [VbLog, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  · rw [sum_divisors_filter_swap y (fun n b =>
        a n * rhoOf lam n * ((ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)))]
    apply Finset.sum_congr rfl
    intro b _
    rw [Vb, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring

/-- For `0 < n ≤ N`, the divisors of `n` are exactly the elements of `Icc 1 N` that divide `n`. -/
lemma divisors_eq_filter_Icc {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    n.divisors = (Finset.Icc 1 N).filter (fun ν => ν ∣ n) := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hn0 : n ≠ 0 := by omega
  ext ν
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨hνd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hνd (by omega),
      le_trans (Nat.le_of_dvd (by omega) hνd) hnN⟩, hνd⟩
  · rintro ⟨_, hνd⟩
    exact ⟨hνd, hn0⟩

/-- Exchange the order of summation in `∑_{n ≤ N, Q n} ∑_{ν ∣ n}`. -/
theorem sum_filter_divisors_swap {N : ℕ} (Q : ℕ → Prop) [DecidablePred Q]
    (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter Q, ∑ ν ∈ n.divisors, F n ν)
      = ∑ ν ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Q n ∧ ν ∣ n), F n ν := by
  have hL : (∑ n ∈ (Finset.Icc 1 N).filter Q, ∑ ν ∈ n.divisors, F n ν)
      = ∑ n ∈ Finset.Icc 1 N, ∑ ν ∈ Finset.Icc 1 N,
          (if Q n ∧ ν ∣ n then F n ν else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    rw [divisors_eq_filter_Icc hn, Finset.sum_filter]
    by_cases hq : Q n
    · simp only [if_pos hq]
      apply Finset.sum_congr rfl
      intro ν _
      by_cases hν : ν ∣ n <;> simp [hq, hν]
    · simp only [if_neg hq]
      rw [Finset.sum_eq_zero]
      intro ν _
      simp [hq]
  rw [hL, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  rw [Finset.sum_filter]

/-- Exchange the order of summation in `∑_{n ≤ N} ∑_{ν ∣ n}`. -/
theorem sum_divisors_swap {N : ℕ} (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ ν ∈ n.divisors, F n ν)
      = ∑ ν ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ν ∣ n), F n ν := by
  have h := sum_filter_divisors_swap (N := N) (fun _ => True) F
  simpa using h

/-- **The congruence sums through the sieve**: `V_b(x) = ∑_ν λ_ν A_{ν,b}(x)`, i.e.
`∑_{n ≤ x, b ∣ n} aₙρₙ = ∑_ν λ_ν ∑_{n ≤ x, lcm(ν,b) ∣ n} aₙ` (equation (4.3)). -/
theorem Vb_eq_sum_lcm (a lam : ℕ → ℝ) (b : ℕ) (x : ℝ) :
    Vb a lam b x
      = ∑ ν ∈ Finset.Icc 1 ⌊x⌋₊, lam ν * Ad a (Nat.lcm ν b) x := by
  have h1 : Vb a lam b x
      = ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => b ∣ n),
          ∑ ν ∈ n.divisors, a n * lam ν := by
    unfold Vb rhoOf
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
  have h2 : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => b ∣ n),
          ∑ ν ∈ n.divisors, a n * lam ν)
      = ∑ ν ∈ Finset.Icc 1 ⌊x⌋₊,
          ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => b ∣ n ∧ ν ∣ n), a n * lam ν :=
    sum_filter_divisors_swap (N := ⌊x⌋₊) (fun n => b ∣ n) (fun n ν => a n * lam ν)
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro ν _
  have hfil : (Finset.Icc 1 ⌊x⌋₊).filter (fun n => b ∣ n ∧ ν ∣ n)
      = (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.lcm ν b ∣ n) := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, Nat.lcm_dvd_iff.mpr ⟨h.2.2, h.2.1⟩⟩,
      fun h => ⟨h.1, (Nat.lcm_dvd_iff.mp h.2).2, (Nat.lcm_dvd_iff.mp h.2).1⟩⟩
  rw [Ad, hfil, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-! ### Counting pairs with a prescribed `lcm` -/

/-- The number of pairs `(a,b) ∈ S × T` with `lcm a b = d` is at most `τ(d)^2`:
any such pair has `a ∣ d` and `b ∣ d`. -/
theorem card_lcm_eq_le_sq {d : ℕ} (hd : 0 < d) (S T : Finset ℕ) :
    ((S.product T).filter (fun p => Nat.lcm p.1 p.2 = d)).card ≤ d.divisors.card ^ 2 := by
  have hsub : (S.product T).filter (fun p => Nat.lcm p.1 p.2 = d)
      ⊆ d.divisors.product d.divisors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpmem, hlcm⟩ := hp
    have h1 : p.1 ∈ d.divisors := by
      rw [Nat.mem_divisors]; exact ⟨hlcm ▸ Nat.dvd_lcm_left _ _, hd.ne'⟩
    have h2 : p.2 ∈ d.divisors := by
      rw [Nat.mem_divisors]; exact ⟨hlcm ▸ Nat.dvd_lcm_right _ _, hd.ne'⟩
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  calc ((S.product T).filter (fun p => Nat.lcm p.1 p.2 = d)).card
      ≤ (d.divisors.product d.divisors).card := Finset.card_le_card hsub
    _ = d.divisors.card * d.divisors.card := Finset.card_product _ _
    _ = d.divisors.card ^ 2 := by ring

/-- Shadow bound: `∑_{(a,b) ∈ S×T} r(lcm a b) ≤ ∑_e τ(e)^2 r(e)` for `r ≥ 0`
and `S, T` free of `0`. -/
theorem sum_lcm_shadow_le {r : ℕ → ℝ} (hr : ∀ e, 0 ≤ r e) (S T : Finset ℕ)
    (hS : ∀ a ∈ S, 0 < a) (hT : ∀ b ∈ T, 0 < b) :
    (∑ p ∈ S.product T, r (Nat.lcm p.1 p.2))
      ≤ ∑ e ∈ (S.product T).image (fun p => Nat.lcm p.1 p.2),
          ((e.divisors.card : ℝ)) ^ 2 * r e := by
  rw [← Finset.sum_fiberwise_of_maps_to'
      (s := S.product T) (t := (S.product T).image (fun p => Nat.lcm p.1 p.2))
      (g := fun p => Nat.lcm p.1 p.2) (f := r) (fun i hi => Finset.mem_image_of_mem _ hi)]
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨p₀, hp₀, hp₀e⟩ := Finset.mem_image.mp he
  have hp1 : 0 < p₀.1 := hS _ (Finset.mem_product.mp hp₀).1
  have hp2 : 0 < p₀.2 := hT _ (Finset.mem_product.mp hp₀).2
  have hd : 0 < e := by rw [← hp₀e]; exact Nat.lcm_pos hp1 hp2
  have hcard : (((S.product T).filter (fun p => Nat.lcm p.1 p.2 = e)).card : ℝ)
      ≤ (e.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast card_lcm_eq_le_sq hd S T
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard (hr e)

/-- `T₁(x;y) = ∑_{b ≤ y} μ(b) ∑_{b ∣ n ≤ x} aₙρₙ log n` (see (4.1)). -/
def T1 (a lam : ℕ → ℝ) (x y : ℝ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
    (ArithmeticFunction.moebius b : ℝ) * VbLog a lam b x

/-- `T₂(x;y) = −∑_{b ≤ y} μ(b) log b ∑_{b ∣ n ≤ x} aₙρₙ` (see (4.4)). -/
def T2 (a lam : ℕ → ℝ) (x y : ℝ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
    (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ) * Vb a lam b x

/-- For `0 ≤ y ≤ N` the integers `b ∈ [1,N]` with `b ≤ y` are exactly `[1,⌊y⌋]`. -/
lemma filter_Icc_eq_Icc_floor {N : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hfl : ⌊y⌋₊ ≤ N) :
    (Finset.Icc 1 N).filter (fun b => ((b : ℕ) : ℝ) ≤ y) = Finset.Icc 1 ⌊y⌋₊ := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, Nat.le_floor h3⟩
  · rintro ⟨h1, h2⟩
    have hb : ((b : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
    exact ⟨⟨h1, le_trans h2 hfl⟩, le_trans hb (Nat.floor_le hy0)⟩

/-- The `lcm` of two squarefree numbers is squarefree. -/
lemma lcm_squarefree {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  have ha' := Nat.squarefree_iff_prime_squarefree.mp ha
  have hb' := Nat.squarefree_iff_prime_squarefree.mp hb
  have ha0 : a ≠ 0 := fun h => ha' 2 Nat.prime_two (by rw [h]; exact dvd_zero _)
  have hb0 : b ≠ 0 := fun h => hb' 2 Nat.prime_two (by rw [h]; exact dvd_zero _)
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero ha0 hb0)]
  intro p
  rw [Nat.factorization_lcm ha0 hb0]
  exact max_le ((Nat.squarefree_iff_factorization_le_one ha0).mp ha p)
    ((Nat.squarefree_iff_factorization_le_one hb0).mp hb p)

/-- Squarefree reduction of a `μ`-weighted double sum: since `|μ b| = [b ♭]` and (under `hlam_sq`)
`|λ_ν| ≤ [ν ♭]`, the two coefficient factors may be traded for a restriction of both summation
indices to squarefree integers. -/
lemma sum_mu_lam_abs_le_sqfree {F : ℕ → ℕ → ℝ} (hF : ∀ b ν, 0 ≤ F b ν)
    {s t : Finset ℕ} {lam : ℕ → ℝ} (hlam_sq : ∀ ν, ¬ Squarefree ν → lam ν = 0)
    (hlam_le : ∀ ν, |lam ν| ≤ 1) :
    (∑ b ∈ s, |(ArithmeticFunction.moebius b : ℝ)| * ∑ ν ∈ t, |lam ν| * F b ν)
      ≤ ∑ b ∈ s.filter Squarefree, ∑ ν ∈ t.filter Squarefree, F b ν := by
  have h1 : ∀ b : ℕ,
      |(ArithmeticFunction.moebius b : ℝ)| ≤ (if Squarefree b then 1 else 0) := by
    intro b
    by_cases h : Squarefree b
    · rw [if_pos h]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    · rw [if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; norm_num
  have h2 : ∀ ν : ℕ, |lam ν| ≤ (if Squarefree ν then 1 else 0) := by
    intro ν
    by_cases h : Squarefree ν
    · rw [if_pos h]; exact hlam_le ν
    · rw [if_neg h, hlam_sq ν h]; norm_num
  have hstep : ∀ b : ℕ, (∑ ν ∈ t, (if Squarefree b ∧ Squarefree ν then F b ν else 0))
      = (if Squarefree b then (∑ ν ∈ t.filter Squarefree, F b ν) else 0) := by
    intro b
    by_cases hb : Squarefree b
    · rw [if_pos hb, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ν _
      by_cases hν : Squarefree ν <;> simp [hb, hν]
    · rw [if_neg hb]
      exact Finset.sum_eq_zero (fun ν _ => by simp [hb])
  calc (∑ b ∈ s, |(ArithmeticFunction.moebius b : ℝ)| * ∑ ν ∈ t, |lam ν| * F b ν)
      ≤ ∑ b ∈ s, ∑ ν ∈ t,
          ((if Squarefree b then 1 else 0) * ((if Squarefree ν then 1 else 0) * F b ν)) := by
        apply Finset.sum_le_sum
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro ν _
        have hb0 : (0 : ℝ) ≤ (if Squarefree b then 1 else 0) := by split <;> norm_num
        refine le_trans (mul_le_mul_of_nonneg_right (h1 b)
          (mul_nonneg (abs_nonneg _) (hF b ν))) ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (h2 ν) (hF b ν)) hb0
    _ = ∑ b ∈ s, ∑ ν ∈ t, (if Squarefree b ∧ Squarefree ν then F b ν else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro ν _
        by_cases hb : Squarefree b <;> by_cases hν : Squarefree ν <;> simp [hb, hν]
    _ = ∑ b ∈ s.filter Squarefree, ∑ ν ∈ t.filter Squarefree, F b ν := by
        rw [Finset.sum_congr rfl (fun b _ => hstep b)]
        exact (Finset.sum_filter (s := s) (p := Squarefree)
          (f := fun b => ∑ ν ∈ t.filter Squarefree, F b ν)).symm

/-- Shadow bound for the `lcm`-weighted remainder sums, in the squarefree form in which (R′) is
available: `∑_{ν ≤ Δ, ♭} ∑_{b ≤ M, ♭} |r(lcm ν b, m)| ≤ ∑_{e ≤ D, ♭} τ(e)⁵ |r(e,m)|` whenever
`Δ·M ≤ D`. -/
theorem sum_lcm_le_remainderSum {r : ℕ → ℕ → ℝ} {Δ M D : ℕ}
    (hDM : Δ * M ≤ D) (m : ℕ) :
    (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        ∑ b ∈ (Finset.Icc 1 M).filter Squarefree, |r (Nat.lcm ν b) m|)
      ≤ RemainderSum r D m := by
  set S := (Finset.Icc 1 Δ).filter Squarefree with hS
  set T := (Finset.Icc 1 M).filter Squarefree with hT
  have hSpos : ∀ a ∈ S, 0 < a := fun a ha =>
    (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  have hTpos : ∀ b ∈ T, 0 < b := fun b hb =>
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  have hprod : (∑ ν ∈ S, ∑ b ∈ T, |r (Nat.lcm ν b) m|)
      = ∑ p ∈ S.product T, |r (Nat.lcm p.1 p.2) m| :=
    (Finset.sum_product S T (fun p : ℕ × ℕ => |r (Nat.lcm p.1 p.2) m|)).symm
  rw [hprod]
  refine le_trans (sum_lcm_shadow_le (r := fun e => |r e m|) (fun e => abs_nonneg _) S T hSpos hTpos) ?_
  have hsub : (S.product T).image (fun p => Nat.lcm p.1 p.2) ⊆ (Finset.Icc 1 D).filter Squarefree := by
    intro e he
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp he
    rw [← hpe, Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have h1 : 1 ≤ p.1 := hSpos p.1 hp1
    have h2 : 1 ≤ p.2 := hTpos p.2 hp2
    have h3 : p.1 ≤ Δ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
    have h4 : p.2 ≤ M := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp2).1).2
    refine ⟨⟨le_trans h1 (Nat.le_lcm_left p.1 (by omega)), le_trans ?_ hDM⟩,
      lcm_squarefree (Finset.mem_filter.mp hp1).2 (Finset.mem_filter.mp hp2).2⟩
    have hdvd : Nat.lcm p.1 p.2 ∣ p.1 * p.2 := Nat.lcm_dvd_mul p.1 p.2
    calc Nat.lcm p.1 p.2 ≤ p.1 * p.2 := Nat.le_of_dvd (by positivity) hdvd
      _ ≤ Δ * M := Nat.mul_le_mul h3 h4
  have hstep1 : (∑ e ∈ (S.product T).image (fun p => Nat.lcm p.1 p.2),
        ((e.divisors.card : ℝ)) ^ 2 * |r e m|)
      ≤ ∑ e ∈ (S.product T).image (fun p => Nat.lcm p.1 p.2),
        ((e.divisors.card : ℝ)) ^ 5 * |r e m| := by
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp he
    have he1 : 1 ≤ e := by
      rw [← hpe]
      exact Nat.lcm_pos (hSpos p.1 (Finset.mem_product.mp hp).1)
        (hTpos p.2 (Finset.mem_product.mp hp).2)
    have h1 : (1 : ℝ) ≤ ((e.divisors.card : ℕ) : ℝ) := by
      have hpos : 0 < e.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd e, by omega⟩⟩
      exact_mod_cast hpos
    have h25 : ((e.divisors.card : ℝ)) ^ 2 ≤ ((e.divisors.card : ℝ)) ^ 5 := by
      calc ((e.divisors.card : ℝ)) ^ 2 = ((e.divisors.card : ℝ)) ^ 2 * 1 := by ring
        _ ≤ ((e.divisors.card : ℝ)) ^ 2 * ((e.divisors.card : ℝ)) ^ 3 :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ h1) (by positivity)
        _ = ((e.divisors.card : ℝ)) ^ 5 := by ring
    exact mul_le_mul_of_nonneg_right h25 (abs_nonneg _)
  have hstep2 : (∑ e ∈ (S.product T).image (fun p => Nat.lcm p.1 p.2),
        ((e.divisors.card : ℝ)) ^ 5 * |r e m|)
      ≤ RemainderSum r D m := by
    rw [RemainderSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e _ _ => mul_nonneg (by positivity) (abs_nonneg _))
  exact le_trans hstep1 hstep2

end

end Submission.ASP
