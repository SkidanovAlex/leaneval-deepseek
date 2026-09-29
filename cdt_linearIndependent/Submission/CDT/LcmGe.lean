import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq
import Submission.Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq_ge
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_band_sub_id_isLittleO

/-!
# The prime-cutoff window product `L^{≥ l}_{n,k}` and the analytic step of Lemma `lcm-2`

For `0 ≤ l ≤ n` and `k ≤ n`, let `L^{≥ l}_{n,k}` be the product of the primes `p` with `l < p ≤ n`
that have a multiple in the window `(n - k, …, n)` (the integer `0` being excluded from the window,
as in `Commons.NumberTheory.Chebyshev.log_lcm_window_erase_zero_sub_theta_sub_bad_le`).

The paper (Lemma `lcm-2`) computes the size of `log L^{≥ l}_{n,k}`: for
`0 < γ₀ ≤ k/n, l/n ≤ γ₀' ≤ 1` it is asymptotic, uniformly in `k, l`, to the model
`k·(Σ_{h ≤ (n-k)/max(k,l)} 1/h) + (n/⌊(n + (l-k)⁺)/max(k,l)⌋ − l)⁺ + o(n)`.

The exact combinatorial decomposition is

  `log L^{≥ l}_{n,k} = θ(n) − θ(l) − Σ_{a ≤ h} (θ((n-k-1)/a) − θ(max(n/(a+1), l)))`,
  `h = (n-k-1)/max(k,l)`,

which is the prime-cutoff refinement of the identity proved for `l = 0` in
`Commons.NumberTheory.Chebyshev.log_lcm_window_erase_zero_sub_theta_sub_bad_le`
(the cutoff version of the sum over "bad" primes is
`Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq_ge`).

This module isolates the *analytic* step (the prime number theorem, uniformly in `k, l`):
replacing every `θ(y)` by `y` in the last sum costs `o(n)`, uniformly in `k, l`.  The point is that
the number `h` of terms is `≤ 1/γ₀` while each argument of `θ` is `≥ γ₀n`, so the estimate
`θ(y) = y + o(y)` applies uniformly.

Main result: **`bad_sum_model_error`**.
-/

namespace Submission.CDT.LcmGe

open Finset
open scoped BigOperators Topology

/-- `L^{≥ l}_{n,k}`: the product of the primes `p` with `l < p ≤ n` having a multiple in the
window `[n-k, n]` (with `0` removed from the window). -/
def Lge (l n k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 1 n).filter
    (fun p => p.Prime ∧ l < p ∧ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)), p

/-- `Lge` is the product of its defining primes, cast to `ℝ`. -/
theorem Lge_cast (l n k : ℕ) :
    ((Lge l n k : ℕ) : ℝ)
      = ∏ p ∈ (Finset.Icc 1 n).filter
          (fun p => p.Prime ∧ l < p ∧ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)),
          (p : ℝ) := by
  rw [Lge]; push_cast; rfl

/-- **The analytic step of Lemma `lcm-2`.**  For `γ > 0` and every `ε > 0`, for all sufficiently
large `n` and all `k, l` with `γn ≤ k ≤ n` and `γn ≤ l ≤ n`, the prime-number-theorem error in the
cutoff decomposition is at most `εn`:

`|Σ_{a ≤ h} (θ((n-k-1)/a) − θ(max(n/(a+1), l))) − Σ_{a ≤ h} ((n-k-1)/a − max(n/(a+1), l))| ≤ εn`
with `h = (n-k-1)/max(k,l)`. -/
theorem bad_sum_model_error (γ : ℝ) (hγ : 0 < γ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ k l : ℕ, γ * (n : ℝ) ≤ (k : ℝ) → k ≤ n → γ * (n : ℝ) ≤ (l : ℝ) → l ≤ n →
      |(∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
        - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ)) - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))| 
        ≤ ε * (n : ℝ) := by
  intro ε hε
  set δ : ℝ := ε * γ / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  -- the PNT estimate, uniformly
  have hθ : (fun y : ℝ => Chebyshev.theta y - y) =o[Filter.atTop] (fun y : ℝ => y) :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO
  have hb : ∀ᶠ y : ℝ in Filter.atTop, |Chebyshev.theta y - y| ≤ δ * y := by
    have h := hθ.bound hδpos
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with y hy hy0
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy0] at hy
  rw [Filter.eventually_atTop] at hb
  obtain ⟨Y, hY⟩ := hb
  -- the threshold on `n`
  have hγn : ∀ᶠ n : ℕ in Filter.atTop, max Y 1 ≤ γ * (n : ℝ) := by
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have hlim : Filter.Tendsto (fun n : ℕ => γ * (n : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hγ hcast
    exact hlim.eventually (Filter.eventually_ge_atTop (max Y 1))
  filter_upwards [hγn] with n hn k l hk hkn hl hln
  set h : ℕ := (n - k - 1) / max k l with hhdef
  have hγn' : γ * (n : ℝ) ≤ (max k l : ℝ) := by
    have hmax := max_le_max hk hl
    rwa [max_self] at hmax
  have hn1 : (1 : ℝ) ≤ γ * (n : ℝ) := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by nlinarith [hγ, hn1]
  have hYle : Y ≤ γ * (n : ℝ) := le_trans (le_max_left _ _) hn
  -- every argument is `≥ γn`
  have harg1 : ∀ a ∈ Finset.Icc 1 h,
      γ * (n : ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) / (a : ℝ) := by
    intro a ha
    obtain ⟨ha1, hah⟩ := Finset.mem_Icc.mp ha
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
    rw [le_div_iff₀ hapos]
    have hstep : a * max k l ≤ n - k - 1 :=
      le_trans (Nat.mul_le_mul_right _ hah) (Nat.div_mul_le_self _ _)
    have hstep' : ((a * max k l : ℕ) : ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) := by exact_mod_cast hstep
    have hle : γ * (n : ℝ) * (a : ℝ) ≤ (a : ℝ) * (max k l : ℝ) := by
      have := mul_le_mul_of_nonneg_left hγn' (by positivity : (0 : ℝ) ≤ (a : ℝ))
      linarith
    push_cast at hstep'
    linarith
  have harg2 : ∀ a ∈ Finset.Icc 1 h,
      γ * (n : ℝ) ≤ max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ) :=
    fun a _ => le_trans hl (le_max_right _ _)
  -- the two auxiliary sums are `≤ h·n`
  have hyle : ∀ a ∈ Finset.Icc 1 h, ((n - k - 1 : ℕ) : ℝ) / (a : ℝ) ≤ (n : ℝ) := by
    intro a ha
    obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp ha
    have ha1' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have hn0 : (0 : ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) := by positivity
    have hnkc : ((n - k - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : n - k - 1 ≤ n := by omega
      exact_mod_cast this
    exact le_trans (div_le_self hn0 ha1') hnkc
  have hzle : ∀ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ) ≤ (n : ℝ) := by
    intro a _
    refine max_le ?_ (by exact_mod_cast hln)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) + 1)]
    nlinarith [hnpos]
  have hcard : ((Finset.Icc 1 h).card : ℝ) = (h : ℝ) := by
    rw [Nat.card_Icc]; simp
  -- `h ≤ 1/γ`
  have hhle : (h : ℝ) ≤ 1 / γ := by
    have hmul : (h : ℝ) * (max k l : ℝ) ≤ (n : ℝ) := by
      have h1 : h * max k l ≤ n := le_trans (Nat.div_mul_le_self _ _) (by omega)
      have h2 : ((h * max k l : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    have h3 : (h : ℝ) * (γ * (n : ℝ)) ≤ (h : ℝ) * (max k l : ℝ) :=
      mul_le_mul_of_nonneg_left hγn' (by positivity : (0 : ℝ) ≤ (h : ℝ))
    rw [le_div_iff₀ hγ]
    nlinarith [hmul, h3, hnpos, hγ]
  -- assemble
  rw [← Finset.sum_sub_distrib]
  calc |∑ a ∈ Finset.Icc 1 h,
        ((Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))
          - ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ)) - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))|
      ≤ ∑ a ∈ Finset.Icc 1 h,
          |(Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
              - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))
            - ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ)) - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 h,
          (δ * (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            + δ * max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)) := by
        apply Finset.sum_le_sum
        intro a ha
        set y : ℝ := ((n - k - 1 : ℕ) : ℝ) / (a : ℝ) with hydef
        set z : ℝ := max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ) with hzdef
        have h1 : |Chebyshev.theta y - y| ≤ δ * y := hY y (le_trans hYle (harg1 a ha))
        have h2 : |Chebyshev.theta z - z| ≤ δ * z := hY z (le_trans hYle (harg2 a ha))
        have h3 : |(Chebyshev.theta y - Chebyshev.theta z) - (y - z)|
            = |(Chebyshev.theta y - y) - (Chebyshev.theta z - z)| := by
          congr 1; ring
        rw [h3]
        have h4 := abs_sub (Chebyshev.theta y - y) (Chebyshev.theta z - z)
        simp only [hydef, hzdef] at h1 h2 h4 ⊢
        linarith
    _ = δ * (∑ a ∈ Finset.Icc 1 h, (((n - k - 1 : ℕ) : ℝ) / (a : ℝ)))
          + δ * (∑ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ δ * ((h : ℝ) * (n : ℝ)) + δ * ((h : ℝ) * (n : ℝ)) := by
        have hy : (∑ a ∈ Finset.Icc 1 h, (((n - k - 1 : ℕ) : ℝ) / (a : ℝ)))
            ≤ (h : ℝ) * (n : ℝ) := by
          calc (∑ a ∈ Finset.Icc 1 h, (((n - k - 1 : ℕ) : ℝ) / (a : ℝ)))
              ≤ ∑ _a ∈ Finset.Icc 1 h, (n : ℝ) := Finset.sum_le_sum hyle
            _ = ((Finset.Icc 1 h).card : ℝ) * (n : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ = (h : ℝ) * (n : ℝ) := by rw [hcard]
        have hz : (∑ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))
            ≤ (h : ℝ) * (n : ℝ) := by
          calc (∑ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))
              ≤ ∑ _a ∈ Finset.Icc 1 h, (n : ℝ) := Finset.sum_le_sum hzle
            _ = ((Finset.Icc 1 h).card : ℝ) * (n : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ = (h : ℝ) * (n : ℝ) := by rw [hcard]
        nlinarith [hy, hz, hδpos]
    _ ≤ ε * (n : ℝ) := by
        have hstep : 2 * δ * (h : ℝ) ≤ ε := by
          have hγinv : γ * (1 / γ) = 1 := by field_simp
          have hkey : γ * (h : ℝ) ≤ 1 := by
            have := mul_le_mul_of_nonneg_left hhle hγ.le
            rwa [hγinv] at this
          have hrew : 2 * (ε * γ / 2) * (h : ℝ) = ε * (γ * (h : ℝ)) := by ring
          rw [hδdef, hrew]
          nlinarith [hkey, hε]
        have := mul_le_mul_of_nonneg_right hstep hnpos.le
        linarith [this]

/-! ## The exact decomposition and the model form of Lemma `lcm-2` -/

/-- `θ(b)` as a sum over `range (b+1)`. -/
theorem theta_nat_eq_sum_range (b : ℕ) :
    Chebyshev.theta (b : ℝ)
      = ∑ p ∈ Finset.range (b + 1), (if p.Prime then Real.log (p : ℝ) else 0) := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter]
  apply Finset.sum_congr
  · ext y; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  · intro y _; rfl

/-- `θ(n) − θ(l)` is the sum of `log p` over the primes `l < p ≤ n`. -/
theorem theta_sub_theta_eq (l n : ℕ) (hln : l ≤ n) :
    Chebyshev.theta (n : ℝ) - Chebyshev.theta (l : ℝ)
      = ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p), Real.log (p : ℝ) := by
  rw [theta_nat_eq_sum_range n, theta_nat_eq_sum_range l,
    ← Finset.sum_Ico_eq_sub (f := fun p => if p.Prime then Real.log (p : ℝ) else 0)
      (m := l + 1) (n := n + 1) (by omega)]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext y
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp, by omega⟩
  · rintro ⟨⟨h1, h2⟩, hp, h3⟩
    exact ⟨⟨by omega, by omega⟩, hp⟩

/-- **The exact decomposition of `log L^{≥ l}_{n,k}`**: the logarithm of the cutoff window product
is `θ(n) − θ(l)` minus the sum of `log p` over the "bad" primes `l < p ≤ n` that have no multiple in
the window; and the bad primes are exactly the primes in the gaps (Lemma `sum_log_primes_bad_eq_ge`
of the commons). -/
theorem log_Lge (l n k : ℕ) (hM : 0 < max k l) (hkn : k ≤ n) (hln : l ≤ n) :
    Real.log ((Lge l n k : ℕ) : ℝ)
      = Chebyshev.theta (n : ℝ) - Chebyshev.theta (l : ℝ)
        - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))) := by
  have hlog : Real.log (∏ p ∈ (Finset.Icc 1 n).filter
      (fun p => p.Prime ∧ l < p ∧ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)), (p : ℝ))
      = ∑ p ∈ (Finset.Icc 1 n).filter
          (fun p => p.Prime ∧ l < p ∧ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)),
          Real.log (p : ℝ) := by
    refine Real.log_prod (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    exact_mod_cast hp.2.1.pos.ne'
  have hsplit : (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p), Real.log (p : ℝ))
      = (∑ p ∈ (Finset.Icc 1 n).filter
            (fun p => p.Prime ∧ l < p ∧ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)),
            Real.log (p : ℝ))
        + (∑ p ∈ (Finset.Icc 1 n).filter
            (fun p => p.Prime ∧ l < p ∧ ¬ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)),
            Real.log (p : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p))
      (p := fun p => ∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)
      (f := fun p => Real.log (p : ℝ))]
    rw [Finset.filter_filter, Finset.filter_filter]
    congr 1
    · apply Finset.sum_congr
      · ext p; simp only [Finset.mem_filter]; tauto
      · intro p _; rfl
    · apply Finset.sum_congr
      · ext p; simp only [Finset.mem_filter]; tauto
      · intro p _; rfl
  rw [Lge_cast, hlog, theta_sub_theta_eq l n hln, hsplit,
    ← Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq_ge n k l hM hkn]
  ring

/-- **The model form of Lemma `lcm-2` (part 1).**  For `0 < γ ≤ 1` and every `ε > 0`, for all
sufficiently large `n` and all `k, l` with `γn ≤ k ≤ n` and `γn ≤ l ≤ n`,

`|log L^{≥ l}_{n,k} − (n − l − Σ_{a ≤ h} ((n-k-1)/a − max(n/(a+1), l)))| ≤ εn`,
`h = (n-k-1)/max(k,l)`.

(The remaining, purely algebraic, step is to evaluate the model sum in closed form; the paper's
displayed value `k·Σ_{h ≤ (n-k)/max(k,l)} 1/h + (n/⌊(n+(l-k)⁺)/max(k,l)⌋ − l)⁺` agrees with it up
to `O(log n)`, hence also `o(n)`.) -/
theorem lcm_ge_model (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ k l : ℕ, γ * (n : ℝ) ≤ (k : ℝ) → k ≤ n → γ * (n : ℝ) ≤ (l : ℝ) → l ≤ n →
      |Real.log ((Lge l n k : ℕ) : ℝ)
        - ((n : ℝ) - (l : ℝ)
            - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
              ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
                - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))|
        ≤ ε * (n : ℝ) := by
  intro ε hε
  set δ : ℝ := ε / 6 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hε3 : 0 < ε / 3 := by linarith
  have hθ : (fun y : ℝ => Chebyshev.theta y - y) =o[Filter.atTop] (fun y : ℝ => y) :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO
  have hb : ∀ᶠ y : ℝ in Filter.atTop, |Chebyshev.theta y - y| ≤ δ * y := by
    have h := hθ.bound hδpos
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with y hy hy0
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy0] at hy
  rw [Filter.eventually_atTop] at hb
  obtain ⟨Y, hY⟩ := hb
  have hγn : ∀ᶠ n : ℕ in Filter.atTop, max (max Y 1) 1 ≤ γ * (n : ℝ) := by
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have hlim : Filter.Tendsto (fun n : ℕ => γ * (n : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hγ hcast
    exact hlim.eventually (Filter.eventually_ge_atTop (max (max Y 1) 1))
  filter_upwards [hγn, bad_sum_model_error γ hγ (ε / 3) hε3] with n hn hmodel k l hk hkn hl hln
  have hn1 : (1 : ℝ) ≤ γ * (n : ℝ) := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by nlinarith [hγ, hn1]
  have hYle : Y ≤ γ * (n : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := le_trans hn1 hl
  have hlpos : (0 : ℕ) < l := by exact_mod_cast (show (0 : ℝ) < (l : ℝ) by linarith)
  have hM : 0 < max k l := lt_of_lt_of_le hlpos (le_max_right _ _)
  have hlog := log_Lge l n k hM hkn hln
  have hγnn : γ * (n : ℝ) ≤ (n : ℝ) := by nlinarith [hnpos, hγ1]
  have hA : |Chebyshev.theta (n : ℝ) - (n : ℝ)| ≤ δ * (n : ℝ) := hY n (le_trans hYle hγnn)
  have hB : |Chebyshev.theta (l : ℝ) - (l : ℝ)| ≤ δ * (l : ℝ) := hY l (le_trans hYle hl)
  have hC := hmodel k l hk hkn hl hln
  have hEq : Chebyshev.theta (n : ℝ) - Chebyshev.theta (l : ℝ)
      - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
      - ((n : ℝ) - (l : ℝ)
          - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
              - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
      = (Chebyshev.theta (n : ℝ) - (n : ℝ)) - (Chebyshev.theta (l : ℝ) - (l : ℝ))
        - ((∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
              - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
          - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
              - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))) := by ring
  rw [hlog, hEq]
  have h5 := abs_sub ((Chebyshev.theta (n : ℝ) - (n : ℝ)) - (Chebyshev.theta (l : ℝ) - (l : ℝ)))
    ((∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
        (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
          - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
      - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
        ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
          - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
  have h6 := abs_sub (Chebyshev.theta (n : ℝ) - (n : ℝ)) (Chebyshev.theta (l : ℝ) - (l : ℝ))
  have hfin : δ * (n : ℝ) + δ * (l : ℝ) + (ε / 3) * (n : ℝ) ≤ ε * (n : ℝ) := by
    have hln' : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
    rw [hδdef]
    nlinarith [hε, hnpos, hln']
  linarith [h5, h6, hA, hB, hC, hfin]

/-! ## The closed form of the model sum: an evaluation via harmonic sums -/

/-- The telescoping identity for the shifted harmonic sums. -/
theorem sum_Icc_one_div_add_one (h : ℕ) :
    (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / ((a : ℝ) + 1))
      = (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ)) - 1 + 1 / ((h : ℝ) + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ h + 1), ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ h + 1)]
    have h1 : ((h + 1 : ℕ) : ℝ) = (h : ℝ) + 1 := by push_cast; ring
    rw [h1]
    have h2 : ((h : ℝ) + 1) ≠ 0 := by positivity
    have h3 : ((h : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

/-- The pointwise identity behind the closed form: `max(x, y) = x + max(y - x, 0)`. -/
theorem max_eq_self_add_max_sub (x y : ℝ) : max x y = x + max (y - x) 0 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ y - x)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith : y - x ≤ 0), add_zero]

/-- **The closed form of the model of Lemma `lcm-2` (part 1).**  With
`h = (n-k-1)/max(k,l)`, `H = Σ_{a ≤ h} 1/a` and `C = Σ_{a ≤ h} max(l - n/(a+1), 0)`,

`log L^{≥l}_{n,k} = (k+1)·H + n/(h+1) - l + C + o(n)`,

uniformly in `k, l` with `γn ≤ k ≤ n`, `γn ≤ l ≤ n` (`0 < γ ≤ 1`).  (The paper's displayed value
`k·Σ_{h ≤ (n-k)/max(k,l)} 1/h + (n/⌊(n+(l-k)⁺)/max(k,l)⌋ - l)⁺` agrees with `(k+1)H + n/(h+1) - l + C`
up to `O(log n)`, since `C` is a sum of at most two nonzero terms.) -/
theorem lcm_ge_harmonic (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ k l : ℕ, γ * (n : ℝ) ≤ (k : ℝ) → k ≤ n → γ * (n : ℝ) ≤ (l : ℝ) → l ≤ n →
      |Real.log ((Lge l n k : ℕ) : ℝ)
        - (((k : ℝ) + 1) * (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l), (1 : ℝ) / (a : ℝ))
            + (n : ℝ) / ((((n - k - 1) / max k l : ℕ) : ℝ) + 1) - (l : ℝ)
            + (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
                max ((l : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0))| 
        ≤ ε * (n : ℝ) := by
  intro ε hε
  filter_upwards [lcm_ge_model γ hγ hγ1 ε hε] with n hn k l hk hkn hl hln
  have hmodel := hn k l hk hkn hl hln
  set h : ℕ := (n - k - 1) / max k l with hhdef
  have hmax : ∀ a : ℕ, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)
      = (n : ℝ) / ((a : ℝ) + 1) + max ((l : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0 :=
    fun a => max_eq_self_add_max_sub _ _
  have hsum : (∑ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))
      = (n : ℝ) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ))
        - (n : ℝ) + (n : ℝ) / ((h : ℝ) + 1)
        + (∑ a ∈ Finset.Icc 1 h, max ((l : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0) := by
    rw [Finset.sum_congr rfl (fun a _ => hmax a), Finset.sum_add_distrib]
    have hsplit : (∑ a ∈ Finset.Icc 1 h, (n : ℝ) / ((a : ℝ) + 1))
        = (n : ℝ) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / ((a : ℝ) + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [hsplit, sum_Icc_one_div_add_one]
    ring
  have hysum : (∑ a ∈ Finset.Icc 1 h, (((n - k - 1 : ℕ) : ℝ) / (a : ℝ)))
      = ((n - k - 1 : ℕ) : ℝ) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hW : ((n : ℝ) - ((n - k - 1 : ℕ) : ℝ)) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ))
      = ((k : ℝ) + 1) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ)) := by
    by_cases hk' : k + 1 ≤ n
    · have hcast : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n - k), Nat.cast_sub hkn]
        push_cast
        ring
      rw [hcast]; ring
    · have hkn' : k = n := by omega
      have hh0 : h = 0 := by rw [hhdef]; simp [hkn']
      rw [hh0]; simp
  have hkey : (n : ℝ) - (l : ℝ)
      - (∑ a ∈ Finset.Icc 1 h,
          ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ)) - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))
      = ((k : ℝ) + 1) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ))
        + (n : ℝ) / ((h : ℝ) + 1) - (l : ℝ)
        + (∑ a ∈ Finset.Icc 1 h, max ((l : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0) := by
    rw [Finset.sum_sub_distrib, hysum, hsum]
    nlinarith [hW]
  rw [hkey] at hmodel
  exact hmodel


end Submission.CDT.LcmGe
