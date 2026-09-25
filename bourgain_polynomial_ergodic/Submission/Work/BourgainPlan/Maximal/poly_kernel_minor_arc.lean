import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.minor_arc_decay_pre

namespace Work.BourgainPlan.Maximal

open Polynomial

/-! ## Reducing the `(a, q, l)`-form minor-arc hypothesis to the Weyl form

`weyl_minor_arc_decay` requires the leading coefficient `c·θ` to be far from every rational `a/q`
with `q ≤ N^{1/4}` (`q` and `a` integers, no coprimality or size restriction on `a`), while the
circle-method hypothesis of `poly_kernel_minor_arc` only excludes the arc centres `a/q + l` with
`1 ≤ q ≤ ⌊N^{1/4}⌋`, `0 ≤ a < q`, `gcd a q = 1` and `l ∈ [-1, c]`.  The reduction is the standard
one: write an arbitrary `a/q` as `m + r/q` with `0 ≤ r < q`, cancel the common divisor of `r` and
`q`, and appeal to the hypothesis; the integer part `m` lies in `[-1, c]` exactly when the
corresponding arc is one of the excluded ones, and otherwise the distance `|cθ - a/q| ≥ 1` is
already bigger than the threshold `N^{-(d-1/4)} < 1` (here `0 ≤ θ ≤ 1` confines
`cθ - r/q ∈ (-1, c]`). -/

/-- Reduction of the `(a, l)`-form minor-arc hypothesis (`a < q`, `gcd a q = 1`,
`l ∈ [-1, c]`) to the `ℤ`-denominator form required by `weyl_minor_arc_decay`. -/
lemma poly_minor_arc_reduce (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {N : ℕ} (hN : 3 ≤ N) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hnoarc : ∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) →
      a < q → Nat.gcd a q = 1 → l ∈ Finset.Icc (-1) P.leadingCoeff →
      (N : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ) / 4)) <
        |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|) :
    ∀ (q : ℕ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) →
      (N : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ) / 4)) <
        |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)| := by
  intro q a hq hqle
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hqpos : 0 < q := by omega
  have hqZne : ((q : ℤ)) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hqZpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqpos
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hcR : (0 : ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  -- Euclidean division of `a` by `q`
  set r : ℤ := a % (q : ℤ) with hr
  have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg a hqZne
  have hrlt : r < (q : ℤ) := hr ▸ Int.emod_lt_of_pos a hqZpos
  set m : ℤ := a / (q : ℤ) with hm
  have hdecZ : a = (q : ℤ) * m + r := by
    have h := Int.mul_ediv_add_emod a (q : ℤ)
    rw [← hm, ← hr] at h
    exact h.symm
  set rn : ℕ := r.toNat with hrn
  have hrcast : (rn : ℤ) = r := hrn ▸ Int.toNat_of_nonneg hr0
  have hrnlt : rn < q := by
    have h : ((rn : ℤ)) < (q : ℤ) := by rw [hrcast]; exact hrlt
    exact_mod_cast h
  -- cancel the common divisor of `rn` and `q`
  set D : ℕ := Nat.gcd rn q with hD
  have hDq : D ∣ q := hD ▸ Nat.gcd_dvd_right rn q
  have hDr : D ∣ rn := hD ▸ Nat.gcd_dvd_left rn q
  have hDpos : 0 < D := Nat.pos_of_dvd_of_pos hDq hqpos
  set q₁ : ℕ := q / D with hq1
  set r₁ : ℕ := rn / D with hr1
  have hq1D : q₁ * D = q := hq1 ▸ Nat.div_mul_cancel hDq
  have hr1D : r₁ * D = rn := hr1 ▸ Nat.div_mul_cancel hDr
  have hcop : Nat.gcd r₁ q₁ = 1 := by
    have h := Nat.coprime_div_gcd_div_gcd (m := rn) (n := q) (by rw [← hD]; exact hDpos)
    rw [hq1, hr1]
    exact Nat.coprime_iff_gcd_eq_one.mp h
  have hr1lt : r₁ < q₁ := by
    have h := Nat.div_lt_div_of_lt_of_dvd hDq hrnlt
    rw [hq1, hr1]; exact h
  have hq1le : q₁ ≤ q := hq1 ▸ Nat.div_le_self q D
  have hq1leN : q₁ ≤ Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) := by
    refine Nat.le_floor ?_
    have h1 : (q₁ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1le
    linarith
  have hfr : (r₁ : ℝ) / (q₁ : ℝ) = (rn : ℝ) / (q : ℝ) := by
    have h1 : (rn : ℝ) = (r₁ : ℝ) * (D : ℝ) := by rw [← hr1D]; push_cast; ring
    have h2 : (q : ℝ) = (q₁ : ℝ) * (D : ℝ) := by rw [← hq1D]; push_cast; ring
    rw [h1, h2]
    have hDne : (D : ℝ) ≠ 0 := by positivity
    field_simp
  have haq : (a : ℝ) / (q : ℝ) = (m : ℝ) + (r₁ : ℝ) / (q₁ : ℝ) := by
    have h1 : (a : ℝ) = (q : ℝ) * (m : ℝ) + (rn : ℝ) := by
      have hZ : a = (q : ℤ) * m + ((rn : ℤ)) := by rw [hrcast]; exact hdecZ
      exact_mod_cast hZ
    rw [h1, add_div, mul_div_cancel_left₀ _ (ne_of_gt hqRpos), hfr]
  have hq1pos : 1 ≤ q₁ := by
    rcases Nat.eq_zero_or_pos q₁ with h0 | hp
    · rw [h0, zero_mul] at hq1D; omega
    · exact hp
  have hq1Rpos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast (by omega : 0 < q₁)
  have habs : |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)|
      = |(P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) - (m : ℝ)| := by
    rw [haq]; congr 1; ring
  by_cases hml : m ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff
  · -- the arc is one of the excluded ones: apply the hypothesis
    rw [habs]
    exact hnoarc q₁ r₁ m hq1pos hq1leN hr1lt hcop hml
  · -- otherwise `|cθ - a/q| ≥ 1 > N^{-(d-1/4)}`
    have hml' : m < -1 ∨ P.leadingCoeff < m := by
      by_contra hcon
      rw [not_or] at hcon
      exact hml (Finset.mem_Icc.mpr
        ⟨le_of_not_gt hcon.1, le_of_not_gt hcon.2⟩)
    have hsmall : (N : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ) / 4)) < 1 := by
      have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      have hexp : (0 : ℝ) < (P.natDegree : ℝ) - (1 : ℝ) / 4 := by linarith
      have h1 : (1 : ℝ) < (N : ℝ) ^ ((P.natDegree : ℝ) - (1 : ℝ) / 4) := by
        have h2 := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1)
          (by exact_mod_cast (by omega : 1 < N) : (1 : ℝ) < (N : ℝ)) hexp
        rwa [Real.one_rpow] at h2
      rw [Real.rpow_neg hNr.le]
      exact inv_lt_one_of_one_lt₀ h1
    have hge1 : (1 : ℝ) ≤
        |(P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) - (m : ℝ)| := by
      have hr1q1lt : (r₁ : ℝ) / (q₁ : ℝ) < 1 := by
        rw [div_lt_one hq1Rpos]; exact_mod_cast hr1lt
      have hr1q1nn : (0 : ℝ) ≤ (r₁ : ℝ) / (q₁ : ℝ) := by positivity
      have hcθnn : (0 : ℝ) ≤ (P.leadingCoeff : ℝ) * θ := mul_nonneg hcR.le hθ0
      have hcθle : (P.leadingCoeff : ℝ) * θ ≤ (P.leadingCoeff : ℝ) := by nlinarith [hcR, hθ1]
      rcases hml' with hlt | hgt
      · have hm2 : (m : ℝ) ≤ -2 := by
          have h : m ≤ (-2 : ℤ) := by omega
          exact_mod_cast h
        have hβgt : (-1 : ℝ) < (P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) := by linarith
        have hpos : (0 : ℝ) <
            (P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) - (m : ℝ) := by linarith
        rw [abs_of_pos hpos]; linarith
      · have hmge : (P.leadingCoeff : ℝ) + 1 ≤ (m : ℝ) := by
          have h : P.leadingCoeff + 1 ≤ m := by omega
          exact_mod_cast h
        have hβle : (P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) - (m : ℝ) ≤ -1 := by linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
    rw [habs]
    linarith

/-- **Minor-arc decay of the polynomial Weyl kernel (non-monic form).**  For an integer polynomial
`P` of degree `d ≥ 2` with `c = P.leadingCoeff > 0`: if the `c`-scaled frequency `c·θ` is at
distance `> N^{-(d−1/4)}` from every arc centre `a/q + l` with `1 ≤ q ≤ ⌊N^{1/4}⌋`, `a < q`,
`gcd a q = 1`, `l ∈ [-1, c]`, then the Weyl kernel decays like a power of `N`:
`‖N⁻¹ ∑_{n<N} e(θ P n)‖ ≤ C N^{-ν}`.

Proof route: this is `Commons.Analysis.ExponentialSums.weyl_minor_arc_decay` applied to the real
polynomial `θ • toRealPoly P`, exactly as
`Commons.Analysis.ExponentialSums.pow_kernel_minor_arc_bound` does it for `P = X^d` (see
Submission/Commons/Analysis/ExponentialSums/pure_power_kernel_maximal_l2.lean, theorem
`pow_kernel_minor_arc_bound`, whose proof body can be adapted almost verbatim: it performs the
`a % q` reduction and the `gcd` division to turn a hypothesis restricted to `a < q`,
`gcd a q = 1` into the hypothesis of `weyl_minor_arc_decay` over all `a : ℤ`).  The new wrinkle is
that `l` is restricted to `Icc (-1) P.leadingCoeff`; the case `m ∉ Icc (-1) P.leadingCoeff` is
handled by the size bound `|cθ − a/q| ≥ 1` (using `0 ≤ θ ≤ 1` so that `cθ − r₁/q₁ ∈ (-1, c]`). -/
theorem poly_kernel_minor_arc (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧ ∀ (N : ℕ), 3 ≤ N → ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
      (∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N:ℝ)^((1:ℝ)/4)) → a < q →
        Nat.gcd a q = 1 → l ∈ Finset.Icc (-1) P.leadingCoeff →
        (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)) < |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|) →
      ‖Work.BourgainPlan.Maximal.polyWeylKernel P N θ‖ ≤ C * (N:ℝ)^(-ν) := by
  obtain ⟨ν, C, hν, hC, hmain⟩ := minor_arc_decay_pre P hc hd
  exact ⟨ν, C, hν, hC, fun N hN θ hθ0 hθ1 hnoarc =>
    hmain N θ hN hθ0 hθ1 (poly_minor_arc_reduce P hc hd hN hθ0 hθ1 hnoarc)⟩

end Work.BourgainPlan.Maximal
