-- Redirected copy of `Submission.Work.DSM2p.approx_lem` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALvaln
import Submission.Work.DSM2p.AALcopy_approx_defs
import Submission.Work.DSM2p.AALcopy_witt_step_rec
import Submission.Work.DSM2p.AALcopy_iterate_tail_bound

/-!
# `Work.DSM2p.approx_lem` — the Česnavičius–Scholze approximation lemma

The statement (frozen) is Česnavičius–Scholze, *Purity for flat cohomology*, `approx-lem`:
for a perfectoid ring `R` with pseudo-uniformizer `ϖ` (`ϖ^p ∣ p`), every `P : R` and `m : ℕ`, there
is `ξ : PreTilt R p` with

  `v (P - ♯ξ) ≤ v (p:R) * max (v (♯ξ)) (v (ϖ 0) ^ (p * m))`

at every continuous valuation of the unit ball of `R`.

The route: `Work.DSM2p.witt_step` (the one-step Witt recursion of the source, TeX lines
2128–2203) produces `z'` from `z` keeping `θ z' = θ z` and lowering the tails of the Teichmüller
digits; iterating it `m` times and reading off `ξ = z_m.coeff 0` through the truncated expansion
`Work.DSM2p.fontaineTheta_sub_sum_mem` gives the estimate.

## Contents

* `surjective_fontaineTheta_of_frobSurj` : `θ` is onto (Frobenius is onto `R ⧸ (p)`);
* `exists_lift_digits_le_one` : every `P : R` has a lift all of whose tilt digits are `≤ 1`;
* `v_fontaineTheta_le_of_digits` : the tilt digits bound the `θ`-value.
-/

set_option linter.unusedSectionVars false

namespace Work.DSM2p

/-! ## The elementary inputs of the assembly -/

/-- `fontaineTheta` is surjective, because Frobenius is surjective on `R ⧸ (p)`. -/
theorem surjective_fontaineTheta_of_frobSurj {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (QR : DSMap.PerfectoidData p R) :
    Function.Surjective (WittVector.fontaineTheta R p) := by
  refine surjective_fontaineTheta ?_
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, hz⟩ := QR.frobSurj x
  refine ⟨Ideal.Quotient.mk (Ideal.span {(p : R)}) z, ?_⟩
  rw [frobenius_def, ← map_pow, Ideal.Quotient.eq]
  simpa [sub_eq_add_neg, add_comm] using neg_mem hz

/-- Every element of `R` is the `θ`-image of a Witt vector all of whose tilt digits are `≤ 1`
(the unit-ball condition bounds every digit by `1`). -/
theorem exists_lift_digits_le_one {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (QR : DSMap.PerfectoidData p R) (P : R) :
    ∃ z : WittVector p (PreTilt R p), WittVector.fontaineTheta R p z = P ∧ DigitsLe QR z 1 := by
  obtain ⟨z, hz⟩ := surjective_fontaineTheta_of_frobSurj QR P
  refine ⟨z, hz, fun Γ₀ _ v _ hball j => ?_⟩
  simpa using hball (PreTilt.untilt (tiltDigit z j)) (Set.mem_univ _)

/-- **The tilt digits bound the `θ`-value.**  If every tilt digit of `u` has `v`-value at most `γ`,
then `v (θ u) ≤ max γ ((v (p:R)) ^ (N + 1))`: the truncated Teichmüller expansion writes `θ u` as
`∑_{j ≤ N} ♯(tiltDigit u j) * p^j` plus a multiple of `p^{N+1}`, and `v` is unit-ball. -/
theorem v_fontaineTheta_le_of_digits {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (QR : DSMap.PerfectoidData p R) {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} (hv : IsContinuousValuation (QR.ϖ 0) v)
    (hball : IsUnitBall v Set.univ) (u : WittVector p (PreTilt R p)) (γ : Γ₀) {N : ℕ}
    (hγ : ∀ j : ℕ, v (PreTilt.untilt (tiltDigit u j)) ≤ γ) :
    v (WittVector.fontaineTheta R p u) ≤ max γ (v (p : R) ^ (N + 1)) := by
  have hp1 : v (p : R) < 1 := Valuation.map_p_lt_one QR v hv hball
  have hmem := fontaineTheta_sub_sum_mem QR u N
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hsplit : WittVector.fontaineTheta R p u =
      (∑ j ≤ N, PreTilt.untilt (tiltDigit u j) * (p : R) ^ j) + (p : R) ^ (N + 1) * c := by
    rw [← hc]; ring
  rw [hsplit]
  refine le_trans (v.map_add _ _) (max_le ?_ ?_)
  · refine v.map_sum_le fun j hj => ?_
    rw [map_mul]
    refine le_trans (mul_le_mul' (hγ j) le_rfl) ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · simp only [pow_zero, map_one, mul_one]
      exact le_max_left γ (v (p : R) ^ (N + 1))
    · have h1 : v ((p : R) ^ j) ≤ 1 := by
        rw [map_pow]
        exact pow_le_one' (le_of_lt hp1) j
      calc γ * v ((p : R) ^ j) ≤ γ * 1 := mul_le_mul' le_rfl h1
        _ = γ := mul_one γ
        _ ≤ max γ (v (p : R) ^ (N + 1)) := le_max_left _ _
  · rw [map_mul, map_pow]
    have h1 : v c ≤ 1 := hball c (Set.mem_univ _)
    calc v (p : R) ^ (N + 1) * v c ≤ v (p : R) ^ (N + 1) * 1 := mul_le_mul' le_rfl h1
      _ = v (p : R) ^ (N + 1) := mul_one _
      _ ≤ max γ (v (p : R) ^ (N + 1)) := le_max_right _ _

/-- **The sharper estimate.**  If in addition the `0`-th Witt coordinate of `u` vanishes, then
`P - ♯ξ = θ u` is not merely `≤ max γ (v p)^{N+1}` but `≤ v p * max γ (v p)^N`: the `j = 0` term of
the expansion is `0`, so every remaining term carries a factor `v p`. -/
theorem v_fontaineTheta_le_mul_of_coeff_zero_eq_zero {p : ℕ} [Fact p.Prime] {R : Type*}
    [CommRing R] [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (QR : DSMap.PerfectoidData p R) {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} (hv : IsContinuousValuation (QR.ϖ 0) v)
    (hball : IsUnitBall v Set.univ) (u : WittVector p (PreTilt R p)) (γ : Γ₀) {N : ℕ}
    (h0 : u.coeff 0 = 0) (hγ : ∀ j : ℕ, 1 ≤ j → v (PreTilt.untilt (tiltDigit u j)) ≤ γ) :
    v (WittVector.fontaineTheta R p u) ≤ v (p : R) * max γ (v (p : R) ^ N) := by
  have hp1 : v (p : R) < 1 := Valuation.map_p_lt_one QR v hv hball
  have hp0 : 0 ≤ v (p : R) := zero_le
  have hmem := fontaineTheta_sub_sum_mem QR u N
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hsplit : WittVector.fontaineTheta R p u =
      (∑ j ≤ N, PreTilt.untilt (tiltDigit u j) * (p : R) ^ j) + (p : R) ^ (N + 1) * c := by
    rw [← hc]; ring
  rw [hsplit]
  refine le_trans (v.map_add _ _) (max_le ?_ ?_)
  · refine v.map_sum_le (g := v (p : R) * max γ (v (p : R) ^ N)) fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · have hz : PreTilt.untilt (tiltDigit u 0) = 0 := by
        rw [tiltDigit_zero, h0]
        change Perfection.teichmuller p (Ideal.span {(p : R)}) 0 = 0
        exact Perfection.teichmuller_zero
      rw [hz, zero_mul, map_zero]
      exact mul_nonneg hp0 (zero_le.trans (le_max_left γ (v (p : R) ^ N)))
    · rw [map_mul]
      have h1 : v ((p : R) ^ j) ≤ v (p : R) := by
        rw [map_pow]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj')
        rw [pow_succ, mul_comm]
        exact mul_le_of_le_one_right hp0 (pow_le_one' hp1.le k)
      calc v (PreTilt.untilt (tiltDigit u j)) * v ((p : R) ^ j)
          ≤ γ * v (p : R) := mul_le_mul' (hγ j hj') h1
        _ ≤ max γ (v (p : R) ^ N) * v (p : R) := mul_le_mul' (le_max_left _ _) le_rfl
        _ = v (p : R) * max γ (v (p : R) ^ N) := mul_comm _ _
  · rw [map_mul, map_pow]
    have h1 : v c ≤ 1 := hball c (Set.mem_univ _)
    calc v (p : R) ^ (N + 1) * v c ≤ v (p : R) ^ (N + 1) * 1 := mul_le_mul' le_rfl h1
      _ = v (p : R) ^ (N + 1) := mul_one _
      _ = v (p : R) * v (p : R) ^ N := by rw [pow_succ']
      _ ≤ v (p : R) * max γ (v (p : R) ^ N) := mul_le_mul' le_rfl (le_max_right _ _)

/-! ## The target -/

theorem approx_lem {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    (QR : DSMap.PerfectoidData p R) [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R] (P : R) (m : ℕ) :
    ∃ ξ : PreTilt R p, ∀ {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
      (v : Valuation R Γ₀), IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ →
        v (P - PreTilt.untilt ξ) ≤
          v (p : R) * max (v (PreTilt.untilt ξ)) (v (QR.ϖ 0) ^ (p * m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: any lift `z₀` of `P` and `ξ := z₀.coeff 0`; the `0`-th coordinate of
    -- `z₀ - [ξ]` vanishes, so `P - ♯ξ = θ (z₀ - [ξ]) ∈ (p)`.
    obtain ⟨z₀, hz₀⟩ := surjective_fontaineTheta_of_frobSurj QR P
    refine ⟨z₀.coeff 0, ?_⟩
    intro Γ₀ _ v hv hball
    have hcoeff : (z₀ - WittVector.teichmuller p (z₀.coeff 0)).coeff 0 = 0 := by
      have h := (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (n := 1)
        (x := z₀) (y := WittVector.teichmuller p (z₀.coeff 0))).mp
      exact h (fun i hi => by
        interval_cases i
        rw [WittVector.teichmuller_coeff_zero]) 0 (by norm_num)
    have hmem : WittVector.fontaineTheta R p
        (z₀ - WittVector.teichmuller p (z₀.coeff 0)) ∈ Ideal.span {(p : R)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, WittVector.mk_fontaineTheta, hcoeff]
      rfl
    rw [mul_zero, pow_zero, max_eq_right (hball _ (Set.mem_univ _)), mul_one]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hmem
    have hsplit : P - PreTilt.untilt (z₀.coeff 0)
        = WittVector.fontaineTheta R p
            (z₀ - WittVector.teichmuller p (z₀.coeff 0)) := by
      rw [map_sub, hz₀, WittVector.fontaineTheta_teichmuller]
    rw [hsplit, hc, map_mul]
    calc v (p : R) * v c ≤ v (p : R) * 1 := mul_le_mul' le_rfl (hball c (Set.mem_univ _))
      _ = v (p : R) := mul_one _
  · -- `m ≥ 1`: iterate the one-step recursion
    obtain ⟨z₀, hz₀⟩ := surjective_fontaineTheta_of_frobSurj QR P
    let step : WittVector p (PreTilt R p) → WittVector p (PreTilt R p) :=
      fun z => Classical.choose (witt_step_rec QR z)
    let zs : ℕ → WittVector p (PreTilt R p) := fun n => Nat.rec z₀ (fun _ z => step z) n
    have hzs_succ : ∀ n : ℕ, zs (n + 1) = step (zs n) := fun n => rfl
    have hθ : ∀ n : ℕ,
        WittVector.fontaineTheta R p (zs (n + 1)) = WittVector.fontaineTheta R p (zs n) := by
      intro n
      rw [hzs_succ]
      exact (Classical.choose_spec (witt_step_rec QR (zs n))).1
    have hθP : WittVector.fontaineTheta R p (zs m) = P := by
      have hall : ∀ n : ℕ, WittVector.fontaineTheta R p (zs n) = P := by
        intro n
        induction n with
        | zero => simpa [zs] using hz₀
        | succ k ih => rw [hθ k, ih]
      exact hall m
    refine ⟨(zs m).coeff 0, ?_⟩
    intro Γ₀ _ v hv hball
    have hstep : ∀ n : ℕ, ∀ (v' : Valuation R Γ₀),
        IsContinuousValuation (QR.ϖ 0) v' → IsUnitBall v' Set.univ →
        ∀ (β : Γ₀), (∀ j : ℕ, v' (PreTilt.untilt (tiltDigit (zs n) j)) ≤ β) →
          (∀ j : ℕ, v' (PreTilt.untilt (tiltDigit (zs (n + 1)) j)) ≤
              max (v' (QR.ϖ 0) ^ p * β) (v' (PreTilt.untilt ((zs n).coeff 0)))) ∧
          (∀ j : ℕ, v' (PreTilt.untilt (tiltDigit
                (zs (n + 1) - WittVector.teichmuller p ((zs (n + 1)).coeff 0)) j)) ≤
              max (v' (QR.ϖ 0) ^ p * β) (v' (PreTilt.untilt ((zs n).coeff 0)))) := by
      intro n v' hv' hball' β hβ
      rw [hzs_succ]
      exact (Classical.choose_spec (witt_step_rec QR (zs n))).2 Γ₀ v' hv' hball' β hβ
    have htail := iterate_tail_bound_fixed (QR := QR) (zs := zs) (m := m) hθ hstep v hv hball
    set A : Γ₀ := max (v (PreTilt.untilt ((zs m).coeff 0))) (v (QR.ϖ 0) ^ (p * m)) with hA
    have hu0 : (zs m - WittVector.teichmuller p ((zs m).coeff 0)).coeff 0 = 0 := by
      have h := (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (n := 1)
        (x := zs m) (y := WittVector.teichmuller p ((zs m).coeff 0))).mp
      exact h (fun i hi => by interval_cases i; rw [WittVector.teichmuller_coeff_zero])
        0 (by norm_num)
    have hkey := v_fontaineTheta_le_mul_of_coeff_zero_eq_zero (N := m) QR hv hball
      (zs m - WittVector.teichmuller p ((zs m).coeff 0)) A hu0
      (fun j hj => by rw [hA]; exact htail j)
    have hN : v (p : R) ^ m ≤ A := by
      rw [hA]
      refine le_trans ?_ (le_max_right _ _)
      have hpow : v (QR.ϖ 0) ^ (p * m) = v (p : R) ^ m := by
        rw [pow_mul, v_varpi_pow_eq_v_p QR hball]
      rw [hpow]
    have hsplit : P - PreTilt.untilt ((zs m).coeff 0) = WittVector.fontaineTheta R p
        (zs m - WittVector.teichmuller p ((zs m).coeff 0)) := by
      rw [map_sub, hθP, WittVector.fontaineTheta_teichmuller]
    rw [hsplit]
    exact le_trans hkey (mul_le_mul' le_rfl (max_le le_rfl hN))

end Work.DSM2p
