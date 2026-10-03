import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup
import Submission.Work.FIArea4.A4varbounds
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

/-!
# The `L²`-loss of a shift of the first coordinate: `Σ_ρ ρ^{-1/2} L2(ρ·) ≪ (2R)^{ε/2} L2`

Write `shiftCoef ρ β (r,s) = β (ρ r) s` and `p14L2 R S β = Σ_{r ≤ 2R, s ≤ 2S} |β r s|²`.
The main theorem of this file bounds the sum of the shifted `L²`-norms, weighted by
`ρ^{-1/2}`, by a constant times `(2R)^{ε/2}` times `L2 β`, for every `ε > 0` — the loss
`(2R)^{ε/2}` replaces the trivial (and useless) loss `O(√R)`.

The only arithmetic input is the divisor bound `d(n) ≪_ε n^ε`
(`Commons.NumberTheory.DivisorBound.card_divisors_le_rpow`); the point is that after
reindexing by `u = ρ r` the weight of a pair `(ρ, r)` is bounded by the divisor count
`d(u) ≤ #{ρ : ρ | u}`, which is exactly the quantity the divisor bound controls.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Reindexing the multiples of `ρ` in `[1, N]` by `u ↦ ρ * u`. -/
private lemma sum_Icc_filter_dvd_eq_sum_Icc_div {ρ N : ℕ} (hρ : 1 ≤ ρ) (g : ℕ → ℝ) :
    ∑ r ∈ (Finset.Icc 1 N).filter (fun r => ρ ∣ r), g r
      = ∑ u ∈ Finset.Icc 1 (N / ρ), g (ρ * u) := by
  apply Finset.sum_bij (fun r _ => r / ρ)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hr1, hr2⟩, k, hk⟩ := hr
    subst hk
    simp only [Finset.mem_Icc]
    rw [Nat.mul_div_cancel_left k hρ]
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp at hr1
      · exact hk0
    · rw [Nat.le_div_iff_mul_le hρ]
      calc k * ρ = ρ * k := by ring
        _ ≤ N := hr2
  · intro r1 hr1 r2 hr2 h
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr1 hr2
    obtain ⟨-, k1, hk1⟩ := hr1
    obtain ⟨-, k2, hk2⟩ := hr2
    rw [hk1, hk2, Nat.mul_div_cancel_left k1 hρ, Nat.mul_div_cancel_left k2 hρ] at h
    rw [hk1, hk2, h]
  · intro u hu
    simp only [Finset.mem_Icc] at hu
    refine ⟨ρ * u, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨one_le_mul hρ hu.1, ?_⟩, dvd_mul_right ρ u⟩
      calc ρ * u ≤ ρ * (N / ρ) := Nat.mul_le_mul_left ρ hu.2
        _ ≤ N := Nat.mul_div_le _ _
    · exact Nat.mul_div_cancel_left u hρ
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨-, k, hk⟩ := hr
    subst hk
    rw [Nat.mul_div_cancel_left k hρ]

/-- **Reindexing the shifted sum.**  For `a` vanishing above `N`,
`Σ_{ρ ≤ N} ρ^{-1/2} Σ_{r ≤ N} a(ρ r) = Σ_{u ≤ N} a(u) Σ_{ρ | u} ρ^{-1/2}`.
(The hypothesis that `a` vanishes above `N` is what makes the truncations `ρ ≤ N`,
`r ≤ N` on the left harmless: on the left the product `ρ r` never exceeds `N`.) -/
private lemma sum_rpow_mul_shift_eq_divisors (N : ℕ) (a : ℕ → ℝ)
    (hav : ∀ u, N < u → a u = 0) :
    ∑ ρ ∈ Finset.Icc 1 N, (ρ : ℝ) ^ (-(1 : ℝ) / 2) * (∑ r ∈ Finset.Icc 1 N, a (ρ * r))
      = ∑ u ∈ Finset.Icc 1 N, a u * ∑ ρ ∈ u.divisors, (ρ : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hinner : ∀ ρ ∈ Finset.Icc 1 N,
      ∑ r ∈ Finset.Icc 1 N, a (ρ * r)
        = ∑ u ∈ Finset.Icc 1 N, (if ρ ∣ u then a u else 0) := by
    intro ρ hρ
    have hρ1 : 1 ≤ ρ := (Finset.mem_Icc.mp hρ).1
    have hρpos : 0 < ρ := hρ1
    have hsub : Finset.Icc 1 (N / ρ) ⊆ Finset.Icc 1 N := by
      intro r hr
      simp only [Finset.mem_Icc] at hr ⊢
      exact ⟨hr.1, le_trans hr.2 (Nat.div_le_self N ρ)⟩
    -- terms with `ρ * r > N` vanish, so the range `r ≤ N` may be cut down to `r ≤ N / ρ`
    have h1 : ∑ r ∈ Finset.Icc 1 (N / ρ), a (ρ * r) = ∑ r ∈ Finset.Icc 1 N, a (ρ * r) := by
      refine Finset.sum_subset hsub ?_
      intro r hr hrn
      apply hav
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hlt : N / ρ < r := by
        by_contra hc
        exact hrn (Finset.mem_Icc.mpr ⟨hr1, Nat.le_of_not_lt hc⟩)
      have hmodlt : N % ρ < ρ := Nat.mod_lt N hρpos
      have h2 : ρ * (N / ρ + 1) = ρ * (N / ρ) + ρ := by ring
      calc N = ρ * (N / ρ) + N % ρ := (Nat.div_add_mod N ρ).symm
        _ < ρ * (N / ρ) + ρ := by omega
        _ = ρ * (N / ρ + 1) := h2.symm
        _ ≤ ρ * r := Nat.mul_le_mul_left ρ (Nat.succ_le_of_lt hlt)
    have h2 : ∑ r ∈ Finset.Icc 1 (N / ρ), a (ρ * r)
        = ∑ u ∈ (Finset.Icc 1 N).filter (fun u => ρ ∣ u), a u :=
      (sum_Icc_filter_dvd_eq_sum_Icc_div hρ1 a).symm
    have h3 : ∑ u ∈ (Finset.Icc 1 N).filter (fun u => ρ ∣ u), a u
        = ∑ u ∈ Finset.Icc 1 N, (if ρ ∣ u then a u else 0) :=
      Finset.sum_filter ..
    exact h1.symm.trans (h2.trans h3)
  calc ∑ ρ ∈ Finset.Icc 1 N, (ρ : ℝ) ^ (-(1 : ℝ) / 2) * (∑ r ∈ Finset.Icc 1 N, a (ρ * r))
      = ∑ ρ ∈ Finset.Icc 1 N, (ρ : ℝ) ^ (-(1 : ℝ) / 2)
          * (∑ u ∈ Finset.Icc 1 N, (if ρ ∣ u then a u else 0)) := by
        apply Finset.sum_congr rfl; intro ρ hρ; rw [hinner ρ hρ]
    _ = ∑ ρ ∈ Finset.Icc 1 N, ∑ u ∈ Finset.Icc 1 N,
          (ρ : ℝ) ^ (-(1 : ℝ) / 2) * (if ρ ∣ u then a u else 0) := by
        apply Finset.sum_congr rfl; intro ρ _; rw [Finset.mul_sum]
    _ = ∑ u ∈ Finset.Icc 1 N, ∑ ρ ∈ Finset.Icc 1 N,
          (ρ : ℝ) ^ (-(1 : ℝ) / 2) * (if ρ ∣ u then a u else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ u ∈ Finset.Icc 1 N, a u
          * ∑ ρ ∈ Finset.Icc 1 N, (if ρ ∣ u then (ρ : ℝ) ^ (-(1 : ℝ) / 2) else 0) := by
        apply Finset.sum_congr rfl; intro u _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro ρ _
        by_cases h : ρ ∣ u
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
    _ = ∑ u ∈ Finset.Icc 1 N, a u * ∑ ρ ∈ u.divisors, (ρ : ℝ) ^ (-(1 : ℝ) / 2) := by
        apply Finset.sum_congr rfl; intro u hu
        congr 1
        rw [← Finset.sum_filter]
        congr 1
        obtain ⟨hu1, hu2⟩ := Finset.mem_Icc.mp hu
        ext ρ
        rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨h1, h2⟩, hd⟩
          exact ⟨hd, by omega⟩
        · rintro ⟨hd, hu0⟩
          have hρpos : 0 < ρ := Nat.pos_of_dvd_of_pos hd (by omega)
          exact ⟨⟨hρpos, le_trans (Nat.le_of_dvd (by omega) hd) hu2⟩, hd⟩

/-- **The main estimate.**  For every `ε > 0` there is `K > 0` such that for every `R, S ≥ 1`
and every coefficient array `β` supported on `r ≤ 2R`,
`Σ_{ρ ≤ 2R} ρ^{-1/2} · L2 (shiftCoef ρ β) ≤ K · (2R)^{ε/2} · L2 β`. -/
theorem sum_shift_L2_rpow_le (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R S : ℕ) (β : ℕ → ℕ → ℂ),
      1 ≤ R → 1 ≤ S → (∀ r s, β r s ≠ 0 → r ≤ 2*R) →
      ∑ ρ ∈ Finset.Icc 1 (2*R),
          ((ρ:ℝ)) ^ (-(1:ℝ)/2) * Work.FIArea4.p14L2 R S (Work.FIArea4.Vflip.Vfd.shiftCoef ρ β)
        ≤ K * ((2*R:ℝ)) ^ (ε/2) * Work.FIArea4.p14L2 R S β := by
  -- the divisor bound at the exponent `ε/2`
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (ε / 2) (by linarith)
  refine ⟨C, hCpos, ?_⟩
  intro R S β hR hS hβ
  set N : ℕ := 2*R with hNdef
  -- the `s`-summed array; by hypothesis it vanishes above `2R = N`
  set a : ℕ → ℝ := fun u => ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β u s) with hadef
  have hNR : (N:ℝ) = (2:ℝ) * (R:ℝ) := by rw [hNdef]; push_cast; ring
  have ha0 : ∀ u, 0 ≤ a u := fun u => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _)
  have hav : ∀ u, N < u → a u = 0 := by
    intro u hu
    have huR : 2*R < u := by omega
    apply Finset.sum_eq_zero
    intro s _
    rw [Complex.normSq_eq_zero]
    by_contra h
    exact absurd (hβ u s h) (by omega)
  have hL2 : Work.FIArea4.p14L2 R S β = ∑ u ∈ Finset.Icc 1 N, a u := by
    rw [hNdef]; rfl
  have hL : ∑ ρ ∈ Finset.Icc 1 N,
        ((ρ:ℝ)) ^ (-(1:ℝ)/2) * Work.FIArea4.p14L2 R S (Work.FIArea4.Vflip.Vfd.shiftCoef ρ β)
      = ∑ ρ ∈ Finset.Icc 1 N, (ρ:ℝ)^(-(1:ℝ)/2) * ∑ r ∈ Finset.Icc 1 N, a (ρ*r) := by
    apply Finset.sum_congr rfl
    intro ρ _
    congr 1
  -- each `u ≤ N` contributes a divisor sum, bounded by `d(u) ≤ C u^{ε/2} ≤ C N^{ε/2}`
  have hmid : ∑ u ∈ Finset.Icc 1 N, a u * (∑ ρ ∈ u.divisors, (ρ:ℝ)^(-(1:ℝ)/2))
      ≤ C * (N:ℝ)^(ε/2) * ∑ u ∈ Finset.Icc 1 N, a u := by
    have hbound : ∀ u ∈ Finset.Icc 1 N,
        a u * (∑ ρ ∈ u.divisors, (ρ:ℝ)^(-(1:ℝ)/2)) ≤ a u * (C * (N:ℝ)^(ε/2)) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Finset.mem_Icc.mp hu
      have h1 : ∑ ρ ∈ u.divisors, (ρ:ℝ)^(-(1:ℝ)/2) ≤ (u.divisors.card : ℝ) := by
        calc ∑ ρ ∈ u.divisors, (ρ:ℝ)^(-(1:ℝ)/2) ≤ ∑ _ρ ∈ u.divisors, (1:ℝ) := by
              apply Finset.sum_le_sum
              intro ρ hρmem
              have hρ1 : 1 ≤ ρ := Nat.pos_of_mem_divisors hρmem
              have hb : (1:ℝ) ≤ (ρ:ℝ) := by exact_mod_cast hρ1
              calc (ρ:ℝ)^(-(1:ℝ)/2) ≤ (ρ:ℝ)^(0:ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
                _ = 1 := Real.rpow_zero _
          _ = (u.divisors.card : ℝ) := by simp
      have h2 : ((u.divisors.card : ℕ) : ℝ) ≤ C * (u:ℝ)^(ε/2) := hC u
      have h3 : (u:ℝ)^(ε/2) ≤ (N:ℝ)^(ε/2) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hu2) (by linarith)
      have h5 : ∑ ρ ∈ u.divisors, (ρ:ℝ)^(-(1:ℝ)/2) ≤ C * (N:ℝ)^(ε/2) :=
        le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left h3 (le_of_lt hCpos)))
      exact mul_le_mul_of_nonneg_left h5 (ha0 u)
    calc ∑ u ∈ Finset.Icc 1 N, a u * (∑ ρ ∈ u.divisors, (ρ:ℝ)^(-(1:ℝ)/2))
        ≤ ∑ u ∈ Finset.Icc 1 N, a u * (C * (N:ℝ)^(ε/2)) := Finset.sum_le_sum hbound
      _ = C * (N:ℝ)^(ε/2) * ∑ u ∈ Finset.Icc 1 N, a u := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro u _; ring
  calc ∑ ρ ∈ Finset.Icc 1 N,
        ((ρ:ℝ)) ^ (-(1:ℝ)/2) * Work.FIArea4.p14L2 R S (Work.FIArea4.Vflip.Vfd.shiftCoef ρ β)
      = ∑ ρ ∈ Finset.Icc 1 N, (ρ:ℝ)^(-(1:ℝ)/2) * ∑ r ∈ Finset.Icc 1 N, a (ρ*r) := hL
    _ = ∑ u ∈ Finset.Icc 1 N, a u * ∑ ρ ∈ u.divisors, (ρ:ℝ)^(-(1:ℝ)/2) :=
        sum_rpow_mul_shift_eq_divisors N a hav
    _ ≤ C * (N:ℝ)^(ε/2) * ∑ u ∈ Finset.Icc 1 N, a u := hmid
    _ = C * ((2*R:ℝ)) ^ (ε/2) * Work.FIArea4.p14L2 R S β := by
        rw [hNR, hL2]

end

end Work.FIArea4.Vflip.Vfd
