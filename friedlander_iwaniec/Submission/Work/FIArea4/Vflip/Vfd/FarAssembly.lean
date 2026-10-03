import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarWDefs

/-!
# Assembly of the far-numerics estimate

This module proves the reindexing steps that reduce the far sum
`Σ_{m,c} [m | c] farW(m,c) · p14L2 (cR c R) S (redA c α)`
to the divisor-weighted energy `Σ_{r} (Σ_{c | r} Σ_{m | c} farW(m,c)) · Σ_s ‖α r s‖²`,
and assembles the final estimate from the pointwise divisor bound `farW_divisor_sum_le`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `Σ_{c ∈ range (n+1)} f c = Σ_{c ∈ Icc 1 n} f c` when `f 0 = 0`. -/
lemma sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) (h0 : f 0 = 0) :
    (∑ c ∈ Finset.range (n + 1), f c) = ∑ c ∈ Finset.Icc 1 n, f c := by
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le n)]
  have hsucc : Order.succ (0 : ℕ) = 1 := by simp [Order.succ_eq_add_one]
  rw [hsucc, Finset.sum_insert (by simp [Finset.mem_Icc]), h0, zero_add]

/-- Reindexing `Σ_{r ∈ Icc 1 N, ρ ∣ r} g r = Σ_{u ∈ Icc 1 (N/ρ)} g (ρ u)`. -/
lemma sum_Icc_filter_dvd_eq_sum_Icc_div {ρ N : ℕ} (hρ : 1 ≤ ρ) (g : ℕ → ℝ) :
    (∑ r ∈ (Finset.Icc 1 N).filter (fun r => ρ ∣ r), g r)
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
    refine ⟨ρ * u, ?_, Nat.mul_div_cancel_left u hρ⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨one_le_mul hρ hu.1, ?_⟩, dvd_mul_right ρ u⟩
    calc ρ * u ≤ ρ * (N / ρ) := Nat.mul_le_mul_left ρ hu.2
      _ ≤ N := Nat.mul_div_le _ _
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨-, k, hk⟩ := hr
    subst hk
    rw [Nat.mul_div_cancel_left k hρ]

/-- `Σ_{ρ ≤ N} Gr (c ρ) = Σ_{r ≤ N} [c ∣ r] Gr r`, when `Gr` vanishes above `N`. -/
lemma sum_shift_Gr (c N : ℕ) (Gr : ℕ → ℝ) (hc : 1 ≤ c) (hGr : ∀ r, N < r → Gr r = 0) :
    (∑ ρ ∈ Finset.Icc 1 N, Gr (c * ρ)) = ∑ r ∈ Finset.Icc 1 N, (if c ∣ r then Gr r else 0) := by
  have hsub : Finset.Icc 1 (N / c) ⊆ Finset.Icc 1 N := by
    intro x hx; rw [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 (Nat.div_le_self N c)⟩
  have hzero : ∀ ρ ∈ Finset.Icc 1 N, ρ ∉ Finset.Icc 1 (N / c) → Gr (c * ρ) = 0 := by
    intro ρ hρ hρc
    apply hGr
    have hρ1 : 1 ≤ ρ := (Finset.mem_Icc.mp hρ).1
    have hlt : N / c < ρ := by
      by_contra hle
      exact hρc (Finset.mem_Icc.mpr ⟨hρ1, by omega⟩)
    have hmodlt : N % c < c := Nat.mod_lt N (by omega)
    calc N = c * (N / c) + N % c := (Nat.div_add_mod N c).symm
      _ < c * (N / c) + c := by omega
      _ = c * (N / c + 1) := by ring
      _ ≤ c * ρ := Nat.mul_le_mul_left c (Nat.succ_le_of_lt hlt)
  rw [← Finset.sum_subset hsub hzero, ← sum_Icc_filter_dvd_eq_sum_Icc_div hc Gr,
    Finset.sum_filter]

/-- The `(m,c)`-double sum of the far part is the `c`-sum of the divisor sums of the weights. -/
lemma far_sum_reindex (D R S : ℕ) (H ε : ℝ) (α : ℕ → ℕ → ℂ) :
    (∑ m ∈ Finset.range (2 * R + 1), ∑ c ∈ Finset.range (2 * R + 1),
        if m ∣ c then farW D R S H ε m c * Work.FIArea4.p14L2 (cR c R) S (redA c α) else 0)
      = ∑ c ∈ Finset.Icc 1 (2 * R),
          (∑ m ∈ c.divisors, farW D R S H ε m c)
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) := by
  rw [Finset.sum_comm]
  rw [sum_range_succ_eq_sum_Icc (2 * R)
        (fun c => ∑ m ∈ Finset.range (2 * R + 1),
            if m ∣ c then farW D R S H ε m c * Work.FIArea4.p14L2 (cR c R) S (redA c α) else 0) ?_]
  · apply Finset.sum_congr rfl; intro c hc
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    have hc2 : c ≤ 2 * R := (Finset.mem_Icc.mp hc).2
    have hfilter : (Finset.range (2 * R + 1)).filter (fun m => m ∣ c) = c.divisors := by
      ext m; rw [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
      constructor
      · rintro ⟨hm, hd⟩; exact ⟨hd, by omega⟩
      · rintro ⟨hd, hcne⟩
        have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hcne)
        have hmle : m ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hcne) hd
        exact ⟨by omega, hd⟩
    rw [show (∑ m ∈ Finset.range (2 * R + 1),
            (if m ∣ c then farW D R S H ε m c
              * Work.FIArea4.p14L2 (cR c R) S (redA c α) else 0))
          = (∑ m ∈ Finset.range (2 * R + 1),
              (if m ∣ c then farW D R S H ε m c else 0))
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) from by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro m _
        by_cases h : m ∣ c <;> simp [h]]
    rw [← Finset.sum_filter, hfilter]
  · -- the `c = 0` term vanishes
    simp only [Work.FIArea4.p14L2, cR]
    simp

/-- The reindexed far sum is controlled by the divisor weights times the energies of the rows. -/
lemma far_sum_le_ener (D R S : ℕ) (H ε : ℝ) (α : ℕ → ℕ → ℂ)
    (hR : 1 ≤ R) (hH1 : 1 ≤ H) (hsupp : ∀ r s, α r s ≠ 0 → r ≤ 2 * R) :
    (∑ c ∈ Finset.Icc 1 (2 * R), (∑ m ∈ c.divisors, farW D R S H ε m c)
        * Work.FIArea4.p14L2 (cR c R) S (redA c α))
      ≤ ∑ r ∈ Finset.Icc 1 (2 * R),
          (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farW D R S H ε m c)
            * (∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)) := by
  set Gr : ℕ → ℝ := fun x => ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α x s) with hGrdef
  have hGnn : ∀ x, 0 ≤ Gr x := fun x =>
    Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _)
  have hGsupp : ∀ r, 2 * R < r → Gr r = 0 := by
    intro r hr; rw [hGrdef]
    apply Finset.sum_eq_zero; intro s _
    rw [Complex.normSq_eq_zero]
    by_contra h
    exact absurd (hsupp r s h) (by omega)
  have hFnn : ∀ c, 1 ≤ c → 0 ≤ ∑ m ∈ c.divisors, farW D R S H ε m c := by
    intro c hc
    exact Finset.sum_nonneg (fun m _ => farW_nonneg hH1 hR hc)
  have hL2 : ∀ c, Work.FIArea4.p14L2 (cR c R) S (redA c α)
      = ∑ ρ ∈ Finset.Icc 1 (2 * (cR c R)), Gr (c * ρ) := by
    intro c
    rw [Work.FIArea4.p14L2, hGrdef]
    apply Finset.sum_congr rfl; intro ρ _
    apply Finset.sum_congr rfl; intro s _
    rw [redA_apply]
  calc (∑ c ∈ Finset.Icc 1 (2 * R), (∑ m ∈ c.divisors, farW D R S H ε m c)
          * Work.FIArea4.p14L2 (cR c R) S (redA c α))
      = ∑ c ∈ Finset.Icc 1 (2 * R), (∑ m ∈ c.divisors, farW D R S H ε m c)
          * ∑ ρ ∈ Finset.Icc 1 (2 * (cR c R)), Gr (c * ρ) := by
        apply Finset.sum_congr rfl; intro c _; rw [hL2 c]
    _ ≤ ∑ c ∈ Finset.Icc 1 (2 * R), (∑ m ∈ c.divisors, farW D R S H ε m c)
          * ∑ ρ ∈ Finset.Icc 1 (2 * R), Gr (c * ρ) := by
        apply Finset.sum_le_sum; intro c hc
        apply mul_le_mul_of_nonneg_left _ (hFnn c (Finset.mem_Icc.mp hc).1)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ρ hρ; rw [Finset.mem_Icc] at hρ ⊢
          exact ⟨hρ.1, le_trans hρ.2 (Nat.mul_le_mul_left 2 (cR_le_self (Finset.mem_Icc.mp hc).1 hR))⟩
        · intro ρ _ _; exact hGnn (c * ρ)
    _ = ∑ c ∈ Finset.Icc 1 (2 * R), ∑ ρ ∈ Finset.Icc 1 (2 * R),
          (∑ m ∈ c.divisors, farW D R S H ε m c) * Gr (c * ρ) := by
        apply Finset.sum_congr rfl; intro c _; rw [Finset.mul_sum]
    _ = ∑ c ∈ Finset.Icc 1 (2 * R), ∑ r ∈ Finset.Icc 1 (2 * R),
          (∑ m ∈ c.divisors, farW D R S H ε m c) * (if c ∣ r then Gr r else 0) := by
        apply Finset.sum_congr rfl; intro c hc
        rw [← Finset.mul_sum, sum_shift_Gr c (2 * R) Gr (Finset.mem_Icc.mp hc).1 hGsupp,
          Finset.mul_sum]
    _ = ∑ r ∈ Finset.Icc 1 (2 * R), Gr r * ∑ c ∈ Finset.Icc 1 (2 * R),
          (if c ∣ r then ∑ m ∈ c.divisors, farW D R S H ε m c else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro c _
        by_cases h : c ∣ r <;> simp [h, mul_comm]
    _ = ∑ r ∈ Finset.Icc 1 (2 * R), Gr r * ∑ c ∈ r.divisors,
          ∑ m ∈ c.divisors, farW D R S H ε m c := by
        apply Finset.sum_congr rfl; intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hr2 : r ≤ 2 * R := (Finset.mem_Icc.mp hr).2
        congr 1
        rw [← Finset.sum_filter]
        congr 1
        ext c; rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨h1, h2⟩, hd⟩; exact ⟨hd, by omega⟩
        · rintro ⟨hd, hrne⟩
          have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hrne)
          have hcle : c ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hrne) hd
          exact ⟨⟨hcpos, by omega⟩, hd⟩
    _ = ∑ r ∈ Finset.Icc 1 (2 * R),
          (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farW D R S H ε m c)
            * (∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)) := by
        apply Finset.sum_congr rfl; intro r _
        rw [hGrdef]; ring

/-- **Assembly.**  Given the pointwise divisor bound on `farW`, the far sum of the flipped-moduli
bound is at most a constant times `farB · p14Ener`. -/
theorem far_sum_numerics_aux (ε : ℝ) (hε : 0 < ε) (Cw : ℝ) (hCw : 0 < Cw)
    (hW : ∀ (D R S : ℕ) (H : ℝ) (r : ℕ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S → R * S < D * D →
      H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) →
      1 ≤ r → r ≤ 2 * R →
      (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farW D R S H ε m c)
        ≤ Cw * farB D R S H ε * ((r.divisors.card : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (H : ℝ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S → R * S < D * D →
      H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      (∑ m ∈ Finset.range (2 * R + 1), ∑ c ∈ Finset.range (2 * R + 1),
        if m ∣ c then farW D R S H ε m c
            * Work.FIArea4.p14L2 (cR c R) S (redA c α) else 0)
      ≤ C * farB D R S H ε * Work.FIArea4.p14Ener R S α := by
  refine ⟨Cw, hCw, ?_⟩
  intro D R S H α hD hR hS hDRS hRSD hH hsupp
  have hsupp' : ∀ r s, α r s ≠ 0 → r ≤ 2 * R := fun r s h => (hsupp r s h).2.1
  have hH1 : 1 ≤ H := by
    rw [hH]
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
    apply Real.one_le_rpow
    · rw [le_div_iff₀ hDpos, one_mul]
      exact_mod_cast hDRS
    · norm_num
  rw [far_sum_reindex D R S H ε α]
  calc ∑ c ∈ Finset.Icc 1 (2 * R), (∑ m ∈ c.divisors, farW D R S H ε m c)
        * Work.FIArea4.p14L2 (cR c R) S (redA c α)
      ≤ ∑ r ∈ Finset.Icc 1 (2 * R),
          (∑ c ∈ r.divisors, ∑ m ∈ c.divisors, farW D R S H ε m c)
            * (∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)) :=
        far_sum_le_ener D R S H ε α hR hH1 hsupp'
    _ ≤ ∑ r ∈ Finset.Icc 1 (2 * R),
          (Cw * farB D R S H ε * ((r.divisors.card : ℕ) : ℝ))
            * (∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)) := by
        apply Finset.sum_le_sum; intro r hr
        exact mul_le_mul_of_nonneg_right
          (hW D R S H r hD hR hS hDRS hRSD hH (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)
          (Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
    _ = Cw * farB D R S H ε * Work.FIArea4.p14Ener R S α := by
        rw [Work.FIArea4.p14Ener, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        ring

end
end Work.FIArea4.Vflip.Vfd
