import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- From membership in the non-zero box `zPz N` deduce the absolute-value bound. -/
lemma natAbs_le_of_mem_zPz {N : ℕ} {z : ℤ} (h : z ∈ zPz N) : z.natAbs ≤ N := by
  simp only [zPz, Finset.mem_filter, Finset.mem_Icc] at h
  have : ((z.natAbs : ℤ)) ≤ (N : ℤ) := by
    rw [Int.natCast_natAbs]
    exact (abs_le (a := z) (b := (N : ℤ))).mpr h.1
  exact_mod_cast this

/-- The `k = 2` lacunarity step (Friedlander–Iwaniec Lemma 2.2). -/
lemma tau4_le_sum_small_divisors' :
    ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℝ)) ^ 4
        ≤ 256 * ∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d * d ≤ m),
                  ((d.divisors.card : ℝ)) ^ 8 := by
  intro m hm
  obtain ⟨d, hdvd, hd2, hcard⟩ :=
    Commons.NumberTheory.Divisors.small_divisor_tau_le (k := 2) (n := m) (by norm_num) hm
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : ((2 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ) / Real.log 2 = ((2 : ℕ) : ℝ) := by
    have heq : Real.log (((2 : ℕ)) : ℝ) = Real.log 2 := by norm_num
    rw [heq]
    rw [div_eq_iff (ne_of_gt hlog2pos)]
  rw [hexp] at hcard
  rw [Real.rpow_natCast] at hcard
  have hτm0 : (0 : ℝ) ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
  have hstep : ((m.divisors.card : ℝ)) ^ 4 ≤ 256 * ((d.divisors.card : ℝ)) ^ 8 := by
    calc ((m.divisors.card : ℝ)) ^ 4 ≤ ((2 * (d.divisors.card : ℝ)) ^ 2) ^ 4 :=
          pow_le_pow_left₀ hτm0 hcard 4
      _ = 256 * ((d.divisors.card : ℝ)) ^ 8 := by
        simp only [← pow_mul, mul_pow]
        norm_num
  have hmem : d ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d * d ≤ m) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), Nat.le_of_dvd (by omega) hdvd⟩, hdvd,
      by simpa [pow_two] using hd2⟩
  have hnn : ∀ e ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d * d ≤ m),
      0 ≤ ((e.divisors.card : ℝ)) ^ 8 := by intro e _; positivity
  have hsingle := Finset.single_le_sum hnn hmem
  exact le_trans hstep (mul_le_mul_of_nonneg_left hsingle (by norm_num))

/-- The `k = 2` majorant in indicator form on the range `[1, √M]`. -/
lemma tau4_le_sum_indicators' {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    ((m.divisors.card : ℝ)) ^ 4
      ≤ 256 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
          (if d ∣ m then ((d.divisors.card : ℝ)) ^ 8 else (0 : ℝ)) := by
  have h1 := tau4_le_sum_small_divisors' m hm
  have h2 : (∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d * d ≤ m),
        ((d.divisors.card : ℝ)) ^ 8)
      ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
          (if d ∣ m then ((d.divisors.card : ℝ)) ^ 8 else (0 : ℝ)) := by
    have hsub : (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d * d ≤ m)
        ⊆ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ∣ m) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, hdvd, hdd⟩ := hd
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hd1, Nat.le_sqrt'.mpr (le_trans (by simpa [pow_two] using hdd) hmM)⟩, hdvd⟩
    calc (∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d * d ≤ m),
            ((d.divisors.card : ℝ)) ^ 8)
        ≤ ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ∣ m),
            ((d.divisors.card : ℝ)) ^ 8 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
      _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
            (if d ∣ m then ((d.divisors.card : ℝ)) ^ 8 else (0 : ℝ)) := by
          rw [Finset.sum_filter]
  linarith [h1, h2]

/-- Commuting the innermost `d`-sum out of four nested sums over `ℤ`-finsets. -/
lemma sum4_sum_comm {a b c e : Finset ℤ} {D : Finset ℕ}
    (F : ℤ → ℤ → ℤ → ℤ → ℕ → ℝ) :
    (∑ x ∈ a, ∑ y ∈ b, ∑ h1 ∈ c, ∑ h2 ∈ e, ∑ d ∈ D, F x y h1 h2 d)
      = ∑ d ∈ D, ∑ x ∈ a, ∑ y ∈ b, ∑ h1 ∈ c, ∑ h2 ∈ e, F x y h1 h2 d := by
  have e1 : ∀ x y h1, (∑ h2 ∈ e, ∑ d ∈ D, F x y h1 h2 d)
      = ∑ d ∈ D, ∑ h2 ∈ e, F x y h1 h2 d := fun x y h1 => Finset.sum_comm
  have e2 : ∀ x y, (∑ h1 ∈ c, ∑ d ∈ D, ∑ h2 ∈ e, F x y h1 h2 d)
      = ∑ d ∈ D, ∑ h1 ∈ c, ∑ h2 ∈ e, F x y h1 h2 d := fun x y => Finset.sum_comm
  have e3 : ∀ x, (∑ y ∈ b, ∑ d ∈ D, ∑ h1 ∈ c, ∑ h2 ∈ e, F x y h1 h2 d)
      = ∑ d ∈ D, ∑ y ∈ b, ∑ h1 ∈ c, ∑ h2 ∈ e, F x y h1 h2 d := fun x => Finset.sum_comm
  calc (∑ x ∈ a, ∑ y ∈ b, ∑ h1 ∈ c, ∑ h2 ∈ e, ∑ d ∈ D, F x y h1 h2 d)
      = ∑ x ∈ a, ∑ y ∈ b, ∑ h1 ∈ c, ∑ d ∈ D, ∑ h2 ∈ e, F x y h1 h2 d := by
          apply Finset.sum_congr rfl; intro x _
          apply Finset.sum_congr rfl; intro y _
          apply Finset.sum_congr rfl; intro h1 _
          exact e1 x y h1
    _ = ∑ x ∈ a, ∑ y ∈ b, ∑ d ∈ D, ∑ h1 ∈ c, ∑ h2 ∈ e, F x y h1 h2 d := by
          apply Finset.sum_congr rfl; intro x _
          apply Finset.sum_congr rfl; intro y _
          exact e2 x y
    _ = ∑ x ∈ a, ∑ d ∈ D, ∑ y ∈ b, ∑ h1 ∈ c, ∑ h2 ∈ e, F x y h1 h2 d := by
          apply Finset.sum_congr rfl; intro x _
          exact e3 x
    _ = ∑ d ∈ D, ∑ x ∈ a, ∑ y ∈ b, ∑ h1 ∈ c, ∑ h2 ∈ e, F x y h1 h2 d :=
          Finset.sum_comm

/-- Pulling a constant out of four nested sums over `ℤ`-finsets. -/
lemma pull_const4'' {a b c e : Finset ℤ} (k : ℝ) (F : ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ x ∈ a, ∑ y ∈ b, ∑ h1 ∈ c, ∑ h2 ∈ e, k * F x y h1 h2)
      = k * ∑ x ∈ a, ∑ y ∈ b, ∑ h1 ∈ c, ∑ h2 ∈ e, F x y h1 h2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro h1 _
  rw [Finset.mul_sum]

/-- **The box reduction.** -/
theorem uboxSum_le_dsum :
    ∃ C : ℝ, 0 < C ∧ ∀ (r X Y : ℕ), 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.uboxSum r X Y
        ≤ C * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (r * (X ^ 2 + Y ^ 2))),
            ((d.divisors.card : ℝ)) ^ 8 * Work.FIArea2.R6.ndCount d r X Y := by
  refine ⟨256, by norm_num, ?_⟩
  intro r X Y hr hX hY
  set M : ℕ := r * (X ^ 2 + Y ^ 2) with hM
  have key : ∀ x ∈ zPz r, ∀ y ∈ zPz r, ∀ h1 ∈ zPz X, ∀ h2 ∈ zPz Y,
      T4 x y h1 h2
        ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
            (256 * ((d.divisors.card : ℝ)) ^ 8)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0) := by
    intro x hx y hy h1 hh1 h2 hh2
    have hxr : x.natAbs ≤ r := natAbs_le_of_mem_zPz hx
    have hyr : y.natAbs ≤ r := natAbs_le_of_mem_zPz hy
    have hh1X : h1.natAbs ≤ X := natAbs_le_of_mem_zPz hh1
    have hh2Y : h2.natAbs ≤ Y := natAbs_le_of_mem_zPz hh2
    have hmM : (x * h1 ^ 2 - y * h2 ^ 2).natAbs ≤ M := by
      have hx1 : (x * h1 ^ 2).natAbs ≤ r * X ^ 2 := by
        rw [Int.natAbs_mul, Int.natAbs_pow]
        exact Nat.mul_le_mul hxr (Nat.pow_le_pow_left hh1X 2)
      have hy1 : (y * h2 ^ 2).natAbs ≤ r * Y ^ 2 := by
        rw [Int.natAbs_mul, Int.natAbs_pow]
        exact Nat.mul_le_mul hyr (Nat.pow_le_pow_left hh2Y 2)
      calc (x * h1 ^ 2 - y * h2 ^ 2).natAbs
          ≤ (x * h1 ^ 2).natAbs + (y * h2 ^ 2).natAbs := Int.natAbs_sub_le _ _
        _ ≤ r * X ^ 2 + r * Y ^ 2 := add_le_add hx1 hy1
        _ = M := by rw [hM]; ring
    change (((x * h1 ^ 2 - y * h2 ^ 2).natAbs.divisors.card : ℝ)) ^ 4
        ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
            (256 * ((d.divisors.card : ℝ)) ^ 8)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0)
    by_cases hm0 : (x * h1 ^ 2 - y * h2 ^ 2).natAbs = 0
    · have hz : ((x * h1 ^ 2 - y * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4 = 0 := by
        rw [hm0]; simp
      rw [hz]
      apply Finset.sum_nonneg; intro d _
      split_ifs <;> positivity
    · have hm1 : 1 ≤ (x * h1 ^ 2 - y * h2 ^ 2).natAbs := Nat.one_le_iff_ne_zero.mpr hm0
      have hzz : (x * h1 ^ 2 - y * h2 ^ 2) ≠ 0 := fun h => hm0 ((Int.natAbs_eq_zero).mpr h)
      have hb := tau4_le_sum_indicators' (m := (x * h1 ^ 2 - y * h2 ^ 2).natAbs) (M := M) hm1 hmM
      refine hb.trans ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro d _
      by_cases hd : d ∣ (x * h1 ^ 2 - y * h2 ^ 2).natAbs
      · have hc : (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0 :=
          ⟨(Int.natCast_dvd).mpr hd, hzz⟩
        rw [if_pos hd, if_pos hc]
        exact le_of_eq (by ring)
      · have hc : ¬ ((d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0) := by
          rintro ⟨h1', _⟩
          exact hd ((Int.natCast_dvd).mp h1')
        rw [if_neg hd, if_neg hc]
        exact le_of_eq (by ring)
  have hstep1 : Work.FIArea2.R6.uboxSum r X Y
      = ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 x y h1 h2 := rfl
  have hstep2 : (∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 x y h1 h2)
      ≤ ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
          ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
            (256 * ((d.divisors.card : ℝ)) ^ 8)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum; intro x hx
    apply Finset.sum_le_sum; intro y hy
    apply Finset.sum_le_sum; intro h1 hh1
    apply Finset.sum_le_sum; intro h2 hh2
    exact key x hx y hy h1 hh1 h2 hh2
  have hstep3 : (∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
          ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
            (256 * ((d.divisors.card : ℝ)) ^ 8)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0))
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), ∑ x ∈ zPz r, ∑ y ∈ zPz r,
          ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            (256 * ((d.divisors.card : ℝ)) ^ 8)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0) :=
    sum4_sum_comm _
  have hstep4 : (∑ d ∈ Finset.Icc 1 (Nat.sqrt M), ∑ x ∈ zPz r, ∑ y ∈ zPz r,
          ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            (256 * ((d.divisors.card : ℝ)) ^ 8)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0))
      = 256 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
            ((d.divisors.card : ℝ)) ^ 8 * ndCount d r X Y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [pull_const4'' (256 * ((d.divisors.card : ℝ)) ^ 8)
      (fun x y h1 h2 => if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                          then (1 : ℝ) else 0)]
    have hsum : (∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
        (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
          then (1 : ℝ) else 0)) = ndCount d r X Y := rfl
    rw [hsum]; ring
  calc Work.FIArea2.R6.uboxSum r X Y
      = ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 x y h1 h2 := hstep1
    _ ≤ _ := hstep2
    _ = _ := hstep3
    _ = _ := hstep4

end

end Work.FIArea2.R6
