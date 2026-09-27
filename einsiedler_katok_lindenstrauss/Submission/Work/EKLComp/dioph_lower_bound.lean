import Mathlib
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLComp

open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

/-- `distToNearestInt x` vanishes exactly at the integers. -/
lemma distToNearestInt_eq_zero_iff (x : ℝ) :
    distToNearestInt x = 0 ↔ ∃ k : ℤ, x = k := by
  rw [distToNearestInt, abs_eq_zero, sub_eq_zero]
  constructor
  · rintro h; exact ⟨round x, h⟩
  · rintro ⟨k, rfl⟩; rw [round_intCast]

/-- `distToNearestInt` is positive exactly away from the integers. -/
lemma distToNearestInt_pos_iff (x : ℝ) :
    0 < distToNearestInt x ↔ ¬ ∃ k : ℤ, x = k := by
  rw [distToNearestInt, abs_pos]
  constructor
  · rintro h ⟨k, rfl⟩
    exact h (by rw [round_intCast, sub_self])
  · rintro h hx
    exact h ⟨round x, sub_eq_zero.mp hx⟩

/-- For irrational `u` and nonzero `n`, `n * u` is never an integer. -/
lemma irrational_natCast_mul_not_int {u : ℝ} (hu : Irrational u) {n : ℕ} (hn : n ≠ 0)
    (k : ℤ) : (n : ℝ) * u ≠ k := by
  rw [mul_comm]
  exact (hu.mul_natCast hn).ne_int k

/-- If the `liminf` of `n * ⟨nu⟩ * ⟨nv⟩` is positive then `u` is irrational. -/
lemma irrational_of_liminf_pos (u v : ℝ)
    (h : 0 < Filter.atTop.liminf (fun n : ℕ =>
      (n : ℝ) * distToNearestInt (n * u) * distToNearestInt (n * v))) :
    Irrational u := by
  by_contra hu
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hu
  set F : ℕ → ℝ := fun n => (n : ℝ) * distToNearestInt (n * u) * distToNearestInt (n * v)
    with hF
  have hlimF : 0 < Filter.atTop.liminf F := by rw [hF]; exact h
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hmul : (r.den : ℚ) * r = r.num := by
    have h' := Rat.num_div_den r
    rw [div_eq_iff hden] at h'
    rw [h']
    exact mul_comm _ _
  have hqu : (r.den : ℝ) * u = (r.num : ℝ) := by
    have h' := congrArg (fun x : ℚ => (x : ℝ)) hmul
    push_cast at h'
    rw [← hr] at h'
    exact h'
  have hFm_zero : ∀ m : ℕ, (∃ k : ℤ, (m : ℝ) * u = k) → F m = 0 := by
    intro m ⟨k, hk⟩
    have hm : distToNearestInt ((m : ℝ) * u) = 0 := (distToNearestInt_eq_zero_iff _).2 ⟨k, hk⟩
    show (m : ℝ) * distToNearestInt ((m : ℝ) * u) * distToNearestInt ((m : ℝ) * v) = 0
    rw [hm, mul_zero, zero_mul]
  have hfreq : ∃ᶠ n in Filter.atTop, F n ≤ 0 := by
    rw [Filter.frequently_atTop]
    intro a
    refine ⟨r.den * (a + 1), ?_, ?_⟩
    · calc a ≤ a + 1 := Nat.le_succ a
        _ = 1 * (a + 1) := by rw [one_mul]
        _ ≤ r.den * (a + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt r.den_pos)
    · have hm_int : ∃ k : ℤ, (((r.den * (a + 1) : ℕ)) : ℝ) * u = k := by
        refine ⟨(((a + 1 : ℕ) : ℤ) * r.num : ℤ), ?_⟩
        rw [Nat.cast_mul]
        calc ((r.den : ℝ) * ((a + 1 : ℕ) : ℝ)) * u
            = ((a + 1 : ℕ) : ℝ) * ((r.den : ℝ) * u) := by ring
          _ = ((a + 1 : ℕ) : ℝ) * (r.num : ℝ) := by rw [hqu]
          _ = ((((a + 1 : ℕ) : ℤ) * r.num : ℤ) : ℝ) := by push_cast; ring
      exact le_of_eq (hFm_zero _ hm_int)
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop F :=
    Filter.isBoundedUnder_of ⟨0, fun n => by
      rw [hF]
      have h1 : (0 : ℝ) ≤ distToNearestInt (n * u) := by rw [distToNearestInt]; exact abs_nonneg _
      have h2 : (0 : ℝ) ≤ distToNearestInt (n * v) := by rw [distToNearestInt]; exact abs_nonneg _
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) h1) h2⟩
  have hle0 : Filter.atTop.liminf F ≤ 0 :=
    Filter.liminf_le_of_frequently_le (f := Filter.atTop) (u := F) (a := 0) hfreq hbdd
  linarith

theorem dioph_lower_bound (u v : ℝ)
    (h : 0 < Filter.atTop.liminf
      (fun n : ℕ ↦ (n : ℝ) * LeanEval.Dynamics.EinsiedlerKatokLindenstrauss.distToNearestInt (n * u)
        * LeanEval.Dynamics.EinsiedlerKatokLindenstrauss.distToNearestInt (n * v))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 1 ≤ n →
      δ ≤ (n : ℝ) * LeanEval.Dynamics.EinsiedlerKatokLindenstrauss.distToNearestInt (n * u)
        * LeanEval.Dynamics.EinsiedlerKatokLindenstrauss.distToNearestInt (n * v) := by
  set F : ℕ → ℝ := fun n => (n : ℝ) * distToNearestInt (n * u) * distToNearestInt (n * v)
    with hF
  have hlimF : 0 < Filter.atTop.liminf F := by rw [hF]; exact h
  have hiu : Irrational u := irrational_of_liminf_pos u v h
  have hiv : Irrational v := by
    apply irrational_of_liminf_pos v u
    have heq : (fun n : ℕ => (n : ℝ) * distToNearestInt (n * v) * distToNearestInt (n * u))
        = (fun n : ℕ => (n : ℝ) * distToNearestInt (n * u) * distToNearestInt (n * v)) := by
      funext n; ring
    rw [heq]; exact h
  have hpos : ∀ n : ℕ, 1 ≤ n → 0 < F n := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hdu : 0 < distToNearestInt (n * u) := by
      rw [distToNearestInt_pos_iff]
      rintro ⟨k, hk⟩
      exact irrational_natCast_mul_not_int hiu hn0 k hk
    have hdv : 0 < distToNearestInt (n * v) := by
      rw [distToNearestInt_pos_iff]
      rintro ⟨k, hk⟩
      exact irrational_natCast_mul_not_int hiv hn0 k hk
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    rw [hF]
    exact mul_pos (mul_pos hnpos hdu) hdv
  have hFnn : ∀ n, 0 ≤ F n := by
    intro n
    rw [hF]
    have h1 : (0 : ℝ) ≤ distToNearestInt (n * u) := by rw [distToNearestInt]; exact abs_nonneg _
    have h2 : (0 : ℝ) ≤ distToNearestInt (n * v) := by rw [distToNearestInt]; exact abs_nonneg _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) h1) h2
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop F :=
    Filter.isBoundedUnder_of ⟨0, hFnn⟩
  have hev : ∀ᶠ n in Filter.atTop, Filter.atTop.liminf F / 2 < F n :=
    Filter.eventually_lt_of_lt_liminf (f := Filter.atTop) (u := F)
      (b := Filter.atTop.liminf F / 2) (by linarith) hbdd
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hSne : (Finset.Icc 1 (max N 1)).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, le_max_right _ _⟩⟩
  refine ⟨min (Filter.atTop.liminf F / 2) ((Finset.Icc 1 (max N 1)).inf' hSne F), ?_, ?_⟩
  · apply lt_min
    · linarith
    · rw [Finset.lt_inf'_iff hSne]
      intro n hn
      exact hpos n (Finset.mem_Icc.mp hn).1
  · intro n hn1
    by_cases hnS : n ∈ Finset.Icc 1 (max N 1)
    · exact le_trans (min_le_right _ _) (Finset.inf'_le F hnS)
    · have hgt : max N 1 < n := by
        by_contra hle
        exact hnS (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt hle⟩)
      have hNle : N ≤ n := le_trans (le_max_left N 1) (le_of_lt hgt)
      exact le_trans (min_le_left _ _) (le_of_lt (hN n hNle))

end Work.EKLComp
