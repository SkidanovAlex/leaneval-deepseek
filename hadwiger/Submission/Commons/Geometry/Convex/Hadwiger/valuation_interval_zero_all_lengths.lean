import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Commons.Geometry.Convex.Hadwiger.interval_interior_empty_iff
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_interval_additive_length

open Set
open Metric

namespace Commons.Geometry.Convex.Hadwiger

/-- canonical interval body `[0, t]`, `0 ≤ t` -/
private noncomputable def intB (t : ℝ) (ht : 0 ≤ t) : ConvexBody ℝ := AuxVL.intervalBody 0 t ht

/-- Hausdorff distance between `[0,x]` and `[0,y]` is at most `|x - y|` (when `0 ≤ x, y`). -/
private lemma hausdorffDist_Icc_zero_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Metric.hausdorffDist (Set.Icc (0 : ℝ) x) (Set.Icc (0 : ℝ) y) ≤ |x - y| := by
  refine Metric.hausdorffDist_le_of_mem_dist (abs_nonneg _) ?_ ?_
  · intro z hz
    refine ⟨z, ?_, by rw [dist_self]; exact abs_nonneg _⟩
    rw [Set.mem_Icc] at hz ⊢
    exact ⟨hz.1, le_trans hz.2 hxy⟩
  · intro z hz
    rw [Set.mem_Icc] at hz
    by_cases hzx : z ≤ x
    · refine ⟨z, Set.mem_Icc.mpr ⟨hz.1, hzx⟩, by rw [dist_self]; exact abs_nonneg _⟩
    · have hxz : x ≤ z := le_of_not_ge hzx
      refine ⟨x, Set.mem_Icc.mpr ⟨hx, le_rfl⟩, ?_⟩
      have hzsub : z - x ≤ y - x := sub_le_sub_right hz.2 x
      have hxy_abs : |x - y| = y - x := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
      rw [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxz)]
      rw [hxy_abs]
      exact hzsub

private lemma hausdorffDist_Icc_zero (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Metric.hausdorffDist (Set.Icc (0 : ℝ) x) (Set.Icc (0 : ℝ) y) ≤ |x - y| := by
  rcases le_total x y with hxy | hyx
  · exact hausdorffDist_Icc_zero_le hx hxy
  · have hb := hausdorffDist_Icc_zero_le hy hyx
    rw [Metric.hausdorffDist_comm]
    simpa [abs_sub_comm y x] using hb

/-- The degenerate body `[0,0]` is empty-interior, hence zero. -/
private lemma zero_interval_zero (φ : ConvexBody ℝ → ℝ)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0) :
    φ (intB 0 (by norm_num : (0 : ℝ) ≤ 0)) = 0 := by
  refine hsimple (intB 0 (by norm_num)) ?_
  change interior (Set.Icc (0 : ℝ) 0 : Set ℝ) = ∅
  rw [interior_Icc]
  simp

/-- The unit interval `[0,1]` is zero. -/
private lemma unit_interval_zero (φ : ConvexBody ℝ → ℝ)
    (hunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc 0 1 → φ U = 0) :
    φ (intB 1 (by norm_num : (0 : ℝ) ≤ 1)) = 0 := by
  exact hunit (intB 1 (by norm_num)) (by simp [intB])

/-- Natural lengths are zero: `φ [0, n] = 0`. -/
private lemma nat_length_zero (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    (hunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc 0 1 → φ U = 0) :
    ∀ n : ℕ, φ (intB (n : ℝ) (Nat.cast_nonneg n)) = 0 := by
  intro n
  induction n with
  | zero =>
      simpa using (zero_interval_zero φ hsimple)
  | succ n ih =>
      let h1 : 0 ≤ (1 : ℝ) := by norm_num
      have hKts : (intB ((n + 1 : ℕ) : ℝ) (Nat.cast_nonneg (n + 1)) : Set ℝ) =
          Set.Icc (0 : ℝ) ((n : ℝ) + 1) := by
        change Set.Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ) = Set.Icc (0 : ℝ) ((n : ℝ) + 1)
        rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num]
      have hsum := valuation_interval_additive_length φ hadd hsimple htrans
          (t := (n : ℝ)) (s := 1) (Nat.cast_nonneg n) h1
          (intB ((n + 1 : ℕ) : ℝ) (Nat.cast_nonneg (n + 1))) hKts
          (intB (n : ℝ) (Nat.cast_nonneg n)) (by simp [intB])
          (intB 1 h1) (by simp [intB])
      have hK1 : φ (intB 1 h1) = 0 := by
        have hu := unit_interval_zero φ hunit
        -- body with h1 equals body with `by norm_num`
        have hb : intB 1 h1 = intB 1 (by norm_num : (0 : ℝ) ≤ 1) := by
          apply ConvexBody.ext
          simp [intB]
        rwa [hb] at hu
      calc
        φ (intB ((n + 1 : ℕ) : ℝ) (Nat.cast_nonneg (n + 1))) = φ (intB (n : ℝ) (Nat.cast_nonneg n)) + φ (intB 1 h1) := hsum
        _ = 0 := by rw [ih, hK1, zero_add]

/-- Scaling: `φ [0, n·x] = n · φ [0, x]` for `0 ≤ x`, `n : ℕ`. -/
private lemma nat_scale (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    (x : ℝ) (hx : 0 ≤ x) :
    ∀ n : ℕ,
      φ (intB ((n : ℝ) * x) (mul_nonneg (Nat.cast_nonneg n) hx)) =
        (n : ℝ) * φ (intB x hx) := by
  intro n
  induction n with
  | zero =>
      calc
        φ (intB (((0 : ℕ) : ℝ) * x) (mul_nonneg (Nat.cast_nonneg 0) hx))
            = φ (intB (0 : ℝ) (by norm_num : (0 : ℝ) ≤ 0)) := by
          apply congrArg φ
          apply ConvexBody.ext
          simp [intB]
        _ = 0 := zero_interval_zero φ hsimple
        _ = ((0 : ℕ) : ℝ) * φ (intB x hx) := by norm_num
  | succ n ih =>
      let h1 : 0 ≤ (1 : ℝ) := by norm_num
      let hnx : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx
      have hKts : (intB (((n + 1 : ℕ) : ℝ) * x) (mul_nonneg (Nat.cast_nonneg (n + 1)) hx) : Set ℝ) =
          Set.Icc (0 : ℝ) ((n : ℝ) * x + x) := by
        change Set.Icc (0 : ℝ) (((n + 1 : ℕ) : ℝ) * x) = Set.Icc (0 : ℝ) ((n : ℝ) * x + x)
        rw [show (((n + 1 : ℕ) : ℝ) * x) = ((n : ℝ) * x + x) by
          rw [show (((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1) by norm_num]
          ring]
      have hsum := valuation_interval_additive_length φ hadd hsimple htrans
          (t := (n : ℝ) * x) (s := x) hnx hx
          (intB (((n + 1 : ℕ) : ℝ) * x) (mul_nonneg (Nat.cast_nonneg (n + 1)) hx)) hKts
          (intB ((n : ℝ) * x) hnx) (by simp [intB])
          (intB x hx) (by simp [intB])
      calc
        φ (intB (((n + 1 : ℕ) : ℝ) * x) (mul_nonneg (Nat.cast_nonneg (n + 1)) hx))
            = φ (intB ((n : ℝ) * x) hnx) + φ (intB x hx) := hsum
        _ = ((n : ℝ) * φ (intB x hx)) + φ (intB x hx) := by rw [ih]
        _ = ((n + 1 : ℕ) : ℝ) * φ (intB x hx) := by
          rw [show (((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1) by norm_num]
          ring

/-- Rational (real numerator/denominator) lengths are zero: `φ [0, a/n] = 0`. -/
private lemma rational_length_zero (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    (hunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc 0 1 → φ U = 0)
    (a n : ℕ) (hn : n ≠ 0) :
    φ (intB ((a : ℝ) / (n : ℝ)) (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg n))) = 0 := by
  let x : ℝ := (a : ℝ) / (n : ℝ)
  have hx : 0 ≤ x := div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg n)
  have hnnz : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsc := nat_scale φ hadd hsimple htrans x hx n
  have hprod : (n : ℝ) * x = (a : ℝ) := by
    dsimp [x]
    field_simp [hnnz]
  have hbody : intB ((n : ℝ) * x) (mul_nonneg (Nat.cast_nonneg n) hx) =
      intB (a : ℝ) (Nat.cast_nonneg a) := by
    apply ConvexBody.ext
    simp [intB, hprod]
  have hval : φ (intB ((n : ℝ) * x) (mul_nonneg (Nat.cast_nonneg n) hx)) = 0 := by
    rw [hbody, nat_length_zero φ hadd hsimple htrans hunit a]
  have hmul : (n : ℝ) * φ (intB x hx) = 0 := by
    rwa [← hsc]
  have hzero : φ (intB x hx) = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact False.elim (hnnz h)
    · exact h
  exact hzero

/-- `ℚ` rational lengths are zero. -/
private lemma rat_zero (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    (hunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc 0 1 → φ U = 0) :
    ∀ q : ℚ, (hq : 0 ≤ (q : ℝ)) → φ (intB (q : ℝ) hq) = 0 := by
  intro q hq
  have hqQ : 0 ≤ q := by exact_mod_cast hq
  have hnum : 0 ≤ q.num := (Rat.num_nonneg).2 hqQ
  let a : ℕ := q.num.toNat
  have ha : (a : ℤ) = q.num := by
    dsimp [a]
    exact Int.toNat_of_nonneg hnum
  have hqcast : (q : ℝ) = (a : ℝ) / (q.den : ℝ) := by
    calc
      (q : ℝ) = ((Rat.divInt q.num (q.den : ℤ)) : ℝ) := by
        rw [q.num_divInt_den]
      _ = (q.num : ℝ) / ((q.den : ℤ) : ℝ) := by rw [Rat.cast_divInt]
      _ = (q.num : ℝ) / (q.den : ℝ) := by
        rw [show ((q.den : ℤ) : ℝ) = (q.den : ℝ) by exact Int.cast_natCast q.den]
      _ = (a : ℝ) / (q.den : ℝ) := by
        have hnum_eq : (q.num : ℝ) = (a : ℝ) := by
          rw [← ha]
          exact Int.cast_natCast a
        rw [hnum_eq]
  have hz := rational_length_zero φ hadd hsimple htrans hunit a q.den (q.den_ne_zero)
  have hbody : intB (q : ℝ) hq = intB ((a : ℝ) / (q.den : ℝ)) (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg q.den)) := by
    apply ConvexBody.ext
    simp [intB, hqcast]
  rwa [hbody]

/-- Zero on nonneg rationals extends to zero at every positive length, by continuity. -/
private lemma real_interval_zero_of_rational
    (φ : ConvexBody ℝ → ℝ) (hcont : Continuous φ)
    (hrat : ∀ q : ℚ, (hq : 0 ≤ (q : ℝ)) → φ (intB (q : ℝ) hq) = 0)
    {t : ℝ} (ht : 0 < t) (K : ConvexBody ℝ) (hK : (K : Set ℝ) = Set.Icc 0 t) :
    φ K = 0 := by
  by_contra hne
  have hε : 0 < |φ K| / 2 := half_pos (abs_pos.mpr hne)
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.mp hcont.continuousAt) (|φ K| / 2) hε
  have htail : ∀ r : ℚ, 0 ≤ (r : ℝ) → |(r : ℝ) - t| < δ → False := by
    intro r hr hrd
    have hbdd := hausdorffDist_Icc_zero (r : ℝ) t hr (le_of_lt ht)
    have hQK : dist (intB (r : ℝ) hr) K < δ := by
      change Metric.hausdorffDist (intB (r : ℝ) hr : Set ℝ) (K : Set ℝ) < δ
      rw [hK]
      change Metric.hausdorffDist (Set.Icc (0 : ℝ) (r : ℝ)) (Set.Icc (0 : ℝ) t) < δ
      exact lt_of_le_of_lt hbdd hrd
    have hd2 : dist (φ (intB (r : ℝ) hr)) (φ K) < |φ K| / 2 := hclose hQK
    have hφKlt : |φ K| < |φ K| / 2 := by
      have : |φ K - 0| < |φ K| / 2 := by
        simpa [Real.dist_eq, hrat r hr] using hd2
      simpa using this
    nlinarith [abs_nonneg (φ K)]
  have hlt : t - δ < t + δ := by linarith
  obtain ⟨q, hqlow, hqhigh⟩ := exists_rat_btwn hlt
  by_cases hqneg : (q : ℝ) < 0
  · refine htail 0 (by norm_num) ?_
    have htltδ : t < δ := by linarith
    have hc : ((0 : ℚ) : ℝ) = 0 := by norm_num
    rw [hc, sub_eq_add_neg, zero_add, abs_neg, abs_of_pos ht]
    exact htltδ
  · refine htail q (le_of_not_gt hqneg) ?_
    rw [abs_lt]
    constructor <;> linarith

theorem valuation_interval_zero_all_lengths
    (φ : ConvexBody ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    (hunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc 0 1 → φ U = 0) :
    ∀ (t : ℝ) (ht : 0 ≤ t) (K : ConvexBody ℝ),
      (K : Set ℝ) = Set.Icc 0 t → φ K = 0 := by
  intro t ht K hK
  by_cases ht0 : t = 0
  · subst t
    have hint : interior (K : Set ℝ) = ∅ := by
      rw [hK]
      exact (interval_interior_empty_iff (le_rfl : (0 : ℝ) ≤ 0)).mpr rfl
    exact hsimple K hint
  · have htpos : 0 < t := lt_of_le_of_ne ht (by intro h; exact ht0 h.symm)
    have hrat := rat_zero φ hadd hsimple htrans hunit
    exact real_interval_zero_of_rational φ hcont hrat htpos K hK

end Commons.Geometry.Convex.Hadwiger