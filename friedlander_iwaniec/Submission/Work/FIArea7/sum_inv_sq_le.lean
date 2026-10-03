import Mathlib
import Submission.Commons.Analysis.Series.tail_inv_sq_le
import Submission.Commons.Analysis.Series.tail_inv_sq_summable

namespace Work.FIArea7

/-- For a finset `A` of naturals all `≥ N`, the finite sum of `1/a²` is dominated by the
full (infinite) tail `∑' n, [N ≤ n] / n²`. -/
private lemma sum_inv_sq_le_tsum_tail (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, N ≤ a) :
    ∑ a ∈ A, (1:ℝ)/(a:ℝ)^2
      ≤ ∑' n : ℕ, (if N ≤ n then (1:ℝ)/(n:ℝ)^2 else 0) := by
  calc ∑ a ∈ A, (1:ℝ)/(a:ℝ)^2
      = ∑ a ∈ A, (if N ≤ a then (1:ℝ)/(a:ℝ)^2 else 0) :=
        Finset.sum_congr rfl (fun a ha => by rw [if_pos (hA a ha)])
    _ ≤ ∑' n : ℕ, (if N ≤ n then (1:ℝ)/(n:ℝ)^2 else 0) :=
        Summable.sum_le_tsum A (fun n _ => by split <;> positivity)
          (Commons.Analysis.Series.tail_inv_sq_summable N)

/-- `k ↦ |k|` is injective on a set of positive integers. -/
private lemma natAbs_injOn_pos (P : Finset ℤ) (hP : ∀ k ∈ P, 0 < k) :
    Set.InjOn (fun k : ℤ => k.natAbs) (P : Set ℤ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  rw [Int.natAbs_eq_natAbs_iff] at hab
  rcases hab with h | h
  · exact h
  · exfalso
    have ha' : 0 < a := hP a ha
    rw [h] at ha'
    have hb' : 0 < b := hP b hb
    omega

/-- `k ↦ |k|` is injective on a set of negative integers. -/
private lemma natAbs_injOn_neg (P : Finset ℤ) (hP : ∀ k ∈ P, k < 0) :
    Set.InjOn (fun k : ℤ => k.natAbs) (P : Set ℤ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  rw [Int.natAbs_eq_natAbs_iff] at hab
  rcases hab with h | h
  · exact h
  · exfalso
    have ha' : a < 0 := hP a ha
    rw [h] at ha'
    have hb' : b < 0 := hP b hb
    omega

/-- If `k ↦ |k|` is injective on `P ⊆ ℤ` and every `k ∈ P` has `R + 1 ≤ |k|`, then
`∑_{k∈P} 1/k² ≤ 2/(2R+1)`. -/
private lemma sum_inv_sq_le_of_inj (R : ℕ) (P : Finset ℤ)
    (hinj : Set.InjOn (fun k : ℤ => k.natAbs) (P : Set ℤ))
    (hP : ∀ k ∈ P, R + 1 ≤ k.natAbs) :
    ∑ k ∈ P, (1:ℝ)/(k:ℝ)^2 ≤ 2/(2*(R:ℝ)+1) := by
  have hcast : ∀ k : ℤ, (1:ℝ)/(k:ℝ)^2 = (1:ℝ)/(((k.natAbs:ℕ):ℝ))^2 := by
    intro k
    rw [show ((k.natAbs:ℕ):ℝ) = |(k:ℝ)| by rw [← Int.cast_abs]; norm_num, sq_abs]
  calc ∑ k ∈ P, (1:ℝ)/(k:ℝ)^2
      = ∑ k ∈ P, (1:ℝ)/(((k.natAbs:ℕ):ℝ))^2 := Finset.sum_congr rfl (fun k _ => hcast k)
    _ = ∑ n ∈ P.image (fun k : ℤ => k.natAbs), (1:ℝ)/(n:ℝ)^2 :=
        (Finset.sum_image (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2)
          (g := fun k : ℤ => k.natAbs) hinj).symm
    _ ≤ ∑' n : ℕ, (if R+1 ≤ n then (1:ℝ)/(n:ℝ)^2 else 0) :=
        sum_inv_sq_le_tsum_tail (R+1) _ (fun n hn => by
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
          exact hP k hk)
    _ ≤ 2/(2*(R:ℝ)+1) := by
        have h := Commons.Analysis.Series.tail_inv_sq_le (R+1) (by omega)
        have hc : (2:ℝ) * (((R+1 : ℕ)) : ℝ) - 1 = 2*(R:ℝ)+1 := by push_cast; ring
        rwa [hc] at h

theorem sum_inv_sq_le (R : ℕ) (hR : 1 ≤ R) (T : Finset ℤ)
    (hT : ∀ k ∈ T, (R : ℝ) < |(k : ℝ)|) :
    ∑ k ∈ T, 1 / (k : ℝ) ^ 2 ≤ 2 / (R : ℝ) := by
  have hcastabs : ∀ k : ℤ, ((k.natAbs : ℕ) : ℝ) = |(k:ℝ)| := by
    intro k; rw [← Int.cast_abs]; norm_num
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  rw [← Finset.sum_filter_add_sum_filter_not T (fun k : ℤ => 0 < k)
        (fun k => (1:ℝ)/(k:ℝ)^2)]
  set P : Finset ℤ := T.filter (fun k => 0 < k) with hPdef
  set Q : Finset ℤ := T.filter (fun k => ¬ 0 < k) with hQdef
  have hPP : ∀ k ∈ P, R + 1 ≤ k.natAbs := by
    intro k hk
    rw [hPdef, Finset.mem_filter] at hk
    have h1 := hT k hk.1
    rw [← hcastabs k] at h1
    have h2 : R < k.natAbs := by exact_mod_cast h1
    omega
  have hPQ : ∀ k ∈ Q, R + 1 ≤ k.natAbs := by
    intro k hk
    rw [hQdef, Finset.mem_filter] at hk
    have h1 := hT k hk.1
    rw [← hcastabs k] at h1
    have h2 : R < k.natAbs := by exact_mod_cast h1
    omega
  have hQneg : ∀ k ∈ Q, k < 0 := by
    intro k hk
    rw [hQdef, Finset.mem_filter] at hk
    have hkne : k ≠ 0 := by
      intro h0
      have h1 := hT k hk.1
      rw [h0] at h1
      simp at h1
      linarith
    omega
  have hinjP : Set.InjOn (fun k : ℤ => k.natAbs) (P : Set ℤ) := by
    apply natAbs_injOn_pos
    intro k hk
    rw [hPdef, Finset.mem_filter] at hk
    exact hk.2
  have hinjQ : Set.InjOn (fun k : ℤ => k.natAbs) (Q : Set ℤ) := natAbs_injOn_neg Q hQneg
  have bP := sum_inv_sq_le_of_inj R P hinjP hPP
  have bQ := sum_inv_sq_le_of_inj R Q hinjQ hPQ
  have hfinal : (4:ℝ)/(2*(R:ℝ)+1) ≤ 2/(R:ℝ) := by
    have hpos : (0:ℝ) < R := by linarith
    have hpos2 : (0:ℝ) < 2*(R:ℝ)+1 := by linarith
    rw [div_le_div_iff₀ hpos2 hpos]
    nlinarith
  calc ∑ k ∈ P, (1:ℝ)/(k:ℝ)^2 + ∑ k ∈ Q, (1:ℝ)/(k:ℝ)^2
      ≤ 2/(2*(R:ℝ)+1) + 2/(2*(R:ℝ)+1) := add_le_add bP bQ
    _ = 4/(2*(R:ℝ)+1) := by ring
    _ ≤ 2/(R:ℝ) := hfinal

end Work.FIArea7
