import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Bump4
import Submission.Work.FITop4.Bump4.QuinticAux

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators
open Work.FITop4.Bump4

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

/-!
# The angular partition of unity (5.12)

Friedlander–Iwaniec use, on the circle of Gaussian-integer arguments, a `C²` partition of unity
`Σ_k q_k(α − φ_k) = 1` (`α ∈ [−π, π]`) subordinate to the sector `[0, 2πθ]`, with the derivative
bounds `|q_k^{(j)}| ≤ c_j θ^{−j}` (`j ≤ 2`).  The construction here is the elementary one: the
*tent* bump

  `tent W x = quinticStep (x/W) − quinticStep (x/W − 1)`

(the difference of two translates of the clamped quintic step of `Bump4`), supported in `[0, 2W]`,
taking values in `[0, 1]`, and satisfying `Σ_{k∈ℤ} tent W (x − kW) = 1` by telescoping.  Restricting
to the finitely many translates meeting `[−π, π]` (at most `4/θ + 4` of them) gives the statement.
-/

/-- The tent bump of width `2W`: `quinticStep (x/W) − quinticStep (x/W − 1)`, supported in `[0,2W]`,
with `tent W W = 1` and `tent W ∈ [0,1]`. -/
def tent (W : ℝ) : ℝ → ℝ := fun x => quinticStep (x / W) - quinticStep (x / W - 1)

lemma tent_contDiff (W : ℝ) : ContDiff ℝ 2 (tent W) := by
  unfold tent
  have h1 : ContDiff ℝ 2 (fun x : ℝ => quinticStep (x / W)) :=
    contDiff_quinticStep.comp (by fun_prop)
  have h2 : ContDiff ℝ 2 (fun x : ℝ => quinticStep (x / W - 1)) :=
    contDiff_quinticStep.comp (by fun_prop)
  exact h1.sub h2

lemma tent_nonneg (W : ℝ) (x : ℝ) : 0 ≤ tent W x := by
  unfold tent
  rcases le_or_gt (x / W) 0 with h1 | h1
  · rw [quinticStep_eq_zero_of_nonpos _ h1, quinticStep_eq_zero_of_nonpos _ (by linarith)]
    norm_num
  · rcases le_or_gt 1 (x / W) with h2 | h2
    · rw [quinticStep_eq_one_of_one_le _ h2]
      linarith [quinticStep_le_one (x / W - 1)]
    · rw [quinticStep_eq_zero_of_nonpos _ (by linarith : x / W - 1 ≤ 0)]
      linarith [quinticStep_nonneg (x / W)]

lemma tent_le_one (W : ℝ) (x : ℝ) : tent W x ≤ 1 := by
  unfold tent
  rcases le_or_gt (x / W) 0 with h1 | h1
  · rw [quinticStep_eq_zero_of_nonpos _ h1, quinticStep_eq_zero_of_nonpos _ (by linarith)]
    norm_num
  · rcases le_or_gt 1 (x / W) with h2 | h2
    · rw [quinticStep_eq_one_of_one_le _ h2]
      linarith [quinticStep_nonneg (x / W - 1)]
    · rw [quinticStep_eq_zero_of_nonpos _ (by linarith : x / W - 1 ≤ 0)]
      linarith [quinticStep_le_one (x / W)]

lemma tent_eq_zero_of_nonpos (W : ℝ) (hW : 0 < W) {x : ℝ} (hx : x ≤ 0) : tent W x = 0 := by
  unfold tent
  have hu : x / W ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx hW.le
  rw [quinticStep_eq_zero_of_nonpos _ hu, quinticStep_eq_zero_of_nonpos _ (by linarith)]
  ring

lemma tent_eq_zero_of_le (W : ℝ) (hW : 0 < W) {x : ℝ} (hx : 2 * W ≤ x) : tent W x = 0 := by
  unfold tent
  have hu : 1 ≤ x / W - 1 := by
    rw [div_sub_one (ne_of_gt hW)]
    exact (le_div_iff₀ hW).mpr (by linarith)
  have hu2 : 1 ≤ x / W := (le_div_iff₀ hW).mpr (by linarith)
  rw [quinticStep_eq_one_of_one_le _ hu2, quinticStep_eq_one_of_one_le _ hu]
  ring

lemma tent_support (W : ℝ) (hW : 0 < W) {x : ℝ} (h : tent W x ≠ 0) :
    0 ≤ x ∧ x ≤ 2 * W := by
  constructor
  · by_contra hx
    exact h (tent_eq_zero_of_nonpos W hW (not_le.mp hx).le)
  · by_contra hx
    exact h (tent_eq_zero_of_le W hW (not_le.mp hx).le)

lemma tent_hasDerivAt (W t : ℝ) :
    HasDerivAt (tent W) ((qstep1 (t / W) - qstep1 (t / W - 1)) * (1 / W)) t := by
  have hg : HasDerivAt (fun x : ℝ => x / W) (1 / W) t := by
    simpa using (hasDerivAt_id t).div_const W
  have hg2 : HasDerivAt (fun x : ℝ => x / W - 1) (1 / W) t := by
    simpa using hg.sub_const 1
  have h1 : HasDerivAt (fun x : ℝ => quinticStep (x / W)) (qstep1 (t / W) * (1 / W)) t := by
    have := (quinticStep_hasDerivAt (t / W)).comp t hg
    convert this using 1 <;> first | rfl | (ext s; rfl)
  have h2 : HasDerivAt (fun x : ℝ => quinticStep (x / W - 1))
      (qstep1 (t / W - 1) * (1 / W)) t := by
    have := (quinticStep_hasDerivAt (t / W - 1)).comp t hg2
    convert this using 1 <;> first | rfl | (ext s; rfl)
  have h := h1.sub h2
  unfold tent
  convert h using 1 <;> first | rfl | ring

lemma tent_deriv (W t : ℝ) :
    deriv (tent W) t = (qstep1 (t / W) - qstep1 (t / W - 1)) * (1 / W) :=
  (tent_hasDerivAt W t).deriv

lemma tent_hasDerivAt' (W t : ℝ) :
    HasDerivAt (fun x : ℝ => (qstep1 (x / W) - qstep1 (x / W - 1)) * (1 / W))
      ((qstep2 (t / W) - qstep2 (t / W - 1)) * (1 / W) * (1 / W)) t := by
  have hg : HasDerivAt (fun x : ℝ => x / W) (1 / W) t := by
    simpa using (hasDerivAt_id t).div_const W
  have hg2 : HasDerivAt (fun x : ℝ => x / W - 1) (1 / W) t := by
    simpa using hg.sub_const 1
  have h1 : HasDerivAt (fun x : ℝ => qstep1 (x / W)) (qstep2 (t / W) * (1 / W)) t := by
    have := (qstep1_hasDerivAt (t / W)).comp t hg
    convert this using 1 <;> first | rfl | (ext s; rfl)
  have h2 : HasDerivAt (fun x : ℝ => qstep1 (x / W - 1))
      (qstep2 (t / W - 1) * (1 / W)) t := by
    have := (qstep1_hasDerivAt (t / W - 1)).comp t hg2
    convert this using 1 <;> first | rfl | (ext s; rfl)
  have h := (h1.sub h2).mul_const (1 / W)
  convert h using 1 <;> first | rfl | ring

lemma tent_deriv2 (W t : ℝ) :
    deriv (deriv (tent W)) t = (qstep2 (t / W) - qstep2 (t / W - 1)) * (1 / W) * (1 / W) := by
  have hd1 : deriv (tent W) = fun x : ℝ => (qstep1 (x / W) - qstep1 (x / W - 1)) * (1 / W) :=
    funext (tent_deriv W)
  rw [hd1]
  exact (tent_hasDerivAt' W t).deriv

lemma abs_iteratedDeriv_one_tent_le (W : ℝ) (hW : 0 < W) (t : ℝ) :
    |iteratedDeriv 1 (tent W) t| ≤ 4 / W := by
  have hval : iteratedDeriv 1 (tent W) t
      = (qstep1 (t / W) - qstep1 (t / W - 1)) * (1 / W) := by
    rw [iteratedDeriv_one, tent_deriv]
  rw [hval, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / W)]
  have hsub : |qstep1 (t / W) - qstep1 (t / W - 1)| ≤ 4 := by
    calc |qstep1 (t / W) - qstep1 (t / W - 1)|
        ≤ |qstep1 (t / W)| + |qstep1 (t / W - 1)| := abs_sub _ _
      _ ≤ 2 + 2 := add_le_add (abs_qstep1_le _) (abs_qstep1_le _)
      _ = 4 := by norm_num
  calc |qstep1 (t / W) - qstep1 (t / W - 1)| * (1 / W)
      ≤ 4 * (1 / W) := mul_le_mul_of_nonneg_right hsub (by positivity)
    _ = 4 / W := by ring

lemma abs_iteratedDeriv_two_tent_le (W : ℝ) (hW : 0 < W) (t : ℝ) :
    |iteratedDeriv 2 (tent W) t| ≤ 12 / W ^ 2 := by
  have hval : iteratedDeriv 2 (tent W) t
      = (qstep2 (t / W) - qstep2 (t / W - 1)) * (1 / W ^ 2) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, tent_deriv2]
    ring
  rw [hval, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / W ^ 2)]
  have hsub : |qstep2 (t / W) - qstep2 (t / W - 1)| ≤ 12 := by
    calc |qstep2 (t / W) - qstep2 (t / W - 1)|
        ≤ |qstep2 (t / W)| + |qstep2 (t / W - 1)| := abs_sub _ _
      _ ≤ 6 + 6 := add_le_add (abs_qstep2_le _) (abs_qstep2_le _)
      _ = 12 := by norm_num
  calc |qstep2 (t / W) - qstep2 (t / W - 1)| * (1 / W ^ 2)
      ≤ 12 * (1 / W ^ 2) := mul_le_mul_of_nonneg_right hsub (by positivity)
    _ = 12 / W ^ 2 := by ring

lemma cMoll_one : cMoll 1 = 1024 := by unfold cMoll; norm_num

lemma cMoll_two : cMoll 2 = (2:ℝ) ^ (20:ℕ) := by unfold cMoll; norm_num

lemma sum_range_telescope (F : ℕ → ℝ) (n : ℕ) :
    ∑ i in Finset.range n, (F i - F (i + 1)) = F 0 - F n := by
  have h := Finset.sum_range_sub F n
  have h2 : ∑ i in Finset.range n, (F i - F (i + 1))
      = -∑ i in Finset.range n, (F (i + 1) - F i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h2, h]; ring

theorem angular_partition_le (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ (K : ℕ) (φ : Fin K → ℝ) (q : Fin K → ℝ → ℝ),
      (∀ k, ContDiff ℝ 2 (q k)) ∧
      (∀ k α, 0 ≤ q k α) ∧ (∀ k α, q k α ≤ 1) ∧
      (∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) ∧
      (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) ∧
      (∀ k j, j ≤ 2 → ∀ α,
        |iteratedDeriv j (q k) α| ≤ cMoll j * θ ^ (-(j : ℝ))) ∧
      ((K : ℝ) ≤ 4 / θ + 4) := by
  have hWpos : 0 < Real.pi * θ := by positivity
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  refine ⟨Nat.ceil (2 / θ) + 1,
    (fun k => -(Real.pi * (1 + θ)) + ((k : ℕ) : ℝ) * (Real.pi * θ)),
    (fun _ x => tent (Real.pi * θ) x), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact tent_contDiff _
  · intro k α; exact tent_nonneg _ _
  · intro k α; exact tent_le_one _ _
  · intro k α h
    obtain ⟨h1, h2⟩ := tent_support (Real.pi * θ) hWpos h
    exact ⟨h1, h2.trans (le_of_eq (by ring))⟩
  · intro α hlo hhi
    set t : ℝ := (α + Real.pi + Real.pi * θ) / (Real.pi * θ) with ht
    rw [Fin.sum_univ_eq_sum_range
      (fun i => tent (Real.pi * θ) (α - (-(Real.pi * (1 + θ)) + (i : ℝ) * (Real.pi * θ))))]
    have hterm : ∀ i : ℕ, tent (Real.pi * θ) (α - (-(Real.pi * (1 + θ)) + (i : ℝ) * (Real.pi * θ)))
        = (fun m : ℕ => quinticStep (t - m)) i - (fun m : ℕ => quinticStep (t - m)) (i + 1) := by
      intro i
      unfold tent
      have h1 : (α - (-(Real.pi * (1 + θ)) + (i : ℝ) * (Real.pi * θ))) / (Real.pi * θ) = t - i := by
        rw [ht]; field_simp; ring
      have h2 : (α - (-(Real.pi * (1 + θ)) + (i : ℝ) * (Real.pi * θ))) / (Real.pi * θ) - 1
          = t - (i + 1) := by
        rw [ht]; push_cast; field_simp; ring
      rw [h2, h1]
      simp only [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    have htel := sum_range_telescope (fun m : ℕ => quinticStep (t - m)) (Nat.ceil (2 / θ) + 1)
    rw [htel]
    have ht1 : 1 ≤ t := by
      rw [ht, le_div_iff₀ hWpos]
      nlinarith [Real.pi_pos, hlo]
    have htK : t - ((Nat.ceil (2 / θ) + 1 : ℕ) : ℝ) ≤ 0 := by
      have hceil : (2 : ℝ) / θ ≤ (Nat.ceil (2 / θ) : ℝ) := Nat.le_ceil _
      have htle : t ≤ 2 / θ + 1 := by
        rw [ht, div_le_iff₀ hWpos]
        have he : (2 / θ + 1) * (Real.pi * θ) = 2 * Real.pi + Real.pi * θ := by field_simp
        rw [he]; linarith
      push_cast
      linarith
    have h0 : t - ((0 : ℕ) : ℝ) = t := by norm_num
    rw [h0, quinticStep_eq_one_of_one_le _ ht1, quinticStep_eq_zero_of_nonpos _ htK]
    ring
  · intro k j hj α
    interval_cases j
    · rw [iteratedDeriv_zero, cMoll_zero, abs_of_nonneg (tent_nonneg _ α)]
      simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
      exact tent_le_one _ α
    · calc |iteratedDeriv 1 (tent (Real.pi * θ)) α| ≤ 4 / (Real.pi * θ) :=
            abs_iteratedDeriv_one_tent_le _ hWpos α
        _ ≤ cMoll 1 * θ ^ (-((1 : ℕ) : ℝ)) := by
            have h4pi : (4 : ℝ) / Real.pi ≤ 1024 := by
              rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
            calc (4 : ℝ) / (Real.pi * θ) = (4 / Real.pi) * (1 / θ) := by field_simp
              _ ≤ 1024 * (1 / θ) := mul_le_mul_of_nonneg_right h4pi (by positivity)
              _ = cMoll 1 * θ ^ (-((1 : ℕ) : ℝ)) := by
                    rw [cMoll_one]; norm_num [Real.rpow_neg_one]
    · calc |iteratedDeriv 2 (tent (Real.pi * θ)) α| ≤ 12 / (Real.pi * θ) ^ 2 :=
            abs_iteratedDeriv_two_tent_le _ hWpos α
        _ ≤ cMoll 2 * θ ^ (-((2 : ℕ) : ℝ)) := by
            have h12pi : (12 : ℝ) / Real.pi ^ 2 ≤ (2 : ℝ) ^ 20 := by
              rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
              nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
            have hrpow : θ ^ (-((2 : ℕ) : ℝ)) = 1 / θ ^ 2 := by
              rw [show -(((2 : ℕ)) : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hθ0.le 2,
                  show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_eq_one_div]
            calc (12 : ℝ) / (Real.pi * θ) ^ 2 = ((12 / Real.pi ^ 2)) * (1 / θ ^ 2) := by field_simp
              _ ≤ (2 : ℝ) ^ 20 * (1 / θ ^ 2) := mul_le_mul_of_nonneg_right h12pi (by positivity)
              _ = cMoll 2 * θ ^ (-((2 : ℕ) : ℝ)) := by rw [cMoll_two, hrpow]
  · have hceil : ((Nat.ceil (2 / θ) : ℕ) : ℝ) ≤ 2 / θ + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have h2θ : (2 : ℝ) / θ ≤ 4 / θ := div_le_div_of_nonneg_right (by norm_num) hθ0.le
    push_cast
    linarith

end

end Work.FITop4.Red5
