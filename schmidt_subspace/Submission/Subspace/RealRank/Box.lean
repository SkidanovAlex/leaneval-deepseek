import Mathlib
import Submission.Commons.GeometryOfNumbers.Box.box_rank_eq_card_successiveMinimum
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.exists_gap_index
import Submission.Commons.Analysis.Normed.intVec_norm_le_sum_forms

/-!
# The approximation box, its rank and its successive minima

For a system of `N` linear forms `L : Fin N → Fin N → ℂ` in `N` variables, exponents
`c : Fin N → ℝ` and a scale `Q ≥ 1`, we consider the boxes

`boxT L c Q t = {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}`

and their `ℚ`-rank `rankT L c Q t` (the dimension of the span of the image in `ℚ^N`).  The
successive minima are

`lamS L c Q j = sInf {t ≥ 0 | j + 1 ≤ rankT L c Q t}`.

This file collects the elementary properties needed for the rank descent over `ℝ`: monotonicity
and positivity of the minima, the dictionary "`rankT t` = number of minima `≤ t`"
(`Commons.GeometryOfNumbers.Box.box_rank_eq_card_successiveMinimum`), and the existence of a gap
index (`Commons.GeometryOfNumbers.SuccessiveMinima.exists_gap_index`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Submission.Subspace.RealRank

variable {N : ℕ}

/-- The approximation box at scale `t`: integer points whose form values are bounded by
`t * Q ^ (c i)`. -/
def boxT (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) (Q t : ℝ) : Set (Fin N → ℤ) :=
  {y | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}

/-- The image of the box in `ℚ^N`. -/
def boxTQ (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) (Q t : ℝ) : Set (Fin N → ℚ) :=
  Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ)) (boxT L c Q t)

/-- The `ℚ`-rank of the box at scale `t`. -/
noncomputable def rankT (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) (Q t : ℝ) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ (boxTQ L c Q t))

/-- The successive minima of the box. -/
noncomputable def lamS (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) (Q : ℝ) (j : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ rankT L c Q t}

/-- The box is monotone in the scale, for `Q ≥ 1`. -/
lemma boxT_mono (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) {Q : ℝ} (hQ : 1 ≤ Q)
    {t t' : ℝ} (htt : t ≤ t') : boxT L c Q t ⊆ boxT L c Q t' := by
  intro y hy i
  have hQc : 0 ≤ Q ^ (c i) := Real.rpow_nonneg (le_trans zero_le_one hQ) _
  calc ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i) := hy i
    _ ≤ t' * Q ^ (c i) := mul_le_mul_of_nonneg_right htt hQc

lemma rankT_mono (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) {Q : ℝ} (hQ : 1 ≤ Q)
    {t t' : ℝ} (htt : t ≤ t') : rankT L c Q t ≤ rankT L c Q t' := by
  unfold rankT
  exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (boxT_mono L c hQ htt)))

lemma rankT_le (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) (Q t : ℝ) : rankT L c Q t ≤ N := by
  unfold rankT
  calc Module.finrank ℚ (Submodule.span ℚ (boxTQ L c Q t)) ≤
        Module.finrank ℚ (⊤ : Submodule ℚ (Fin N → ℚ)) := Submodule.finrank_mono le_top
    _ = N := by rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The box at scale `0` is trivial, for an invertible system. -/
lemma boxT_zero (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0) (c : Fin N → ℝ)
    (Q : ℝ) : boxT L c Q 0 = {0} := by
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · intro i
    simp
  · intro y hy
    have h1 : ∀ i, ∑ k, L i k * (y k : ℂ) = 0 := by
      intro i
      have h2 : ‖∑ k, L i k * (y k : ℂ)‖ ≤ 0 := by
        have := hy i
        simpa using this
      exact norm_eq_zero.mp (le_antisymm h2 (norm_nonneg _))
    have hz : (Matrix.of L).mulVec (fun k => (y k : ℂ)) = 0 := by
      funext i
      simpa [Matrix.mulVec, dotProduct] using h1 i
    have hmap : IsUnit (Matrix.of L) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hinj := (Matrix.mulVec_injective_iff_isUnit).mpr hmap
    have hz' : (Matrix.of L).mulVec (fun k => (y k : ℂ)) =
        (Matrix.of L).mulVec (0 : Fin N → ℂ) := by
      rw [hz]
      funext k
      simp [Matrix.mulVec]
    have h0 : (fun k => (y k : ℂ)) = 0 := hinj hz'
    funext k
    have hk : ((y k : ℤ) : ℂ) = 0 := congrFun h0 k
    have hk' : (y k : ℤ) = 0 := by exact_mod_cast hk
    simp [hk']

lemma rankT_zero (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0) (c : Fin N → ℝ)
    (Q : ℝ) : rankT L c Q 0 = 0 := by
  have himg : Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
      (boxT L c Q 0) = {0} := by
    rw [boxT_zero L hdet c Q, Set.image_singleton]
    congr 1
  unfold rankT boxTQ
  rw [himg]
  simp

/-- For large `t` the box contains all the unit vectors, hence has full rank. -/
lemma rankT_large (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ∃ t₁ : ℝ, 0 ≤ t₁ ∧ ∀ t : ℝ, t₁ ≤ t → rankT L c Q t = N := by
  classical
  set t₁ : ℝ := ∑ p : Fin N × Fin N, (‖L p.1 p.2‖ + 1) * (Q ^ (-(c p.1)) + 1) with ht₁
  have ht₁0 : 0 ≤ t₁ := by
    rw [ht₁]; exact Finset.sum_nonneg fun p _ => by positivity
  have hQci : ∀ i : Fin N, 0 < Q ^ (c i) := fun i => Real.rpow_pos_of_pos hQ _
  have hQneg : ∀ i : Fin N, Q ^ (-(c i)) * Q ^ (c i) = 1 := by
    intro i
    rw [← Real.rpow_add hQ, neg_add_cancel, Real.rpow_zero]
  have hmem : ∀ (t : ℝ), t₁ ≤ t → ∀ j : Fin N, Pi.single j (1 : ℤ) ∈ boxT L c Q t := by
    intro t ht j i
    have h1 : (∑ k, L i k * ((Pi.single j (1 : ℤ) : Fin N → ℤ) k : ℂ)) = L i j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb]
        simp
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [h1]
    have h2 : ‖L i j‖ * (Q ^ (-(c i)) + 1) ≤ t₁ := by
      have h3 : (‖L i j‖ + 1) * (Q ^ (-(c i)) + 1)
          ≤ ∑ p : Fin N × Fin N, (‖L p.1 p.2‖ + 1) * (Q ^ (-(c p.1)) + 1) :=
        Finset.single_le_sum (f := fun p : Fin N × Fin N =>
          (‖L p.1 p.2‖ + 1) * (Q ^ (-(c p.1)) + 1))
          (fun p _ => by positivity) (Finset.mem_univ (i, j))
      have h4 : ‖L i j‖ * (Q ^ (-(c i)) + 1) ≤ (‖L i j‖ + 1) * (Q ^ (-(c i)) + 1) := by
        nlinarith [norm_nonneg (L i j), Real.rpow_pos_of_pos hQ (-(c i))]
      linarith [ht₁ ▸ h3]
    have h4 : t₁ * Q ^ (c i) ≤ t * Q ^ (c i) :=
      mul_le_mul_of_nonneg_right ht (le_of_lt (hQci i))
    have h6a : (Q ^ (-(c i)) + 1) * Q ^ (c i) = 1 + Q ^ (c i) := by
      rw [add_mul, one_mul, hQneg i]
    have h6 : ‖L i j‖ * (Q ^ (-(c i)) + 1) * Q ^ (c i) = ‖L i j‖ * (1 + Q ^ (c i)) := by
      rw [mul_assoc, h6a]
    have h5 : ‖L i j‖ ≤ t₁ * Q ^ (c i) := by
      have h7 : ‖L i j‖ * (Q ^ (-(c i)) + 1) * Q ^ (c i) ≤ t₁ * Q ^ (c i) :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt (hQci i))
      nlinarith [hQci i, norm_nonneg (L i j), h6, h7]
    linarith [h5, h4]
  refine ⟨t₁, ht₁0, fun t ht => ?_⟩
  have hsingle : ∀ j : Fin N, (Pi.single j (1 : ℚ) : Fin N → ℚ)
      ∈ Submodule.span ℚ (boxTQ L c Q t) := by
    intro j
    refine Submodule.subset_span ⟨Pi.single j (1 : ℤ), hmem t ht j, ?_⟩
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  have hspan : Submodule.span ℚ (boxTQ L c Q t) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    have hv : v = ∑ j : Fin N, v j • (Pi.single j (1 : ℚ) : Fin N → ℚ) := by
      funext k
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb)]
        simp
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hv]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hsingle j)
  unfold rankT
  rw [hspan, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The zero vector belongs to every box at a nonnegative scale. -/
lemma zero_mem_boxT (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) {Q t : ℝ} (hQ : 0 < Q)
    (ht : 0 ≤ t) : (0 : Fin N → ℤ) ∈ boxT L c Q t := by
  intro i
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero, Finset.sum_const_zero, norm_zero]
  exact mul_nonneg ht (Real.rpow_nonneg hQ.le _)

/-- The box is trivial for small scales, so the minima are positive. -/
lemma lamS_pos (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0)
    (c : Fin N → ℝ) {Q : ℝ} (hQ : 0 < Q) {j : ℕ} (hj : j < N) : 0 < lamS L c Q j := by
  classical
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨C, hC0, hC⟩ := Commons.Analysis.Normed.intVec_norm_le_sum_forms (Matrix.of L) hdet
  set S : ℝ := ∑ i : Fin N, Q ^ (c i) with hS
  have hS0 : 0 < S := by
    rw [hS]
    exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos hQ _) Finset.univ_nonempty
  set t₀ : ℝ := 1 / (C * S) with ht₀
  have ht₀0 : 0 < t₀ := by rw [ht₀]; positivity
  have hkey : ∀ t : ℝ, 0 ≤ t → t < t₀ → rankT L c Q t = 0 := by
    intro t ht0 htt
    have himg : boxTQ L c Q t = {0} := by
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨⟨(0 : Fin N → ℤ), zero_mem_boxT L c hQ ht0, (by ext k; simp)⟩, ?_⟩
      rintro v ⟨y, hy, rfl⟩
      have h1 : ‖y‖ ≤ C * (∑ i, ‖∑ k, L i k * (y k : ℂ)‖) := hC y
      have h2 : ∑ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ ∑ i, t * Q ^ (c i) :=
        Finset.sum_le_sum fun i _ => hy i
      have h3 : ∑ i, t * Q ^ (c i) = t * S := by
        rw [hS, Finset.mul_sum]
      have h4 : ‖y‖ < 1 := by
        rw [h3] at h2
        have h5 : t * S < t₀ * S := mul_lt_mul_of_pos_right htt hS0
        have h6 : C * (t₀ * S) = 1 := by
          rw [ht₀]
          field_simp
        nlinarith [h1, h2, hC0]
      funext k
      have h7 : ‖y k‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm y k) h4
      rw [Int.norm_eq_abs] at h7
      have h8 : (y k : ℝ) < 1 := lt_of_le_of_lt (le_abs_self _) h7
      have h9 : (-1 : ℝ) < (y k : ℝ) := by
        have := neg_abs_le ((y k : ℤ) : ℝ)
        linarith
      have h10 : y k < 1 := by exact_mod_cast h8
      have h11 : -1 < y k := by exact_mod_cast h9
      have : y k = 0 := by omega
      simp [this, Pi.zero_apply]
    unfold rankT
    rw [himg]
    simp
  have hbdd : ∀ t ∈ {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ rankT L c Q t}, t₀ ≤ t := by
    rintro t ⟨ht0, htrank⟩
    by_contra hcon
    push_neg at hcon
    have := hkey t ht0 hcon
    omega
  have hne : ({t : ℝ | 0 ≤ t ∧ (j + 1) ≤ rankT L c Q t}).Nonempty := by
    obtain ⟨t₁, ht₁0, ht₁⟩ := rankT_large L c hQ
    exact ⟨t₁, ht₁0, by rw [ht₁ t₁ le_rfl]; omega⟩
  exact lt_of_lt_of_le ht₀0 (le_csInf hne hbdd)

/-- Monotonicity of the successive minima. -/
lemma lamS_mono (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) {Q : ℝ} (hQ : 0 < Q)
    {j j' : ℕ} (hjj : j ≤ j') (hj' : j' < N) : lamS L c Q j ≤ lamS L c Q j' := by
  refine csInf_le_csInf ?_ ?_ ?_
  · exact ⟨0, fun t ht => ht.1⟩
  · obtain ⟨t₁, ht₁0, ht₁⟩ := rankT_large L c hQ
    exact ⟨t₁, ht₁0, by have := ht₁ t₁ le_rfl; omega⟩
  · rintro t ⟨ht0, htrank⟩
    exact ⟨ht0, le_trans (Nat.succ_le_succ hjj) htrank⟩

/-- **The dictionary.**  The rank of the box at scale `t` is the number of successive minima not
exceeding `t`. -/
theorem rankT_eq_card (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0)
    (c : Fin N → ℝ) {Q : ℝ} (hQ : 1 ≤ Q) (t : ℝ) (ht : 0 ≤ t) :
    rankT L c Q t =
      ((Finset.univ : Finset (Fin N)).filter (fun j => lamS L c Q j.val ≤ t)).card :=
  Commons.GeometryOfNumbers.Box.box_rank_eq_card_successiveMinimum hN L hdet Q hQ c
    (fun j : Fin N => lamS L c Q j.val) (fun j => rfl) t ht


end Submission.Subspace.RealRank
