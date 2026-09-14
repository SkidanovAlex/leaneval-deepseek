import Mathlib
import Submission.Subspace.RealRank.Box
import Submission.Subspace.RankDesc
import Submission.Commons.GeometryOfNumbers.Box.prod_successiveMinimum_box_le_real
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.exists_gap_index
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.successiveMinima_bounds
import Submission.Commons.NumberTheory.DiophantineApproximation.graded_basis_real

/-!
# The gap index and the realiser family

This file chains the geometry-of-numbers input into the shape needed for the rank descent: the
last successive minimum is `≥ Q ^ (ε/(2N))`, hence there is a *gap index* `k` with
`λ_k / λ_{k+1} ≤ Q ^ (-ε/(2N(N-R)))`, and the realisers of the successive minima satisfy the
hypotheses of the straightening lemma `graded_basis_real`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Submission.Subspace.RealRank

variable {N : ℕ}

/-- The successive minima extended to `ℕ` (clamped at the top): `lam1 j` is the `(j+1)`-st
minimum for `j < N` and the last minimum for `j ≥ N`. -/
noncomputable def lam1 (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) (Q : ℝ) (j : ℕ) : ℝ :=
  if j < N then lamS L c Q (j - 1) else lamS L c Q (N - 1)

lemma lam1_of_lt {L : Fin N → Fin N → ℂ} {c : Fin N → ℝ} {Q : ℝ} {j : ℕ} (hj : j < N) :
    lam1 L c Q j = lamS L c Q (j - 1) := by
  rw [lam1, if_pos hj]

lemma lam1_of_ge {L : Fin N → Fin N → ℂ} {c : Fin N → ℝ} {Q : ℝ} {j : ℕ} (hj : ¬ j < N) :
    lam1 L c Q j = lamS L c Q (N - 1) := by
  rw [lam1, if_neg hj]

lemma lam1_zero (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) (Q : ℝ) :
    lam1 L c Q 0 = lamS L c Q 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [lam1_of_ge (by omega)]
  · rw [lam1_of_lt hN]

lemma lam1_succ {L : Fin N → Fin N → ℂ} {c : Fin N → ℝ} {Q : ℝ} {k : ℕ} (hk : k < N) :
    lam1 L c Q (k + 1) = lamS L c Q k := by
  by_cases h : k + 1 < N
  · rw [lam1_of_lt h, show k + 1 - 1 = k from by omega]
  · rw [lam1_of_ge h, show N - 1 = k from by omega]

/-- Monotonicity of the clamped minima. -/
lemma lam1_mono (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) {Q : ℝ} (hQ : 0 < Q)
    {i j : ℕ} (hij : i ≤ j) : lam1 L c Q i ≤ lam1 L c Q j := by
  by_cases hj : j < N
  · have hi : i < N := lt_of_le_of_lt hij hj
    rw [lam1_of_lt hi, lam1_of_lt hj]
    exact lamS_mono L c hQ (Nat.sub_le_sub_right hij 1) (by omega)
  · rw [lam1_of_ge hj]
    by_cases hi : i < N
    · rw [lam1_of_lt hi]
      exact lamS_mono L c hQ (by omega) (by omega)
    · rw [lam1_of_ge hi]

/-- Positivity of the clamped minima. -/
lemma lam1_pos (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0)
    (c : Fin N → ℝ) {Q : ℝ} (hQ : 0 < Q) {j : ℕ} (hj : j ≤ N) : 0 < lam1 L c Q j := by
  by_cases h : j < N
  · rw [lam1_of_lt h]
    exact lamS_pos hN L hdet c hQ (by omega)
  · rw [lam1_of_ge h]
    exact lamS_pos hN L hdet c hQ (by omega)

/-- **The last successive minimum is large.**  For `Q` large, `λ_N ≥ Q ^ (ε/(2N))`, where
`ε = -∑ c i > 0`.  This is the rank bound `scaled_box_rank_lt` in the language of successive
minima. -/
theorem lamS_last_ge (hN : 2 ≤ N) (L : Fin N → Fin N → ℂ) (ind : LinearIndependent ℂ L)
    (hdet : (Matrix.of L).det ≠ 0) (c : Fin N → ℝ) (hc : ∑ i, c i < 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      Q ^ (-(∑ i, c i) / (2 * (N : ℝ))) ≤ lamS L c Q (N - 1) := by
  classical
  obtain ⟨Q₁, hQ₁, hQ₁'⟩ := scaled_box_rank_lt (σ := Fin N) (by simpa using hN) L ind c hc
  refine ⟨max Q₁ 1, le_max_right _ _, fun Q hQ => ?_⟩
  have hQ1 : 1 ≤ Q := le_trans (le_max_right _ _) hQ
  have hQ₁Q : Q₁ ≤ Q := le_trans (le_max_left _ _) hQ
  have hεpos : 0 < -(∑ i, c i) := by linarith
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ1
  set t : ℝ := Q ^ (-(∑ i, c i) / (2 * (N : ℝ))) with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.rpow_nonneg (le_of_lt hQpos) _
  have htN : t ≤ Q ^ (-(∑ i, c i) / (2 * ((Fintype.card (Fin N) : ℕ) : ℝ))) := by
    rw [ht]; simp
  have hrank := hQ₁' Q hQ₁Q t (by rw [ht]; exact Real.rpow_pos_of_pos hQpos _) htN
  have hdict := rankT_eq_card (Nat.one_le_iff_ne_zero.mpr (by omega)) L hdet c hQ1 t ht0
  have hrankN : rankT L c Q t < N := by
    unfold rankT boxTQ boxT
    simpa using hrank
  by_contra hcon
  push_neg at hcon
  have hmem : ∀ j : Fin N, lamS L c Q j.val ≤ t := by
    intro j
    refine le_trans (lamS_mono L c hQpos (show j.val ≤ N - 1 by omega)
      (show N - 1 < N by omega)) (le_of_lt hcon)
  have hcard : ((Finset.univ : Finset (Fin N)).filter
      (fun j => lamS L c Q j.val ≤ t)).card = N := by
    rw [Finset.filter_true_of_mem (fun j _ => hmem j), Finset.card_univ, Fintype.card_fin]
  rw [hdict, hcard] at hrankN
  omega

/-- **The gap index.**  If the rank of the box is `R` (so that the `R`-th minimum is `≤ 1`),
there is `k` with `R ≤ k ≤ N-1` and `λ_k / λ_{k+1} ≤ Q ^ (-ε/(2N(N-R)))`. -/
theorem exists_gap_index_lamS (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ)
    (hdet : (Matrix.of L).det ≠ 0) (c : Fin N → ℝ) (hc : ∑ i, c i < 0) {Q : ℝ} (hQ : 1 < Q)
    {R : ℕ} (hR : R < N) (hRle : lamS L c Q (R - 1) ≤ 1)
    (hgapN : Q ^ ((-(∑ i, c i)) / (2 * (N : ℝ))) ≤ lamS L c Q (N - 1)) :
    ∃ k, R ≤ k ∧ k < N ∧
      lamS L c Q (k - 1) / lamS L c Q k ≤
        Q ^ (-(-(∑ i, c i) / (2 * (N : ℝ) * ((N : ℝ) - R)))) := by
  set ε : ℝ := -(∑ i, c i) with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨k, hk1, hk2, hk3⟩ := Commons.GeometryOfNumbers.SuccessiveMinima.exists_gap_index
    (lam := lam1 L c Q) hN hR (fun i j hij => lam1_mono hN L c (lt_trans zero_lt_one hQ) hij)
    (fun i hi => lam1_pos hN L hdet c (lt_trans zero_lt_one hQ) hi)
    (by rw [lam1_of_lt hR]; exact hRle) hεpos hQ
    (by
      rw [show lam1 L c Q N = lamS L c Q (N - 1) from lam1_of_ge (by omega), hε]
      exact hgapN)
  refine ⟨k, hk1, hk2, ?_⟩
  rw [lam1_of_lt hk2, lam1_succ (k := k) hk2, hε] at hk3
  exact hk3

end Submission.Subspace.RealRank
