import Mathlib
import Submission.Work.GM.Trace.Defs

namespace Work.GM.Trace

open Complex Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Submission.GM Submission.LargeValues

/-- Elementary real inequality: for `0 ≤ u, v, w` with `u - v ≤ w` we have
`u ^ 3 - 3 * u ^ 2 * v ≤ w ^ 3`. -/
private lemma cube_sub_three_mul_sq_le {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : u - v ≤ w) : u ^ 3 - 3 * u ^ 2 * v ≤ w ^ 3 := by
  by_cases hv3 : v ≤ 3 * u
  · have h1 : (u - v) ^ 3 ≤ w ^ 3 := (Odd.pow_le_pow (show Odd 3 by decide)).mpr h
    have h2 : 0 ≤ v ^ 2 * (3 * u - v) := mul_nonneg (sq_nonneg v) (by linarith)
    nlinarith [h1, h2, hu, hv3]
  · push Not at hv3
    have h2 : u ^ 3 - 3 * u ^ 2 * v ≤ 0 := by nlinarith [hu, hv3]
    have h3 : 0 ≤ w ^ 3 := by positivity
    linarith

/-- Power-mean nonnegativity of the Guth–Maynard quantity `A = Σσᵢ⁶ - (Σσᵢ²)³/|W|²`:
the effective number of nonzero singular values is at most `|W|`. -/
private lemma singularValues_A_nonneg (N : ℕ) (W : Finset ℝ) (hW : 0 < W.card) :
    0 ≤ (∑ i : Fin (N + 1), (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 6)
      - (∑ i : Fin (N + 1), (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 2) ^ 3
          / (W.card : ℝ) ^ 2 := by
  classical
  set T := Matrix.toEuclideanLin (MWmat N W) with hT
  have hcpos : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast hW
  have hfF : Module.finrank ℂ (EuclideanSpace ℂ ↥W) = W.card := by
    rw [finrank_euclideanSpace, Fintype.card_coe]
  have hvanish : ∀ i : ℕ, W.card ≤ i → T.singularValues i = 0 := by
    intro i hi
    have hrank : Module.finrank ℂ ↥T.range
        ≤ Module.finrank ℂ (EuclideanSpace ℂ ↥W) := Submodule.finrank_le T.range
    rw [hfF] at hrank
    have hlt : ¬ i < Module.finrank ℂ ↥T.range := by omega
    have h : ¬ 0 < T.singularValues i := by
      rw [T.singularValues_pos_iff_lt_finrank_range]; exact hlt
    exact le_antisymm (not_lt.mp h) (T.singularValues_nonneg i)
  have h2v : (∑ i : Fin (N + 1), T.singularValues i ^ 2)
      = ∑ i ∈ Finset.range W.card, T.singularValues i ^ 2 :=
    Commons.LinearAlgebra.InnerProductSpace.sum_fin_eq_sum_range_of_vanish
      (fun i => T.singularValues i ^ 2)
      (fun i hi => by rw [T.singularValues_of_finrank_le (by simpa using hi)]; ring)
      (fun i hi => by rw [hvanish i hi]; ring)
  have h6v : (∑ i : Fin (N + 1), T.singularValues i ^ 6)
      = ∑ i ∈ Finset.range W.card, T.singularValues i ^ 6 :=
    Commons.LinearAlgebra.InnerProductSpace.sum_fin_eq_sum_range_of_vanish
      (fun i => T.singularValues i ^ 6)
      (fun i hi => by rw [T.singularValues_of_finrank_le (by simpa using hi)]; ring)
      (fun i hi => by rw [hvanish i hi]; ring)
  have hPQ : (∑ i ∈ Finset.range W.card, T.singularValues i ^ 2) ^ 3
      ≤ (W.card : ℝ) ^ 2 * ∑ i ∈ Finset.range W.card, T.singularValues i ^ 6 := by
    have h1 := pow_sum_div_card_le_sum_pow (s := Finset.range W.card)
      (f := fun i => T.singularValues i ^ 2) (fun i _ => by positivity) 2
    simp only [Finset.card_range] at h1
    rw [show (2 : ℕ) + 1 = 3 from rfl] at h1
    have h2 : (∑ i ∈ Finset.range W.card, (T.singularValues i ^ 2) ^ 3)
        = ∑ i ∈ Finset.range W.card, T.singularValues i ^ 6 := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [h2] at h1
    rw [div_le_iff₀ (pow_pos hcpos 2)] at h1
    nlinarith [h1]
  rw [h2v, h6v, sub_nonneg, div_le_iff₀ (pow_pos hcpos 2)]
  nlinarith [hPQ]

/-- The numerical heart of the assembly: from the spectral large-values bound together with
one-sided bounds on `A = Σσᵢ⁶ - (Σσᵢ²)³/|W|²` and `B = Σσᵢ²/|W|`, deduce the final
Guth–Maynard inequality. -/
private lemma core {N c V A B Az Sn δA δB : ℝ}
    (hN : 1 ≤ N) (hc : 1 ≤ c) (hV : 0 < V) (hAz : 0 ≤ Az) (hSn : 0 ≤ Sn)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hδA0 : 0 ≤ δA) (hδA1 : δA ≤ 1) (hδB1 : δB ≤ 1)
    (hBub : B ≤ N * Az + δB) (hAub : A ≤ Sn + δA)
    (hspec : c * V ^ 2 ≤ (N + 1) * (8 * A ^ (1 / 3 : ℝ) + 8 * B)) :
    c ≤ (16 * Az + 48) * (N ^ 2 / V ^ 2 + N / V ^ 2 * Sn ^ (1 / 3 : ℝ)) := by
  have hV2 : (0 : ℝ) < V ^ 2 := by positivity
  have hVne : V ≠ 0 := ne_of_gt hV
  have hX0 : 0 ≤ Sn ^ (1 / 3 : ℝ) := Real.rpow_nonneg hSn _
  have hA13 : A ^ (1 / 3 : ℝ) ≤ Sn ^ (1 / 3 : ℝ) + 1 := by
    have h1 : A ^ (1 / 3 : ℝ) ≤ (Sn + δA) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow hA0 hAub (by norm_num)
    have h2 : (Sn + δA) ^ (1 / 3 : ℝ) ≤ Sn ^ (1 / 3 : ℝ) + δA ^ (1 / 3 : ℝ) :=
      Real.rpow_add_le_add_rpow hSn hδA0 (by norm_num) (by norm_num)
    have h3 : δA ^ (1 / 3 : ℝ) ≤ 1 := Real.rpow_le_one hδA0 hδA1 (by norm_num)
    linarith
  have hkey : (N + 1) * (8 * A ^ (1 / 3 : ℝ) + 8 * B)
      ≤ (16 * Az + 48) * (N ^ 2 + N * Sn ^ (1 / 3 : ℝ)) := by
    nlinarith [hA13, hBub, hδB1, hX0, hAz, hN, hA0, hB0]
  have hstep : c * V ^ 2 ≤ (16 * Az + 48) * (N ^ 2 + N * Sn ^ (1 / 3 : ℝ)) :=
    le_trans hspec hkey
  have hfinal : c ≤ (16 * Az + 48) * (N ^ 2 + N * Sn ^ (1 / 3 : ℝ)) / V ^ 2 := by
    rw [le_div_iff₀ hV2]
    exact hstep
  calc c ≤ (16 * Az + 48) * (N ^ 2 + N * Sn ^ (1 / 3 : ℝ)) / V ^ 2 := hfinal
    _ = (16 * Az + 48) * (N ^ 2 / V ^ 2 + N / V ^ 2 * Sn ^ (1 / 3 : ℝ)) := by
        field_simp

-- Numeric assembly of GM Proposition 4.6: from the spectral large-values bound
-- (`Submission.LargeValues.card_mul_sq_le_trace_terms`) and the two trace estimates supplied as
-- hypotheses, deduce the final inequality
-- `|W| ≤ (16 Azero + 48) (N²/V² + N/V² ‖S₁+S₂+S₃‖^{1/3})`.
-- Write `s2`, `s6` for the two singular-value sums, `S := S₁+S₂+S₃`,
-- `A := s6 - s2³/|W|²` and `B := s2/|W|`.  The spectral bound (apply
-- `Submission.LargeValues.card_mul_sq_le_trace_terms`) gives `|W| V² ≤ (N+1)(8 A^{1/3} + 8 B)`.
-- FIRST prove `0 ≤ A` (power mean over the singular values:
-- `pow_sum_div_card_le_sum_pow`, as used inside
-- `Commons.LinearAlgebra.InnerProductSpace.singularValues_top_sq_le_trace`, whose proof contains
-- exactly this `hA : 0 ≤ A`; the effective number of nonzero singular values is at most `W.card`).
-- Do NOT try to handle `A < 0` via `Real.rpow`: for a negative base Lean gives
-- `x^y = exp (log x * y) * cos (y * π)` (`Real.rpow_def_of_neg`), which is `|x|^{1/3}/2`, unbounded.
-- With `0 ≤ A`: the first hypothesis gives `B ≤ N Azero + δB`, `δB := tinyN N/|W|`; the second and
-- `s2 ≥ N|W|Azero - tinyN N` give `A ≤ ‖S‖ + δA` with `δA := tinyN N + 3 N² Azero² tinyN N`
-- (use `(u-v)³ ≥ u³ - 3u²v` for `u, v ≥ 0`: for `v ≤ u` it is `v²(3u-v) ≥ 0`, for `v > u` it is
-- `u²(3v-u) ≥ 0`).  Then `A^{1/3} ≤ ‖S‖^{1/3} + δA^{1/3}` by `Real.rpow_add_le_add_rpow`.
-- Finally `N₀` is chosen large enough that `δA^{1/3} ≤ 1` and `δB ≤ 1` (the Archimedean property
-- and `Azero > 0` are the only inputs there), and `N ≤ N²`, `N ≥ 1` finish the constant chase.
theorem final_bound :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (W : Finset ℝ) (b : ℕ → ℂ) (V : ℝ),
      (1 : ℝ) ≤ (W.card : ℝ) → (∀ n, ‖b n‖ ≤ 1) → 0 < V →
      (∀ t ∈ W, V ≤ ‖Submission.LargeValues.smoothedPoly N b t‖) →
      |(∑ i : Fin (N + 1),
          (Matrix.toEuclideanLin (Submission.LargeValues.MWmat N W)).singularValues i ^ 2)
          - (N : ℝ) * (W.card : ℝ) * Work.GM.Trace.Azero| ≤ Work.GM.Trace.tinyN N →
      (∑ i : Fin (N + 1),
          (Matrix.toEuclideanLin (Submission.LargeValues.MWmat N W)).singularValues i ^ 6)
        ≤ (N : ℝ) ^ 3 * (W.card : ℝ) * Work.GM.Trace.Azero ^ 3
          + ‖Submission.GM.Spart 1 N W + Submission.GM.Spart 2 N W + Submission.GM.Spart 3 N W‖
          + Work.GM.Trace.tinyN N →
      (W.card : ℝ) ≤ (16 * Work.GM.Trace.Azero + 48) *
        ((N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) / V ^ 2 *
          ‖Submission.GM.Spart 1 N W + Submission.GM.Spart 2 N W + Submission.GM.Spart 3 N W‖
            ^ (1 / 3 : ℝ)) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (3 * Azero ^ 2 + 1)
  refine ⟨max 1 M, ?_⟩
  intro N hN W b V hcard hb hV hval h1 h2
  have hN1 : 1 ≤ N := le_trans (le_max_left 1 M) hN
  have hNM : M ≤ N := le_trans (le_max_right 1 M) hN
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNrgt : 3 * Azero ^ 2 + 1 < (N : ℝ) := lt_of_lt_of_le hM (by exact_mod_cast hNM)
  have hAz : 0 ≤ Azero := Azero_nonneg
  have hc1 : (1 : ℝ) ≤ (W.card : ℝ) := hcard
  have hcpos : (0 : ℝ) < (W.card : ℝ) := by linarith
  have hWc : 0 < W.card := by exact_mod_cast hcpos
  have hspec0 := Submission.LargeValues.card_mul_sq_le_trace_terms N hN1 W b V hV hb hval hWc
  -- abbreviations
  set c : ℝ := (W.card : ℝ) with hc
  set Sn : ℝ := ‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ with hSn
  set s2 : ℝ := ∑ i : Fin (N + 1),
    (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 2 with hs2
  set s6 : ℝ := ∑ i : Fin (N + 1),
    (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 6 with hs6
  have hc1' : (1 : ℝ) ≤ c := by rw [hc]; exact hc1
  have hcpos' : (0 : ℝ) < c := by rw [hc]; exact hcpos
  have hcne : c ≠ 0 := ne_of_gt hcpos'
  have hSn_nn : 0 ≤ Sn := by rw [hSn]; exact norm_nonneg _
  have htiny_nn : 0 ≤ tinyN N := by rw [tinyN]; positivity
  -- `δA ≤ 1`
  have hkey : 3 * (N : ℝ) ^ 2 * Azero ^ 2 + 1 ≤ (N : ℝ) ^ 50 := by
    have hmul : (3 * Azero ^ 2 + 1) * (N : ℝ) ^ 2 < (N : ℝ) * (N : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right hNrgt (by positivity)
    have h3 : 3 * (N : ℝ) ^ 2 * Azero ^ 2 + 1 ≤ (N : ℝ) ^ 3 := by
      have hsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      nlinarith [hmul]
    have h450 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 50 := pow_le_pow_right₀ hNr1 (by norm_num)
    linarith
  have hδA1 : tinyN N * (1 + 3 * (N : ℝ) ^ 2 * Azero ^ 2) ≤ 1 := by
    have hpow : (0 : ℝ) < (N : ℝ) ^ 50 := by positivity
    rw [tinyN, div_mul_eq_mul_div, one_mul, div_le_iff₀ hpow]
    linarith [hkey]
  have hδA0 : 0 ≤ tinyN N * (1 + 3 * (N : ℝ) ^ 2 * Azero ^ 2) :=
    mul_nonneg htiny_nn (by nlinarith [hAz, hNr1])
  have htiny1 : tinyN N ≤ 1 := by
    have hge : (1 : ℝ) ≤ 1 + 3 * (N : ℝ) ^ 2 * Azero ^ 2 := by nlinarith [hAz, hNr1]
    exact le_trans (le_mul_of_one_le_right htiny_nn hge) hδA1
  have hδB1 : tinyN N / c ≤ 1 := by
    rw [div_le_iff₀ hcpos']
    linarith
  -- `0 ≤ A`
  have hA0 : 0 ≤ s6 - s2 ^ 3 / c ^ 2 := by
    have h := singularValues_A_nonneg N W hWc
    rw [← hc, ← hs2, ← hs6] at h
    exact h
  have hs2_nn : 0 ≤ s2 := by
    rw [hs2]
    exact Finset.sum_nonneg fun i _ => pow_nonneg (LinearMap.singularValues_nonneg _ i) 2
  have hB0 : 0 ≤ s2 / c := div_nonneg hs2_nn hcpos'.le
  -- `B ≤ N Azero + δB`
  have h1a : (N : ℝ) * c * Azero - tinyN N ≤ s2 := by
    have := (abs_le.mp h1).1; linarith
  have h1b : s2 ≤ (N : ℝ) * c * Azero + tinyN N := by
    have := (abs_le.mp h1).2; linarith
  have hBub : s2 / c ≤ (N : ℝ) * Azero + tinyN N / c := by
    have h := div_le_div_of_nonneg_right h1b hcpos'.le
    have e : ((N : ℝ) * c * Azero + tinyN N) / c = (N : ℝ) * Azero + tinyN N / c := by
      field_simp
    rwa [e] at h
  -- `A ≤ Sn + δA`
  have hS2low : (N : ℝ) ^ 3 * c * Azero ^ 3 - 3 * (N : ℝ) ^ 2 * Azero ^ 2 * tinyN N
      ≤ s2 ^ 3 / c ^ 2 := by
    have hu : (0 : ℝ) ≤ (N : ℝ) * c * Azero :=
      mul_nonneg (mul_nonneg (by positivity) hcpos'.le) hAz
    have hcube := cube_sub_three_mul_sq_le hu htiny_nn hs2_nn h1a
    have hdiv := div_le_div_of_nonneg_right hcube (by positivity : (0:ℝ) ≤ c ^ 2)
    have e : (((N : ℝ) * c * Azero) ^ 3 - 3 * ((N : ℝ) * c * Azero) ^ 2 * tinyN N) / c ^ 2
        = (N : ℝ) ^ 3 * c * Azero ^ 3 - 3 * (N : ℝ) ^ 2 * Azero ^ 2 * tinyN N := by
      field_simp
    rwa [e] at hdiv
  have hAub : s6 - s2 ^ 3 / c ^ 2 ≤ Sn + tinyN N * (1 + 3 * (N : ℝ) ^ 2 * Azero ^ 2) := by
    have e : tinyN N * (1 + 3 * (N : ℝ) ^ 2 * Azero ^ 2)
        = tinyN N + 3 * (N : ℝ) ^ 2 * Azero ^ 2 * tinyN N := by ring
    linarith [h2, hS2low, e]
  exact core hNr1 hc1' hV hAz hSn_nn hA0 hB0 hδA0 hδA1 hδB1 hBub hAub hspec0

end Work.GM.Trace
