import Mathlib
import Submission.Commons.Analysis.Sigma2.projected_gram_four
import Submission.Commons.Analysis.Sigma2.proj_inner_eq
import Submission.Commons.Analysis.Sigma2.jacobi_trace_quad_nonneg_four
import Submission.Commons.Analysis.Sigma2.jacobi_det_nonneg_four
import Submission.Commons.Analysis.Sigma2.linearized_pos_four
import Submission.Commons.Analysis.Sigma2.linearized_grad_sq
import Submission.Commons.Analysis.Sigma2.sigma1_sq_ge_two
import Submission.Commons.Algebra.Matrix.gramForm_trace_det_id
import Submission.Commons.Algebra.Matrix.twoByTwo_psd_of_gram_trace_det

namespace Commons.Analysis.Sigma2

open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Generalized Cauchy–Schwarz for the projection onto the span of two vectors `E`, `L`
in `ℝ⁴`: the square of the orthogonal projection of `t` onto `span{E,L}` is at most `|t|²`.
Concretely, writing `E2 = ∑ E²`, `L2 = ∑ L²`, `EL = ∑ E·L`, `SE = ∑ E·t`, `SL = ∑ L·t`,
the number `(L2*SE² - 2*EL*SE*SL + E2*SL²)/(E2*L2-EL²)` equals `α*SE + β*SL` for the
coordinates `(α,β)` of the projection, and is at most `∑ t²`. -/
private lemma proj_sq_le (E L t : Fin 4 → ℝ)
    (hg0 : 0 < (∑ j, E j * E j) * (∑ j, L j * L j) - (∑ j, E j * L j) ^ 2) :
    ((∑ j, L j * L j) * (∑ j, E j * t j) ^ 2
        - 2 * (∑ j, E j * L j) * (∑ j, E j * t j) * (∑ j, L j * t j)
        + (∑ j, E j * E j) * (∑ j, L j * t j) ^ 2)
        / ((∑ j, E j * E j) * (∑ j, L j * L j) - (∑ j, E j * L j) ^ 2)
      ≤ ∑ j, (t j) ^ 2 := by
  simp only [Fin.sum_univ_four] at hg0 ⊢
  set E2 : ℝ := E 0 * E 0 + E 1 * E 1 + E 2 * E 2 + E 3 * E 3 with hE2
  set L2 : ℝ := L 0 * L 0 + L 1 * L 1 + L 2 * L 2 + L 3 * L 3 with hL2
  set EL : ℝ := E 0 * L 0 + E 1 * L 1 + E 2 * L 2 + E 3 * L 3 with hEL
  set SE : ℝ := E 0 * t 0 + E 1 * t 1 + E 2 * t 2 + E 3 * t 3 with hSE
  set SL : ℝ := L 0 * t 0 + L 1 * t 1 + L 2 * t 2 + L 3 * t 3 with hSL
  set g : ℝ := E2 * L2 - EL ^ 2 with hgdef
  clear_value E2 L2 EL SE SL g
  have hg' : 0 < g := hg0
  have hgne : g ≠ 0 := ne_of_gt hg'
  set α : ℝ := (L2 * SE - EL * SL) / g with hαdef
  set β : ℝ := (E2 * SL - EL * SE) / g with hβdef
  clear_value α β
  have hαE : α * E2 + β * EL = SE := by
    rw [hαdef, hβdef]; field_simp; rw [hgdef]; ring
  have hβL : α * EL + β * L2 = SL := by
    rw [hαdef, hβdef]; field_simp; rw [hgdef]; ring
  rw [div_le_iff₀ hg']
  have hexp1 : (t 0 - α * E 0 - β * L 0) ^ 2 + (t 1 - α * E 1 - β * L 1) ^ 2
      + (t 2 - α * E 2 - β * L 2) ^ 2 + (t 3 - α * E 3 - β * L 3) ^ 2
      = (t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2)
        - 2 * α * (E 0 * t 0 + E 1 * t 1 + E 2 * t 2 + E 3 * t 3)
        - 2 * β * (L 0 * t 0 + L 1 * t 1 + L 2 * t 2 + L 3 * t 3)
        + α ^ 2 * (E 0 * E 0 + E 1 * E 1 + E 2 * E 2 + E 3 * E 3)
        + 2 * α * β * (E 0 * L 0 + E 1 * L 1 + E 2 * L 2 + E 3 * L 3)
        + β ^ 2 * (L 0 * L 0 + L 1 * L 1 + L 2 * L 2 + L 3 * L 3) := by ring
  rw [← hSE, ← hSL, ← hE2, ← hL2, ← hEL] at hexp1
  have hk : α ^ 2 * E2 + 2 * α * β * EL + β ^ 2 * L2 = α * SE + β * SL := by
    rw [show SE = α * E2 + β * EL from hαE.symm, show SL = α * EL + β * L2 from hβL.symm]
    ring
  have hsq : 0 ≤ (t 0 - α * E 0 - β * L 0) ^ 2 + (t 1 - α * E 1 - β * L 1) ^ 2
      + (t 2 - α * E 2 - β * L 2) ^ 2 + (t 3 - α * E 3 - β * L 3) ^ 2 := by positivity
  have hle : α * SE + β * SL ≤ t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 := by
    linarith [hsq, hexp1, hk]
  have hnum : L2 * SE ^ 2 - 2 * EL * SE * SL + E2 * SL ^ 2 = g * (α * SE + β * SL) := by
    rw [show SE = α * E2 + β * EL from hαE.symm, show SL = α * EL + β * L2 from hβL.symm]
    rw [hgdef]; ring
  have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hg')
  linarith [hnum, hmul]

open scoped BigOperators in
theorem jacobi_quad_nonneg_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) (i : Fin 4) (t : Fin 4 → ℝ)
    (ht : (∑ j : Fin 4, ((∑ k : Fin 4, lam k) - lam j) * t j) = 0) :
    let S : ℝ := ∑ k : Fin 4, lam k
    let eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S)
    let δ : ℝ := 1 + eps
    0 ≤ 3 * (∑ j : Fin 4, t j ^ 2) - 2 * t i ^ 2 -
      (1 + δ * (S - lam i) / S) * (∑ j : Fin 4, t j) ^ 2 := by
  dsimp only
  set S : ℝ := ∑ k : Fin 4, lam k with hS
  set eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S) with heps
  set δ : ℝ := 1 + eps with hδ
  set f : ℝ := S - lam i with hf
  set D : ℝ := 3 * S ^ 2 - 2 with hD
  set df : Fin 4 → ℝ := fun j => S - lam j with hdf
  set e : Fin 4 → ℝ := fun j => if j = i then (1 : ℝ) else 0 with he
  set E : Fin 4 → ℝ := fun j => e j - (f / D) * df j with hE
  set L : Fin 4 → ℝ := fun j => 1 - (3 * S / D) * df j with hL
  set η : ℝ := 1 + δ * f / S with hη
  set E2 : ℝ := ∑ j : Fin 4, E j * E j with hE2def
  set L2 : ℝ := ∑ j : Fin 4, L j * L j with hL2def
  set EL : ℝ := ∑ j : Fin 4, E j * L j with hELdef
  set SE : ℝ := ∑ j : Fin 4, E j * t j with hSEdef
  set SL : ℝ := ∑ j : Fin 4, L j * t j with hSLdef
  clear_value S eps δ f D df e E L η E2 L2 EL SE SL
  have hσ1' : 0 < ∑ i : Fin 4, lam i := by rw [← hS]; exact hσ1
  have ht' : (∑ j : Fin 4, ((∑ k : Fin 4, lam k) - lam j) * t j) = 0 := by
    rw [hS] at ht; exact ht
  -- basic positivity
  have hSpos : 0 < S := hσ1
  have hfpos : 0 < f := by
    rw [hf, hS]; exact linearized_pos_four lam hmono hσ2 hσ1' i
  have hDpos : 0 < D := by
    have h2 : 2 ≤ S ^ 2 := by rw [hS]; exact sigma1_sq_ge_two lam hσ2
    rw [hD]; nlinarith
  have hepspos : 0 < eps := by
    rw [heps, hS]
    exact (jacobi_eps_range_four lam hmono hσ2 hσ1').1
  have hepslt : eps < 1 / 2 := by
    rw [heps, hS]
    exact (jacobi_eps_range_four lam hmono hσ2 hσ1').2
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hηpos : 0 < η := by
    rw [hη]
    have hfd : 0 < δ * f / S := div_pos (mul_pos hδpos hfpos) hSpos
    linarith
  -- the constraint identities
  have hin : (∑ j : Fin 4, E j * t j) = t i ∧ (∑ j : Fin 4, L j * t j) = ∑ j : Fin 4, t j := by
    have h := proj_inner_eq lam i t ht'
    dsimp only at h
    simpa only [hS, hf, hD, hdf, he, hE, hL] using h
  -- the Gram data
  have hgram := projected_gram_four lam hmono hσ2 hσ1' i
  dsimp only at hgram
  have hgram' : ((∑ j : Fin 4, E j * E j) = 1 - f ^ 2 / D) ∧
      ((∑ j : Fin 4, L j * L j) = 1 - 6 / D) ∧
      ((∑ j : Fin 4, E j * L j) = 1 - 3 * S * f / D) := by
    simpa only [hS, hf, hD, hdf, he, hE, hL] using hgram
  have hE2val : E2 = 1 - f ^ 2 / D := by rw [hE2def]; exact hgram'.1
  have hL2val : L2 = 1 - 6 / D := by rw [hL2def]; exact hgram'.2.1
  have hELval : EL = 1 - 3 * S * f / D := by rw [hELdef]; exact hgram'.2.2
  -- trace and determinant nonnegativity
  have hδ0 : 0 ≤ δ := le_of_lt hδpos
  have hδ2 : δ ≤ 2 := by rw [hδ]; linarith
  have htr := jacobi_trace_quad_nonneg_four lam hmono hσ2 hσ1' δ hδ0 hδ2 i
  dsimp only at htr
  rw [← hS, ← hf, ← hD] at htr
  have hA : 0 ≤ 6 - 2 * E2 - η * L2 := by
    have key : 6 - 2 * E2 - η * L2 = (3 - δ * f / S) + (2 * f ^ 2 + 6 * (1 + δ * f / S)) / D := by
      rw [hE2val, hL2val, hη]; field_simp; ring
    rw [key]; exact htr
  have hdet := jacobi_det_nonneg_four lam hmono hσ2 hσ1' i
  dsimp only at hdet
  rw [← hS, ← hf, ← hD] at hdet
  have hB : 0 ≤ 9 - 6 * E2 - 3 * η * L2 + 2 * η * (E2 * L2 - EL ^ 2) := by
    rw [hE2val, hL2val, hELval, hη, hδ, heps]
    exact hdet
  -- E2 > 0
  have hE2pos : 0 < E2 := by
    rw [hE2def]
    obtain ⟨j0, hj0⟩ : ∃ j : Fin 4, j ≠ i := by
      by_cases hi : i = 0
      · exact ⟨1, by rw [hi]; decide⟩
      · exact ⟨0, fun h => hi h.symm⟩
    have hdfj0 : 0 < df j0 := by
      rw [hdf, hS]
      exact linearized_pos_four lam hmono hσ2 hσ1' j0
    have hEj0 : E j0 = -(f / D) * df j0 := by
      simp only [hE, he, hdf, hj0, if_false, zero_sub]
      ring
    have hEj0ne : E j0 ≠ 0 := by
      rw [hEj0]
      have hfd : 0 < f / D := div_pos hfpos hDpos
      have : -(f / D) * df j0 < 0 := by nlinarith
      exact ne_of_lt this
    have hterm : 0 < E j0 * E j0 := mul_self_pos.mpr hEj0ne
    have hle := Finset.single_le_sum (f := fun j : Fin 4 => E j * E j)
      (fun j _ => mul_self_nonneg (E j)) (Finset.mem_univ j0)
    linarith
  -- Gram Cauchy-Schwarz
  have hCS0 : EL ^ 2 ≤ E2 * L2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4)) E L
    rw [hELdef, hE2def, hL2def]
    simpa [pow_two] using h
  have hgnonneg : 0 ≤ E2 * L2 - EL ^ 2 := by linarith
  rw [← hin.1, ← hin.2, ← hSEdef, ← hSLdef]
  rcases eq_or_lt_of_le hgnonneg with hg0 | hgpos
  · -- degenerate case: E and L are linearly dependent; trace condition degenerates
    have hc : 0 ≤ 3 - 2 * E2 - η * L2 := by
      have h := hB
      rw [hg0] at h
      nlinarith
    have hCS1 : SE ^ 2 ≤ E2 * (∑ j : Fin 4, t j ^ 2) := by
      rw [hSEdef]
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4)) E t
      rw [hE2def]
      simpa [pow_two] using h
    have hCS2 : SL ^ 2 ≤ L2 * (∑ j : Fin 4, t j ^ 2) := by
      rw [hSLdef]
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4)) L t
      rw [hL2def]
      simpa [pow_two] using h
    have htsq : 0 ≤ ∑ j : Fin 4, t j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (t j))
    have h1' : 2 * SE ^ 2 ≤ 2 * (E2 * (∑ j : Fin 4, t j ^ 2)) := by linarith
    have h2' : η * SL ^ 2 ≤ η * (L2 * (∑ j : Fin 4, t j ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS2 (le_of_lt hηpos)
    have hprod : 0 ≤ (3 - 2 * E2 - η * L2) * (∑ j : Fin 4, t j ^ 2) := mul_nonneg hc htsq
    linarith [h1', h2', hprod]
  · -- nondegenerate case: reduce to the span of E and L
    set M11 : ℝ := 3 * E2 - 2 * E2 ^ 2 - η * EL ^ 2 with hM11
    set M12 : ℝ := 3 * EL - 2 * E2 * EL - η * EL * L2 with hM12
    set M22 : ℝ := 3 * L2 - 2 * EL ^ 2 - η * L2 ^ 2 with hM22
    clear_value M11 M12 M22
    have htrM : 0 ≤ L2 * M11 - 2 * EL * M12 + E2 * M22 := by
      have key : L2 * M11 - 2 * EL * M12 + E2 * M22
          = (E2 * L2 - EL ^ 2) * (6 - 2 * E2 - η * L2) := by
        rw [hM11, hM12, hM22]; ring
      rw [key]; exact mul_nonneg hgnonneg hA
    have hdetM : 0 ≤ M11 * M22 - M12 ^ 2 := by
      have key : M11 * M22 - M12 ^ 2
          = (E2 * L2 - EL ^ 2) * (9 - 6 * E2 - 3 * η * L2 + 2 * η * (E2 * L2 - EL ^ 2)) := by
        rw [hM11, hM12, hM22]; ring
      rw [key]; exact mul_nonneg hgnonneg hB
    have hMpos := Commons.Algebra.Matrix.twoByTwo_psd_of_gram_trace_det E2 L2 EL M11 M12 M22 hE2pos hgpos htrM hdetM
    set g : ℝ := E2 * L2 - EL ^ 2 with hgdef
    clear_value g
    have hgne : g ≠ 0 := ne_of_gt hgpos
    have hgposE : 0 < E2 * L2 - EL ^ 2 := by rw [← hgdef]; exact hgpos
    set α : ℝ := (L2 * SE - EL * SL) / g with hαdef
    set β : ℝ := (E2 * SL - EL * SE) / g with hβdef
    clear_value α β
    have hαE : α * E2 + β * EL = SE := by
      rw [hαdef, hβdef]; field_simp; rw [hgdef]; ring
    have hβL : α * EL + β * L2 = SL := by
      rw [hαdef, hβdef]; field_simp; rw [hgdef]; ring
    have hle : α * SE + β * SL ≤ ∑ j : Fin 4, t j ^ 2 := by
      have h := proj_sq_le E L t (by rw [← hE2def, ← hL2def, ← hELdef]; exact hgposE)
      rw [← hE2def, ← hL2def, ← hELdef, ← hgdef] at h
      have key : α * SE + β * SL
          = (L2 * (∑ j, E j * t j) ^ 2
              - (2 * EL * (∑ j, E j * t j)) * (∑ j, L j * t j)
              + E2 * (∑ j, L j * t j) ^ 2) / g := by
        rw [hαdef, hβdef, ← hSEdef, ← hSLdef]
        field_simp; ring
      rw [key]; exact h
    have hval : α * SE + β * SL = α ^ 2 * E2 + 2 * α * β * EL + β ^ 2 * L2 := by
      rw [show SE = α * E2 + β * EL from hαE.symm, show SL = α * EL + β * L2 from hβL.symm]
      ring
    have hmain : 0 ≤ 3 * (α ^ 2 * E2 + 2 * α * β * EL + β ^ 2 * L2)
        - 2 * (α * E2 + β * EL) ^ 2 - η * (α * EL + β * L2) ^ 2 := by
      have hm := hMpos α β
      rw [hM11, hM12, hM22] at hm
      nlinarith [hm]
    have hSE' : SE = α * E2 + β * EL := hαE.symm
    have hSL' : SL = α * EL + β * L2 := hβL.symm
    rw [hSE', hSL'] at hle hval ⊢
    linarith [hle, hval, hmain]

end Commons.Analysis.Sigma2
