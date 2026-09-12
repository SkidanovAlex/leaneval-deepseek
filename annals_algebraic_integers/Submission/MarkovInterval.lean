import Submission.Markov
import Submission.SerreExample

/-!
# Markov's inequality on the Serre interval

Affine image of `Submission.Markov.markov_unit` under
`x = chebPoint t = (a+b)/2 + (b−a)/2·t`, `t = (2x−a−b)/(b−a)`.
Chain rule: `P'(x) = R'(t)·(2/(b−a))` where `R(t) := P.eval (chebPoint t)`
(`R = P.comp (C ((a+b)/2) + C ((b−a)/2)·X)`), and `R.natDegree ≤ P.natDegree ≤ n`.
-/

noncomputable section

open scoped Real
open Polynomial

namespace Submission.MarkovInterval

open Submission.SerreExample

/-- The affine coordinate `t = (2x − a − b)/(b − a) ∈ [−1,1]` for `x ∈ [a,b]`. -/
def unitCoord (x : ℝ) : ℝ := (2 * x - aSerre - bSerre) / (bSerre - aSerre)

/-- Inverse map `x = chebPoint t` for `t ∈ [−1,1]`. -/
def chebPoint (t : ℝ) : ℝ := (aSerre + bSerre) / 2 + (bSerre - aSerre) / 2 * t

/-- The polynomial `t ↦ chebPoint t`. -/
noncomputable def chebPointPoly : Polynomial ℝ :=
  C ((aSerre + bSerre) / 2) + C ((bSerre - aSerre) / 2) * X

/-- `unitCoord (chebPoint t) = t` on the real line. -/
lemma unitCoord_chebPoint (t : ℝ) : unitCoord (chebPoint t) = t := by
  unfold chebPoint unitCoord
  have hb : bSerre - aSerre ≠ 0 := by norm_num [aSerre, bSerre]
  field_simp [hb]
  ring

/-- For `x ∈ [aSerre,bSerre]`, the normalized coordinate lies in `[−1,1]`. -/
lemma unitCoord_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    unitCoord x ∈ Set.Icc (-1) 1 := by
  unfold unitCoord
  have hb : 0 < bSerre - aSerre := by norm_num [aSerre, bSerre]
  constructor
  · have hxa : aSerre ≤ x := hx.1
    rw [le_div_iff₀ hb]
    nlinarith
  · have hxb : x ≤ bSerre := hx.2
    rw [div_le_iff₀ hb]
    nlinarith

/-- For `x ∈ [aSerre,bSerre]`, `x = chebPoint (unitCoord x)`. -/
lemma chebPoint_unitCoord_of_mem {_x : ℝ} (_hx : _x ∈ Set.Icc aSerre bSerre) :
    chebPoint (unitCoord _x) = _x := by
  unfold chebPoint unitCoord
  have hb : bSerre - aSerre ≠ 0 := by norm_num [aSerre, bSerre]
  field_simp [hb]
  ring

/-- Evaluation of `chebPointPoly` at `t` is `chebPoint t`. -/
lemma chebPointPoly_eval (t : ℝ) : chebPointPoly.eval t = chebPoint t := by
  simp [chebPointPoly, chebPoint]

/-- `chebPointPoly.derivative` is the constant `(b−a)/2`. -/
lemma chebPointPoly_derivative : chebPointPoly.derivative = C ((bSerre - aSerre) / 2) := by
  simp [chebPointPoly]

/-- The affine map sends `[−1,1]` into `[aSerre,bSerre]`. -/
lemma chebPoint_mem_Icc_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    chebPoint t ∈ Set.Icc aSerre bSerre := by
  have hbpos : 0 < bSerre - aSerre := by norm_num [aSerre, bSerre]
  have hA : 0 < (bSerre - aSerre) / 2 := by positivity
  have hA' : 0 ≤ (bSerre - aSerre) / 2 := le_of_lt hA
  constructor
  · have hm : (bSerre - aSerre) / 2 * (-1 : ℝ) ≤ (bSerre - aSerre) / 2 * t :=
      mul_le_mul_of_nonneg_left ht.1 hA'
    unfold chebPoint
    nlinarith
  · have hm : (bSerre - aSerre) / 2 * t ≤ (bSerre - aSerre) / 2 * (1 : ℝ) :=
      mul_le_mul_of_nonneg_left ht.2 hA'
    unfold chebPoint
    nlinarith

/-- `chebPointPoly` has degree at most one. -/
lemma chebPointPoly_natDegree_le_one : chebPointPoly.natDegree ≤ 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [chebPointPoly, coeff_add, coeff_C, coeff_C_mul_X]
  have hN0 : N ≠ 0 := by omega
  have hN1 : N ≠ 1 := by omega
  simp [hN0, hN1]

/-- Markov's inequality on the Serre interval: `|P'| ≤ (2n²/(b−a))·M`
whenever `|P| ≤ M` on `[aSerre,bSerre]` and `deg P ≤ n`. -/
lemma markov_interval {P : Polynomial ℝ} {n : ℕ} (hdeg : P.natDegree ≤ n)
    {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |P.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc aSerre bSerre) :
    |P.derivative.eval x| ≤ (2 * (n : ℝ) ^ 2 / (bSerre - aSerre)) * M := by
  -- Pull back P to the unit interval: R(t) = P(chebPointPoly.eval t).
  let R : Polynomial ℝ := P.comp chebPointPoly
  let t : ℝ := unitCoord x
  have hbpos : 0 < bSerre - aSerre := by norm_num [aSerre, bSerre]
  have hApos : 0 < (bSerre - aSerre) / 2 := by positivity
  have hbne : bSerre - aSerre ≠ 0 := ne_of_gt hbpos
  -- R has degree at most n.
  have hdegR : R.natDegree ≤ n := by
    dsimp [R]
    calc
      (P.comp chebPointPoly).natDegree ≤ P.natDegree * chebPointPoly.natDegree := natDegree_comp_le
      _ ≤ n := by
        exact le_trans (Nat.mul_le_mul hdeg chebPointPoly_natDegree_le_one) (by simp)
  -- |R| ≤ M on [−1,1].
  have hbdR : ∀ t' : ℝ, t' ∈ Set.Icc (-1) 1 → |R.eval t'| ≤ M := by
    intro t' ht'
    dsimp [R]
    rw [eval_comp]
    rw [chebPointPoly_eval]
    exact hbd (chebPoint t') (chebPoint_mem_Icc_of_mem ht')
  have ht : t ∈ Set.Icc (-1) 1 := by
    dsimp [t]
    exact unitCoord_mem_Icc hx
  have hxeq : chebPointPoly.eval t = x := by
    dsimp [t]
    rw [chebPointPoly_eval]
    exact chebPoint_unitCoord_of_mem hx
  -- Apply the unit-interval Markov inequality to R.
  have hmain := Submission.Markov.markov_unit hdegR hM hbdR t ht
  -- Chain rule: R' = P'∘chebPointPoly · chebPointPoly', R'(t) = ((b−a)/2)·P'(x).
  have hder : R.derivative.eval t = ((bSerre - aSerre) / 2) * P.derivative.eval x := by
    dsimp [R]
    rw [derivative_comp, eval_mul]
    rw [chebPointPoly_derivative]
    simp [eval_comp, hxeq]
  have hder_abs : ((bSerre - aSerre) / 2) * |P.derivative.eval x| ≤ (n : ℝ) ^ 2 * M := by
    have h := hmain
    rw [hder] at h
    rwa [abs_mul, abs_of_pos hApos] at h
  -- Divide by (b−a)/2 > 0 and rearrange to the stated form.
  have hq0 : |P.derivative.eval x| ≤ (n : ℝ) ^ 2 * M / ((bSerre - aSerre) / 2) := by
    have h' : |P.derivative.eval x| * ((bSerre - aSerre) / 2) ≤ (n : ℝ) ^ 2 * M := by
      simpa [mul_comm] using hder_abs
    exact (le_div_iff₀ hApos).mpr h'
  calc
    |P.derivative.eval x| ≤ (n : ℝ) ^ 2 * M / ((bSerre - aSerre) / 2) := hq0
    _ = (2 * (n : ℝ) ^ 2 / (bSerre - aSerre)) * M := by
      field_simp [hbne]

end Submission.MarkovInterval
