import Mathlib
import Submission.Work.Mostow.PhiMaxLine
import Submission.Work.Mostow.LinAlgMatrixIneqAux

/-!
# Derivative of `t ↦ ∑ k, matG (TwoPtLine x i j t k)`

Moving mass `t` from coordinate `j` to coordinate `i` keeps the sum of the coordinates fixed, so
the derivative of `∑ k, matG (TwoPtLine x i j t k)` at `t = 0` is the derivative of `matG` at
`x i` (weight `+1`) minus the derivative of `matG` at `x j` (weight `-1`), i.e.
`matPhi (x i) - matPhi (x j)`.

Since `x ∈ Kset n δ` with `δ > 0` we have `x k ≥ δ > 0` for every `k`, and (because `n ≥ 2`, so
that there is another index besides `k`) `x k < 1` as well; this is exactly what is needed for
`matG` to be differentiable at each `x k`.
-/

namespace Work.Mostow

noncomputable section

open scoped BigOperators

/-- `matG` is differentiable at `a` with derivative `matPhi a`, as long as `a ≠ 0` and `a ≠ 1`
(the two points where `Real.log x` respectively `Real.log (1 - x)` blow up). -/
private lemma hasDerivAt_matG_of {a : ℝ} (h0 : a ≠ 0) (h1 : 1 - a ≠ 0) :
    HasDerivAt matG (matPhi a) a := by
  have hA : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log x) ((1 / 2 : ℝ) * a⁻¹) a :=
    (Real.hasDerivAt_log h0).const_mul (1 / 2 : ℝ)
  have hB : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1 : ℝ) / (1 - a)) a := by
    have hsub : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1 : ℝ) a :=
      (hasDerivAt_id a).const_sub (1 : ℝ)
    exact hsub.log h1
  have hsum := hA.sub hB
  have hval : (1 / 2 : ℝ) * a⁻¹ - ((-1 : ℝ) / (1 - a)) = matPhi a := by
    unfold matPhi
    rw [one_div, one_div]
    field_simp
    ring
  rw [hval] at hsum
  change HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log x - Real.log (1 - x)) (matPhi a) a
  exact hsum

/-- Every coordinate of a point of `Kset n δ` with `δ > 0` and `n ≥ 2` lies strictly between
`0` and `1`. -/
private lemma mem_Kset_coord_bounds {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {x : Fin n → ℝ} (hx : x ∈ Kset n δ) (k : Fin n) : 0 < x k ∧ x k < 1 := by
  obtain ⟨hle, hsum⟩ := hx
  have hpos : 0 < x k := lt_of_lt_of_le hδ (hle k)
  refine ⟨hpos, ?_⟩
  have hcard : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  obtain ⟨l, hlk⟩ := Fintype.exists_ne_of_one_lt_card hcard k
  have hmem : l ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hlk, Finset.mem_univ l⟩
  have hle_sum : x l ≤ ∑ m ∈ Finset.univ.erase k, x m :=
    Finset.single_le_sum (fun m _ => le_of_lt (lt_of_lt_of_le hδ (hle m))) hmem
  have hsplit : (∑ m ∈ Finset.univ.erase k, x m) + x k = 1 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ k), hsum]
  linarith [hle l, hδ]

theorem hasDerivAt_sum_matG_twoPtLine {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {x : Fin n → ℝ} (hx : x ∈ Kset n δ) {i j : Fin n} (hij : i ≠ j) :
    HasDerivAt (fun t : ℝ => ∑ k, matG (TwoPtLine x i j t k))
      (matPhi (x i) - matPhi (x j)) 0 := by
  -- `matG` is differentiable at every coordinate of `x`
  have hmatG : ∀ k, HasDerivAt matG (matPhi (x k)) (TwoPtLine x i j 0 k) := by
    intro k
    obtain ⟨h0, h1⟩ := mem_Kset_coord_bounds hn hδ hx k
    have h := hasDerivAt_matG_of (ne_of_gt h0) (by linarith)
    simpa only [TwoPtLine_zero] using h
  -- differentiate the finite sum coordinatewise
  have hsum_deriv : HasDerivAt (∑ k, fun t : ℝ => matG (TwoPtLine x i j t k))
      (∑ k, matPhi (x k) * ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0)))
      0 := by
    apply HasDerivAt.sum
    intro k _
    exact (hmatG k).comp 0 (hasDerivAt_TwoPtLine x i j k)
  have hderiv : HasDerivAt (fun t : ℝ => ∑ k, matG (TwoPtLine x i j t k))
      (∑ k, matPhi (x k) * ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0)))
      0 := by
    rw [show (fun t : ℝ => ∑ k, matG (TwoPtLine x i j t k))
        = (∑ k, fun t : ℝ => matG (TwoPtLine x i j t k)) from by
      funext t; simp]
    exact hsum_deriv
  -- the linear combination of the `matPhi (x k)` collapses to `matPhi (x i) - matPhi (x j)`
  have hkey : (∑ k, matPhi (x k) * ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0)))
      = matPhi (x i) - matPhi (x j) := by
    have h1 : (∑ k, matPhi (x k)
          * ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0)))
        = ∑ k, (matPhi (x k) * (if k = i then (1 : ℝ) else 0)
            - matPhi (x k) * (if k = j then (1 : ℝ) else 0)) :=
      Finset.sum_congr rfl (fun k _ => by ring)
    rw [h1, Finset.sum_sub_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hkey] at hderiv
  exact hderiv

end

end Work.Mostow
