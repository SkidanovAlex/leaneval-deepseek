import Mathlib
open Real
open scoped BigOperators

/-!
# The elementary core of Lemma G (Schwartz, *The optimal paper Moebius band*)

This module formalizes, in pure real arithmetic, the "punchline" algebra of
Lemma G (Section 2.3, Equations (4)–(5) of the paper):  a band whose aspect
ratio `2λ` exceeds both of the radical lengths
`δ(t) = √(1+t²) + √(5+t²)` and `ν(t) = 2√(5+t²) − 2t` must satisfy `λ > √3`.

Nothing here refers to the Moebius band setup; it is a self-contained real
analysis fact.  The geometric reduction that produces the hypothesis
`2 * L > max (aspectDelta t) (aspectNu t)` for a real `t` is the content of
Lemma G proper (cutting the band open along a pre-bend and comparing arc
lengths), and is not part of this module.
-/

noncomputable section
namespace Submission.PaperBand

/-- `δ(t) = √(1+t²) + √(5+t²)`. -/
def aspectDelta (t : ℝ) : ℝ := Real.sqrt (1 + t^2) + Real.sqrt (5 + t^2)

/-- `ν(t) = 2√(5+t²) − 2t`. -/
def aspectNu (t : ℝ) : ℝ := 2 * Real.sqrt (5 + t^2) - 2 * t

/-- The critical value `t₀ = 1/√3` where `δ` and `ν` both equal `2√3`. -/
def tStar : ℝ := 1 / Real.sqrt 3

lemma hs3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
lemma hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
lemma hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3pos

lemma hdiv_sq : (1 / Real.sqrt 3)^2 = 1 / 3 := by
  rw [div_pow]
  rw [hs3]
  norm_num

lemma tStar_sq : tStar ^ 2 = 1 / 3 := by
  unfold tStar
  exact hdiv_sq

lemma six_div_sqrt3 : 6 / Real.sqrt 3 = 2 * Real.sqrt 3 := by
  rw [div_eq_iff_mul_eq hs3ne]
  rw [mul_assoc, ← pow_two, hs3]
  norm_num

lemma delta_tStar : aspectDelta tStar = 2 * Real.sqrt 3 := by
  unfold aspectDelta tStar
  rw [hdiv_sq]
  norm_num
  rw [← six_div_sqrt3]
  ring

lemma nu_tStar : aspectNu tStar = 2 * Real.sqrt 3 := by
  unfold aspectNu tStar
  rw [hdiv_sq]
  norm_num
  rw [← six_div_sqrt3]
  ring

/-- `δ` is nondecreasing to the right of `t₀`: if `t ≥ t₀` then `δ(t) ≥ 2√3`. -/
lemma delta_ge_of_ge (t : ℝ) (ht : tStar ≤ t) : 2 * Real.sqrt 3 ≤ aspectDelta t := by
  have htStar0 : 0 ≤ tStar := le_of_lt (by unfold tStar; positivity)
  have htsq : tStar ^ 2 ≤ t ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self htStar0 ht
  have h1 : 1 + tStar^2 ≤ 1 + t^2 := by nlinarith
  have h2 : 5 + tStar^2 ≤ 5 + t^2 := by nlinarith
  have hs1 : Real.sqrt (1 + tStar^2) ≤ Real.sqrt (1 + t^2) := Real.sqrt_le_sqrt h1
  have hs2 : Real.sqrt (5 + tStar^2) ≤ Real.sqrt (5 + t^2) := Real.sqrt_le_sqrt h2
  have hsum : Real.sqrt (1 + tStar^2) + Real.sqrt (5 + tStar^2) ≤ aspectDelta t := by
    unfold aspectDelta
    exact add_le_add hs1 hs2
  have hleft : 2 * Real.sqrt 3 = Real.sqrt (1 + tStar^2) + Real.sqrt (5 + tStar^2) := by
    simpa [aspectDelta] using delta_tStar.symm
  linarith

/-- `ν` is decreasing: if `t ≤ t₀` then `ν(t) ≥ 2√3`. -/
lemma nu_ge_of_le (t : ℝ) (ht : t ≤ tStar) : 2 * Real.sqrt 3 ≤ aspectNu t := by
  let u : ℝ := Real.sqrt (5 + t^2)
  have hut : 0 < u + t := by
    have hlt : Real.sqrt (t^2) < u := by
      dsimp [u]
      exact Real.sqrt_lt_sqrt (sq_nonneg t) (by nlinarith)
    have habs : Real.sqrt (t^2) = |t| := Real.sqrt_sq_eq_abs t
    rw [habs] at hlt
    have h1 : |t| + t < u + t := by nlinarith
    have h2 : 0 ≤ |t| + t := by
      have hneg : -t ≤ |t| := by simpa using (le_abs_self (-t))
      linarith
    exact lt_of_le_of_lt h2 h1
  have hQ : 0 < u + Real.sqrt 3 + t := by
    have hsum : 0 < u + t + Real.sqrt 3 := add_pos hut hs3pos
    nlinarith
  have hmain : Real.sqrt 3 ≤ u - t := by
    let F : ℝ := u - (Real.sqrt 3 + t)
    let Q : ℝ := u + Real.sqrt 3 + t
    have hu2 : u^2 = 5 + t^2 := by
      dsimp [u]
      rw [Real.sq_sqrt]
      positivity
    have hsq : (Real.sqrt 3 + t)^2 = 3 + 2 * Real.sqrt 3 * t + t^2 := by
      rw [add_sq, hs3]
    have hP : F * Q = 2 * (1 - Real.sqrt 3 * t) := by
      dsimp [F, Q]
      calc
        (u - (Real.sqrt 3 + t)) * (u + Real.sqrt 3 + t) = u^2 - (Real.sqrt 3 + t)^2 := by ring
        _ = (5 + t^2) - (3 + 2 * Real.sqrt 3 * t + t^2) := by rw [hu2, hsq]
        _ = 2 * (1 - Real.sqrt 3 * t) := by ring
    have ht3 : t * Real.sqrt 3 ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right ht (le_of_lt hs3pos)
      have hinv : tStar * Real.sqrt 3 = 1 := by
        unfold tStar
        simpa using (div_mul_cancel₀ (a := (1:ℝ)) hs3ne)
      rwa [hinv] at hmul
    have hPQ : 0 ≤ F * Q := by
      rw [hP]
      nlinarith [ht3]
    have hF : 0 ≤ F := by
      have hFQ : 0 ≤ Q * F := by simpa [mul_comm] using hPQ
      exact (mul_nonneg_iff_of_pos_left hQ).mp hFQ
    dsimp [F] at hF
    linarith
  unfold aspectNu
  dsimp [u] at hmain
  nlinarith [hmain]

/-- Main algebraic content of Lemma G: if `2λ` exceeds both radical lengths
`δ(t)` and `ν(t)` (i.e. `2λ > max(δ(t),ν(t))`), then `λ > √3`. -/
lemma aspect_bound {L t : ℝ} (h : 2 * L > max (aspectDelta t) (aspectNu t)) :
    Real.sqrt 3 < L := by
  have h2 : 2 * Real.sqrt 3 < 2 * L := by
    by_cases ht : t ≤ tStar
    · have hmax : aspectNu t ≤ max (aspectDelta t) (aspectNu t) := le_max_right _ _
      have hnu : 2 * Real.sqrt 3 ≤ aspectNu t := nu_ge_of_le t ht
      exact lt_of_le_of_lt (le_trans hnu hmax) h
    · have hδ : 2 * Real.sqrt 3 ≤ aspectDelta t := delta_ge_of_ge t (le_of_not_ge ht)
      have hmax : aspectDelta t ≤ max (aspectDelta t) (aspectNu t) := le_max_left _ _
      exact lt_of_le_of_lt (le_trans hδ hmax) h
  linarith



/-- The length chain of Lemma G (paper §2.3, equations (3) ⇒ (5)), abstracted
away from the band geometry:  suppose the two halves `H`, `D` of the cut-open
band satisfy
  * `√(1+t²) ≤ H`  (the pre-bend `T` is a shortest path, so `ℓ(T) ≤ ℓ(H)`),
  * `√(5+t²) < D`  (Lemma A1 strict: the broken side of the triangle is longer
    than the straight pre-bend),
  * `D − 2t = H`   and `H + D = 2a` (total boundary length `2a`),
then `2a > max(δ(t), ν(t))`.  Combined with `aspect_bound` this yields
`a > √3`.  All that remains for a full Lemma G is to produce such `H`, `D`
and `t` from the T-pattern geometry of a band. -/
lemma length_chain_bound {a H D t : ℝ} (hH : Real.sqrt (1 + t^2) ≤ H)
    (hD : Real.sqrt (5 + t^2) < D) (hDm : D - 2 * t = H) (hsum : H + D = 2 * a) :
    2 * a > max (aspectDelta t) (aspectNu t) := by
  have hδ2 : aspectDelta t < 2 * a := by
    have hδ : Real.sqrt (1 + t^2) + Real.sqrt (5 + t^2) < H + D :=
      add_lt_add_of_le_of_lt hH hD
    unfold aspectDelta
    linarith
  have hν2 : aspectNu t < 2 * a := by
    have hν : 2 * Real.sqrt (5 + t^2) - 2 * t < 2 * D - 2 * t := by
      nlinarith [hD]
    have hD2 : 2 * D - 2 * t = H + D := by nlinarith [hDm]
    unfold aspectNu
    linarith
  change max (aspectDelta t) (aspectNu t) < 2 * a
  rw [max_lt_iff]
  exact ⟨hδ2, hν2⟩


/-- The full algebraic conclusion of Lemma G once the length data `(H, D, t)`
is in hand:  `√3 < a`. -/
lemma lemmaG_punchline {a H D t : ℝ} (hH : Real.sqrt (1 + t^2) ≤ H)
    (hD : Real.sqrt (5 + t^2) < D) (hDm : D - 2 * t = H) (hsum : H + D = 2 * a) :
    Real.sqrt 3 < a :=
  aspect_bound (L := a) (length_chain_bound hH hD hDm hsum)

end Submission.PaperBand

end
