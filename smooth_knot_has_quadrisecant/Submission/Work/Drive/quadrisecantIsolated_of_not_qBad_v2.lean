import Mathlib
import Submission.Work.Drive.qwDefs

namespace Work.Drive

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

open LeanEval.KnotTheory.Quadrisecant

/-! ## Helper lemmas for the passage from the bad set to quadrisecant isolation

This is the *strict-box* version of `Work.Drive.quadrisecantIsolated_of_not_qBad`: the compact box
`qBox k` bounds the total length of a window by `2π - 1/(k+1)`, so the separation level `k` has to be
chosen large enough to also make `1/(k+1) ≤ 2π - (b - a)`, not merely large enough for the three
gaps. -/

/-- A `period`-periodic curve is invariant under shifts by integer multiples of the period. -/
private lemma periodic_add_int_mul {E : Type*} [AddCommGroup E] {f : ℝ → E}
    (hper : Function.Periodic f period) (n : ℤ) (x : ℝ) :
    f (x + (n : ℝ) * period) = f x := by
  have h := hper.zsmul n x
  rwa [zsmul_eq_mul] at h

/-- Cancellation in a real vector space: if `α + β = 1`, then `α • x + β • y - x = β • (y - x)`. -/
private lemma smul_add_smul_sub {E : Type*} [AddCommGroup E] [Module ℝ E]
    {α β : ℝ} (h : α + β = 1) (x y : E) : (α • x + β • y) - x = β • (y - x) := by
  have hα : α = 1 - β := by linarith
  rw [hα, sub_smul, one_smul, smul_sub]
  abel

private lemma qU_qPar (r : ℝ → Space) (c : Coeff) (a z w b : ℝ) :
    qU r (c, qPar a z w b) = pertV r c z - pertV r c a := by
  simp [qU, qPZ, qPA]

private lemma qV_qPar (r : ℝ → Space) (c : Coeff) (a z w b : ℝ) :
    qV r (c, qPar a z w b) = pertV r c w - pertV r c a := by
  simp [qV, qPW, qPA]

private lemma qS_qPar (r : ℝ → Space) (c : Coeff) (a z w b : ℝ) :
    qS r (c, qPar a z w b) = pertV r c b - pertV r c a := by
  simp [qS, qPB, qPA]

private lemma qPartial_qPar (r : ℝ → Space) (c : Coeff) (a z w b : ℝ) :
    qPartial r (c, qPar a z w b) = quadPartial (pertV r c) a z w b := by
  simp [qPartial]

/-- The Gram determinant of the partials vanishes as soon as the partials themselves are
linearly dependent (`WithLp.toLp` does not change linear independence). -/
private lemma qGram_eq_zero_of_not_li {r : ℝ → Space} {p : Coeff × QP}
    (h : ¬ LinearIndependent ℝ (qPartial r p)) : qGram r p = 0 := by
  rw [qGram_eq_zero_iff]
  intro hLI
  exact h (LinearIndependent.of_comp (WithLp.linearEquiv 2 ℝ (Space × Space)).symm.toLinearMap hLI)

/-- The four partials of the collinearity map are invariant under a common shift of the four
parameters by an integer multiple of the period. -/
private lemma quadPartial_add_int_mul {f : ℝ → Space} (hper : Function.Periodic f period)
    (n : ℤ) (a z w b : ℝ) :
    quadPartial f (a + (n:ℝ)*period) (z + (n:ℝ)*period) (w + (n:ℝ)*period)
        (b + (n:ℝ)*period) = quadPartial f a z w b := by
  have hv : Function.Periodic (deriv f) period := periodic_deriv' hper
  funext i
  fin_cases i <;>
    simp only [quadPartial, velocity, periodic_add_int_mul hper n, periodic_add_int_mul hv n]

/-- Membership in the compact window box, in the coordinates of `qPar`.  The last hypothesis is the
*strict* total-length bound of `qBox`. -/
private lemma qPar_mem_qBox {A Z W B : ℝ} {k : ℕ} (hA : 0 ≤ A)
    (hA' : A ≤ 2 * Real.pi) (h1 : 1/(k+1) ≤ Z - A) (h2 : 1/(k+1) ≤ W - Z)
    (h3 : 1/(k+1) ≤ B - W) (h4 : B - A ≤ 2 * Real.pi - 1/(k+1)) : qPar A Z W B ∈ qBox k := by
  have hAq : qA (qPar A Z W B) = A := by simp
  have hZq : qZ (qPar A Z W B) = Z := by simp
  have hWq : qW (qPar A Z W B) = W := by simp
  have hBq : qB (qPar A Z W B) = B := by simp
  simp only [qBox, Set.mem_ofPred_eq, hAq, hZq, hWq, hBq]
  exact ⟨⟨hA, hA'⟩, h1, h2, h3, h4⟩


open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **The passage from the bad set to quadrisecant isolation** (strict-box version).

Let `c ∈ Kv ρ` be a coefficient for which the perturbed curve `pertV r c` is a smooth knot and which
avoids every bad set `qBad r ρ k` (`k : ℕ`).  Then `pertV r c` is *quadrisecant-isolated*: at every
collinear quadruple `r a, r z, r w, r b` of one period window with `r z` and `r w` strictly inside
the chord from `r a` to `r b`, the four partials of the four-point collinearity map are linearly
independent.

Sketch of the bookkeeping.  Given such a quadruple, `IsMiddleOnChord` (twice) makes the four
perturbed points collinear, i.e. `triplet r c τ = 0` for the window `τ` of the four parameters.
Shifting all four parameters by a common multiple of the period (which leaves the perturbed curve
and hence the collinearity and the partials unchanged, using the periodicity of `pertV r c`) puts the
first parameter into `[0, 2π)`, and the three gaps `z - a`, `w - z`, `b - w` are positive with total
length `b - a < 2π`; choosing `k` so large that `1/(k+1)` is at most both the smallest gap and
`2π - (b - a)` puts the shifted window into `qBox k` (whose total-length bound is the strict
`≤ 2π - 1/(k+1)`).  If the partials were not independent, the Gram determinant `qGram` would vanish
(by `Work.Drive.qGram_eq_zero_iff`), so `c ∈ qBad r ρ k`, contradicting the hypothesis. -/
theorem quadrisecantIsolated_of_not_qBad_v2 {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ}
    {c : Coeff} (hc : c ∈ Kv ρ) (hS : IsSmoothKnot (pertV r c))
    (h : ∀ k : ℕ, c ∉ qBad r ρ k) : QuadrisecantIsolated (pertV r c) := by
  intro a z w b hza hwz hbw hlen hmidz hmidw
  have hper : Function.Periodic (pertV r c) period := hS.periodic
  -- The two middle conditions, with real parameters
  have hzoc : pertV r c z ∈ openSegment ℝ (pertV r c a) (pertV r c b) := by
    have h' := hmidz
    simp only [IsMiddleOnChord] at h'
    rw [knotMap_coe_of_periodic hper z, knotMap_coe_of_periodic hper a,
      knotMap_coe_of_periodic hper b] at h'
    exact h'
  have hwoc : pertV r c w ∈ openSegment ℝ (pertV r c a) (pertV r c b) := by
    have h' := hmidw
    simp only [IsMiddleOnChord] at h'
    rw [knotMap_coe_of_periodic hper w, knotMap_coe_of_periodic hper a,
      knotMap_coe_of_periodic hper b] at h'
    exact h'
  obtain ⟨α, β, hα, hβ, hαβ, hzeq⟩ := hzoc
  obtain ⟨α', β', hα', hβ', hα'β', hweq⟩ := hwoc
  -- Shift the window so that the first parameter lies in `[0, period)`
  obtain ⟨n, hn⟩ := exists_zsmul_add_mem_Ico a
  have hn' : a + (n : ℝ) * period ∈ Set.Ico 0 period := by rwa [zsmul_eq_mul] at hn
  have hperS : ∀ x : ℝ, pertV r c (x + (n : ℝ) * period) = pertV r c x :=
    fun x => periodic_add_int_mul hper n x
  set A : ℝ := a + (n : ℝ) * period with hA
  set Z : ℝ := z + (n : ℝ) * period with hZ
  set W : ℝ := w + (n : ℝ) * period with hW
  set B : ℝ := b + (n : ℝ) * period with hB
  have hBA : B - A = b - a := by rw [hB, hA]; ring
  have hZA : Z - A = z - a := by rw [hZ, hA]; ring
  have hWZ : W - Z = w - z := by rw [hW, hZ]; ring
  have hBW : B - W = b - w := by rw [hB, hW]; ring
  have hperiod : period = 2 * Real.pi := rfl
  have hlen' : b - a < 2 * Real.pi := by rw [← hperiod]; exact hlen
  -- Choose the separation level `k` from the three positive gaps *and* the total-length slack
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt
    (show (0:ℝ) < min (min (z - a) (min (w - z) (b - w))) (2 * Real.pi - (b - a)) from
      lt_min (lt_min hza (lt_min hwz hbw)) (by linarith [hlen']))
  have hm1 : (1:ℝ) / ((k:ℝ) + 1) ≤ min (z - a) (min (w - z) (b - w)) :=
    le_trans (le_of_lt hk) (min_le_left _ _)
  have hm2 : (1:ℝ) / ((k:ℝ) + 1) ≤ 2 * Real.pi - (b - a) :=
    le_trans (le_of_lt hk) (min_le_right _ _)
  have hk1 : (1:ℝ) / (k + 1) ≤ z - a := by
    simpa only [Nat.cast_add, Nat.cast_one] using le_trans hm1 (min_le_left _ _)
  have hk2 : (1:ℝ) / (k + 1) ≤ w - z := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      le_trans hm1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hk3 : (1:ℝ) / (k + 1) ≤ b - w := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      le_trans hm1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hk4 : (1:ℝ) / (k + 1) ≤ 2 * Real.pi - (b - a) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hm2
  -- Suppose the four partials were dependent
  by_contra hnolI
  -- The two middle points of the shifted window are interior points of the shifted chord
  have hU : qU r (c, qPar A Z W B) = β • qS r (c, qPar A Z W B) := by
    rw [qU_qPar, qS_qPar, hA, hZ, hB, hperS z, hperS a, hperS b, ← hzeq]
    exact smul_add_smul_sub hαβ _ _
  have hV : qV r (c, qPar A Z W B) = β' • qS r (c, qPar A Z W B) := by
    rw [qV_qPar, qS_qPar, hA, hW, hB, hperS w, hperS a, hperS b, ← hweq]
    exact smul_add_smul_sub hα'β' _ _
  -- Shift invariance of the partials, hence the vanishing of the Gram determinant
  have hqp : qPartial r (c, qPar A Z W B) = quadPartial (pertV r c) a z w b := by
    rw [qPartial_qPar, hA, hZ, hW, hB, quadPartial_add_int_mul hper n a z w b]
  have hgram : qGram r (c, qPar A Z W B) = 0 := by
    refine qGram_eq_zero_of_not_li ?_
    rw [hqp]
    exact hnolI
  -- The triplet of pairwise collinearity conditions vanishes
  have hcross1 : cross3 (qU r (c, qPar A Z W B)) (qS r (c, qPar A Z W B)) = 0 := by
    rw [hU, cross3_smul_left, cross3_self, smul_zero]
  have hcross2 : cross3 (qU r (c, qPar A Z W B)) (qV r (c, qPar A Z W B)) = 0 := by
    rw [hU, hV, cross3_smul_left, cross3_smul_right, cross3_self, smul_zero, smul_zero]
  have hcross3 : cross3 (qV r (c, qPar A Z W B)) (qS r (c, qPar A Z W B)) = 0 := by
    rw [hV, cross3_smul_left, cross3_self, smul_zero]
  have htriplet : triplet r (c, qPar A Z W B) = 0 := by
    simp only [triplet, hcross1, hcross2, hcross3]
    rfl
  -- The shifted window lies in the compact box `qBox k`
  have hbox : qPar A Z W B ∈ qBox k :=
    qPar_mem_qBox hn'.1 (by rw [← hperiod]; linarith [hn'.2]) (by rw [hZA]; exact hk1)
      (by rw [hWZ]; exact hk2) (by rw [hBW]; exact hk3)
      (by rw [hBA]; linarith [hk4])
  exact h k ⟨hc, qPar A Z W B, hbox, htriplet, hgram⟩

end Work.Drive
