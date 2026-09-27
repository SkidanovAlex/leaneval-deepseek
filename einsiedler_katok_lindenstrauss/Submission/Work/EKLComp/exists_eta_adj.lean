import Mathlib

namespace Work.EKLComp

/-- Continuity/perturbation form of the statement, phrased for matrices seen as
functions `Fin 3 → Fin 3 → ℝ` so that the product (sup) metric is available.

If `det M = 1` and the `(q,p)` entry of the adjugate of `M` is nonzero, then for
every `η > 0` a small enough entrywise perturbation `G` of `M` keeps
`G.adjugate q p` away from `0` and makes `|(1 - G.det) / (G.adjugate q p)| ≤ η/2`.
This is just continuity of `G ↦ (G.adjugate q p, G.det)` at `M`, together with
`M.det = 1` and `M.adjugate q p ≠ 0`. -/
private lemma exists_eta_adj_aux (M : Fin 3 → Fin 3 → ℝ) (hMdet : Matrix.det M = 1)
    {q p : Fin 3} (hMadj : Matrix.adjugate M q p ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ G : Fin 3 → Fin 3 → ℝ, (∀ i j, |G i j - M i j| < δ) →
      Matrix.adjugate G q p ≠ 0 ∧
        |(1 - Matrix.det G) / (Matrix.adjugate G q p)| ≤ η / 2 := by
  have hc : 0 < |Matrix.adjugate M q p| := abs_pos.mpr hMadj
  -- The two relevant maps are continuous (polynomials in the entries).
  have hadj_cont : Continuous (fun G : Fin 3 → Fin 3 → ℝ => Matrix.adjugate G q p) :=
    (continuous_apply_apply q p).comp continuous_id.matrix_adjugate
  have hdet_cont : Continuous (fun G : Fin 3 → Fin 3 → ℝ => Matrix.det G) :=
    continuous_id.matrix_det
  -- Extract explicit moduli of continuity at `M`.
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    (Metric.continuousAt_iff.mp (hadj_cont.continuousAt (x := M)))
      (|Matrix.adjugate M q p| / 2) (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    (Metric.continuousAt_iff.mp (hdet_cont.continuousAt (x := M)))
      (η * |Matrix.adjugate M q p| / 4) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro G hG
  -- Entrywise closeness upgrades to closeness in the sup metric.
  have hdist : dist G M < min δ₁ δ₂ := by
    rw [dist_pi_lt_iff (lt_min hδ₁pos hδ₂pos)]
    intro i
    rw [dist_pi_lt_iff (lt_min hδ₁pos hδ₂pos)]
    intro j
    simpa [Real.dist_eq] using hG i j
  have hδ₁' : dist G M < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hδ₂' : dist G M < δ₂ := lt_of_lt_of_le hdist (min_le_right _ _)
  have hadj_b : |Matrix.adjugate G q p - Matrix.adjugate M q p| <
      |Matrix.adjugate M q p| / 2 := by
    have h := hδ₁ hδ₁'
    rwa [Real.dist_eq] at h
  have hdet_b : |Matrix.det G - Matrix.det M| <
      η * |Matrix.adjugate M q p| / 4 := by
    have h := hδ₂ hδ₂'
    rwa [Real.dist_eq] at h
  -- The adjugate entry stays bounded away from zero.
  have hGadj_gt : |Matrix.adjugate M q p| / 2 < |Matrix.adjugate G q p| := by
    have h2 := abs_abs_sub_abs_le_abs_sub (Matrix.adjugate G q p) (Matrix.adjugate M q p)
    have h3 : |(|Matrix.adjugate G q p| - |Matrix.adjugate M q p|)| <
        |Matrix.adjugate M q p| / 2 := lt_of_le_of_lt h2 hadj_b
    have h4 := abs_lt.mp h3
    linarith [h4.2]
  constructor
  · intro hzero
    rw [hzero, abs_zero] at hGadj_gt
    linarith [hc]
  · have hpos : 0 < |Matrix.adjugate G q p| :=
      lt_of_lt_of_le (by linarith [hc]) hGadj_gt.le
    have hnum : |1 - Matrix.det G| < η * |Matrix.adjugate M q p| / 4 := by
      have h1 : (1 : ℝ) - Matrix.det G = -(Matrix.det G - Matrix.det M) := by
        rw [hMdet]; ring
      rw [h1, abs_neg]
      exact hdet_b
    rw [abs_div]
    apply le_of_lt
    rw [div_lt_iff₀ hpos]
    nlinarith [hGadj_gt, hnum, hη, hc]

/-- Perturbation lemma: for a unimodular `3 × 3` matrix `M` and a nonzero entry
`M.adjugate q p` of its adjugate, small entrywise perturbations `G` of `M` keep
`G.adjugate q p ≠ 0`, and since `det M = 1` the quantity
`|(1 - G.det) / (G.adjugate q p)|` becomes arbitrarily small (specifically at
most `η/2`). -/
lemma exists_eta_adj (M : Matrix (Fin 3) (Fin 3) ℝ) (hMdet : M.det = 1) {q p : Fin 3}
    (hMadj : M.adjugate q p ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ G : Matrix (Fin 3) (Fin 3) ℝ, (∀ i j, |G i j - M i j| < δ) →
      G.adjugate q p ≠ 0 ∧ |(1 - G.det) / (G.adjugate q p)| ≤ η / 2 := by
  exact exists_eta_adj_aux M hMdet hMadj η hη

end Work.EKLComp
