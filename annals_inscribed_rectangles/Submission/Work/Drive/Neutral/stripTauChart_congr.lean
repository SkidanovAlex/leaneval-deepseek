import Mathlib
import Submission.Work.Drive.Neutral.stripTauChart

namespace Work.Drive.Neutral

/-- The unit normalisation `tauE` of the factorised direction depends only on the value of `G` at the
point. -/
lemma tauE_congr {G G' : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p : EuclideanSpace ℝ (Fin 2)} (h : G p = G' p) : tauE G p = tauE G' p := by
  rw [tauE, tauE, h]

/-- The `ℝ/ℤ`-valued third coordinate of the clamped data depends only on the value of `G` at the
point. -/
lemma tauS_congr {G G' : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p : EuclideanSpace ℝ (Fin 2)} (h : G p = G' p) : tauS G p = tauS G' p := by
  unfold tauS
  exact circOf_congr (tauE_norm G p) (tauE_norm G' p) (tauE_congr h)

/-- The clamped configuration data depends only on the value of `G` at the point. -/
lemma tauData_congr {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {G G' : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ} {σ₀ : ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (h : G p = G' p) :
    tauData hγ hγne G σ₀ p = tauData hγ hγne G' σ₀ p := by
  by_cases hc : 0 < (G p).1 ∧ ‖(G p).2.1‖ ≤ 1
  · have hc' : 0 < (G' p).1 ∧ ‖(G' p).2.1‖ ≤ 1 := by rwa [← h]
    rw [tauData_eq_of_good hγ hγne G σ₀ hc, tauData_eq_of_good hγ hγne G' σ₀ hc']
    simp only [h, tauS_congr h]
  · have hc' : ¬ (0 < (G' p).1 ∧ ‖(G' p).2.1‖ ≤ 1) := by rwa [← h]
    rw [tauData, tauData, dif_neg hc, dif_neg hc']

/-- **The `τ`-chart only depends on the data at the point.**  Two factorised data maps `G`, `G'` that
agree at `p` give the same point of the capping space: the clamped data `tauData` is a function of
the value `G p` alone (the side condition `0 < r ∧ ‖d‖ ≤ 1` is decided there, and the `ℝ/ℤ` third
coordinate is `circOf` applied to the unit normalisation of the direction). -/
theorem stripTauChart_congr (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {G G' : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ} {σ₀ : ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (h : G p = G' p) :
    Work.Drive.Neutral.stripTauChart hγ hγne G σ₀ p = Work.Drive.Neutral.stripTauChart hγ hγne G' σ₀ p := by
  unfold stripTauChart
  exact congrArg (fun z : ConfigPiece => Quotient.mk'' (Sum.inl z))
    (Subtype.ext (tauData_congr hγ hγne h))

end Work.Drive.Neutral
