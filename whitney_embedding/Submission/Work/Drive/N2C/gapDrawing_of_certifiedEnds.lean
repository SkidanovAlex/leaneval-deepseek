import Mathlib
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Drive.N2C.isLevelIsotopy_transport
import Submission.Work.Drive.N2C.isLevelIsotopy_windowMovie
import Submission.Work.Drive.N2C.isLevelIsotopy_blend
import Submission.Work.Drive.N2C.levelCurves_transport
import Submission.Work.Drive.N2C.levelCurves_reverse
import Submission.Work.Drive.N2C.gapEngine

namespace Work.Drive.N2C

theorem gapDrawing_of_certifiedEnds {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {Φ : ℝ × M → M}
    (hΦsm : ContMDiff (((modelWithCornersSelf ℝ ℝ)).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    {lo' lo h₁ u₁ m₁ m₂ u₂ h₂ hi hi' : ℝ}
    (hord : lo' < lo ∧ lo < h₁ ∧ h₁ < u₁ ∧ u₁ < m₁ ∧ m₁ ≤ m₂ ∧ m₂ < u₂ ∧ u₂ < h₂ ∧
      h₂ < hi ∧ hi < hi')
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc lo' hi' → f x + t ∈ Set.Icc lo' hi' →
      f (Φ (t, x)) = f x + t)
    (hreg : ∀ x : M, f x ∈ Set.Icc lo' hi' → ¬ Work.Drive.Morse.IsCritical f x)
    {g₁ g₂ : M → EuclideanSpace ℝ (Fin 3)}
    (hg₁ : Work.Drive.N2.GoodDrawingOn f (Set.Ioo lo' m₁) g₁)
    (hg₂ : Work.Drive.N2.GoodDrawingOn f (Set.Ioo m₂ hi') g₂)
    (hc₁ : Work.Drive.N2C.IsCertifiedAt f u₁ g₁) (hc₂ : Work.Drive.N2C.IsCertifiedAt f u₂ g₂) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      Work.Drive.N2.GoodDrawingOn f (Set.Ioo lo hi) G ∧
      (∀ x : M, f x ∈ Set.Ioo lo h₁ → G x = g₁ x) ∧
      (∀ x : M, f x ∈ Set.Ioo h₂ hi → G x = g₂ x) :=
  Work.Drive.N2C.H7.gapDrawing_of_certifiedEnds hf hΦsm hΦ0 hΦcomp hord hΦf hreg hg₁ hg₂ hc₁ hc₂

end Work.Drive.N2C
