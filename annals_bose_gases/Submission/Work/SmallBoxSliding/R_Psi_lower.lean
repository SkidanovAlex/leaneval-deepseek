import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

/-- The a-priori remainder is bounded below by the `c₁`-multiple of the
`(n/|B| − μ)²`-moment of the localised mass: this is the pointwise
Fenchel-type estimate `hF` integrated against the non-negative weight
`∬ w_{1,B(u)}` (`hker`). -/
lemma R_Psi_lower {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d μ c c₁ : ℝ) (n : EuclideanSpace ℝ (Fin 3) → ℝ) (hc₁ : 0 ≤ c₁)
    (hF : ∀ u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ,
      c₁ * (n u / Work.SmallBoxSliding.boxVol ℓ d - μ) ^ 2
        ≤ Work.SmallBoxSliding.psiWeight c μ (n u / Work.SmallBoxSliding.boxVol ℓ d))
    (hker : ∀ u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ,
      0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
    (hint : MeasureTheory.IntegrableOn (fun u =>
      (n u / Work.SmallBoxSliding.boxVol ℓ d - μ) ^ 2 *
        (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
      (Work.SmallBoxSliding.interiorSet ℓ d μ))
    (hintPsi : MeasureTheory.IntegrableOn (fun u =>
      Work.SmallBoxSliding.psiWeight c μ (n u / Work.SmallBoxSliding.boxVol ℓ d) *
        (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
      (Work.SmallBoxSliding.interiorSet ℓ d μ)) :
    c₁ * (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
      (n u / Work.SmallBoxSliding.boxVol ℓ d - μ) ^ 2 *
        (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
      ≤ Work.SmallBoxSliding.R_Psi h M ℓ d μ c n := by
  -- the interior set is closed, hence measurable (it is a finite intersection
  -- of coordinatewise `|·| ≤ const` conditions)
  have hclosed : IsClosed (interiorSet ℓ d μ) := by
    unfold interiorSet
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have hms : MeasurableSet (interiorSet ℓ d μ) := hclosed.measurableSet
  -- pull the constant `c₁` inside the set integral
  unfold R_Psi
  rw [← MeasureTheory.integral_const_mul]
  -- compare the two integrands pointwise on the interior set
  refine MeasureTheory.integral_mono_ae (hint.const_mul c₁) hintPsi ?_
  apply MeasureTheory.ae_restrict_of_forall_mem hms
  intro u hu
  have h1 := hF u hu
  have h2 : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y := hker u hu
  calc c₁ * ((n u / boxVol ℓ d - μ) ^ 2 *
        (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
      = (c₁ * (n u / boxVol ℓ d - μ) ^ 2) *
        (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by ring
    _ ≤ psiWeight c μ (n u / boxVol ℓ d) *
        (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y) :=
        mul_le_mul_of_nonneg_right h1 h2

end Work.SmallBoxSliding
