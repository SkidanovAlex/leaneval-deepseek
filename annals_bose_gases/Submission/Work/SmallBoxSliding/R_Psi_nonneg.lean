import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

/-- The interior set `I₋` is closed — a finite intersection of the closed
coordinate half-space conditions `|((ℓd)•u).ofLp j| ≤ ½ℓ(1+d) − 2μ^{-1/3}` —
hence measurable. -/
lemma measurableSet_interiorSet (ℓ d μ : ℝ) :
    MeasurableSet (interiorSet ℓ d μ) := by
  unfold interiorSet
  rw [show {u : ℝ³ | ∀ j : Fin 3,
        |((ℓ * d) • u).ofLp j| ≤ 1 / 2 * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)}
      = ⋂ j : Fin 3, {u : ℝ³ |
        |((ℓ * d) • u).ofLp j| ≤ 1 / 2 * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)}
      by ext u; simp]
  exact MeasurableSet.iInter (fun j =>
    (isClosed_le (f := fun u : ℝ³ => |((ℓ * d) • u).ofLp j|)
      (by fun_prop) continuous_const).measurableSet)

/-- `R_Ψ ≥ 0`: the a-priori remainder is the `u`-integral over `I₋` of the
product `psiWeight c μ (n(u)/|B(u)|) · ∬ w_{1,B(u)}`, and both factors are
pointwise nonnegative on `I₋` (the hypotheses `hF`, `hker`), so the integral
of the nonnegative integrand is nonnegative.  No integrability hypothesis is
needed: the set integral is nonnegative by
`MeasureTheory.setIntegral_nonneg_of_ae_restrict`. -/
lemma R_Psi_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d μ c : ℝ) (n : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hF : ∀ u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ,
      0 ≤ Work.SmallBoxSliding.psiWeight c μ (n u / Work.SmallBoxSliding.boxVol ℓ d))
    (hker : ∀ u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ,
      0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y) :
    0 ≤ Work.SmallBoxSliding.R_Psi h M ℓ d μ c n := by
  unfold R_Psi
  apply setIntegral_nonneg_of_ae_restrict
  apply ae_restrict_of_forall_mem (measurableSet_interiorSet ℓ d μ)
  intro u hu
  exact mul_nonneg (hF u hu) (hker u hu)

end Work.SmallBoxSliding
