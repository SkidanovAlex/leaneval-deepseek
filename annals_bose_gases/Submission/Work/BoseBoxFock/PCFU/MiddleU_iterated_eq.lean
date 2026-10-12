import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.pairSum_MiddleV_star_MiddleU
import Submission.Work.BoseBoxFock.dict13RowShapeEqProd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The `L¹` input: the product-space `MiddleU` integrand

`Θ` is measurable, bounded and supported in the box `boxPow n (ellH v μ)`, `pinCond` and `MiddleU`
are bounded (`pinCond_bdd`, `MiddleU_bdd`), so the product integrand is bounded and supported in
`boxPow n ℓ × (boxL ℓ × boxL ℓ)`, a finite-measure set.  The support argument uses `i ≠ j`: if one
of the two momentum variables `q.2.1`, `q.2.2` lies outside `boxL ℓ`, then the *updated*
configuration `q.1[i↦q.2.1][j↦q.2.2]` has its `i`-th (resp. `j`-th) coordinate outside `boxL ℓ`,
hence leaves `boxPow n ℓ`, and the second `Θ`-factor vanishes. -/

/-- The support set: configurations in the box, the two momentum variables in `boxL`. -/
private def uBoxSet (n : ℕ) (ℓ : ℝ) : Set (Xn n × (E3 × E3)) :=
  Work.MB.boxPow n ℓ ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)

private lemma uBoxSet_measurableSet (n : ℕ) (ℓ : ℝ) : MeasurableSet (uBoxSet n ℓ) :=
  (Work.MB.measurableSet_boxPow n ℓ).prod
    ((Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ))

private lemma uBoxSet_measure_ne_top (n : ℕ) (ℓ : ℝ) :
    (volume : Measure (Xn n × (E3 × E3))) (uBoxSet n ℓ) ≠ ⊤ := by
  rw [uBoxSet, MeasureTheory.Measure.volume_eq_prod (Xn n) (E3 × E3),
    MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.volume_eq_prod E3 E3,
    MeasureTheory.Measure.prod_prod]
  exact ENNReal.mul_ne_top (Work.MB.volume_boxPow_lt_top n ℓ)
    (ENNReal.mul_ne_top
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne)

/-- **The product-space `MiddleU` integrand is integrable.**  Bounded by
`‖Θ‖·‖pinCond‖·‖MiddleU‖·‖Θ‖`, supported in `boxPow n ℓ × (boxL ℓ × boxL ℓ)`. -/
theorem MiddleU_prod_integrable {n : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {c : ℂ} {i j : Fin n} (hij : i ≠ j)
    {Θ : Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (ellH v μ)) :
    Integrable (fun q : Xn n × (E3 × E3) => star (Θ q.1) * pinCond v μ c (q.1 i)
      * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
      * Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)) volume := by
  classical
  obtain ⟨Cm, hCm0, hCm⟩ := MiddleU_bdd v h fc fu μ N
  obtain ⟨Cp, hCp0, hCp⟩ := pinCond_bdd v μ c
  obtain ⟨CT, hCT⟩ := hΘb
  have hmeas : Measurable (fun q : Xn n × (E3 × E3) => star (Θ q.1) * pinCond v μ c (q.1 i)
      * MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
      * Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)) := by
    have h1 : Measurable (fun q : Xn n × (E3 × E3) => star (Θ q.1)) :=
      continuous_star.measurable.comp (hΘm.comp measurable_fst)
    have h2 : Measurable (fun q : Xn n × (E3 × E3) => pinCond v μ c (q.1 i)) :=
      (pinCond_measurable v μ c).comp ((measurable_pi_apply i).comp measurable_fst)
    have h3 : Measurable (fun q : Xn n × (E3 × E3) =>
        MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2) := by
      have hMU := MiddleU_measurable v h fc fu μ N
      fun_prop
    have h4 : Measurable (fun q : Xn n × (E3 × E3) =>
        Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)) := by fun_prop
    exact ((h1.mul h2).mul h3).mul h4
  refine Work.MB.integrable_of_bdd_of_support (S := uBoxSet n (ellH v μ))
    (uBoxSet_measurableSet n (ellH v μ)) (uBoxSet_measure_ne_top n (ellH v μ))
    hmeas.aestronglyMeasurable
    (C := (max CT 0 * max Cp 0) * (max Cm 0 * max CT 0)) ?_ ?_
  · intro q
    have h1 : ‖Θ q.1‖ ≤ max CT 0 := (hCT q.1).trans (le_max_left _ _)
    have h2 : ‖pinCond v μ c (q.1 i)‖ ≤ max Cp 0 := (hCp _).trans (le_max_left _ _)
    have h3 : ‖MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2‖ ≤ max Cm 0 :=
      (hCm _ _ _).trans (le_max_left _ _)
    have h4 : ‖Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)‖ ≤ max CT 0 :=
      (hCT _).trans (le_max_left _ _)
    have h12 : ‖Θ q.1‖ * ‖pinCond v μ c (q.1 i)‖ ≤ max CT 0 * max Cp 0 :=
      mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
    have h123 : ‖Θ q.1‖ * ‖pinCond v μ c (q.1 i)‖
        * ‖MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2‖ ≤ (max CT 0 * max Cp 0) * max Cm 0 :=
      mul_le_mul h12 h3 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    calc ‖Θ q.1‖ * ‖pinCond v μ c (q.1 i)‖ * ‖MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2‖
          * ‖Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2)‖
        ≤ (max CT 0 * max Cp 0) * max Cm 0 * max CT 0 :=
          mul_le_mul h123 h4 (norm_nonneg _) (mul_nonneg (mul_nonneg (le_max_right _ _)
            (le_max_right _ _)) (le_max_right _ _))
      _ = (max CT 0 * max Cp 0) * (max Cm 0 * max CT 0) := by ring
  · intro q hq
    by_cases hx : q.1 ∈ Work.MB.boxPow n (ellH v μ)
    · by_cases hy : q.2.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      · by_cases hu : q.2.2 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
        · exact absurd ⟨hx, ⟨hy, hu⟩⟩ hq
        · have h0 : Function.update (Function.update q.1 i q.2.1) j q.2.2
              ∉ Work.MB.boxPow n (ellH v μ) := by
            intro hmem
            exact hu (by
              have hc := (Work.MB.mem_boxPow_iff.mp hmem) j
              rwa [Function.update_self] at hc)
          have hΘ0 : Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) = 0 :=
            Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
          simp only [hΘ0, mul_zero]
      · have h0 : Function.update (Function.update q.1 i q.2.1) j q.2.2
            ∉ Work.MB.boxPow n (ellH v μ) := by
          intro hmem
          exact hy (by
            have hc := (Work.MB.mem_boxPow_iff.mp hmem) i
            rwa [Function.update_of_ne hij, Function.update_self] at hc)
        have hΘ0 : Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) = 0 :=
          Function.notMem_support.mp fun hmem => h0 (hΘs hmem)
        simp only [hΘ0, mul_zero]
    · have hΘ0 : Θ q.1 = 0 := Function.notMem_support.mp fun hmem => hx (hΘs hmem)
      simp only [hΘ0, star_zero, zero_mul]

/-- **The iterated-to-product Fubini bridge for the `MiddleU` integrand.**  The
integral over `X n × (E³ × E³)` of `star (Θ x)·pinCond(x i)·MiddleU(x_j,y,u)·Θ(x[i↦y][j↦u])` equals
the iterated integral `∫x ∫y ∫u` of the same integrand.  Proof recipe: (1) `Θ` is measurable,
bounded and supported in `Work.MB.boxPow n (ellH v μ)` (a finite-measure set), `pinCond` is bounded
and `MiddleU` is bounded (`Work.BoseBoxFock.PCFU.MiddleU_bdd`); hence the product integrand is
integrable by `Work.MB.integrable_of_bdd_of_support` applied to
`Work.MB.boxPow n (ellH v μ) ×ˢ (boxL (ellH v μ) ×ˢ boxL (ellH v μ))` — the support step uses
`hij : i ≠ j` and `Work.MB.mem_boxPow_iff` (if the `i`-th or `j`-th momentum leaves `boxL`, the
updated configuration leaves `boxPow`, so the second `Θ` vanishes).  A verbatim template is
`Submission.Work.BoseBoxFock.PCFU.pairSum_MiddleV_star_MiddleU`'s private `PairU_integrable`.
(2) the general Fubini lemma `Work.BoseBoxFock.integral_iterated_eq_integral_prod`
(`Submission/Work/BoseBoxFock/dict13RowShapeEqProd.lean`) at `μ = ν = ρ = volume` turns the
product integral into the iterated one. -/
theorem MiddleU_iterated_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (c : ℂ)
    {Θ : Submission.BoseGases.X n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ)) :
    (∫ x : Submission.BoseGases.X n, ∫ y : EuclideanSpace ℝ (Fin 3),
        ∫ u : EuclideanSpace ℝ (Fin 3),
        star (Θ x) * Work.BoseBoxFock.pinCond v μ c (x i)
          * Work.BoseBoxFock.PCFU.MiddleU v h fc fu μ N (x j) y u
          * Θ (Function.update (Function.update x i y) j u))
      = ∫ q : Submission.BoseGases.X n
            × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
          star (Θ q.1) * Work.BoseBoxFock.pinCond v μ c (q.1 i)
            * Work.BoseBoxFock.PCFU.MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
            * Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) := by
  exact Work.BoseBoxFock.integral_iterated_eq_integral_prod
    (volume : Measure (Submission.BoseGases.X n))
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (f := fun q : Submission.BoseGases.X n
        × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      star (Θ q.1) * Work.BoseBoxFock.pinCond v μ c (q.1 i)
        * Work.BoseBoxFock.PCFU.MiddleU v h fc fu μ N (q.1 j) q.2.1 q.2.2
        * Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2))
    (MiddleU_prod_integrable hij hΘm hΘb hΘs)

end Work.BoseBoxFock.PCFU
