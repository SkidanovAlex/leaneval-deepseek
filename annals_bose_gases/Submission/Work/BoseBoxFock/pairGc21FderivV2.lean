import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGc21_continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGc21FderivV2` — the parametric derivative of the clean `pairG21` fibre

The clean fibre `pairGc21 ℓ p hp Θ₀ A u y` (`Work.BoseBoxFock.pairGCore`) is the set integral

    ∫ z in triBox ℓ p, star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2
      * Θ₀ (insertCoord2 p y u z.2)

over the triple box.  Only the last factor depends on the parameter `u` (which is inserted in slot
`p.2` of the second configuration); the remaining factor is a *measurable, bounded* function of the
integration variable `z` (the kernel `A` is only assumed measurable and bounded).  This module
therefore uses the parametric-differentiation lemma with a bounded measurable multiplier
`Work.BoseBoxFock.hasFDerivAt_integral_mul_const` (`pairGAssembly`), which is exactly shaped for
that situation: it differentiates under the integral with a dominating constant.

The parameter derivative of the sliced factor is computed by the chain rule, the inner affine map
`u' ↦ insertCoord2 p y u' x''` having the constant continuous-linear derivative `slotIns p.2`
(the insertion map of `Zero`-padded slot vectors, `ContinuousLinearMap.pi` of `Pi.single`); the
crucial identification is `slotIns i (single j 1) = slotDirVec i j`, so the derivative in the
coordinate-`j` direction is exactly the `fderiv Θ₀` evaluated on the slot direction vector.

All lemmas are `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- The ambient space of the triple box: the two kernel coordinates and the complementary
`n - 2` coordinates. -/
abbrev PgZ {n : ℕ} (p : Fin n × Fin n) : Type :=
  (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)

/-! ## 1. The slot insertion as a continuous linear map -/

/-- **The insertion of a vector into a single slot**, as a continuous linear map: it sends `v` to
the configuration which is `v` at slot `i` and `0` everywhere else. -/
noncomputable def slotIns {n : ℕ} (i : Fin n) : E3 →L[ℝ] Xn n :=
  ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ E3))

lemma slotIns_apply {n : ℕ} (i : Fin n) (v : E3) :
    slotIns i v = Function.update (0 : Xn n) i v := by
  funext k
  rw [slotIns, ContinuousLinearMap.pi_apply]
  by_cases hk : k = i
  · subst hk; rw [Pi.single_eq_same, ContinuousLinearMap.id_apply, Function.update_self]
  · rw [Pi.single_eq_of_ne hk, Function.update_of_ne hk]; rfl

/-- **The insertion map at the unit coordinate vector is the slot direction vector** — the
identification that makes the chain-rule expression of the derivative equal to the
`slotDirVec`-spelling of the statement. -/
lemma slotIns_single {n : ℕ} (i : Fin n) (j : Fin 3) :
    slotIns i (EuclideanSpace.single j (1 : ℝ)) = slotDirVec i j := by
  rw [slotIns_apply]; rfl

/-! ## 2. The affine map `u' ↦ insertCoord2 p y u' x''` and its derivative -/

lemma hasFDerivAt_insertCoord2_snd {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    (y : E3) (x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) (u : E3) :
    HasFDerivAt (fun u' : E3 => insertCoord2 p y u' x'') (slotIns p.2) u := by
  have hfun : (fun u' : E3 => insertCoord2 p y u' x'')
      = Function.update (insertCoord2 p y (0 : E3) x'') p.2 := by
    funext u' k
    rw [Function.update_apply]
    by_cases h2 : k = p.2
    · rw [if_pos h2, h2, insertCoord2_apply_other hp]
    · rw [if_neg h2]
      by_cases h1 : k = p.1
      · rw [h1, insertCoord2_apply_self, insertCoord2_apply_self]
      · rw [insertCoord2_apply_ne h1 h2, insertCoord2_apply_ne h1 h2]
  rw [hfun]
  exact hasFDerivAt_update _ _

/-- **The chain rule for the sliced state**: for a smooth `Θ` the slice
`u' ↦ Θ (insertCoord2 p y u' x'')` has derivative `fderiv Θ (insertCoord2 p y u x'') ∘ slotIns p.2`
at every `u`. -/
lemma hasFDerivAt_comp_insertCoord2_snd {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {Θ : Xn n → ℂ} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) (y : E3)
    (x'' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) (u : E3) :
    HasFDerivAt (fun u' : E3 => Θ (insertCoord2 p y u' x''))
      ((fderiv ℝ Θ (insertCoord2 p y u x'')).comp (slotIns p.2)) u := by
  have h1 : HasFDerivAt Θ (fderiv ℝ Θ (insertCoord2 p y u x'')) (insertCoord2 p y u x'') :=
    (hΘ.differentiable (by simp) _).hasFDerivAt
  have h2 : HasFDerivAt (fun u' : E3 => insertCoord2 p y u' x'') (slotIns p.2) u :=
    hasFDerivAt_insertCoord2_snd hp y x'' u
  exact h1.comp u h2

/-! ## 3. The fibre as a parametric integral with a bounded measurable multiplier -/

/-- **The clean fibre as an integral of a smooth slice against the bounded multiplier
`pairGc21Factor`** — the form in which the parametric-differentiation lemma
`hasFDerivAt_integral_mul_const` applies. -/
theorem pairGc21_eq_integral_factor {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ₀ : Xn n → ℂ) (A : E3 → ℂ) (u y : E3) :
    pairGc21 ℓ p hp Θ₀ A u y
      = ∫ z in triBox ℓ p, Θ₀ (insertCoord2 p y u z.2) * pairGc21Factor p Θ₀ A z := by
  rw [pairGc21]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  unfold pairGc21Factor
  ring

/-! ## 4. The parametric derivative -/

/-- **The parametric derivative of the clean `pairG21` fibre in its `u`-variable** (with the fixed
`y = z.2` parameter), together with the integrability of the continuous-linear-map-valued
integrand needed to evaluate the derivative.

The conclusion is stated in the `pairGc21Factor`-normalised form; the statement of
`pairGc21FderivV2` is obtained from it by `pairGc21_eq_integral_factor`. -/
theorem hasFDerivAt_pairGc21 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hAb : ∀ x, ‖A x‖ ≤ cA)
    (hcA : 0 ≤ cA) (y u : E3) :
    HasFDerivAt (fun u' : E3 => ∫ z in triBox ℓ p,
        Θ₀ (insertCoord2 p y u' z.2) * pairGc21Factor p Θ₀ A z)
      (∫ z in triBox ℓ p, pairGc21Factor p Θ₀ A z •
        (fderiv ℝ Θ₀ (insertCoord2 p y u z.2)).comp (slotIns p.2)) u
    ∧ Integrable (fun z : PgZ p => pairGc21Factor p Θ₀ A z •
        (fderiv ℝ Θ₀ (insertCoord2 p y u z.2)).comp (slotIns p.2))
        ((volume : Measure (PgZ p)).restrict (triBox ℓ p)) := by
  have hK : IsCompact (triBox ℓ p) := isCompact_triBox hℓ p
  haveI hFin : IsFiniteMeasure ((volume : Measure (PgZ p)).restrict (triBox ℓ p)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict]
    exact hK.measure_lt_top.ne
  -- measurability of the multiplier
  have hfac_m : Measurable (pairGc21Factor p Θ₀ A) := by
    unfold pairGc21Factor
    exact ((continuous_star.measurable.comp (hΘ₀.continuous.measurable.comp
        (continuous_insertCoord2 p hp).measurable)).mul
        (hA.comp (continuous_fst.fst).measurable)).mul
      (hA.comp (continuous_fst.snd).measurable)
  -- the state factor is bounded on the triple box
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn
    ((hΘ₀.continuous.comp (continuous_insertCoord2 p hp)).continuousOn)
  have hfac_pt : ∀ z ∈ triBox ℓ p, ‖pairGc21Factor p Θ₀ A z‖ ≤ max M0 0 * cA * cA := by
    intro z hz
    have h1 : ‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ≤ max M0 0 :=
      le_trans (hM0 z hz) (le_max_left _ _)
    unfold pairGc21Factor
    rw [norm_mul, norm_mul, norm_star]
    exact mul_le_mul (mul_le_mul h1 (hAb _) (norm_nonneg _) (le_trans (norm_nonneg _) h1))
      (hAb _) (norm_nonneg _) (mul_nonneg (le_max_right _ _) hcA)
  -- the derivative factor is bounded on a neighbourhood of the base point times the free box
  have hKc : IsCompact (Metric.closedBall u 1 ×ˢ
      boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) :=
    (isCompact_closedBall u 1).prod (isCompact_boxPiSet (ℓ := ℓ) hℓ)
  have hcontC : ContinuousOn (fun q : E3 × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      fderiv ℝ Θ₀ (insertCoord2 p y q.1 q.2))
      (Metric.closedBall u 1 ×ˢ boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) := by
    have h1 : Continuous (fun q : E3 × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        insertCoord2 p y q.1 q.2) :=
      (continuous_insertCoord2 p hp).comp
        (((continuous_const : Continuous fun _ : E3 ×
            ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) => y).prodMk continuous_fst).prodMk
          continuous_snd)
    exact ((hΘ₀.continuous_fderiv (by simp)).comp h1).continuousOn
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn hcontC
  have hfd_pt : ∀ x ∈ Metric.closedBall u 1,
      ∀ z' ∈ boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
      ‖(fderiv ℝ Θ₀ (insertCoord2 p y x z')).comp (slotIns p.2)‖
        ≤ max C0 0 * ‖slotIns p.2‖ := by
    intro x hx z' hz'
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have h1 : ‖fderiv ℝ Θ₀ (insertCoord2 p y x z')‖ ≤ max C0 0 :=
      le_trans (hC0 (x, z') ⟨hx, hz'⟩) (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  -- the bound of the derivative integrand
  have hM : ∀ᵐ z ∂((volume : Measure (PgZ p)).restrict (triBox ℓ p)),
      ∀ x ∈ Metric.ball u 1, ‖pairGc21Factor p Θ₀ A z •
        fderiv ℝ (fun w' : E3 => Θ₀ (insertCoord2 p y w' z.2)) x‖
        ≤ (max M0 0 * cA * cA) * (max C0 0 * ‖slotIns p.2‖) := by
    refine ae_restrict_of_forall_mem hK.measurableSet (fun z hz x hx => ?_)
    have hfz : fderiv ℝ (fun w' : E3 => Θ₀ (insertCoord2 p y w' z.2)) x
        = (fderiv ℝ Θ₀ (insertCoord2 p y x z.2)).comp (slotIns p.2) :=
      (hasFDerivAt_comp_insertCoord2_snd hp hΘ₀ y z.2 x).fderiv
    rw [hfz, norm_smul]
    exact mul_le_mul (hfac_pt z hz)
      (hfd_pt x (Metric.ball_subset_closedBall hx) z.2 hz.2)
      (norm_nonneg _) (mul_nonneg (mul_nonneg (le_max_right _ _) hcA) hcA)
  -- measurability of the slices
  have hslice_m : ∀ x : E3, Measurable (fun z : PgZ p => Θ₀ (insertCoord2 p y x z.2)) := by
    intro x
    have h1 : Continuous (fun z : PgZ p => (((y, x) : E3 × E3), z.2)) :=
      continuous_const.prodMk continuous_snd
    exact hΘ₀.continuous.measurable.comp ((continuous_insertCoord2 p hp).comp h1).measurable
  have hdslice_m : Measurable (fun z : PgZ p =>
      (fderiv ℝ Θ₀ (insertCoord2 p y u z.2)).comp (slotIns p.2)) := by
    have hc1 : Continuous (fun z : PgZ p => insertCoord2 p y u z.2) :=
      (continuous_insertCoord2 p hp).comp
        (((continuous_const : Continuous fun _ : PgZ p => ((y, u) : E3 × E3))).prodMk
          continuous_snd)
    have h2 : Continuous (fun z : PgZ p => fderiv ℝ Θ₀ (insertCoord2 p y u z.2)) :=
      (hΘ₀.continuous_fderiv (by simp)).comp hc1
    exact (h2.clm_comp continuous_const).measurable
  have hclm_m : Measurable (fun z : PgZ p => pairGc21Factor p Θ₀ A z •
      (fderiv ℝ Θ₀ (insertCoord2 p y u z.2)).comp (slotIns p.2)) :=
    hfac_m.smul hdslice_m
  -- the derivative integrand of `pairGc21` is (a.e.) the one of `hasFDerivAt_integral_mul_const`
  have hFmeas : AEStronglyMeasurable (fun z : PgZ p => pairGc21Factor p Θ₀ A z •
      fderiv ℝ (fun w' : E3 => Θ₀ (insertCoord2 p y w' z.2)) u)
      ((volume : Measure (PgZ p)).restrict (triBox ℓ p)) := by
    have hmeq : (fun z : PgZ p => pairGc21Factor p Θ₀ A z •
          fderiv ℝ (fun w' : E3 => Θ₀ (insertCoord2 p y w' z.2)) u)
        = fun z : PgZ p => pairGc21Factor p Θ₀ A z •
          (fderiv ℝ Θ₀ (insertCoord2 p y u z.2)).comp (slotIns p.2) := by
      funext z
      exact congrArg (fun F => pairGc21Factor p Θ₀ A z • F)
        (hasFDerivAt_comp_insertCoord2_snd hp hΘ₀ y z.2 u).fderiv
    rw [hmeq]
    exact hclm_m.aestronglyMeasurable
  -- the slice mass is bounded (the slice of `Θ₀` at the fixed parameter pair `(y,u)`)
  obtain ⟨M2, hM2⟩ := (isCompact_boxPiSet (ℓ := ℓ) (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2})
      hℓ).exists_bound_of_continuousOn
    ((hΘ₀.continuous.comp (continuous_insertCoord2_fixed p hp y u)).continuousOn)
  have hΦint : Integrable (fun z : PgZ p => Θ₀ (insertCoord2 p y u z.2) * pairGc21Factor p Θ₀ A z)
      ((volume : Measure (PgZ p)).restrict (triBox ℓ p)) := by
    refine Integrable.of_bound ((hslice_m u).mul hfac_m).aestronglyMeasurable
      (max M2 0 * (max M0 0 * cA * cA)) ?_
    refine ae_restrict_of_forall_mem hK.measurableSet (fun z hz => ?_)
    rw [norm_mul]
    have h1 : ‖Θ₀ (insertCoord2 p y u z.2)‖ ≤ max M2 0 :=
      le_trans (hM2 z.2 hz.2) (le_max_left _ _)
    have h2 : ‖pairGc21Factor p Θ₀ A z‖ ≤ max M0 0 * cA * cA := hfac_pt z hz
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
  -- the parametric differentiation
  have hmain : HasFDerivAt (fun w : E3 => ∫ z, Θ₀ (insertCoord2 p y w z.2) *
        pairGc21Factor p Θ₀ A z ∂((volume : Measure (PgZ p)).restrict (triBox ℓ p)))
      (∫ z, pairGc21Factor p Θ₀ A z •
        fderiv ℝ (fun w' : E3 => Θ₀ (insertCoord2 p y w' z.2)) u
        ∂((volume : Measure (PgZ p)).restrict (triBox ℓ p))) u :=
    hasFDerivAt_integral_mul_const (μ := (volume : Measure (PgZ p)).restrict (triBox ℓ p))
      (Φ := fun w z => Θ₀ (insertCoord2 p y w z.2))
      (c := pairGc21Factor p Θ₀ A) (s := Metric.ball u 1)
      (M := (max M0 0 * cA * cA) * (max C0 0 * ‖slotIns p.2‖))
      (Metric.ball_mem_nhds u zero_lt_one) hM
      (Eventually.of_forall fun x => ((hslice_m x).mul hfac_m).aestronglyMeasurable)
      hΦint hFmeas
      (fun z x _ => (hasFDerivAt_comp_insertCoord2_snd hp hΘ₀ y z.2 x).differentiableAt.hasFDerivAt)
  have hderiv : (∫ z, pairGc21Factor p Θ₀ A z •
        fderiv ℝ (fun w' : E3 => Θ₀ (insertCoord2 p y w' z.2)) u
        ∂((volume : Measure (PgZ p)).restrict (triBox ℓ p)))
      = ∫ z in triBox ℓ p, pairGc21Factor p Θ₀ A z •
          (fderiv ℝ Θ₀ (insertCoord2 p y u z.2)).comp (slotIns p.2) :=
    integral_congr_ae (Eventually.of_forall fun z =>
      congrArg (fun F => pairGc21Factor p Θ₀ A z • F)
        (hasFDerivAt_comp_insertCoord2_snd hp hΘ₀ y z.2 u).fderiv)
  refine ⟨?_, ?_⟩
  · rw [hderiv] at hmain
    exact hmain
  · refine Integrable.of_bound hclm_m.aestronglyMeasurable
      ((max M0 0 * cA * cA) * (max C0 0 * ‖slotIns p.2‖)) ?_
    refine hM.mono fun z hz => ?_
    rw [← (hasFDerivAt_comp_insertCoord2_snd hp hΘ₀ y z.2 u).fderiv]
    exact hz u (Metric.mem_ball_self zero_lt_one)

/-! ## 5. The target -/

theorem pairGc21FderivV2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hAb : ∀ x, ‖A x‖ ≤ cA)
    (hcA : 0 ≤ cA) :
    (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        DifferentiableAt ℝ (fun u' => Work.BoseBoxFock.pairGc21 ℓ p hp Θ₀ A u' z.2) z.1)
    ∧ (∀ (z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) (j : Fin 3),
        fderiv ℝ (fun u' => Work.BoseBoxFock.pairGc21 ℓ p hp Θ₀ A u' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))
          = ∫ z' in Work.BoseBoxFock.triBox ℓ p,
              (star (Θ₀ (Work.BoseBoxFock.insertCoord2 p z'.1.1 z'.1.2 z'.2))
                * A z'.1.1 * A z'.1.2)
                * fderiv ℝ Θ₀ (Work.BoseBoxFock.insertCoord2 p z.2 z.1 z'.2)
                    (Work.BoseBoxFock.slotDirVec p.2 j)) := by
  have key : ∀ z : E3 × E3, (fun u' : E3 => pairGc21 ℓ p hp Θ₀ A u' z.2)
      = fun u' : E3 => ∫ z' in triBox ℓ p,
          Θ₀ (insertCoord2 p z.2 u' z'.2) * pairGc21Factor p Θ₀ A z' := by
    intro z
    funext u'
    exact pairGc21_eq_integral_factor ℓ p hp Θ₀ A u' z.2
  constructor
  · intro z
    rw [key z]
    exact (hasFDerivAt_pairGc21 hℓ p hp hΘ₀ hA hAb hcA z.2 z.1).1.differentiableAt
  · intro z j
    obtain ⟨hH, hInt⟩ := hasFDerivAt_pairGc21 hℓ p hp hΘ₀ hA hAb hcA z.2 z.1
    rw [key z, hH.fderiv, ContinuousLinearMap.integral_apply hInt]
    refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, slotIns_single,
      smul_eq_mul, pairGc21Factor]

end Work.BoseBoxFock
