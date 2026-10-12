import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGBounds
import Submission.Work.BoseBoxFock.pairGc13_continuous
import Submission.Work.BoseBoxFock.pairGc13_differentiableAt
import Submission.Work.BoseBoxFock.pairGc13_fderiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGc13_core`

The clean fibre `pairGc13 ℓ p hp Θ₀ A B` of `pairGCore` is the box-restricted representative of
the honest fibre `pairG13 p Θ A B` (with `Θ = 1_{abox n ℓ}·Θ₀`): the two agree on
`boxL ℓ × boxL ℓ`, the clean fibre is continuous and differentiable in its first variable, and it
satisfies the two Cauchy–Schwarz estimates

    ‖pairGc13 w y‖² ≤ cA²cB²ℓ³·memX13 w·memY13 y,
    Σ_j ‖∂_j pairGc13 (·,y) w‖² ≤ cA²cB²ℓ³·dirX13 w·memY13 y

(the factor `ℓ³` is the volume of the free box `boxL ℓ`).  The three analytic conjuncts
(agreement, continuity, parametric derivative) are proved in the sibling modules
`pairGc13_agree` / `pairGc13_continuous` / `pairGc13_fderiv`; the two estimates are proved here.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## 1. The two factors of the clean fibre -/

/-- The `X`-factor `star Θ₀(insertCoord p.2 w x')·A(x' ⟨p.1,hp⟩)·star (B u)` of the clean fibre. -/
noncomputable def gc13F {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (Θ₀ : Xn n → ℂ)
    (A B : E3 → ℂ) (w : E3) (z : ({k : Fin n // k ≠ p.2} → E3) × E3) : ℂ :=
  star (Θ₀ (insertCoord p.2 w z.1)) * A (z.1 ⟨p.1, hp⟩) * star (B z.2)

/-- The `Y`-factor `Θ₀(confY13 p y u x')` of the clean fibre. -/
noncomputable def gc13G {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (y : E3)
    (z : ({k : Fin n // k ≠ p.2} → E3) × E3) : ℂ :=
  Θ₀ (confY13 p y z.2 z.1)

/-- The derivative of the `X`-factor in the direction `v` of the `w`-variable. -/
noncomputable def gc13Fd {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (Θ₀ : Xn n → ℂ)
    (A B : E3 → ℂ) (w : E3) (v : Xn n) (z : ({k : Fin n // k ≠ p.2} → E3) × E3) : ℂ :=
  star (fderiv ℝ Θ₀ (insertCoord p.2 w z.1) v) * A (z.1 ⟨p.1, hp⟩) * star (B z.2)

/-- **The clean fibre as a set integral of the product of the two factors.** -/
theorem pairGc13_eq_setIntegral {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ) (w y : E3) :
    pairGc13 ℓ p hp Θ₀ A B w y
      = ∫ z in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
          gc13F p hp Θ₀ A B w z * gc13G p Θ₀ y z := rfl

/-! ## 2. Continuity of the coordinate insertions -/

/-- `x' ↦ insertCoord j w x'` is continuous (with `w` held fixed). -/
theorem continuous_insertCoord_const {n : ℕ} (j : Fin n) (w : E3) :
    Continuous (fun x' : ({k : Fin n // k ≠ j} → E3) => insertCoord j w x') := by
  refine continuous_pi fun k => ?_
  by_cases hk : k = j
  · have h : (fun x' : ({k : Fin n // k ≠ j} → E3) => insertCoord j w x' k) = fun _ => w := by
      funext x'
      simp only [insertCoord_eq]
      rw [dif_pos hk]
    rw [h]; exact continuous_const
  · have h : (fun x' : ({k : Fin n // k ≠ j} → E3) => insertCoord j w x' k)
        = fun x' => x' ⟨k, hk⟩ := by
      funext x'
      simp only [insertCoord_eq]
      rw [dif_neg hk]
    rw [h]; exact continuous_apply _

/-- `z ↦ confY13 p y z.2 z.1` is continuous. -/
theorem continuous_confY13 {n : ℕ} (p : Fin n × Fin n) (y : E3) :
    Continuous (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => confY13 p y z.2 z.1) := by
  refine continuous_pi fun k => ?_
  by_cases h1 : k = p.1
  · have h : (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => confY13 p y z.2 z.1 k)
        = fun _ => y := by
      funext z; simp only [confY13]; rw [dif_pos h1]
    rw [h]; exact continuous_const
  · by_cases h2 : k = p.2
    · have h : (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => confY13 p y z.2 z.1 k)
          = fun z => z.2 := by
        funext z; simp only [confY13]; rw [dif_neg h1, dif_pos h2]
      rw [h]; exact continuous_snd
    · have h : (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => confY13 p y z.2 z.1 k)
          = fun z => z.1 ⟨k, h2⟩ := by
        funext z; simp only [confY13]; rw [dif_neg h1, dif_neg h2]
      rw [h]; exact (continuous_apply _).comp continuous_fst

/-! ## 3. Bounds and integrability on the product box -/

/-- The product box `boxPiSet ι ℓ × boxL ℓ` has finite volume. -/
theorem volume_boxPiSet_prod_boxL_lt_top {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure ((ι → E3) × E3)) (boxPiSet ι ℓ ×ˢ boxL ℓ) < ⊤ :=
  ((isCompact_boxPiSet (ι := ι) hℓ).prod
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)).measure_lt_top

/-- The product box is measurable. -/
theorem measurableSet_boxPiSet_prod_boxL {ι : Type*} [Fintype ι] (ℓ : ℝ) :
    MeasurableSet (boxPiSet ι ℓ ×ˢ boxL ℓ) :=
  (MeasurableSet.univ_pi fun _ => Work.BoseB4.BoxData.boxL_measurableSet _ ℓ).prod
    (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)

/-- A measurable function bounded on the product box is integrable there. -/
theorem integrableOn_boxPiSet_prod_boxL {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {F : (ι → E3) × E3 → E} (hF : Measurable F) {C : ℝ}
    (hC : ∀ z ∈ boxPiSet ι ℓ ×ˢ boxL ℓ, ‖F z‖ ≤ C) :
    IntegrableOn F (boxPiSet ι ℓ ×ˢ boxL ℓ) := by
  haveI : IsFiniteMeasure (volume.restrict (boxPiSet ι ℓ ×ˢ boxL ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_boxPiSet_prod_boxL_lt_top hℓ⟩
  exact Integrable.of_bound hF.aestronglyMeasurable C (by
    filter_upwards [self_mem_ae_restrict (measurableSet_boxPiSet_prod_boxL (ι := ι) ℓ)] with z hz
    exact hC z hz)

/-- A bound for `Θ₀` on the `X`-configurations `insertCoord j w x'` of the box. -/
theorem exists_bound_insertCoord {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) (j : Fin n) (w : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x' ∈ boxPiSet ({k : Fin n // k ≠ j}) ℓ,
      ‖Θ₀ (insertCoord j w x')‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_boxPiSet (ι := {k : Fin n // k ≠ j}) hℓ).exists_bound_of_continuousOn
    (f := fun x' : {k : Fin n // k ≠ j} → E3 => Θ₀ (insertCoord j w x'))
    ((hΘ₀.comp (continuous_insertCoord_const j w)).continuousOn)
  exact ⟨max C 0, le_max_right _ _, fun x' hx => (hC x' hx).trans (le_max_left _ _)⟩

/-- A bound for `Θ₀` on the `Y`-configurations `confY13 p y u x'` of the box. -/
theorem exists_bound_confY13 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : Continuous Θ₀) (p : Fin n × Fin n) (y : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
      ‖Θ₀ (confY13 p y z.2 z.1)‖ ≤ C := by
  have hKc : IsCompact (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ) :=
    (isCompact_boxPiSet (ι := {k : Fin n // k ≠ p.2}) hℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  obtain ⟨C, hC⟩ := (hKc.image (continuous_confY13 p y)).exists_bound_of_continuousOn
    hΘ₀.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)⟩

/-- A bound for `fderiv Θ₀` on the `X`-configurations of the box. -/
theorem exists_bound_fderiv_insertCoord {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (j : Fin n) (w : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x' ∈ boxPiSet ({k : Fin n // k ≠ j}) ℓ,
      ‖fderiv ℝ Θ₀ (insertCoord j w x')‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_boxPiSet (ι := {k : Fin n // k ≠ j}) hℓ).exists_bound_of_continuousOn
    (f := fun x' : {k : Fin n // k ≠ j} → E3 => fderiv ℝ Θ₀ (insertCoord j w x'))
    (((hΘ₀.continuous_fderiv (by simp)).comp (continuous_insertCoord_const j w)).continuousOn)
  exact ⟨max C 0, le_max_right _ _, fun x' hx => (hC x' hx).trans (le_max_left _ _)⟩

/-! ## 4. The integral computations -/

/-- **The `u`-integration over the box amounts to multiplying by its volume `ℓ³`.** -/
theorem setIntegral_boxL_const {ι : Type*} [Fintype ι] (ℓ : ℝ) (hℓ : 0 < ℓ)
    (F : (ι → E3) → ℝ) :
    (∫ x' in boxPiSet ι ℓ, ∫ u in boxL ℓ, F x') = ℓ ^ 3 * ∫ x' in boxPiSet ι ℓ, F x' := by
  have hinner : ∀ x' : ι → E3, (∫ u in boxL ℓ, F x') = ℓ ^ 3 * F x' := by
    intro x'
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real,
      Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  simp_rw [hinner]
  rw [MeasureTheory.integral_const_mul]

/-- The double integral of the `X`-mass: it is `ℓ³·memX13`. -/
theorem setIntegral_insertCoord_sq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : Continuous Θ₀) (w : E3) :
    (∫ z, ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2
        ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      = ℓ ^ 3 * memX13 ℓ p Θ₀ w := by
  obtain ⟨C, _hC0, hC⟩ := exists_bound_insertCoord hℓ hΘ₀ p.2 w
  have hI : IntegrableOn (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2) (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxPiSet_prod_boxL hℓ
      (F := fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2)
      (C := C ^ 2) ?_ ?_
    · exact ((hΘ₀.measurable.comp ((continuous_insertCoord_const p.2 w).measurable.comp
        measurable_fst)).norm).pow_const 2
    · intro z hz
      have h1 : ‖‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2‖ = ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC z.1 hz.1) 2
  rw [show (∫ z, ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2
        ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      = ∫ z in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
          ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2 ∂(volume.prod volume) from rfl]
  rw [MeasureTheory.setIntegral_prod _ hI, memX13]
  exact setIntegral_boxL_const ℓ hℓ (fun x' => ‖Θ₀ (insertCoord p.2 w x')‖ ^ 2)

/-- The double integral of the `Y`-mass: it is `memY13`. -/
theorem setIntegral_gc13G_sq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : Continuous Θ₀) (y : E3) :
    (∫ z, ‖gc13G p Θ₀ y z‖ ^ 2
        ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      = memY13 ℓ p Θ₀ y := by
  obtain ⟨C, _hC0, hC⟩ := exists_bound_confY13 hℓ hΘ₀ p y
  have hI : IntegrableOn (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      ‖gc13G p Θ₀ y z‖ ^ 2) (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxPiSet_prod_boxL hℓ
      (F := fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => ‖gc13G p Θ₀ y z‖ ^ 2)
      (C := C ^ 2) ?_ ?_
    · exact (((hΘ₀.measurable.comp (continuous_confY13 p y).measurable)).norm).pow_const 2
    · intro z hz
      have h1 : ‖‖gc13G p Θ₀ y z‖ ^ 2‖ = ‖gc13G p Θ₀ y z‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC z hz) 2
  rw [show (∫ z, ‖gc13G p Θ₀ y z‖ ^ 2
        ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      = ∫ z in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
          ‖gc13G p Θ₀ y z‖ ^ 2 ∂(volume.prod volume) from rfl]
  rw [MeasureTheory.setIntegral_prod _ hI, memY13]
  rfl

/-- The double integral of the `j`-th derivative mass: it is `ℓ³` times the fibre integral. -/
theorem setIntegral_fderiv_sq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (w : E3) (j : Fin 3) :
    (∫ z, ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2
        ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      = ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2 := by
  obtain ⟨C, _hC0, hC⟩ := exists_bound_fderiv_insertCoord hℓ hΘ₀ p.2 w
  have hcont : Continuous (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)) :=
    ((hΘ₀.continuous_fderiv (by simp)).comp
      ((continuous_insertCoord_const p.2 w).comp continuous_fst)).clm_apply continuous_const
  have hI : IntegrableOn (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2)
      (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxPiSet_prod_boxL hℓ
      (F := fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2)
      (C := (C * ‖slotDirVec p.2 j‖) ^ 2) ?_ ?_
    · exact (hcont.measurable.norm).pow_const 2
    · intro z hz
      have h1 : ‖‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2‖
          = ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hC z.1 hz.1) (norm_nonneg _))) 2
  rw [show (∫ z, ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2
        ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      = ∫ z in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2
          ∂(volume.prod volume) from rfl]
  rw [MeasureTheory.setIntegral_prod _ hI]
  exact setIntegral_boxL_const ℓ hℓ
    (fun x' => ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2)

/-! ## 5. The `L²` (mass) bound -/

/-- **Cauchy–Schwarz, mass form.**  `‖pairGc13 w y‖² ≤ cA²cB²ℓ³·memX13 w·memY13 y`. -/
theorem pairGc13_mass_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (w y : E3) :
    ‖pairGc13 ℓ p hp Θ₀ A B w y‖ ^ 2
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_bound_insertCoord hℓ hΘ₀.continuous p.2 w
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_confY13 hℓ hΘ₀.continuous p y
  have hKm := measurableSet_boxPiSet_prod_boxL (ι := {k : Fin n // k ≠ p.2}) ℓ
  haveI : IsFiniteMeasure
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_boxPiSet_prod_boxL_lt_top hℓ⟩
  have hfm : Measurable (gc13F p hp Θ₀ A B w) := by
    unfold gc13F
    exact (((continuous_star.measurable.comp (hΘ₀.continuous.measurable.comp
        ((continuous_insertCoord_const p.2 w).measurable.comp measurable_fst))).mul
      (hA.comp ((measurable_pi_apply (⟨p.1, hp⟩ : {k : Fin n // k ≠ p.2})).comp
        measurable_fst))).mul
      (continuous_star.measurable.comp (hB.comp measurable_snd)))
  have hgm : Measurable (gc13G p Θ₀ y) := by
    unfold gc13G
    exact hΘ₀.continuous.measurable.comp (continuous_confY13 p y).measurable
  have hfb : ∀ z ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
      ‖gc13F p hp Θ₀ A B w z‖ ≤ M * cA * cB := by
    intro z hz
    have h1 : ‖gc13F p hp Θ₀ A B w z‖
        = ‖Θ₀ (insertCoord p.2 w z.1)‖ * ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖ := by
      unfold gc13F; rw [norm_mul, norm_mul, norm_star, norm_star]
    rw [h1]
    exact mul_le_mul (mul_le_mul (hM z.1 hz.1) (hAb _) (norm_nonneg _) hM0) (hBb _)
      (norm_nonneg _) (by positivity)
  have hgb : ∀ z ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
      ‖gc13G p Θ₀ y z‖ ≤ M₂ := by
    intro z hz
    have h1 : ‖gc13G p Θ₀ y z‖ = ‖Θ₀ (confY13 p y z.2 z.1)‖ := rfl
    rw [h1]; exact hM₂ z hz
  have hfmem : MemLp (gc13F p hp Θ₀ A B w) 2
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) :=
    MemLp.of_bound hfm.aestronglyMeasurable (M * cA * cB) (by
      filter_upwards [self_mem_ae_restrict hKm] with z hz
      exact hfb z hz)
  have hgmem : MemLp (gc13G p Θ₀ y) 2
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) :=
    MemLp.of_bound hgm.aestronglyMeasurable M₂ (by
      filter_upwards [self_mem_ae_restrict hKm] with z hz
      exact hgb z hz)
  have hcs := norm_integral_mul_sq_le
    (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) hfmem hgmem
  have hXint := setIntegral_insertCoord_sq hℓ p hΘ₀.continuous w
  have hYint := setIntegral_gc13G_sq hℓ p hΘ₀.continuous y
  have hpt : ∀ z, z ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ →
      ‖gc13F p hp Θ₀ A B w z‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2 := by
    intro z _
    have h1 : ‖gc13F p hp Θ₀ A B w z‖
        = ‖Θ₀ (insertCoord p.2 w z.1)‖ * ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖ := by
      unfold gc13F; rw [norm_mul, norm_mul, norm_star, norm_star]
    have h2 : ‖gc13F p hp Θ₀ A B w z‖ ≤ ‖Θ₀ (insertCoord p.2 w z.1)‖ * cA * cB := by
      rw [h1]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hAb _) (norm_nonneg _)) (hBb _)
        (norm_nonneg _) (by positivity)
    calc ‖gc13F p hp Θ₀ A B w z‖ ^ 2
        ≤ (‖Θ₀ (insertCoord p.2 w z.1)‖ * cA * cB) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2 := by ring
  have hmaj : Integrable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2)
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) := by
    refine Integrable.of_bound ?_ (cA ^ 2 * cB ^ 2 * M ^ 2) ?_
    · exact (measurable_const.mul (((hΘ₀.continuous.measurable.comp
        ((continuous_insertCoord_const p.2 w).measurable.comp measurable_fst)).norm).pow_const
          2)).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict hKm] with z hz
      have h1 : ‖cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2‖
          = cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hM z.1 hz.1) 2)
        (by positivity)
  have hXle : (∫ z, ‖gc13F p hp Θ₀ A B w z‖ ^ 2
      ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      ≤ cA ^ 2 * cB ^ 2 * (ℓ ^ 3 * memX13 ℓ p Θ₀ w) := by
    have hmono := integral_mono_of_nonneg
      (μ := volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ))
      (f := fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => ‖gc13F p hp Θ₀ A B w z‖ ^ 2)
      (g := fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord p.2 w z.1)‖ ^ 2)
      (Filter.Eventually.of_forall fun z => by positivity) hmaj
      (by filter_upwards [self_mem_ae_restrict hKm] with z hz; exact hpt z hz)
    rw [MeasureTheory.integral_const_mul, hXint] at hmono
    exact hmono
  have hYnn : 0 ≤ memY13 ℓ p Θ₀ y := by
    rw [memY13]
    exact integral_nonneg fun _ => integral_nonneg fun _ => by positivity
  calc ‖pairGc13 ℓ p hp Θ₀ A B w y‖ ^ 2
      = ‖∫ z, gc13F p hp Θ₀ A B w z * gc13G p Θ₀ y z
          ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ))‖ ^ 2 := by
        rw [pairGc13_eq_setIntegral]
    _ ≤ (∫ z, ‖gc13F p hp Θ₀ A B w z‖ ^ 2
            ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
          * (∫ z, ‖gc13G p Θ₀ y z‖ ^ 2
            ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ))) := hcs
    _ = (∫ z, ‖gc13F p hp Θ₀ A B w z‖ ^ 2
            ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
          * memY13 ℓ p Θ₀ y := by rw [hYint]
    _ ≤ (cA ^ 2 * cB ^ 2 * (ℓ ^ 3 * memX13 ℓ p Θ₀ w)) * memY13 ℓ p Θ₀ y :=
        mul_le_mul_of_nonneg_right hXle hYnn
    _ = cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y := by ring

/-! ## 6. The Dirichlet bound -/

/-- **Cauchy–Schwarz, Dirichlet form**, given the parametric-derivative formula `hfderiv`
(proved in `pairGc13_fderiv`). -/
theorem pairGc13_dir_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hfderiv : ∀ y w v : E3, fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w v
      = ∫ z in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
          gc13Fd p hp Θ₀ A B w (Function.update (0 : Xn n) p.2 v) z * gc13G p Θ₀ y z)
    (w y : E3) :
    ∑ j : Fin 3, ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y := by
  classical
  obtain ⟨Mg, hMg0, hMg⟩ := exists_bound_fderiv_insertCoord hℓ hΘ₀ p.2 w
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_confY13 hℓ hΘ₀.continuous p y
  have hKm := measurableSet_boxPiSet_prod_boxL (ι := {k : Fin n // k ≠ p.2}) ℓ
  haveI : IsFiniteMeasure
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_boxPiSet_prod_boxL_lt_top hℓ⟩
  have hgm : Measurable (gc13G p Θ₀ y) := by
    unfold gc13G
    exact hΘ₀.continuous.measurable.comp (continuous_confY13 p y).measurable
  have hgb : ∀ z ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
      ‖gc13G p Θ₀ y z‖ ≤ M₂ := by
    intro z hz
    have h1 : ‖gc13G p Θ₀ y z‖ = ‖Θ₀ (confY13 p y z.2 z.1)‖ := rfl
    rw [h1]; exact hM₂ z hz
  have hgmem : MemLp (gc13G p Θ₀ y) 2
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) :=
    MemLp.of_bound hgm.aestronglyMeasurable M₂ (by
      filter_upwards [self_mem_ae_restrict hKm] with z hz
      exact hgb z hz)
  -- the `j`-th factor `gc13Fd`, its measurability and its `MemLp`
  have hdcont : ∀ j : Fin 3, Continuous (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)) := fun j =>
    ((hΘ₀.continuous_fderiv (by simp)).comp
      ((continuous_insertCoord_const p.2 w).comp continuous_fst)).clm_apply continuous_const
  have hdmeas : ∀ j : Fin 3, Measurable (gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j)) := by
    intro j
    unfold gc13Fd
    exact (((continuous_star.measurable.comp (hdcont j).measurable).mul
      (hA.comp ((measurable_pi_apply (⟨p.1, hp⟩ : {k : Fin n // k ≠ p.2})).comp
        measurable_fst))).mul
      (continuous_star.measurable.comp (hB.comp measurable_snd)))
  have hdb : ∀ j : Fin 3, ∀ z ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
      ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖
        ≤ (Mg * ‖slotDirVec p.2 j‖) * cA * cB := by
    intro j z hz
    have h1 : ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖
        = ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖
          * ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖ := by
      unfold gc13Fd; rw [norm_mul, norm_mul, norm_star, norm_star]
    rw [h1]
    have h2 : ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖
        ≤ Mg * ‖slotDirVec p.2 j‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hMg z.1 hz.1) (norm_nonneg _))
    exact mul_le_mul (mul_le_mul h2 (hAb _) (norm_nonneg _) (by positivity)) (hBb _)
      (norm_nonneg _) (by positivity)
  have hdmem : ∀ j : Fin 3, MemLp (gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j)) 2
      (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) := fun j =>
    MemLp.of_bound (hdmeas j).aestronglyMeasurable (Mg * ‖slotDirVec p.2 j‖ * cA * cB) (by
      filter_upwards [self_mem_ae_restrict hKm] with z hz
      exact hdb j z hz)
  have hYint := setIntegral_gc13G_sq hℓ p hΘ₀.continuous y
  have hXint : ∀ j : Fin 3, (∫ z, ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2
      ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      = ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2 := fun j =>
    setIntegral_fderiv_sq hℓ p hΘ₀ w j
  -- per-`j` Cauchy–Schwarz
  have hDj : ∀ j : Fin 3, ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ (∫ z, ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖ ^ 2
          ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
        * memY13 ℓ p Θ₀ y := by
    intro j
    have hform := hfderiv y w (EuclideanSpace.single j (1 : ℝ))
    have hslot : (Function.update (0 : Xn n) p.2 (EuclideanSpace.single j (1 : ℝ)))
        = slotDirVec p.2 j := rfl
    rw [hform, hslot]
    refine (norm_integral_mul_sq_le _ (hdmem j) hgmem).trans ?_
    rw [hYint]
  -- the `X`-mass of the `j`-th factor, summed over `j`
  have hper : ∀ j : Fin 3, (∫ z, ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖ ^ 2
      ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      ≤ cA ^ 2 * cB ^ 2 * (ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2) := by
    intro j
    have hmaj : Integrable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        cA ^ 2 * cB ^ 2 * ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2)
        (volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)) := by
      refine Integrable.of_bound ?_ (cA ^ 2 * cB ^ 2 * (Mg * ‖slotDirVec p.2 j‖) ^ 2) ?_
      · exact (measurable_const.mul ((hdcont j).measurable.norm.pow_const 2)).aestronglyMeasurable
      · filter_upwards [self_mem_ae_restrict hKm] with z hz
        have h1 : ‖cA ^ 2 * cB ^ 2
              * ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2‖
            = cA ^ 2 * cB ^ 2
              * ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [h1]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
          ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hMg z.1 hz.1) (norm_nonneg _))) 2) (by positivity)
    have hmono := integral_mono_of_nonneg
      (μ := volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ))
      (f := fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖ ^ 2)
      (g := fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        cA ^ 2 * cB ^ 2 * ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2)
      (Filter.Eventually.of_forall fun z => by positivity) hmaj (by
        filter_upwards [self_mem_ae_restrict hKm] with z hz
        have h1 : ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖
            = ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖
              * ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖ := by
          unfold gc13Fd; rw [norm_mul, norm_mul, norm_star, norm_star]
        have h2 : ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖
              * ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖
            ≤ ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ * cA * cB :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hAb _) (norm_nonneg _)) (hBb _)
            (norm_nonneg _) (by positivity)
        rw [h1]
        calc (‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖
              * ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖) ^ 2
            ≤ (‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ * cA * cB) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h2 2
          _ = cA ^ 2 * cB ^ 2
              * ‖fderiv ℝ Θ₀ (insertCoord p.2 w z.1) (slotDirVec p.2 j)‖ ^ 2 := by ring)
    rw [MeasureTheory.integral_const_mul, hXint j] at hmono
    exact hmono
  have hsumX : (∑ j : Fin 3, ∫ z, ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖ ^ 2
      ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
      ≤ cA ^ 2 * cB ^ 2 * (ℓ ^ 3 * dirX13 ℓ p Θ₀ w) := by
    calc (∑ j : Fin 3, ∫ z, ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖ ^ 2
          ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
        ≤ ∑ j : Fin 3, cA ^ 2 * cB ^ 2 * (ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
            ‖fderiv ℝ Θ₀ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2) :=
          Finset.sum_le_sum fun j _ => hper j
      _ = cA ^ 2 * cB ^ 2 * (ℓ ^ 3 * dirX13 ℓ p Θ₀ w) := by
          rw [dirX13, Finset.mul_sum, Finset.mul_sum]
  have hYnn : 0 ≤ memY13 ℓ p Θ₀ y := by
    rw [memY13]
    exact integral_nonneg fun _ => integral_nonneg fun _ => by positivity
  calc ∑ j : Fin 3, ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ∑ j : Fin 3, (∫ z, ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖ ^ 2
          ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
          * memY13 ℓ p Θ₀ y := Finset.sum_le_sum fun j _ => hDj j
    _ = (∑ j : Fin 3, ∫ z, ‖gc13Fd p hp Θ₀ A B w (slotDirVec p.2 j) z‖ ^ 2
          ∂(volume.restrict (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ)))
          * memY13 ℓ p Θ₀ y := (Finset.sum_mul _ _ _).symm
    _ ≤ (cA ^ 2 * cB ^ 2 * (ℓ ^ 3 * dirX13 ℓ p Θ₀ w)) * memY13 ℓ p Θ₀ y :=
        mul_le_mul_of_nonneg_right hsumX hYnn
    _ = cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y := by ring

/-! ## 7. The box agreement `pairG13 = pairGc13`

`pairG13` is an *iterated* Bochner integral over the whole fibre space and all of `ℝ³`, while
`pairGc13` is the integral over the product **measure** on the compact box.  The bridge is
Bochner–Fubini (`MeasureTheory.setIntegral_prod`), which needs the box integrand to be integrable;
that is supplied by the boundedness of `Θ₀`, `A`, `B` on the box (`exists_bound_on_abox`,
`exists_bound_insertCoord`).

(Note.  This agreement is *false* for an arbitrary measurable `Θ₀` and unbounded `A`, `B`: then
both sides are junk-`0` and in general unequal.  The hypotheses below — exactly those of the
target — are what make it true.) -/

/-- The double `Function.update` of the `p.2`-inserted configuration is `confY13`. -/
lemma gc13Agree_confY13_eq_update {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (w y u : E3)
    (x' : {k : Fin n // k ≠ p.2} → E3) :
    Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u
      = confY13 p y u x' := by
  funext k
  by_cases h1 : k = p.1
  · subst h1
    simp [confY13, insertCoord, Function.update, hp]
  · by_cases h2 : k = p.2
    · subst h2
      simp [confY13, insertCoord, Function.update, hp, Ne.symm hp]
    · simp [confY13, insertCoord, Function.update, h1, h2]

/-- The `A`-argument of the `pairG13` integrand. -/
lemma gc13Agree_insertCoord_apply_fst {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (w : E3)
    (x' : {k : Fin n // k ≠ p.2} → E3) : (insertCoord p.2 w x') p.1 = x' ⟨p.1, hp⟩ := by
  simp [insertCoord, hp]

/-- If `u ∉ boxL ℓ` then the double update leaves `abox n ℓ`. -/
lemma gc13Agree_upd_notMem {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {w y u : E3} (_hw : w ∈ boxL ℓ) (_hy : y ∈ boxL ℓ)
    {x' : {k : Fin n // k ≠ p.2} → E3} (_hx : x' ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ)
    (hu : u ∉ boxL ℓ) :
    Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u
      ∉ Submission.BoseGases.abox n ℓ := by
  intro h
  have h2 : (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u) p.2
      ∈ Submission.BoseGases.acube ℓ :=
    (Submission.BoseGases.mem_abox_iff n ℓ _).mp h p.2
  rw [Function.update_apply, if_pos rfl] at h2
  rw [corpusBox_boxL_eq_acube hℓ] at hu
  exact hu h2

/-- On the box the `pairG13` integrand is the indicator of the product box times the clean
integrand `gc13F·gc13G` of `pairGc13`.  Nothing is needed on `A`, `B`: the `Θ`-indicator factors
already kill everything off the box. -/
lemma gc13Agree_integrand_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ}
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    {w y : E3} (hw : w ∈ boxL ℓ) (hy : y ∈ boxL ℓ)
    (x' : {k : Fin n // k ≠ p.2} → E3) (u : E3) :
    star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)
      = Set.indicator (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
        * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
            * (gc13F p hp Θ₀ A B w (x', u) * gc13G p Θ₀ y (x', u))) := by
  rw [hΘ (insertCoord p.2 w x'),
    hΘ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u),
    star_indicatorC Θ₀ (insertCoord p.2 w x'),
    gc13Agree_confY13_eq_update p hp w y u x',
    gc13Agree_insertCoord_apply_fst p hp w x']
  by_cases hx : x' ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ
  · have hxab : insertCoord p.2 w x' ∈ Submission.BoseGases.abox n ℓ :=
      (insertCoord_mem_abox_iff hℓ hw x').mpr hx
    by_cases hu : u ∈ boxL ℓ
    · have hcf : confY13 p y u x' ∈ Submission.BoseGases.abox n ℓ :=
        confY13_mem_abox hℓ hy hu hx
      simp only [Set.indicator_of_mem hxab, Set.indicator_of_mem hx, Set.indicator_of_mem hu,
        Set.indicator_of_mem hcf, one_mul, gc13F, gc13G]
    · have hcf : confY13 p y u x' ∉ Submission.BoseGases.abox n ℓ := by
        rw [← gc13Agree_confY13_eq_update p hp w y u x']
        exact gc13Agree_upd_notMem hℓ hp hw hy hx hu
      simp only [Set.indicator_of_mem hxab, Set.indicator_of_notMem hcf,
        Set.indicator_of_mem hx, Set.indicator_of_notMem hu, one_mul, zero_mul, mul_zero,
        gc13F, gc13G]
  · have hxab : insertCoord p.2 w x' ∉ Submission.BoseGases.abox n ℓ :=
      fun h => hx ((insertCoord_mem_abox_iff hℓ hw x').mp h)
    simp only [Set.indicator_of_notMem hxab, Set.indicator_of_notMem hx, zero_mul, mul_zero]

/-- **The box agreement of the honest fibre with the clean one** (the first conjunct of
`pairGc13_core`). -/
theorem pairGc13_box_agree {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) :
    ∀ w y : E3, w ∈ boxL ℓ → y ∈ boxL ℓ →
      pairG13 p Θ A B w y = pairGc13 ℓ p hp Θ₀ A B w y := by
  intro w y hw hy
  have hKs : IsCompact (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) := isCompact_boxPiSet hℓ
  have hKt : IsCompact (boxL ℓ) := by
    rw [corpusBox_boxL_eq_acube hℓ]
    exact Submission.BoseGases.acube_compact hℓ
  have hmeass : MeasurableSet (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) := hKs.measurableSet
  have hmeast : MeasurableSet (boxL ℓ) := hKt.measurableSet
  have hfm : Measurable (gc13F p hp Θ₀ A B w) := by
    unfold gc13F
    exact (((continuous_star.measurable.comp (hΘ₀.continuous.measurable.comp
        ((continuous_insertCoord_const p.2 w).measurable.comp measurable_fst))).mul
      (hA.comp ((measurable_pi_apply (⟨p.1, hp⟩ : {k : Fin n // k ≠ p.2})).comp
        measurable_fst))).mul
      (continuous_star.measurable.comp (hB.comp measurable_snd)))
  have hgm : Measurable (gc13G p Θ₀ y) := by
    unfold gc13G
    exact hΘ₀.continuous.measurable.comp (continuous_confY13 p y).measurable
  -- the clean integrand is integrable on the compact box
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox (n := n) (ℓ := ℓ) hℓ hΘ₀.continuous
  have hGint : IntegrableOn (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      gc13F p hp Θ₀ A B w z * gc13G p Θ₀ y z)
      (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxPiSet_prod_boxL hℓ
      (F := fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        gc13F p hp Θ₀ A B w z * gc13G p Θ₀ y z)
      (C := (M * max cA 0) * max cB 0 * M) (hfm.mul hgm) ?_
    intro z hz
    have hin : insertCoord p.2 w z.1 ∈ Submission.BoseGases.abox n ℓ :=
      (insertCoord_mem_abox_iff hℓ hw z.1).mpr hz.1
    have hconf : confY13 p y z.2 z.1 ∈ Submission.BoseGases.abox n ℓ :=
      confY13_mem_abox hℓ hy hz.2 hz.1
    have hAnn : (0 : ℝ) ≤ max cA 0 := le_max_right _ _
    have hBnn : (0 : ℝ) ≤ max cB 0 := le_max_right _ _
    have hstep : ‖gc13F p hp Θ₀ A B w z‖ ≤ M * max cA 0 * max cB 0 := by
      have h1 : ‖gc13F p hp Θ₀ A B w z‖
          = ‖Θ₀ (insertCoord p.2 w z.1)‖ * ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖ := by
        unfold gc13F; rw [norm_mul, norm_mul, norm_star, norm_star]
      rw [h1]
      exact mul_le_mul (mul_le_mul (hM _ hin) (le_trans (hAb _) (le_max_left _ _))
        (norm_nonneg _) hM0) (le_trans (hBb _) (le_max_left _ _)) (norm_nonneg _)
        (mul_nonneg hM0 hAnn)
    calc ‖gc13F p hp Θ₀ A B w z * gc13G p Θ₀ y z‖
        = ‖gc13F p hp Θ₀ A B w z‖ * ‖Θ₀ (confY13 p y z.2 z.1)‖ := by
          rw [norm_mul]; rfl
      _ ≤ (M * max cA 0 * max cB 0) * M :=
          mul_le_mul hstep (hM _ hconf) (norm_nonneg _) (by positivity)
  calc pairG13 p Θ A B w y
      = ∫ x' : {k : Fin n // k ≠ p.2} → E3, ∫ u : E3,
          star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
            * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u) := rfl
    _ = ∫ x' : {k : Fin n // k ≠ p.2} → E3, ∫ u : E3,
          Set.indicator (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
            * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                * (gc13F p hp Θ₀ A B w (x', u) * gc13G p Θ₀ y (x', u))) :=
        integral₂_congr fun x' u => gc13Agree_integrand_eq hℓ hp hΘ hw hy x' u
    _ = ∫ x' : {k : Fin n // k ≠ p.2} → E3,
          Set.indicator (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
            * (∫ u : E3, Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                * (gc13F p hp Θ₀ A B w (x', u) * gc13G p Θ₀ y (x', u))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
        simp only []
        rw [integral_const_mul]
    _ = ∫ x' : {k : Fin n // k ≠ p.2} → E3,
          Set.indicator (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
            * (∫ u in boxL ℓ, gc13F p hp Θ₀ A B w (x', u) * gc13G p Θ₀ y (x', u)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
        simp only []
        rw [integral_indicator_mul hmeast]
    _ = ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in boxL ℓ,
          gc13F p hp Θ₀ A B w (x', u) * gc13G p Θ₀ y (x', u) := by
        rw [integral_indicator_mul hmeass]
    _ = ∫ z in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ boxL ℓ,
          gc13F p hp Θ₀ A B w z * gc13G p Θ₀ y z :=
        (MeasureTheory.setIntegral_prod _ hGint).symm
    _ = pairGc13 ℓ p hp Θ₀ A B w y := (pairGc13_eq_setIntegral ℓ p hp Θ₀ A B w y).symm

/-! ## 8. The target -/

theorem pairGc13_core {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
    {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    (∀ w y : EuclideanSpace ℝ (Fin 3), w ∈ Work.BoseK15.corpusBox.boxL ℓ →
        y ∈ Work.BoseK15.corpusBox.boxL ℓ → pairG13 p Θ A B w y = pairGc13 ℓ p hp Θ₀ A B w y)
    ∧ Continuous (Function.uncurry (pairGc13 ℓ p hp Θ₀ A B))
    ∧ (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        DifferentiableAt ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1)
    ∧ (∀ w y : EuclideanSpace ℝ (Fin 3), ‖pairGc13 ℓ p hp Θ₀ A B w y‖ ^ 2
          ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y)
    ∧ (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ z.1 * memY13 ℓ p Θ₀ z.2) := by
  exact ⟨pairGc13_box_agree hℓ p hp hΘ₀ hΘ hA hB hAb hBb,
    pairGc13_continuous hℓ p hp hΘ₀ hA hB hAb hBb,
    fun z => pairGc13_differentiableAt hℓ p hp hΘ₀ hA hB hAb hBb z.2 z.1,
    fun w y => pairGc13_mass_bound hℓ p hp hΘ₀ hA hB hAb hBb hcA hcB w y,
    fun z => pairGc13_dir_bound hℓ p hp hΘ₀ hA hB hAb hBb hcA hcB
      (fun y w v => (pairGc13_fderiv hℓ p hp hΘ₀ hA hB hAb hBb y w v).trans
        (by simp only [gc13Fd, gc13G])) z.1 z.2⟩

end Work.BoseBoxFock
