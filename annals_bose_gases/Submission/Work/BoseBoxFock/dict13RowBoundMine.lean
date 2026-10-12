import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13Aux7
import Submission.Work.BoseBoxFock.dict13RowDomLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13RowBoundMine` — the `L¹` bound of the block-I row integrand

The pointwise domination `rowProd_enorm_le_rowDom` (`dict13RowDomLe`) reduces the `L¹` bound of the
block-I row to the box integrals of the four rows of the `Q M Q` kernel; those are computed here by
Tonelli together with the one-coordinate peel `lintegral_coord_abox`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "acb" => Submission.BoseGases.acube

set_option autoImplicit false

/-- The fibre lintegral of a measurable pair kernel is a.e.-measurable. -/
theorem aemeasurable_fibreLintegral {ℓ : ℝ} {e : E3 → E3 → ℝ}
    (he : Measurable (Function.uncurry e)) :
    AEMeasurable (fun w : E3 => ∫⁻ y', ‖e w y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
      (volume : Measure E3) := by
  have h2 : AEMeasurable (fun w : E3 => ∫⁻ y', ‖Function.uncurry e (w, y')‖ₑ
      ∂((volume : Measure E3).restrict (acb ℓ))) (volume : Measure E3) :=
    he.enorm.aemeasurable.lintegral_prod_right' (ν := (volume : Measure E3).restrict (acb ℓ))
  simpa only [Function.uncurry] using h2

/-- The first row integrand is a.e.-measurable on the product space. -/
theorem aemeasurable_row1 {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} {e : E3 → E3 → ℝ}
    (he : Measurable (Function.uncurry e)) :
    AEMeasurable (fun z : Xn n × (E3 × E3) => ‖e (z.1 p.2) z.2.1‖ₑ)
      (((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
        (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ)))) := by
  have hmap : Measurable (fun z : Xn n × (E3 × E3) => (z.1 p.2, z.2.1)) :=
    ((measurable_pi_apply p.2).comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have h1 : Measurable (fun z : Xn n × (E3 × E3) => ‖Function.uncurry e (z.1 p.2, z.2.1)‖ₑ) :=
    he.enorm.comp hmap
  simpa only [Function.uncurry] using h1.aemeasurable

/-- The slice measurability of the pair kernel. -/
theorem measurable_slice {e : E3 → E3 → ℝ} (he : Measurable (Function.uncurry e)) (a : E3) :
    Measurable (fun y : E3 => ‖e a y‖ₑ) := by
  have hmap : Measurable (fun y : E3 => (a, y)) := measurable_const.prodMk measurable_id
  have h1 : Measurable (fun y : E3 => ‖Function.uncurry e (a, y)‖ₑ) := he.enorm.comp hmap
  simpa only [Function.uncurry] using h1

/-- **The first row**: `∫∫∫ ‖e (x_{p.2}, y)‖` over the box square. -/
theorem int_row1 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} {e : E3 → E3 → ℝ}
    (he : Measurable (Function.uncurry e)) :
    ∫⁻ z : Xn n × (E3 × E3), ‖e (z.1 p.2) z.2.1‖ₑ
        ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
          (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))))
      = (volume : Measure E3) (acb ℓ)
        * ((volume : Measure E3) (acb ℓ) ^ (n - 1) * boxL1 ℓ e) := by
  have hVfin : (volume : Measure E3) (acb ℓ) ≠ ⊤ :=
    ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  rw [lintegral_prod _ (aemeasurable_row1 he)]
  have hinner : ∀ x : Xn n,
      (∫⁻ w : E3 × E3, ‖e (x p.2) w.1‖ₑ
        ∂(((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))))
        = (volume : Measure E3) (acb ℓ) * ∫⁻ y, ‖e (x p.2) y‖ₑ
            ∂((volume : Measure E3).restrict (acb ℓ)) := by
    intro x
    have h2 : AEMeasurable (fun w : E3 × E3 => ‖e (x p.2) w.1‖ₑ)
        (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))) := by
      have hmap : Measurable (fun w : E3 × E3 => (x p.2, w.1)) :=
        measurable_const.prodMk measurable_fst
      exact (he.enorm.comp hmap).aemeasurable
    rw [lintegral_prod _ h2]
    have h3 : ∀ y : E3, (∫⁻ u : E3, ‖e (x p.2) y‖ₑ
        ∂((volume : Measure E3).restrict (acb ℓ)))
        = ‖e (x p.2) y‖ₑ * (volume : Measure E3) (acb ℓ) := by
      intro y
      rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
    simp_rw [h3]
    rw [MeasureTheory.lintegral_mul_const _ (measurable_slice he (x p.2))]
    ring
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ hVfin]
  rw [Work.BoseFixB2.Pot.lintegral_coord_abox (n := n) (ℓ := ℓ) hℓ p.2
    (G := fun a : E3 => ∫⁻ y, ‖e a y‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
    (aemeasurable_fibreLintegral he).aestronglyMeasurable]
  rw [boxL1]

/-- The AEMeasurability of the second-row integrand. -/
theorem aemeasurable_row2 {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} {e : E3 → E3 → ℝ}
    (he : Measurable (Function.uncurry e)) :
    AEMeasurable (fun z : Xn n × (E3 × E3) =>
        ∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
      (((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
        (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ)))) := by
  have hmap : Measurable (fun q : (Xn n × (E3 × E3)) × E3 => (q.1.1 p.2, q.2)) :=
    (((measurable_pi_apply p.2).comp measurable_fst).comp measurable_fst).prodMk measurable_snd
  have h1 : Measurable (fun q : (Xn n × (E3 × E3)) × E3 => ‖e (q.1.1 p.2) q.2‖ₑ) := by
    have heq : (fun q : (Xn n × (E3 × E3)) × E3 => ‖e (q.1.1 p.2) q.2‖ₑ)
        = (fun x : E3 × E3 => ‖e x.1 x.2‖ₑ)
          ∘ (fun q : (Xn n × (E3 × E3)) × E3 => (q.1.1 p.2, q.2)) := rfl
    rw [heq]
    exact he.enorm.comp hmap
  have h2 : AEMeasurable (fun z : Xn n × (E3 × E3) => ∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
      ∂((volume : Measure E3).restrict (acb ℓ)))
      (((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
        (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ)))) :=
    h1.aemeasurable.lintegral_prod_right' (ν := (volume : Measure E3).restrict (acb ℓ))
  exact h2

/-- **The second row**: the `x`-only fibre integral. -/
theorem int_row2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} {e : E3 → E3 → ℝ}
    (he : Measurable (Function.uncurry e)) :
    ∫⁻ z : Xn n × (E3 × E3),
        (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
          (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))))
      = ((volume : Measure E3) (acb ℓ) * (volume : Measure E3) (acb ℓ))
        * ((volume : Measure E3) (acb ℓ) ^ (n - 1) * boxL1 ℓ e) := by
  have hVlt : (volume : Measure E3) (acb ℓ) < ⊤ :=
    Submission.BoseGases.acube_lt_top ℓ hℓ.le
  have hV2 : (volume : Measure E3) (acb ℓ) * (volume : Measure E3) (acb ℓ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_of_lt hVlt) (ne_of_lt hVlt)
  rw [lintegral_prod _ (aemeasurable_row2 he)]
  have hinner : ∀ x : Xn n,
      (∫⁻ w : E3 × E3, (∫⁻ y', ‖e (x p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))))
        = (∫⁻ y', ‖e (x p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
          * ((volume : Measure E3) (acb ℓ) * (volume : Measure E3) (acb ℓ)) := by
    intro x
    rw [MeasureTheory.lintegral_const, (Set.univ_prod_univ).symm, Measure.prod_prod]
    rw [Measure.restrict_apply_univ]
  rw [lintegral_congr hinner, lintegral_mul_const' _ _ hV2]
  rw [Work.BoseFixB2.Pot.lintegral_coord_abox (n := n) (ℓ := ℓ) hℓ p.2
    (G := fun a : E3 => ∫⁻ y', ‖e a y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
    (aemeasurable_fibreLintegral he).aestronglyMeasurable]
  rw [boxL1]
  ring

/-- The AEMeasurability of the third-row integrand. -/
theorem aemeasurable_row3 {n : ℕ} {ℓ : ℝ} {e : E3 → E3 → ℝ}
    (he : Measurable (Function.uncurry e)) :
    AEMeasurable (fun z : Xn n × (E3 × E3) =>
        ∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
      (((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
        (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ)))) := by
  have hmap : Measurable (fun q : (Xn n × (E3 × E3)) × E3 => (q.2, q.1.2.1)) :=
    measurable_snd.prodMk ((measurable_fst.comp measurable_snd).comp measurable_fst)
  have h1 : Measurable (fun q : (Xn n × (E3 × E3)) × E3 => ‖e q.2 q.1.2.1‖ₑ) := by
    have heq : (fun q : (Xn n × (E3 × E3)) × E3 => ‖e q.2 q.1.2.1‖ₑ)
        = (fun x : E3 × E3 => ‖e x.1 x.2‖ₑ)
          ∘ (fun q : (Xn n × (E3 × E3)) × E3 => (q.2, q.1.2.1)) := rfl
    rw [heq]
    exact he.enorm.comp hmap
  exact h1.aemeasurable.lintegral_prod_right' (ν := (volume : Measure E3).restrict (acb ℓ))

/-- **The third row**: the `y`-only fibre integral. -/
theorem int_row3 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : E3 → E3 → ℝ}
    (he : Measurable (Function.uncurry e)) :
    ∫⁻ z : Xn n × (E3 × E3),
        (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
          (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))))
      = ((volume : Measure E3) (acb ℓ) ^ n * (volume : Measure E3) (acb ℓ)) * boxL1 ℓ e := by
  have hVlt : (volume : Measure E3) (acb ℓ) < ⊤ :=
    Submission.BoseGases.acube_lt_top ℓ hℓ.le
  have hμx : ((volume : Measure (Xn n)).restrict (abx n ℓ)) Set.univ
      = (volume : Measure E3) (acb ℓ) ^ n := by
    rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume n ℓ hℓ.le,
      Submission.BoseGases.acube_volume ℓ hℓ.le,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ℓ ^ 3) n]
  rw [lintegral_prod _ (aemeasurable_row3 he)]
  have hinner : ∀ x : Xn n,
      (∫⁻ w : E3 × E3, (∫⁻ w', ‖e w' w.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))))
        = (∫⁻ y, (∫⁻ w', ‖e w' y‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
            ∂((volume : Measure E3).restrict (acb ℓ))) * (volume : Measure E3) (acb ℓ) := by
    intro x
    have h2 : AEMeasurable (fun w : E3 × E3 => (∫⁻ w', ‖e w' w.1‖ₑ
        ∂((volume : Measure E3).restrict (acb ℓ))))
        (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))) := by
      have hmap : Measurable (fun q : (E3 × E3) × E3 => (q.2, q.1.1)) :=
        measurable_snd.prodMk (measurable_fst.comp measurable_fst)
      have h1 : Measurable (fun q : (E3 × E3) × E3 => ‖e q.2 q.1.1‖ₑ) := by
        have heq : (fun q : (E3 × E3) × E3 => ‖e q.2 q.1.1‖ₑ)
            = (fun x : E3 × E3 => ‖e x.1 x.2‖ₑ)
              ∘ (fun q : (E3 × E3) × E3 => (q.2, q.1.1)) := rfl
        rw [heq]
        exact he.enorm.comp hmap
      exact h1.aemeasurable.lintegral_prod_right' (ν := (volume : Measure E3).restrict (acb ℓ))
    rw [lintegral_prod _ h2]
    have h3 : ∀ y : E3, (∫⁻ u : E3, (∫⁻ w', ‖e w' y‖ₑ
        ∂((volume : Measure E3).restrict (acb ℓ))) ∂((volume : Measure E3).restrict (acb ℓ)))
        = (∫⁻ w', ‖e w' y‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
          * (volume : Measure E3) (acb ℓ) := by
      intro y
      rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
    rw [lintegral_congr h3, MeasureTheory.lintegral_mul_const' _ _ (ne_of_lt hVlt)]
  rw [lintegral_congr hinner]
  have hμx' : (volume : Measure (Xn n)) (abx n ℓ) = (volume : Measure E3) (acb ℓ) ^ n := by
    rw [← Measure.restrict_apply_univ]
    exact hμx
  rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, hμx']
  have hswap : (∫⁻ y, (∫⁻ w', ‖e w' y‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
      ∂((volume : Measure E3).restrict (acb ℓ)))
      = ∫⁻ w', ∫⁻ y, ‖e w' y‖ₑ ∂((volume : Measure E3).restrict (acb ℓ))
          ∂((volume : Measure E3).restrict (acb ℓ)) := by
    refine lintegral_lintegral_swap (μ := (volume : Measure E3).restrict (acb ℓ))
      (ν := (volume : Measure E3).restrict (acb ℓ)) (f := fun a b => ‖e b a‖ₑ) ?_
    exact (he.enorm.comp measurable_swap).aemeasurable
  rw [hswap, boxL1]
  ring

/-- **The fourth row**: the constant row. -/
theorem int_row4 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (e : E3 → E3 → ℝ) :
    ∫⁻ _z : Xn n × (E3 × E3), boxL1 ℓ e
        ∂(((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
          (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))))
      = ((volume : Measure E3) (acb ℓ) ^ n
          * ((volume : Measure E3) (acb ℓ) * (volume : Measure E3) (acb ℓ))) * boxL1 ℓ e := by
  have hμx : ((volume : Measure (Xn n)).restrict (abx n ℓ)) Set.univ
      = (volume : Measure E3) (acb ℓ) ^ n := by
    rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume n ℓ hℓ.le,
      Submission.BoseGases.acube_volume ℓ hℓ.le,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ℓ ^ 3) n]
  have hN : (((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
      (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))))
        Set.univ
      = (volume : Measure E3) (acb ℓ) ^ n
        * ((volume : Measure E3) (acb ℓ) * (volume : Measure E3) (acb ℓ)) := by
    rw [show (Set.univ : Set (Xn n × (E3 × E3)))
        = (Set.univ : Set (Xn n)) ×ˢ (Set.univ : Set (E3 × E3)) from (Set.univ_prod_univ).symm,
      Measure.prod_prod]
    rw [show (Set.univ : Set (E3 × E3)) = Set.univ ×ˢ Set.univ from (Set.univ_prod_univ).symm,
      Measure.prod_prod, hμx]
    rw [Measure.restrict_apply_univ]
  rw [MeasureTheory.lintegral_const, hN]
  ring

/-! ## 2. The `L¹` bound of the block-`I` row integrand

The four rows are summed and integrated against the box measure: the pointwise domination
`rowProd_enorm_le_rowDom` (`dict13RowDomLe`) is combined with the indicator of the two cube
coordinates (which is where the state factor vanishes) and the four explicit row integrals
`int_row1`–`int_row4` above.  The result is `lintegral_rowProd_bound`, the `L¹` domination used by
`dict13Aux6`. -/

/-- The measure `μx ⊗ (volume ⊗ volume)` on `Xn n × (ℝ³ × ℝ³)`, `μx` the box measure. -/
noncomputable def bigM13 (n : ℕ) (ℓ : ℝ) : Measure (Xn n × (E3 × E3)) :=
  ((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
    ((volume : Measure E3).prod (volume : Measure E3))

/-- The measure `μx ⊗ (ν ⊗ ν)` on `Xn n × (ℝ³ × ℝ³)`, `ν` the cube measure. -/
noncomputable def smallM (n : ℕ) (ℓ : ℝ) : Measure (Xn n × (E3 × E3)) :=
  ((volume : Measure (Xn n)).restrict (abx n ℓ)).prod
    (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ)))

/-- Restricting the full-volume measure to the two cube coordinates gives the cube measure. -/
theorem bigM_restrict_eq_smallM (n : ℕ) (ℓ : ℝ) :
    (bigM13 n ℓ).restrict {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ} = smallM n ℓ := by
  rw [bigM13, smallM,
    show {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ}
        = Set.univ ×ˢ (acb ℓ ×ˢ acb ℓ) from by
      ext z; simp [Set.mem_prod],
    ← Measure.prod_restrict, Measure.restrict_univ, ← Measure.prod_restrict]

/-- **The indicator conversion.**  Inserting the indicator of the two cube coordinates converts the
full-volume measure into the cube measure. -/
theorem lintegral_indicator_pair {n : ℕ} {ℓ : ℝ} (F : Xn n × (E3 × E3) → ENNReal) :
    ∫⁻ z : Xn n × (E3 × E3),
        (Set.indicator {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ} (fun _ => 1) z) * F z
        ∂(bigM13 n ℓ)
      = ∫⁻ z : Xn n × (E3 × E3), F z ∂(smallM n ℓ) := by
  have hSmeas : MeasurableSet {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ} :=
    MeasurableSet.preimage
      ((Submission.BoseGases.acube_measurable ℓ).prod (Submission.BoseGases.acube_measurable ℓ))
      measurable_snd
  have hpoint : ∀ z : Xn n × (E3 × E3),
      (Set.indicator {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ} (fun _ => 1) z) * F z
        = Set.indicator {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ} F z := by
    intro z
    by_cases hz : z ∈ {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ}
    · simp only [Set.indicator_of_mem hz, one_mul]
    · simp only [Set.indicator_of_notMem hz, zero_mul]
  rw [lintegral_congr hpoint, lintegral_indicator hSmeas, bigM_restrict_eq_smallM]

/-- Five-fold monotonicity of the product in `ENNReal`. -/
theorem mul5_le_mul5 {a b c d f a' b' c' d' f' : ENNReal} (ha : a ≤ a') (hb : b ≤ b')
    (hc : c ≤ c') (hd : d ≤ d') (hf : f ≤ f') :
    a * b * c * d * f ≤ a' * b' * c' * d' * f' :=
  mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' ha hb) hc) hd) hf

/-- **The `L¹` bound of the block-`I` row integrand.**  The `lintegral` of the `rowShape13`
integrand at the `Q M Q` kernel of `e` is bounded by a constant (depending on the state bounds and
on `n`, `ℓ`) times the double cube integral of `‖e‖`. -/
theorem lintegral_rowProd_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Xn n → ℂ} {A B : E3 → ℂ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {BΘ BA BB : ENNReal}
    (hΘs : Function.support Θ ⊆ abx n ℓ)
    (hΘb : ∀ x, ‖Θ x‖ₑ ≤ BΘ) (hAb : ∀ y, ‖A y‖ₑ ≤ BA) (hBb : ∀ y, ‖B y‖ₑ ≤ BB)
    (hΘf : BΘ ≠ ⊤) (hAf : BA ≠ ⊤) (hBf : BB ≠ ⊤) :
    ∃ K : ENNReal, K ≠ ⊤ ∧ ∀ e : E3 → E3 → ℝ, Measurable (Function.uncurry e) →
      ∫⁻ z, ‖rowProd Θ A B (qmqKernel ℓ e) p z‖ₑ ∂(bigM13 n ℓ) ≤ K * boxL1 ℓ e := by
  set V : ENNReal := (volume : Measure E3) (acb ℓ) with hV
  set cV : ENNReal := ENNReal.ofReal ((ℓ ^ 3)⁻¹) with hcV
  set Cst : ENNReal := BΘ * BA * BB * BΘ with hCst
  set KL : ENNReal := V * V ^ (n - 1) + cV * (V * V) * V ^ (n - 1) + cV * (V ^ n * V)
    + cV ^ 2 * (V ^ n * (V * V)) with hKL
  have hVtop : V ≠ ⊤ := by
    rw [hV]; exact ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  have hcVtop : cV ≠ ⊤ := by rw [hcV]; exact ENNReal.ofReal_ne_top
  have hCtop : Cst ≠ ⊤ := by
    rw [hCst]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hΘf hAf) hBf) hΘf
  have hVlt : V < ⊤ := lt_top_iff_ne_top.mpr hVtop
  have hcVlt : cV < ⊤ := lt_top_iff_ne_top.mpr hcVtop
  have hKLlt : KL < ⊤ := by
    rw [hKL]
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr
        ⟨ENNReal.add_lt_top.mpr
          ⟨ENNReal.mul_lt_top hVlt (ENNReal.pow_lt_top hVlt),
            ENNReal.mul_lt_top (ENNReal.mul_lt_top hcVlt (ENNReal.mul_lt_top hVlt hVlt))
              (ENNReal.pow_lt_top hVlt)⟩,
          ENNReal.mul_lt_top hcVlt (ENNReal.mul_lt_top (ENNReal.pow_lt_top hVlt) hVlt)⟩,
        ENNReal.mul_lt_top (ENNReal.pow_lt_top hcVlt)
          (ENNReal.mul_lt_top (ENNReal.pow_lt_top hVlt)
            (ENNReal.mul_lt_top hVlt hVlt))⟩
  refine ⟨Cst * KL, ENNReal.mul_ne_top hCtop (ne_of_lt hKLlt), ?_⟩
  intro e he
  have hΘzero : ∀ x : Xn n, x ∉ abx n ℓ → Θ x = 0 := by
    intro x hx
    by_contra h
    exact hx (hΘs (Function.mem_support.mpr h))
  have hupd1 : ∀ (x : Xn n) (y u : E3),
      (Function.update (Function.update x p.1 y) p.2 u) p.1 = y := by
    intro x y u
    rw [Function.update_of_ne hp, Function.update_self]
  have hupd2 : ∀ (x : Xn n) (y u : E3),
      (Function.update (Function.update x p.1 y) p.2 u) p.2 = u := by
    intro x y u
    rw [Function.update_self]
  -- the pointwise bound, with the indicator of the two cube coordinates
  have hpt : ∀ z : Xn n × (E3 × E3),
      ‖rowProd Θ A B (qmqKernel ℓ e) p z‖ₑ
        ≤ (Set.indicator {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ} (fun _ => 1) z)
            * (Cst * (‖e (z.1 p.2) z.2.1‖ₑ
                + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
                    ∂((volume : Measure E3).restrict (acb ℓ)))
                + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ
                    ∂((volume : Measure E3).restrict (acb ℓ)))
                + cV ^ 2 * boxL1 ℓ e)) := by
    intro z
    by_cases hz : z ∈ {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ}
    · rw [Set.indicator_of_mem hz, one_mul]
      refine (rowProd_enorm_le_rowDom hℓ z).trans ?_
      rw [rowDom, hcV, hCst, boxL1]
      exact mul5_le_mul5 (hΘb z.1) (hAb (z.1 p.1)) (hBb z.2.2)
        (hΘb (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2)) le_rfl
    · rw [Set.indicator_of_notMem hz, zero_mul]
      have hz2 : z.2 ∉ acb ℓ ×ˢ acb ℓ := hz
      have hcases : z.2.1 ∉ acb ℓ ∨ z.2.2 ∉ acb ℓ := by
        by_contra h
        rw [not_or, not_not, not_not] at h
        exact hz2 (by rw [Set.mem_prod]; exact h)
      have hzero : Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) = 0 := by
        rcases hcases with hy | hu
        · exact hΘzero _ (fun hmem => hy (by
            rw [← hupd1 z.1 z.2.1 z.2.2]
            exact (Submission.BoseGases.mem_abox_iff n ℓ _).mp hmem p.1))
        · exact hΘzero _ (fun hmem => hu (by
            rw [← hupd2 z.1 z.2.1 z.2.2]
            exact (Submission.BoseGases.mem_abox_iff n ℓ _).mp hmem p.2))
      have hf0 : ‖rowProd Θ A B (qmqKernel ℓ e) p z‖ₑ = 0 := by
        simp only [rowProd, rowInt, hzero, mul_zero, enorm_zero]
      rw [hf0]
  -- the four row integrals
  have h1 : (∫⁻ z : Xn n × (E3 × E3), ‖e (z.1 p.2) z.2.1‖ₑ ∂(smallM n ℓ))
      = V * (V ^ (n - 1) * boxL1 ℓ e) := by
    rw [hV]
    exact int_row1 (n := n) (ℓ := ℓ) (p := p) (e := e) hℓ he
  have h2 : (∫⁻ z : Xn n × (E3 × E3),
        (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(smallM n ℓ))
      = (V * V) * (V ^ (n - 1) * boxL1 ℓ e) := by
    rw [hV]
    exact int_row2 (n := n) (ℓ := ℓ) (p := p) (e := e) hℓ he
  have h3 : (∫⁻ z : Xn n × (E3 × E3),
        (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(smallM n ℓ))
      = (V ^ n * V) * boxL1 ℓ e := by
    rw [hV]
    exact int_row3 (n := n) (ℓ := ℓ) (e := e) hℓ he
  have h4 : (∫⁻ _z : Xn n × (E3 × E3), boxL1 ℓ e ∂(smallM n ℓ))
      = (V ^ n * (V * V)) * boxL1 ℓ e := by
    rw [hV]
    exact int_row4 (n := n) (ℓ := ℓ) hℓ e
  -- the measure of the cube product
  have hmass : (smallM n ℓ) Set.univ = V ^ n * (V * V) := by
    have hμx : ((volume : Measure (Xn n)).restrict (abx n ℓ)) Set.univ = V ^ n := by
      rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume n ℓ hℓ.le, hV,
        Submission.BoseGases.acube_volume ℓ hℓ.le,
        ← ENNReal.ofReal_pow (p := ℓ ^ 3) (by positivity) n]
    have hν : ((volume : Measure E3).restrict (acb ℓ)) Set.univ = V := by
      rw [Measure.restrict_apply_univ, hV]
    rw [smallM,
      show (Set.univ : Set (Xn n × (E3 × E3)))
          = Set.univ ×ˢ (Set.univ : Set (E3 × E3)) from (Set.univ_prod_univ).symm,
      Measure.prod_prod,
      show (Set.univ : Set (E3 × E3)) = (Set.univ : Set E3) ×ˢ (Set.univ : Set E3)
          from (Set.univ_prod_univ).symm,
      Measure.prod_prod, hμx, hν]
  -- the decomposition of the sum integral
  have hA12 : AEMeasurable (fun z : Xn n × (E3 × E3) =>
      ‖e (z.1 p.2) z.2.1‖ₑ + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
        ∂((volume : Measure E3).restrict (acb ℓ)))) (smallM n ℓ) :=
    (aemeasurable_row1 (n := n) (ℓ := ℓ) (p := p) (e := e) he).add
      ((aemeasurable_row2 (n := n) (ℓ := ℓ) (p := p) (e := e) he).const_mul cV)
  have hA123 : AEMeasurable (fun z : Xn n × (E3 × E3) =>
      ‖e (z.1 p.2) z.2.1‖ₑ + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
        ∂((volume : Measure E3).restrict (acb ℓ)))
      + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ))))
      (smallM n ℓ) :=
    hA12.add ((aemeasurable_row3 (n := n) (ℓ := ℓ) (e := e) he).const_mul cV)
  have e1 : (∫⁻ z : Xn n × (E3 × E3),
        ‖e (z.1 p.2) z.2.1‖ₑ + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
          ∂((volume : Measure E3).restrict (acb ℓ)))
        + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        + cV ^ 2 * boxL1 ℓ e ∂(smallM n ℓ))
      = (∫⁻ z : Xn n × (E3 × E3),
          ‖e (z.1 p.2) z.2.1‖ₑ + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
            ∂((volume : Measure E3).restrict (acb ℓ)))
          + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ
            ∂((volume : Measure E3).restrict (acb ℓ))) ∂(smallM n ℓ))
        + ∫⁻ z : Xn n × (E3 × E3), cV ^ 2 * boxL1 ℓ e ∂(smallM n ℓ) :=
    lintegral_add_left' hA123 _
  have e2 : (∫⁻ z : Xn n × (E3 × E3),
        ‖e (z.1 p.2) z.2.1‖ₑ + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
          ∂((volume : Measure E3).restrict (acb ℓ)))
        + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(smallM n ℓ))
      = (∫⁻ z : Xn n × (E3 × E3),
          ‖e (z.1 p.2) z.2.1‖ₑ + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
            ∂((volume : Measure E3).restrict (acb ℓ))) ∂(smallM n ℓ))
        + ∫⁻ z : Xn n × (E3 × E3), cV * (∫⁻ w', ‖e w' z.2.1‖ₑ
            ∂((volume : Measure E3).restrict (acb ℓ))) ∂(smallM n ℓ) :=
    lintegral_add_left' hA12 _
  have e3 : (∫⁻ z : Xn n × (E3 × E3),
        ‖e (z.1 p.2) z.2.1‖ₑ + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
          ∂((volume : Measure E3).restrict (acb ℓ))) ∂(smallM n ℓ))
      = (∫⁻ z : Xn n × (E3 × E3), ‖e (z.1 p.2) z.2.1‖ₑ ∂(smallM n ℓ))
        + ∫⁻ z : Xn n × (E3 × E3), cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
            ∂((volume : Measure E3).restrict (acb ℓ))) ∂(smallM n ℓ) :=
    lintegral_add_left' (aemeasurable_row1 (n := n) (ℓ := ℓ) (p := p) (e := e) he) _
  have e4 : (∫⁻ z : Xn n × (E3 × E3),
        cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(smallM n ℓ))
      = cV * (∫⁻ z : Xn n × (E3 × E3),
          (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
          ∂(smallM n ℓ)) :=
    lintegral_const_mul' cV _ hcVtop
  have e5 : (∫⁻ z : Xn n × (E3 × E3),
        cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        ∂(smallM n ℓ))
      = cV * (∫⁻ z : Xn n × (E3 × E3),
          (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
          ∂(smallM n ℓ)) :=
    lintegral_const_mul' cV _ hcVtop
  have e6 : (∫⁻ z : Xn n × (E3 × E3), cV ^ 2 * boxL1 ℓ e ∂(smallM n ℓ))
      = (cV ^ 2 * boxL1 ℓ e) * (V ^ n * (V * V)) := by
    rw [lintegral_const, hmass]
  -- the sum integral equals `KL · ∬`
  have hsum : (∫⁻ z : Xn n × (E3 × E3),
        ‖e (z.1 p.2) z.2.1‖ₑ + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
          ∂((volume : Measure E3).restrict (acb ℓ)))
        + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        + cV ^ 2 * boxL1 ℓ e ∂(smallM n ℓ)) = KL * boxL1 ℓ e := by
    rw [e1, e2, e3, e4, e5, e6, h1, h2, h3]
    rw [hKL]
    ring
  -- the constant prefactor
  have hsplit : (∫⁻ z : Xn n × (E3 × E3),
        Cst * (‖e (z.1 p.2) z.2.1‖ₑ
          + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
          + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
          + cV ^ 2 * boxL1 ℓ e) ∂(smallM n ℓ)) = Cst * (KL * boxL1 ℓ e) := by
    rw [lintegral_const_mul' Cst (fun z : Xn n × (E3 × E3) =>
      ‖e (z.1 p.2) z.2.1‖ₑ
        + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
        + cV ^ 2 * boxL1 ℓ e) hCtop, hsum]
  calc ∫⁻ z, ‖rowProd Θ A B (qmqKernel ℓ e) p z‖ₑ ∂(bigM13 n ℓ)
      ≤ ∫⁻ z, (Set.indicator {z : Xn n × (E3 × E3) | z.2 ∈ acb ℓ ×ˢ acb ℓ} (fun _ => 1) z)
            * (Cst * (‖e (z.1 p.2) z.2.1‖ₑ
                + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ
                    ∂((volume : Measure E3).restrict (acb ℓ)))
                + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ
                    ∂((volume : Measure E3).restrict (acb ℓ)))
                + cV ^ 2 * boxL1 ℓ e)) ∂(bigM13 n ℓ) :=
        lintegral_mono hpt
    _ = ∫⁻ z, Cst * (‖e (z.1 p.2) z.2.1‖ₑ
          + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
          + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
          + cV ^ 2 * boxL1 ℓ e) ∂(smallM n ℓ) :=
        lintegral_indicator_pair (fun z : Xn n × (E3 × E3) =>
          Cst * (‖e (z.1 p.2) z.2.1‖ₑ
            + cV * (∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
            + cV * (∫⁻ w', ‖e w' z.2.1‖ₑ ∂((volume : Measure E3).restrict (acb ℓ)))
            + cV ^ 2 * boxL1 ℓ e))
    _ = Cst * (KL * boxL1 ℓ e) := hsplit
    _ = (Cst * KL) * boxL1 ℓ e := (mul_assoc Cst KL (boxL1 ℓ e)).symm

end Work.BoseBoxFock
