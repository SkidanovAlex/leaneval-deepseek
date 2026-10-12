import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.chiW1_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.Bchan_chiChatC_integrableOn`

Integrability over the `n`-particle box `abox n ℓ` of the `ℂ`-valued one-slot
"chat" function

`x ↦ χ_ℓ(x_j) · ∫ y, χ_ℓ(y) · W₁(y − x_j)`,

where `χ_ℓ = corpusBox.chiLam ℓ` is the corpus localisation function on the box
of side `ℓ` and `W₁ = W1fun v h ℓ` is FS's `W(1−ω)`.

## Argument

This is the complex-valued companion of the (proved) real-valued
`Work.BoseBoxFock.PCFU.Bchan_chiChat_integrableOn`; the absolute values there
are replaced by the (multiplicative) complex norm, and no new analysis is
needed.

1. `Work.BoseBoxFock.PCFU.chiW1_integrable` gives the joint integrability of
   the renormalised pair kernel `(p, q) ↦ χ_ℓ(p)·W₁(p − q)·χ_ℓ(q)` with respect
   to `volume × volume`.  Its `ℂ`-valued version (the pointwise `ofReal` of that
   real kernel) is integrable by `Integrable.ofReal`.
2. Fubini (`MeasureTheory.Integrable.integral_prod_right`) then shows that

       a ↦ ∫ y, χ_ℓ(y) · (χ_ℓ a · W₁(y − a))

   is integrable on `ℝ³`; pulling the constant `χ_ℓ(a)` out of the integral
   (`MeasureTheory.integral_mul_const`) shows that the one-particle profile

       H a := χ_ℓ(a) · ∫ y, χ_ℓ(y) · W₁(y − a)

   is integrable on `ℝ³`.
3. A `ℂ`-valued one-particle function integrable on the cube `acube ℓ` pulls
   back to any coordinate of the box: the box measure is the product of the cube
   measures (`Submission.BoseGases.restrict_abox_eq_pi`), the pushforward along
   the `j`-th coordinate is a finite scalar multiple of the cube measure
   (`Measure.pi_map_eval`), and integrability survives the map
   (`MeasureTheory.Integrable.comp_measurable`).  This is the auxiliary lemma
   `integrableOn_coord_pullback_abox_complex` below (the verbatim `ℂ`-valued
   twin of `Work.BoseBoxFock.PCFU.integrableOn_coord_pullback_abox`).
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

/-- **One-coordinate pullback, `ℂ`-valued form.**  A one-particle complex
function integrable on the centred cube `acube ℓ` is integrable, composed with
the `j`-th coordinate, on the `n`-particle centred box `abox n ℓ`. -/
lemma integrableOn_coord_pullback_abox_complex {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {G : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : MeasureTheory.IntegrableOn G (Submission.BoseGases.acube ℓ) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => G (x j))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  let μ : Fin n → Measure (EuclideanSpace ℝ (Fin 3)) :=
    fun _ => (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)
  -- the pushforward of the box measure along the `j`-th coordinate
  have hmap : (Measure.pi μ).map (Function.eval j)
      = (∏ k ∈ Finset.univ.erase j, μ k Set.univ) • μ j := Measure.pi_map_eval μ j
  have hcard : (Finset.univ.erase j : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hμ : ∀ k : Fin n, μ k Set.univ = ENNReal.ofReal (ℓ ^ 3) := by
    intro k
    simp only [μ]
    rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
  have hprod : (∏ k ∈ Finset.univ.erase j, μ k Set.univ)
      = ENNReal.ofReal ((ℓ ^ 3) ^ (n - 1)) := by
    rw [Finset.prod_congr rfl (fun k _ => hμ k), Finset.prod_const, hcard]
    exact (ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ℓ ^ 3) (n - 1)).symm
  have hintμ : Integrable G (μ j) := hG
  have hintmap : Integrable G ((Measure.pi μ).map (Function.eval j)) := by
    rw [hmap, hprod]
    exact hintμ.smul_measure ENNReal.ofReal_ne_top
  have hintpi : Integrable (fun x : Submission.BoseGases.X n => G (x j)) (Measure.pi μ) := by
    have hh := hintmap.comp_measurable (measurable_pi_apply j)
    simpa [Function.comp_def] using hh
  rw [show MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => G (x j))
        (Submission.BoseGases.abox n ℓ) MeasureTheory.volume
      = Integrable (fun x : Submission.BoseGases.X n => G (x j))
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))
      from rfl]
  rw [Submission.BoseGases.restrict_abox_eq_pi n ℓ]
  exact hintpi

theorem Bchan_chiChatC_integrableOn {n : ℕ} {j : Fin n}
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
        * (∫ y : EuclideanSpace ℝ (Fin 3),
            ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
              * ((Work.BoseFixR.W1fun v h ℓ (y - x j) : ℝ) : ℂ)))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  -- ## 1. The `ℂ`-valued pair kernel `χ_ℓ(p)·W₁(p−q)·χ_ℓ(q)` is `L¹` on `ℝ³ × ℝ³`
  have hKr : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ p.1 * Work.BoseFixR.W1fun v h ℓ (p.1 - p.2)
        * Submission.BoseGases.chiScale ℓ p.2)
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod volume) :=
    Work.BoseBoxFock.PCFU.chiW1_integrable h hℓ
  have hKc : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiScale ℓ p.1 : ℂ)
        * (Work.BoseFixR.W1fun v h ℓ (p.1 - p.2) : ℂ)
        * (Submission.BoseGases.chiScale ℓ p.2 : ℂ))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod volume) := by
    refine hKr.ofReal.congr ?_
    filter_upwards with p
    push_cast
    rfl
  -- ## 2. Fubini in the second slot, then pull out the constant `χ_ℓ(a)`
  have hH : Integrable (fun a : EuclideanSpace ℝ (Fin 3) =>
      ∫ y : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiScale ℓ y : ℂ) * (Work.BoseFixR.W1fun v h ℓ (y - a) : ℂ)
          * (Submission.BoseGases.chiScale ℓ a : ℂ)) volume :=
    hKc.integral_prod_right
  have hH' : Integrable (fun a : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiScale ℓ a : ℂ)
        * ∫ y : EuclideanSpace ℝ (Fin 3),
            (Submission.BoseGases.chiScale ℓ y : ℂ) * (Work.BoseFixR.W1fun v h ℓ (y - a) : ℂ))
      volume := by
    refine hH.congr ?_
    filter_upwards with a
    rw [MeasureTheory.integral_mul_const]
    rw [mul_comm]
  -- ## 3. Pull back along the `j`-th coordinate
  have hfin := integrableOn_coord_pullback_abox_complex hℓ j hH'.integrableOn
  simp only [Submission.BoseGases.chiScale, Work.BoseB4.BoxData.chiLam,
    Work.BoseK15.corpusBox_chi] at hfin ⊢
  exact hfin

end Work.BoseBoxFock.PCFU
