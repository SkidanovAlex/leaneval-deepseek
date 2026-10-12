import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.selfPairG
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.boxAnnOf_boxAnnOf_comm`

The box annihilation of the superposition `η_w = Σ_l w_l e_l` on the `k`-particle space is

    `(boxAnnOf e w k Θ)(y) = √(k+1) · ∫_z conj(η_w z) · Θ (z, y)`

(`Work.BoseDict.boxAnnOf`).  This module proves that **the two superposed annihilations of a
symmetric `(d+2)`-particle function commute**:

    `boxAnnOf e u d (boxAnnOf e v (d+1) Θ) = boxAnnOf e v d (boxAnnOf e u (d+1) Θ)`

for `Θ` invariant under every permutation of the particle labels (`hΘsym`).  This is the box-side
form of the model identity `annOf m u (annOf m v Ψ) = annOf m v (annOf m u Ψ)` transported by
`Work.BoseDict.boxRealise_annOf_annOf`.

## Proof

1. `boxAnnOf_boxAnnOf_apply` — the **double peel** (no hypothesis at all): unfolding the two
   definitions and using only the unconditional identities `integral_mul_const` /
   `integral_const_mul` of the Bochner integral (the constant of the inner annihilation is pulled
   out of the two integrals),

       `boxAnnOf e u d (boxAnnOf e v (d+1) Θ) y
          = √(d+1)·√(d+2) · ∫_z ∫_w conj(η_u z)·(conj(η_v w)·Θ(w,z,y))`.

   (This step needs no integrability: `∫ r·f = r·∫ f` holds by definition of the Bochner
   integral on the whole space of functions.)

2. The two peeled expressions differ by (a) the **order of the two integrations** and (b) the
   exchange of the first two particle slots of `Θ`, which is exactly the hypothesis `hΘsym` at
   the transposition `Equiv.swap 0 1` (`Matrix.cons_cons_comp_swap_zero_one`).  Concretely, writing
   `H z w = conj(η_u z)·(conj(η_v w)·Θ (w,z,y))`, the second peel is
   `∫_z ∫_w H w z` (by symmetry of `Θ` and commutativity in `ℂ`), and
   `∫_z ∫_w H z w = ∫_w ∫_z H z w = ∫_z ∫_w H w z` is Fubini (`integral_integral_swap`) followed
   by the renaming of the two bound variables (definitional).

3. The Fubini step needs `H` to be **jointly integrable** on `Sp × Sp`.  This holds because the
   modes are supported in the box `boxL ℓ` (`etaOf` is therefore supported there), `Θ` and the
   modes are everywhere bounded, and the box has finite measure:
   `Work.MB.integrable_of_bdd_of_support` applied on the product of the box with itself.

The whole argument uses the hypotheses `hmeas`, `hbdd`, `hsupp`, `hΘm`, `hΘb` and `hΘsym`; the
support hypothesis `hΘsupp` is not needed.
-/

namespace Work.BoseBoxFock.PotCubicLowBandAux

open MeasureTheory
open scoped BigOperators
open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The double peel.**  Unfolding both annihilations, the composed box annihilation of the
superposition `η_u` and `η_v` on a `(d+2)`-particle function `Θ` is the double integral
`√(d+1)·√(d+2)·∫_z ∫_w conj(η_u z)·(conj(η_v w)·Θ (w,z,y))`.

No hypothesis is needed: the two `integral_const_mul`/`integral_mul_const` steps are
unconditional identities of the Bochner integral. -/
private lemma boxAnnOf_boxAnnOf_apply {m d : ℕ} {e : Fin m → Sp → ℂ} (u v : Fin m → ℝ)
    (Θ : Xn (d + 2) → ℂ) (y : Xn d) :
    boxAnnOf e u d (boxAnnOf e v (d + 1) Θ) y
      = ((Real.sqrt ((d : ℝ) + 1) : ℂ) * (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ))
        * ∫ z : Sp, ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
            * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
  have hB : (∫ z : Sp, (starRingEnd ℂ) (etaOf e u z) * boxAnnOf e v (d + 1) Θ (Fin.cons z y))
      = ∫ z : Sp, (starRingEnd ℂ) (etaOf e u z)
          * ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
              * ∫ w : Sp, (starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [show boxAnnOf e v (d + 1) Θ (Fin.cons z y)
        = (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
            * ∫ w : Sp, (starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)) from rfl]
  have hinner : ∀ z : Sp, (starRingEnd ℂ) (etaOf e u z)
        * (∫ w : Sp, (starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))
      = ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
          * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
    intro z
    calc (starRingEnd ℂ) (etaOf e u z)
          * (∫ w : Sp, (starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))
        = (∫ w : Sp, (starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))
            * (starRingEnd ℂ) (etaOf e u z) := mul_comm _ _
      _ = ∫ w : Sp, ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))
              * (starRingEnd ℂ) (etaOf e u z) :=
            (MeasureTheory.integral_mul_const ((starRingEnd ℂ) (etaOf e u z))
              (fun w : Sp => (starRingEnd ℂ) (etaOf e v w)
                * Θ (Fin.cons w (Fin.cons z y)))).symm
      _ = ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
              * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)
  have hC : (∫ z : Sp, (starRingEnd ℂ) (etaOf e u z)
        * ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
            * ∫ w : Sp, (starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))))
      = ∫ z : Sp, (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
          * ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
              * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    calc (starRingEnd ℂ) (etaOf e u z)
          * ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
              * ∫ w : Sp, (starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))
        = (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
            * ((starRingEnd ℂ) (etaOf e u z)
                * ∫ w : Sp, (starRingEnd ℂ) (etaOf e v w)
                    * Θ (Fin.cons w (Fin.cons z y))) := by ring
      _ = (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
            * ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
                * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
            rw [hinner z]
  have hD : (∫ z : Sp, (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
        * ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
            * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))))
      = (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
        * ∫ z : Sp, ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
            * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) :=
    MeasureTheory.integral_const_mul _ _
  calc boxAnnOf e u d (boxAnnOf e v (d + 1) Θ) y
      = (Real.sqrt ((d : ℝ) + 1) : ℂ)
          * ∫ z : Sp, (starRingEnd ℂ) (etaOf e u z) * boxAnnOf e v (d + 1) Θ (Fin.cons z y) := rfl
    _ = (Real.sqrt ((d : ℝ) + 1) : ℂ)
          * ∫ z : Sp, (starRingEnd ℂ) (etaOf e u z)
              * ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
                  * ∫ w : Sp, (starRingEnd ℂ) (etaOf e v w)
                      * Θ (Fin.cons w (Fin.cons z y))) := by
          rw [hB]
    _ = (Real.sqrt ((d : ℝ) + 1) : ℂ)
          * ∫ z : Sp, (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
              * ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
                  * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
          rw [hC]
    _ = (Real.sqrt ((d : ℝ) + 1) : ℂ)
          * ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ)
              * ∫ z : Sp, ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
                  * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))) := by
          rw [hD]
    _ = ((Real.sqrt ((d : ℝ) + 1) : ℂ) * (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ))
          * ∫ z : Sp, ∫ w : Sp, (starRingEnd ℂ) (etaOf e u z)
              * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by ring

theorem boxAnnOf_boxAnnOf_comm {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (u v : Fin m → ℝ) {Θ : Work.BoseDict.Xn (d + 2) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x) :
    Work.BoseDict.boxAnnOf e u d (Work.BoseDict.boxAnnOf e v (d + 1) Θ)
      = Work.BoseDict.boxAnnOf e v d (Work.BoseDict.boxAnnOf e u (d + 1) Θ) := by
  classical
  funext y
  -- the boxes have finite measure, and `etaOf`/`Θ` are measurable and everywhere bounded
  have hu_meas : Measurable (etaOf e u) := Work.MB.etaOf_weak_measurable hmeas u
  have hv_meas : Measurable (etaOf e v) := Work.MB.etaOf_weak_measurable hmeas v
  have hu_supp : Function.support (etaOf e u) ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    Work.MB.etaOf_weak_support hsupp u
  have hv_supp : Function.support (etaOf e v) ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    Work.MB.etaOf_weak_support hsupp v
  obtain ⟨Cu, hCu0, hCu⟩ := Work.MB.etaOf_weak_bound hbdd u
  obtain ⟨Cv, hCv0, hCv⟩ := Work.MB.etaOf_weak_bound hbdd v
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hΘbdd : ∀ x : Xn (d + 2), ‖Θ x‖ ≤ max CΘ 0 := fun x => (hCΘ x).trans (le_max_left _ _)
  have hBmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hBfin : (volume : Measure Sp) (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ :=
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
  have hcont2 : Continuous (fun p : Sp × Sp => (Fin.cons p.2 (Fin.cons p.1 y) : Xn (d+2))) :=
    Continuous.finCons continuous_snd (Continuous.finCons continuous_fst continuous_const)
  -- joint integrability of the double integrand, over the product of the box with itself
  have hFint : Integrable (Function.uncurry (fun z w : Sp =>
      (starRingEnd ℂ) (etaOf e u z)
        * ((starRingEnd ℂ) (etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))))
      (volume.prod volume) := by
    refine Work.MB.integrable_of_bdd_of_support
      (S := Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
      (C := Cu * (Cv * max CΘ 0))
      (MeasurableSet.prod hBmeas hBmeas) ?_ ?_ ?_ ?_
    · rw [MeasureTheory.Measure.prod_prod]
      exact ENNReal.mul_ne_top hBfin hBfin
    · exact (((Complex.continuous_conj.measurable.comp (hu_meas.comp measurable_fst)).mul
        ((Complex.continuous_conj.measurable.comp (hv_meas.comp measurable_snd)).mul
          (hΘm.comp hcont2.measurable)))).aestronglyMeasurable
    · intro p
      have h1 : ‖(starRingEnd ℂ) (etaOf e u p.1)‖ ≤ Cu := by
        rw [RCLike.norm_conj]; exact hCu p.1
      have h2 : ‖(starRingEnd ℂ) (etaOf e v p.2)‖ ≤ Cv := by
        rw [RCLike.norm_conj]; exact hCv p.2
      have h3 : ‖Θ (Fin.cons p.2 (Fin.cons p.1 y))‖ ≤ max CΘ 0 := hΘbdd _
      calc ‖(starRingEnd ℂ) (etaOf e u p.1)
              * ((starRingEnd ℂ) (etaOf e v p.2) * Θ (Fin.cons p.2 (Fin.cons p.1 y)))‖
          = ‖(starRingEnd ℂ) (etaOf e u p.1)‖
              * ‖(starRingEnd ℂ) (etaOf e v p.2) * Θ (Fin.cons p.2 (Fin.cons p.1 y))‖ :=
            norm_mul _ _
        _ = ‖(starRingEnd ℂ) (etaOf e u p.1)‖
              * (‖(starRingEnd ℂ) (etaOf e v p.2)‖ * ‖Θ (Fin.cons p.2 (Fin.cons p.1 y))‖) := by
            rw [norm_mul]
        _ ≤ Cu * (Cv * max CΘ 0) :=
            mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) hCv0) (by positivity) hCu0
    · intro p hp
      simp only [Set.mem_prod, not_and_or] at hp
      rcases hp with hp1 | hp2
      · have hz : etaOf e u p.1 = 0 := Function.notMem_support.mp fun h => hp1 (hu_supp h)
        change (starRingEnd ℂ) (etaOf e u p.1)
          * ((starRingEnd ℂ) (etaOf e v p.2) * Θ (Fin.cons p.2 (Fin.cons p.1 y))) = 0
        rw [hz, map_zero, zero_mul]
      · have hz : etaOf e v p.2 = 0 := Function.notMem_support.mp fun h => hp2 (hv_supp h)
        change (starRingEnd ℂ) (etaOf e u p.1)
          * ((starRingEnd ℂ) (etaOf e v p.2) * Θ (Fin.cons p.2 (Fin.cons p.1 y))) = 0
        rw [hz, map_zero, zero_mul, mul_zero]
  -- the symmetry of `Θ` under the exchange of the first two particle slots
  have hswapΘ : ∀ z w : Sp, Θ (Fin.cons w (Fin.cons z y)) = Θ (Fin.cons z (Fin.cons w y)) := by
    intro z w
    have h := hΘsym (Equiv.swap (0 : Fin (d + 2)) 1) (Fin.cons z (Fin.cons w y))
    have hcons : (Fin.cons z (Fin.cons w y) : Xn (d + 2)) ∘ (Equiv.swap (0 : Fin (d + 2)) 1)
        = Fin.cons w (Fin.cons z y) := by
      simpa [Matrix.vecCons] using Matrix.cons_cons_comp_swap_zero_one z w y
    rw [hcons] at h
    exact h
  -- peel both sides
  rw [boxAnnOf_boxAnnOf_apply u v Θ y, boxAnnOf_boxAnnOf_apply v u Θ y]
  congr 1
  -- rewrite the right-hand integrand into the symmetric form `H w z`
  rw [show (∫ z : Sp, ∫ w : Sp, (starRingEnd ℂ) (etaOf e v z)
        * ((starRingEnd ℂ) (etaOf e u w) * Θ (Fin.cons w (Fin.cons z y))))
      = ∫ z : Sp, ∫ w : Sp, (starRingEnd ℂ) (etaOf e u w)
        * ((starRingEnd ℂ) (etaOf e v z) * Θ (Fin.cons z (Fin.cons w y))) from by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    dsimp only
    rw [hswapΘ w z]
    ring]
  -- Fubini, then the (definitional) renaming of the two integration variables
  exact (MeasureTheory.integral_integral_swap hFint).trans rfl

end Work.BoseBoxFock.PotCubicLowBandAux
