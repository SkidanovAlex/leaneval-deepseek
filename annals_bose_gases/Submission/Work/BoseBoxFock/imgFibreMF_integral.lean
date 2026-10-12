import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibreEnergyDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreMF_integral`

The first of the two measure-preserving-insertion identities recorded in
`Work.BoseBoxFock.imgFibreEnergyDefs`:

    ∫_{v ∈ boxL ℓ} imgFibreMF ℓ p F v = imgFibreN ℓ F .

Recall `imgFibreMF ℓ p F v = ∫_{x' ∈ boxPiSet (pairFib23 n p) ℓ} ∫_{s ∈ boxL ℓ} F (insertCoord2 p s v x')²`
and `imgFibreN ℓ F = ∫_{abox n ℓ} F²`.  The insertion `(x', s, v) ↦ insertCoord2 p s v x'` is the
measure-preserving bijection of the triple box onto the `n`-particle box (see
`Work.BoseBoxFock.splitEquiv` and `Work.BoseBoxFock.pairS23_integral_sq_eq_pinL2`); the content of
the present lemma is that the iterated integral defining `imgFibreMF` is exactly the integral
against the product measure on that triple box, with the integration over `v` moved inside relative
to the definition of `imgFibreMF`.

The proof is therefore

* `pairS23_integral_sq_eq_pinL2` (the `pairS23` box integral of `F (insertCoord2 p s v x')²` equals
  `pinL2 ℓ F = imgFibreN ℓ F`),
* two Fubini swaps (`MeasureTheory.integral_integral_swap`, hypotheses discharged by continuity on
  the compact boxes),
* two product/iterated conversions (`MeasureTheory.setIntegral_prod`),
* one measure-preserving change of variables (`MeasureTheory.MeasurePreserving.setIntegral_image_emb`
  along `Prod.swap`, whose measure preservation for the volumes is `Measure.prod_swap`).

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem imgFibreMF_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {F : Submission.BoseGases.X n → ℝ} (hF : Continuous F) :
    (∫ v in Work.BoseK15.corpusBox.boxL ℓ, Work.BoseBoxFock.imgFibreMF ℓ p F v)
      = Work.BoseBoxFock.imgFibreN ℓ F := by
  -- The base identity: the `pairS23` box integral of `F (insertCoord2 p s v x')²` is `imgFibreN`.
  have hbase : (∫ z in pairS23 ℓ p, (F (insertCoord2 p z.2.1 z.2.2 z.1)) ^ 2)
      = imgFibreN ℓ F := by
    have h := pairS23_integral_sq_eq_pinL2 (ℓ := ℓ) hℓ (p := p) hp
      (Θ₀ := fun x => ((F x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hF)
    have key : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
      intro r
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    calc (∫ z in pairS23 ℓ p, (F (insertCoord2 p z.2.1 z.2.2 z.1)) ^ 2)
        = ∫ z in pairS23 ℓ p,
            ‖((F (insertCoord2 p z.2.1 z.2.2 z.1) : ℝ) : ℂ)‖ ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact (key _).symm
      _ = pinL2 ℓ (fun x => ((F x : ℝ) : ℂ)) := h
      _ = imgFibreN ℓ F := by
          rw [pinL2, imgFibreN]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact key _
  unfold imgFibreMF
  set A : Set (pairFib23 n p → E3) := boxPiSet (pairFib23 n p) ℓ with hA
  set B : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hB
  have hAc : IsCompact A := by
    rw [hA]; exact isCompact_boxPiSet (ι := pairFib23 n p) hℓ
  have hBc : IsCompact B := by
    rw [hB]; exact Work.BoseB4.BoxData.boxL_compact _ ℓ
  have hins : Continuous (fun z : (pairFib23 n p → E3) × (E3 × E3) =>
      insertCoord2 p z.2.1 z.2.2 z.1) := continuous_insertCoord2_joint_pg23 p
  -- **Step A**: for fixed `v`, swap the two inner integrations (`x'` and `s`).
  have hA1 : (∫ v in B, ∫ x' in A, ∫ s in B, (F (insertCoord2 p s v x')) ^ 2)
      = ∫ v in B, ∫ s in B, ∫ x' in A, (F (insertCoord2 p s v x')) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    refine integral_integral_swap ?_
    have hct : Continuous (fun z : (pairFib23 n p → E3) × E3 =>
        (F (insertCoord2 p z.2 v z.1)) ^ 2) :=
      (hF.comp (hins.comp (continuous_fst.prodMk
        (continuous_snd.prodMk continuous_const)))).pow 2
    rw [Measure.prod_restrict]
    exact hct.continuousOn.integrableOn_compact (hAc.prod hBc)
  rw [hA1]
  -- **Step B**: swap the outer two integrations (`v` and `s`).
  have hB1 : (∫ v in B, ∫ s in B, ∫ x' in A, (F (insertCoord2 p s v x')) ^ 2)
      = ∫ s in B, ∫ v in B, ∫ x' in A, (F (insertCoord2 p s v x')) ^ 2 := by
    refine integral_integral_swap ?_
    have hct : Continuous (fun q : E3 × E3 => ∫ x' in A, (F (insertCoord2 p q.2 q.1 x')) ^ 2) := by
      have huc : Continuous (Function.uncurry (fun q : E3 × E3 =>
          fun x' : (pairFib23 n p → E3) => (F (insertCoord2 p q.2 q.1 x')) ^ 2)) := by
        show Continuous (fun z : (E3 × E3) × (pairFib23 n p → E3) =>
          (F (insertCoord2 p z.1.2 z.1.1 z.2)) ^ 2)
        exact (hF.comp (hins.comp (continuous_snd.prodMk
          ((continuous_snd.comp continuous_fst).prodMk
            (continuous_fst.comp continuous_fst))))).pow 2
      exact continuous_parametric_integral_of_continuous huc hAc
    rw [Measure.prod_restrict]
    exact hct.continuousOn.integrableOn_compact (hBc.prod hBc)
  rw [hB1]
  -- **Step C1**: combine the two `B`-integrations into one over `B ×ˢ B`.
  have hC1 : (∫ s in B, ∫ v in B, ∫ x' in A, (F (insertCoord2 p s v x')) ^ 2)
      = ∫ w in B ×ˢ B, ∫ x' in A, (F (insertCoord2 p w.1 w.2 x')) ^ 2 := by
    refine (setIntegral_prod (fun w : E3 × E3 =>
        ∫ x' in A, (F (insertCoord2 p w.1 w.2 x')) ^ 2) ?_).symm
    have hct : Continuous (fun w : E3 × E3 =>
        ∫ x' in A, (F (insertCoord2 p w.1 w.2 x')) ^ 2) := by
      have huc : Continuous (Function.uncurry (fun w : E3 × E3 =>
          fun x' : (pairFib23 n p → E3) => (F (insertCoord2 p w.1 w.2 x')) ^ 2)) := by
        show Continuous (fun z : (E3 × E3) × (pairFib23 n p → E3) =>
          (F (insertCoord2 p z.1.1 z.1.2 z.2)) ^ 2)
        exact (hF.comp (hins.comp (continuous_snd.prodMk
          ((continuous_fst.comp continuous_fst).prodMk
            (continuous_snd.comp continuous_fst))))).pow 2
      exact continuous_parametric_integral_of_continuous huc hAc
    exact hct.continuousOn.integrableOn_compact (hBc.prod hBc)
  rw [hC1]
  -- **Step C2**: combine the `(B ×ˢ B)`-integration with the `A`-integration.
  have hC2 : (∫ w in B ×ˢ B, ∫ x' in A, (F (insertCoord2 p w.1 w.2 x')) ^ 2)
      = ∫ q in (B ×ˢ B) ×ˢ A, (F (insertCoord2 p q.1.1 q.1.2 q.2)) ^ 2 := by
    refine (setIntegral_prod (fun q : (E3 × E3) × (pairFib23 n p → E3) =>
        (F (insertCoord2 p q.1.1 q.1.2 q.2)) ^ 2) ?_).symm
    have hct : Continuous (fun q : (E3 × E3) × (pairFib23 n p → E3) =>
        (F (insertCoord2 p q.1.1 q.1.2 q.2)) ^ 2) :=
      (hF.comp (hins.comp (continuous_snd.prodMk
        ((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.comp continuous_fst))))).pow 2
    exact hct.continuousOn.integrableOn_compact ((hBc.prod hBc).prod hAc)
  rw [hC2]
  -- **Step D**: permute the two factors of the product box (`Prod.swap`).
  have hD : (∫ q in (B ×ˢ B) ×ˢ A, (F (insertCoord2 p q.1.1 q.1.2 q.2)) ^ 2)
      = ∫ z in pairS23 ℓ p, (F (insertCoord2 p z.2.1 z.2.2 z.1)) ^ 2 := by
    have hpmp : MeasurePreserving (Prod.swap : (E3 × E3) × (pairFib23 n p → E3) →
        (pairFib23 n p → E3) × (E3 × E3)) volume volume :=
      ⟨measurable_swap, Measure.prod_swap⟩
    have himg := hpmp.setIntegral_image_emb (MeasurableEquiv.measurableEmbedding
        (MeasurableEquiv.prodComm : (E3 × E3) × (pairFib23 n p → E3) ≃ᵐ
          (pairFib23 n p → E3) × (E3 × E3)))
        (fun z : (pairFib23 n p → E3) × (E3 × E3) =>
          (F (insertCoord2 p z.2.1 z.2.2 z.1)) ^ 2)
        (((B ×ˢ B) ×ˢ A))
    rw [Set.image_swap_prod] at himg
    have h1 : (∫ q in (B ×ˢ B) ×ˢ A, (F (insertCoord2 p q.1.1 q.1.2 q.2)) ^ 2)
        = ∫ x in (B ×ˢ B) ×ˢ A,
            (F (insertCoord2 p x.swap.2.1 x.swap.2.2 x.swap.1)) ^ 2 := rfl
    rw [h1]
    exact himg.symm
  rw [hD]
  exact hbase

end Work.BoseBoxFock
