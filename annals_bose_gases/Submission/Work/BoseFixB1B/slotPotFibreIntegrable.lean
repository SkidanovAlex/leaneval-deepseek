import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.slotPotFibreIntegrable` — the Tonelli step of the fibre factorisation

**(R3) of the potential half of `Work.PerBoxSectorBound`.**  The potential fibre factorisation
(`Work.SlotWord.qLHSword_slotFibre`, FS `eq:potsplit` at the fibre) reads

  `qLHSword_N (slotPiece B S Φ) = ∫_y qLHSword_{|S|} (pieceFibre B S e Φ y)`,

and the Bochner convention `∫ = 0` makes the right-hand side usable only once the fibre word is
*integrable* in `y`.  This theorem supplies exactly that, from the ambient integrability
hypothesis `hgi` (the box integrability of the `slotPiece`-weighted `qLHSden` density, which is the
`x`-integrand of the left-hand side).

## Proof route (Tonelli/Fubini through the slot reassembly, no a.e. measurability of the kernels)

* `hgi` is `IntegrableOn F (abox n ℓ)` for the ambient density `F`.
* `slotTheta S e : X |S| × (SlotOut → ℝ³) ≃ᵐ X n` is measure preserving
  (`slotTheta_measurePreserving`) and pulls `abox n ℓ` back to
  `abox |S| ℓ × slotBox (acube ℓ)` (`slotTheta_preimage_abox`); hence
  `IntegrableOn (F ∘ slotTheta) (abox |S| ℓ × slotOutside ℓ B S)` (`MeasurePreserving.
  integrableOn_comp_preimage` + `IntegrableOn.mono_set`), i.e. `F ∘ slotTheta` is integrable for
  the product of the restricted measures (`Measure.prod_restrict`, `Measure.volume_eq_prod`).
* `Integrable.integral_prod_right` (Fubini) then gives the `y`-integrability of the section
  integral `y ↦ ∫_{z ∈ abox |S| ℓ} F (slotTheta (z, y))`.
* The pointwise identification of the section with the fibre word is `qLHSden_slotComb`: on
  `y ∈ slotOutside` every outside coordinate lies outside the sliding box, so the support
  hypotheses `wSmallPair_support_left`/`wSmall1Pair_support_left` (from the support of
  `chiSmallB`, `chiSmallB_support_mem_dlBox`, at `M = PBM v μ ≥ 1`) kill the chemical and pair
  terms carried by the outside coordinates, leaving exactly
  `qLHSword (N := |S|) ℓ μ w w1 (pieceFibre B S e Φ y)`.
* `Integrable.congr` with the a.e. (indeed, everywhere on `slotOutside`) equality finishes.

Note the proof never needs a.e. strong measurability of the kernels: Fubini's theorem is applied
to an *integrable* function, so the `MemLp v 1`/`IsRadial v`/support hypotheses of the statement
are not consumed (they are kept for the caller's use downstream).
-/

namespace Work.BoseFixB1B

theorem slotPotFibreIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ c C : ℝ} (hε₀ : 0 < ε₀) {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ))
    (S : Finset (Fin n)) (e : Work.PerSector.SlotIn n S ≃ Fin S.card)
    (hgi : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S
            (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
          * Submission.BoseGases.qLHSden n (Work.BoseFixB1B.PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u) x)
      (Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ))) :
    MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.qLHSword (N := S.card) (Work.BoseFixB1B.PBℓ v μ) μ
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u)
          (Work.SlotWord.pieceFibre (Work.BoseFixB1B.PBB v μ u) S e
            (Φ : Submission.BoseGases.X n → ℝ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) S)) := by
  classical
  -- ## 0. The frozen parameters: positivity and the regularity `M ≥ 1`
  obtain ⟨hμpos, _hdil, _hp⟩ := hμ
  have hM : 1 ≤ PBM v μ := by
    simp only [PBM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    norm_num
  have hL : 0 < PBℓ v μ := Work.BoseBox.sideAt_pos hμpos hav
  have hd : 0 < PBd v μ := by
    simp only [PBd, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Real.rpow_pos_of_pos (mul_pos hμpos (pow_pos hav 3)) _
  -- ## 1. The support hypotheses of the two localised kernels
  have hsupp1 : ∀ x : EuclideanSpace ℝ (Fin 3), x ∉ PBB v μ u →
      ∀ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u x y = 0 :=
    fun x hx y => Work.SlotWord.wSmall1Pair_support_left hM hL hd u hx y
  have hsupp2 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ PBB v μ u ∨ y ∉ PBB v μ u) →
        Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v x y = 0 := by
    intro x y hxy
    rcases hxy with hx | hy
    · exact Work.SlotWord.wSmallPair_support_left hM hL hd u v hx y
    · have hy0 : Submission.BoseGases.chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u y = 0 := by
        by_contra hne
        exact hy (Work.SlotWord.chiSmallB_support_mem_dlBox hM hL hd hne)
      simp only [Submission.BoseGases.wSmallPair, hy0, mul_zero]
  -- ## 2. Abbreviations
  let Ψ : Submission.BoseGases.X n → ℝ := (Φ : Submission.BoseGases.X n → ℝ)
  let w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
    Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v
  let w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
    Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u
  let F : Submission.BoseGases.X n → ℝ := fun x =>
    (Work.PerSector.slotPiece (PBB v μ u) S Ψ x) ^ 2
      * Submission.BoseGases.qLHSden n (PBℓ v μ) μ w w1 x
  let U : Set (Submission.BoseGases.X S.card ×
      (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))) :=
    Submission.BoseGases.abox S.card (PBℓ v μ) ×ˢ
      Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S
  -- ## 3. The ambient integrand is `F`, by hypothesis
  have hgiF : MeasureTheory.IntegrableOn F (Submission.BoseGases.abox n (PBℓ v μ)) := hgi
  -- ## 4. Push the integrability through the slot reassembly `slotTheta`
  have hmp : MeasureTheory.MeasurePreserving (Work.SlotWord.slotTheta S e)
      (MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X S.card × (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    Work.SlotWord.slotTheta_measurePreserving S e
  have hInt : MeasureTheory.IntegrableOn
      (fun p : Submission.BoseGases.X S.card ×
          (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3)) =>
        F (Work.SlotWord.slotTheta S e p))
      ((Work.SlotWord.slotTheta S e) ⁻¹' Submission.BoseGases.abox n (PBℓ v μ)) :=
    (hmp.integrableOn_comp_preimage (Work.SlotWord.slotTheta S e).measurableEmbedding
      (f := F) (s := Submission.BoseGases.abox n (PBℓ v μ))).mpr hgiF
  rw [Work.SlotWord.slotTheta_preimage_abox S e (PBℓ v μ)] at hInt
  -- ## 5. Restrict to the outside configurations
  have hUsub : U ⊆ Submission.BoseGases.abox S.card (PBℓ v μ) ×ˢ
      Work.PerSector.slotBox (Submission.BoseGases.acube (PBℓ v μ)) := by
    intro p hp
    have hp' : p.1 ∈ Submission.BoseGases.abox S.card (PBℓ v μ) ∧
        p.2 ∈ Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S := by
      simpa only [U, Set.mem_prod] using hp
    refine Set.mem_prod.mpr ⟨hp'.1, fun j => ?_⟩
    exact (Work.PerSector.mem_slotOutside_iff.mp hp'.2).1 j
  have hIntU : MeasureTheory.IntegrableOn
      (fun p : Submission.BoseGases.X S.card ×
          (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3)) =>
        F (Work.SlotWord.slotTheta S e p)) U := hInt.mono_set hUsub
  -- ## 6. Fubini: the section integral is integrable on the outside configurations
  have hf : MeasureTheory.Integrable
      (fun p : Submission.BoseGases.X S.card ×
          (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3)) =>
        F (Work.SlotWord.slotTheta S e p))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).restrict
          (Submission.BoseGases.abox S.card (PBℓ v μ)) |>.prod
        ((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S))) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod
      (Submission.BoseGases.X S.card)
      (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))]
    exact hIntU
  have hf' : MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
        ∫ z, F (Work.SlotWord.slotTheta S e (z, y))
          ∂((MeasureTheory.volume : MeasureTheory.Measure
            (Submission.BoseGases.X S.card)).restrict
            (Submission.BoseGases.abox S.card (PBℓ v μ))))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside (PBℓ v μ) (PBB v μ u) S)) :=
    hf.integral_prod_right
  -- ## 7. Identify the section integral with the fibre potential word
  refine hf'.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem (Work.SlotWord.measurableSet_slotOutside (PBℓ v μ)
    (Work.SmallBoxSliding.measurableSet_dlBox (PBℓ v μ) (PBd v μ) u) S) ?_
  intro y hy
  have hyB : ∀ j : Work.PerSector.SlotOut n S, y j ∉ PBB v μ u :=
    (Work.PerSector.mem_slotOutside_iff.mp hy).2
  have hgy : ∀ p : Submission.BoseGases.X S.card ×
        (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3)),
      (∀ j : Work.PerSector.SlotOut n S, p.2 j ∉ PBB v μ u) →
      F (Work.SlotWord.slotTheta S e p) =
        (Work.SlotWord.pieceFibre (PBB v μ u) S e Ψ p.2 p.1) ^ 2
          * Submission.BoseGases.qLHSden S.card (PBℓ v μ) μ w w1 p.1 := by
    intro p hp2
    dsimp only [F, Ψ]
    rw [Work.SlotWord.slotTheta_apply, ← Work.SlotWord.pieceFibre_apply,
      Work.SlotWord.qLHSden_slotComb (PBℓ v μ) (PBd v μ) μ u S e w w1 hsupp1 hsupp2 p.1 p.2 hp2]
  simp only [Submission.BoseGases.qLHSword_eq_integral_qLHSden]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  exact hgy (z, y) hyB

end Work.BoseFixB1B
