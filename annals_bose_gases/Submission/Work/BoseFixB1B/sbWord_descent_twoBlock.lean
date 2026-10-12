import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.sbWordSliceSuperaddHolds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-!
# `Work.BoseFixB1B.sbWord_descent_twoBlock` — the two-block descent for `sbWord`

`sbWord_slice_superadd_regime_holds` (FS Step E, the *grouping* step at the sliding box)
says that the `(N₁+N₂)`-particle word dominates the sum of the two block-slice integrals:

    sbWord h μ u Φ ≥ ∫_w sbWord h μ u (slice_w Φ) + ∫_u sbWord h μ u (slice'_u Φ) .

Given that each `N`-particle slice carries at least `g₁·∫(slice)²` (resp. `g₂·∫(slice)²`) — the
hypotheses `hB1`/`hB2`, which are quantified over *all* particle numbers — the two slice
integrals can be bounded below by `g₁` and `g₂` times the corresponding slice masses.  Fubini
(`aboxFubini_slice` / `aboxFubini_slice_swapped`) identifies each of those with the full mass:

    (g₁ + g₂)·∫Φ² ≤ ∫_w sbWord(slice_w) + ∫_u sbWord(slice'_u) ≤ sbWord Φ .

The `dlBox`-localisation hypothesis `hin` splits into the two per-block localisation hypotheses
along the measure-preserving block decomposition of the box: `volume.restrict (abox (N₁+N₂) ℓ)`
is the image of the product of the two restricted block volumes under `blockSplitEquiv`, so its
a.e. statements pull back to a.e. statements on the product, and a.e. on a product gives a.e.
sections in either order.

## Helpers

* `blockSplitEquiv_symm_eq_mergeBlock` — the inverse of the block-split equivalence is `mergeBlock`.
* `mergeBlock_apply_castAdd` / `mergeBlock_apply_natAdd` — the coordinates of a merged
  configuration are the coordinates of the two blocks.
* `ae_prod_abox_of_ae_abox` — an a.e. statement on the big box transfers to the product of the
  block boxes.
* `ae_sections_prod` — a.e. on a product implies a.e. sections in either order.
* `integrable_prod_merge_of_integrableOn_abox` — integrability on the big box transfers to the
  composition with `mergeBlock` on the product of the block boxes.
-/

/-- The inverse of the block-split equivalence is `mergeBlock`. -/
lemma blockSplitEquiv_symm_eq_mergeBlock {N1 N2 : ℕ}
    (p : Submission.BoseGases.X N1 × Submission.BoseGases.X N2) :
    (Submission.BoseGases.blockSplitEquiv N1 N2).symm p
      = Submission.BoseGases.mergeBlock N1 N2 p := by
  obtain ⟨y, w⟩ := p
  have h : (Submission.BoseGases.blockSplitEquiv N1 N2)
      (Submission.BoseGases.mergeBlock N1 N2 (y, w)) = (y, w) := by
    simp [Submission.BoseGases.blockSplitEquiv_apply, Submission.BoseGases.mergeBlock_first,
      Submission.BoseGases.mergeBlock_last]
  calc (Submission.BoseGases.blockSplitEquiv N1 N2).symm (y, w)
      = (Submission.BoseGases.blockSplitEquiv N1 N2).symm
          ((Submission.BoseGases.blockSplitEquiv N1 N2)
            (Submission.BoseGases.mergeBlock N1 N2 (y, w))) := by rw [h]
    _ = Submission.BoseGases.mergeBlock N1 N2 (y, w) := Equiv.symm_apply_apply _ _

/-- A coordinate of the first block of a merged configuration is the corresponding coordinate
of the first block. -/
lemma mergeBlock_apply_castAdd {N1 N2 : ℕ}
    (p : Submission.BoseGases.X N1 × Submission.BoseGases.X N2) (j : Fin N1) :
    Submission.BoseGases.mergeBlock N1 N2 p (Fin.castAdd N2 j) = p.1 j := by
  obtain ⟨y, w⟩ := p
  simp [Submission.BoseGases.mergeBlock]

/-- A coordinate of the second block of a merged configuration is the corresponding coordinate
of the second block. -/
lemma mergeBlock_apply_natAdd {N1 N2 : ℕ}
    (p : Submission.BoseGases.X N1 × Submission.BoseGases.X N2) (j : Fin N2) :
    Submission.BoseGases.mergeBlock N1 N2 p (Fin.natAdd N1 j) = p.2 j := by
  obtain ⟨y, w⟩ := p
  simp [Submission.BoseGases.mergeBlock]

/-- An a.e. statement on the full centred box transfers to the product of the block boxes,
composed with `mergeBlock`. -/
lemma ae_prod_abox_of_ae_abox {N1 N2 : ℕ} {ℓ : ℝ}
    {P : Submission.BoseGases.X (N1 + N2) → Prop}
    (hP : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (N1 + N2) ℓ)), P x) :
    ∀ᵐ p ∂((volume.restrict (Submission.BoseGases.abox N1 ℓ)).prod
        (volume.restrict (Submission.BoseGases.abox N2 ℓ))),
      P (Submission.BoseGases.mergeBlock N1 N2 p) := by
  have hmp := (Submission.BoseGases.aboxSplit_measurePreserving_restrict N1 N2 ℓ).symm
  have h' := hmp.quasiMeasurePreserving.ae hP
  filter_upwards [h'] with p hp
  simpa only [blockSplitEquiv_symm_eq_mergeBlock p] using hp

/-- An a.e. statement on the product of the two block boxes yields a.e. statements on the
sections, in both orders. -/
lemma ae_sections_prod {N1 N2 : ℕ} {ℓ : ℝ}
    {P : Submission.BoseGases.X (N1 + N2) → Prop}
    (hP : ∀ᵐ p ∂((volume.restrict (Submission.BoseGases.abox N1 ℓ)).prod
        (volume.restrict (Submission.BoseGases.abox N2 ℓ))),
      P (Submission.BoseGases.mergeBlock N1 N2 p)) :
    (∀ᵐ w ∂(volume.restrict (Submission.BoseGases.abox N2 ℓ)),
        ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.abox N1 ℓ)),
          P (Submission.BoseGases.mergeBlock N1 N2 (y, w)))
    ∧ (∀ᵐ y ∂(volume.restrict (Submission.BoseGases.abox N1 ℓ)),
        ∀ᵐ w ∂(volume.restrict (Submission.BoseGases.abox N2 ℓ)),
          P (Submission.BoseGases.mergeBlock N1 N2 (y, w))) := by
  set μ1 : MeasureTheory.Measure (Submission.BoseGases.X N1) :=
    volume.restrict (Submission.BoseGases.abox N1 ℓ) with hμ1
  set μ2 : MeasureTheory.Measure (Submission.BoseGases.X N2) :=
    volume.restrict (Submission.BoseGases.abox N2 ℓ) with hμ2
  have hfirst : ∀ᵐ y ∂μ1, ∀ᵐ w ∂μ2,
      P (Submission.BoseGases.mergeBlock N1 N2 (y, w)) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod (μ := μ1) (ν := μ2) hP
  have hsecond : ∀ᵐ w ∂μ2, ∀ᵐ y ∂μ1,
      P (Submission.BoseGases.mergeBlock N1 N2 (y, w)) := by
    have hswap := (MeasureTheory.Measure.measurePreserving_swap (μ := μ2) (ν := μ1)
      ).quasiMeasurePreserving.ae hP
    refine MeasureTheory.Measure.ae_ae_of_ae_prod (μ := μ2) (ν := μ1)
      (p := fun z : Submission.BoseGases.X N2 × Submission.BoseGases.X N1 =>
        P (Submission.BoseGases.mergeBlock N1 N2 (z.2, z.1))) ?_
    filter_upwards [hswap] with q hq
    simpa [Prod.swap] using hq
  exact ⟨hsecond, hfirst⟩

/-- Integrability on the full centred box transfers to the composition with `mergeBlock` on the
product of the two block boxes. -/
lemma integrable_prod_merge_of_integrableOn_abox {N1 N2 : ℕ} {ℓ : ℝ}
    {G : Submission.BoseGases.X (N1 + N2) → ℝ}
    (hG : IntegrableOn G (Submission.BoseGases.abox (N1 + N2) ℓ) volume) :
    Integrable (fun p : Submission.BoseGases.X N1 × Submission.BoseGases.X N2 =>
        G (Submission.BoseGases.mergeBlock N1 N2 p))
      ((volume.restrict (Submission.BoseGases.abox N1 ℓ)).prod
        (volume.restrict (Submission.BoseGases.abox N2 ℓ))) := by
  have hmp := Submission.BoseGases.aboxSplit_measurePreserving_restrict N1 N2 ℓ
  have hif := (hmp.integrable_comp_emb
    (Submission.BoseGases.blockSplitEquiv N1 N2).measurableEmbedding
    (g := fun p : Submission.BoseGases.X N1 × Submission.BoseGases.X N2 =>
        G (Submission.BoseGases.mergeBlock N1 N2 p)))
  apply hif.1
  change Integrable (fun x : Submission.BoseGases.X (N1 + N2) =>
      G (Submission.BoseGases.mergeBlock N1 N2 (Submission.BoseGases.blockSplitEquiv N1 N2 x)))
    (volume.restrict (Submission.BoseGases.abox (N1 + N2) ℓ))
  have hpt : (fun x : Submission.BoseGases.X (N1 + N2) =>
      G (Submission.BoseGases.mergeBlock N1 N2 (Submission.BoseGases.blockSplitEquiv N1 N2 x)))
      = G := by
    funext x
    rw [Submission.BoseGases.blockSplitEquiv_apply]
    exact congrArg G (Submission.BoseGases.mergeBlock_eq N1 N2 x)
  rw [hpt]
  exact hG

theorem sbWord_descent_twoBlock {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N1 N2 : ℕ} (g1 g2 : ℝ)
    (hB1 : ∀ {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      g1 * (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1.sbWord h μ u Ψ)
    (hB2 : ∀ {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      g2 * (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1.sbWord h μ u Ψ)
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hin : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox (N1 + N2) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      Φ x ≠ 0 → ∀ i : Fin (N1 + N2), x i ∈ Submission.BoseGases.dlBox
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    (g1 + g2) * (∫ x in Submission.BoseGases.abox (N1 + N2)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
      ≤ Work.BoseFixB1.sbWord h μ u Φ := by
  -- abbreviations: `let` bindings are definitionally transparent, so every lemma below applies
  -- with the literal expressions of the statement.
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
  let V : Set E3 := Submission.BoseGases.dlBox ℓ d u
  have hℓpos : 0 < ℓ := Work.BoseFixB1.adm_ell_pos hAdm
  have hΦc : Continuous Φ := hΦ.continuous
  -- integrability of `Φ²` on the full box (the box is compact and `Φ` is continuous)
  have hGint : IntegrableOn (fun x : Submission.BoseGases.X (N1 + N2) => (Φ x) ^ 2)
      (Submission.BoseGases.abox (N1 + N2) ℓ) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓpos (hΦc.pow 2)
  -- the a.e. localisation statements on the sections, from `hin` via the block split
  have hprodP : ∀ᵐ p ∂((volume.restrict (Submission.BoseGases.abox N1 ℓ)).prod
        (volume.restrict (Submission.BoseGases.abox N2 ℓ))),
      Φ (Submission.BoseGases.mergeBlock N1 N2 p) ≠ 0 →
        ∀ i : Fin (N1 + N2), Submission.BoseGases.mergeBlock N1 N2 p i ∈ V :=
    ae_prod_abox_of_ae_abox (N1 := N1) (N2 := N2) (ℓ := ℓ) hin
  have hsec := ae_sections_prod (N1 := N1) (N2 := N2) (ℓ := ℓ)
    (P := fun x : Submission.BoseGases.X (N1 + N2) =>
      Φ x ≠ 0 → ∀ i : Fin (N1 + N2), x i ∈ V) hprodP
  have hcont1 : ∀ᵐ w ∂(volume.restrict (Submission.BoseGases.abox N2 ℓ)),
      ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.abox N1 ℓ)),
        Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)) ≠ 0 →
          ∀ j : Fin N1, y j ∈ V :=
    hsec.1.mono fun w hw => hw.mono fun y hy => fun hne j => by
      have h1 := hy hne (Fin.castAdd N2 j)
      rwa [mergeBlock_apply_castAdd (y, w) j] at h1
  have hcont2 : ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.abox N1 ℓ)),
      ∀ᵐ w ∂(volume.restrict (Submission.BoseGases.abox N2 ℓ)),
        Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)) ≠ 0 →
          ∀ j : Fin N2, w j ∈ V :=
    hsec.2.mono fun y hy => hy.mono fun w hw => fun hne j => by
      have h1 := hw hne (Fin.natAdd N1 j)
      rwa [mergeBlock_apply_natAdd (y, w) j] at h1
  -- the two a.e. slice bounds, from `hB1`/`hB2`
  have hae1 : ∀ᵐ w ∂(volume.restrict (Submission.BoseGases.abox N2 ℓ)),
      g1 * (∫ y in Submission.BoseGases.abox N1 ℓ,
          (Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) ^ 2)
        ≤ Work.BoseFixB1.sbWord h μ u
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) := by
    filter_upwards [hcont1] with w hw
    exact hB1 (N := N1) (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))
      (Work.KinPSuperadd.slice_contDiff_infty_fst hΦ w) hw
  have hae2 : ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.abox N1 ℓ)),
      g2 * (∫ w in Submission.BoseGases.abox N2 ℓ,
          (Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) ^ 2)
        ≤ Work.BoseFixB1.sbWord h μ u
            (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) := by
    filter_upwards [hcont2] with y hy
    exact hB2 (N := N2) (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))
      (Work.KinPSuperadd.slice_contDiff_infty_snd hΦ y) hy
  -- integrability of the two mass slices, from the product integrability of `Φ²`
  have hprodG := integrable_prod_merge_of_integrableOn_abox (N1 := N1) (N2 := N2) (ℓ := ℓ)
    (G := fun x : Submission.BoseGases.X (N1 + N2) => (Φ x) ^ 2) hGint
  have hmass1 : IntegrableOn (fun w : Submission.BoseGases.X N2 =>
      ∫ y in Submission.BoseGases.abox N1 ℓ,
        (Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) ^ 2)
      (Submission.BoseGases.abox N2 ℓ) volume := hprodG.integral_prod_right
  have hmass2 : IntegrableOn (fun y : Submission.BoseGases.X N1 =>
      ∫ w in Submission.BoseGases.abox N2 ℓ,
        (Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) ^ 2)
      (Submission.BoseGases.abox N1 ℓ) volume := hprodG.integral_prod_left
  -- integrability of the two slice words, from the word-level grouping
  have hS1 : IntegrableOn (fun w : Submission.BoseGases.X N2 =>
      Work.BoseFixB1.sbWord h μ u
        (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))))
      (Submission.BoseGases.abox N2 ℓ) volume := by
    have hkin := (Work.BoseFixB1B.sbKin_slice_slotSplit (v := v) h hv hv1 hvrad hR hv_supp
      hav hAdm u).int₁ (N1 := N1) (N2 := N2) Φ hΦ
    have hpot := (Work.BoseFixB1S.sbPot_slice_integrable_regime (v := v) h hv hv1 hvrad hR
      hv_supp hav hAdm hR16 hRχ u (N₁ := N1) (N₂ := N2) hΦ).1
    exact hkin.add hpot
  have hS2 : IntegrableOn (fun y : Submission.BoseGases.X N1 =>
      Work.BoseFixB1.sbWord h μ u
        (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))))
      (Submission.BoseGases.abox N1 ℓ) volume := by
    have hkin := (Work.BoseFixB1B.sbKin_slice_slotSplit (v := v) h hv hv1 hvrad hR hv_supp
      hav hAdm u).int₂ (N1 := N1) (N2 := N2) Φ hΦ
    have hpot := (Work.BoseFixB1S.sbPot_slice_integrable_regime (v := v) h hv hv1 hvrad hR
      hv_supp hav hAdm hR16 hRχ u (N₁ := N1) (N₂ := N2) hΦ).2
    exact hkin.add hpot
  -- integrate the two a.e. bounds
  have hA : g1 * (∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, (Φ x) ^ 2)
      ≤ ∫ w in Submission.BoseGases.abox N2 ℓ,
          Work.BoseFixB1.sbWord h μ u
            (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) := by
    have hI1 : IntegrableOn (fun w : Submission.BoseGases.X N2 =>
        g1 * (∫ y in Submission.BoseGases.abox N1 ℓ,
          (Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) ^ 2))
        (Submission.BoseGases.abox N2 ℓ) volume := hmass1.const_mul g1
    have hmono := integral_mono_ae (μ := volume.restrict (Submission.BoseGases.abox N2 ℓ))
      hI1 hS1 hae1
    calc g1 * (∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, (Φ x) ^ 2)
        = ∫ w in Submission.BoseGases.abox N2 ℓ,
            g1 * (∫ y in Submission.BoseGases.abox N1 ℓ,
              (Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) ^ 2) := by
          rw [integral_const_mul,
            aboxFubini_slice_swapped (N1 := N1) (N2 := N2) ℓ
              (fun x : Submission.BoseGases.X (N1 + N2) => (Φ x) ^ 2) hGint]
      _ ≤ ∫ w in Submission.BoseGases.abox N2 ℓ,
            Work.BoseFixB1.sbWord h μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) := hmono
  have hB : g2 * (∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, (Φ x) ^ 2)
      ≤ ∫ y in Submission.BoseGases.abox N1 ℓ,
          Work.BoseFixB1.sbWord h μ u
            (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) := by
    have hI2 : IntegrableOn (fun y : Submission.BoseGases.X N1 =>
        g2 * (∫ w in Submission.BoseGases.abox N2 ℓ,
          (Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) ^ 2))
        (Submission.BoseGases.abox N1 ℓ) volume := hmass2.const_mul g2
    have hmono := integral_mono_ae (μ := volume.restrict (Submission.BoseGases.abox N1 ℓ))
      hI2 hS2 hae2
    calc g2 * (∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, (Φ x) ^ 2)
        = ∫ y in Submission.BoseGases.abox N1 ℓ,
            g2 * (∫ w in Submission.BoseGases.abox N2 ℓ,
              (Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) ^ 2) := by
          rw [integral_const_mul,
            aboxFubini_slice (N1 := N1) (N2 := N2) ℓ
              (fun x : Submission.BoseGases.X (N1 + N2) => (Φ x) ^ 2) hGint]
      _ ≤ ∫ y in Submission.BoseGases.abox N1 ℓ,
            Work.BoseFixB1.sbWord h μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))) := hmono
  -- the word-level grouping (FS Step E) at the sliding box
  have hsuper := sbWord_slice_superadd_regime_holds (v := v) h hv hv1 hvrad hR hv_supp hav
    hAdm hR16 hRχ u (N₁ := N1) (N₂ := N2) (Φ := Φ) hΦ
  have hsplit : (g1 + g2) * (∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, (Φ x) ^ 2)
      = g1 * (∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, (Φ x) ^ 2)
        + g2 * (∫ x in Submission.BoseGases.abox (N1 + N2) ℓ, (Φ x) ^ 2) := by ring
  rw [hsplit]
  linarith [hA, hB, hsuper]

end

end Work.BoseFixB1B
