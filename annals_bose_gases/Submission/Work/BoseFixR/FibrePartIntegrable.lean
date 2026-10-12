import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.q3kinMomFormLeGapBare
import Submission.Work.BoseBox.q3kinNeuFracLeGapBare
import Submission.Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge
import Submission.Work.BoseFixB2.Pot.potWordU_integrable
import Submission.Work.BoseFixR.BsOneBodyBoxBound
import Submission.Work.BoseFixR.FibreTelescope
import Submission.Work.BoseFixR.NeuFracFibreMeas
import Submission.Work.BoseFixR.WindowedFTMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.FibrePartIntegrable` — the four fibre marginals of the box word

The target asks that for a small enough diluteness threshold `ε₀ > 0` and every admissible `μ`,
the four *piece* marginals of the box word

* `y ↦ kinFormB k ℓ … (bfL Φ y)` and `z ↦ kinFormB j ℓ … (bfR Φ z)` (the kinetic halves),
* `y ↦ ∫ z in abox k ℓ, (bfL Φ y z)² · potWordU k ⋯ z` and its right-block mirror (the
  potential halves),

be honest Bochner integrals over the block boxes, `ℓ = sideAt μ (a v)`.

## The decomposition (and the one missing hypothesis)

The kinetic halves are *theorems* for every smooth `Φ` and every box side `ℓ > 0` — no
hypothesis on `v` at all — because the anchored slot integrand is already integrable on the box
for smooth states (`integrableOn_fsT_fibre`); the whole argument is the block change of
variables followed by Fubini (`kinFibreMarginal_general` below, needing only `0 < ℓ`; the
`Adm`-bookkeeping and the fact that `0 < sideAt μ (a v)` then give the target's kinetic
conjuncts, see `kinFibreMarginal_of_adm`).

The potential halves are different: the box-restricted potential word
`potWordU N v (g₀ v h) ℓ μ 0` has the *bare potential `v`* as its two-body kernel numerator
(`wLoc ℓ v 0 a b = χ(a)·v(a−b)/(χ⋆χ)((a−b)/ℓ)·χ(b)`), so both its measurability and its
`L¹`-ness on the box require a hypothesis on `v` that `ScatSol v = ∃ w, IsRadial w ∧
IsScatteringSolution w v` does **not** provide:

* `IsScatteringSolution` gives only `LocallyIntegrable w` and `LocallyIntegrable (v(1−w))`
  (`ChallengeDeps.lean`), so `v` itself need be neither `L¹_loc` nor a.e. strongly measurable
  on `{w = 1}`; the corpus's own suppliers of the two facts needed here carry exactly the
  missing hypothesis — `Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU` needs
  `AEStronglyMeasurable v`, and `Work.BoseFixB2.Pot.potWordU_integrable` (resp. the delegated
  `Work.BoseFixR.PotWordUIntegrableLoc`) needs `MemLp v 1` (resp. `LocallyIntegrable v` and
  `LocallyIntegrable (g₀ v h)`).
* The pointwise bound of `Work.BoseFixGlue.Pot.abs_potWordU_le`, which is all the dilute
  régime gives, is
  `|potWordU N v g ℓ μ u x| ≤ |μ|N(2χ²∫|g|) + χ²·Σ_{i<j} 2|v(x_i − x_j)|`,
  whose right-hand side is *not* uniformly bounded; integrating it over the box is finite
  exactly when `v ∈ L¹` near `0`, i.e. under the missing hypothesis.

Accordingly the potential halves are proved here under the standard standing hypothesis
`hv1 : MeasureTheory.MemLp v 1` of the paper (`FibrePartIntegrable_of_memLp`, the *corrected*
statement), and the target itself is assembled from the two halves as hypotheses
(`FibrePartIntegrable_of_pieces`).  That missing hypothesis is not cosmetic: without it the
potential half is **false**, not merely unprovable — see the FINDING at the end of this file and
`Submission/Work/BoseFixR/PotFibreMarginalNoMemLp.lean`.
-/

namespace Work.BoseFixR

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The kinetic half of the fibre marginals

The anchored slot integrand of a smooth state is integrable on the box
(`integrableOn_fsT_fibre`, proved in `KinSplit`), so the two-block change of variables
`abox (k+j) ℓ ≃ abox k ℓ × abox j ℓ` plus Fubini gives both word marginals. -/

/-- **The kinetic half, in the general block form.**  For a smooth `Φ` and every `ℓ > 0` the
kinetic word of either block fibre is an honest Bochner integral over the corresponding box. -/
theorem kinFibreMarginal_general {k j : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
        Work.BoseKinLoc.kinFormB k ℓ d s εT b (Work.BoseFixR.bfL Φ y))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ)))
    ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
        Work.BoseKinLoc.kinFormB j ℓ d s εT b (Work.BoseFixR.bfR Φ z))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ))) := by
  constructor
  · -- ## the left block
    have hIntN : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (k + j) =>
        ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x))
        (Submission.BoseGases.abox (k + j) ℓ) :=
      integrable_finsetSum Finset.univ
        (fun i _ => integrableOn_fsT_fibre hℓ hΦ (Fin.castAdd j i))
    -- transfer the integrability along the block equivalence
    have hIntP : MeasureTheory.IntegrableOn
        (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
          ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ
              ((Work.BoseFixR.blockME k j) p)))
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) := by
      have h := (measurePreserving_blockME k j).integrableOn_image
        (MeasurableEquiv.measurableEmbedding (blockME k j))
        (f := fun x : Submission.BoseGases.X (k + j) =>
          ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x))
        (s := Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
      rw [blockME_image_abox] at h
      exact h.mp hIntN
    -- the slot identity of the block fibres
    have hIntG : MeasureTheory.IntegrableOn
        (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
          ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre k i (Work.BoseFixR.bfL Φ p.2) p.1))
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) :=
      hIntP.congr_fun (fun p _ => by
        exact Finset.sum_congr rfl
          (fun i _ => congrArg (Work.BoseKinLoc.fsT ℓ d s εT b 0)
            (Work.BoseFixR.fibre_blockME_castAdd Φ i p.1 p.2)))
        ((Submission.BoseGases.abox_measurable k ℓ).prod
          (Submission.BoseGases.abox_measurable j ℓ))
    -- Fubini: the marginal is integrable
    have hMarg : MeasureTheory.IntegrableOn (fun y : Submission.BoseGases.X j =>
        ∫ z in Submission.BoseGases.abox k ℓ,
          ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre k i (Work.BoseFixR.bfL Φ y) z))
        (Submission.BoseGases.abox j ℓ) :=
      Work.BoseFixR.integrableOn_inner_integral hIntG
    -- identify the inner integral with `kinFormB`
    have hMul : MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
        ℓ ^ (3 : ℤ) * Work.BoseKinLoc.kinFormB k ℓ d s εT b (Work.BoseFixR.bfL Φ y))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ)) :=
      hMarg.integrable.congr (Filter.Eventually.of_forall (fun y =>
        kinFormB_blockL hℓ hΦ y))
    -- remove the volume factor
    refine (hMul.const_mul ((ℓ ^ (3 : ℤ))⁻¹)).congr (Filter.Eventually.of_forall (fun y => ?_))
    change (ℓ ^ (3 : ℤ))⁻¹ * (ℓ ^ (3 : ℤ) *
      Work.BoseKinLoc.kinFormB k ℓ d s εT b (Work.BoseFixR.bfL Φ y))
      = Work.BoseKinLoc.kinFormB k ℓ d s εT b (Work.BoseFixR.bfL Φ y)
    rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
  · -- ## the right block
    have hIntN : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (k + j) =>
        ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x))
        (Submission.BoseGases.abox (k + j) ℓ) :=
      integrable_finsetSum Finset.univ
        (fun i _ => integrableOn_fsT_fibre hℓ hΦ (Fin.natAdd k i))
    have hIntP : MeasureTheory.IntegrableOn
        (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
          ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ
              ((Work.BoseFixR.blockME k j) p)))
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) := by
      have h := (measurePreserving_blockME k j).integrableOn_image
        (MeasurableEquiv.measurableEmbedding (blockME k j))
        (f := fun x : Submission.BoseGases.X (k + j) =>
          ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x))
        (s := Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
      rw [blockME_image_abox] at h
      exact h.mp hIntN
    have hIntG : MeasureTheory.IntegrableOn
        (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
          ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre j i (Work.BoseFixR.bfR Φ p.1) p.2))
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) :=
      hIntP.congr_fun (fun p _ => by
        exact Finset.sum_congr rfl
          (fun i _ => congrArg (Work.BoseKinLoc.fsT ℓ d s εT b 0)
            (Work.BoseFixR.fibre_blockME_natAdd Φ i p.1 p.2)))
        ((Submission.BoseGases.abox_measurable k ℓ).prod
          (Submission.BoseGases.abox_measurable j ℓ))
    have hMarg : MeasureTheory.IntegrableOn (fun z : Submission.BoseGases.X k =>
        ∫ y in Submission.BoseGases.abox j ℓ,
          ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre j i (Work.BoseFixR.bfR Φ z) y))
        (Submission.BoseGases.abox k ℓ) :=
      Work.BoseFixR.integrableOn_inner_integral' hIntG
    have hMul : MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
        ℓ ^ (3 : ℤ) * Work.BoseKinLoc.kinFormB j ℓ d s εT b (Work.BoseFixR.bfR Φ z))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)) :=
      hMarg.integrable.congr (Filter.Eventually.of_forall (fun z =>
        kinFormB_blockR hℓ hΦ z))
    refine (hMul.const_mul ((ℓ ^ (3 : ℤ))⁻¹)).congr (Filter.Eventually.of_forall (fun z => ?_))
    change (ℓ ^ (3 : ℤ))⁻¹ * (ℓ ^ (3 : ℤ) *
      Work.BoseKinLoc.kinFormB j ℓ d s εT b (Work.BoseFixR.bfR Φ z))
      = Work.BoseKinLoc.kinFormB j ℓ d s εT b (Work.BoseFixR.bfR Φ z)
    rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

/-! ## 2. The kinetic conjuncts at FS's parameters

`Adm v ε₀ μ` supplies `0 < μ`, so `ℓ = sideAt μ (a v) > 0`, and the general block statement
above applies verbatim. -/

theorem kinFibreMarginal_of_adm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {k j : ℕ} {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
        Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfL Φ y))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
    ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
        Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfR Φ z))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
  kinFibreMarginal_general (Work.BoseBox.sideAt_pos hμ.1 hav) hΦ

/-! ## 3. The potential half under the standing hypothesis `MemLp v 1`

Both halves are the same argument: the bare word is `L¹` on the box
(`Work.BoseFixB2.Pot.potWordU_integrable`) and a.e. strongly measurable
(`Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU`, which needs measurability of *both*
numerators `v` and `g₀ v h`; the latter is a structure field of `ScatSol v`), the continuous
factor `(block fibre)²` is bounded on the product box, and Fubini gives the marginal. -/

/-- **The left potential marginal** under `MemLp v 1`. -/
theorem potFibreMarginal_left_of_interface {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hv_aesm : MeasureTheory.AEStronglyMeasurable v volume) {μ ℓ : ℝ} (hℓ : 0 < ℓ)
    {k j : ℕ} {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hIk : MeasureTheory.IntegrableOn (fun z : Submission.BoseGases.X k =>
      Work.BoseKinLoc.potWordU k v (Submission.BoseGases.g0 v h) ℓ μ 0 z)
      (Submission.BoseGases.abox k ℓ) volume) :
    MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
      ∫ z in Submission.BoseGases.abox k ℓ,
        (Work.BoseFixR.bfL Φ y z) ^ 2 *
          Work.BoseKinLoc.potWordU k v (Submission.BoseGases.g0 v h) ℓ μ 0 z)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ)) := by
  set U : Submission.BoseGases.X k → ℝ := fun z =>
    Work.BoseKinLoc.potWordU k v (Submission.BoseGases.g0 v h) ℓ μ 0 z with hU
  have hUI : MeasureTheory.IntegrableOn U (Submission.BoseGases.abox k ℓ) volume := by
    rw [hU]; exact hIk
  have hgaesm : MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.g0 v h) volume :=
    (Submission.BoseGases.g0_integrable hR hv_supp h).aestronglyMeasurable
  have hUaesm : MeasureTheory.AEStronglyMeasurable U volume :=
    Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU (N := k) (ℓ := ℓ) (μ := μ) (u := 0)
      hv_aesm hgaesm
  -- `Φ` is bounded on the box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (k + j) hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox (k + j) ℓ) (f := Φ) hΦ.continuous.continuousOn
  -- the uncurried integrand is integrable on the product box
  have hprod : MeasureTheory.IntegrableOn
      (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
        (Work.BoseFixR.bfL Φ p.2 p.1) ^ 2 * U p.1)
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) volume := by
    rw [MeasureTheory.IntegrableOn,
      show (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j))
        = (volume : Measure (Submission.BoseGases.X k)).prod
          (volume : Measure (Submission.BoseGases.X j)) from rfl,
      ← MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.Integrable.bdd_mul (c := C ^ 2) ?hg ?hf ?hb
    · -- the bare word, as a function of the first block only
      have hconst : MeasureTheory.Integrable (fun _ : Submission.BoseGases.X j => (1 : ℝ))
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ)) :=
        MeasureTheory.integrableOn_const (μ := volume) (s := Submission.BoseGases.abox j ℓ)
          (C := (1 : ℝ)) (Submission.BoseGases.abox_lt_top j ℓ hℓ.le).ne (by norm_num)
      simpa only [mul_one] using MeasureTheory.Integrable.mul_prod hUI hconst
    · -- measurability of the continuous factor
      have hbf : (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
          (Work.BoseFixR.bfL Φ p.2 p.1) ^ 2)
          = fun p => Φ ((Work.BoseFixR.blockME k j) p) ^ 2 := by
        funext p
        rw [congrFun (Work.BoseFixR.bfL_eq_blockME Φ p.2) p.1]
      rw [hbf]
      exact (((hΦ.continuous.measurable.comp (Work.BoseFixR.blockME k j).measurable)).pow_const
        2).aestronglyMeasurable
    · -- the pointwise bound on the product box
      rw [show (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)).prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ))
          = (MeasureTheory.volume : MeasureTheory.Measure
              (Submission.BoseGases.X k × Submission.BoseGases.X j)).restrict
              (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) from by
        rw [show (MeasureTheory.volume : MeasureTheory.Measure
              (Submission.BoseGases.X k × Submission.BoseGases.X j))
            = (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).prod
              (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X j)) from rfl,
          MeasureTheory.Measure.prod_restrict]]
      refine (ae_restrict_iff' (MeasurableSet.prod (Submission.BoseGases.abox_measurable k ℓ)
        (Submission.BoseGases.abox_measurable j ℓ))).mpr ?_
      filter_upwards with p hp
      obtain ⟨hz, hy⟩ := hp
      have hmem : (Work.BoseFixR.blockME k j) p ∈ Submission.BoseGases.abox (k + j) ℓ := by
        rw [← Work.BoseFixR.blockME_image_abox k j ℓ]
        exact ⟨p, ⟨hz, hy⟩, rfl⟩
      have hb : ‖Φ ((Work.BoseFixR.blockME k j) p)‖ ≤ C := hC _ hmem
      have hbf : Work.BoseFixR.bfL Φ p.2 p.1 = Φ ((Work.BoseFixR.blockME k j) p) :=
        congrFun (Work.BoseFixR.bfL_eq_blockME Φ p.2) p.1
      rw [hbf, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb' : |Φ ((Work.BoseFixR.blockME k j) p)| ≤ C := by
        simpa [Real.norm_eq_abs] using hb
      calc Φ ((Work.BoseFixR.blockME k j) p) ^ 2
          = |Φ ((Work.BoseFixR.blockME k j) p)| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb' 2
  exact Work.BoseFixR.integrableOn_inner_integral hprod

/-- **The right potential marginal** under `MemLp v 1`. -/
theorem potFibreMarginal_right_of_interface {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hv_aesm : MeasureTheory.AEStronglyMeasurable v volume) {μ ℓ : ℝ} (hℓ : 0 < ℓ)
    {k j : ℕ} {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hIj : MeasureTheory.IntegrableOn (fun y : Submission.BoseGases.X j =>
      Work.BoseKinLoc.potWordU j v (Submission.BoseGases.g0 v h) ℓ μ 0 y)
      (Submission.BoseGases.abox j ℓ) volume) :
    MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
      ∫ y in Submission.BoseGases.abox j ℓ,
        (Work.BoseFixR.bfR Φ z y) ^ 2 *
          Work.BoseKinLoc.potWordU j v (Submission.BoseGases.g0 v h) ℓ μ 0 y)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)) := by
  set U : Submission.BoseGases.X j → ℝ := fun y =>
    Work.BoseKinLoc.potWordU j v (Submission.BoseGases.g0 v h) ℓ μ 0 y with hU
  have hUI : MeasureTheory.IntegrableOn U (Submission.BoseGases.abox j ℓ) volume := by
    rw [hU]; exact hIj
  have hgaesm : MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.g0 v h) volume :=
    (Submission.BoseGases.g0_integrable hR hv_supp h).aestronglyMeasurable
  have hUaesm : MeasureTheory.AEStronglyMeasurable U volume :=
    Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU (N := j) (ℓ := ℓ) (μ := μ) (u := 0)
      hv_aesm hgaesm
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (k + j) hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox (k + j) ℓ) (f := Φ) hΦ.continuous.continuousOn
  have hprod : MeasureTheory.IntegrableOn
      (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
        (Work.BoseFixR.bfR Φ p.1 p.2) ^ 2 * U p.2)
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) volume := by
    rw [MeasureTheory.IntegrableOn,
      show (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j))
        = (volume : Measure (Submission.BoseGases.X k)).prod
          (volume : Measure (Submission.BoseGases.X j)) from rfl,
      ← MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.Integrable.bdd_mul (c := C ^ 2) ?hg ?hf ?hb
    · have hconst : MeasureTheory.Integrable (fun _ : Submission.BoseGases.X k => (1 : ℝ))
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)) :=
        MeasureTheory.integrableOn_const (μ := volume) (s := Submission.BoseGases.abox k ℓ)
          (C := (1 : ℝ)) (Submission.BoseGases.abox_lt_top k ℓ hℓ.le).ne (by norm_num)
      simpa only [one_mul] using MeasureTheory.Integrable.mul_prod hconst hUI
    · have hbf : (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
          (Work.BoseFixR.bfR Φ p.1 p.2) ^ 2)
          = fun p => Φ ((Work.BoseFixR.blockME k j) p) ^ 2 := by
        funext p
        rw [congrFun (Work.BoseFixR.bfR_eq_blockME Φ p.1) p.2]
      rw [hbf]
      exact (((hΦ.continuous.measurable.comp (Work.BoseFixR.blockME k j).measurable)).pow_const
        2).aestronglyMeasurable
    · 
      rw [show (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)).prod
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ))
          = (MeasureTheory.volume : MeasureTheory.Measure
              (Submission.BoseGases.X k × Submission.BoseGases.X j)).restrict
              (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) from by
        rw [show (MeasureTheory.volume : MeasureTheory.Measure
              (Submission.BoseGases.X k × Submission.BoseGases.X j))
            = (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).prod
              (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X j)) from rfl,
          MeasureTheory.Measure.prod_restrict]]
      refine (ae_restrict_iff' (MeasurableSet.prod (Submission.BoseGases.abox_measurable k ℓ)
        (Submission.BoseGases.abox_measurable j ℓ))).mpr ?_
      filter_upwards with p hp
      obtain ⟨hz, hy⟩ := hp
      have hmem : (Work.BoseFixR.blockME k j) p ∈ Submission.BoseGases.abox (k + j) ℓ := by
        rw [← Work.BoseFixR.blockME_image_abox k j ℓ]
        exact ⟨p, ⟨hz, hy⟩, rfl⟩
      have hb : ‖Φ ((Work.BoseFixR.blockME k j) p)‖ ≤ C := hC _ hmem
      have hbf : Work.BoseFixR.bfR Φ p.1 p.2 = Φ ((Work.BoseFixR.blockME k j) p) :=
        congrFun (Work.BoseFixR.bfR_eq_blockME Φ p.1) p.2
      rw [hbf, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb' : |Φ ((Work.BoseFixR.blockME k j) p)| ≤ C := by
        simpa [Real.norm_eq_abs] using hb
      calc Φ ((Work.BoseFixR.blockME k j) p) ^ 2
          = |Φ ((Work.BoseFixR.blockME k j) p)| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb' 2
  exact Work.BoseFixR.integrableOn_inner_integral' hprod


/-- **The left potential marginal** under the standing hypothesis `MemLp v 1`. -/
theorem potFibreMarginal_memLp_left {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {μ ℓ : ℝ} (hℓ : 0 < ℓ)
    {k j : ℕ} {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
      ∫ z in Submission.BoseGases.abox k ℓ,
        (Work.BoseFixR.bfL Φ y z) ^ 2 *
          Work.BoseKinLoc.potWordU k v (Submission.BoseGases.g0 v h) ℓ μ 0 z)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ)) :=
  potFibreMarginal_left_of_interface h hR hv_supp hv1.aestronglyMeasurable hℓ hΦ
    (Work.BoseFixB2.Pot.potWordU_integrable (μ := μ) h hR hv_supp hv1 ℓ)

/-- **The right potential marginal** under the standing hypothesis `MemLp v 1`. -/
theorem potFibreMarginal_memLp_right {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {μ ℓ : ℝ} (hℓ : 0 < ℓ)
    {k j : ℕ} {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
      ∫ y in Submission.BoseGases.abox j ℓ,
        (Work.BoseFixR.bfR Φ z y) ^ 2 *
          Work.BoseKinLoc.potWordU j v (Submission.BoseGases.g0 v h) ℓ μ 0 y)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)) :=
  potFibreMarginal_right_of_interface h hR hv_supp hv1.aestronglyMeasurable hℓ hΦ
    (Work.BoseFixB2.Pot.potWordU_integrable (μ := μ) h hR hv_supp hv1 ℓ)

/-! ## 4. The assemblies -/

/-- **The general assembly from the two interface facts.**  The four marginals follow from the
kinetic half together with, for the potential word,

* `hv_aesm : AEStronglyMeasurable v` — supplied by `LocallyIntegrable v`
  (`MeasureTheory.LocallyIntegrable.aestronglyMeasurable`) and by `MemLp v 1`; this is what
  `Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU` needs, and it is *not* available from
  `ScatSol v` (see the FINDING at the end of this file);
* `hUI` — box-integrability of the bare word `potWordU N v (g₀ v h) ℓ' μ 0` for every `N`, `ℓ'`,
  `μ`; supplied by `Work.BoseFixR.PotWordUIntegrableLoc` from `LocallyIntegrable v` and
  `LocallyIntegrable (g₀ v h)` (the vocabulary of `Work.BoseFixR.wordB_split`), and by
  `MemLp v 1` through `Work.BoseFixB2.Pot.potWordU_integrable`.

No diluteness hypothesis is needed on this route: the box-integrability of the bare word is an
input, and the continuous factor `(block fibre)²` is bounded on the compact product box. -/
theorem FibrePartIntegrable_of_interface {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hv_aesm : MeasureTheory.AEStronglyMeasurable v volume)
    (hUI : ∀ (N : ℕ) (ℓ' μ : ℝ), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.BoseKinLoc.potWordU N v (Submission.BoseGases.g0 v h) ℓ' μ 0 x)
      (Submission.BoseGases.abox N ℓ') volume) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {k j : ℕ}
      {Φ : Submission.BoseGases.X (k + j) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Φ →
      (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfL Φ y))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfR Φ z))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) := by
  refine ⟨1 / 2, by norm_num, fun μ hμ k j Φ hΦ => ?_⟩
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ.1 hav
  obtain ⟨hk1, hk2⟩ := kinFibreMarginal_of_adm h hav hμ hΦ
  exact ⟨hk1,
    potFibreMarginal_left_of_interface h hR hv_supp hv_aesm hℓ hΦ
      (hUI k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ),
    hk2,
    potFibreMarginal_right_of_interface h hR hv_supp hv_aesm hℓ hΦ
      (hUI j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ)⟩

/-- **The corrected statement** (with the standing hypothesis `MemLp v 1`): all four fibre
marginals are honest Bochner integrals. -/
theorem FibrePartIntegrable_of_memLp {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {k j : ℕ}
      {Φ : Submission.BoseGases.X (k + j) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Φ →
      (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfL Φ y))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfR Φ z))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) := by
  exact FibrePartIntegrable_of_interface h hR hv_supp hav hv1.aestronglyMeasurable
    (fun N ℓ' μ => Work.BoseFixB2.Pot.potWordU_integrable (μ := μ) h hR hv_supp hv1 ℓ')

/-- **The assembly of the target from the two halves.**  If the kinetic half (with no
hypothesis beyond `0 < ℓ`) and the potential half (under the diluteness condition
`R ≤ sideAt μ (a v)·chiR0`, which `exists_adm_chiR0_ge` produces from `Adm` for small `ε₀`)
are available as theorems, then the four marginals of the target follow. -/
theorem FibrePartIntegrable_of_pieces {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < _root_.BoseGases.a v) {R : ℝ} (hR : 0 < R)
    (hK : ∀ (μ : ℝ), 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) → ∀ {k j : ℕ}
      {Φ : Submission.BoseGases.X (k + j) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Φ →
      (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfL Φ y))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfR Φ z))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))))
    (hP : ∀ (μ : ℝ), 0 < μ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 → ∀ {k j : ℕ}
      {Φ : Submission.BoseGases.X (k + j) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Φ →
      (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {k j : ℕ}
      {Φ : Submission.BoseGases.X (k + j) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Φ →
      (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfL Φ y))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfR Φ z))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) := by
  obtain ⟨ε₀, hε₀, hregime⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  refine ⟨ε₀, hε₀, fun μ hμ k j Φ hΦ => ?_⟩
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ.1 hav
  obtain ⟨hk1, hk2⟩ := hK μ hℓ hΦ
  obtain ⟨hp1, hp2⟩ := hP μ hμ.1 (hregime μ hμ) hΦ
  exact ⟨hk1, hp1, hk2, hp2⟩

/-! ## 5. The requested statement

The target follows from `FibrePartIntegrable_of_pieces` **iff** the potential half is available
without the integrability hypothesis on `v`; this is exactly the point of the FINDING below. -/

/-- **The target from the single remaining piece.**  The kinetic half is a theorem
(`kinFibreMarginal_general`), so the *whole* target is equivalent to the potential half under the
dilute condition `R ≤ sideAt μ (a v)·chiR0`.  A consumer who has a proof of that half — for
instance from `LocallyIntegrable v` plus `Work.BoseFixR.PotWordUIntegrableLoc`, or from
`PotFibreMarginalMemLp` plus `MemLp v 1` — gets the target by one application of this lemma. -/
theorem FibrePartIntegrable_of_potHalf {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < _root_.BoseGases.a v) {R : ℝ} (hR : 0 < R)
    (hP : ∀ (μ : ℝ), 0 < μ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 → ∀ {k j : ℕ}
      {Φ : Submission.BoseGases.X (k + j) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Φ →
      (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {k j : ℕ}
      {Φ : Submission.BoseGases.X (k + j) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Φ →
      (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfL Φ y))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfR Φ z))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
  FibrePartIntegrable_of_pieces h hav hR
    (fun μ hℓ k j Φ hΦ => kinFibreMarginal_general hℓ hΦ) hP

theorem FibrePartIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {k j : ℕ}
      {Φ : Submission.BoseGases.X (k + j) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Φ →
      (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfL Φ y))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
          ∫ z in Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 z)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfR Φ z))
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))))
      ∧ (MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
          ∫ y in Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v
              (Submission.BoseGases.g0 v h) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ 0 y)
        (MeasureTheory.volume.restrict
          (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) := by sorry


/-!
## FINDING — the target is missing the standing hypothesis `MemLp v 1`

**Verdict.**  `Work.BoseFixR.FibrePartIntegrable` is *not provable as stated*: two of its four
conjuncts (the potential halves) need a hypothesis on the potential `v` that
`h : Work.UBB.ScatSol v` does not supply.  With the paper's standing hypothesis
`hv1 : MeasureTheory.MemLp v 1` added the statement is a theorem:
`FibrePartIntegrable_of_memLp` above (proved, `sorry`-free).

**The reduction (machine-checked).**  `FibrePartIntegrable_of_pieces` above proves that the
target follows from

* the kinetic half, which is *proved here* for every smooth `Φ` and every box side `ℓ > 0`
  (`kinFibreMarginal_general`), with no hypothesis on `v` whatsoever — the anchored slot
  integrand is already integrable on the box for smooth states (`integrableOn_fsT_fibre`), and
  the block change of variables plus Fubini concludes (`kinFibreMarginal_of_adm` gives the
  target's two kinetic conjuncts at `ℓ = sideAt μ (a v)`, using only `0 < sideAt μ (a v)`);
* the potential half under the dilute condition `R ≤ sideAt μ (a v) · chiR0`, which
  `Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge` derives from `Adm v ε₀ μ` for small `ε₀`.

So all the difficulty sits in the potential half.

**Why the potential half needs the hypothesis.**  `potWordU N v g ℓ μ 0` contains the pair sum
`Σ_{i<j} wLoc ℓ v 0 (x_i) (x_j)` with `wLoc ℓ v 0 a b = χ(a)·v(a−b)/(χ⋆χ)((a−b)/ℓ)·χ(b)`, i.e.
the *bare* potential `v` is the two-body kernel numerator.

1. *Measurability.*  `Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU` produces
   `AEStronglyMeasurable (fun x => potWordU N v g ℓ μ u x)` from `AEStronglyMeasurable v` **and**
   `AEStronglyMeasurable g`.  The second is available (`g₀ v h = v·(1−w₀)` is a field of
   `IsScatteringSolution`), the first is not: `IsScatteringSolution w v` constrains `v` only
   through `v·(1−w)`, so `v` is unconstrained on `{w = 1}` and may be non-measurable there.  The
   marginal requires joint a.e. strong measurability of the uncurried integrand, which is exactly
   what `Fubini`-type measurability lemmas (`AEStronglyMeasurable.integral_prod_right'`) need —
   there is no slice-wise version in Mathlib (and none can exist).
2. *`L¹`-ness.*  The dilute-régime pointwise bound `Work.BoseFixGlue.Pot.abs_potWordU_le` gives,
   with `C := chiSup`, under exactly the target's hypotheses (`hℓ`, `hRℓ`, `chiR0_half`, `hav`)
   `|potWordU N v (g₀ v h) ℓ μ 0 x| ≤ |μ|·N·(2C²∫|g₀|) + C²·Σ_{i<j} 2|v(x_i − x_j)|`,
   whose right-hand side is *not* uniformly bounded, so
   `∫⁻_{abox N ℓ} ‖potWordU N v (g₀ v h) ℓ μ 0‖ₑ = ∞` as soon as `v ∉ L¹(B(0, 2ℓ))`.
   Consistently, *every* corpus supplier of the box integrability of the bare word carries the
   missing hypothesis: `Work.BoseFixB2.Pot.potWordU_integrable` (`MemLp v 1`), the delegated
   `Work.BoseFixR.PotWordUIntegrableLoc` (`LocallyIntegrable v`, `LocallyIntegrable g`), and the
   pair-kernel master inequality `Work.BoseFixR.lintegral_wPairC_acube_le`
   (`IntegrableOn h (closedBall 0 ℓ)`).

**`ScatSol v` does not provide it — the potential half is FALSE without it.**  The potential
half without the hypothesis was requested separately (`Work.BoseFixR.PotFibreMarginalNoMemLp`);
the colleague who worked it refuted it, and the refutation is recorded in full in
`Submission/Work/BoseFixR/PotFibreMarginalNoMemLp.lean`.  The data are the counterexample family
of `Submission/Work/BoseFixB1/FINDING_sbWord_marginal_integrable_missing_hv1.md` — `ψ ≡ 0` on
`‖x‖ ≤ ε`, `ψ(r) = a∫_ε^r f(s)/s² ds` for smooth increasing `f` vanishing on `(−∞, ε]` and `≡ 1`
on `[r₀, ∞)`, normalised so that `ψ → 1`; `w := 1 − ψ`, `v := 2Δψ/ψ`.  Then `v` is radial,
`0 ≤ v`, `tsupport v ⊆ ball 0 R` for `R > r₀`, `ScatSol v` holds through `w` and `a v = a > 0`
— *every* hypothesis of the target — while `v ∼ 2dist(·, S_ε)^{−4}` near the sphere
`S_ε = {‖u‖ = ε}` (`v = 0` inside it), so `v ∉ L¹_loc`.

One then takes `k = j = 2`, `μ > 0` small (so that `R ≤ sideAt μ (a v)·chiR0`, which the target
supplies through `Adm`) and the *moving* bump `Φ(z₁,z₂,y₁,y₂) := η(z₁ − y₁, z₂ − y₂)` with
`η ∈ C_c^∞(ℝ⁶)` of radius `r`.  Then `bfL Φ y z = η(z₁ − y₁, z₂ − y₂)` is supported on
`{|(z₁−z₂) − (y₁−y₂)| ≤ √2 r}` (parallelogram identity), so the slice integrand sees the
singular set `{z₁ − z₂ ∈ S_ε}` exactly when `dist(y₁ − y₂, S_ε) < √2 r`: there its `∫⁻` is
infinite and Mathlib's inner Bochner integral is the junk value `0`, whereas for
`dist(y₁ − y₂, S_ε) > √2 r` it is honest and dominates `c·(dist(y₁−y₂,S_ε) − √2 r)^{−2}` with
`c > 0`.  The marginal therefore dominates a function whose integral over `abox 2 ℓ` diverges
(the level sets of `y ↦ dist(y₁−y₂,S_ε)` have positive bounded `5`-dimensional measure and
`∫_0 s^{−2} ds = ∞`), so the first potential conjunct — hence the target — is false.  In other
words the target is not merely unprovable: it *fails* for admissible data.

(`Work.BoseFixR.wordB_split`, `Work.BoseFixR.PotSplit` and `Work.BoseFixR.KinSplit` all apply
`MeasureTheory.integral_add`, monotonicity and Fubini to these integrals, so the missing
hypothesis is precisely what makes those applications meaningful.)

**Repair (delivered).**  Add `(hv1 : MeasureTheory.MemLp v 1)` — nothing else.  This is the
standing hypothesis of the paper (`Submission.lean`'s `theorem_1_2` assumes it), of every sibling
in this chain (`Work.BoseFixR.windowBound`, `Work.BoseFixR.PerBoxWordCrudeHigh`,
`Work.BoseFixR.PotFibreMarginalMemLp`, the `Work.BoseFixB2` chapters) and of the whole UBB
assembly.  The corrected statement `FibrePartIntegrable_of_memLp` is proved above, so a consumer
may replace `FibrePartIntegrable` by it verbatim; if the local-integrability vocabulary
(`hvi : MeasureTheory.LocallyIntegrable v`, as in `wordB_split`) is preferred, instantiate the
same proof with `LocallyIntegrable.aestronglyMeasurable` and
`Work.BoseFixR.PotWordUIntegrableLoc`.
-/

end Work.BoseFixR
