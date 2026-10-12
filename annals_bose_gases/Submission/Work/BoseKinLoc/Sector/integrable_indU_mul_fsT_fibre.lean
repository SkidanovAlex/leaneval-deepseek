import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Sector.aemeasurable_gapWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.aemeasurable_mainWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.aemeasurable_momWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.aemeasurable_neuWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.fsT_bound_all
import Submission.Work.BoseKinLoc.Word.boxFormB_eq_boxForm_of_supp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre`

**The slot-`i` kinetic integrand of the localised box form is integrable.**  For a smooth state
`Ψ` supported in the configuration box `abox N L` and every slot `i`, the function

    `x ↦ 1_{Λ(0)}(xᵢ) · fsT ℓ d s ε_T b 0 (fibre N i Ψ x)`

(the `i`-th summand of the box-restricted kinetic word `kinFormB`) is integrable on `X N`.

## Proof

*Measurability.*  Peel the slot `i` by the measure preserving equivalence
`kcInsN n i : ℝ³ × X n ≃ᵐ X (n+1)`: for `x = kcInsN n i (y,r)` the fibre `fibre (n+1) i Ψ x` is
`genFibre i Ψ r = z ↦ Ψ (kcInsN n i (z,r))`, which does not depend on the inserted coordinate `y`.
So the target is the product function `(y,r) ↦ 1_{Λ(0)}(y) · fsT ℓ d s ε_T b 0 (genFibre i Ψ r)`,
and the fibre word is a.e. strongly measurable in `r` — this is the `u = 0` slice of the joint
measurability of `fsT` along the slot fibres, assembled from the four one-body words
(`aemeasurable_neuWord_zero_fibre`, `aemeasurable_gapWord_zero_fibre`,
`aemeasurable_momWord_zero_fibre`, `aemeasurable_mainWord_zero_fibre`; the two words carrying the
factor `(dℓ)⁻²` vanish identically when `d = 0`).

*Integrability.*  `fsT` is bounded by a constant times the free `H¹`-norm of its argument
(`Kinetic.fsT_H1_bound_all`), the `H¹`-data of the slot fibres is integrable in `r`
(`Kinetic.integral_fibre_sq` + `Kinetic.dSpace_fibre_eq`), and the box indicator `1_{Λ(0)}` is
integrable on `ℝ³` — so the product function is integrable by `Integrable.mul_prod`.  Finally the
change of variables `kcInsN n i` transfers integrability back to `X (n+1)`
(`MeasurePreserving.integrable_comp`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The measurability of the anchored fibre word -/

/-- **The slot-`i` fibre word at the anchored box is a.e. strongly measurable in the remaining
coordinates.**  For a smooth state `Ψ` supported in `abox (n+1) L`,

    `r ↦ fsT ℓ d s ε_T b 0 (genFibre i Ψ r)`

is a.e. strongly measurable; this is the pointwise (`u = 0`) companion of the joint measurability
of `fsT` along the slot fibres, which is *not* available by slicing at `u = 0` because a fixed
slice of a product-a.e.-measurable function need not be measurable. -/
theorem aemeasurable_fsT_genFibre_zero {n : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
      MeasureTheory.volume := by
  have hgap := aemeasurable_gapWord_zero_fibre (ℓ := ℓ) (b := b) (L := L) hℓ hL hΨ hsupp i
  have hmain := aemeasurable_mainWord_zero_fibre (ℓ := ℓ) (d := d) (s := s) (εT := εT) (L := L)
    hℓ hL hΨ hsupp i
  by_cases hd : d = 0
  · have hsum : (fun r : Submission.BoseGases.X n =>
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = fun r => (0 : ℝ)
            + Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
            + 0 + Work.BoseKinLoc.mainWord ℓ d s εT 0
                (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) := by
      funext r
      rw [Work.BoseKinLoc.fsT_eq_sum, hd]
      simp [Work.BoseKinLoc.neuWord, Work.BoseKinLoc.momWord]
    rw [hsum]
    exact ((aestronglyMeasurable_const.add hgap).add aestronglyMeasurable_const).add hmain
  · have hneu := aemeasurable_neuWord_zero_fibre (ℓ := ℓ) (d := d) (εT := εT) (L := L)
      hℓ hd hL hΨ hsupp i
    have hmom := aemeasurable_momWord_zero_fibre (ℓ := ℓ) (d := d) (εT := εT) (b := b) (L := L)
      hℓ hL hΨ hsupp i
    have hsum : (fun r : Submission.BoseGases.X n =>
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = fun r => Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
            + Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
            + Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
            + Work.BoseKinLoc.mainWord ℓ d s εT 0
                (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) := by
      funext r
      rw [Work.BoseKinLoc.fsT_eq_sum]
    rw [hsum]
    exact ((hneu.add hgap).add hmom).add hmain

/-! ## The target -/

theorem integrable_indU_mul_fsT_fibre {N : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L) (i : Fin N) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i Ψ x)) := by
  rcases N with _ | n
  · exact i.elim0
  -- the state is compactly supported
  have hcsΨ : HasCompactSupport Ψ :=
    IsCompact.of_isClosed_subset
      (Work.BoseKinLoc.Kinetic.abox_compact_of_nonneg (n + 1) hL) (isClosed_tsupport Ψ) hsupp
  -- ## Step 1: the fibre word is integrable in the remaining coordinates
  have hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)) MeasureTheory.volume :=
    aemeasurable_fsT_genFibre_zero hℓ hL hΨ hsupp i
  obtain ⟨C, hC0, hCbd⟩ :=
    Work.BoseKinLoc.Kinetic.fsT_H1_bound_all (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ
  have hAint : MeasureTheory.Integrable
      (fun r : Submission.BoseGases.X n =>
        ∫ z : ℝ³, (Work.BoseKinLoc.Kinetic.genFibre i Ψ r z) ^ 2) :=
    (Work.BoseKinLoc.Kinetic.integral_fibre_sq (n := n) hΨ hcsΨ i).1
  have hDint : MeasureTheory.Integrable
      (fun r : Submission.BoseGases.X n =>
        Work.BSKinetic.dSpace (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)) :=
    (Work.BoseKinLoc.Kinetic.dSpace_fibre_eq (n := n) hΨ hcsΨ i).1
  set M : Submission.BoseGases.X n → ℝ := fun r =>
    (∫ z : ℝ³, (Work.BoseKinLoc.Kinetic.genFibre i Ψ r z) ^ 2)
      + Work.BSKinetic.dSpace (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) with hM
  have hMint : MeasureTheory.Integrable M MeasureTheory.volume := by
    rw [hM]
    exact hAint.add hDint
  have hFint : MeasureTheory.Integrable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
      MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono' (hMint.const_mul C) hFmeas ?_
    filter_upwards with r
    rw [hM]
    have hb := hCbd 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
      (Work.BoseKinLoc.Kinetic.genFibre_contDiff hΨ i r)
      (Work.BoseKinLoc.Kinetic.genFibre_hasCompactSupport_of_supp hL hsupp i r)
    simpa only [Real.norm_eq_abs, Work.BSKinetic.dSpace] using hb
  -- ## Step 2: the product with the box indicator is integrable
  have hlam_zero : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
    ext z
    simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
  have hind : MeasureTheory.Integrable (fun y : ℝ³ => Work.BoseKinLoc.indU ℓ 0 y)
      MeasureTheory.volume := by
    rw [Work.BoseKinLoc.indU, MeasureTheory.integrable_indicator_iff
      (Work.BoseKinLoc.Word.measurableSet_lamBox ℓ 0)]
    refine MeasureTheory.integrableOn_const ?_ (by simp)
    rw [hlam_zero, Submission.BoseGases.acube_volume ℓ hℓ.le]
    exact ENNReal.ofReal_lt_top.ne
  have hprod : MeasureTheory.Integrable
      (fun q : ℝ³ × Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 q.1
          * Work.BoseKinLoc.fsT ℓ d s εT b 0
              (Work.BoseKinLoc.Kinetic.genFibre i Ψ q.2))
      MeasureTheory.volume :=
    MeasureTheory.Integrable.mul_prod hind hFint
  -- ## Step 3: transfer along the measure preserving insertion
  set g : Submission.BoseGases.X (n + 1) → ℝ := fun x =>
    Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
      (Work.BoseKinLoc.fibre (n + 1) i Ψ x) with hg
  have hfib_eq : ∀ (y : ℝ³) (r : Submission.BoseGases.X n),
      Work.BoseKinLoc.fibre (n + 1) i Ψ (Submission.BoseGases.kcInsN n i (y, r))
        = Work.BoseKinLoc.Kinetic.genFibre i Ψ r := by
    intro y r
    funext z
    simp only [Work.BoseKinLoc.fibre, Work.BoseKinLoc.Kinetic.genFibre,
      Submission.BoseGases.update_kcInsN]
  have hcomp : MeasureTheory.Integrable (g ∘ ⇑(Submission.BoseGases.kcInsN n i))
      MeasureTheory.volume := by
    refine hprod.congr (Filter.Eventually.of_forall fun q => ?_)
    obtain ⟨y, r⟩ := q
    simp only [Function.comp_apply, hg, Submission.BoseGases.kc_insN_apply_same, hfib_eq]
  have hmeasg : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume :=
    ((Submission.BoseGases.kc_mp_insN n i).aestronglyMeasurable_comp_iff
      (Submission.BoseGases.kcInsN n i).measurableEmbedding).mp hcomp.1
  exact ((Submission.BoseGases.kc_mp_insN n i).integrable_comp hmeasg).mp hcomp

end Work.BoseKinLoc.Sector
