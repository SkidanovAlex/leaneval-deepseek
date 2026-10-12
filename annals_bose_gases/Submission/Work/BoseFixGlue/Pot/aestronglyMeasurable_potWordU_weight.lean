import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixGlue.Residuals
import Submission.Work.BoseSym.Form.qmp_pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight`

A.e. strong measurability of the weighted potential word `(Φ x)² · potWordU N v g ℓ μ u x`
on the product space `ℝ³ × X N`, for a.e. measurable one-body potentials `v, g` (with respect
to Lebesgue measure on `ℝ³`) and a continuous weight `Φ : X N → ℝ`.

`potWordU` (FS `eq:Def_HB`'s multiplicative part) is the sum of a one-body term and a
two-body term,

    `potWordU N v g ℓ μ u x = -μ * Σᵢ ∫_y wLoc ℓ g u (xᵢ) y + Σ_{i<j} wLoc ℓ v u (xᵢ) (xⱼ)`,

where the localisation kernel is `wLoc ℓ h u x y = χ_u(x) · (h(x−y)/(χ⋆χ)((x−y)/ℓ)) · χ_u(y)`.
The mathematical content is therefore:

* the maps `(u,x) ↦ xᵢ − xⱼ` (pair terms) and `((u,x),y) ↦ xᵢ − y` (the parametric `y`-integral)
  are quasi-measure-preserving, so that `v`/`g` — only a.e. measurable on `ℝ³` — may be
  composed with them (`AEMeasurable.comp_quasiMeasurePreserving`);
* the `y`-integral is a measurable function of the parameter
  (`AEStronglyMeasurable.integral_prod_right'`, which needs no integrability hypothesis);
* the remaining factors `χ_u`, `(χ⋆χ)((·)/ℓ)⁻¹`, `Φ²` are continuous (hence strongly
  measurable) and closed under pointwise products and finite sums.

The two geometric inputs are the corpus' `Work.BoseSym.Form.qmp_pair_pi` (the two-coordinate
projection `x ↦ (x i, x j)` is quasi-measure-preserving) together with
`Measure.quasiMeasurePreserving_eval`, `Measure.quasiMeasurePreserving_snd` and
`quasiMeasurePreserving_sub_of_right_invariant`.

## Contents

* `qmp_pair_coord`, `qmp_coord`, `qmp_coordDiff`, `qmp_coordDiff_prod` — the QMP facts;
* `aestronglyMeasurable_wLoc_pair` — the two-body term `(u,x) ↦ wLoc ℓ v u (xᵢ) (xⱼ)`;
* `aestronglyMeasurable_wLoc_integrand` — the triple-product integrand of the `y`-integral;
* `aestronglyMeasurable_wLoc_integral` — the parametric integral `(u,x) ↦ ∫_y wLoc ℓ g u (xᵢ) y`;
* `aestronglyMeasurable_potWordU_weight` — the target.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixGlue.Pot

set_option maxHeartbeats 2000000

/-! ## 1. Quasi-measure-preserving coordinate maps

All measures below are Lebesgue (`volume`).  On `X N = Fin N → ℝ³` this is the product
measure; the only two-coordinate input is `Work.BoseSym.Form.qmp_pair_pi`. -/

/-- **The two-coordinate projection of `X N` is quasi-measure-preserving.**  For `i ≠ j`,
`x ↦ (x i, x j)` pushes the product Lebesgue measure on `X N = Fin N → ℝ³` to a measure
absolutely continuous w.r.t. `volume.prod volume` on `ℝ³ × ℝ³`. -/
lemma qmp_pair_coord {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Measure.QuasiMeasurePreserving (fun x : Submission.BoseGases.X N => (x i, x j))
      (MeasureTheory.volume : Measure (Submission.BoseGases.X N))
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
  have h := Work.BoseSym.Form.qmp_pair_pi (ι := Fin N) i j hij
  rwa [← MeasureTheory.volume_pi] at h

/-- **A single coordinate of `ℝ³ × X N` is quasi-measure-preserving.** -/
lemma qmp_coord {N : ℕ} (i : Fin N) :
    Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N => p.2 i)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  (Measure.quasiMeasurePreserving_eval
    (fun _ : Fin N => (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) i).comp
    Measure.quasiMeasurePreserving_snd

/-- Subtraction on `ℝ³ × ℝ³` is quasi-measure-preserving (Lebesgue measure is translation
invariant). -/
lemma qmp_sub_coord :
    Measure.QuasiMeasurePreserving
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => q.1 - q.2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  quasiMeasurePreserving_sub_of_right_invariant _ _

/-- **The relative coordinate `(u,x) ↦ xᵢ − xⱼ` is quasi-measure-preserving.** -/
lemma qmp_coordDiff {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N => p.2 i - p.2 j)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  qmp_sub_coord.comp ((qmp_pair_coord i j hij).comp Measure.quasiMeasurePreserving_snd)

/-- **The relative coordinate `((u,x),y) ↦ xᵢ − y` of the parametric `y`-integral is
quasi-measure-preserving.** -/
lemma qmp_coordDiff_prod {N : ℕ} (i : Fin N) :
    Measure.QuasiMeasurePreserving
      (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
          EuclideanSpace ℝ (Fin 3) => z.1.2 i - z.2)
      (((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  qmp_sub_coord.comp
    (MeasureTheory.QuasiMeasurePreserving.prodMap (qmp_coord i)
      (Measure.QuasiMeasurePreserving.id
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))))

/-! ## 2. Auxiliary continuity/measurability of the kernel factors -/

/-- `(u,x) ↦ χ_u(x)` is continuous (as a function of `(u,x) ∈ ℝ³ × X N`, at the slot `i`). -/
lemma continuous_chiU_slot {N : ℕ} (ℓ : ℝ) (i : Fin N) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      Submission.BoseGases.chiU ℓ p.1 (p.2 i)) := by
  have h : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      Submission.BoseGases.chi ((ℓ⁻¹) • (p.2 i) - p.1)) :=
    Submission.BoseGases.chi_continuous.comp (by fun_prop)
  simpa only [Submission.BoseGases.chiU] using h

/-- `((u,x),y) ↦ χ_u(x)` is continuous (as a function on the triple product, at the slot `i`). -/
lemma continuous_chiU_slot_prod {N : ℕ} (ℓ : ℝ) (i : Fin N) :
    Continuous (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
        EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiU ℓ z.1.1 (z.1.2 i)) := by
  have h : Continuous (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
      EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi ((ℓ⁻¹) • (z.1.2 i) - z.1.1)) :=
    Submission.BoseGases.chi_continuous.comp (by fun_prop)
  simpa only [Submission.BoseGases.chiU] using h

/-- `((u,x),y) ↦ χ_u(y)` is continuous on the triple product. -/
lemma continuous_chiU_snd_prod {N : ℕ} (ℓ : ℝ) :
    Continuous (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
        EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiU ℓ z.1.1 z.2) := by
  have h : Continuous (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
      EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi ((ℓ⁻¹) • z.2 - z.1.1)) :=
    Submission.BoseGases.chi_continuous.comp (by fun_prop)
  simpa only [Submission.BoseGases.chiU] using h

/-- The window factor `χ_u(xᵢ)` is a.e. strongly measurable on `ℝ³ × X N`. -/
lemma aestronglyMeasurable_chiU_slot {N : ℕ} (ℓ : ℝ) (i : Fin N) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        Submission.BoseGases.chiU ℓ p.1 (p.2 i))
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) :=
  (continuous_chiU_slot ℓ i).aestronglyMeasurable

/-- The window factor `χ_u(xᵢ)` is a.e. strongly measurable on the triple product. -/
lemma aestronglyMeasurable_chiU_slot_prod {N : ℕ} (ℓ : ℝ) (i : Fin N) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
          EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiU ℓ z.1.1 (z.1.2 i))
      (((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
  (continuous_chiU_slot_prod ℓ i).aestronglyMeasurable

/-- The window factor `χ_u(y)` is a.e. strongly measurable on the triple product. -/
lemma aestronglyMeasurable_chiU_snd_prod {N : ℕ} (ℓ : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
          EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiU ℓ z.1.1 z.2)
      (((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
  (continuous_chiU_snd_prod ℓ).aestronglyMeasurable

/-- The reciprocal scaling `(χ⋆χ)((xᵢ − xⱼ)/ℓ)⁻¹` is measurable. -/
lemma measurable_convScale_inv_slot {N : ℕ} (ℓ : ℝ) (i j : Fin N) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      (Submission.BoseGases.convScale ℓ (p.2 i - p.2 j))⁻¹) :=
  (by fun_prop : Measurable fun t : ℝ => t⁻¹).comp
    ((Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)).measurable

/-- The reciprocal scaling `(χ⋆χ)((xᵢ − y)/ℓ)⁻¹` is measurable on the triple product. -/
lemma measurable_convScale_inv_slot_prod {N : ℕ} (ℓ : ℝ) (i : Fin N) :
    Measurable (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
        EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.convScale ℓ (z.1.2 i - z.2))⁻¹) :=
  (by fun_prop : Measurable fun t : ℝ => t⁻¹).comp
    ((Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)).measurable

/-! ## 3. The two-body (pair) term -/

/-- **The pair kernel `(u,x) ↦ wLoc ℓ v u (xᵢ) (xⱼ)` is a.e. strongly measurable** for an
a.e. measurable one-body potential `v` and distinct labels `i ≠ j`. -/
lemma aestronglyMeasurable_wLoc_pair {N : ℕ} {ℓ : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : AEMeasurable v (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (i j : Fin N) (hij : i ≠ j) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        Submission.BoseGases.wLoc ℓ v p.1 (p.2 i) (p.2 j))
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) := by
  have hchi1 := aestronglyMeasurable_chiU_slot (N := N) ℓ i
  have hchi2 := aestronglyMeasurable_chiU_slot (N := N) ℓ j
  have hvij : AEMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N => v (p.2 i - p.2 j))
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) :=
    hv.comp_quasiMeasurePreserving (qmp_coordDiff i j hij)
  have hnum : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        v (p.2 i - p.2 j) / Submission.BoseGases.convScale ℓ (p.2 i - p.2 j))
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) :=
    (hvij.mul (measurable_convScale_inv_slot (N := N) ℓ i j).aemeasurable).aestronglyMeasurable
  refine MeasureTheory.AEStronglyMeasurable.congr ((hchi1.mul hnum).mul hchi2) ?_
  filter_upwards with p
  simp only [Pi.mul_apply, Submission.BoseGases.wLoc, Submission.BoseGases.wScaled]

/-! ## 4. The one-body term: the parametric `y`-integral -/

/-- **The triple-product integrand `((u,x),y) ↦ wLoc ℓ g u (xᵢ) y` is a.e. strongly
measurable** for an a.e. measurable one-body potential `g`. -/
lemma aestronglyMeasurable_wLoc_integrand {N : ℕ} {ℓ : ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : AEMeasurable g (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (i : Fin N) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
          EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.wLoc ℓ g z.1.1 (z.1.2 i) z.2)
      (((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
  have hchi1 := aestronglyMeasurable_chiU_slot_prod (N := N) ℓ i
  have hchi2 := aestronglyMeasurable_chiU_snd_prod (N := N) ℓ
  have hgsub : AEMeasurable
      (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
          EuclideanSpace ℝ (Fin 3) => g (z.1.2 i - z.2))
      (((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    hg.comp_quasiMeasurePreserving (qmp_coordDiff_prod i)
  have hnum : MeasureTheory.AEStronglyMeasurable
      (fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
          EuclideanSpace ℝ (Fin 3) =>
        g (z.1.2 i - z.2) / Submission.BoseGases.convScale ℓ (z.1.2 i - z.2))
      (((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    (hgsub.mul (measurable_convScale_inv_slot_prod (N := N) ℓ i).aemeasurable).aestronglyMeasurable
  refine MeasureTheory.AEStronglyMeasurable.congr ((hchi1.mul hnum).mul hchi2) ?_
  filter_upwards with p
  simp only [Pi.mul_apply, Submission.BoseGases.wLoc, Submission.BoseGases.wScaled]

/-- **The parametric integral `(u,x) ↦ ∫_y wLoc ℓ g u (xᵢ) y` is a.e. strongly measurable** for
an a.e. measurable `g` (no integrability of `g` is needed: the Bochner integral is `0` on the
non-integrable set and `AEStronglyMeasurable.integral_prod_right'` handles the convention). -/
lemma aestronglyMeasurable_wLoc_integral {N : ℕ} {ℓ : ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : AEMeasurable g (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (i : Fin N) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g p.1 (p.2 i) y)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) :=
  MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      (MeasureTheory.volume : Measure (Submission.BoseGases.X N)))
    (f := fun z : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N) ×
        EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wLoc ℓ g z.1.1 (z.1.2 i) z.2)
    (aestronglyMeasurable_wLoc_integrand (N := N) (ℓ := ℓ) hg i)

/-! ## 5. The weighted potential word -/

theorem aestronglyMeasurable_potWordU_weight {N : ℕ} {ℓ μ : ℝ}
    {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : AEMeasurable v MeasureTheory.volume) (hg : AEMeasurable g MeasureTheory.volume)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        (Φ p.2) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ p.1 p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- the one-body part `Σᵢ ∫_y wLoc ℓ g u (xᵢ) y`
  have hsumI : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        ∑ i : Fin N, ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wLoc ℓ g p.1 (p.2 i) y)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) := by
    refine MeasureTheory.AEStronglyMeasurable.congr
      (Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin N))
        (fun i _ => aestronglyMeasurable_wLoc_integral (N := N) (ℓ := ℓ) hg i)) ?_
    filter_upwards with p
    simp only [Finset.sum_apply]
  have hA : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        -μ * ∑ i : Fin N, ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wLoc ℓ g p.1 (p.2 i) y)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) :=
    hsumI.const_mul (-μ)
  -- the two-body part `Σ_{i<j} wLoc ℓ v u (xᵢ) (xⱼ)`
  have hB : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v p.1 (p.2 ij.1.1) (p.2 ij.1.2))
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) := by
    refine MeasureTheory.AEStronglyMeasurable.congr
      (Finset.aestronglyMeasurable_sum (Finset.univ : Finset {ij : Fin N × Fin N | ij.1 < ij.2})
        (fun ij _ => aestronglyMeasurable_wLoc_pair (N := N) (ℓ := ℓ) hv ij.1.1 ij.1.2
          (ne_of_lt ij.2))) ?_
    filter_upwards with p
    simp only [Finset.sum_apply]
  -- `potWordU` is the sum of the two parts
  have hpot : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        Work.BoseKinLoc.potWordU N v g ℓ μ p.1 p.2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) := by
    refine MeasureTheory.AEStronglyMeasurable.congr (hA.add hB) ?_
    filter_upwards with p
    simp only [Pi.add_apply, Work.BoseKinLoc.potWordU]
  -- the continuous weight `Φ²`
  have hsq : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N => (Φ p.2) ^ 2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : Measure (Submission.BoseGases.X N))) :=
    ((hΦ.comp continuous_snd).aestronglyMeasurable).pow 2
  refine MeasureTheory.AEStronglyMeasurable.congr (hsq.mul hpot) ?_
  filter_upwards with p
  simp only [Pi.mul_apply]

end Work.BoseFixGlue.Pot
