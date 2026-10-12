import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU`

A.e. strong measurability of the localised potential word `x ↦ potWordU N v g ℓ μ u x`
on the configuration space `X N = Fin N → ℝ³`, for the numerators `v, g` only
*a.e. strongly measurable* with respect to Lebesgue measure on `ℝ³`.

The word (FS `eq:Def_HB`, multiplicative part) is

    `potWordU N v g ℓ μ u x = -μ * Σᵢ ∫_y wLoc ℓ g u (xᵢ) y + Σ_{i<j} wLoc ℓ v u (xᵢ) (xⱼ)`,

with the localisation kernel `wLoc ℓ h u x y = χ_u(x) · h(x−y)/(χ⋆χ)((x−y)/ℓ) · χ_u(y)`
(FS `wPair`/`wScaled`).  Since `u` is *fixed* here (unlike
`Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight`, which treats `(u,x)` and then
still has to multiply by a continuous weight `Φ²`), the two mathematical inputs are:

* `x ↦ xᵢ − xⱼ` and `(x,y) ↦ xᵢ − y` are quasi-measure-preserving for Lebesgue measure
  (the corpus' `qmp_pair_coord`, `qmp_sub_coord`, and Mathlib's
  `Measure.quasiMeasurePreserving_eval`), so the *a.e.* measurable numerators `v`, `g` may
  be composed with them (`AEMeasurable.comp_quasiMeasurePreserving`);
* `χ_u` is continuous and `(χ⋆χ)((·)/ℓ)⁻¹` is measurable, and the parametric `y`-integral
  is a.e. strongly measurable with no integrability hypothesis
  (`AEStronglyMeasurable.integral_prod_right'`).

Everything closes under pointwise products and finite sums.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB2.Pot

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Quasi-measure-preserving coordinate maps -/

/-- A single coordinate of `X N = Fin N → ℝ³` is quasi-measure-preserving for Lebesgue
measure (i.e. for the product measure, by `volume_pi`). -/
lemma qmp_coord_X {N : ℕ} (i : Fin N) :
    Measure.QuasiMeasurePreserving (fun x : Submission.BoseGases.X N => x i)
      (MeasureTheory.volume : Measure (Submission.BoseGases.X N))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have h := Measure.quasiMeasurePreserving_eval
    (fun _ : Fin N => (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) i
  rw [← MeasureTheory.volume_pi] at h
  exact h

/-- The relative coordinate `x ↦ xᵢ − xⱼ` on `X N` is quasi-measure-preserving. -/
lemma qmp_coordDiff_X {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Measure.QuasiMeasurePreserving (fun x : Submission.BoseGases.X N => x i - x j)
      (MeasureTheory.volume : Measure (Submission.BoseGases.X N))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  Work.BoseFixGlue.Pot.qmp_sub_coord.comp (Work.BoseFixGlue.Pot.qmp_pair_coord i j hij)

/-- The relative coordinate `(x,y) ↦ xᵢ − y` on `X N × ℝ³` is quasi-measure-preserving. -/
lemma qmp_coord_prod {N : ℕ} (i : Fin N) :
    Measure.QuasiMeasurePreserving
      (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) => p.1 i - p.2)
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have h := Work.BoseFixGlue.Pot.qmp_sub_coord.comp
    (MeasureTheory.QuasiMeasurePreserving.prodMap (qmp_coord_X i)
      (Measure.QuasiMeasurePreserving.id (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))))
  convert h using 1
  funext p
  obtain ⟨a, b⟩ := p
  rfl

/-! ## 2. The two-body (pair) term -/

/-- **The pair kernel `x ↦ wLoc ℓ v u (xᵢ) (xⱼ)` is a.e. strongly measurable** for an
a.e. strongly measurable numerator `v` and distinct labels `i ≠ j`. -/
lemma aesm_wLoc_pair_X {N : ℕ} {ℓ : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : AEStronglyMeasurable v (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (i j : Fin N) (hij : i ≠ j) :
    AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.wLoc ℓ v u (x i) (x j))
      (volume : Measure (Submission.BoseGases.X N)) := by
  have hchi1 : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.chiU ℓ u (x i))
      (volume : Measure (Submission.BoseGases.X N)) := by
    have h : Continuous (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.chi ((ℓ⁻¹) • (x i) - u)) :=
      Submission.BoseGases.chi_continuous.comp (by fun_prop)
    simpa only [Submission.BoseGases.chiU] using h.aestronglyMeasurable
  have hchi2 : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.chiU ℓ u (x j))
      (volume : Measure (Submission.BoseGases.X N)) := by
    have h : Continuous (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.chi ((ℓ⁻¹) • (x j) - u)) :=
      Submission.BoseGases.chi_continuous.comp (by fun_prop)
    simpa only [Submission.BoseGases.chiU] using h.aestronglyMeasurable
  have hvij : AEMeasurable (fun x : Submission.BoseGases.X N => v (x i - x j))
      (volume : Measure (Submission.BoseGases.X N)) :=
    hv.aemeasurable.comp_quasiMeasurePreserving (qmp_coordDiff_X i j hij)
  have hinv : Measurable
      (fun x : Submission.BoseGases.X N => (Submission.BoseGases.convScale ℓ (x i - x j))⁻¹) :=
    measurable_inv.comp ((Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)).measurable
  refine AEStronglyMeasurable.congr
    (((hchi1.mul ((hvij.mul hinv.aemeasurable).aestronglyMeasurable))).mul hchi2) ?_
  filter_upwards with x
  simp only [Pi.mul_apply, Submission.BoseGases.wLoc, Submission.BoseGases.wScaled, div_eq_mul_inv]

/-! ## 3. The one-body term: the parametric `y`-integral -/

/-- **The integrand `(x,y) ↦ wLoc ℓ g u (xᵢ) y` is a.e. strongly measurable** for an
a.e. strongly measurable numerator `g`, on `X N × ℝ³`. -/
lemma aesm_wLoc_integrand_X {N : ℕ} {ℓ : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure (EuclideanSpace ℝ (Fin 3)))) (i : Fin N) :
    AEStronglyMeasurable
      (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wLoc ℓ g u (p.1 i) p.2)
      ((volume : Measure (Submission.BoseGases.X N)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
  have hchi1 : AEStronglyMeasurable
      (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiU ℓ u (p.1 i))
      ((volume : Measure (Submission.BoseGases.X N)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h : Continuous (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chi ((ℓ⁻¹) • (p.1 i) - u)) :=
      Submission.BoseGases.chi_continuous.comp (by fun_prop)
    simpa only [Submission.BoseGases.chiU] using h.aestronglyMeasurable
  have hchi2 : AEStronglyMeasurable
      (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiU ℓ u p.2)
      ((volume : Measure (Submission.BoseGases.X N)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h : Continuous (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chi ((ℓ⁻¹) • p.2 - u)) :=
      Submission.BoseGases.chi_continuous.comp (by fun_prop)
    simpa only [Submission.BoseGases.chiU] using h.aestronglyMeasurable
  have hgp : AEMeasurable
      (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) => g (p.1 i - p.2))
      ((volume : Measure (Submission.BoseGases.X N)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    hg.aemeasurable.comp_quasiMeasurePreserving (qmp_coord_prod i)
  have hinv : Measurable
      (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.convScale ℓ (p.1 i - p.2))⁻¹) :=
    measurable_inv.comp ((Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)).measurable
  refine AEStronglyMeasurable.congr
    (((hchi1.mul ((hgp.mul hinv.aemeasurable).aestronglyMeasurable))).mul hchi2) ?_
  filter_upwards with p
  simp only [Pi.mul_apply, Submission.BoseGases.wLoc, Submission.BoseGases.wScaled, div_eq_mul_inv]

/-- **The parametric integral `x ↦ ∫_y wLoc ℓ g u (xᵢ) y` is a.e. strongly measurable** for
an a.e. strongly measurable `g`; no integrability of `g` is assumed (the Bochner integral
is `0` on the non-integrable set, which `integral_prod_right'` handles). -/
lemma aesm_wLoc_integral_X {N : ℕ} {ℓ : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure (EuclideanSpace ℝ (Fin 3)))) (i : Fin N) :
    AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N =>
        ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g u (x i) y)
      (volume : Measure (Submission.BoseGases.X N)) :=
  AEStronglyMeasurable.integral_prod_right' (aesm_wLoc_integrand_X hg i)

/-! ## 4. The target -/

theorem aestronglyMeasurable_potWordU {N : ℕ} {ℓ μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : MeasureTheory.AEStronglyMeasurable v (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hg : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Work.BoseKinLoc.potWordU N v g ℓ μ u x)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)) := by
  -- the one-body part `Σᵢ ∫_y wLoc ℓ g u (xᵢ) y`
  have hsumI : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N =>
        ∑ i : Fin N, ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g u (x i) y)
      (MeasureTheory.volume : Measure (Submission.BoseGases.X N)) := by
    refine AEStronglyMeasurable.congr
      (Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin N))
        (fun i _ => aesm_wLoc_integral_X (ℓ := ℓ) (u := u) hg i)) ?_
    filter_upwards with x
    simp only [Finset.sum_apply]
  have hA : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N =>
        -μ * ∑ i : Fin N, ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g u (x i) y)
      (MeasureTheory.volume : Measure (Submission.BoseGases.X N)) :=
    hsumI.const_mul (-μ)
  -- the two-body part `Σ_{i<j} wLoc ℓ v u (xᵢ) (xⱼ)`
  have hsumB : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N =>
        ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2))
      (MeasureTheory.volume : Measure (Submission.BoseGases.X N)) := by
    refine AEStronglyMeasurable.congr
      (Finset.aestronglyMeasurable_sum (Finset.univ : Finset {ij : Fin N × Fin N | ij.1 < ij.2})
        (fun ij _ => aesm_wLoc_pair_X (ℓ := ℓ) (u := u) hv ij.1.1 ij.1.2 (ne_of_lt ij.2))) ?_
    filter_upwards with x
    simp only [Finset.sum_apply]
  -- `potWordU` is the sum of the two parts
  refine AEStronglyMeasurable.congr (hA.add hsumB) ?_
  filter_upwards with x
  simp only [Pi.add_apply, Work.BoseKinLoc.potWordU]

end Work.BoseFixB2.Pot
