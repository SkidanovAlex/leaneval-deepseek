import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integrableOn_pairDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integrableOn_imgKernel_slots`

Integrability, over the centred `n`-particle box `abox n ℓ`, of the integrand

    `x ↦ F x * |imgKernel ℓ W (x i) (x j)|`

for a continuous `F`, distinct slots `i ≠ j`, and an *integrable* potential `W` supported in
`ball 0 R` with `R ≤ ℓ/2`.

The proof combines

* the flatness/`L¹` bound `imgKernel_abs_le_finsum`
  (`|imgKernel ℓ W x y| ≤ chiImgC K (R/ℓ)^K Σ_{m ∈ latImgSet} |W (x - y + ℓ•m)|`, a *finite* sum
  of `26` terms), and
* the fact that each `x ↦ |W (x i - x j + c)|` is integrable on `abox n ℓ`
  (`integrableOn_coordDiff`, from the box-restricted Fubini lemma `integrableOn_pairDiff`),
  together with
* a.e.-strong measurability of the pullback `x ↦ W (x i - x j + c)` (`AEMeasurable.tsum`, applied
  to the lattice sum defining `imgKernel`).

Everything is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X

/-- **Integrability of a shifted coordinate difference over the box.**  For an integrable
`S : ℝ³ → ℝ`, any shift `c`, and distinct slots `i ≠ j`, the pullback
`x ↦ S (x i - x j + c)` is integrable on the centred box `abox N ℓ`.

(The case `N ≥ 2` is reduced to `N = p + 2` and then to the box-restricted Fubini lemma
`integrableOn_pairDiff` via the corpus measure-preserving insertion `integrableOn_pair_comp_ae`.) -/
theorem integrableOn_coordDiff {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {S : EuclideanSpace ℝ (Fin 3) → ℝ} (hS : MeasureTheory.Integrable S)
    (c : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn (fun x : Xn N => S (x i - x j + c)) (Submission.BoseGases.abox N ℓ) := by
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have h2 : 2 ≤ N := by
    by_contra h
    push Not at h
    exact hij' (by omega)
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, N = p + 2 := ⟨N - 2, by omega⟩
  exact Submission.BoseGases.integrableOn_pair_comp_ae (p := p) hℓ i j hij
    (integrableOn_pairDiff hℓ hS c)

/-- A.e.-strong measurability of the pullback `x ↦ W (x i - x j + c)` on the box, for an
integrable `W`. -/
theorem aemeasurable_coordDiff {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (c : EuclideanSpace ℝ (Fin 3)) :
    AEMeasurable (fun x : Xn N => W (x i - x j + c))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
  (integrableOn_coordDiff hℓ hij hW c).aestronglyMeasurable.aemeasurable

/-- **A.e.-strong measurability of the images kernel on the box** (as a function of the
configuration), i.e. of `x ↦ imgKernel ℓ W (x i) (x j)`.

The lattice sum defining `imgKernel` is an a.e.-measurable function of `x` because every one of its
terms is (`AEMeasurable.tsum`), and the two `χ`-factors are continuous. -/
theorem aestronglyMeasurable_imgKernel_slots {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n}
    (hij : i ≠ j) {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W) :
    AEStronglyMeasurable (fun x : Xn n =>
        Submission.BoseGases.chiScale ℓ (x i)
          * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℝ) else W (x i - x j + ℓ • latVec m))
          * Submission.BoseGases.chiScale ℓ (x j))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
  have htsum : AEMeasurable (fun x : Xn n =>
      ∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℝ) else W (x i - x j + ℓ • latVec m))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    apply AEMeasurable.tsum
    intro m
    by_cases hm : m = 0
    · simp only [hm, ↓reduceIte]
      exact aemeasurable_const
    · simp only [hm, ↓reduceIte]
      exact aemeasurable_coordDiff hℓ hij hW (ℓ • latVec m)
  have hi : AEStronglyMeasurable
      (fun x : Xn n => Submission.BoseGases.chiScale ℓ (x i))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).aestronglyMeasurable
  have hj : AEStronglyMeasurable
      (fun x : Xn n => Submission.BoseGases.chiScale ℓ (x j))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j)).aestronglyMeasurable
  exact (hi.mul htsum.aestronglyMeasurable).mul hj

/-- `imgKernel` form of `aestronglyMeasurable_imgKernel_slots`. -/
theorem aestronglyMeasurable_imgKernel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n}
    (hij : i ≠ j) {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W) :
    AEStronglyMeasurable (fun x : Fin n → EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.imgKernel ℓ W (x i) (x j))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
  simpa only [imgKernel] using aestronglyMeasurable_imgKernel_slots hℓ hij hW

/-- **Integrability of `|imgKernel|` over the box.**  Combining the flatness bound
`imgKernel_abs_le_finsum` with the integrability of the `26` finite-summands. -/
theorem integrableOn_imgKernel_abs_slots {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {i j : Fin n}
    (hij : i ≠ j) {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hR : 0 ≤ R) (hRℓ : R ≤ ℓ / 2)
    (hWs : ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ → W u = 0) :
    MeasureTheory.IntegrableOn (fun x : Xn n => |imgKernel ℓ W (x i) (x j)|)
      (Submission.BoseGases.abox n ℓ) := by
  have hWabs : MeasureTheory.Integrable (fun z : E3 => |W z|) := by
    simpa only [Real.norm_eq_abs] using hWi.abs
  have hInt_m : ∀ m : Fin 3 → ℤ, MeasureTheory.Integrable
      (fun x : Xn n => |W (x i - x j + ℓ • latVec m)|)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    fun m => integrableOn_coordDiff hℓ hij hWabs (ℓ • latVec m)
  have hsum : MeasureTheory.Integrable
      (fun x : Xn n => ∑ m ∈ latImgSet, |W (x i - x j + ℓ • latVec m)|)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    integrable_finsetSum latImgSet (fun m _ => hInt_m m)
  have hmaj : MeasureTheory.Integrable
      (fun x : Xn n => chiImgC 0 * (1 : ℝ) * ∑ m ∈ latImgSet, |W (x i - x j + ℓ • latVec m)|)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    hsum.const_mul _
  have hbound : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      ‖|imgKernel ℓ W (x i) (x j)|‖
        ≤ chiImgC 0 * (1 : ℝ) * ∑ m ∈ latImgSet, |W (x i - x j + ℓ • latVec m)| := by
    apply ae_of_all
    intro x
    have hmain := imgKernel_abs_le_finsum hℓ hR hRℓ 0 hWs (x i) (x j)
    simpa only [Real.norm_eq_abs, abs_abs, pow_zero, mul_one] using hmain
  exact Integrable.mono' hmaj
    (by simpa only [Real.norm_eq_abs] using (aestronglyMeasurable_imgKernel hℓ hij hWi).norm)
    hbound

theorem integrableOn_imgKernel_slots {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hR : 0 ≤ R) (hRℓ : R ≤ ℓ / 2) (hWs : ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ → W u = 0)
    (F : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℝ) (hF : Continuous F) :
    MeasureTheory.IntegrableOn (fun x : Fin n → EuclideanSpace ℝ (Fin 3) =>
      F x * |Work.BoseBoxFock.imgKernel ℓ W (x i) (x j)|) (Submission.BoseGases.abox n ℓ) := by
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := F) hF.continuousOn
  have hB' : ∀ x ∈ Submission.BoseGases.abox n ℓ, |F x| ≤ max B 0 := by
    intro x hx
    have h1 := hB x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  have habs : MeasureTheory.Integrable
      (fun x : Xn n => |imgKernel ℓ W (x i) (x j)|)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    integrableOn_imgKernel_abs_slots hℓ hij hWi hR hRℓ hWs
  have hmaj : MeasureTheory.Integrable
      (fun x : Xn n => max B 0 * |imgKernel ℓ W (x i) (x j)|)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    habs.const_mul _
  have hAESM : AEStronglyMeasurable
      (fun x : Xn n => F x * |imgKernel ℓ W (x i) (x j)|)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    hF.measurable.aestronglyMeasurable.mul habs.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      ‖F x * |imgKernel ℓ W (x i) (x j)|‖ ≤ max B 0 * |imgKernel ℓ W (x i) (x j)| := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    apply ae_of_all
    intro x hx
    rw [Real.norm_eq_abs, abs_mul, abs_abs]
    exact mul_le_mul_of_nonneg_right (hB' x hx) (abs_nonneg _)
  exact Integrable.mono' hmaj hAESM hbound

end Work.BoseBoxFock
