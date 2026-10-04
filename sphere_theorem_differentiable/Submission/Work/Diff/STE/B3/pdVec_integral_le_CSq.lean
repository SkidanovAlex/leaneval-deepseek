import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.fourierCoeff_pdVec_normSq
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.ENormSq_seriesFun_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pdVec_integral_le_CSq`: the physical `Hᵐ` energy is bounded by the coefficient weight

Layer B3 of the STE torus development.  For every `s : ℕ` there is a constant `C` with

  `∫_{unitCube} ‖∂^{l} u‖² ≤ C · CSq s (fourierCoeff u)`

for every `1`-periodic `C^∞` function `u` on `(ι → ℝ)`, every `m ≤ s` and every list of
directions `l : Fin m → ι` (repetitions allowed).  This is the "Sobolev comparison" in the
direction *opposite* to `CSq_le_ENormSq` (which bounds the coefficient norm by the physical
energy): here the physical energy of the derivatives is bounded by the weighted coefficient
norm.  The constant is explicit, `C = (2π)^{2s}`, and depends neither on `u` nor on `m` nor on
`l`.

## Proof

Three ingredients, all already available in Layer A/B3.

* **Parseval/Fourier inversion on the cube** (`integral_normSq_eq_tsum_fourierCoeff`): for a *continuous* `g` one has
  `∫_{unitCube} ‖g‖² = Σ_k ‖ĝ(k)‖²`.  This is Mathlib's Parseval identity
  `UnitAddTorus.hasSum_sq_mFourierCoeff` on the additive torus, transported to the cube along the
  measure preserving `Ioc`-representative map `measurePreserving_rep`.  (Bessel's inequality,
  proved as `bessel_continuous`, gives only the reverse inequality, so this step is genuinely
  needed; note that it uses *equality*, i.e. completeness of the characters.)
  Mathlib's torus statement is phrased for the `MeasureSpace` instance carried by
  `UnitAddCircle`; the local instance `instMSUnitAddCircleSte` below (the same device as in
  `summable_weighted_fourierCoeff_of_contDiff`) makes it match the `Pi`-instance volume of
  `UnitAddTorus`.
* **The Fourier multiplier of an iterated derivative**
  (`fourierCoeff_pdVec_normSq`): `‖∂^{l}u^(k)‖² = (∏_i (2π k_{l i})²) ‖û(k)‖²`.
* **The weight comparison** (`prod_weight_le`): for `m ≤ s` and any `l : Fin m → ι`,
  `∏_i (2π k_{l i})² ≤ (2π)^{2s} ⟨k⟩^{2s}`; each factor is at most `(2π)²⟨k⟩²` because
  `k_j² ≤ ⟨k⟩²`, and then one uses `⟨k⟩ ≥ 1` and `2π ≥ 1`.
  Everything is then a termwise comparison of summable nonnegative families, summed with
  `Summable.tsum_le_tsum`; the summability of the right-hand side is
  `summable_weighted_fourierCoeff_of_contDiff` (which needs `u` periodic and `C^∞`).
-/

open MeasureTheory

namespace Work.Diff.STE.B3

open MeasureTheory BigOperators

variable {ι : Type*}

/-! ## The weight comparison -/

/-- **The multiplier weight is dominated by the `CSq` weight.**  For `m ≤ s`, any list of
directions `l : Fin m → ι` and any frequency `k : ι → ℤ`,

  `∏ i, (2π k_{l i})² ≤ (2π)^{2s} ⟨k⟩^{2s}`.

Indeed each factor is bounded by `(2π)²⟨k⟩²` (as `k_j² ≤ ⟨k⟩²`), the product of `m` copies of
this bound is `((2π)²⟨k⟩²)^m = (2π)^{2m} ⟨k⟩^{2m}`, and both factors are then increased to the
exponent `s` using `⟨k⟩ ≥ 1` and `2π ≥ 1`. -/
lemma prod_weight_le [Fintype ι] [DecidableEq ι] {m s : ℕ} (hm : m ≤ s)
    (l : Fin m → ι) (k : ι → ℤ) :
    (∏ i : Fin m, (2 * Real.pi * ((k (l i) : ℤ) : ℝ)) ^ 2)
      ≤ (2 * Real.pi) ^ (2 * s) * (wt k) ^ s := by
  have hfac : ∀ i : Fin m,
      (2 * Real.pi * ((k (l i) : ℤ) : ℝ)) ^ 2 ≤ (2 * Real.pi) ^ 2 * wt k := by
    intro i
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (sq_le_wt k (l i)) (sq_nonneg _)
  have hprod : (∏ i : Fin m, (2 * Real.pi * ((k (l i) : ℤ) : ℝ)) ^ 2)
      ≤ ((2 * Real.pi) ^ 2 * wt k) ^ m := by
    calc (∏ i : Fin m, (2 * Real.pi * ((k (l i) : ℤ) : ℝ)) ^ 2)
        ≤ ∏ _i : Fin m, ((2 * Real.pi) ^ 2 * wt k) :=
          Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hfac i)
      _ = ((2 * Real.pi) ^ 2 * wt k) ^ m := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod' : (∏ i : Fin m, (2 * Real.pi * ((k (l i) : ℤ) : ℝ)) ^ 2)
      ≤ (2 * Real.pi) ^ (2 * m) * (wt k) ^ m := by
    rw [mul_pow, ← pow_mul] at hprod
    exact hprod
  have h1 : (2 * Real.pi) ^ (2 * m) ≤ (2 * Real.pi) ^ (2 * s) :=
    pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) (by omega)
  have h2 : (wt k) ^ m ≤ (wt k) ^ s := pow_le_pow_right₀ (wt_one_le k) hm
  exact hprod'.trans (mul_le_mul h1 h2 (pow_nonneg (le_of_lt (wt_pos k)) m)
    (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) _))

/-! ## Parseval on the cube -/

section ParsevalCube

/-- The `MeasureSpace` structure on `UnitAddCircle` used by Mathlib's multivariate torus Fourier
theory, with volume the Haar *probability* measure.  It is needed to speak about
`UnitAddTorus.hasSum_sq_mFourierCoeff` in a file whose `Pi`-instance volume on `UnitAddTorus` uses
the canonical measure-space instance of `AddCircle 1`.  Declared in a section so that it does not
influence the elaboration of anything outside. -/
noncomputable local instance instMSUnitAddCircleSte : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- **Parseval on the unit cube.**  For a continuous function `g` on `(ι → ℝ)`,

  `∫_{unitCube} ‖g‖² = Σ_k ‖ĝ(k)‖²`.

This is the equality counterpart of Bessel's inequality `bessel_continuous`; it is deduced from
Mathlib's Parseval identity on the additive torus `UnitAddTorus ι`, transported to the cube along
the measure preserving `Ioc`-representative map `measurePreserving_rep`. -/
lemma integral_normSq_eq_tsum_fourierCoeff [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℂ) (hg : Continuous g) :
    (∫ x in unitCube (ι := ι), ‖g x‖ ^ 2)
      = ∑' k : ι → ℤ, ‖fourierCoeff g k‖ ^ 2 := by
  classical
  set rep : UnitAddTorus ι → (ι → ℝ) := fun t i => (AddCircle.equivIoc 1 0 (t i)).1 with hrep
  set G : UnitAddTorus ι → ℂ := fun t => g (rep t) with hGdef
  -- the volume on `UnitAddTorus` is the product of the Haar measures
  have hvol : (volume : Measure (UnitAddTorus ι))
      = Measure.pi (fun _ : ι => AddCircle.haarAddCircle) := by
    rw [MeasureTheory.volume_pi]
    rfl
  have hGpi : MemLp G 2 (Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) := by
    rw [hGdef]
    exact memLp_comp_rep (ste_memLp_of_continuous hg)
  have hG : MemLp G 2 (volume : Measure (UnitAddTorus ι)) := hvol.symm ▸ hGpi
  set u : Lp ℂ 2 (volume : Measure (UnitAddTorus ι)) := hG.toLp G with hudef
  -- Parseval on the torus
  have hparse : HasSum (fun k : ι → ℤ =>
      ‖UnitAddTorus.mFourierCoeff (u : UnitAddTorus ι → ℂ) k‖ ^ 2)
      (∫ t, ‖(u : UnitAddTorus ι → ℂ) t‖ ^ 2) := UnitAddTorus.hasSum_sq_mFourierCoeff u
  -- the torus coefficients are the cube coefficients
  have hGfun : G = fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1) := by
    rw [hGdef]
  have hcoef : ∀ k : ι → ℤ,
      UnitAddTorus.mFourierCoeff (u : UnitAddTorus ι → ℂ) k = fourierCoeff g k := by
    intro k
    have h1 : UnitAddTorus.mFourierCoeff (u : UnitAddTorus ι → ℂ) k
        = UnitAddTorus.mFourierCoeff G k := by
      rw [hudef]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hG] with t ht
      rw [ht]
    rw [h1, hGfun, ste_mFourierCoeff_lift g k]
  -- the torus integral is the cube integral
  have h1 : (∫ t, ‖(u : UnitAddTorus ι → ℂ) t‖ ^ 2 ∂(volume : Measure (UnitAddTorus ι)))
      = ∫ t, ‖G t‖ ^ 2 ∂(volume : Measure (UnitAddTorus ι)) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hG] with t ht
    rw [ht]
  have h2 : (∫ t, ‖G t‖ ^ 2 ∂(volume : Measure (UnitAddTorus ι)))
      = ∫ t, ‖G t‖ ^ 2 ∂(Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) := by
    rw [hvol]
  have hmap : Measure.map rep (Measure.pi (fun _ : ι => AddCircle.haarAddCircle))
      = volume.restrict (unitCube (ι := ι)) :=
    MeasureTheory.MeasurePreserving.map_eq measurePreserving_rep
  have h3 : (∫ t, ‖G t‖ ^ 2 ∂(Measure.pi (fun _ : ι => AddCircle.haarAddCircle)))
      = ∫ x in unitCube (ι := ι), ‖g x‖ ^ 2 := by
    have hmeas : AEMeasurable rep (Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) :=
      measurePreserving_rep.measurable.aemeasurable
    have hsm : AEStronglyMeasurable (fun x : ι → ℝ => ‖g x‖ ^ 2)
        (Measure.map rep (Measure.pi (fun _ : ι => AddCircle.haarAddCircle))) := by
      rw [hmap]
      exact (hg.norm.pow 2).aestronglyMeasurable
    calc ∫ t, ‖G t‖ ^ 2 ∂(Measure.pi (fun _ : ι => AddCircle.haarAddCircle))
        = ∫ t, ‖g (rep t)‖ ^ 2 ∂(Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) := by
          rw [hGdef]
      _ = ∫ x, ‖g x‖ ^ 2 ∂(Measure.map rep (Measure.pi (fun _ : ι => AddCircle.haarAddCircle))) :=
          (MeasureTheory.integral_map hmeas hsm).symm
      _ = ∫ x, ‖g x‖ ^ 2 ∂(volume.restrict (unitCube (ι := ι))) := by rw [hmap]
      _ = ∫ x in unitCube (ι := ι), ‖g x‖ ^ 2 := rfl
  calc (∫ x in unitCube (ι := ι), ‖g x‖ ^ 2)
      = ∫ t, ‖(u : UnitAddTorus ι → ℂ) t‖ ^ 2 ∂(volume : Measure (UnitAddTorus ι)) :=
        (h1.trans (h2.trans h3)).symm
    _ = ∑' k : ι → ℤ, ‖UnitAddTorus.mFourierCoeff (u : UnitAddTorus ι → ℂ) k‖ ^ 2 :=
        hparse.tsum_eq.symm
    _ = ∑' k : ι → ℤ, ‖fourierCoeff g k‖ ^ 2 :=
        tsum_congr (fun k => by rw [hcoef k])

end ParsevalCube

/-! ## The target -/

theorem pdVec_integral_le_CSq {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (ι → ℝ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u → Work.Diff.STE.Periodic1 u →
      ∀ (m : ℕ) (hm : m ≤ s) (l : Fin m → ι),
        ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec m l u x‖ ^ 2
          ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u) := by
  refine ⟨(2 * Real.pi) ^ (2 * s), by positivity, ?_⟩
  intro u hu hper m hm l
  -- the hypothesis is the `C^∞` level, written as `↑⊤ : WithTop ℕ∞`
  have hu' : ContDiff ℝ (⊤ : ℕ∞) u := hu
  have hsmooth : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) u := fun n => hu'.of_le (by simp)
  -- summability of the weighted coefficient family
  have hsum : Summable (fun k : ι → ℤ => wt k ^ s * ‖fourierCoeff u k‖ ^ 2) :=
    summable_weighted_fourierCoeff_of_contDiff u hu' hper s
  -- the derivative is continuous, so Parseval applies to it
  have hcont : Continuous (pdVec m l u) := continuous_pdVec m l u (hsmooth m)
  have hparse := integral_normSq_eq_tsum_fourierCoeff (pdVec m l u) hcont
  have hpsumm : Summable (fun k : ι → ℤ => ‖fourierCoeff (pdVec m l u) k‖ ^ 2) :=
    ste_summable_sq_fourierCoeff (pdVec m l u) (ste_memLp_of_continuous hcont)
  -- the pointwise comparison of the coefficients
  have hle : ∀ k : ι → ℤ, ‖fourierCoeff (pdVec m l u) k‖ ^ 2
      ≤ (2 * Real.pi) ^ (2 * s) * (wt k ^ s * ‖fourierCoeff u k‖ ^ 2) := by
    intro k
    rw [fourierCoeff_pdVec_normSq m l u (hsmooth m) hper k]
    calc (∏ i : Fin m, (2 * Real.pi * ((k (l i) : ℤ) : ℝ)) ^ 2)
            * ‖fourierCoeff u k‖ ^ 2
        ≤ ((2 * Real.pi) ^ (2 * s) * wt k ^ s) * ‖fourierCoeff u k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (prod_weight_le hm l k) (sq_nonneg _)
      _ = (2 * Real.pi) ^ (2 * s) * (wt k ^ s * ‖fourierCoeff u k‖ ^ 2) := by ring
  calc ∫ x in unitCube (ι := ι), ‖pdVec m l u x‖ ^ 2
      = ∑' k : ι → ℤ, ‖fourierCoeff (pdVec m l u) k‖ ^ 2 := hparse
    _ ≤ ∑' k : ι → ℤ, (2 * Real.pi) ^ (2 * s) * (wt k ^ s * ‖fourierCoeff u k‖ ^ 2) :=
        Summable.tsum_le_tsum hle hpsumm (hsum.mul_left _)
    _ = (2 * Real.pi) ^ (2 * s) * CSq s (fourierCoeff u) := by
        rw [CSq, tsum_mul_left]

end Work.Diff.STE.B3
