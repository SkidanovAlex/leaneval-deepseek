import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.norm_sq_Lp_eq_integral
import Submission.Work.Diff.STE.mFourier_mk_eq_fourierExp
import Submission.Work.Diff.STE.integral_pullback_norm_sq
import Submission.Work.Diff.STE.coeFn_sum_mFourierLp
import Submission.Work.Diff.STE.aestronglyMeasurable_of_norm_sq_sub
import Submission.Work.Diff.STE.memLp_comp_rep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Density of the trigonometric polynomials in `L²` on the unit cube

`trigPoly_dense_L2`: every `f : (ι → ℝ) → ℂ` that is square integrable on the half open unit
cube `unitCube = (0,1]^ι` is approximated in the `L²` sense by a finite complex linear
combination of the characters `fourierExp k = exp (2πi k·x)`, `k : ι → ℤ`.

The argument goes through the compact torus `UnitAddTorus ι = (ℝ/ℤ)^ι`: the coordinatewise
`Ioc`-representative map identifies the torus with the cube up to a null set and is measure
preserving, so `f` pulls back to an `L²` function on the torus; there Mathlib's
`UnitAddTorus.span_mFourierLp_closure_eq_top` (Stone–Weierstrass + density of continuous
functions in `Lᵖ`) provides a finite combination of the characters close to the pullback, and
everything is transported back to the cube.

If `f` is not a.e. strongly measurable there is nothing to transport: then one of the
integrands `‖f - 1‖²`, `‖f - I‖²` fails to be a.e. strongly measurable, hence is not
integrable, so the corresponding integral vanishes; this is the content of
`aestronglyMeasurable_of_norm_sq_sub`.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate ENNReal

/-- The torus is equipped with the normalised Haar (probability) measure, as in Mathlib's
multivariate Fourier theory. -/
noncomputable local instance instMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Haar probability measure on the unit torus `(ℝ/ℤ)^ι`, as a product measure. -/
noncomputable abbrev torusMeasure (ι : Type*) [Fintype ι] : Measure (UnitAddTorus ι) :=
  Measure.pi (fun _ : ι => AddCircle.haarAddCircle)

/-- Lebesgue measure restricted to the half open unit cube. -/
noncomputable abbrev cubeMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  (volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι))

/-! ## The characters -/

omit [DecidableEq ι] in
lemma continuous_fourierExp (k : ι → ℤ) : Continuous (fourierExp k) := by
  change Continuous (fun x : ι → ℝ =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((k i : ℤ) : ℂ) * (x i : ℂ)))
  fun_prop

omit [DecidableEq ι] in
lemma tpd_norm_fourierExp (k : ι → ℤ) (x : ι → ℝ) : ‖fourierExp k x‖ = 1 := by
  have hmain : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((k i : ℤ) : ℂ) * (x i : ℂ))
      = (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * x i : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourierExp, hmain, Complex.norm_exp_ofReal_mul_I]

omit [DecidableEq ι] in
lemma fourierExp_zero (x : ι → ℝ) : fourierExp (0 : ι → ℤ) x = 1 := by
  simp [fourierExp]

/-! ## Measure bookkeeping -/

omit [DecidableEq ι] in
lemma measurableSet_unitCube : MeasurableSet (unitCube (ι := ι)) := by
  rw [unitCube]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

omit [DecidableEq ι] in
lemma volume_unitCube : (volume : Measure (ι → ℝ)) (unitCube (ι := ι)) = 1 := by
  rw [unitCube, Real.volume_pi_Ioc]
  simp

instance isFiniteMeasure_cubeMeasure : IsFiniteMeasure (cubeMeasure ι) := by
  refine ⟨?_⟩
  rw [cubeMeasure, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_unitCube]
  exact ENNReal.one_lt_top

/-! ## Identifications between the torus characters and the cube characters -/

omit [DecidableEq ι] in
/-- Mathlib's torus character `mFourier k` evaluated at `t` is the character `fourierExp k`
evaluated at the `Ioc`-representative of `t`. -/
lemma mFourier_eq_fourierExp_rep (k : ι → ℤ) (t : UnitAddTorus ι) :
    UnitAddTorus.mFourier k t = fourierExp k (fun i => (AddCircle.equivIoc 1 0 (t i)).1) := by
  rw [← mFourier_mk_eq_fourierExp k (fun i => (AddCircle.equivIoc 1 0 (t i)).1)]
  congr 1
  funext i
  exact (AddCircle.coe_equivIoc (𝕜 := ℝ) (p := 1) (a := 0)).symm

omit [DecidableEq ι] in
/-- The evaluation of a one-term trigonometric polynomial. -/
lemma sum_single_one (x : ι → ℝ) :
    (∑ k ∈ (Finsupp.single (0 : ι → ℤ) (1 : ℂ)).support,
        (Finsupp.single (0 : ι → ℤ) (1 : ℂ)) k * fourierExp k x) = 1 := by
  show (Finsupp.single (0 : ι → ℤ) (1 : ℂ)).sum (fun k c => c * fourierExp k x) = 1
  rw [Finsupp.sum_single_index (by simp), fourierExp_zero, mul_one]

omit [DecidableEq ι] in
/-- The evaluation of a one-term trigonometric polynomial. -/
lemma sum_single_I (x : ι → ℝ) :
    (∑ k ∈ (Finsupp.single (0 : ι → ℤ) Complex.I).support,
        (Finsupp.single (0 : ι → ℤ) Complex.I) k * fourierExp k x) = Complex.I := by
  show (Finsupp.single (0 : ι → ℤ) Complex.I).sum (fun k c => c * fourierExp k x) = Complex.I
  rw [Finsupp.sum_single_index (by simp), fourierExp_zero, mul_one]

/-! ## The main theorem -/

theorem trigPoly_dense_L2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ)
    (hf : MeasureTheory.Integrable (fun x : ι → ℝ => ‖f x‖ ^ 2)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : (ι → ℤ) →₀ ℂ,
      ∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖f x - ∑ k ∈ p.support, p k * Work.Diff.STE.fourierExp k x‖ ^ 2 < ε ^ 2 := by
  classical
  by_cases hfasm : AEStronglyMeasurable f (cubeMeasure ι)
  · -- ## Case A: `f` is a.e. strongly measurable
    have hfm : MemLp f 2 (cubeMeasure ι) :=
      (memLp_two_iff_integrable_sq_norm hfasm).mpr hf
    -- the pull-back of `f` to the torus
    have hfhmem : MemLp (fun t : UnitAddTorus ι => f (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) 2
        (torusMeasure ι) := memLp_comp_rep hfm
    -- density of the characters in `L²` of the torus
    have hcl : (Submodule.span ℂ
        (Set.range (UnitAddTorus.mFourierLp (d := ι) (p := 2)))).topologicalClosure = ⊤ :=
      UnitAddTorus.span_mFourierLp_closure_eq_top (by norm_num)
    have hmem : MemLp.toLp
          (fun t : UnitAddTorus ι => f (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hfhmem
        ∈ (Submodule.span ℂ
            (Set.range (UnitAddTorus.mFourierLp (d := ι) (p := 2)))).topologicalClosure := by
      rw [hcl]
      trivial
    obtain ⟨q, hq, hqd⟩ := Metric.mem_closure_iff.mp hmem (ε / 2) (by linarith)
    obtain ⟨p, hp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq
    -- the approximating trigonometric polynomial
    set T : (ι → ℝ) → ℂ := fun x => ∑ k ∈ p.support, p k * fourierExp k x with hT
    set u : MeasureTheory.Lp ℂ 2 (torusMeasure ι) :=
      MemLp.toLp (fun t : UnitAddTorus ι => f (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hfhmem
        - ∑ k ∈ p.support, p k • UnitAddTorus.mFourierLp (d := ι) (p := 2) k with hu
    have hu_lt : ‖u‖ < ε / 2 := by
      rw [hu]
      rw [← hp, dist_eq_norm] at hqd
      exact hqd
    -- `T` is bounded, hence in `L²`
    have hTmem : MemLp T 2 (cubeMeasure ι) := by
      refine MemLp.of_bound ?_ (∑ k ∈ p.support, ‖p k‖) ?_
      · rw [hT]
        exact (continuous_finsetSum _ fun k _ =>
            continuous_const.mul (continuous_fourierExp k)).aestronglyMeasurable
      · filter_upwards with x
        rw [hT]
        calc ‖∑ k ∈ p.support, p k * fourierExp k x‖
            ≤ ∑ k ∈ p.support, ‖p k * fourierExp k x‖ := norm_sum_le _ _
          _ = ∑ k ∈ p.support, ‖p k‖ := Finset.sum_congr rfl fun k _ => by
              rw [norm_mul, tpd_norm_fourierExp, mul_one]
    have hfTmem : MemLp (fun x => f x - T x) 2 (cubeMeasure ι) := hfm.sub hTmem
    -- the `L²`-class of the error is the class of `(f - T) ∘ rep`
    have hu_eq : u =ᵐ[torusMeasure ι]
        (fun t => (fun x => f x - T x) (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) := by
      rw [hu]
      have h1 : ((MemLp.toLp
            (fun t : UnitAddTorus ι => f (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) hfhmem :
            UnitAddTorus ι → ℂ))
          =ᵐ[torusMeasure ι] (fun t => f (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) :=
        MemLp.coeFn_toLp hfhmem
      have h2 : (((∑ k ∈ p.support, p k • UnitAddTorus.mFourierLp (d := ι) (p := 2) k) :
            MeasureTheory.Lp ℂ 2 (torusMeasure ι)) : UnitAddTorus ι → ℂ)
          =ᵐ[torusMeasure ι] (fun t => ∑ k ∈ p.support, p k * UnitAddTorus.mFourier k t) :=
        coeFn_sum_mFourierLp p
      refine (Lp.coeFn_sub _ _).trans ((h1.sub h2).trans ?_)
      apply Filter.Eventually.of_forall
      intro t
      simp only [hT, Pi.sub_apply]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [mFourier_eq_fourierExp_rep k t]
    -- the integral over the torus equals the integral over the cube
    have hkey : ∫ t, ‖(u : UnitAddTorus ι → ℂ) t‖ ^ 2 ∂(torusMeasure ι)
        = ∫ x, ‖f x - T x‖ ^ 2 ∂(cubeMeasure ι) := by
      have hA : (fun t => ‖(u : UnitAddTorus ι → ℂ) t‖ ^ 2) =ᵐ[torusMeasure ι]
          (fun t => ‖(fun t => (fun x => f x - T x)
            (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) t‖ ^ 2) := by
        filter_upwards [hu_eq] with t ht
        rw [ht]
      calc ∫ t, ‖(u : UnitAddTorus ι → ℂ) t‖ ^ 2 ∂(torusMeasure ι)
          = ∫ t, ‖(fun t => (fun x => f x - T x)
              (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) t‖ ^ 2 ∂(torusMeasure ι) :=
            integral_congr_ae hA
        _ = ∫ x, ‖f x - T x‖ ^ 2 ∂(cubeMeasure ι) :=
            integral_pullback_norm_sq (fun x => f x - T x) hfTmem.aestronglyMeasurable
    refine ⟨p, ?_⟩
    have hfin : ∫ x, ‖f x - T x‖ ^ 2 ∂(cubeMeasure ι) < ε ^ 2 := by
      rw [← hkey, ← norm_sq_Lp_eq_integral u]
      have h1 : ‖u‖ ^ 2 < (ε / 2) ^ 2 := by nlinarith [norm_nonneg u, hε]
      calc ‖u‖ ^ 2 < (ε / 2) ^ 2 := h1
        _ = ε ^ 2 / 4 := by ring
        _ < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
    simpa only [hT] using hfin
  · -- ## Case B: `f` is not a.e. strongly measurable
    by_cases h1 : AEStronglyMeasurable (fun x : ι → ℝ => ‖f x - 1‖ ^ 2) (cubeMeasure ι)
    · by_cases h2 : AEStronglyMeasurable (fun x : ι → ℝ => ‖f x - Complex.I‖ ^ 2) (cubeMeasure ι)
      · exact absurd (aestronglyMeasurable_of_norm_sq_sub f hf.aestronglyMeasurable h1 h2) hfasm
      · refine ⟨Finsupp.single (0 : ι → ℤ) Complex.I, ?_⟩
        have hval : (∫ x in unitCube (ι := ι),
              ‖f x - ∑ k ∈ (Finsupp.single (0 : ι → ℤ) Complex.I).support,
                (Finsupp.single (0 : ι → ℤ) Complex.I) k * fourierExp k x‖ ^ 2)
            = ∫ x in unitCube (ι := ι), ‖f x - Complex.I‖ ^ 2 :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            show ‖f x - ∑ k ∈ (Finsupp.single (0 : ι → ℤ) Complex.I).support,
                (Finsupp.single (0 : ι → ℤ) Complex.I) k * fourierExp k x‖ ^ 2
              = ‖f x - Complex.I‖ ^ 2
            rw [sum_single_I x])
        rw [hval, integral_undef (fun hInt : Integrable
          (fun x : ι → ℝ => ‖f x - Complex.I‖ ^ 2) (cubeMeasure ι) =>
            h2 hInt.aestronglyMeasurable)]
        exact pow_pos hε 2
    · refine ⟨Finsupp.single (0 : ι → ℤ) (1 : ℂ), ?_⟩
      have hval : (∫ x in unitCube (ι := ι),
            ‖f x - ∑ k ∈ (Finsupp.single (0 : ι → ℤ) (1 : ℂ)).support,
              (Finsupp.single (0 : ι → ℤ) (1 : ℂ)) k * fourierExp k x‖ ^ 2)
          = ∫ x in unitCube (ι := ι), ‖f x - 1‖ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          show ‖f x - ∑ k ∈ (Finsupp.single (0 : ι → ℤ) (1 : ℂ)).support,
              (Finsupp.single (0 : ι → ℤ) (1 : ℂ)) k * fourierExp k x‖ ^ 2
            = ‖f x - 1‖ ^ 2
          rw [sum_single_one x])
      rw [hval, integral_undef (fun hInt : Integrable
        (fun x : ι → ℝ => ‖f x - 1‖ ^ 2) (cubeMeasure ι) =>
          h1 hInt.aestronglyMeasurable)]
      exact pow_pos hε 2

end Work.Diff.STE
