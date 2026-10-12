import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseB7AK.Q2Gram.chiSq_fourier_sum
import Submission.Work.BoseBoxFock.integral_toLp
import Submission.Work.BoseBoxFock.parseval_torus_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sampling_unitCube_L2`

The **unit-cube Fourier (Parseval) identity for `L²` functions**: for
`g : ℝ³ → ℂ` in `L²(ℝ³)` whose support lies in the unit cube `[-1/2,1/2]³`,

    ∑_{n : ℤ³} ‖∫_{ℝ³} e^{-i⟪2π n, y⟫} g(y) dy‖² = ∫_{ℝ³} ‖g(y)‖² ,

i.e. the Fourier samples of `g` on the lattice `2πℤ³` (`Work.BoseB4.vec n = 2πn`) reproduce `g`
with the `L²` norm: the discrete Fourier transform is an isometry.

This is the `L²` version of `Work.BoseBoxFock.sampling_unitCube`, which is stated for smooth
compactly supported `g`.  The proof is the same (everything goes through the torus
`𝕋³ = (ℝ/ℤ)³`), only the ingredient "the lift of `g` to `𝕋³` is `L²`" is proved differently:
instead of boundedness of a continuous compactly supported function, we transport the `L²`
property along the measure-preserving maps

    (Fin 3 → ℝ) --WithLp.toLp--> ℝ³ ,   𝕋³ --representative in (-1/2,1/2]³--> (Fin 3 → ℝ)

both of which are measure preserving with respect to Lebesgue measure restricted to the
half-open box `(-1/2,1/2]³`.  (The second one is `UnitAddTorus.measurePreserving_equivPiIoc`
composed with `map_comap_subtype_coe`.)

## The three ingredients

* `torusLift_memLp_of_memLp` : `MemLp (torusLift g) 2 torusVol` for `g ∈ L²`;
* `integral_torusLift_normSq` : `∫_{𝕋³} ‖torusLift g‖² = ∫_{ℝ³} ‖g‖²` (the lift is an isometry on
  functions supported in the cube);
* `mFourierCoeff_torusLift` : the torus Fourier coefficients of the lift are the integrals in the
  statement.

Parseval for Mathlib's orthonormal Fourier basis of `L²(𝕋³)` (`UnitAddTorus.hasSum_sq_mFourierCoeff`)
then gives the result.

Conventions (see `Submission/Work/BoseBoxFock/SamplingDefs.lean`): `torusVol` is the Haar
probability measure on `𝕋³`; Mathlib's torus Fourier theory is stated for the Haar measure
registered by the *local* instance `instMeasureSpaceUnitAddCircle` of
`Mathlib/Analysis/Fourier/AddCircleMulti.lean`, so we register that instance in this file too.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

attribute [local instance] instMeasureSpaceUnitAddCircle

/-! ## The half-open box in the form used by the torus API -/

/-- The half-open box `(-1/2,1/2]³` in the set-builder form produced by
`UnitAddTorus.integral_preimage` / `UnitAddTorus.mFourierCoeff_eq_integral` /
`UnitAddTorus.measurableEquivPiIoc`. -/
def boxHalf : Set (Fin 3 → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)}

lemma measurableSet_boxHalf : MeasurableSet boxHalf := by
  rw [show boxHalf = Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)) from by
    ext x
    simp only [boxHalf, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]]
  exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioc

/-- The half-open box `(-1/2,1/2]³` in the set-builder form produced by
`UnitAddTorus.integral_preimage` / `UnitAddTorus.mFourierCoeff_eq_integral` /
`UnitAddTorus.measurableEquivPiIoc`. -/
lemma halfBox_eq_boxIoc :
    {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} = boxIoc := by
  rw [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num]
  ext x
  simp [boxIoc, Set.mem_pi]

lemma boxIoc_eq_halfBox : boxIoc = {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} :=
  halfBox_eq_boxIoc.symm

lemma measurableSet_halfBox :
    MeasurableSet {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} := by
  rw [halfBox_eq_boxIoc]
  exact measurableSet_boxIoc

/-! ## Ingredient 1: the lift of an `L²` function is `L²` on the torus -/

/-- **The lift to the torus of an `L²` function is `L²`.**  This is the `L²` counterpart of
`Work.BoseBoxFock.torusLift_memLp` (which assumes `g` smooth with compact support and uses
boundedness).  Here the norm bound is replaced by the measure-preserving transport along
`PiLp.volume_preserving_toLp` and the representative equivalence of `AddCircleMulti`. -/
theorem torusLift_memLp_of_memLp {g : ℝ³ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (torusLift g) 2 torusVol := by
  -- push forward along `WithLp.toLp 2 : (Fin 3 → ℝ) → ℝ³`
  have hgt : MemLp (fun x : Fin 3 → ℝ => g (WithLp.toLp 2 x)) 2
      (volume : Measure (Fin 3 → ℝ)) :=
    hg.comp_measurePreserving (PiLp.volume_preserving_toLp (Fin 3))
  -- the inclusion of the half-open box as a subtype is measure preserving
  have hsub : MeasureTheory.MeasurePreserving
      (Subtype.val : {x : Fin 3 → ℝ // ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} →
        (Fin 3 → ℝ))
      (Measure.comap Subtype.val (volume : Measure (Fin 3 → ℝ)))
      (volume.restrict {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)}) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_halfBox volume⟩
  have h2 : MemLp (fun y : {x : Fin 3 → ℝ // ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} =>
      g (WithLp.toLp 2 (y : Fin 3 → ℝ))) 2
      (Measure.comap Subtype.val (volume : Measure (Fin 3 → ℝ))) :=
    (hgt.restrict {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)}).comp_measurePreserving
      hsub
  -- the representative equivalence of the torus with the half-open box
  have h1 : MeasureTheory.MeasurePreserving
      (⇑(UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 3 => (-(1/2) : ℝ))))
      torusVol (Measure.comap Subtype.val (volume : Measure (Fin 3 → ℝ))) :=
    UnitAddTorus.measurePreserving_equivPiIoc _
  have h3 := h2.comp_measurePreserving h1
  convert h3 using 1
  ext t
  simp only [Function.comp_apply, torusLift, UnitAddTorus.coe_measurableEquivPiIoc_apply]

/-! ## Ingredient 2: the lift is an isometry -/

/-- **The torus lift is an isometry** (for functions supported in the cube): the integral of
`‖torusLift g‖²` against the Haar probability measure `torusVol` equals the Lebesgue integral
`∫ ‖g‖²` over `ℝ³`.  This is `Work.BoseBoxFock.torusLift_norm_eq` with the smoothness and
compact-support hypotheses removed (its proof never used them). -/
theorem integral_torusLift_normSq {g : ℝ³ → ℂ}
    (hgsupp : tsupport g ⊆ {y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)}) :
    (∫ t : UnitAddTorus (Fin 3), ‖torusLift g t‖ ^ 2 ∂torusVol) = ∫ y : ℝ³, ‖g y‖ ^ 2 := by
  -- Step 1: the torus integral is the integral over the fundamental domain of the projection.
  have h1 : (∫ t : UnitAddTorus (Fin 3), ‖torusLift g t‖ ^ 2 ∂torusVol)
      = ∫ x in boxIoc, ‖torusLift g (torusProj x)‖ ^ 2 := by
    rw [torusVol_eq_volume, boxIoc_eq_halfBox]
    exact UnitAddTorus.integral_preimage (d := Fin 3)
      (fun t : UnitAddTorus (Fin 3) => ‖torusLift g t‖ ^ 2) (fun _ => (-(1/2) : ℝ))
  -- Step 2: on the fundamental domain the lift of `g` is `g` itself.
  have h2 : ∫ x in boxIoc, ‖torusLift g (torusProj x)‖ ^ 2
      = ∫ x in boxIoc, ‖g (WithLp.toLp 2 x)‖ ^ 2 := by
    refine setIntegral_congr_fun measurableSet_boxIoc fun x hx => ?_
    rw [torusLift_apply_proj hx]
  -- Step 3: `g` vanishes off the closed box, which agrees a.e. with the half-open box.
  have h3 : ∫ x in boxIoc, ‖g (WithLp.toLp 2 x)‖ ^ 2
      = ∫ x : Fin 3 → ℝ, ‖g (WithLp.toLp 2 x)‖ ^ 2 := by
    rw [setIntegral_congr_set boxIoc_ae_eq_boxIcc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have hx' : ¬ ∀ i, |x i| ≤ (1 / 2 : ℝ) := fun h => hx (mem_boxIcc.mpr h)
    simp only [not_forall, not_le] at hx'
    obtain ⟨i, hi⟩ := hx'
    have hy : ¬ ∀ i, |(WithLp.toLp 2 x : ℝ³) i| ≤ (1 / 2 : ℝ) :=
      fun h => absurd (h i) (not_le.mpr hi)
    have h0 : g (WithLp.toLp 2 x) = 0 := by
      by_contra hc
      exact hy (hgsupp (subset_tsupport g (Function.mem_support.mpr hc)))
    rw [h0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  -- Step 4: change of variables along `WithLp.toLp 2`.
  rw [h1, h2, h3, ← integral_toLp (fun y : ℝ³ => ‖g y‖ ^ 2)]

/-! ## Ingredient 3: the Fourier coefficients of the lift -/

/-- `mFourier (-n)` evaluated at the lift of a point `x` of the box is `exp (-i⟪2πn, x⟫)`. -/
private lemma mFourier_neg_torusProj (n : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    UnitAddTorus.mFourier (-n) (torusProj x)
      = Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) (WithLp.toLp 2 x) : ℂ))) :=
  Work.BoseB7AK.Q2Gram.mFourier_neg_apply n x

/-- The lift of `g` vanishes off the closed box, because `g` is supported in it. -/
private lemma torusLift_apply_eq_zero_off_boxIcc {g : ℝ³ → ℂ}
    (hgsupp : tsupport g ⊆ {y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)}) {x : Fin 3 → ℝ}
    (hx : x ∉ boxIcc) : g (WithLp.toLp 2 x) = 0 := by
  by_contra hne
  have hmem : WithLp.toLp 2 x ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hne)
  exact hx (mem_boxIcc.mpr fun i => by simpa using hgsupp hmem i)

/-- **The Fourier coefficients of the lift.**  For `n : ℤ³`, the `n`-th torus Fourier
coefficient of the lift of `g` is the integral of `e^{-i⟪2πn,y⟫} g` over `ℝ³`. -/
theorem mFourierCoeff_torusLift {g : ℝ³ → ℂ}
    (hP : MemLp (torusLift g) 2 torusVol)
    (hgsupp : tsupport g ⊆ {y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)}) (n : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(hP.toLp (torusLift g))) n
      = ∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y := by
  -- replace the `Lp` representative by `torusLift g` itself
  rw [show UnitAddTorus.mFourierCoeff (⇑(hP.toLp (torusLift g))) n
        = UnitAddTorus.mFourierCoeff (torusLift g) n from by
    refine integral_congr_ae ?_
    filter_upwards [hP.coeFn_toLp] with t ht
    rw [ht]]
  -- the coefficient as an integral over the fundamental box
  rw [UnitAddTorus.mFourierCoeff_eq_integral (torusLift g) n (fun _ : Fin 3 => -(1/2 : ℝ)),
    halfBox_eq_boxIoc]
  -- identify the integrand on the box
  rw [show (∫ x in boxIoc, UnitAddTorus.mFourier (-n) (torusProj x) • torusLift g (torusProj x))
        = ∫ x in boxIoc, Complex.exp
            (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) (WithLp.toLp 2 x) : ℂ)))
            * g (WithLp.toLp 2 x) from by
    refine setIntegral_congr_fun measurableSet_boxIoc fun x hx => ?_
    dsimp only
    rw [mFourier_neg_torusProj n x, torusLift_apply_proj hx, smul_eq_mul]]
  -- the integrand vanishes outside the closed box: integrate over `boxIcc`, then over `ℝ³`
  rw [setIntegral_congr_set boxIoc_ae_eq_boxIcc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := boxIcc) fun x hx => by
    rw [torusLift_apply_eq_zero_off_boxIcc hgsupp hx, mul_zero]]
  exact (integral_toLp (E := ℂ) fun y : ℝ³ =>
    Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y).symm

/-! ## The theorem -/

theorem sampling_unitCube_L2 {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.volume)
    (hgsupp : tsupport g ⊆ {y : EuclideanSpace ℝ (Fin 3) | ∀ i, |y i| ≤ (1 / 2 : ℝ)}) :
    HasSum (fun n : Fin 3 → ℤ =>
        ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y‖ ^ 2)
      (∫ y, ‖g y‖ ^ 2) := by
  have hP : MemLp (torusLift g) 2 torusVol := torusLift_memLp_of_memLp hg
  -- Parseval on the torus for the lift of `g`
  have hsum := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin 3) (hP.toLp (torusLift g))
  -- identify the coefficients with the integrals of the statement
  have hfun : ∀ n : Fin 3 → ℤ,
      ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y‖ ^ 2
        = ‖UnitAddTorus.mFourierCoeff (⇑(hP.toLp (torusLift g))) n‖ ^ 2 :=
    fun n => by rw [mFourierCoeff_torusLift hP hgsupp n]
  -- identify the sum with `∫ ‖g‖²`
  have hval : (∫ t : UnitAddTorus (Fin 3), ‖(hP.toLp (torusLift g)) t‖ ^ 2)
      = ∫ y : ℝ³, ‖g y‖ ^ 2 := by
    rw [← integral_torusLift_normSq hgsupp]
    refine integral_congr_ae ?_
    filter_upwards [hP.coeFn_toLp] with t ht
    rw [ht]
  have hsum2 : HasSum (fun n : Fin 3 → ℤ =>
        ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y‖ ^ 2)
      (∫ t : UnitAddTorus (Fin 3), ‖(hP.toLp (torusLift g)) t‖ ^ 2) := hsum.congr_fun hfun
  rw [hval] at hsum2
  exact hsum2

end Work.BoseBoxFock
