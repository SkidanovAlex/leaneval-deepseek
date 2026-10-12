import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseB7AK.Q2Gram.chiSq_fourier_sum
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.parseval_torus_box
import Submission.Work.BoseBoxFock.torusLift_memLp
import Submission.Work.BoseBoxFock.torusLift_norm_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sampling_unitCube`

The **unit-cube Fourier (Parseval) identity**: for a smooth, compactly supported
`g : ℝ³ → ℂ` whose support lies in the unit cube `[-1/2,1/2]³`,

    ∑_{n : ℤ³} ‖∫_{ℝ³} e^{-i⟪2π n, y⟫} g(y) dy‖² = ∫_{ℝ³} ‖g(y)‖² ,

i.e. the Fourier samples of `g` on the lattice `2πℤ³` (`Work.BoseB4.vec n = 2πn`) reproduce `g`
with the `L²` norm: the discrete Fourier transform is an isometry.

## The proof

Everything is done on the unit torus `𝕋³ = (ℝ/ℤ)³` (see
`Submission/Work/BoseBoxFock/SamplingDefs.lean` for the vocabulary `torusLift`, `torusProj`,
`boxIoc`, `boxIcc`, `torusVol`).

1. `g` lifts to `torusLift g : 𝕋³ → ℂ` through the fundamental domain `(-1/2,1/2]³`, which is in
   `L²(𝕋³)` (`torusLift_memLp`).
2. For `n : ℤ³`, the `n`-th torus Fourier coefficient of that lift is the integral appearing in
   the statement (`mFourierCoeff_torusLift` below): Mathlib's
   `UnitAddTorus.mFourierCoeff_eq_integral` rewrites the coefficient as an integral over the
   fundamental box, on which the monomial `mFourier (-n)` is `e^{-i⟪2πn,·⟫}`
   (`Work.BoseB7AK.Q2Gram.mFourier_neg_apply`) and `torusLift` is `g` itself
   (`torusLift_apply_proj`); since `g` vanishes off the closed box `boxIcc`, and `boxIcc`
   agrees with the half-open `boxIoc` almost everywhere, the box integral is the full
   Lebesgue integral over `ℝ³` (`integral_toLp`).
3. Parseval for Mathlib's orthonormal Fourier basis of `L²(𝕋³)`
   (`UnitAddTorus.hasSum_sq_mFourierCoeff`) thus turns the sum of squared coefficients into the
   box integral of `‖torusLift g‖²` (`parseval_torus_box`), which is `∫_{ℝ³} ‖g‖²`
   (`torusLift_norm_eq`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

attribute [local instance] instMeasureSpaceUnitAddCircle

/-! ## Auxiliary facts -/

/-- The set produced by `UnitAddTorus.mFourierCoeff_eq_integral` /
`UnitAddTorus.integral_preimage` for `a = fun _ => -1/2` is the box `(-1/2,1/2]³`. -/
private lemma boxIoc_set_eq :
    {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} = boxIoc := by
  rw [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num]
  ext x
  simp [boxIoc, Set.mem_pi]

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
private lemma mFourierCoeff_torusLift {g : ℝ³ → ℂ}
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
    boxIoc_set_eq]
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

theorem sampling_unitCube {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ {y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)}) :
    (∑' n : Fin 3 → ℤ,
        ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y‖ ^ 2)
      = ∫ y, ‖g y‖ ^ 2 := by
  have hP : MemLp (torusLift g) 2 torusVol := torusLift_memLp hg hgc
  -- the box integral of `‖torusLift g‖²` is the torus integral
  have hboxT : (∫ x in boxIoc, ‖torusLift g (torusProj x)‖ ^ 2)
      = ∫ t : UnitAddTorus (Fin 3), ‖torusLift g t‖ ^ 2 ∂torusVol := by
    rw [← boxIoc_set_eq, ← UnitAddTorus.integral_preimage
      (fun t : UnitAddTorus (Fin 3) => ‖torusLift g t‖ ^ 2) (fun _ : Fin 3 => -(1/2 : ℝ)),
      ← torusVol_eq_volume]
  calc (∑' n : Fin 3 → ℤ,
        ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y‖ ^ 2)
      = ∑' n : Fin 3 → ℤ,
          ‖UnitAddTorus.mFourierCoeff (⇑(hP.toLp (torusLift g))) n‖ ^ 2 :=
        tsum_congr fun n => by rw [mFourierCoeff_torusLift hP hgsupp n]
    _ = ∫ x in boxIoc, ‖torusLift g (torusProj x)‖ ^ 2 :=
        parseval_torus_box (torusLift g) hP
    _ = ∫ t : UnitAddTorus (Fin 3), ‖torusLift g t‖ ^ 2 ∂torusVol := hboxT
    _ = ∫ y : ℝ³, ‖g y‖ ^ 2 := torusLift_norm_eq hg hgc hgsupp

end Work.BoseBoxFock
