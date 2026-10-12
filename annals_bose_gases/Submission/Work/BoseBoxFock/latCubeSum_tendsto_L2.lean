import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.latRowSum_tendsto_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latCubeSum_tendsto_L2`

The **un-cut** lattice partial sums of `W` converge in `L²` of the centred corpus box
`corpusBox.boxL ℓ = [-ℓ/2,ℓ/2]³` to `ℓ³` times the periodisation `latPer ℓ W z = Σ'_m W(z+ℓ·latVec m)`:

    `∫_{boxL ℓ} ‖Σ_{k : Lab N'} Ŵ(kmomLab ℓ N' k)e^{i⟪kmomLab ℓ N' k,z⟫} − ℓ³·latPer ℓ W z‖² → 0` .

This differs from the *sibling* `Work.BoseBoxFock.latRowSum_tendsto_L2` only in that the row sum
there carries the ultraviolet factor `uvCut fu (uvRad ℓ N')` (which kills every mode with
`‖kmomLab ℓ N' k‖ > 2·uvRad ℓ N'`), whereas here **all** the modes of the cube
`Lab N' ≃ cube N'` are kept.  The extra terms are exactly the lattice modes in the annulus
`N'/4 < ‖latVec n‖ ≤ √3·N'`, so the difference `latCubeSum − rowSum` is a *finite character sum* whose
`L²` norm is computed in closed form by the finite lattice Parseval identity
`Work.BoseBoxFock.latFinset_parseval_box`:

    `∫_{latBox ℓ} ‖latCubeSum − rowSum‖² = ℓ³ Σ_{n ∈ cube N'} ‖(1 − ζ_n)Ŵ(k_n)‖²`,

and is therefore bounded by the lattice tail `ℓ³ Σ'_{n : uvRad ℓ N' ≤ ‖k_n‖} ‖Ŵ(k_n)‖²`, which
tends to `0` by `Work.BoseBoxFock.kinFT_lattice_tail_sq_lt`.  The conclusion then follows from the
sibling's convergence in `L²` by `‖a − c‖² ≤ 2‖a − b‖² + 2‖b − c‖²`.

Since the cut-off function `ζ = uvCut fu (uvRad N')` is only used through `0 ≤ ζ ≤ 1` and
`ζ = 1` below the cut-off, any `LowCut fu` can be used; the file constructs one explicitly
(`cutLin`, the smooth transition function) so that the statement is self-contained.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

open LatFourier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. A concrete low-pass cut-off `f` -/

/-- FS's cut-off `f` (`= 1` on `(-∞,1]`, `= 0` on `[2,∞)`, smooth, non-increasing) realised as the
smooth transition function of `2 - s`. -/
noncomputable def cutLin : Work.BoseBoxFix.LowCut where
  f := fun s => Real.smoothTransition (2 - s)
  smooth := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 2 - s) := by fun_prop
    exact Real.smoothTransition.contDiff.comp h1
  anti := fun a b hab => Real.smoothTransition.monotone (by linarith)
  one := fun s hs => Real.smoothTransition.one_of_one_le (by linarith)
  zero := fun s hs => Real.smoothTransition.zero_of_nonpos (by linarith)

/-! ## 1. The cube partial sum and its reindexing -/

/-- **The `Lab N`-indexed cube partial sum** of the lattice Fourier series of `W` (the un-cut
partial sum of the target statement). -/
noncomputable def latCubeSum (ℓ : ℝ) (N : ℕ) (W : E3 → ℝ) (z : E3) : ℂ :=
  ∑ k : Lab N, LatFourier.latFt ℓ W (labVec N k) * latChr ℓ (labVec N k) z

/-- `latCubeSum` is *definitionally* the sum appearing in the target statement. -/
lemma cubeSum_apply (ℓ : ℝ) (N : ℕ) (W : E3 → ℝ) (z : E3) :
    latCubeSum ℓ N W z = ∑ k : Lab N,
      Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N k)
        * Complex.exp (Complex.I * ((inner ℝ (kmomLab ℓ N k) z : ℝ) : ℂ)) := rfl

/-- The `Lab N`-indexed sum reindexed onto the box `cube N = [-N,N]³ ∩ ℤ³`. -/
lemma cubeSum_eq_cube_sum (ℓ : ℝ) (N : ℕ) (W : E3 → ℝ) (z : E3) :
    latCubeSum ℓ N W z = ∑ n ∈ Work.BoseRowQ2.cube N, LatFourier.latFt ℓ W n * latChr ℓ n z := by
  unfold latCubeSum
  rw [← Work.BoseRowQ2.image_labVec_eq_cube N]
  rw [Finset.sum_image (Work.BoseRowQ2.labVec_inj' N).injOn]

/-- The row sum reindexed onto the box `cube N`. -/
lemma rowSum_eq_cube_sum (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) (z : E3) :
    rowSum ℓ fu N W z
      = ∑ n ∈ Work.BoseRowQ2.cube N,
          ((uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ) : ℂ) * LatFourier.latFt ℓ W n
            * latChr ℓ n z := by
  rw [show rowSum ℓ fu N W z
      = ∑ k : Lab N, ((uvCut fu (uvRad ℓ N) (kmomInt ℓ (labVec N k)) : ℝ) : ℂ)
          * LatFourier.latFt ℓ W (labVec N k) * latChr ℓ (labVec N k) z from rfl]
  rw [← Work.BoseRowQ2.image_labVec_eq_cube N]
  rw [Finset.sum_image (Work.BoseRowQ2.labVec_inj' N).injOn]

/-- The row sum is *definitionally* the sum in the sibling
`Work.BoseBoxFock.latRowSum_tendsto_L2` (the momentum `kmomLab ℓ N k` being `kmomInt ℓ (labVec N k)`
and `latChr` being the exponential of the same inner product). -/
lemma rowSum_sibling_form (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) (z : E3) :
    rowSum ℓ fu N W z = ∑ k : Lab N,
      ((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
        * Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N k)
        * Complex.exp (Complex.I * ((inner ℝ (kmomLab ℓ N k) z : ℝ) : ℂ)) := rfl

/-- The periodisation is *definitionally* the `tsum` of the statement. -/
lemma latPer_sibling_form (ℓ : ℝ) (W : E3 → ℝ) (z : E3) :
    LatFourier.latPer ℓ W z = ∑' m : Fin 3 → ℤ, ((W (z + ℓ • latVec m) : ℝ) : ℂ) := rfl

/-- `‖(t : ℂ)‖ ≤ 1` for `0 ≤ t ≤ 1`. -/
lemma norm_ofReal_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ‖((t : ℝ) : ℂ)‖ ≤ 1 := by
  have h2 : ‖((t : ℝ) : ℂ)‖ ^ 2 = t * t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  nlinarith [norm_nonneg ((t : ℝ) : ℂ)]

/-- The pointwise identity**: the difference of the cube partial sum and the row sum is the
box-indexed character sum with the coefficients `(1 − ζ_n)·Ŵ(k_n)`. -/
lemma cubeSum_sub_rowSum (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) (z : E3) :
    latCubeSum ℓ N W z - rowSum ℓ fu N W z
      = ∑ n ∈ Work.BoseRowQ2.cube N,
          (((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ)
            * LatFourier.latFt ℓ W n * latChr ℓ n z := by
  rw [rowSum_eq_cube_sum, cubeSum_eq_cube_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-! ## 2. Periodicity of the summands under the lattice translations -/

lemma latChr_add_latVec {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n m : Fin 3 → ℤ) (z : E3) :
    latChr ℓ n (z + ℓ • latVec m) = latChr ℓ n z :=
  LatFourier.exp_I_inner_add_latVec hℓ n m z

lemma cubeSum_add_latVec {ℓ : ℝ} (hℓ : ℓ ≠ 0) (N : ℕ) (W : E3 → ℝ)
    (m : Fin 3 → ℤ) (z : E3) :
    latCubeSum ℓ N W (z + ℓ • latVec m) = latCubeSum ℓ N W z := by
  unfold latCubeSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [latChr_add_latVec hℓ (labVec N k) m z]

lemma rowSum_add_latVec {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (W : E3 → ℝ) (m : Fin 3 → ℤ) (z : E3) :
    rowSum ℓ fu N W (z + ℓ • latVec m) = rowSum ℓ fu N W z := by
  simp only [rowSum, latChr]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LatFourier.exp_I_inner_add_latVec (ne_of_gt hℓ)]

lemma latPer_add_latVec {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (m : Fin 3 → ℤ) (z : E3) :
    LatFourier.latPer ℓ W (z + ℓ • latVec m) = LatFourier.latPer ℓ W z := by
  have hpt : ∀ n : Fin 3 → ℤ,
      z + ℓ • latVec m + ℓ • latVec n = z + ℓ • latVec (n + m) := by
    intro n
    rw [LatFourier.latVec_add, smul_add]
    abel
  have h1 : LatFourier.latPer ℓ W (z + ℓ • latVec m)
      = ∑' n : Fin 3 → ℤ, (W (z + ℓ • latVec (n + m)) : ℂ) := by
    simp only [LatFourier.latPer]
    exact tsum_congr fun n => by rw [hpt n]
  rw [h1]
  exact Equiv.tsum_eq (Equiv.addRight m) (fun n => (W (z + ℓ • latVec n) : ℂ))

/-! ## 3. Finite lattice Parseval for the difference -/

/-- **Parseval for `latCubeSum − rowSum`**: its `L²` norm on the closed cube is the `ℓ³`-multiple of
the sum of the squared coefficients. -/
lemma integral_normSq_cubeSum_sub_rowSum {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
    (N : ℕ) (W : E3 → ℝ) :
    (∫ z in LatFourier.latBox ℓ, ‖latCubeSum ℓ N W z - rowSum ℓ fu N W z‖ ^ 2)
      = ℓ ^ 3 * ∑ n ∈ Work.BoseRowQ2.cube N,
          ‖(((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ)
            * LatFourier.latFt ℓ W n‖ ^ 2 := by
  rw [show (∫ z in LatFourier.latBox ℓ, ‖latCubeSum ℓ N W z - rowSum ℓ fu N W z‖ ^ 2)
      = ∫ z in LatFourier.latBox ℓ,
          ‖∑ n ∈ Work.BoseRowQ2.cube N,
            ((((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ)
                * LatFourier.latFt ℓ W n)
              * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))‖ ^ 2 from
    setIntegral_congr_fun (LatFourier.measurableSet_latBox ℓ)
      (fun z _ => by rw [cubeSum_sub_rowSum ℓ fu N W z]; rfl)]
  exact latFinset_parseval_box hℓ (Work.BoseRowQ2.cube N)
    (fun n => (((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ) * LatFourier.latFt ℓ W n)

/-! ## 4. The coefficient bound and the lattice tail -/

/-- **The pointwise bound on the coefficient of `latCubeSum − rowSum`.**  For `N ≥ 1`, the coefficient
vanishes on the momentum ball `‖kmomInt ℓ n‖ ≤ uvRad ℓ N`, and outside it is bounded by the Fourier
sample itself. -/
lemma cubeCoef_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {fu : Work.BoseBoxFix.LowCut} {N : ℕ} (hN : 1 ≤ N)
    (W : E3 → ℝ) (n : Fin 3 → ℤ) :
    ‖(((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ) * LatFourier.latFt ℓ W n‖ ^ 2
      ≤ (if uvRad ℓ N < ‖kmomInt ℓ n‖ then ‖LatFourier.latFt ℓ W n‖ ^ 2 else 0) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hΛ : 0 < uvRad ℓ N := by rw [uvRad]; positivity
  by_cases hc : ‖kmomInt ℓ n‖ ≤ uvRad ℓ N
  · have ht : uvCut fu (uvRad ℓ N) (kmomInt ℓ n) = 1 := by
      rw [uvCut]
      exact fu.one _ (div_le_one_of_le₀ hc hΛ.le)
    rw [if_neg (not_lt.mpr hc), ht]
    norm_num
  · rw [if_pos (not_le.mp hc)]
    have ht0 : 0 ≤ uvCut fu (uvRad ℓ N) (kmomInt ℓ n) := fu.nonneg _
    have ht1 : uvCut fu (uvRad ℓ N) (kmomInt ℓ n) ≤ 1 := fu.le_one _
    have h1 : ‖(((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ)‖ ^ 2 ≤ 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      nlinarith
    calc ‖(((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ) * LatFourier.latFt ℓ W n‖ ^ 2
        = ‖(((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ)‖ ^ 2
            * ‖LatFourier.latFt ℓ W n‖ ^ 2 := by rw [norm_mul, mul_pow]
      _ ≤ 1 * ‖LatFourier.latFt ℓ W n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖LatFourier.latFt ℓ W n‖ ^ 2 := by ring

/-- **The coefficient sum is bounded by the lattice tail.** -/
lemma cubeCoef_sum_le_tail {ℓ R : ℝ} (hℓ : 0 < ℓ) {fu : Work.BoseBoxFix.LowCut} {N : ℕ}
    (hN : 1 ≤ N) {W : E3 → ℝ} (hWm : AEStronglyMeasurable W volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    (∑ n ∈ Work.BoseRowQ2.cube N,
        ‖(((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ) * LatFourier.latFt ℓ W n‖ ^ 2)
      ≤ ∑' n : Fin 3 → ℤ,
          (if uvRad ℓ N ≤ ‖kmomInt ℓ n‖ then ‖LatFourier.latFt ℓ W n‖ ^ 2 else 0) := by
  have hWc_bdd : ∃ C : ℝ, ∀ x : E3, ‖((W x : ℝ) : ℂ)‖ ≤ C :=
    ⟨hWb.choose, fun x => by simpa using hWb.choose_spec x⟩
  have hWc_supp : ∀ x : E3, R < ‖x‖ → ((W x : ℝ) : ℂ) = 0 := fun x hx => by
    rw [hWs x hx]; norm_num
  have hWc_aesm : AEStronglyMeasurable (fun x : E3 => ((W x : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hWm
  have hsumm : Summable (fun n : Fin 3 → ℤ => ‖LatFourier.latFt ℓ W n‖ ^ 2) :=
    summable_kinFT_lattice_of_bounded (ℓ := ℓ) (R := R) hℓ hWc_bdd hWc_supp hWc_aesm
  have hg : Summable (fun n : Fin 3 → ℤ =>
      (if uvRad ℓ N < ‖kmomInt ℓ n‖ then ‖LatFourier.latFt ℓ W n‖ ^ 2 else 0)) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> simp) hsumm
  have hh : Summable (fun n : Fin 3 → ℤ =>
      (if uvRad ℓ N ≤ ‖kmomInt ℓ n‖ then ‖LatFourier.latFt ℓ W n‖ ^ 2 else 0)) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> simp) hsumm
  calc (∑ n ∈ Work.BoseRowQ2.cube N,
        ‖(((1 - uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ)) : ℂ) * LatFourier.latFt ℓ W n‖ ^ 2)
      ≤ ∑ n ∈ Work.BoseRowQ2.cube N,
          (if uvRad ℓ N < ‖kmomInt ℓ n‖ then ‖LatFourier.latFt ℓ W n‖ ^ 2 else 0) :=
        Finset.sum_le_sum (fun n _ => cubeCoef_bound hℓ hN W n)
    _ ≤ ∑' n : Fin 3 → ℤ,
          (if uvRad ℓ N < ‖kmomInt ℓ n‖ then ‖LatFourier.latFt ℓ W n‖ ^ 2 else 0) :=
        hg.sum_le_tsum _ (fun n _ => by split_ifs <;> positivity)
    _ ≤ ∑' n : Fin 3 → ℤ,
          (if uvRad ℓ N ≤ ‖kmomInt ℓ n‖ then ‖LatFourier.latFt ℓ W n‖ ^ 2 else 0) := by
        refine Summable.tsum_le_tsum (fun n => ?_) hg hh
        by_cases hc : uvRad ℓ N < ‖kmomInt ℓ n‖
        · rw [if_pos hc, if_pos hc.le]
        · rw [if_neg hc]; positivity

/-! ## 5. Continuity, measurability and integrability of the pieces -/

lemma norm_latChr (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ‖latChr ℓ n z‖ = 1 := by
  rw [show latChr ℓ n z = Complex.exp (Complex.I *
    ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) from rfl]
  rw [Complex.norm_exp]
  have h : (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  rw [h, Real.exp_zero]

lemma continuous_latChr (ℓ : ℝ) (n : Fin 3 → ℤ) : Continuous (latChr ℓ n) := by
  rw [show latChr ℓ n = fun z : E3 => Complex.exp (Complex.I *
      ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) from rfl]
  fun_prop

lemma continuous_cubeSum (ℓ : ℝ) (N : ℕ) (W : E3 → ℝ) : Continuous (latCubeSum ℓ N W) := by
  unfold latCubeSum
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_latChr ℓ (labVec N k))

lemma continuous_rowSum (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) :
    Continuous (rowSum ℓ fu N W) := by
  unfold rowSum
  exact continuous_finsetSum _ fun k _ =>
    (continuous_const.mul continuous_const).mul (continuous_latChr ℓ (labVec N k))

/-- The periodisation is a.e. strongly measurable on the closed cube. -/
lemma latPer_aesm_latBox {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    AEStronglyMeasurable (LatFourier.latPer ℓ W) (volume.restrict (LatFourier.latBox ℓ)) :=
  ((LatFourier.latPerCut_aestronglyMeasurable hℓ hWm hWs).restrict (s := LatFourier.latBox ℓ)).congr
    ((ae_restrict_iff' (s := LatFourier.latBox ℓ) (LatFourier.measurableSet_latBox ℓ)).mpr
      (Eventually.of_forall fun z hz => by
        rw [LatFourier.latPerCut, Set.indicator_of_mem hz]))

/-- A bounded, a.e. strongly measurable complex function on the closed cube has an integrable
square. -/
lemma integrableOn_latBox_normSq {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (haesm : AEStronglyMeasurable f (volume.restrict (LatFourier.latBox ℓ)))
    (C : ℝ) (hC : ∀ z ∈ LatFourier.latBox ℓ, ‖f z‖ ≤ C) :
    Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (LatFourier.latBox ℓ)) := by
  haveI : IsFiniteMeasure (volume.restrict (LatFourier.latBox ℓ)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ,
      MeasureTheory.measure_congr (latBox_ae_eq_latCell hℓ.le),
      LatFourier.volume_latCell hℓ.le]
    exact ENNReal.ofReal_lt_top
  refine MemLp.integrable (q := 2) (by norm_num) (MemLp.of_bound ?_ ((max C 0) ^ 2) ?_)
  · exact (haesm.norm.mul haesm.norm).congr
      (Eventually.of_forall (fun z => by simp [Pi.mul_apply, sq]))
  · rw [ae_restrict_iff' (LatFourier.measurableSet_latBox ℓ)]
    refine Eventually.of_forall fun z hz => ?_
    have h1 : ‖f z‖ ≤ max C 0 := le_trans (hC z hz) (le_max_left C 0)
    have h0 : 0 ≤ ‖f z‖ := norm_nonneg _
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ h0 h1 2

/-! ## 6. Arithmetic of the cut-off radius -/

lemma uvRad_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N) : 0 < uvRad ℓ N := by
  rw [uvRad]
  have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  positivity

lemma uvRad_mono {ℓ : ℝ} (hℓ : 0 < ℓ) {N N' : ℕ} (h : N ≤ N') : uvRad ℓ N ≤ uvRad ℓ N' := by
  rw [uvRad, uvRad]
  have h1 : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast h
  have h2 : (0 : ℝ) < 2 * Real.pi / ℓ / 4 := by positivity
  nlinarith [h1, h2]

lemma uvRad_eq_div (ℓ : ℝ) (N : ℕ) (hℓ : ℓ ≠ 0) :
    uvRad ℓ N = (N : ℝ) / (4 * ℓ / (2 * Real.pi)) := by
  rw [uvRad]
  field_simp

/-! ## 7. The target -/

theorem latCubeSum_tendsto_L2 {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
        ‖(∑ k : Work.BoseBoxFock.Lab N',
              Submission.BoseGases.kinFT (fun y => (W y : ℂ))
                (Work.BoseBoxFock.kmomLab ℓ N' k)
                * Complex.exp (Complex.I *
                    ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N' k) z : ℝ) : ℂ)))
          - (((ℓ ^ 3 : ℝ) : ℂ)
              * ∑' m : Fin 3 → ℤ, ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))‖ ^ 2)
      ≤ ε := by
  classical
  intro ε hε
  -- a concrete low-pass cut-off for the sibling's row sum
  set fu : Work.BoseBoxFix.LowCut := cutLin with hfu
  -- the sibling convergence, at level `ε/4`
  obtain ⟨N₀, hN₀⟩ :=
    latRowSum_tendsto_L2 (ℓ := ℓ) (R := R) hℓ fu hWm hWb hWs (ε / 4) (by positivity)
  -- the lattice tail, at level `ε/(4ℓ³)`
  obtain ⟨Λ₁, hΛ₁⟩ :=
    kinFT_lattice_tail_sq_lt (ℓ := ℓ) (R := R) hℓ hWb hWs (ε / (4 * ℓ ^ 3)) (by positivity)
  -- the lattice size
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (max (max (N₀ : ℝ) 1) (Λ₁ * (4 * ℓ / (2 * Real.pi))))
  refine ⟨N₁, fun N' hN' => ?_⟩
  have hN₁N' : N₁ ≤ N' := hN'
  have hN₀le : (N₀ : ℝ) ≤ (N₁ : ℝ) :=
    le_trans (le_trans (le_max_left (N₀ : ℝ) 1)
      (le_max_left (max (N₀ : ℝ) 1) (Λ₁ * (4 * ℓ / (2 * Real.pi))))) hN₁
  have h1le : (1 : ℝ) ≤ (N₁ : ℝ) :=
    le_trans (le_trans (le_max_right (N₀ : ℝ) 1)
      (le_max_left (max (N₀ : ℝ) 1) (Λ₁ * (4 * ℓ / (2 * Real.pi))))) hN₁
  have hΛle : Λ₁ * (4 * ℓ / (2 * Real.pi)) ≤ (N₁ : ℝ) :=
    le_trans (le_max_right (max (N₀ : ℝ) 1) (Λ₁ * (4 * ℓ / (2 * Real.pi)))) hN₁
  have hN₁pos : 1 ≤ N₁ := by exact_mod_cast h1le
  have hN'pos : 1 ≤ N' := le_trans hN₁pos hN'
  have hN₀N' : N₀ ≤ N' := by
    have h : (N₀ : ℝ) ≤ (N' : ℝ) := le_trans hN₀le (by exact_mod_cast hN')
    exact_mod_cast h
  have hΛN' : Λ₁ ≤ uvRad ℓ N' := by
    have hc : (0 : ℝ) < 4 * ℓ / (2 * Real.pi) := by positivity
    have h1 : Λ₁ ≤ uvRad ℓ N₁ := by
      rw [uvRad_eq_div ℓ N₁ (ne_of_gt hℓ)]
      exact (le_div_iff₀ hc).mpr hΛle
    exact le_trans h1 (uvRad_mono hℓ hN₁N')
  -- the two integrable pieces on the closed cube
  have hcont1 : Continuous (fun z : E3 => latCubeSum ℓ N' W z - rowSum ℓ fu N' W z) :=
    (continuous_cubeSum ℓ N' W).sub (continuous_rowSum ℓ fu N' W)
  have hcont2 : Continuous (fun z : E3 => rowSum ℓ fu N' W z) := continuous_rowSum ℓ fu N' W
  obtain ⟨D, hD0, hD⟩ := LatFourier.latPer_bdd (ℓ := ℓ) (R := R) hℓ hWb hWs
  set A : ℝ := ∑ k : Lab N', ‖LatFourier.latFt ℓ W (labVec N' k)‖ with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hcube_le : ∀ z : E3, ‖latCubeSum ℓ N' W z‖ ≤ A := by
    intro z
    rw [latCubeSum]
    calc ‖∑ k : Lab N', LatFourier.latFt ℓ W (labVec N' k) * latChr ℓ (labVec N' k) z‖
        ≤ ∑ k : Lab N', ‖LatFourier.latFt ℓ W (labVec N' k) * latChr ℓ (labVec N' k) z‖ :=
          norm_sum_le _ _
      _ = A := by
          rw [hAdef]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_latChr, mul_one]
  have hrow_le : ∀ z : E3, ‖rowSum ℓ fu N' W z‖ ≤ A := by
    intro z
    rw [rowSum, hAdef]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, norm_latChr, mul_one]
    calc ‖((uvCut fu (uvRad ℓ N') (kmomLab ℓ N' k) : ℝ) : ℂ)‖
          * ‖Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N' k)‖
        ≤ 1 * ‖Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N' k)‖ :=
          mul_le_mul_of_nonneg_right
            (norm_ofReal_le_one (fu.nonneg _) (fu.le_one _)) (norm_nonneg _)
      _ = ‖LatFourier.latFt ℓ W (labVec N' k)‖ := by rw [one_mul]; rfl
  have hintSP : Integrable (fun z => ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2)
      (volume.restrict (LatFourier.latBox ℓ)) :=
    integrableOn_latBox_normSq hℓ (hcont1.aestronglyMeasurable.restrict) (2 * A)
      (fun z _ => le_trans (norm_sub_le _ _) (by linarith [hcube_le z, hrow_le z]))
  have hintPG : Integrable
      (fun z => ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2)
      (volume.restrict (LatFourier.latBox ℓ)) :=
    integrableOn_latBox_normSq hℓ
      ((hcont2.aestronglyMeasurable.restrict).sub
        ((latPer_aesm_latBox (ℓ := ℓ) (R := R) hℓ hWm hWs).const_mul _))
      (A + ‖(((ℓ ^ 3 : ℝ) : ℂ))‖ * D)
      (fun z hz => by
        refine le_trans (norm_sub_le _ _) (add_le_add (hrow_le z) ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hD z hz) (norm_nonneg _))
  -- the two estimates over the closed cube
  have hAint : (∫ z in LatFourier.latBox ℓ, ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2)
      ≤ ε / 4 := by
    rw [integral_normSq_cubeSum_sub_rowSum hℓ fu N' W]
    have h1 : (∑ n ∈ Work.BoseRowQ2.cube N',
        ‖(((1 - uvCut fu (uvRad ℓ N') (kmomInt ℓ n) : ℝ)) : ℂ)
          * LatFourier.latFt ℓ W n‖ ^ 2) ≤ ε / (4 * ℓ ^ 3) :=
      le_trans (cubeCoef_sum_le_tail hℓ hN'pos hWm hWb hWs) (hΛ₁ (uvRad ℓ N') hΛN')
    calc ℓ ^ 3 * (∑ n ∈ Work.BoseRowQ2.cube N',
          ‖(((1 - uvCut fu (uvRad ℓ N') (kmomInt ℓ n) : ℝ)) : ℂ)
            * LatFourier.latFt ℓ W n‖ ^ 2)
        ≤ ℓ ^ 3 * (ε / (4 * ℓ ^ 3)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε / 4 := by field_simp
  have hBint : (∫ z in LatFourier.latBox ℓ,
        ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2) ≤ ε / 4 := by
    have h0 : (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
        ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2) ≤ ε / 4 := by
      simpa only [rowSum_sibling_form, latPer_sibling_form] using hN₀ N' hN₀N'
    rw [latTransfer_integral_real hℓ (f := fun z : E3 =>
      ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2)
      (fun m z => by
        show ‖rowSum ℓ fu N' W (z + ℓ • latVec m)
            - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W (z + ℓ • latVec m)‖ ^ 2 = _
        rw [rowSum_add_latVec hℓ fu N' W m z, latPer_add_latVec hℓ W m z])] at h0
    exact h0
  -- the pointwise split and the assembly, on the closed cube
  have hsplit : ∀ z : E3,
      ‖latCubeSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2
        ≤ 2 * ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2
          + 2 * ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2 := by
    intro z
    rw [show latCubeSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z
        = (latCubeSum ℓ N' W z - rowSum ℓ fu N' W z)
          + (rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z) by ring]
    calc ‖(latCubeSum ℓ N' W z - rowSum ℓ fu N' W z)
            + (rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z)‖ ^ 2
        ≤ (‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖
            + ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (norm_add_le _ _) 2
      _ ≤ 2 * (‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2
            + ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2) :=
          add_sq_le
      _ = 2 * ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2
            + 2 * ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2 :=
          by ring
  have hmono : (∫ z in LatFourier.latBox ℓ,
        ‖latCubeSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2)
      ≤ ∫ z in LatFourier.latBox ℓ, (2 * ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2
          + 2 * ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2) :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
      ((hintSP.const_mul 2).add (hintPG.const_mul 2)) (Eventually.of_forall hsplit)
  have hsum : (∫ z in LatFourier.latBox ℓ, (2 * ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2
          + 2 * ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2))
      = 2 * (∫ z in LatFourier.latBox ℓ, ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2)
        + 2 * (∫ z in LatFourier.latBox ℓ,
            ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2) := by
    rw [integral_add (hintSP.const_mul 2) (hintPG.const_mul 2), integral_const_mul,
      integral_const_mul]
  have hmain : (∫ z in LatFourier.latBox ℓ,
      ‖latCubeSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2) ≤ ε := by
    calc (∫ z in LatFourier.latBox ℓ,
          ‖latCubeSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2)
        ≤ ∫ z in LatFourier.latBox ℓ, (2 * ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2
            + 2 * ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2) :=
          hmono
      _ = 2 * (∫ z in LatFourier.latBox ℓ, ‖latCubeSum ℓ N' W z - rowSum ℓ fu N' W z‖ ^ 2)
          + 2 * (∫ z in LatFourier.latBox ℓ,
              ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2) :=
          hsum
      _ ≤ 2 * (ε / 4) + 2 * (ε / 4) := by linarith [hAint, hBint]
      _ = ε := by ring
  -- transfer the target's integral to the closed cube
  rw [show (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
        ‖(∑ k : Work.BoseBoxFock.Lab N',
              Submission.BoseGases.kinFT (fun y => (W y : ℂ))
                (Work.BoseBoxFock.kmomLab ℓ N' k)
                * Complex.exp (Complex.I *
                    ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N' k) z : ℝ) : ℂ)))
          - (((ℓ ^ 3 : ℝ) : ℂ)
              * ∑' m : Fin 3 → ℤ, ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))‖ ^ 2)
      = ∫ z in LatFourier.latBox ℓ,
          ‖latCubeSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2 from
    latTransfer_integral_real hℓ (f := fun z : E3 =>
      ‖latCubeSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W z‖ ^ 2)
      (fun m z => by
        show ‖latCubeSum ℓ N' W (z + ℓ • latVec m)
            - (((ℓ ^ 3 : ℝ) : ℂ)) * LatFourier.latPer ℓ W (z + ℓ • latVec m)‖ ^ 2 = _
        rw [cubeSum_add_latVec (ne_of_gt hℓ) N' W m z, latPer_add_latVec hℓ W m z])]
  exact hmain

end Work.BoseBoxFock
