import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1lim_meas_bdd
import Submission.Work.BoseBoxFock.lintegral_periodisation_boxL
import Submission.Work.BoseBoxFock.periodic_double_fold_enorm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_mul_integrable` — integrability of the limit pair kernel against a
bounded, box-supported kernel

`K1lim ℓ W` (`pinQLimDefs`) is the four-term limit pair kernel

    `K1lim ℓ W w y = ℓ⁻³ ( χ(w)χ(y)·latPer3 ℓ W (w−y) − χ(w)θ(y)·pinQBl ℓ W w
                          − θ(w)χ(y)·pinQCl ℓ W y + θ(w)θ(y)·pinQDl ℓ W )`,

and `G` is a bounded, a.e. strongly measurable kernel supported in the box `Λ(ℓ)²`.  The target
says that `(w,y) ↦ K1lim ℓ W w y · G w y` is Lebesgue integrable on `ℝ³ × ℝ³` as soon as the
weight `W` is merely *integrable* (no boundedness, no compact support).

## Route

The three `χ̂`-rows are bounded uniformly in the position (`errBdd_pinQBl_bdd`,
`errBdd_pinQCl_bdd`, `errBdd_pinQDl_bdd`, valid for *every* `W`), the two cutoffs `χ_ℓ`, `θ_Λ` are
bounded by `Mχ` and `1`, and `G` vanishes off `Λ(ℓ)²`, so only the `χχ`-row
`χ(w)χ(y)·latPer3 ℓ W (w−y)` needs real analysis.

The row is handled in `ℝ≥0∞` with the pointwise bound

    `‖latPer3 ℓ W z‖ₑ ≤ ‖(ℓ³ : ℂ)‖ₑ · k1PerEnorm ℓ W z`,
    `k1PerEnorm ℓ W z = ∑'_m ‖W (z + ℓ • latVec m)‖ₑ`  (the periodisation of `‖W‖ₑ`),

and the **tiling identity**
`∫⁻_{z ∈ Λ(ℓ)} k1PerEnorm ℓ W z = ∫⁻ ‖W‖ₑ` (`lintegral_periodisation_boxL`: the translates
`Λ(ℓ) + ℓ•latVec m` tile `ℝ³`), combined with the `ENNReal` twin of the double fold
`∫⁻_{w∈Λ}∫⁻_{y∈Λ} h (w−y) = ℓ³ ∫⁻_{z∈Λ} h z` for `ℤ³`-periodic `h`
(`periodic_double_fold_enorm`).  The resulting bound is

    `∫⁻_p ‖K1lim ℓ W p.1 p.2 · G p.1 p.2‖ₑ
       ≤ Cg·‖(ℓ³)⁻¹‖ₑ·(Mχ²‖(ℓ³:ℂ)‖ₑ + (Mχ·CB + Mχ·CC + CD))·(ℓ³·∫⁻‖W‖ₑ + ℓ⁶)`,

finite because `W ∈ L¹`.  Measurability is `AEStronglyMeasurable` of the four rows
(`latPer3` through the quasi-measure-preserving difference map, the `χ̂`-rows through
`errBdd_pinQBl_aesm`/`errBdd_pinQCl_aesm`).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas -/

/-- The `ℝ≥0∞`-norm of the cast of a real number into `ℂ`. -/
lemma k1enorm_ofReal_cast (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  have h1 : ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |r| := by
    rw [← ofReal_norm]
    congr 1
    exact RCLike.norm_ofReal r
  have h2 : ‖r‖ₑ = ENNReal.ofReal |r| := by
    rw [← ofReal_norm, Real.norm_eq_abs]
  rw [h1, h2]

/-- The sharp box indicator `θ_Λ` is measurable. -/
lemma k1thetaFun_measurable (ℓ : ℝ) : Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  have h : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) := by
    funext z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hz]
  rw [h]
  exact measurable_const.indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)

/-- `‖θ_Λ‖ ≤ 1`. -/
lemma k1thetaFun_enorm_le (ℓ : ℝ) (x : E3) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ x‖ₑ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  split <;> simp

/-- The cutoff `χ_ℓ` is bounded by `(√chiNormSq)⁻¹` (the corpus normalisation `∫χ² = 1`). -/
lemma k1chiScale_norm_le (ℓ : ℝ) (w : E3) :
    ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
  have hnn : 0 ≤ Submission.BoseGases.chiScale ℓ w :=
    Submission.BoseGases.chi_nonneg ((ℓ⁻¹) • w)
  have h1 : ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)‖
      = |Submission.BoseGases.chiScale ℓ w| := RCLike.norm_ofReal _
  rw [h1, abs_of_nonneg hnn]
  exact Submission.BoseGases.chi_le_sqrt_inv ((ℓ⁻¹) • w)

/-- The periodisation of `‖W‖ₑ`: `∑'_m ‖W (z + ℓ • latVec m)‖ₑ`. -/
def k1PerEnorm (ℓ : ℝ) (W : E3 → ℝ) : E3 → ENNReal :=
  fun z => ∑' m : Fin 3 → ℤ, ‖W (z + ℓ • latVec m)‖ₑ

/-- The pointwise bound of the `χχ`-row by the periodisation of `‖W‖ₑ`. -/
lemma k1enorm_latPer3_le (ℓ : ℝ) (W : E3 → ℝ) (z : E3) :
    ‖latPer3 ℓ W z‖ₑ ≤ ‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ₑ * k1PerEnorm ℓ W z := by
  rw [latPer3, k1PerEnorm]
  calc ‖(((ℓ ^ 3 : ℝ)) : ℂ) * LatFourier.latPer ℓ W z‖ₑ
      = ‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ₑ * ‖LatFourier.latPer ℓ W z‖ₑ := enorm_mul _ _
    _ ≤ ‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ₑ
          * (∑' m : Fin 3 → ℤ, ‖((W (z + ℓ • latVec m) : ℝ) : ℂ)‖ₑ) := by
        gcongr
        exact enorm_tsum_le_tsum_enorm
    _ = ‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ₑ * (∑' m : Fin 3 → ℤ, ‖(W (z + ℓ • latVec m))‖ₑ) := by
        congr 1
        exact tsum_congr fun m => k1enorm_ofReal_cast _

/-- The periodisation of an a.e. strongly measurable weight is a.e. measurable. -/
lemma k1aemeasurable_perEnorm {ℓ : ℝ} {W : E3 → ℝ} (hWm : AEStronglyMeasurable W volume) :
    AEMeasurable (k1PerEnorm ℓ W) volume := by
  refine AEMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) (fun m => ?_)
  exact (hWm.comp_measurePreserving
    (measurePreserving_add_right (volume : Measure E3) (ℓ • latVec m))).enorm

/-- The periodisation of `W` composed with the difference map is a.e. measurable for the product
measure. -/
lemma k1aemeasurable_perEnorm_sub {ℓ : ℝ} {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) :
    AEMeasurable (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2)) (volume.prod volume) :=
  ((k1aemeasurable_perEnorm hWm).aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub (volume : Measure E3) (volume : Measure E3))).aemeasurable

/-- The periodisation of `‖W‖ₑ` is `ℓℤ³`-periodic. -/
lemma k1perEnorm_add_latVec (ℓ : ℝ) (W : E3 → ℝ) (m : Fin 3 → ℤ) (z : E3) :
    k1PerEnorm ℓ W (z + ℓ • latVec m) = k1PerEnorm ℓ W z := by
  rw [k1PerEnorm, k1PerEnorm]
  have hstep : ∀ n : Fin 3 → ℤ,
      ‖W ((z + ℓ • latVec m) + ℓ • latVec n)‖ₑ = ‖W (z + ℓ • latVec (m + n))‖ₑ := by
    intro n
    congr 2
    rw [LatFourier.latVec_add, smul_add]
    abel
  simp only [hstep]
  rw [← Equiv.tsum_eq (Equiv.addLeft m) (fun n : Fin 3 → ℤ => ‖W (z + ℓ • latVec n)‖ₑ)]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addLeft]

/-- The triangle inequality for the four-term combination of `K1lim`. -/
lemma k1enorm_sub_sub_add_le (A B C D : ℂ) :
    ‖A - B - C + D‖ₑ ≤ ‖A‖ₑ + ‖B‖ₑ + ‖C‖ₑ + ‖D‖ₑ := by
  calc ‖A - B - C + D‖ₑ ≤ ‖A - B - C‖ₑ + ‖D‖ₑ := enorm_add_le _ _
    _ ≤ (‖A - B‖ₑ + ‖C‖ₑ) + ‖D‖ₑ := add_le_add enorm_sub_le le_rfl
    _ ≤ ((‖A‖ₑ + ‖B‖ₑ) + ‖C‖ₑ) + ‖D‖ₑ :=
        add_le_add (add_le_add enorm_sub_le le_rfl) le_rfl

/-- **The pointwise bound of the kernel** by the four row bounds and the periodisation. -/
lemma k1enorm_K1lim_le {ℓ : ℝ} {W : E3 → ℝ} {Mχ CB CC CD : ℝ} (hMχ0 : 0 ≤ Mχ)
    (hMχ : ∀ w, ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)‖ ≤ Mχ)
    (hCB0 : 0 ≤ CB) (hCB : ∀ w, ‖pinQBl ℓ W w‖ ≤ CB)
    (hCC0 : 0 ≤ CC) (hCC : ∀ y, ‖pinQCl ℓ W y‖ ≤ CC)
    (hCD0 : 0 ≤ CD) (hCD : ‖pinQDl ℓ W‖ ≤ CD) (w y : E3) :
    ‖K1lim ℓ W w y‖ₑ ≤ ‖(((ℓ ^ 3)⁻¹ : ℝ) : ℂ)‖ₑ *
      (ENNReal.ofReal Mχ * ENNReal.ofReal Mχ * ‖latPer3 ℓ W (w - y)‖ₑ
        + ENNReal.ofReal Mχ * ENNReal.ofReal CB
        + ENNReal.ofReal Mχ * ENNReal.ofReal CC + ENNReal.ofReal CD) := by
  have hχw : ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal Mχ := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal_iff hMχ0).mpr (hMχ w)
  have hχy : ‖((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal Mχ := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal_iff hMχ0).mpr (hMχ y)
  have hCB' : ‖pinQBl ℓ W w‖ₑ ≤ ENNReal.ofReal CB := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal_iff hCB0).mpr (hCB w)
  have hCC' : ‖pinQCl ℓ W y‖ₑ ≤ ENNReal.ofReal CC := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal_iff hCC0).mpr (hCC y)
  have hCD' : ‖pinQDl ℓ W‖ₑ ≤ ENNReal.ofReal CD := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal_iff hCD0).mpr hCD
  have hθw := k1thetaFun_enorm_le ℓ w
  have hθy := k1thetaFun_enorm_le ℓ y
  have hT1 : ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y)‖ₑ
      ≤ ENNReal.ofReal Mχ * ENNReal.ofReal Mχ * ‖latPer3 ℓ W (w - y)‖ₑ := by
    rw [enorm_mul, enorm_mul]
    gcongr
  have hT2 : ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w‖ₑ
      ≤ ENNReal.ofReal Mχ * ENNReal.ofReal CB := by
    rw [enorm_mul, enorm_mul]
    calc (‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)‖ₑ
          * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ₑ) * ‖pinQBl ℓ W w‖ₑ
        ≤ (ENNReal.ofReal Mχ * 1) * ENNReal.ofReal CB := by gcongr
      _ = ENNReal.ofReal Mχ * ENNReal.ofReal CB := by rw [mul_one]
  have hT3 : ‖Work.BoseK15.corpusBox.thetaFun ℓ w
        * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y‖ₑ
      ≤ ENNReal.ofReal Mχ * ENNReal.ofReal CC := by
    rw [enorm_mul, enorm_mul]
    calc (‖Work.BoseK15.corpusBox.thetaFun ℓ w‖ₑ
          * ‖(((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)‖ₑ) * ‖pinQCl ℓ W y‖ₑ
        ≤ (1 * ENNReal.ofReal Mχ) * ENNReal.ofReal CC := by gcongr
      _ = ENNReal.ofReal Mχ * ENNReal.ofReal CC := by rw [one_mul]
  have hT4 : ‖Work.BoseK15.corpusBox.thetaFun ℓ w
        * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQDl ℓ W‖ₑ ≤ ENNReal.ofReal CD := by
    rw [enorm_mul, enorm_mul]
    calc (‖Work.BoseK15.corpusBox.thetaFun ℓ w‖ₑ
          * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ₑ) * ‖pinQDl ℓ W‖ₑ
        ≤ (1 * 1) * ENNReal.ofReal CD := by gcongr
      _ = ENNReal.ofReal CD := by rw [one_mul, one_mul]
  rw [K1lim, enorm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  exact le_trans (k1enorm_sub_sub_add_le _ _ _ _)
    (add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4)

/-- **The pointwise bound for the integrand**: the product `K1lim ℓ W w y · G w y` is dominated by
a constant times the indicator of `Λ(ℓ)²` of `k1PerEnorm ℓ W (w−y) + 1`. -/
lemma k1enorm_mul_le {l : ℝ} {W : E3 → ℝ} {G : E3 → E3 → ℂ}
    (hGs : Function.support (Function.uncurry G) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL l) (Work.BoseK15.corpusBox.boxL l))
    {Cg M CB CC CD : ℝ} (hCg0 : 0 ≤ Cg) (hCg : ∀ w y, ‖G w y‖ ≤ Cg)
    (hM0 : 0 ≤ M) (hMle : ∀ w, ‖((Submission.BoseGases.chiScale l w : ℝ) : ℂ)‖ ≤ M)
    (hCB0 : 0 ≤ CB) (hCB : ∀ w, ‖pinQBl l W w‖ ≤ CB)
    (hCC0 : 0 ≤ CC) (hCC : ∀ y, ‖pinQCl l W y‖ ≤ CC)
    (hCD0 : 0 ≤ CD) (hCD : ‖pinQDl l W‖ ≤ CD) :
    ∀ p : E3 × E3, ‖K1lim l W p.1 p.2 * G p.1 p.2‖ₑ ≤
      (ENNReal.ofReal Cg * ‖(((l ^ 3)⁻¹ : ℝ) : ℂ)‖ₑ *
        (ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ
          + (ENNReal.ofReal M * ENNReal.ofReal CB + ENNReal.ofReal M * ENNReal.ofReal CC
              + ENNReal.ofReal CD)))
      * (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
          (fun p : E3 × E3 => k1PerEnorm l W (p.1 - p.2) + 1) p := by
  intro p
  by_cases hp : p ∈ Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l
  · have h1 : ‖G p.1 p.2‖ₑ ≤ ENNReal.ofReal Cg := by
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_le_ofReal_iff hCg0).mpr (hCg p.1 p.2)
    have h2 := k1enorm_K1lim_le (ℓ := l) hM0 hMle hCB0 hCB hCC0 hCC hCD0 hCD p.1 p.2
    have h3 : ENNReal.ofReal M * ENNReal.ofReal M * ‖latPer3 l W (p.1 - p.2)‖ₑ
        ≤ (ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ)
            * k1PerEnorm l W (p.1 - p.2) := by
      calc ENNReal.ofReal M * ENNReal.ofReal M * ‖latPer3 l W (p.1 - p.2)‖ₑ
          ≤ ENNReal.ofReal M * ENNReal.ofReal M
              * (‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ * k1PerEnorm l W (p.1 - p.2)) := by
            gcongr
            exact k1enorm_latPer3_le l W _
        _ = (ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ)
              * k1PerEnorm l W (p.1 - p.2) := by ac_rfl
    have hshape : (ENNReal.ofReal M * ENNReal.ofReal M * ‖latPer3 l W (p.1 - p.2)‖ₑ
            + ENNReal.ofReal M * ENNReal.ofReal CB
            + ENNReal.ofReal M * ENNReal.ofReal CC + ENNReal.ofReal CD)
          = ENNReal.ofReal M * ENNReal.ofReal M * ‖latPer3 l W (p.1 - p.2)‖ₑ
            + (ENNReal.ofReal M * ENNReal.ofReal CB
              + ENNReal.ofReal M * ENNReal.ofReal CC + ENNReal.ofReal CD) := by abel
    have hsum : (ENNReal.ofReal M * ENNReal.ofReal M * ‖latPer3 l W (p.1 - p.2)‖ₑ
            + ENNReal.ofReal M * ENNReal.ofReal CB
            + ENNReal.ofReal M * ENNReal.ofReal CC + ENNReal.ofReal CD)
          ≤ (ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ
              + (ENNReal.ofReal M * ENNReal.ofReal CB
                + ENNReal.ofReal M * ENNReal.ofReal CC + ENNReal.ofReal CD))
            * (k1PerEnorm l W (p.1 - p.2) + 1) := by
      rw [hshape, add_mul]
      refine add_le_add ?_ ?_
      · exact le_trans h3 (mul_le_mul_of_nonneg_left (le_add_right le_rfl) (by simp))
      · calc (ENNReal.ofReal M * ENNReal.ofReal CB + ENNReal.ofReal M * ENNReal.ofReal CC
              + ENNReal.ofReal CD)
            = (ENNReal.ofReal M * ENNReal.ofReal CB + ENNReal.ofReal M * ENNReal.ofReal CC
                + ENNReal.ofReal CD) * 1 := (mul_one _).symm
          _ ≤ (ENNReal.ofReal M * ENNReal.ofReal CB + ENNReal.ofReal M * ENNReal.ofReal CC
                + ENNReal.ofReal CD) * (k1PerEnorm l W (p.1 - p.2) + 1) :=
              mul_le_mul_of_nonneg_left (le_add_left (le_rfl : (1 : ENNReal) ≤ 1)) (by simp)
    calc ‖K1lim l W p.1 p.2 * G p.1 p.2‖ₑ
        = ‖K1lim l W p.1 p.2‖ₑ * ‖G p.1 p.2‖ₑ := enorm_mul _ _
      _ ≤ (‖(((l ^ 3)⁻¹ : ℝ) : ℂ)‖ₑ
            * (ENNReal.ofReal M * ENNReal.ofReal M * ‖latPer3 l W (p.1 - p.2)‖ₑ
              + ENNReal.ofReal M * ENNReal.ofReal CB
              + ENNReal.ofReal M * ENNReal.ofReal CC + ENNReal.ofReal CD))
            * ENNReal.ofReal Cg := mul_le_mul h2 h1 (by simp) (by simp)
      _ ≤ (‖(((l ^ 3)⁻¹ : ℝ) : ℂ)‖ₑ
            * ((ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ
                + (ENNReal.ofReal M * ENNReal.ofReal CB
                  + ENNReal.ofReal M * ENNReal.ofReal CC + ENNReal.ofReal CD))
              * (k1PerEnorm l W (p.1 - p.2) + 1)))
            * ENNReal.ofReal Cg := by
          refine mul_le_mul_of_nonneg_right ?_ (by simp)
          exact mul_le_mul_of_nonneg_left hsum (by simp)
      _ = (ENNReal.ofReal Cg * ‖(((l ^ 3)⁻¹ : ℝ) : ℂ)‖ₑ *
            (ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ
              + (ENNReal.ofReal M * ENNReal.ofReal CB
                + ENNReal.ofReal M * ENNReal.ofReal CC + ENNReal.ofReal CD)))
            * (Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l).indicator
                (fun p : E3 × E3 => k1PerEnorm l W (p.1 - p.2) + 1) p := by
          rw [Set.indicator_of_mem hp]
          ac_rfl
  · rw [Set.indicator_of_notMem hp]
    have hG0 : G p.1 p.2 = 0 := by
      by_contra hne
      exact hp (hGs (Function.mem_support.mpr hne))
    rw [hG0, mul_zero, enorm_zero]
    simp

/-- **The integrated bound for the `χχ`-row**: the indicator of `Λ(ℓ)²` times `latPer3 ℓ W`
integrated against the product measure is bounded by `ℓ³ ∫⁻‖W‖ₑ`. -/
theorem k1lintegral_indicator_perEnorm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) :
    (∫⁻ p : E3 × E3,
      ((Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
        (fun p => k1PerEnorm ℓ W (p.1 - p.2))) p)
      ≤ ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z, ‖W z‖ₑ := by
  have hprod : (∫⁻ p in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
        k1PerEnorm ℓ W (p.1 - p.2))
      = ∫⁻ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫⁻ y in Work.BoseK15.corpusBox.boxL ℓ, k1PerEnorm ℓ W (w - y) :=
    MeasureTheory.setLIntegral_prod (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
      (s := Work.BoseK15.corpusBox.boxL ℓ) (t := Work.BoseK15.corpusBox.boxL ℓ)
      (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2))
      (((k1aemeasurable_perEnorm_sub hWm).aestronglyMeasurable.mono_measure
        MeasureTheory.Measure.restrict_le_self).aemeasurable)
  have hBm : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
  calc ∫⁻ p, (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
          (fun p => k1PerEnorm ℓ W (p.1 - p.2)) p
      = ∫⁻ p in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
          k1PerEnorm ℓ W (p.1 - p.2) := MeasureTheory.lintegral_indicator hBm _
    _ = ∫⁻ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫⁻ y in Work.BoseK15.corpusBox.boxL ℓ, k1PerEnorm ℓ W (w - y) := hprod
    _ = ENNReal.ofReal (ℓ ^ 3) *
          ∫⁻ z in Work.BoseK15.corpusBox.boxL ℓ, k1PerEnorm ℓ W z :=
        periodic_double_fold_enorm hℓ (fun m z => k1perEnorm_add_latVec ℓ W m z)
    _ ≤ ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z, ‖W z‖ₑ :=
        le_of_eq (congrArg (fun t => ENNReal.ofReal (ℓ ^ 3) * t)
          (lintegral_periodisation_boxL hℓ hWm.aemeasurable))

/-- **The integrated majorant**: the indicator of `Λ(ℓ)²` times `k1PerEnorm ℓ W + 1` is finite,
with the explicit bound `ℓ³∫⁻‖W‖ₑ + ℓ⁶`. -/
theorem k1lintegral_indicator_add_le {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) (hWm : AEStronglyMeasurable W volume) :
    (∫⁻ p : E3 × E3,
        (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
          (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2) + 1) p)
      ≤ (ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z, ‖W z‖ₑ)
          + ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (ℓ ^ 3) := by
  have hBm : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
  have hsplit : ∀ p : E3 × E3,
      (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
        (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2) + 1) p
      = (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
          (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2)) p
        + (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
          (fun _ : E3 × E3 => (1 : ENNReal)) p := fun p =>
    congrFun (Set.indicator_add (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
      (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2)) (fun _ : E3 × E3 => (1 : ENNReal))) p
  have hAEM : AEMeasurable (fun p : E3 × E3 =>
      (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
        (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2)) p) volume :=
    (k1aemeasurable_perEnorm_sub hWm).indicator hBm
  have hIndPer := k1lintegral_indicator_perEnorm_le hℓ hWm
  have hIndOne : (∫⁻ p : E3 × E3,
      (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
        (fun _ : E3 × E3 => (1 : ENNReal)) p)
      = ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (ℓ ^ 3) := by
    rw [MeasureTheory.lintegral_indicator hBm, MeasureTheory.setLIntegral_const, one_mul,
      show (volume : Measure (E3 × E3)) = (volume : Measure E3).prod (volume : Measure E3)
        from rfl,
      MeasureTheory.Measure.prod_prod,
      Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ]
  calc ∫⁻ p, (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
          (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2) + 1) p
      = ∫⁻ p, ((Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
            (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2)) p
          + (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
            (fun _ : E3 × E3 => (1 : ENNReal)) p) := lintegral_congr hsplit
    _ = (∫⁻ p, (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
            (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2)) p)
          + ∫⁻ p, (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
            (fun _ : E3 × E3 => (1 : ENNReal)) p := lintegral_add_left' hAEM _
    _ ≤ (ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z, ‖W z‖ₑ)
          + ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (ℓ ^ 3) := by
        rw [hIndOne]
        exact add_le_add hIndPer le_rfl

/-- **Finiteness of the majorant at an arbitrary finite constant**: for `a ≠ ⊤`,
`∫⁻ p, a · 1_{Λ(ℓ)²}(p)(k1PerEnorm ℓ W (p.1−p.2) + 1) < ⊤`. -/
theorem k1lintegral_majorant_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) (hWm : AEStronglyMeasurable W volume)
    {a : ENNReal} (ha : a ≠ ⊤) :
    (∫⁻ p : E3 × E3, a *
        (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
          (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2) + 1) p) < ⊤ := by
  have hid := k1lintegral_indicator_add_le hℓ hWi hWm
  have hXtop : (ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z, ‖W z‖ₑ)
      + ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (ℓ ^ 3) < ⊤ :=
    ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) hWi.hasFiniteIntegral,
       ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
        (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)⟩
  calc ∫⁻ p, a * (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
          (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2) + 1) p
      = a * ∫⁻ p, (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ).indicator
            (fun p : E3 × E3 => k1PerEnorm ℓ W (p.1 - p.2) + 1) p :=
        lintegral_const_mul' a _ ha
    _ ≤ a * ((ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z, ‖W z‖ₑ)
          + ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (ℓ ^ 3)) :=
        mul_le_mul_of_nonneg_left hid (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ha) hXtop

/-- **Measurability of the integrand** at an a.e. strongly measurable weight. -/
lemma k1aestronglyMeasurable_K1lim_mul {l : ℝ} {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) {G : E3 → E3 → ℂ}
    (hGm : AEStronglyMeasurable (Function.uncurry G) volume) :
    AEStronglyMeasurable (fun p : E3 × E3 => K1lim l W p.1 p.2 * G p.1 p.2) volume := by
  have hχ1 : AEStronglyMeasurable (fun p : E3 × E3 =>
      ((Submission.BoseGases.chiScale l p.1 : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp
      ((Submission.BoseGases.chiScale_continuous l).comp continuous_fst)).aestronglyMeasurable
  have hχ2 : AEStronglyMeasurable (fun p : E3 × E3 =>
      ((Submission.BoseGases.chiScale l p.2 : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp
      ((Submission.BoseGases.chiScale_continuous l).comp continuous_snd)).aestronglyMeasurable
  have hθ1 : AEStronglyMeasurable (fun p : E3 × E3 =>
      Work.BoseK15.corpusBox.thetaFun l p.1) volume :=
    ((k1thetaFun_measurable l).comp measurable_fst).aestronglyMeasurable
  have hθ2 : AEStronglyMeasurable (fun p : E3 × E3 =>
      Work.BoseK15.corpusBox.thetaFun l p.2) volume :=
    ((k1thetaFun_measurable l).comp measurable_snd).aestronglyMeasurable
  have hlat : AEStronglyMeasurable (fun p : E3 × E3 => latPer3 l W (p.1 - p.2)) volume :=
    (errBdd_latPer3_aesm hWm).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub (volume : Measure E3) (volume : Measure E3))
  have hBq : AEStronglyMeasurable (fun p : E3 × E3 => pinQBl l W p.1) volume :=
    (errBdd_pinQBl_aesm (ℓ := l) (W := W)).comp_quasiMeasurePreserving
      MeasureTheory.Measure.quasiMeasurePreserving_fst
  have hCq : AEStronglyMeasurable (fun p : E3 × E3 => pinQCl l W p.2) volume :=
    (errBdd_pinQCl_aesm (ℓ := l) (W := W)).comp_quasiMeasurePreserving
      MeasureTheory.Measure.quasiMeasurePreserving_snd
  have hDq : AEStronglyMeasurable (fun _ : E3 × E3 => pinQDl l W) volume :=
    aestronglyMeasurable_const
  have h1 : AEStronglyMeasurable (fun p : E3 × E3 =>
      (((Submission.BoseGases.chiScale l p.1 : ℝ)) : ℂ)
        * (((Submission.BoseGases.chiScale l p.2 : ℝ)) : ℂ) * latPer3 l W (p.1 - p.2)) volume :=
    (hχ1.mul hχ2).mul hlat
  have h2 : AEStronglyMeasurable (fun p : E3 × E3 =>
      (((Submission.BoseGases.chiScale l p.1 : ℝ)) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun l p.2 * pinQBl l W p.1) volume :=
    (hχ1.mul hθ2).mul hBq
  have h3 : AEStronglyMeasurable (fun p : E3 × E3 =>
      Work.BoseK15.corpusBox.thetaFun l p.1
        * (((Submission.BoseGases.chiScale l p.2 : ℝ)) : ℂ) * pinQCl l W p.2) volume :=
    (hθ1.mul hχ2).mul hCq
  have h4 : AEStronglyMeasurable (fun p : E3 × E3 =>
      Work.BoseK15.corpusBox.thetaFun l p.1
        * Work.BoseK15.corpusBox.thetaFun l p.2 * pinQDl l W) volume :=
    (hθ1.mul hθ2).mul hDq
  have hbr : AEStronglyMeasurable (fun p : E3 × E3 =>
      (((Submission.BoseGases.chiScale l p.1 : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale l p.2 : ℝ)) : ℂ) * latPer3 l W (p.1 - p.2)
        - (((Submission.BoseGases.chiScale l p.1 : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun l p.2 * pinQBl l W p.1
        - Work.BoseK15.corpusBox.thetaFun l p.1
          * (((Submission.BoseGases.chiScale l p.2 : ℝ)) : ℂ) * pinQCl l W p.2
        + Work.BoseK15.corpusBox.thetaFun l p.1
          * Work.BoseK15.corpusBox.thetaFun l p.2 * pinQDl l W) volume :=
    ((h1.sub h2).sub h3).add h4
  have hK1 : AEStronglyMeasurable (fun p : E3 × E3 => K1lim l W p.1 p.2) volume := by
    have hc : AEStronglyMeasurable
        (fun _ : E3 × E3 => (((l ^ 3)⁻¹ : ℝ) : ℂ)) volume := aestronglyMeasurable_const
    have hmul := hc.mul hbr
    convert hmul using 2 with p
    simp only [K1lim, Pi.mul_apply]
  exact hK1.mul (show AEStronglyMeasurable (fun p : E3 × E3 => G p.1 p.2) volume from hGm)

/-! ## The target -/

theorem K1lim_mul_integrable {l : ℝ} (hl : 0 < l) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWi : MeasureTheory.Integrable W)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hGm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G) MeasureTheory.volume)
    (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C)
    (hGs : Function.support (Function.uncurry G) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL l) (Work.BoseK15.corpusBox.boxL l)) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseBoxFock.K1lim l W p.1 p.2 * G p.1 p.2)
      (MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) := by
  set M : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hMle : ∀ w, ‖((Submission.BoseGases.chiScale l w : ℝ) : ℂ)‖ ≤ M := fun w => by
    rw [hMdef]; exact k1chiScale_norm_le l w
  obtain ⟨Cg, hCg⟩ := hGb
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (G 0 0)) (hCg 0 0)
  have hWme : AEStronglyMeasurable W volume := hWi.aestronglyMeasurable
  obtain ⟨CB, hCB0, hCB⟩ := errBdd_pinQBl_bdd hl W
  obtain ⟨CC, hCC0, hCC⟩ := errBdd_pinQCl_bdd hl W
  obtain ⟨CD, hCD0, hCD⟩ := errBdd_pinQDl_bdd hl W
  have hpt := k1enorm_mul_le (l := l) (W := W) (G := G) hGs hCg0 hCg hM0 hMle
    hCB0 hCB hCC0 hCC hCD0 hCD
  have hAne : ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      enorm_ne_top
  have hCne : ENNReal.ofReal M * ENNReal.ofReal CB + ENNReal.ofReal M * ENNReal.ofReal CC
      + ENNReal.ofReal CD ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
       ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩
  have hne : ENNReal.ofReal Cg * ‖(((l ^ 3)⁻¹ : ℝ) : ℂ)‖ₑ *
      (ENNReal.ofReal M * ENNReal.ofReal M * ‖(((l ^ 3 : ℝ)) : ℂ)‖ₑ
        + (ENNReal.ofReal M * ENNReal.ofReal CB + ENNReal.ofReal M * ENNReal.ofReal CC
            + ENNReal.ofReal CD)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)
      (ENNReal.add_ne_top.mpr ⟨hAne, hCne⟩)
  exact ⟨k1aestronglyMeasurable_K1lim_mul hWme hGm,
    lt_of_le_of_lt (lintegral_mono hpt) (k1lintegral_majorant_lt_top hl hWi hWme hne)⟩

end Work.BoseBoxFock
