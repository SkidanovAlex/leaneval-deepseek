import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusPartitionDefs
import Submission.Work.BourgainPlan.Maximal.annulusSquare_l2
import Submission.Work.BourgainPlan.Maximal.annulusSymbolSmooth_annAtomC
import Submission.Work.BourgainPlan.Maximal.annulusConv_star_pairing
import Submission.Work.BourgainPlan.Maximal.annulusConv_finsetSum_eq
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le

/-!
# Self-adjointness of the annulus projection in the `L^p`--`L^q` pairing

The annulus projection `f ↦ annulusConv annAtomC n f` (`= K_n * f`, `K_n = 𝓕⁻ (annAtomC n)`) is
self-adjoint for the Hermitian pairing `(f, g) ↦ ∫ x, f x * star (g x)` on `L^p × L^q`,
`p, q` Hölder conjugate.  This file proves the general statement for an arbitrary Hermitian `L¹`
kernel (`star (k t) = k (-t)`) and then specialises it to the annulus kernel, whose Hermitian
symmetry comes from `annAtomC n` being real-valued.

The proof is a Fubini computation.  With `Φ x y = k (x - y) * u y * star (w x)` both sides equal
`∫ z, Φ z` (up to relabelling):  the left-hand side by `integral_mul_const`, the right-hand side by
conjugating the inner Bochner integral and using `star (k t) = k (-t)`.  The only analytic input is
the `L¹(volume × volume)`-integrability of `Φ`, obtained from Tonelli, Hölder in `ℝ≥0∞` and Young's
convolution inequality (`|k| ∈ L¹`, `u ∈ L^p`, `w ∈ L^q`, `1/p + 1/q = 1`).
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators FourierTransform Topology

namespace Work.BourgainPlan.Maximal

/-! ## Hermitian symmetry of the annulus kernel -/

/-- **The annulus kernel is Hermitian**: `star (K_n t) = K_n (-t)`.
Since `annAtomC n` is real-valued, conjugating the Bochner integral defining
`𝓕⁻ (annAtomC n) t = ∫ v, Real.fourierChar (v * t) • annAtomC n v` flips the sign of the phase. -/
private lemma annulusK_hermitian_aux (n : ℤ) (t : ℝ) :
    star (annulusK annAtomC n t) = annulusK annAtomC n (-t) := by
  simp only [annulusK]
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  rw [show star (∫ v, Real.fourierChar (inner ℝ v t) • annAtomC n v)
      = ∫ v, star (Real.fourierChar (inner ℝ v t) • annAtomC n v) from by
        rw [Complex.star_def]; exact integral_conj.symm]
  apply integral_congr_ae
  filter_upwards with v
  have harg : (starRingEnd ℂ) (↑(2 * Real.pi * (inner ℝ v t)) * Complex.I)
      = ↑(2 * Real.pi * (inner ℝ v (-t))) * Complex.I := by
    rw [Real.inner_apply, Real.inner_apply, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, annAtomC_apply,
    Complex.star_def]
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, harg]

/-- Norm form of the Hermitian symmetry. -/
private lemma annulusK_hermitian_norm_aux (n : ℤ) (t : ℝ) :
    ‖annulusK annAtomC n t‖ₑ = ‖annulusK annAtomC n (-t)‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  congr 1
  rw [← annulusK_hermitian_aux n t]
  simp

/-- **The annulus kernel is continuous** (it is the inverse Fourier transform of the integrable
function `annAtomC n`). -/
private lemma continuous_annulusK_aux (n : ℤ) : Continuous (annulusK annAtomC n) := by
  have hbint : Integrable (annAtomC n) (volume : Measure ℝ) := integrable_annAtomC n
  rw [annulusK, Real.fourierInv_eq_fourier_comp_neg]
  exact VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner hbint.comp_neg

/-! ## Integrability of the uncurried integrand -/

/-- **The uncurried integrand of the pairing is integrable.**  For `k ∈ L¹`, `u ∈ L^p`, `w ∈ L^q`
with `p, q` Hölder conjugate and `‖k t‖ = ‖k (-t)‖`, the function
`(x, y) ↦ k (x - y) * u y * star (w x)` is integrable for the product measure. -/
private lemma integrable_uncurry_conv_mul_star_aux (k u w : ℝ → ℂ)
    (hk : MemLp k 1 (volume : Measure ℝ)) (hkm : Measurable k)
    (hksym : ∀ t : ℝ, ‖k t‖ = ‖k (-t)‖)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    (hu : MemLp u (ENNReal.ofReal p) (volume : Measure ℝ))
    (hw : MemLp w (ENNReal.ofReal q) (volume : Measure ℝ)) :
    Integrable (fun z : ℝ × ℝ => k (z.1 - z.2) * u z.2 * star (w z.1))
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => k (z.1 - z.2) * u z.2 * star (w z.1))
      (volume.prod volume) :=
    (((hkm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
      hu.aestronglyMeasurable.comp_snd).mul (hw.aestronglyMeasurable.comp_fst).star)
  refine ⟨hmeas, ?_⟩
  change ∫⁻ z : ℝ × ℝ, ‖k (z.1 - z.2) * u z.2 * star (w z.1)‖ₑ < ⊤
  have hksymn : ∀ t : ℝ, ‖k t‖ₑ = ‖k (-t)‖ₑ := fun t => by
    rw [← ofReal_norm, ← ofReal_norm, hksym t]
  have hFpae : AEMeasurable (fun z : ℝ × ℝ => ‖k (z.1 - z.2)‖ₑ * ‖u z.2‖ₑ * ‖w z.1‖ₑ)
      (volume.prod volume) :=
    ((((hkm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).enorm.mul
      (hu.aestronglyMeasurable.comp_snd).enorm).mul
      (hw.aestronglyMeasurable.comp_fst).enorm)
  have hBae : ∀ y : ℝ, AEMeasurable (fun x : ℝ => ‖k (x - y)‖ₑ * ‖w x‖ₑ) volume := fun y =>
    (((hkm.comp (measurable_id.sub (measurable_const : Measurable fun _ : ℝ => y)))
      ).aestronglyMeasurable).enorm.mul hw.aestronglyMeasurable.enorm
  have hBae' : AEMeasurable (fun y : ℝ => ∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ) volume := by
    have hAM : AEMeasurable (fun z : ℝ × ℝ => ‖k (z.2 - z.1)‖ₑ * ‖w z.1‖ₑ)
        (volume.prod volume) :=
      (((hkm.comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable).enorm.mul
        (hw.aestronglyMeasurable.comp_fst).enorm)
    exact hAM.lintegral_prod_left (f := fun a b : ℝ => ‖k (b - a)‖ₑ * ‖w a‖ₑ)
  -- the integrand rewritten as a product of norms
  have h1 : ∫⁻ z : ℝ × ℝ, ‖k (z.1 - z.2) * u z.2 * star (w z.1)‖ₑ
      = ∫⁻ x : ℝ, ∫⁻ y : ℝ, ‖k (x - y)‖ₑ * ‖u y‖ₑ * ‖w x‖ₑ :=
    (lintegral_congr fun z => by rw [enorm_mul, enorm_mul]; simp).trans
      (lintegral_prod _ hFpae)
  rw [h1]
  -- Tonelli: swap the two integrations
  have h2 : (∫⁻ x : ℝ, ∫⁻ y : ℝ, ‖k (x - y)‖ₑ * ‖u y‖ₑ * ‖w x‖ₑ)
      = ∫⁻ y : ℝ, ∫⁻ x : ℝ, ‖k (x - y)‖ₑ * ‖u y‖ₑ * ‖w x‖ₑ :=
    lintegral_lintegral_swap hFpae
  rw [h2]
  -- pull `‖u y‖ₑ` out of the inner integral
  have h3 : ∀ y : ℝ, (∫⁻ x : ℝ, ‖k (x - y)‖ₑ * ‖u y‖ₑ * ‖w x‖ₑ)
      = ‖u y‖ₑ * ∫⁻ x : ℝ, ‖k (x - y)‖ₑ * ‖w x‖ₑ := by
    intro y
    rw [show (fun x : ℝ => ‖k (x - y)‖ₑ * ‖u y‖ₑ * ‖w x‖ₑ)
        = (fun x : ℝ => ‖u y‖ₑ * (‖k (x - y)‖ₑ * ‖w x‖ₑ)) from by
      funext x; ac_rfl]
    rw [lintegral_const_mul'' (‖u y‖ₑ) (hBae y)]
  rw [lintegral_congr h3]
  -- rewrite `k (x - y)` as `k (y - x)` using the norm symmetry
  have h4 : (∫⁻ y : ℝ, ‖u y‖ₑ * (∫⁻ x : ℝ, ‖k (x - y)‖ₑ * ‖w x‖ₑ))
      = ∫⁻ y : ℝ, ‖u y‖ₑ * (∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ) := by
    apply lintegral_congr; intro y
    congr 1
    apply lintegral_congr; intro x
    rw [hksymn (x - y), show -(x - y) = y - x by ring]
  rw [h4]
  -- Hölder in `ℝ≥0∞` against `u`
  have hpu : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hpq.pos.le
  have hqu : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hpq.symm.pos.le
  have hLp : eLpNorm u (ENNReal.ofReal p) volume = (∫⁻ y : ℝ, ‖u y‖ₑ ^ p) ^ (1 / p) := by
    rw [← eLpNorm_enorm u hu.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun y : ℝ => ‖u y‖ₑ)
        (ENNReal.ofReal_ne_zero_iff.mpr hpq.pos) ENNReal.ofReal_ne_top
        hu.aestronglyMeasurable.enorm.aestronglyMeasurable]
    simp only [enorm_eq_self, hpu]
  have hBq : eLpNorm (fun y : ℝ => ∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ)
        (ENNReal.ofReal q) volume
      = (∫⁻ y : ℝ, (∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ) ^ q) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (f := fun y : ℝ => ∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ)
      (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos) ENNReal.ofReal_ne_top
      hBae'.aestronglyMeasurable]
    simp only [enorm_eq_self, hqu]
  have hholder : (∫⁻ y : ℝ, ‖u y‖ₑ * (∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ))
      ≤ eLpNorm u (ENNReal.ofReal p) volume
        * eLpNorm (fun y : ℝ => ∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ)
            (ENNReal.ofReal q) volume := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
      hu.aestronglyMeasurable.enorm hBae'
    simpa only [Pi.mul_apply, hLp, hBq] using h
  -- Young's inequality: `|k| * |w| ∈ L^q`
  have hyoung : eLpNorm (fun y : ℝ => ∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ)
        (ENNReal.ofReal q) volume
      ≤ eLpNorm k 1 volume * eLpNorm w (ENNReal.ofReal q) volume := by
    have h := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal (G := ℝ) (μ := volume)
      (K := fun x : ℝ => ‖k x‖ₑ) (Φ := fun x : ℝ => ‖w x‖ₑ)
      (p := q) (q := q) (r := 1) hpq.symm.lt.le le_rfl (by ring)
      hk.aestronglyMeasurable.enorm hw.aestronglyMeasurable.enorm
    have hK' : eLpNorm (fun x : ℝ => ‖k x‖ₑ) (ENNReal.ofReal 1) volume
        = eLpNorm k 1 volume := by
      rw [ENNReal.ofReal_one, eLpNorm_enorm _ hk.aestronglyMeasurable]
    have hΦ' : eLpNorm (fun x : ℝ => ‖w x‖ₑ) (ENNReal.ofReal q) volume
        = eLpNorm w (ENNReal.ofReal q) volume := eLpNorm_enorm w hw.aestronglyMeasurable
    simpa only [hK', hΦ'] using h
  calc ∫⁻ y : ℝ, ‖u y‖ₑ * (∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ)
      ≤ eLpNorm u (ENNReal.ofReal p) volume
          * eLpNorm (fun y : ℝ => ∫⁻ x : ℝ, ‖k (y - x)‖ₑ * ‖w x‖ₑ)
              (ENNReal.ofReal q) volume := hholder
    _ ≤ eLpNorm u (ENNReal.ofReal p) volume
          * (eLpNorm k 1 volume * eLpNorm w (ENNReal.ofReal q) volume) :=
        mul_le_mul' le_rfl hyoung
    _ < ⊤ := ENNReal.mul_lt_top hu.eLpNorm_lt_top
        (ENNReal.mul_lt_top hk.eLpNorm_lt_top hw.eLpNorm_lt_top)

/-! ## The Fubini computation -/

/-- **Adjointness of convolution with a Hermitian integrable kernel, in the `star` pairing.**
For `star (k t) = k (-t)` and integrable uncurried integrand,
`∫ x, (k * u) x * star (w x) = ∫ x, u x * star ((k * w) x)`. -/
private lemma integral_conv_mul_star_eq (k u w : ℝ → ℂ) (hk : ∀ t : ℝ, star (k t) = k (-t))
    (hint : Integrable (Function.uncurry fun x y : ℝ => k (x - y) * u y * star (w x))
      (volume.prod volume)) :
    ∫ x : ℝ, (∫ y : ℝ, k (x - y) * u y) * star (w x)
      = ∫ x : ℝ, u x * star (∫ y : ℝ, k (x - y) * w y) := by
  have hL : (∫ x : ℝ, (∫ y : ℝ, k (x - y) * u y) * star (w x))
      = ∫ x : ℝ, ∫ y : ℝ, k (x - y) * u y * star (w x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [← MeasureTheory.integral_mul_const (star (w x)) (fun y : ℝ => k (x - y) * u y)]
  have hR : (∫ x : ℝ, u x * star (∫ y : ℝ, k (x - y) * w y))
      = ∫ x : ℝ, ∫ y : ℝ, k (y - x) * u x * star (w y) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [show star (∫ y : ℝ, k (x - y) * w y)
        = ∫ y : ℝ, star (k (x - y) * w y) from by
          rw [Complex.star_def]; exact integral_conj.symm]
    rw [← MeasureTheory.integral_const_mul (u x)]
    apply integral_congr_ae
    filter_upwards with y
    rw [star_mul, hk (x - y), show -(x - y) = y - x by ring]
    ring
  rw [hL, hR]
  rw [integral_integral_swap hint]

/-! ## The general `L^p`--`L^q` pairing -/

/-- **Self-adjointness of convolution with a Hermitian `L¹` kernel in the `L^p`--`L^q` pairing.** -/
private lemma conv_star_pairing_lp (k : ℝ → ℂ)
    (hk1 : MemLp k 1 (volume : Measure ℝ)) (hkm : Measurable k)
    (hksym : ∀ t : ℝ, star (k t) = k (-t))
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    (u w : ℝ → ℂ) (hu : MemLp u (ENNReal.ofReal p) (volume : Measure ℝ))
    (hw : MemLp w (ENNReal.ofReal q) (volume : Measure ℝ)) :
    ∫ x : ℝ, (∫ y : ℝ, k (x - y) * u y) * star (w x)
      = ∫ x : ℝ, u x * star (∫ y : ℝ, k (x - y) * w y) := by
  have hksymn : ∀ t : ℝ, ‖k t‖ = ‖k (-t)‖ := fun t => by
    rw [← hksym t]; simp
  exact integral_conv_mul_star_eq k u w hksym
    (integrable_uncurry_conv_mul_star_aux k u w hk1 hkm hksymn hpq hu hw)

/-! ## The main statement -/

/-- Self-adjointness of the annulus projection in the L^p - L^q pairing: for 1 < p, q the Hölder
conjugate of p, u ∈ L^p and w ∈ L^q, the convolution with the annulus kernel annulusK annAtomC n
(whose symbol annAtomC n is real-valued) satisfies
∫ x, (annulusConv annAtomC n u) x * star (w x) = ∫ x, u x * star ((annulusConv annAtomC n w) x).
Unlike the already-proved annulusConv_star_pairing no L^1 hypothesis is needed on u or w. -/
theorem annulusConvStarPairingLp (n : ℤ) {p q : ℝ} (hp : 1 < p) (hpq : Real.HolderConjugate p q)
    (u w : ℝ → ℂ)
    (hu : MeasureTheory.MemLp u (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hw : MeasureTheory.MemLp w (ENNReal.ofReal q) (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∫ x : ℝ, Work.BourgainPlan.Maximal.annulusConv Work.BourgainPlan.Maximal.annAtomC n u x * star (w x)
      = ∫ x : ℝ, u x * star (Work.BourgainPlan.Maximal.annulusConv Work.BourgainPlan.Maximal.annAtomC n w x) := by
  have hb : AnnulusSymbolSmooth annAtomC := annulusSymbolSmooth_annAtomC
  have hs : ∀ m : ℤ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (annAtomC m) := contDiff_annAtomC
  have hK1 : MemLp (annulusK annAtomC n) 1 (volume : Measure ℝ) := by
    simpa using memLp_annulusK_ofReal annAtomC hb hs n (le_refl (1 : ℝ))
  have hKsym : ∀ t : ℝ, star (annulusK annAtomC n t) = annulusK annAtomC n (-t) :=
    annulusK_hermitian_aux n
  have h := conv_star_pairing_lp (annulusK annAtomC n) hK1 (continuous_annulusK_aux n).measurable
    hKsym hpq u w hu hw
  simpa only [annulusConv] using h

end Work.BourgainPlan.Maximal
