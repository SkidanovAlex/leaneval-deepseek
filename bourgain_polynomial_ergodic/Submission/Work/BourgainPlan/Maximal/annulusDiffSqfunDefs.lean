import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusSqfun_add_le
import Submission.Work.BourgainPlan.Maximal.annulusConv_finsetSum_eq
import Submission.Work.BourgainPlan.Maximal.czBad_lintegral_compl_czStar_le

/-!
# The *difference* annulus square function

For two annulus symbol families `b`, `b'` the *difference square function*

  `annulusDiffSqfun b b' j f x
     = (∑'_n ‖(K'_{j+n} * f)(x) - (K_{j+n} * f)(x)‖²)^{1/2}`,   `K_m = 𝓕⁻ (b m)`,

is the object whose decay in the base scale `j` is MST's `(eq:51)`: its `L^q` bound (uniform in `j`)
and its `L²` bound with the gain `2^{-δ|j|}` interpolate (Marcinkiewicz, via
`marcinkiewicz_two_strong_memLp`) to the gain `2^{-δ_p|j|}` at every `p`.

This module provides the vocabulary and the elementary structural facts needed to feed that
interpolation:

* `integrable_annulusK_mul` — for `f ∈ L^p` (`1 ≤ p`) each Bochner integrand
  `y ↦ K_m (x - y) · f y` is integrable (Hölder with the Schwartz kernel), which is what makes
  `annulusConv` additive on `L^p`;
* `annulusConv_add_of_memLp` — additivity of `annulusConv` on `L^p` inputs (it *fails* on all
  functions, Mathlib's `MeasureTheory.integral` being `0` off the integrable functions);
* `annulusConv_smul` — homogeneity, which holds unconditionally;
* `annulusDiffSqfun` and its **subadditivity on `L^p` pairs**, **homogeneity** and
  **a.e.-measurability** — the three hypotheses of `marcinkiewicz_two_strong_memLp`.
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- **The Bochner integrand of `annulusConv` is integrable for `f ∈ L^p`, `1 ≤ p`.**  For `p = 1`
the kernel is bounded; for `p > 1` it is Hölder with the kernel in `L^{p'}` (the kernel is
Schwartz, hence in every `L^r`). -/
lemma integrable_annulusK_mul (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ)
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) (x : ℝ) :
    Integrable (fun y : ℝ => annulusK b m (x - y) * f y) volume := by
  by_cases hp1 : p = 1
  · have hf1 : MemLp f 1 volume := by
      rw [hp1, ENNReal.ofReal_one] at hf
      exact hf
    obtain ⟨C, hCpos, hC⟩ := annulusKernel_size b hb hsmooth 0
    have hCbnd : ∀ z : ℝ, ‖annulusK b m z‖ ≤ C * (2 : ℝ) ^ (-m) := by
      intro z
      have h := hC m z
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, annulusK] using h
    have hφ : MemLp (fun y : ℝ => annulusK b m (x - y)) ∞ volume := by
      refine memLp_top_of_bound ?_ (C * (2 : ℝ) ^ (-m)) ?_
      · exact (((continuous_annulusK b hb hsmooth m).comp
          (continuous_const.sub continuous_id))).aestronglyMeasurable
      · filter_upwards with y
        exact hCbnd (x - y)
    exact (memLp_one_iff_integrable.mp hf1).mul_of_top_right hφ
  · have hp1' : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
    have hppos : 0 < p := lt_trans zero_lt_one hp1'
    have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1'
    have hqpos : 0 < p.conjExponent := by
      rw [Real.conjExponent]; exact div_pos hppos (by linarith)
    have hq1 : 1 ≤ p.conjExponent := by
      rw [Real.conjExponent, le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]; linarith
    have hk : MemLp (fun y : ℝ => annulusK b m (x - y))
        (ENNReal.ofReal p.conjExponent) volume :=
      memLp_shifted_annulusK b hb hsmooth m x hq1
    haveI : (ENNReal.ofReal p.conjExponent).HolderTriple (ENNReal.ofReal p) 1 := by
      refine (ENNReal.holderTriple_iff _ _ 1).mpr ?_
      simp only [inv_one]
      rw [← ENNReal.ofReal_inv_of_pos hqpos, ← ENNReal.ofReal_inv_of_pos hppos,
        ← ENNReal.ofReal_add (inv_nonneg.mpr hqpos.le) (inv_nonneg.mpr hppos.le),
        add_comm p.conjExponent⁻¹ p⁻¹, (Real.holderConjugate_iff.mp hpq).2, ENNReal.ofReal_one]
    exact hk.integrable_mul hf

/-- **`annulusConv` is additive on `L^p` inputs** (`1 ≤ p`).  (On all functions additivity fails:
Mathlib's `MeasureTheory.integral` is `0` on non-integrable functions.) -/
lemma annulusConv_add_of_memLp (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ)
    {p : ℝ} (hp : 1 ≤ p) {f g : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume) :
    annulusConv b m (f + g) = annulusConv b m f + annulusConv b m g := by
  funext x
  have hfg : MemLp (f + g) (ENNReal.ofReal p) volume := hf.add hg
  simp only [annulusConv, Pi.add_apply]
  rw [show (fun y : ℝ => annulusK b m (x - y) * (f y + g y))
      = fun y : ℝ => annulusK b m (x - y) * f y + annulusK b m (x - y) * g y by
    funext y; ring]
  rw [MeasureTheory.integral_add (integrable_annulusK_mul b hb hsmooth m hp hf x)
    (integrable_annulusK_mul b hb hsmooth m hp hg x)]

/-- **Homogeneity of `annulusConv`**, unconditionally (in Mathlib, `∫ r * g = r * ∫ g` carries no
integrability hypothesis). -/
lemma annulusConv_smul (b : ℤ → ℝ → ℂ) (m : ℤ) (c : ℂ) (f : ℝ → ℂ) :
    annulusConv b m (c • f) = c • annulusConv b m f := by
  funext x
  have hcongr : (fun y : ℝ => annulusK b m (x - y) * (c * f y))
      = fun y : ℝ => c * (annulusK b m (x - y) * f y) := by
    funext y; ring
  simp only [annulusConv, Pi.smul_apply, smul_eq_mul]
  rw [hcongr, MeasureTheory.integral_const_mul]

/-- **The difference annulus square function** at base scale `j` for the two annulus symbol families
`b`, `b'`. -/
noncomputable def annulusDiffSqfun (b b' : ℤ → ℝ → ℂ) (j : ℤ) (f : ℝ → ℂ) : ℝ → ℝ≥0∞ :=
  fun x => (∑' n : ℤ, ‖annulusConv b' (j + n) f x - annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ))
    ^ ((1 : ℝ) / 2)

/-- **Subadditivity of the difference square function on `L^p` pairs.** -/
lemma annulusDiffSqfun_add_le (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m))
    {p : ℝ} (hp : 1 ≤ p) (j : ℤ) {f g : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume) (x : ℝ) :
    annulusDiffSqfun b b' j (f + g) x ≤ annulusDiffSqfun b b' j f x + annulusDiffSqfun b b' j g x := by
  have hfgu : MemLp (f + g) (ENNReal.ofReal p) volume := hf.add hg
  have hkey : ∀ n : ℤ, annulusConv b' (j + n) (f + g) x - annulusConv b (j + n) (f + g) x
      = (annulusConv b' (j + n) f x - annulusConv b (j + n) f x)
        + (annulusConv b' (j + n) g x - annulusConv b (j + n) g x) := by
    intro n
    rw [annulusConv_add_of_memLp b' hb' hsmooth' (j + n) hp hf hg,
      annulusConv_add_of_memLp b hb hsmooth (j + n) hp hf hg]
    simp only [Pi.add_apply]
    ring
  simp only [annulusDiffSqfun]
  rw [show (∑' n : ℤ, ‖annulusConv b' (j + n) (f + g) x
        - annulusConv b (j + n) (f + g) x‖ₑ ^ (2 : ℝ))
      = ∑' n : ℤ, ‖(annulusConv b' (j + n) f x - annulusConv b (j + n) f x)
          + (annulusConv b' (j + n) g x - annulusConv b (j + n) g x)‖ₑ ^ (2 : ℝ) from
    tsum_congr (fun n => by rw [hkey n])]
  have hmono : (∑' n : ℤ, ‖(annulusConv b' (j + n) f x - annulusConv b (j + n) f x)
        + (annulusConv b' (j + n) g x - annulusConv b (j + n) g x)‖ₑ ^ (2 : ℝ))
      ≤ ∑' n : ℤ, (‖annulusConv b' (j + n) f x - annulusConv b (j + n) f x‖ₑ
          + ‖annulusConv b' (j + n) g x - annulusConv b (j + n) g x‖ₑ) ^ (2 : ℝ) :=
    ENNReal.tsum_le_tsum fun n =>
      ENNReal.rpow_le_rpow (enorm_add_le _ _) (by norm_num)
  exact le_trans (ENNReal.rpow_le_rpow hmono (by norm_num))
    (sqrt_tsum_add_sq_le_two
      (fun n : ℤ => ‖annulusConv b' (j + n) f x - annulusConv b (j + n) f x‖ₑ)
      (fun n : ℤ => ‖annulusConv b' (j + n) g x - annulusConv b (j + n) g x‖ₑ))

/-- **Homogeneity of the difference square function.** -/
lemma annulusDiffSqfun_smul (b b' : ℤ → ℝ → ℂ) (j : ℤ) (c : ℂ) (f : ℝ → ℂ) :
    annulusDiffSqfun b b' j (c • f) = fun x => ‖c‖ₑ * annulusDiffSqfun b b' j f x := by
  funext x
  have hkey : ∀ n : ℤ, annulusConv b' (j + n) (c • f) x - annulusConv b (j + n) (c • f) x
      = c * (annulusConv b' (j + n) f x - annulusConv b (j + n) f x) := by
    intro n
    rw [annulusConv_smul b' (j + n) c f, annulusConv_smul b (j + n) c f]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [annulusDiffSqfun]
  rw [show (∑' n : ℤ, ‖annulusConv b' (j + n) (c • f) x
        - annulusConv b (j + n) (c • f) x‖ₑ ^ (2 : ℝ))
      = ∑' n : ℤ, ‖c * (annulusConv b' (j + n) f x - annulusConv b (j + n) f x)‖ₑ ^ (2 : ℝ)
      from tsum_congr (fun n => by rw [hkey n])]
  rw [show (∑' n : ℤ, ‖c * (annulusConv b' (j + n) f x - annulusConv b (j + n) f x)‖ₑ ^ (2:ℝ))
      = ∑' n : ℤ, ‖c‖ₑ ^ (2:ℝ) * ‖(annulusConv b' (j + n) f x - annulusConv b (j + n) f x)‖ₑ ^ (2:ℝ)
      from tsum_congr (fun n => by rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)])]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

/-- **a.e.-measurability of the difference square function.** -/
lemma aemeasurable_annulusDiffSqfun (b b' : ℤ → ℝ → ℂ) (j : ℤ) {f : ℝ → ℂ}
    (hfae : AEMeasurable f volume) :
    AEMeasurable (annulusDiffSqfun b b' j f) volume := by
  have hconv : ∀ (b₀ : ℤ → ℝ → ℂ) (m : ℤ), AEMeasurable (annulusConv b₀ m f) volume := fun b₀ m =>
    aemeasurable_annulusConv b₀ m hfae (aemeasurable_annulusK b₀ m)
  have hsq : AEMeasurable (fun x => ∑' n : ℤ,
      ‖annulusConv b' (j + n) f x - annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)) volume := by
    refine AEMeasurable.tsum fun n => ?_
    exact ((hconv b' (j + n)).sub (hconv b (j + n))).enorm.pow_const (2 : ℝ)
  exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hsq

end Work.BourgainPlan.Maximal
