import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_modSeq
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Ortho
import Submission.Work.BourgainPlan.IonescuWainger.BandLimited

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Toolbox for the band-limited `ℓ²` orthogonality

The `ℓ²` orthogonality of Tao's Lemma `ortho`(ii)/(iii) is proved here by reducing it to the
already established `ℓ¹` theory (`BandLimited.lean`, `FreqArc.lean`) rather than by an induction
on the number of factors:

* given band-limited `f, g ∈ ℓ²(ℤ)`, the pointwise product `f · conj g` is **absolutely summable**
  (product of two `ℓ²`-functions), and its discrete Fourier transform `discFourier (f · conj g)` is
  supported in the Minkowski *difference* `E - D` of the two frequency supports;
* for a family of absolutely summable factors the transform of the product is the iterated
  convolution of the transforms (`discFourier_finprod_eq_circConvFin_l1`), whose support is the
  Minkowski sum of the supports (`circConvFin_succ_eq_zero_of_notMem_setSumFin`);
* the pairing `Σ_m ∏_i f_i(m) · conj (∏_i g_i(m))` is the value at `0` of the transform of
  `∏_i (f_i · conj g_i)`, hence vanishes as soon as `0` is outside `Σ_i (E_i - D_i)`, i.e. as soon
  as `Σ_i E_i` and `Σ_i D_i` are disjoint.
-/

/-- The Minkowski **difference** `E - D = {a - b | a ∈ E, b ∈ D}` of two subsets of the circle
(`setAdd` of `FreqArc.lean` is the Minkowski sum). -/
def setSub (E D : Set Circle) : Set Circle := {x | ∃ a ∈ E, ∃ b ∈ D, a - b = x}

/-- `e^{2πi m·0} = 1`. -/
theorem fourier_apply_zero (m : ℤ) : fourier m (0 : Circle) = 1 := by
  simp [fourier_apply]

/-- `star (fourier m (-θ)) = fourier m θ`. -/
theorem star_fourier_neg_apply (m : ℤ) (θ : Circle) : star (fourier m (-θ)) = fourier m θ := by
  rw [Complex.star_def, ← fourier_neg (n := m) (x := -θ), fourier_apply, neg_zsmul, zsmul_neg,
    neg_neg, ← fourier_apply]

/-- **The transform of `f · conj g` is supported in `E - D`.**  If `f, g ∈ ℓ²(ℤ)` are band-limited
with frequency supports `E` and `D`, then the discrete Fourier transform of the absolutely
summable sequence `m ↦ f m · conj (g m)` vanishes outside the Minkowski difference `E - D`.

Proof: for `ξ ∉ E - D` the modulated sequence `modSeq g (-ξ)` is band-limited with frequency support
`{x | x - ξ ∈ D}` (`hasFreqSupport_modSeq`), a set disjoint from `E`; hence the `ℓ²` pairing
`Σ_m f m · conj (modSeq g (-ξ) m)` vanishes (`tsum_mul_conj_eq_zero_of_disjoint_freqSupport`), and
this pairing is exactly `discFourier (f · conj g) ξ`. -/
theorem discFourier_mul_star_eq_zero_of_notMem_setSub {f g : ℤ → ℂ} (hf : Memℓp f 2)
    (hg : Memℓp g 2) {E D : Set Circle} (hE : HasFreqSupport f hf E)
    (hD : HasFreqSupport g hg D) :
    ∀ ξ : Circle, ξ ∉ setSub E D → discFourier (fun m => f m * star (g m)) ξ = 0 := by
  intro ξ hξ
  have hdisj : Disjoint E {x : Circle | x + (-ξ) ∈ D} := by
    rw [Set.disjoint_left]
    intro x hxE hxD
    exact hξ ⟨x, hxE, x + (-ξ), hxD, by abel⟩
  have hsupp : HasFreqSupport (modSeq g (-ξ)) (memℓp_modSeq hg (-ξ))
      {x : Circle | x + (-ξ) ∈ D} := hasFreqSupport_modSeq hg hD (-ξ)
  have hzero : (∑' m : ℤ, f m * star (modSeq g (-ξ) m)) = 0 :=
    tsum_mul_conj_eq_zero_of_disjoint_freqSupport hf (memℓp_modSeq hg (-ξ)) hE hsupp hdisj
  rw [discFourier]
  have hcongr : (∑' m : ℤ, f m * star (g m) * fourier m ξ)
      = ∑' m : ℤ, f m * star (modSeq g (-ξ) m) := by
    refine tsum_congr fun m => ?_
    simp only [modSeq, star_mul, star_fourier_neg_apply]
    ring
  rw [hcongr, hzero]

/-- **`0` is outside the Minkowski sum of the difference sets** if the two Minkowski sums are
disjoint: if `0 = Σ_i x_i` with `x_i = a_i - b_i`, `a_i ∈ E_i`, `b_i ∈ D_i`, then `Σ_i a_i = Σ_i b_i`
lies in `Σ_i E_i ∩ Σ_i D_i`. -/
theorem not_mem_setSumFin_setSub_of_disjoint {m : ℕ} {E D : Fin m → Set Circle}
    (hdisj : Disjoint (setSumFin m E) (setSumFin m D)) :
    (0 : Circle) ∉ setSumFin m (fun i => setSub (E i) (D i)) := by
  rintro ⟨h, hh, hsum⟩
  simp only [setSub, Set.mem_ofPred_eq] at hh
  choose a ha b hb hEq using hh
  have hsum' : ∑ i, (a i - b i) = 0 := by
    have h1 : ∑ i, (a i - b i) = ∑ i, h i := Finset.sum_congr rfl fun i _ => hEq i
    rw [h1, hsum]
  have hsplit : ∑ i, (a i - b i) = (∑ i, a i) - ∑ i, b i :=
    Finset.sum_sub_distrib (s := Finset.univ) (f := a) (g := b)
  have hAB : ∑ i, a i = ∑ i, b i := by
    rw [hsplit] at hsum'
    exact sub_eq_zero.mp hsum'
  have hA : (∑ i, a i) ∈ setSumFin m E := ⟨a, ha, rfl⟩
  have hB : (∑ i, b i) ∈ setSumFin m D := ⟨b, hb, rfl⟩
  exact (Set.disjoint_left.mp hdisj hA) (hAB.symm ▸ hB)

/-- **Tao's `ortho`(ii)/(iii) for band-limited `ℓ²` major-arc systems.**

For `f i, g i : ℤ → ℂ` square-summable, with Fourier transforms `ftLp (f i) (hf i)` supported
(a.e.) in `E i` and `ftLp (g i) (hg i)` supported in `D i`, if the Minkowski sums `Σ_i E i` and
`Σ_i D i` are disjoint, then the pairing vanishes:

`Σ_m (∏_i f i m) · conj (∏_i g i m) = 0`.

This is the `ℓ²` form of Tao's denominator/numerator orthogonality (`ortho`(ii)/(iii)): the `ℓ¹`
case is `tsum_prod_mul_conj_eq_zero_of_nonce_l1` in `BandLimited`, and the two-factor case
(`n = 0`) is `tsum_mul_conj_eq_zero_of_disjoint_freqSupport` in `FourierL2Ortho`.

The proof is by reduction to the absolutely summable (`ℓ¹`) theory: the factors
`k i := f i · conj (g i)` are absolutely summable (products of two `ℓ²` sequences), so the pairing
is the value at `0` of the transform of the product `∏ i, k i`, which by the `ℓ¹` product rule is
the iterated convolution `✻_i 𝓕(k i)`.  Each `𝓕(k i)` is supported in `E i - D i`, whence the
convolution vanishes at `0` because `0 ∉ Σ_i (E i - D i)` when the Minkowski sums are disjoint. -/
theorem tsum_prod_mul_conj_eq_zero_of_freqSupport {n : ℕ} (f g : Fin (n + 1) → ℤ → ℂ)
    (hf : ∀ i, Memℓp (f i) 2) (hg : ∀ i, Memℓp (g i) 2)
    (E D : Fin (n + 1) → Set Circle) (hE : ∀ i, HasFreqSupport (f i) (hf i) (E i))
    (hD : ∀ i, HasFreqSupport (g i) (hg i) (D i))
    (hdisj : Disjoint (setSumFin (n + 1) E) (setSumFin (n + 1) D)) :
    ∑' m : ℤ, (∏ i, f i m) * star (∏ i, g i m) = 0 := by
  -- Each factor `k i = f i · conj (g i)` is absolutely summable.
  have hk_l1 : ∀ i, Summable fun m : ℤ => ‖f i m * star (g i m)‖ := by
    intro i
    have hff : Summable fun m : ℤ => ‖f i m‖ ^ (2 : ℝ) := by simpa [Memℓp] using hf i
    have hgg : Summable fun m : ℤ => ‖g i m‖ ^ (2 : ℝ) := by simpa [Memℓp] using hg i
    have hsum : Summable fun m : ℤ => ‖f i m‖ ^ (2 : ℝ) + ‖g i m‖ ^ (2 : ℝ) := hff.add hgg
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hsum
    · rw [norm_mul, norm_star, Real.rpow_two, Real.rpow_two]
      nlinarith [sq_nonneg (‖f i m‖ - ‖g i m‖), norm_nonneg (f i m), norm_nonneg (g i m)]
  -- The transform of each factor is supported in `E i - D i`.
  have hsupp : ∀ i, ∀ ξ : Circle, ξ ∉ setSub (E i) (D i) →
      discFourier (fun m => f i m * star (g i m)) ξ = 0 :=
    fun i => discFourier_mul_star_eq_zero_of_notMem_setSub (hf i) (hg i) (hE i) (hD i)
  -- `0` is not in the Minkowski sum of the difference sets.
  have h0 : (0 : Circle) ∉ setSumFin (n + 1) (fun i => setSub (E i) (D i)) :=
    not_mem_setSumFin_setSub_of_disjoint hdisj
  -- The pairing is the value at `0` of the transform of the product of the factors.
  have hstep1 : (∑' m : ℤ, (∏ i, f i m) * star (∏ i, g i m))
      = ∑' m : ℤ, ∏ i, f i m * star (g i m) :=
    tsum_congr fun m => by rw [star_prod, ← Finset.prod_mul_distrib]
  have hstep2 : (∑' m : ℤ, ∏ i, f i m * star (g i m))
      = circConvFin (n + 1) (fun i => discFourier (fun m => f i m * star (g i m))) 0 := by
    have hprod : discFourier (fun m : ℤ => ∏ i, f i m * star (g i m))
        = circConvFin (n + 1) (fun i => discFourier (fun m => f i m * star (g i m))) :=
      discFourier_finprod_eq_circConvFin_l1 (fun i m => f i m * star (g i m)) hk_l1
    rw [← hprod, discFourier]
    refine tsum_congr fun m => ?_
    rw [fourier_apply_zero m, mul_one]
  rw [hstep1, hstep2]
  exact circConvFin_succ_eq_zero_of_notMem_setSumFin n hsupp 0 h0

end Work.BourgainPlan.IonescuWainger
