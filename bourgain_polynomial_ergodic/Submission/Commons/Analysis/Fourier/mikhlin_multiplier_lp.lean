import Mathlib
import Submission.Commons.Analysis.CalderonZygmund.cz_shift
import Submission.Commons.Analysis.Fourier.block_maximal_of_separated
import Submission.Commons.Analysis.Fourier.dyadic_linearized_l3

open _root_.MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

namespace Commons.Analysis.Fourier

open Commons.Analysis.CalderonZygmund

noncomputable section

set_option maxHeartbeats 4000000

/-- Split `ℤ` at `L`: `{L, L-1, L-2, …} ∪ {L+1, L+2, …}`. -/
def intSplitEquiv (L : ℤ) : ℕ ⊕ ℕ ≃ ℤ where
  toFun x := match x with | Sum.inl n => L - n | Sum.inr n => L + 1 + n
  invFun z := if z ≤ L then Sum.inl (L - z).toNat else Sum.inr (z - L - 1).toNat
  left_inv := by
    rintro (n | n)
    · have h : L - (n : ℤ) ≤ L := by omega
      show (if L - ↑n ≤ L then Sum.inl (L - (L - ↑n)).toNat else Sum.inr _) = Sum.inl n
      rw [if_pos h]
      congr 1
      have h2 : L - (L - (n : ℤ)) = (n : ℤ) := by ring
      rw [h2, Int.toNat_natCast]
    · have h : ¬ (L + 1 + (n : ℤ) ≤ L) := by omega
      show (if L + 1 + ↑n ≤ L then Sum.inl _ else Sum.inr (L + 1 + ↑n - L - 1).toNat) = Sum.inr n
      rw [if_neg h]
      congr 1
      have h2 : L + 1 + (n : ℤ) - L - 1 = (n : ℤ) := by ring
      rw [h2, Int.toNat_natCast]
  right_inv := by
    intro z
    show (match (if z ≤ L then Sum.inl (L - z).toNat else Sum.inr (z - L - 1).toNat) with
        | Sum.inl n => L - n | Sum.inr n => L + 1 + n) = z
    by_cases hz : z ≤ L
    · rw [if_pos hz]
      have h2 : L - (L - z).toNat = z := by
        rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ L - z)]; ring
      exact h2
    · rw [if_neg hz]
      have h2 : L + 1 + (z - L - 1).toNat = z := by
        rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ z - L - 1)]; ring
      exact h2

/-- Splitting a sum over `ℤ` at `L` (for summable families). -/
lemma tsum_int_split (f : ℤ → ℝ) (L : ℤ) (h1 : Summable (fun n : ℕ => f (L - n)))
    (h2 : Summable (fun n : ℕ => f (L + 1 + n))) :
    ∑' l : ℤ, f l = (∑' n : ℕ, f (L - n)) + (∑' n : ℕ, f (L + 1 + n)) := by
  rw [← Equiv.tsum_eq (intSplitEquiv L) f]
  exact Summable.tsum_sum h1 h2


lemma dlb_mul_left_quasiMeasurePreserving (σ : ℝ) (hσ : σ ≠ 0) :
    Measure.QuasiMeasurePreserving (fun z : ℝ => σ * z) (volume : Measure ℝ) volume :=
  ⟨measurable_const.mul measurable_id, by
    rw [Real.map_volume_mul_left hσ]
    exact Measure.smul_absolutelyContinuous⟩

/-- **The trivial Fourier bound** (the commons form, restated for convenience):
`‖𝓕 f x‖ ≤ ∫ y, ‖f y‖`. -/
lemma dlb_fourier_enorm_le_integral (f : ℝ → ℂ) (x : ℝ) :
    ‖FourierTransform.fourier f x‖ ≤ ∫ y : ℝ, ‖f y‖ :=
  Commons.Analysis.CalderonZygmund.norm_fourier_le f x

/-- **Integration by parts twice**: for a `C²` function with integrable derivatives,
`‖𝓕 f x‖ ≤ (2π|x|)^{-2} ∫ y, ‖f'' y‖`. -/

lemma dlb_fourier_enorm_le_inv_sq {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (h0 : Integrable f volume) (h1 : Integrable (iteratedDeriv 1 f) volume)
    (h2 : Integrable (iteratedDeriv 2 f) volume) (x : ℝ) (hx : x ≠ 0) :
    ‖FourierTransform.fourier f x‖
      ≤ (2 * Real.pi * |x|) ^ (-2 : ℤ) * ∫ y : ℝ, ‖iteratedDeriv 2 f y‖ := by
  have hF : FourierTransform.fourier (iteratedDeriv 2 f)
      = fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2 •
          FourierTransform.fourier f x :=
    Real.fourier_iteratedDeriv (f := f) (N := (2 : ℕ∞)) (n := 2) hf
      (by intro n hn
          have hn' : n ≤ 2 := ENat.coe_le_coe.mp hn
          interval_cases n
          · simpa using h0
          · simpa using h1
          · simpa using h2) (by norm_num)
  have hnormeq : ∀ y : ℝ,
      ‖2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)‖ = 2 * Real.pi * |y| := by
    intro y
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (y : ℂ)
        = (((2 * Real.pi * y : ℝ)) : ℂ) * Complex.I from by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    ring
  have hne : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ≠ 0 := by
    intro h
    have : 2 * Real.pi * |x| = 0 := by rw [← hnormeq x, h, norm_zero]
    have hx0 : |x| = 0 := by
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' (by positivity)
      · exact h'
    exact hx (abs_eq_zero.mp hx0)
  have hx2 : FourierTransform.fourier f x
      = ((2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2)⁻¹ •
          FourierTransform.fourier (iteratedDeriv 2 f) x := by
    rw [congrFun hF x, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hne), one_smul]
  have hnorm2 : ‖((2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2)⁻¹‖
      = (2 * Real.pi * |x|) ^ (-2 : ℤ) := by
    rw [norm_inv, norm_pow, hnormeq x,
      show ((2 * Real.pi * |x|) ^ 2)⁻¹ = (2 * Real.pi * |x|) ^ (-2 : ℤ) from by
        rw [zpow_neg, zpow_ofNat]]
  rw [hx2]
  calc ‖((2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2)⁻¹ •
        FourierTransform.fourier (iteratedDeriv 2 f) x‖
      ≤ ‖((2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2)⁻¹‖
          * ‖FourierTransform.fourier (iteratedDeriv 2 f) x‖ := norm_smul_le _ _
    _ ≤ ‖((2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2)⁻¹‖
          * ∫ y : ℝ, ‖iteratedDeriv 2 f y‖ := by
        gcongr
        exact dlb_fourier_enorm_le_integral _ x
    _ = (2 * Real.pi * |x|) ^ (-2 : ℤ) * ∫ y : ℝ, ‖iteratedDeriv 2 f y‖ := by rw [hnorm2]


lemma dlb_piece_kernel_bound_zero {m φ : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ A) (hφ : Integrable φ volume) (j : ℤ) (x : ℝ) :
    ‖FourierTransform.fourier (fun ξ : ℝ => m ξ * φ ((2:ℝ)^(-j) * ξ)) x‖
      ≤ A * ((2:ℝ)^j * ∫ y : ℝ, ‖φ y‖) := by
  have ha : 0 < (2:ℝ)^(-j) := zpow_pos (by norm_num : (0:ℝ) < 2) (-j)
  have ha' : 0 < (2:ℝ)^j := zpow_pos (by norm_num : (0:ℝ) < 2) j
  have hQMP : Measure.QuasiMeasurePreserving (fun y : ℝ => (2:ℝ)^(-j) * y)
      (volume : Measure ℝ) volume := dlb_mul_left_quasiMeasurePreserving _ (ne_of_gt ha)
  have haesm : AEMeasurable (fun u : ℝ => ‖φ ((2:ℝ)^(-j) * u)‖ₑ) volume :=
    (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving hQMP).enorm
  have hsub := BourgainBlock.lintegral_eq_ofReal_mul_lintegral_comp_mul_left
    (fun u : ℝ => ‖φ ((2:ℝ)^(-j) * u)‖ₑ) haesm ha'
  have hmul : (fun Y : ℝ => ‖φ ((2:ℝ)^(-j) * ((2:ℝ)^j * Y))‖ₑ) = fun Y : ℝ => ‖φ Y‖ₑ := by
    funext Y
    rw [show (2:ℝ)^(-j) * ((2:ℝ)^j * Y) = Y from by
      rw [← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      simp]
  rw [hmul] at hsub
  have hprof : ∫⁻ y : ℝ, ‖φ y‖ₑ < ⊤ := by
    rw [← eLpNorm_one_eq_lintegral_enorm (f := φ) (μ := volume) hφ.aestronglyMeasurable]
    exact (memLp_one_iff_integrable.mpr hφ).eLpNorm_lt_top
  have hfin : (∫⁻ y : ℝ, ‖φ ((2:ℝ)^(-j) * y)‖ₑ) < ⊤ := by
    rw [hsub]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hprof
  have hmem : MemLp (fun y : ℝ => φ ((2:ℝ)^(-j) * y)) 1 volume :=
    by rwa [memLp_iff,
      eLpNorm_one_eq_lintegral_enorm (f := fun y : ℝ => φ ((2:ℝ)^(-j) * y))
        (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving hQMP)]
  have hφj : Integrable (fun y : ℝ => ‖φ ((2:ℝ)^(-j) * y)‖) volume :=
    memLp_one_iff_integrable.mp hmem.norm
  have hkey := BourgainBlock.integral_eq_smul_integral_comp_mul_left
    (fun y : ℝ => ‖φ y‖) ha
  rw [smul_eq_mul] at hkey
  have hφint : ∫ y : ℝ, ‖φ ((2:ℝ)^(-j) * y)‖ = (2:ℝ)^j * ∫ y : ℝ, ‖φ y‖ := by
    rw [hkey, ← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), add_neg_cancel, zpow_zero,
      one_mul]
  refine (dlb_fourier_enorm_le_integral _ x).trans ?_
  calc ∫ y : ℝ, ‖m y * φ ((2:ℝ)^(-j) * y)‖
      ≤ ∫ y : ℝ, A * ‖φ ((2:ℝ)^(-j) * y)‖ := by
        refine integral_mono_of_nonneg (Eventually.of_forall (fun y => norm_nonneg _))
          (hφj.const_mul A) (Eventually.of_forall (fun y => ?_))
        show ‖m y * φ ((2:ℝ)^(-j) * y)‖ ≤ A * ‖φ ((2:ℝ)^(-j) * y)‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hmb y) (norm_nonneg _)
    _ = A * ∫ y : ℝ, ‖φ ((2:ℝ)^(-j) * y)‖ := integral_const_mul A _
    _ = A * ((2:ℝ)^j * ∫ y : ℝ, ‖φ y‖) := by rw [hφint]


lemma dlb_iteratedDeriv_two_mul {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : ℝ) :
    iteratedDeriv 2 (f * g) x
      = iteratedDeriv 2 f x * g x + 2 * (deriv f x * deriv g x) + f x * iteratedDeriv 2 g x := by
  rw [iteratedDeriv_mul (n := 2) hf.contDiffAt hg.contDiffAt]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.reduceSubDiff, Nat.choose_self,
    iteratedDeriv_zero, iteratedDeriv_one]
  norm_num
  ring


lemma dlb_fourier_enorm_le_inv_sq_of_bound {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (h0 : Integrable g volume) (h1 : Integrable (iteratedDeriv 1 g) volume)
    (h2 : Integrable (iteratedDeriv 2 g) volume)
    {s : Set ℝ} (hs : MeasurableSet s) (hsf : volume s ≠ ⊤) {B D : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y ∈ s, ‖iteratedDeriv 2 g y‖ ≤ B)
    (hgs : ∀ y : ℝ, y ∉ s → iteratedDeriv 2 g y = 0)
    (hD : (volume s).toReal ≤ D) (x : ℝ) (hx : x ≠ 0) :
    ‖FourierTransform.fourier g x‖ ≤ (2 * Real.pi * |x|) ^ (-2 : ℤ) * (B * D) := by
  refine (dlb_fourier_enorm_le_inv_sq hg h0 h1 h2 x hx).trans ?_
  gcongr
  have hmaj : ∀ y : ℝ, ‖iteratedDeriv 2 g y‖ ≤ B * s.indicator (fun _ => (1:ℝ)) y := by
    intro y
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy, mul_one]
      exact hB y hy
    · rw [hgs y hy, norm_zero, Set.indicator_of_notMem hy, mul_zero]
  have hind : Integrable (s.indicator (fun _ : ℝ => (1:ℝ))) volume :=
    (integrable_indicator_iff hs).mpr (integrableOn_const hsf (by simp))
  calc ∫ y : ℝ, ‖iteratedDeriv 2 g y‖
      ≤ ∫ y : ℝ, B * s.indicator (fun _ => (1:ℝ)) y :=
        integral_mono_of_nonneg (Eventually.of_forall (fun y => norm_nonneg _))
          (hind.const_mul B) (Eventually.of_forall hmaj)
    _ = B * ∫ y : ℝ, s.indicator (fun _ => (1:ℝ)) y := integral_const_mul B _
    _ = B * (volume s).toReal := by
        rw [integral_indicator_const (μ := volume) (e := (1:ℝ)) hs]
        simp [Measure.real]
    _ ≤ B * D := mul_le_mul_of_nonneg_left hD hB0


lemma dlb_iteratedDeriv_two_comp_mul {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (c x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => f (c * y)) x = c ^ 2 * iteratedDeriv 2 f (c * x) := by
  have hd : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)
  have h1 : deriv (fun y : ℝ => f (c * y)) = fun y : ℝ => (c : ℂ) * deriv f (c * y) := by
    funext y
    rw [deriv_comp_mul_left, Complex.real_smul]
  have h2 : iteratedDeriv 2 (fun y : ℝ => f (c * y)) x
      = deriv (fun y : ℝ => (c : ℂ) * deriv f (c * y)) x := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
      h1]
  have h3 : iteratedDeriv 2 f (c * x) = deriv (deriv f) (c * x) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => deriv f (c * y)) x :=
    hd.differentiableAt.comp x (by fun_prop)
  have h4 : deriv (fun y : ℝ => (c : ℂ) * deriv f (c * y)) x
      = (c : ℂ) * deriv (fun y : ℝ => deriv f (c * y)) x :=
    deriv_const_mul (c : ℂ) hdiff
  have h5 : deriv (fun y : ℝ => deriv f (c * y)) x = (c : ℂ) * deriv (deriv f) (c * x) := by
    rw [deriv_comp_mul_left, Complex.real_smul]
  rw [h2, h4, h5, h3]
  push_cast
  ring


lemma dlb_integrable_of_bound_of_vanishing {h : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    (hsf : volume s ≠ ⊤) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y ∈ s, ‖h y‖ ≤ B)
    (hv : ∀ y : ℝ, y ∉ s → h y = 0) (hmeas : AEStronglyMeasurable h volume) :
    Integrable h volume := by
  have hind : Integrable (s.indicator (fun _ : ℝ => (1:ℝ))) volume :=
    (integrable_indicator_iff hs).mpr (integrableOn_const hsf (by simp))
  refine Integrable.mono' (hind.const_mul B) hmeas (Eventually.of_forall (fun y => ?_))
  by_cases hy : y ∈ s
  · rw [Set.indicator_of_mem hy, mul_one]
    exact hB y hy
  · rw [hv y hy, norm_zero, Set.indicator_of_notMem hy, mul_zero]

/-- The annulus `{y | a ≤ |y| ≤ b}` has volume `2 (b - a)` for `0 < a ≤ b`. -/

lemma dlb_volume_abs_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (volume {y : ℝ | a ≤ |y| ∧ |y| ≤ b}).toReal = 2 * (b - a) := by
  have hset : {y : ℝ | a ≤ |y| ∧ |y| ≤ b} = Set.Icc (-b) (-a) ∪ Set.Icc a b := by
    ext y
    simp only [Set.mem_union, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := abs_le.mp h2
      rcases le_abs.mp h1 with h | h
      · exact Or.inr ⟨h, h3.2⟩
      · exact Or.inl ⟨h3.1, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have hy : y ≤ 0 := by linarith
        exact ⟨by rw [abs_of_nonpos hy]; linarith, by rw [abs_of_nonpos hy]; linarith⟩
      · have hy : 0 ≤ y := by linarith
        exact ⟨le_abs.mpr (Or.inl h1), by rw [abs_of_nonneg hy]; exact h2⟩
  have hdisj : Disjoint (Set.Icc (-b) (-a)) (Set.Icc a b) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    simp only [Set.mem_Icc] at hy1 hy2
    linarith [hy1.2, hy2.1]
  rw [hset, measure_union hdisj measurableSet_Icc, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ -a - -b),
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]
  ring


lemma dlb_piece_kernel_bound_two {m φ : ℝ → ℂ} {A C : ℝ}
    (hm : ContDiff ℝ 2 m) (hφ : ContDiff ℝ 2 φ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hφb : ∀ ξ : ℝ, ‖φ ξ‖ ≤ C) (hφ1 : ∀ ξ : ℝ, ‖deriv φ ξ‖ ≤ C)
    (hφ2 : ∀ ξ : ℝ, ‖iteratedDeriv 2 φ ξ‖ ≤ C)
    (hφsupp : ∀ ξ : ℝ, φ ξ ≠ 0 → (1/2 : ℝ) ≤ |ξ| ∧ |ξ| ≤ 4)
    (j : ℤ) (x : ℝ) (hx : x ≠ 0) :
    ‖FourierTransform.fourier (fun ξ : ℝ => m ξ * φ ((2:ℝ)^(-j) * ξ)) x‖
      ≤ (2 * Real.pi * |x|) ^ (-2 : ℤ) * (63 * A * C * (2:ℝ)^(-j)) := by
  set c : ℝ := (2:ℝ)^(-j) with hcdef
  have hc : 0 < c := by rw [hcdef]; exact zpow_pos (by norm_num : (0:ℝ) < 2) (-j)
  set ψ : ℝ → ℂ := fun ξ => φ (c * ξ) with hψdef
  set g : ℝ → ℂ := fun ξ => m ξ * ψ ξ with hgdef
  have hψc : ContDiff ℝ 2 ψ := by rw [hψdef]; exact hφ.comp (by fun_prop)
  have hgc : ContDiff ℝ 2 g := by rw [hgdef]; exact hm.mul hψc
  have hψ' : ∀ ξ : ℝ, deriv ψ ξ = (c : ℂ) * deriv φ (c * ξ) := by
    intro ξ; rw [hψdef, deriv_comp_mul_left, Complex.real_smul]
  have hψ'' : ∀ ξ : ℝ, iteratedDeriv 2 ψ ξ = c ^ 2 * iteratedDeriv 2 φ (c * ξ) := by
    intro ξ; rw [hψdef]; exact dlb_iteratedDeriv_two_comp_mul hφ c ξ
  set a : ℝ := 1 / (2 * c) with hadef
  set b : ℝ := 4 / c with hbdef
  have ha : 0 < a := by rw [hadef]; positivity
  have hab : a ≤ b := by rw [hadef, hbdef]; field_simp; linarith
  have hac : c * a = 1 / 2 := by rw [hadef]; field_simp
  have hai : 1 / a = 2 * c := by
    field_simp at hac ⊢
    linarith [hac]
  have hai' : a⁻¹ = 2 * c := by rw [← one_div]; exact hai
  set s : Set ℝ := Set.Icc (-b) (-a) ∪ Set.Icc a b with hsdef
  have hsmeas : MeasurableSet s := by
    rw [hsdef]
    exact MeasurableSet.union measurableSet_Icc measurableSet_Icc
  have hdisj : Disjoint (Set.Icc (-b) (-a)) (Set.Icc a b) := by
    rw [Set.disjoint_left]
    intro y h1 h2
    simp only [Set.mem_Icc] at h1 h2
    linarith [h1.2, h2.1, ha]
  have hsfin : volume s ≠ ⊤ := by
    rw [hsdef, measure_union hdisj measurableSet_Icc, Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hvol : (volume s).toReal ≤ 7 / c := by
    rw [hsdef, measure_union hdisj measurableSet_Icc, Real.volume_Icc, Real.volume_Icc,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ -a - -b),
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]
    rw [hadef, hbdef]; field_simp; ring_nf; norm_num
  have hmem : ∀ y ∈ s, a ≤ |y| ∧ |y| ≤ b := by
    intro y hy
    rw [hsdef] at hy
    rcases hy with hy | hy
    · simp only [Set.mem_Icc] at hy
      have hy0 : y ≤ 0 := by linarith [hy.2, ha]
      exact ⟨by rw [abs_of_nonpos hy0]; linarith, by rw [abs_of_nonpos hy0]; linarith⟩
    · simp only [Set.mem_Icc] at hy
      have hy0 : 0 ≤ y := by linarith [hy.1, ha]
      exact ⟨by rw [abs_of_nonneg hy0]; exact hy.1, by rw [abs_of_nonneg hy0]; exact hy.2⟩
  -- the open set where `ψ` vanishes identically, and its relation to `s`
  set U : Set ℝ := {z : ℝ | |c * z| < 1/2 ∨ 4 < |c * z|} with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef]
    refine IsOpen.union ?_ ?_
    · exact isOpen_lt (continuous_const.mul continuous_id).abs continuous_const
    · exact isOpen_lt continuous_const (continuous_const.mul continuous_id).abs
  have hUvan : ∀ z ∈ U, g =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [hUopen.mem_nhds hz] with w hw
    have hw0 : ψ w = 0 := by
      rw [hψdef]
      by_contra hne
      obtain ⟨h1, h2⟩ := hφsupp (c * w) hne
      rcases hw with hw | hw <;> linarith
    show g w = (fun _ : ℝ => (0:ℂ)) w
    simp only [hgdef, Pi.mul_apply, hw0, mul_zero, Pi.zero_apply]
  have hsU : ∀ y : ℝ, y ∉ s → y ∈ U := by
    intro y hy
    rw [hsdef] at hy
    simp only [Set.mem_union, Set.mem_Icc] at hy
    have h1 : ¬(a ≤ y ∧ y ≤ b) := fun h => hy (Or.inr h)
    have h2 : ¬(-b ≤ y ∧ y ≤ -a) := fun h => hy (Or.inl h)
    rw [hUdef]
    have key : |y| < a ∨ b < |y| := by
      by_cases hy0 : 0 ≤ y
      · rw [abs_of_nonneg hy0]
        by_cases h : a ≤ y
        · right
          exact not_le.mp (fun hyb => h1 ⟨h, hyb⟩)
        · left
          exact not_le.mp h
      · have hy0' : y ≤ 0 := le_of_lt (not_le.mp hy0)
        rw [abs_of_nonpos hy0']
        by_cases h : -b ≤ y
        · left
          have hya : -a < y := not_le.mp (fun hya => h2 ⟨h, hya⟩)
          linarith
        · right
          have hyb : y < -b := not_le.mp h
          linarith
    have habs : |c * y| = c * |y| := by rw [abs_mul, abs_of_pos hc]
    have h2' : c * (1 / (2 * c)) = 1 / 2 := by field_simp
    have h4' : c * (4 / c) = 4 := by field_simp
    rcases key with hk | hk
    · left
      rw [habs]
      have := mul_lt_mul_of_pos_left hk hc
      rw [h2'] at this
      exact this
    · right
      rw [habs]
      have := mul_lt_mul_of_pos_left hk hc
      rw [h4'] at this
      exact this
  have hvanish : ∀ y : ℝ, y ∉ s → g y = 0 := fun y hy => (hUvan y (hsU y hy)).self_of_nhds
  have hdvanish : ∀ y : ℝ, y ∉ s → deriv g y = 0 := by
    intro y hy
    rw [Filter.EventuallyEq.deriv_eq (hUvan y (hsU y hy))]
    simp
  have hdev : ∀ y : ℝ, y ∉ s → deriv g =ᶠ[𝓝 y] 0 := by
    intro y hy
    filter_upwards [hUopen.mem_nhds (hsU y hy)] with z hz
    rw [Filter.EventuallyEq.deriv_eq (hUvan z hz)]
    simp
  have hgs : ∀ y : ℝ, y ∉ s → iteratedDeriv 2 g y = 0 := by
    intro y hy
    have h3 : iteratedDeriv 2 g = deriv (deriv g) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [h3, Filter.EventuallyEq.deriv_eq (hdev y hy)]
    simp
  -- bounds on the annulus
  have hdm : ∀ y ∈ s, ‖deriv m y‖ ≤ 2 * A * c := by
    intro y hy
    obtain ⟨hy1, _⟩ := hmem y hy
    have hypos : 0 < |y| := lt_of_lt_of_le (by positivity) hy1
    have h1 : ‖deriv m y‖ ≤ A / |y| := (le_div_iff₀ hypos).mpr (by linarith [hm1 y])
    have h2 : A / |y| ≤ 2 * A * c := by
      have hstep : A / |y| ≤ A / a := div_le_div_of_nonneg_left hA ha hy1
      have hAdiv : A / a = 2 * A * c := by rw [div_eq_mul_inv, hai']; ring
      linarith [hstep, hAdiv]
    exact h1.trans h2
  have hd2m : ∀ y ∈ s, ‖iteratedDeriv 2 m y‖ ≤ 4 * A * c ^ 2 := by
    intro y hy
    obtain ⟨hy1, _⟩ := hmem y hy
    have hypos : 0 < |y| := lt_of_lt_of_le (by positivity) hy1
    have h1 : ‖iteratedDeriv 2 m y‖ ≤ A / |y| ^ 2 := (le_div_iff₀ (by positivity)).mpr (by
      have := hm2 y; nlinarith [this])
    have h2 : A / |y| ^ 2 ≤ 4 * A * c ^ 2 := by
      have hya : a ≤ |y| := hy1
      have hsq : a ^ 2 ≤ |y| ^ 2 := by nlinarith [ha, hya, abs_nonneg y]
      have hstep : A / |y| ^ 2 ≤ A / a ^ 2 := div_le_div_of_nonneg_left hA (by positivity) hsq
      have hAdiv : A / a ^ 2 = 4 * A * c ^ 2 := by
        have h1 : (a ^ 2)⁻¹ = (2 * c) ^ 2 := by
          rw [← inv_pow, hai']
        rw [div_eq_mul_inv, h1]; ring
      linarith [hstep, hAdiv]
    exact h1.trans h2
  have hB : ∀ y ∈ s, ‖iteratedDeriv 2 g y‖ ≤ 9 * A * C * c ^ 2 := by
    intro y hy
    have hdm' := hdm y hy
    have hd2m' := hd2m y hy
    have hlev : iteratedDeriv 2 g y
        = iteratedDeriv 2 m y * ψ y + 2 * (deriv m y * ((c : ℂ) * deriv φ (c * y)))
          + m y * (c ^ 2 * iteratedDeriv 2 φ (c * y)) := by
      rw [hgdef]
      rw [show (fun ξ : ℝ => m ξ * ψ ξ) = m * ψ from rfl]
      rw [dlb_iteratedDeriv_two_mul hm hψc y, hψ' y, hψ'' y]
    rw [hlev]
    calc ‖iteratedDeriv 2 m y * ψ y + 2 * (deriv m y * ((c : ℂ) * deriv φ (c * y)))
          + m y * (c ^ 2 * iteratedDeriv 2 φ (c * y))‖
        ≤ ‖iteratedDeriv 2 m y * ψ y‖ + ‖2 * (deriv m y * ((c : ℂ) * deriv φ (c * y)))‖
          + ‖m y * (c ^ 2 * iteratedDeriv 2 φ (c * y))‖ := by
          refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖iteratedDeriv 2 m y‖ * ‖ψ y‖ + 2 * (‖deriv m y‖ * ‖(c : ℂ) * deriv φ (c * y)‖)
          + ‖m y‖ * ‖c ^ 2 * iteratedDeriv 2 φ (c * y)‖ := by
          refine add_le_add (add_le_add (norm_mul_le _ _) ?_) (norm_mul_le _ _)
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
      _ ≤ 4 * A * c ^ 2 * C + 2 * (2 * A * c * (c * C)) + A * (c ^ 2 * C) := by
          have hψy : ‖ψ y‖ ≤ C := by rw [hψdef]; exact hφb (c * y)
          have hdψ : ‖(c : ℂ) * deriv φ (c * y)‖ ≤ c * C := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            exact mul_le_mul_of_nonneg_left (hφ1 (c * y)) hc.le
          have hd2ψ : ‖c ^ 2 * iteratedDeriv 2 φ (c * y)‖ ≤ c ^ 2 * C := by
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            exact mul_le_mul_of_nonneg_left (hφ2 (c * y)) (by positivity)
          have hm0 : ‖m y‖ ≤ A := hmb y
          have hc2 : (0:ℝ) ≤ c ^ 2 := sq_nonneg c
          have hC0 : 0 ≤ C := hC
          have hA0 : 0 ≤ A := hA
          have hnn : (0:ℝ) ≤ ‖deriv m y‖ := norm_nonneg _
          have hnn2 : (0:ℝ) ≤ ‖iteratedDeriv 2 m y‖ := norm_nonneg _
          have h1 : ‖iteratedDeriv 2 m y‖ * ‖ψ y‖ ≤ 4 * A * c ^ 2 * C := by
            calc ‖iteratedDeriv 2 m y‖ * ‖ψ y‖ ≤ (4 * A * c ^ 2) * C :=
                  mul_le_mul hd2m' hψy (norm_nonneg _) (by positivity)
              _ = 4 * A * c ^ 2 * C := by ring
          have h2 : 2 * (‖deriv m y‖ * ‖(c : ℂ) * deriv φ (c * y)‖)
              ≤ 2 * (2 * A * c * (c * C)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul hdm' hdψ (norm_nonneg _) (by positivity))
              (by norm_num)
          have h3 : ‖m y‖ * ‖c ^ 2 * iteratedDeriv 2 φ (c * y)‖ ≤ A * (c ^ 2 * C) :=
            mul_le_mul hm0 hd2ψ (norm_nonneg _) hA0
          linarith [h1, h2, h3]
      _ = 9 * A * C * c ^ 2 := by ring
  -- the three integrability hypotheses
  have hgm : AEStronglyMeasurable g volume := hgc.continuous.aestronglyMeasurable
  have hg1m : AEStronglyMeasurable (iteratedDeriv 1 g) volume := by
    rw [iteratedDeriv_one]
    exact (hgc.continuous_deriv (by norm_num)).aestronglyMeasurable
  have hg2m : AEStronglyMeasurable (iteratedDeriv 2 g) volume := by
    exact (hgc.continuous_iteratedDeriv 2 (by norm_num)).aestronglyMeasurable
  have hderiv1 : ∀ y ∈ s, ‖iteratedDeriv 1 g y‖ ≤ 3 * A * C * c := by
    intro y hy
    have hdm' := hdm y hy
    have hψy : ‖ψ y‖ ≤ C := by rw [hψdef]; exact hφb (c * y)
    have hmy : ‖m y‖ ≤ A := hmb y
    have hdψ : ‖(c : ℂ) * deriv φ (c * y)‖ ≤ c * C := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (hφ1 (c * y)) hc.le
    have hlev : iteratedDeriv 1 g y
        = deriv m y * ψ y + m y * ((c : ℂ) * deriv φ (c * y)) := by
      rw [iteratedDeriv_one, hgdef]
      rw [show (fun ξ : ℝ => m ξ * ψ ξ) = m * ψ from rfl]
      rw [deriv_mul (hm.differentiable (by norm_num) y)
        (hψc.differentiable (by norm_num) y), hψ' y]
    rw [hlev]
    calc ‖deriv m y * ψ y + m y * ((c : ℂ) * deriv φ (c * y))‖
        ≤ ‖deriv m y * ψ y‖ + ‖m y * ((c : ℂ) * deriv φ (c * y))‖ := norm_add_le _ _
      _ = ‖deriv m y‖ * ‖ψ y‖ + ‖m y‖ * ‖(c : ℂ) * deriv φ (c * y)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (2 * A * c) * C + A * (c * C) := by
          refine add_le_add (mul_le_mul hdm' hψy (norm_nonneg _) (by positivity))
            (mul_le_mul hmy hdψ (norm_nonneg _) (by positivity))
      _ = 3 * A * C * c := by ring
  have hgbound : ∀ y : ℝ, ‖g y‖ ≤ A * C := by
    intro y
    rw [hgdef]
    calc ‖m y * ψ y‖ ≤ ‖m y‖ * ‖ψ y‖ := norm_mul_le _ _
      _ ≤ A * C := mul_le_mul (hmb y) (by rw [hψdef]; exact hφb (c * y)) (norm_nonneg _) hA
  have hint0 : Integrable g volume :=
    dlb_integrable_of_bound_of_vanishing (B := A * C) hsmeas hsfin (by positivity)
      (fun y _ => hgbound y) hvanish hgm
  have hint1 : Integrable (iteratedDeriv 1 g) volume :=
    dlb_integrable_of_bound_of_vanishing (B := 3 * A * C * c) hsmeas hsfin (by positivity)
      (fun y hy => hderiv1 y hy) (fun y hy => by rw [iteratedDeriv_one]; exact hdvanish y hy) hg1m
  have hint2 : Integrable (iteratedDeriv 2 g) volume :=
    dlb_integrable_of_bound_of_vanishing (B := 9 * A * C * c ^ 2) hsmeas hsfin (by positivity)
      (fun y hy => hB y hy) hgs hg2m
  -- assembly
  have hmain := dlb_fourier_enorm_le_inv_sq_of_bound hgc hint0 hint1 hint2 hsmeas hsfin
    (by positivity : (0:ℝ) ≤ 9 * A * C * c ^ 2)
    hB hgs hvol x hx
  refine hmain.trans ?_
  have hBD : 9 * A * C * c ^ 2 * (7 / c) = 63 * A * C * (2:ℝ)^(-j) := by
    rw [← hcdef]
    field_simp
    ring
  rw [hBD]




lemma dlb_exists_zpow_bracket {r t : ℝ} (hr : 1 < r) (ht : 0 < t) :
    ∃ N : ℤ, r ^ N ≤ Real.sqrt t ∧ Real.sqrt t ≤ r ^ (N + 1) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set J : ℝ := Real.log (Real.sqrt t) / Real.log r with hJ
  have hrpowJ : r ^ J = Real.sqrt t := by
    rw [hJ, Real.rpow_def_of_pos hr0, mul_div_cancel₀ _ (ne_of_gt hlogr)]
    exact Real.exp_log hsqrt
  refine ⟨⌊J⌋, ?_, ?_⟩
  · calc r ^ (⌊J⌋ : ℤ) = r ^ ((⌊J⌋ : ℤ) : ℝ) := by rw [Real.rpow_intCast]
      _ ≤ r ^ J := Real.rpow_le_rpow_of_exponent_le hr.le (Int.floor_le J)
      _ = Real.sqrt t := hrpowJ
  · calc Real.sqrt t = r ^ J := hrpowJ.symm
      _ ≤ r ^ (((⌊J⌋ : ℤ) + 1 : ℤ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr.le (by push_cast; exact (Int.lt_floor_add_one J).le)
      _ = r ^ ((⌊J⌋ : ℤ) + 1) := by rw [Real.rpow_intCast]

/-- `r ^ (L - n) = r ^ L * (r⁻¹) ^ n`. -/
lemma dlb_zpow_sub_nat {r : ℝ} (hr : r ≠ 0) (L : ℤ) (n : ℕ) :
    r ^ (L - (n : ℤ)) = r ^ L * (r⁻¹) ^ n := by
  rw [zpow_sub₀ hr L (n : ℤ), zpow_natCast, div_eq_mul_inv, inv_pow]

/-- `r ^ (L + 1 + n) = r ^ (L+1) * r ^ n`. -/
lemma dlb_zpow_add_nat {r : ℝ} (hr : r ≠ 0) (L : ℤ) (n : ℕ) :
    r ^ (L + 1 + (n : ℤ)) = r ^ (L + 1) * r ^ n := by
  rw [show L + 1 + (n : ℤ) = (L + 1) + (n : ℤ) by ring, zpow_add₀ hr (L + 1) (n : ℤ),
    zpow_natCast]

/-- `x ^ (N + 1) = x * x ^ N` for a positive base. -/
lemma dlb_rpow_succ_mul {x N : ℝ} (hx : 0 < x) : x ^ (N + 1) = x * x ^ N := by
  rw [add_comm, Real.rpow_add hx, Real.rpow_one]

/-- `(r ^ n) ^ (-N) = (r ^ (-N)) ^ n`. -/
lemma dlb_rpow_pow_neg {r : ℝ} (hr0 : 0 ≤ r) (N : ℝ) (n : ℕ) :
    (r ^ n) ^ (-N) = (r ^ (-N)) ^ n := by
  have h1 : (r ^ n : ℝ) = r ^ (n : ℝ) := (Real.rpow_natCast r n).symm
  have h2 : (r ^ (-N)) ^ n = (r ^ (-N)) ^ (n : ℝ) :=
    (Real.rpow_natCast (r ^ (-N)) n).symm
  rw [h1, h2, ← Real.rpow_mul hr0, ← Real.rpow_mul hr0]
  congr 1
  ring

/-- **The scale-invariant dyadic `min`-sum.**  For `r > 1`, `a b > 0` and `N > 0`,
`∑_j min (a r^j) (b (r^j)^{-N})` is bounded by an explicit constant times the crossover
value `a (b/a)^{1/(N+1)}`. -/
lemma dlb_tsum_min_zpow_general {r a b N : ℝ} (hr : 1 < r) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) :
    (∑' j : ℤ, min (a * r ^ j) (b * (r ^ j) ^ (-N)))
      ≤ (a * (b / a) ^ (1 / (N + 1))) * ((1 - r ^ (-N))⁻¹ + (1 - r⁻¹)⁻¹) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hrN : 0 < r ^ (-N) := Real.rpow_pos_of_pos hr0 _
  have hrN1 : r ^ (-N) < 1 := by
    rw [Real.rpow_neg hr0.le]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hr hN)
  have hr10 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  set q : ℝ := (b / a) ^ (1 / (N + 1)) with hq
  have hqpos : 0 < q := Real.rpow_pos_of_pos (div_pos hb ha) _
  have hqN : q ^ (N + 1) = b / a := by
    rw [hq, ← Real.rpow_mul (div_pos hb ha).le]
    have h1 : 1 / (N + 1) * (N + 1) = 1 := by field_simp
    rw [h1, Real.rpow_one]
  obtain ⟨L, hL1, hL2⟩ := dlb_exists_zpow_bracket hr (by positivity : (0:ℝ) < q ^ 2)
  rw [Real.sqrt_sq hqpos.le] at hL1 hL2
  have hbranch : ∀ n : ℕ, min (a * r ^ (L - (n : ℤ))) (b * (r ^ (L - (n : ℤ))) ^ (-N))
      = a * r ^ (L - (n : ℤ)) := by
    intro n
    refine min_eq_left ?_
    set x : ℝ := r ^ (L - (n : ℤ)) with hxdef
    have hxpos : 0 < x := zpow_pos hr0 _
    have hxq : x ≤ q := by
      have hle : L - (n : ℤ) ≤ L := by omega
      calc x ≤ r ^ L := zpow_le_zpow_right₀ hr.le hle
        _ ≤ q := hL1
    have hxqN : x ^ (N + 1) ≤ b / a := by
      calc x ^ (N + 1) ≤ q ^ (N + 1) := Real.rpow_le_rpow hxpos.le hxq (by linarith)
        _ = b / a := hqN
    have hxa : a * x ^ (N + 1) ≤ b := by
      have := (le_div_iff₀ ha).mp hxqN
      rw [mul_comm] at this
      exact this
    rw [Real.rpow_neg hxpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hxpos N)]
    have hEq : a * x * x ^ N = a * x ^ (N + 1) := by
      rw [dlb_rpow_succ_mul hxpos, mul_assoc]
    rw [hEq]
    exact hxa
  have hbranch2 : ∀ n : ℕ, min (a * r ^ (L + 1 + (n : ℤ))) (b * (r ^ (L + 1 + (n : ℤ))) ^ (-N))
      = b * (r ^ (L + 1 + (n : ℤ))) ^ (-N) := by
    intro n
    refine min_eq_right ?_
    set x : ℝ := r ^ (L + 1 + (n : ℤ)) with hxdef
    have hxpos : 0 < x := zpow_pos hr0 _
    have hqx : q ≤ x := by
      have hle : L + 1 ≤ L + 1 + (n : ℤ) := by omega
      calc q ≤ r ^ (L + 1) := hL2
        _ ≤ x := zpow_le_zpow_right₀ hr.le hle
    have hxqN : b / a ≤ x ^ (N + 1) := by
      calc b / a = q ^ (N + 1) := hqN.symm
        _ ≤ x ^ (N + 1) := Real.rpow_le_rpow hqpos.le hqx (by linarith)
    have hxa : b ≤ a * x ^ (N + 1) := by
      have := (div_le_iff₀ ha).mp hxqN
      rw [mul_comm] at this
      exact this
    rw [Real.rpow_neg hxpos.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hxpos N)]
    have hEq : a * x * x ^ N = a * x ^ (N + 1) := by
      rw [dlb_rpow_succ_mul hxpos, mul_assoc]
    rw [hEq]
    exact hxa
  -- summability
  have hn1 : ‖(r⁻¹ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]; exact hr10
  have hnN : ‖(r ^ (-N) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrN]; exact hrN1
  have hsumm1 : Summable (fun n : ℕ => a * r ^ (L - (n : ℤ))) := by
    rw [show (fun n : ℕ => a * r ^ (L - (n : ℤ))) = fun n : ℕ => (a * r ^ L) * (r⁻¹) ^ n from by
      funext n; rw [dlb_zpow_sub_nat hrne]; ring]
    exact (summable_geometric_of_norm_lt_one hn1).mul_left _
  have hsumm2 : Summable (fun n : ℕ => b * (r ^ (L + 1 + (n : ℤ))) ^ (-N)) := by
    rw [show (fun n : ℕ => b * (r ^ (L + 1 + (n : ℤ))) ^ (-N))
        = fun n : ℕ => (b * (r ^ (L+1)) ^ (-N)) * ((r ^ (-N)) ^ n) from by
      funext n
      have h : (r ^ (L + 1 + (n : ℤ))) ^ (-N) = (r ^ (L+1)) ^ (-N) * (r ^ (-N)) ^ n := by
        rw [dlb_zpow_add_nat hrne L n, Real.mul_rpow (zpow_nonneg hr0.le _) (pow_nonneg hr0.le _),
          dlb_rpow_pow_neg hr0.le]
      rw [h]; ring]
    exact (summable_geometric_of_norm_lt_one hnN).mul_left _
  have hs1 : Summable (fun n : ℕ => min (a * r ^ (L - (n : ℤ))) (b * (r ^ (L - (n : ℤ))) ^ (-N))) :=
    Summable.of_nonneg_of_le
      (fun n => le_min (mul_nonneg ha.le (zpow_nonneg hr0.le _))
        (mul_nonneg hb.le (Real.rpow_nonneg (zpow_nonneg hr0.le _) _)))
      (fun n => min_le_left _ _) hsumm1
  have hs2 : Summable
      (fun n : ℕ => min (a * r ^ (L + 1 + (n : ℤ))) (b * (r ^ (L + 1 + (n : ℤ))) ^ (-N))) :=
    Summable.of_nonneg_of_le
      (fun n => le_min (mul_nonneg ha.le (zpow_nonneg hr0.le _))
        (mul_nonneg hb.le (Real.rpow_nonneg (zpow_nonneg hr0.le _) _)))
      (fun n => min_le_right _ _) hsumm2
  have hsplit := tsum_int_split (fun j : ℤ => min (a * r ^ j) (b * (r ^ j) ^ (-N))) L hs1 hs2
  rw [hsplit]
  have hval1 : (∑' n : ℕ, min (a * r ^ (L - (n : ℤ))) (b * (r ^ (L - (n : ℤ))) ^ (-N)))
      = a * r ^ L * (1 - r⁻¹)⁻¹ := by
    rw [tsum_congr hbranch]
    rw [show (fun n : ℕ => a * r ^ (L - (n : ℤ)))
        = fun n : ℕ => (a * r ^ L) * (r⁻¹) ^ n from by
      funext n; rw [dlb_zpow_sub_nat hrne]; ring]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hn1]
  have hval2 : (∑' n : ℕ, min (a * r ^ (L + 1 + (n : ℤ))) (b * (r ^ (L + 1 + (n : ℤ))) ^ (-N)))
      = b * (r ^ (L+1)) ^ (-N) * (1 - r ^ (-N))⁻¹ := by
    rw [tsum_congr hbranch2]
    rw [show (fun n : ℕ => b * (r ^ (L + 1 + (n : ℤ))) ^ (-N))
        = fun n : ℕ => (b * (r ^ (L+1)) ^ (-N)) * ((r ^ (-N)) ^ n) from by
      funext n
      have h : (r ^ (L + 1 + (n : ℤ))) ^ (-N) = (r ^ (L+1)) ^ (-N) * (r ^ (-N)) ^ n := by
        rw [dlb_zpow_add_nat hrne L n, Real.mul_rpow (zpow_nonneg hr0.le _) (pow_nonneg hr0.le _),
          dlb_rpow_pow_neg hr0.le]
      rw [h]; ring]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnN]
  rw [hval1, hval2]
  -- final comparison
  have hA : a * r ^ L ≤ a * q := mul_le_mul_of_nonneg_left hL1 ha.le
  have hstep : (r ^ (L+1)) ^ (-N) ≤ q ^ (-N) := by
    rw [Real.rpow_neg (zpow_nonneg hr0.le _), Real.rpow_neg hqpos.le]
    refine (inv_le_inv₀ (Real.rpow_pos_of_pos (zpow_pos hr0 (L+1)) N)
      (Real.rpow_pos_of_pos hqpos N)).mpr ?_
    exact Real.rpow_le_rpow hqpos.le hL2 hN.le
  have hB : b * (r ^ (L+1)) ^ (-N) ≤ b * q ^ (-N) := mul_le_mul_of_nonneg_left hstep hb.le
  have hB2 : b * q ^ (-N) = a * q := by
    have hq' : b = a * q ^ (N + 1) := by
      rw [hqN]; field_simp
    rw [hq', mul_assoc, ← Real.rpow_add hqpos]
    rw [show N + 1 + -N = (1:ℝ) by ring, Real.rpow_one]
  have hQ : a * q = a * (b / a) ^ (1 / (N + 1)) := by rw [hq]
  have hcoefN : 0 ≤ (1 - r ^ (-N))⁻¹ := by positivity
  have hcoef1 : 0 ≤ (1 - r⁻¹)⁻¹ := by positivity
  calc a * r ^ L * (1 - r⁻¹)⁻¹ + b * (r ^ (L+1)) ^ (-N) * (1 - r ^ (-N))⁻¹
      = (a * r ^ L) * (1 - r⁻¹)⁻¹ + (b * (r ^ (L+1)) ^ (-N)) * (1 - r ^ (-N))⁻¹ := by ring
    _ ≤ (a * q) * (1 - r⁻¹)⁻¹ + (b * q ^ (-N)) * (1 - r ^ (-N))⁻¹ := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_right hA hcoef1
        · exact mul_le_mul_of_nonneg_right hB hcoefN
    _ = (a * (b / a) ^ (1 / (N + 1))) * ((1 - r ^ (-N))⁻¹ + (1 - r⁻¹)⁻¹) := by
        rw [hB2, hQ]; ring


/-- **The dyadic `min`-sum, geometric form.**  For `r > 1` and positive `a, b`, a nonnegative
sequence dominated by `min (a r^j) (b r^{-j})` has sum at most `2r/(r-1) · √(ab)`. -/
lemma dlb_tsum_min_geometric {r a b : ℝ} (hr : 1 < r) (ha : 0 < a) (hb : 0 < b)
    (k : ℤ → ℝ) (hnn : ∀ j, 0 ≤ k j) (h : ∀ j, k j ≤ min (a * r ^ j) (b * r ^ (-j))) :
    (∑' j : ℤ, k j) ≤ (2 * r / (r - 1)) * Real.sqrt (a * b) := by
  have hr0 : 0 < r := lt_trans one_pos hr
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hrm1 : 0 < r - 1 := by linarith
  have hnn1 : ‖(r⁻¹ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
    exact inv_lt_one_of_one_lt₀ hr
  obtain ⟨L, hL1, hL2⟩ := dlb_exists_zpow_bracket hr (div_pos hb ha)
  have hsqa : Real.sqrt (b / a) ^ 2 = b / a := Real.sq_sqrt (div_nonneg hb.le ha.le)
  -- the two branch decisions
  have hbr1 : ∀ n : ℕ, k (L - (n : ℤ)) ≤ a * r ^ (L - (n : ℤ)) := by
    intro n
    have hle : r ^ (L - (n : ℤ)) ≤ r ^ L := zpow_le_zpow_right₀ hr.le (by omega)
    have hs : (r ^ (L - (n : ℤ))) ^ 2 ≤ b / a := by
      calc (r ^ (L - (n : ℤ))) ^ 2 ≤ (r ^ L) ^ 2 := pow_le_pow_left₀ (zpow_nonneg hr0.le _) hle 2
        _ ≤ Real.sqrt (b / a) ^ 2 := pow_le_pow_left₀ (zpow_nonneg hr0.le L) hL1 2
        _ = b / a := hsqa
    have hmain : a * r ^ (L - (n : ℤ)) ≤ b * r ^ (-(L - (n : ℤ))) := by
      have hx : 0 < r ^ (L - (n : ℤ)) := zpow_pos hr0 _
      rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ hx]
      rw [show a * r ^ (L - (n : ℤ)) * r ^ (L - (n : ℤ)) = a * (r ^ (L - (n : ℤ)))^2 by ring]
      calc a * (r ^ (L - (n : ℤ)))^2 ≤ a * (b / a) := mul_le_mul_of_nonneg_left hs ha.le
        _ = b := by rw [mul_comm]; exact div_mul_cancel₀ b (ne_of_gt ha)
    exact (h (L - (n : ℤ))).trans (min_eq_left hmain).le
  have hbr2 : ∀ n : ℕ, k (L + 1 + (n : ℤ)) ≤ b * r ^ (-(L + 1 + (n : ℤ))) := by
    intro n
    have hle : r ^ (L + 1) ≤ r ^ (L + 1 + (n : ℤ)) := zpow_le_zpow_right₀ hr.le (by omega)
    have hs : b / a ≤ (r ^ (L + 1 + (n : ℤ))) ^ 2 := by
      calc b / a = Real.sqrt (b / a) ^ 2 := hsqa.symm
        _ ≤ (r ^ (L + 1)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL2 2
        _ ≤ (r ^ (L + 1 + (n : ℤ))) ^ 2 := pow_le_pow_left₀ (zpow_nonneg hr0.le _) hle 2
    have hmain : b * r ^ (-(L + 1 + (n : ℤ))) ≤ a * r ^ (L + 1 + (n : ℤ)) := by
      have hx : 0 < r ^ (L + 1 + (n : ℤ)) := zpow_pos hr0 _
      rw [zpow_neg, ← div_eq_mul_inv, div_le_iff₀ hx]
      rw [show a * r ^ (L + 1 + (n : ℤ)) * r ^ (L + 1 + (n : ℤ))
          = a * (r ^ (L + 1 + (n : ℤ)))^2 by ring]
      calc b = a * (b / a) := by rw [mul_comm]; exact (div_mul_cancel₀ b (ne_of_gt ha)).symm
        _ ≤ a * (r ^ (L + 1 + (n : ℤ)))^2 := mul_le_mul_of_nonneg_left hs ha.le
    exact (h (L + 1 + (n : ℤ))).trans (min_eq_right hmain).le
  -- summability of the two halves
  have hg1 : Summable (fun n : ℕ => a * r ^ (L - (n : ℤ))) := by
    rw [show (fun n : ℕ => a * r ^ (L - (n : ℤ))) = fun n : ℕ => (a * r ^ L) * (r⁻¹) ^ n from by
      funext n; rw [dlb_zpow_sub_nat hrne]; ring]
    exact (summable_geometric_of_norm_lt_one hnn1).mul_left _
  have hg2 : Summable (fun n : ℕ => b * r ^ (-(L + 1 + (n : ℤ)))) := by
    rw [show (fun n : ℕ => b * r ^ (-(L + 1 + (n : ℤ))))
        = fun n : ℕ => (b * r ^ (-(L+1))) * ((r⁻¹) ^ n) from by
      funext n
      rw [show -(L + 1 + (n : ℤ)) = -(L+1) - (n:ℤ) by ring, zpow_sub₀ hrne, zpow_natCast,
        div_eq_mul_inv, inv_pow]
      ring]
    exact (summable_geometric_of_norm_lt_one hnn1).mul_left _
  have hsumm1 : Summable (fun n : ℕ => k (L - (n : ℤ))) :=
    Summable.of_nonneg_of_le (fun n => hnn _) hbr1 hg1
  have hsumm2 : Summable (fun n : ℕ => k (L + 1 + (n : ℤ))) :=
    Summable.of_nonneg_of_le (fun n => hnn _) hbr2 hg2
  have hsplit := tsum_int_split k L hsumm1 hsumm2
  rw [hsplit]
  have hgeo : (1 - r⁻¹)⁻¹ = r / (r - 1) := by
    have h1 : (1 - r⁻¹) = (r - 1) / r := by field_simp
    rw [h1, inv_div]
  have hval1 : (∑' n : ℕ, a * r ^ (L - (n : ℤ))) = a * r ^ L * (r / (r - 1)) := by
    rw [show (fun n : ℕ => a * r ^ (L - (n : ℤ))) = fun n : ℕ => (a * r ^ L) * (r⁻¹) ^ n from by
      funext n; rw [dlb_zpow_sub_nat hrne]; ring]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnn1, hgeo]
  have hval2 : (∑' n : ℕ, b * r ^ (-(L + 1 + (n : ℤ)))) = b * r ^ (-(L+1)) * (r / (r - 1)) := by
    rw [show (fun n : ℕ => b * r ^ (-(L + 1 + (n : ℤ))))
        = fun n : ℕ => (b * r ^ (-(L+1))) * ((r⁻¹) ^ n) from by
      funext n
      rw [show -(L + 1 + (n : ℤ)) = -(L+1) - (n:ℤ) by ring, zpow_sub₀ hrne, zpow_natCast,
        div_eq_mul_inv, inv_pow]
      ring]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnn1, hgeo]
  -- assemble
  have h1 : (∑' n : ℕ, k (L - (n : ℤ))) ≤ a * r ^ L * (r / (r - 1)) := by
    refine (Summable.tsum_le_tsum hbr1 hsumm1 hg1).trans ?_
    rw [hval1]
  have h2 : (∑' n : ℕ, k (L + 1 + (n : ℤ))) ≤ b * r ^ (-(L+1)) * (r / (r - 1)) := by
    refine (Summable.tsum_le_tsum hbr2 hsumm2 hg2).trans ?_
    rw [hval2]
  refine (add_le_add h1 h2).trans ?_
  have hsqL : (r ^ L)^2 ≤ b / a := by
    calc (r ^ L)^2 ≤ Real.sqrt (b / a)^2 := pow_le_pow_left₀ (zpow_nonneg hr0.le L) hL1 2
      _ = b / a := hsqa
  have hsqL1 : b / a ≤ (r ^ (L+1))^2 := by
    calc b / a = Real.sqrt (b / a)^2 := hsqa.symm
      _ ≤ (r ^ (L+1))^2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL2 2
  have hA : a * r ^ L ≤ Real.sqrt (a * b) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    calc (a * r ^ L)^2 = a^2 * (r ^ L)^2 := by ring
      _ ≤ a^2 * (b / a) := mul_le_mul_of_nonneg_left hsqL (by positivity)
      _ = a * b := by field_simp
  have hB : b * r ^ (-(L+1)) ≤ Real.sqrt (a * b) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have hpoly : (b * r ^ (-(L+1)))^2 = b^2 / (r ^ (L+1))^2 := by
      rw [zpow_neg, div_eq_mul_inv, mul_pow, inv_pow]
    rw [hpoly, div_le_iff₀ (by positivity : (0:ℝ) < (r ^ (L+1))^2)]
    calc b^2 = b * b := by ring
      _ ≤ (a * (r ^ (L+1))^2) * b := by
          refine mul_le_mul_of_nonneg_right ?_ hb.le
          calc b = a * (b / a) := by rw [mul_comm]; exact (div_mul_cancel₀ b (ne_of_gt ha)).symm
            _ ≤ a * (r ^ (L+1))^2 := mul_le_mul_of_nonneg_left hsqL1 ha.le
      _ = a * b * (r ^ (L+1))^2 := by ring
  have hcoef : 0 ≤ r / (r - 1) := by positivity
  calc a * r ^ L * (r / (r - 1)) + b * r ^ (-(L+1)) * (r / (r - 1))
      = (r / (r - 1)) * (a * r ^ L + b * r ^ (-(L+1))) := by ring
    _ ≤ (r / (r - 1)) * (Real.sqrt (a * b) + Real.sqrt (a * b)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        linarith [hA, hB]
    _ = (2 * r / (r - 1)) * Real.sqrt (a * b) := by ring

/-- `((2:ℝ)^j)^2 = 4^j`. -/

theorem march_piece_grad_sup {m φ : ℝ → ℂ} {A : ℝ} (_hA : 0 ≤ A)
    (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ A)
    (hφ : MeasureTheory.Integrable φ (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hφsupp : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ 4) (j : ℤ) (x : ℝ) :
    ‖FourierTransform.fourier (fun ξ : ℝ => (ξ : ℂ) * m ξ * φ ((2:ℝ)^(-j) * ξ)) x‖
      ≤ 4 * A * (2:ℝ)^j * ((2:ℝ)^j * ∫ y : ℝ, ‖φ y‖) := by
  have h2 : (0:ℝ) < (2:ℝ)^j := zpow_pos (by norm_num) j
  have ha : (0:ℝ) < (2:ℝ)^(-j) := zpow_pos (by norm_num) (-j)
  have hpt : ∀ ξ : ℝ, ‖(ξ : ℂ) * m ξ * φ ((2:ℝ)^(-j) * ξ)‖
      ≤ (4 * A * (2:ℝ)^j) * ‖φ ((2:ℝ)^(-j) * ξ)‖ := by
    intro ξ
    by_cases h : φ ((2:ℝ)^(-j) * ξ) = 0
    · rw [h]; simp
    · have hle : |ξ| ≤ 4 * (2:ℝ)^j := by
        have h1 := hφsupp ((2:ℝ)^(-j) * ξ) h
        have habs : |(2:ℝ)^(-j) * ξ| = (2:ℝ)^(-j) * |ξ| := by
          rw [abs_mul, abs_of_pos ha]
        rw [habs] at h1
        have h3 : |ξ| ≤ 4 / (2:ℝ)^(-j) := (le_div_iff₀ ha).mpr (by rw [mul_comm]; exact h1)
        have h4 : 4 / (2:ℝ)^(-j) = 4 * (2:ℝ)^j := by
          rw [div_eq_iff (ne_of_gt ha)]
          rw [show (4:ℝ) * (2:ℝ)^j * (2:ℝ)^(-j) = 4 * ((2:ℝ)^(j + (-j))) by
            rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; ring]
          rw [add_neg_cancel, zpow_zero, mul_one]
        linarith [h3, h4.ge]
      have hξ : ‖(ξ : ℂ)‖ = |ξ| := by simp
      calc ‖(ξ : ℂ) * m ξ * φ ((2:ℝ)^(-j) * ξ)‖
          = |ξ| * ‖m ξ‖ * ‖φ ((2:ℝ)^(-j) * ξ)‖ := by
            rw [norm_mul, norm_mul, hξ]
        _ ≤ (4 * (2:ℝ)^j) * A * ‖φ ((2:ℝ)^(-j) * ξ)‖ := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul hle (hmb ξ) (norm_nonneg _) (by positivity)) (norm_nonneg _)
        _ = (4 * A * (2:ℝ)^j) * ‖φ ((2:ℝ)^(-j) * ξ)‖ := by ring
  have hint : MeasureTheory.Integrable (fun ξ : ℝ => ‖φ ((2:ℝ)^(-j) * ξ)‖)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    hφ.norm.comp_mul_left' (ne_of_gt ha)
  have hscal : (∫ ξ : ℝ, ‖φ ((2:ℝ)^(-j) * ξ)‖) = (2:ℝ)^j * ∫ y : ℝ, ‖φ y‖ := by
    have hkey := BourgainBlock.integral_eq_smul_integral_comp_mul_left
      (fun y : ℝ => ‖φ y‖) ha
    rw [smul_eq_mul] at hkey
    rw [hkey, ← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), add_neg_cancel, zpow_zero,
      one_mul]
  refine (dlb_fourier_enorm_le_integral _ x).trans ?_
  calc ∫ ξ : ℝ, ‖(ξ : ℂ) * m ξ * φ ((2:ℝ)^(-j) * ξ)‖
      ≤ ∫ ξ : ℝ, (4 * A * (2:ℝ)^j) * ‖φ ((2:ℝ)^(-j) * ξ)‖ :=
        MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun ξ => norm_nonneg _)
          (hint.const_mul _) (Eventually.of_forall fun ξ => hpt ξ)
    _ = (4 * A * (2:ℝ)^j) * ∫ ξ : ℝ, ‖φ ((2:ℝ)^(-j) * ξ)‖ :=
        MeasureTheory.integral_const_mul _ _
    _ = 4 * A * (2:ℝ)^j * ((2:ℝ)^j * ∫ y : ℝ, ‖φ y‖) := by rw [hscal]

/-- **(L2) The derivative of a dyadic piece also decays as `O(A/|x|²)`.**

Same statement as (L1) but with the decay of `dlb_piece_kernel_bound_two`.  The two together give
the `min`-estimate

  `‖𝓕(ξ ↦ ξ · m ξ · φ(2^{-j}ξ))(x)‖ ≤ C A min(2^{2j}, |x|^{-2})` ,   `x ≠ 0` ,

which is what the mean-value step of (L3) consumes.

**Route (for the next session).**  The `ξ`-factor is absorbed by rescaling the bump:
`ξ · φ(2^{-j}ξ) = 2^j · 	ilde φ(2^{-j}ξ)` with `	ilde φ(y) := y · φ(y)`.  Hence

  `𝓕(ξ ↦ ξ · m ξ · φ(2^{-j}ξ)) = 2^j · 𝓕(ξ ↦ m ξ · 	ilde φ(2^{-j}ξ))` ,

and `dlb_piece_kernel_bound_two` (already proved, in `dyadic_mikhlin.lean`) applied to the pair
`(m, 	ilde φ)` gives `(2π|x|)^{-2} · 63 · A · 	ilde C · 2^{-j}`; multiplying by `2^j` gives the
claim with `~C ≤ 6C` under the *unweighted* hypotheses on `φ` below plus the support condition
(the same hypothesis set as `dlb_piece_kernel_bound_two` itself):
`‖~φ y‖ ≤ 4C`, `‖~φ' y‖ ≤ 5C`, `‖~φ'' y‖ ≤ 6C`.

**Route (final; no Fourier-transform scaling is needed).**  Absorb the `ξ`-factor into a *scaled
bump*: `ξ φ(2^{-j}ξ) = 2^j · Ψ(2^{-j}ξ)` with `Ψ(y) := 2^j · y φ(y)`.  Then the two integrands
`m ξ · Ψ(2^{-j}ξ)` and `ξ m ξ φ(2^{-j}ξ)` are equal **pointwise**, so the linearity of `𝓕` in a
constant is never invoked; and `dlb_piece_kernel_bound_two`, applied to the pair `(m, Ψ)`, gives
`(2π|x|)^{-2} · 63 · A · (2^j · 6C) · 2^{-j} = (2π|x|)^{-2} · 378 A C` — the `2^j` cancels in the
*scalar* domain.  `Ψ` meets the sibling's hypotheses with constant `6C` because the rescaled bump
`ψ(y) = y φ(y)` has `‖ψ‖, ‖ψ'‖, ‖ψ''‖ ≤ 6C`: from the unweighted bounds on `φ` and the fact that
`|y| ≤ 4` wherever `φ`, `φ'` or `φ''` is nonzero — which is exactly what the hypothesis `hvan`
below supplies (it is the natural "the bump and its first two derivatives vanish off the annulus"
condition, and avoids the `deriv`-of-a-locally-zero-function detour).

**Remaining work: 6 mechanical fixes.**  A full staged proof was type-checked up to these; each of
these is a name/tactic mismatch, not mathematics:

1. `hψ1`: `deriv_mul`'s LHS is `deriv (c * d) y` for the *function* product, which does not unify
   with `deriv (fun y => ↑y * φ y) y`.  Insert
   `change deriv ((fun y : ℝ => (y : ℂ)) * φ) y = φ y + (y : ℂ) * deriv φ y` before the `rw`.
2. `hψ2`: the same for `dlb_iteratedDeriv_two_mul` — insert the analogous `change` with the
   function product.
3. `hψ2b` (first branch of the `calc`): the preceding `_ = 2 * ‖deriv φ y‖ + ...` step already
   rewrote the goal, so the extra `rw [norm_mul, h2c]` fails ("no occurrence of `‖?a * ?b‖`").
   Replace that branch body by `linarith [hφ1 y]`.
4. `hψsupp` / `hΨsupp`: after `rw [hψ] at hy` (resp. `rw [hΨ] at hy`) the hypothesis is
   `(fun y => ↑y * φ y) y = 0`, i.e. **not** beta-reduced, so `rw [h, mul_zero]` fails; use
   `by simp [h]`.
5. `hfund`'s `hcast` (`↑(2^j) · ↑(2^{-j}ξ) = ↑ξ`): the term elaborates as `(↑2)^j * ↑(…)`, so
   `← Complex.ofReal_mul` does not fire.  Either `rw [Complex.ofReal_zpow]` first (giving
   `(2:ℂ)^j * ↑(2^{-j}ξ)`) and then the `zpow` normalisation, or prove
   `↑((2:ℝ)^j * ((2:ℝ)^(-j) * ξ)) = ↑ξ` by `push_cast`.
6. `hfund`'s closing `calc`: same beta-reduction issue as (4) — insert `show`/`simp only []` before
   the pointwise `ring`.
**Second pass: the six fixes were applied and the count fell 10 → 6, each of the six exposing one
further elaboration detail.  Exact state of play (all mechanical):**

* `Complex.ofRealCLM.contDiff.mul hφ` works, but the `change` for `deriv_mul` must use the
  **coercion** form, not the lambda: `change deriv ((⇑Complex.ofRealCLM) * φ) y = …` (the lambda
  `fun y => ↑y` does not unify with `⇑Complex.ofRealCLM`); likewise for `dlb_iteratedDeriv_two_mul`.
* **`RCLike.norm_ofReal` does not fire on `‖(2:ℂ)^j‖`**: the term `((2:ℝ)^j : ℂ)` elaborates as
  `(↑2)^j`, so one needs `norm_zpow` first:
  `rw [hΨ, norm_mul, norm_zpow, RCLike.norm_ofReal, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]`
  (or prove `‖(2:ℂ)^j‖ = (2:ℝ)^j` once and reuse it).
* `Complex.ofReal_mul` has the orientation `↑(r*s) = ↑r * ↑s`; the cast identity `hcast` must be
  *used* in that direction (or with `← Complex.ofReal_zpow j 2` first).
* **Cleanest way to kill the last three at once**: define the scaled bump as
  `Ψ := fun y => (((y * (2:ℝ)^j : ℝ)) : ℂ) * φ y` (cast of a *real* product!) instead of
  `2^j • (y φ y)`.  Then `Ψ(2^{-j}ξ) = ↑ξ · φ(2^{-j}ξ)` follows from the *real* identity
  `(2:ℝ)^(-j) * ξ * (2:ℝ)^j = ξ` by a single `rw`, and `hfund` becomes
  `funext ξ; rw [hΨ]; simp only []; rw [hreal]; ring` — no cast juggling at all.  The price is
  recomputing `Ψ`, `Ψ'`, `Ψ''` under the new definition (constant `6·2^j·C` again, via
  `deriv (fun y => ↑(y·2^j)) = ↑(2^j)`), which is the same amount of work as the current block.

So: (L2) is a *transcription* job with a known-best route, not an open mathematical question.

## Third pass: the block was pasted in and run — ONE root cause remains

The staged `Ψ`-block above was pasted in and compiled.  Error count 10 → 6, and the six are all one
root cause (plus two easy consequences), namely:

**`(2 : ℂ)` is `OfNat.ofNat 2 : ℂ`, NOT the coercion `↑(2 : ℝ)`.**  So

* `rw [RCLike.norm_ofReal]` **never fires** on `‖(2 : ℂ)‖` (and, more importantly, `rw [RCLike.norm_ofReal]`
  does not fire at all as a `rw` — it is only a `simp` lemma; the working pattern, used in (L1), is a
  `have : ‖(r : ℂ)‖ = |r| := by simp`).
* `((2 : ℝ) ^ j : ℂ)` elaborates as `((2 : ℂ)) ^ j`, i.e. as `OfNat 2` raised to `j`, so it also is not
  a coercion and `RCLike.norm_ofReal` cannot see it.  Fix once and for all with a named lemma

  ```lean
  have h2jnorm : ‖((2:ℂ)^j)‖ = (2:ℝ)^j := by
    rw [norm_zpow]
    norm_num                      -- `‖(2:ℂ)‖ = 2` is a `norm_num` fact
  ```

  and rewrite with `h2jnorm` (not `RCLike.norm_ofReal`) everywhere the `(2 : ℂ)^j` factor appears.
* consequence in `hderiv1`: after `heq` the goal is `deriv ((fun _ => (2:ℂ)^j)) * ⇑Complex.ofRealCLM) y`;
  `deriv_const_mul` then matches only with that exact `⇑`-coercion shape (the `change` line in the
  staged block is already written that way), and `(2:ℂ)^j` must be used in `heq` rather than
  `((2:ℝ)^j : ℂ)` for the same reason.
* consequence: in `hΨ1` the `ring` after the two rewrites is redundant (the goal is already closed) —
  drop it; and in `hΨb`/`hΨ1b`/`hΨ2b` the remaining scalar manipulation is `nlinarith`/`ring` with
  `h2j.le` and `hC`, not `positivity`.

## (L2): the elaboration history, kept because (L3) will meet the same traps

**`(L2)` is PROVED.**  The three passes below are what it cost, and every trap in them recurs in
(L3), so they are kept.  The final proof is the block marked "`Ψ`-block" together with the
`have e1 / have e2 / have hA / have hB` restructuring of the two norm- and scalar-steps.

### The `Ψ`-block, verbatim

The following is the whole content of the new `Ψ`-block, with the elaboration traps already avoided
(cast of a **real** product, so `RCLike.norm_ofReal` fires everywhere; `change` with the `⇑`
coercion; `funext` for the function-level derivative identity).  Drop it in place of the current
`ψ`/`Ψ` block and (L2)'s body becomes `hkey := dlb_piece_kernel_bound_two … ; rw [hfund] at hkey`.

```lean
  have hderiv1 : ∀ y : ℝ, deriv (fun y : ℝ => (((y * (2:ℝ)^j : ℝ)) : ℂ)) y = ((2:ℝ)^j : ℂ) := by
    intro y
    have heq : (fun z : ℝ => (((z * (2:ℝ)^j : ℝ)) : ℂ))
        = fun z : ℝ => ((2:ℝ)^j : ℂ) * (z : ℂ) := by
      funext z; push_cast; ring
    rw [heq, deriv_const_mul _ Complex.ofRealCLM.differentiableAt, hlinAt y, mul_one]
  have hlin2a : ∀ y : ℝ, iteratedDeriv 2 (fun y : ℝ => (((y * (2:ℝ)^j : ℝ)) : ℂ)) y = 0 := by
    intro y
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
      funext hderiv1]
    simp
  set Ψ : ℝ → ℂ := fun y => (((y * (2:ℝ)^j : ℝ)) : ℂ) * φ y with hΨ
  have hΨcd : ContDiff ℝ 2 Ψ := by
    rw [hΨ]
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)).mul hφ
  have hΨ1 : ∀ y : ℝ, deriv Ψ y
      = ((2:ℝ)^j : ℂ) * φ y + (((y * (2:ℝ)^j : ℝ)) : ℂ) * deriv φ y := by
    intro y
    rw [hΨ]
    change deriv ((fun z : ℝ => (((z * (2:ℝ)^j : ℝ)) : ℂ)) * φ) y = _
    rw [deriv_mul (((Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)).differentiable
      (by norm_num)).differentiableAt) (hφ.differentiable (by norm_num) y), hderiv1 y]
    ring
  have hΨ2 : ∀ y : ℝ, iteratedDeriv 2 Ψ y
      = 2 * ((2:ℝ)^j : ℂ) * deriv φ y + (((y * (2:ℝ)^j : ℝ)) : ℂ) * iteratedDeriv 2 φ y := by
    intro y
    rw [hΨ]
    change iteratedDeriv 2 ((fun z : ℝ => (((z * (2:ℝ)^j : ℝ)) : ℂ)) * φ) y = _
    rw [dlb_iteratedDeriv_two_mul (f := fun z : ℝ => (((z * (2:ℝ)^j : ℝ)) : ℂ)) (g := φ)
      (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)) hφ y, hlin2a y, hderiv1 y]
    ring
  -- bounds: `‖Ψ‖, ‖Ψ'‖, ‖Ψ''‖ ≤ (2:ℝ)^j * (6*C)`, and `Ψ ≠ 0 → 1/2 ≤ |·| ≤ 4`
  -- (`norm_mul`, `RCLike.norm_ofReal`, `abs_mul`, `abs_of_pos h2j`, then `hy4a/hy4b/hy4c`)
  -- the identification (one `rw`, no cast juggling):
  have hreal : (2:ℝ)^(-j) * ξ * (2:ℝ)^j = ξ := by
    rw [mul_assoc, mul_comm ξ, ← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
      neg_add_cancel, zpow_zero, one_mul]
  have hfund : (fun ξ : ℝ => m ξ * Ψ ((2:ℝ)^(-j) * ξ))
      = fun ξ : ℝ => (ξ : ℂ) * m ξ * φ ((2:ℝ)^(-j) * ξ) := by
    funext ξ; rw [hΨ]; simp only []; rw [hreal]; ring
``` -/


theorem march_piece_grad_decay {m φ : ℝ → ℂ} {A C : ℝ}
    (hm : ContDiff ℝ 2 m) (hφ : ContDiff ℝ 2 φ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hφb : ∀ ξ : ℝ, ‖φ ξ‖ ≤ C) (hφ1 : ∀ ξ : ℝ, ‖deriv φ ξ‖ ≤ C)
    (hφ2 : ∀ ξ : ℝ, ‖iteratedDeriv 2 φ ξ‖ ≤ C)
    (hvan : ∀ ξ : ℝ, 4 < |ξ| → φ ξ = 0 ∧ deriv φ ξ = 0 ∧ iteratedDeriv 2 φ ξ = 0)
    (hφsupp : ∀ ξ : ℝ, φ ξ ≠ 0 → (1 / 2 : ℝ) ≤ |ξ| ∧ |ξ| ≤ 4)
    (j : ℤ) (x : ℝ) (hx : x ≠ 0) :
    ‖FourierTransform.fourier (fun ξ : ℝ => (ξ : ℂ) * m ξ * φ ((2:ℝ)^(-j) * ξ)) x‖
      ≤ (2 * Real.pi * |x|) ^ (-2 : ℤ) * (378 * A * C) := by
  have h2j : (0:ℝ) < (2:ℝ)^j := zpow_pos (by norm_num) j
  have h2jnorm : ‖((2:ℂ)^j)‖ = (2:ℝ)^j := by
    rw [norm_zpow]
    norm_num
  have hcastnorm : ∀ z : ℝ, ‖(((z * (2:ℝ)^j : ℝ)) : ℂ)‖ = |z| * (2:ℝ)^j := by
    intro z
    rw [show ‖(((z * (2:ℝ)^j : ℝ)) : ℂ)‖ = |(z * (2:ℝ)^j : ℝ)| from by simp, abs_mul,
      abs_of_pos h2j]
  have hlin : deriv (fun y : ℝ => (y : ℂ)) = fun _ : ℝ => 1 := by
    funext y
    show deriv (⇑Complex.ofRealCLM) y = 1
    rw [(Complex.ofRealCLM.hasDerivAt (x := y)).deriv]
    simp
  have hlinAt : ∀ y : ℝ, deriv (fun y : ℝ => (y : ℂ)) y = 1 := fun y => by rw [hlin]
  have hy4a : ∀ y : ℝ, φ y ≠ 0 → |y| ≤ 4 := fun y h => (hφsupp y h).2
  have hy4b : ∀ y : ℝ, deriv φ y ≠ 0 → |y| ≤ 4 := by
    intro y h
    by_contra hc
    exact h (hvan y (lt_of_not_ge hc)).2.1
  have hy4c : ∀ y : ℝ, iteratedDeriv 2 φ y ≠ 0 → |y| ≤ 4 := by
    intro y h
    by_contra hc
    exact h (hvan y (lt_of_not_ge hc)).2.2
  have hlin_cd : ContDiff ℝ 2 (fun y : ℝ => (((y * (2:ℝ)^j : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)
  have hlin_da : ∀ y : ℝ, DifferentiableAt ℝ (fun y : ℝ => (((y * (2:ℝ)^j : ℝ)) : ℂ)) y :=
    fun y => (hlin_cd.differentiable (by norm_num)).differentiableAt
  have hderiv1 : ∀ y : ℝ, deriv (fun y : ℝ => (((y * (2:ℝ)^j : ℝ)) : ℂ)) y = (2:ℂ)^j := by
    intro y
    have heq : (fun z : ℝ => (((z * (2:ℝ)^j : ℝ)) : ℂ))
        = fun z : ℝ => (2:ℂ)^j * (z : ℂ) := by
      funext z
      push_cast
      ring
    rw [heq]
    change deriv (fun z : ℝ => (2:ℂ)^j * (⇑Complex.ofRealCLM) z) y = (2:ℂ)^j
    have hCLM : deriv (⇑Complex.ofRealCLM) y = 1 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).deriv
    rw [deriv_const_mul _ Complex.ofRealCLM.differentiableAt, hCLM, mul_one]
  have hlin2a : ∀ y : ℝ, iteratedDeriv 2 (fun y : ℝ => (((y * (2:ℝ)^j : ℝ)) : ℂ)) y = 0 := by
    intro y
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
      funext hderiv1]
    simp
  set Ψ : ℝ → ℂ := fun y => (((y * (2:ℝ)^j : ℝ)) : ℂ) * φ y with hΨ
  have hΨcd : ContDiff ℝ 2 Ψ := by
    rw [hΨ]
    exact hlin_cd.mul hφ
  have hΨ1 : ∀ y : ℝ, deriv Ψ y = (2:ℂ)^j * φ y + (((y * (2:ℝ)^j : ℝ)) : ℂ) * deriv φ y := by
    intro y
    rw [hΨ]
    change deriv ((fun z : ℝ => (((z * (2:ℝ)^j : ℝ)) : ℂ)) * φ) y = _
    rw [deriv_mul (hlin_da y) (hφ.differentiable (by norm_num) y), hderiv1 y]
  have hΨ2 : ∀ y : ℝ, iteratedDeriv 2 Ψ y
      = 2 * (2:ℂ)^j * deriv φ y + (((y * (2:ℝ)^j : ℝ)) : ℂ) * iteratedDeriv 2 φ y := by
    intro y
    rw [hΨ]
    change iteratedDeriv 2 ((fun z : ℝ => (((z * (2:ℝ)^j : ℝ)) : ℂ)) * φ) y = _
    rw [dlb_iteratedDeriv_two_mul (f := fun z : ℝ => (((z * (2:ℝ)^j : ℝ)) : ℂ)) (g := φ)
      hlin_cd hφ y, hlin2a y, hderiv1 y]
    ring
  have hΨb : ∀ y : ℝ, ‖Ψ y‖ ≤ (2:ℝ)^j * (6 * C) := by
    intro y
    rw [hΨ]
    simp only []
    rw [norm_mul, hcastnorm y]
    by_cases h : φ y = 0
    · rw [h, norm_zero, mul_zero]
      exact mul_nonneg h2j.le (mul_nonneg (by norm_num) hC)
    · have h4 : |y| * ‖φ y‖ ≤ 4 * C :=
        mul_le_mul (hy4a y h) (hφb y) (norm_nonneg _) (by norm_num)
      have h5 : (2:ℝ)^j * (|y| * ‖φ y‖) ≤ (2:ℝ)^j * (4 * C) :=
        mul_le_mul_of_nonneg_left h4 h2j.le
      have h6 : (2:ℝ)^j * (4 * C) ≤ (2:ℝ)^j * (6 * C) :=
        mul_le_mul_of_nonneg_left (by linarith [hC]) h2j.le
      calc |y| * (2:ℝ)^j * ‖φ y‖ = (2:ℝ)^j * (|y| * ‖φ y‖) := by ring
        _ ≤ (2:ℝ)^j * (4 * C) := h5
        _ ≤ (2:ℝ)^j * (6 * C) := h6
  have hΨ1b : ∀ y : ℝ, ‖deriv Ψ y‖ ≤ (2:ℝ)^j * (6 * C) := by
    intro y
    rw [hΨ1 y]
    have e1 : ‖(2:ℂ)^j * φ y‖ = (2:ℝ)^j * ‖φ y‖ := by rw [norm_mul, h2jnorm]
    have e2 : ‖(((y * (2:ℝ)^j : ℝ)) : ℂ) * deriv φ y‖
        = (2:ℝ)^j * (|y| * ‖deriv φ y‖) := by
      rw [norm_mul, hcastnorm y]
      ring
    have hA : (2:ℝ)^j * ‖φ y‖ ≤ (2:ℝ)^j * C := mul_le_mul_of_nonneg_left (hφb y) h2j.le
    have hB : (2:ℝ)^j * (|y| * ‖deriv φ y‖) ≤ (2:ℝ)^j * (4 * C) := by
      refine mul_le_mul_of_nonneg_left ?_ h2j.le
      by_cases h : deriv φ y = 0
      · rw [h, norm_zero, mul_zero]
        exact mul_nonneg (by norm_num) hC
      · exact mul_le_mul (hy4b y h) (hφ1 y) (norm_nonneg _) (by norm_num)
    have hsum : (2:ℝ)^j * C + (2:ℝ)^j * (4 * C) ≤ (2:ℝ)^j * (6 * C) := by
      nlinarith [h2j.le, hC]
    calc ‖(2:ℂ)^j * φ y + (((y * (2:ℝ)^j : ℝ)) : ℂ) * deriv φ y‖
        ≤ ‖(2:ℂ)^j * φ y‖ + ‖(((y * (2:ℝ)^j : ℝ)) : ℂ) * deriv φ y‖ := norm_add_le _ _
      _ = (2:ℝ)^j * ‖φ y‖ + (2:ℝ)^j * (|y| * ‖deriv φ y‖) := by rw [e1, e2]
      _ ≤ (2:ℝ)^j * C + (2:ℝ)^j * (4 * C) := add_le_add hA hB
      _ ≤ (2:ℝ)^j * (6 * C) := hsum
  have hΨ2b : ∀ y : ℝ, ‖iteratedDeriv 2 Ψ y‖ ≤ (2:ℝ)^j * (6 * C) := by
    intro y
    rw [hΨ2 y]
    have hn1 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have e1 : ‖2 * (2:ℂ)^j * deriv φ y‖ = 2 * (2:ℝ)^j * ‖deriv φ y‖ := by
      rw [norm_mul, norm_mul, hn1, h2jnorm]
    have e2 : ‖(((y * (2:ℝ)^j : ℝ)) : ℂ) * iteratedDeriv 2 φ y‖
        = (2:ℝ)^j * (|y| * ‖iteratedDeriv 2 φ y‖) := by
      rw [norm_mul, hcastnorm y]
      ring
    have hA : 2 * (2:ℝ)^j * ‖deriv φ y‖ ≤ 2 * (2:ℝ)^j * C :=
      mul_le_mul_of_nonneg_left (hφ1 y) (mul_nonneg (by norm_num) h2j.le)
    have hB : (2:ℝ)^j * (|y| * ‖iteratedDeriv 2 φ y‖) ≤ (2:ℝ)^j * (4 * C) := by
      refine mul_le_mul_of_nonneg_left ?_ h2j.le
      by_cases h : iteratedDeriv 2 φ y = 0
      · rw [h, norm_zero, mul_zero]
        exact mul_nonneg (by norm_num) hC
      · exact mul_le_mul (hy4c y h) (hφ2 y) (norm_nonneg _) (by norm_num)
    have hsum : 2 * (2:ℝ)^j * C + (2:ℝ)^j * (4 * C) = (2:ℝ)^j * (6 * C) := by ring
    calc ‖2 * (2:ℂ)^j * deriv φ y + (((y * (2:ℝ)^j : ℝ)) : ℂ) * iteratedDeriv 2 φ y‖
        ≤ ‖2 * (2:ℂ)^j * deriv φ y‖
            + ‖(((y * (2:ℝ)^j : ℝ)) : ℂ) * iteratedDeriv 2 φ y‖ := norm_add_le _ _
      _ = 2 * (2:ℝ)^j * ‖deriv φ y‖ + (2:ℝ)^j * (|y| * ‖iteratedDeriv 2 φ y‖) := by rw [e1, e2]
      _ ≤ 2 * (2:ℝ)^j * C + (2:ℝ)^j * (4 * C) := add_le_add hA hB
      _ = (2:ℝ)^j * (6 * C) := hsum
  have hΨsupp : ∀ y : ℝ, Ψ y ≠ 0 → (1 / 2 : ℝ) ≤ |y| ∧ |y| ≤ 4 := by
    intro y hy
    rw [hΨ] at hy
    simp only [] at hy
    refine hφsupp y ?_
    intro h
    exact hy (by simp [h])
  have hfund : (fun ξ : ℝ => m ξ * Ψ ((2:ℝ)^(-j) * ξ))
      = fun ξ : ℝ => (ξ : ℂ) * m ξ * φ ((2:ℝ)^(-j) * ξ) := by
    funext ξ
    rw [hΨ]
    simp only []
    have hreal : (2:ℝ)^(-j) * ξ * (2:ℝ)^j = ξ := by
      rw [mul_assoc, mul_comm ξ, ← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
        neg_add_cancel, zpow_zero, one_mul]
    rw [hreal]
    ring
  have hkey := dlb_piece_kernel_bound_two (m := m) (φ := Ψ) hm hΨcd hA
    (mul_nonneg h2j.le (mul_nonneg (by norm_num) hC)) hmb hm1 hm2 hΨb hΨ1b hΨ2b hΨsupp j x hx
  rw [hfund] at hkey
  refine hkey.trans (le_of_eq ?_)
  have harith : 63 * A * ((2:ℝ)^j * (6 * C)) * (2:ℝ)^(-j)
      = 378 * A * C := by
    rw [show 63 * A * ((2:ℝ)^j * (6 * C)) * (2:ℝ)^(-j)
        = 378 * A * C * ((2:ℝ)^j * (2:ℝ)^(-j)) by ring]
    rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), add_neg_cancel, zpow_zero, mul_one]
  rw [harith]


/-! ## The dyadic bump and its annulus difference -/

/-- A fixed smooth bump: `1` on `[-1,1]`, supported in `[-2,2]`. -/
def mkRhoB : ContDiffBump (0:ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

lemma mkRhoB_zero {x : ℝ} (hx : 2 ≤ |x|) : mkRhoB x = 0 := by
  apply mkRhoB.zero_of_le_dist
  rw [Real.dist_eq, sub_zero]; exact hx

lemma mkRhoB_one {x : ℝ} (hx : |x| ≤ 1) : mkRhoB x = 1 := by
  apply mkRhoB.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx

/-- The annulus bump `Ψ(u) = ρ(u/2) - ρ(u)`, supported in `{1/2 ≤ |u| ≤ 4}`. -/
def mkPsi : ℝ → ℂ := fun u => ((mkRhoB (u/2) - mkRhoB u : ℝ) : ℂ)

lemma mkPsi_supp (u : ℝ) (hu : mkPsi u ≠ 0) : (1/2:ℝ) ≤ |u| ∧ |u| ≤ 4 := by
  have h2 : (0:ℝ) < 2 := by norm_num
  constructor
  · by_contra h
    rw [not_le] at h
    have ha : |u / 2| ≤ 1 := by rw [abs_div, abs_of_pos h2]; linarith
    have hb : |u| ≤ 1 := by linarith
    simp only [mkPsi, mkRhoB_one ha, mkRhoB_one hb, sub_self, Complex.ofReal_zero] at hu
    exact hu rfl
  · by_contra h
    rw [not_le] at h
    have ha : 2 ≤ |u / 2| := by rw [abs_div, abs_of_pos h2]; linarith
    have hb : 2 ≤ |u| := by linarith
    simp only [mkPsi, mkRhoB_zero ha, mkRhoB_zero hb, sub_self, Complex.ofReal_zero] at hu
    exact hu rfl

lemma mkPsi_contDiff : ContDiff ℝ 2 mkPsi := by
  have h1 : ContDiff ℝ 2 (fun u : ℝ => u / 2) := contDiff_id.div_const 2
  have h : ContDiff ℝ 2 (fun u : ℝ => mkRhoB (u/2) - mkRhoB u) :=
    (mkRhoB.contDiff.comp h1).sub mkRhoB.contDiff
  exact Complex.ofRealCLM.contDiff.comp h

lemma mkPsi_hasCompactSupport : HasCompactSupport mkPsi := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-4:ℝ) 4) isCompact_Icc
  intro u hu
  rw [Set.mem_Icc]
  exact abs_le.mp (mkPsi_supp u hu).2

/-- A single constant bounding `Ψ`, `Ψ'` and `Ψ''`. -/
lemma mkPsi_bounds : ∃ C : ℝ, 0 < C ∧ (∀ x : ℝ, ‖mkPsi x‖ ≤ C) ∧
    (∀ x : ℝ, ‖deriv mkPsi x‖ ≤ C) ∧ (∀ x : ℝ, ‖iteratedDeriv 2 mkPsi x‖ ≤ C) := by
  obtain ⟨C0, hC0⟩ := mkPsi_hasCompactSupport.exists_bound_of_continuous mkPsi_contDiff.continuous
  have hd1 : HasCompactSupport (deriv mkPsi) := mkPsi_hasCompactSupport.deriv
  obtain ⟨C1, hC1⟩ := hd1.exists_bound_of_continuous
    (by simpa only [iteratedDeriv_one] using mkPsi_contDiff.continuous_iteratedDeriv 1 (by simp))
  have hd2 : HasCompactSupport (iteratedDeriv 2 mkPsi) := by
    have heq : iteratedDeriv 2 mkPsi = deriv (deriv mkPsi) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [heq]; exact hd1.deriv
  obtain ⟨C2, hC2⟩ := hd2.exists_bound_of_continuous
    (mkPsi_contDiff.continuous_iteratedDeriv 2 (by simp))
  refine ⟨|max (max C0 C1) C2| + 1, by positivity, ?_, ?_, ?_⟩
  · intro x
    have h := hC0 x
    have hle : C0 ≤ |max (max C0 C1) C2| := by
      linarith [le_abs_self (max (max C0 C1) C2), le_max_left C0 C1,
        le_max_left (max C0 C1) C2]
    linarith
  · intro x
    have h := hC1 x
    have hle : C1 ≤ |max (max C0 C1) C2| := by
      linarith [le_abs_self (max (max C0 C1) C2), le_max_right C0 C1,
        le_max_left (max C0 C1) C2]
    linarith
  · intro x
    have h := hC2 x
    have hle : C2 ≤ |max (max C0 C1) C2| := by
      linarith [le_abs_self (max (max C0 C1) C2), le_max_right (max C0 C1) C2]
    linarith

/-! ## Basic facts about `mkPsi` -/

lemma mkPsi_integrable : Integrable mkPsi :=
  mkPsi_contDiff.continuous.integrable_of_hasCompactSupport mkPsi_hasCompactSupport

lemma mkPsi_deriv_integrable : Integrable (deriv mkPsi) := by
  refine (mkPsi_contDiff.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport ?_
  exact mkPsi_hasCompactSupport.deriv

lemma mkPsi_deriv2_integrable : Integrable (iteratedDeriv 2 mkPsi) := by
  have hc : Continuous (iteratedDeriv 2 mkPsi) := mkPsi_contDiff.continuous_iteratedDeriv 2 (by norm_num)
  have hsupp : HasCompactSupport (iteratedDeriv 2 mkPsi) := by
    have heq : iteratedDeriv 2 mkPsi = deriv (deriv mkPsi) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [heq]; exact mkPsi_hasCompactSupport.deriv.deriv
  exact hc.integrable_of_hasCompactSupport hsupp

/-- `mkPsi`, `deriv mkPsi` and `iteratedDeriv 2 mkPsi` vanish for `|ξ| > 4`. -/
lemma mkPsi_van : ∀ ξ : ℝ, 4 < |ξ| → mkPsi ξ = 0 ∧ deriv mkPsi ξ = 0 ∧ iteratedDeriv 2 mkPsi ξ = 0 := by
  intro ξ hξ
  have hmem : {u : ℝ | 4 < |u|} ∈ 𝓝 ξ :=
    (isOpen_lt continuous_const continuous_id.abs).mem_nhds hξ
  have hzero : mkPsi =ᶠ[𝓝 ξ] (0 : ℝ → ℂ) := by
    filter_upwards [hmem] with u hu
    simp only [Pi.zero_apply]
    by_contra h
    exact absurd (mkPsi_supp u h).2 (not_le.mpr hu)
  refine ⟨by simpa using hzero.self_of_nhds, ?_, ?_⟩
  · rw [Filter.EventuallyEq.deriv_eq hzero]; simp
  · have hd : deriv mkPsi =ᶠ[𝓝 ξ] (0 : ℝ → ℂ) := by
      have := hzero.deriv
      simpa using this
    have h2 : iteratedDeriv 2 mkPsi ξ = deriv (deriv mkPsi) ξ := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2, Filter.EventuallyEq.deriv_eq hd]; simp

/-- Pulling a constant out of the Fourier transform. -/
lemma mk_fourier_const_mul (c : ℂ) (g : ℝ → ℂ) (t : ℝ) :
    FourierTransform.fourier (fun x => c * g x) t = c * FourierTransform.fourier g t := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-! ## The dyadic pieces of a Mikhlin symbol -/

/-- The `j`-th annulus piece of the symbol `m`: `ξ ↦ m ξ · Ψ(2^{-j} ξ)`. -/
def mkPiece (m : ℝ → ℂ) (j : ℤ) : ℝ → ℂ := fun ξ => m ξ * mkPsi ((2:ℝ)^(-j) * ξ)

/-- The "one derivative up" version of the piece. -/
def mkPieceG (m : ℝ → ℂ) (j : ℤ) : ℝ → ℂ := fun ξ => (ξ : ℂ) * m ξ * mkPsi ((2:ℝ)^(-j) * ξ)

lemma mkPsi_zero_of_gt {u : ℝ} (hu : 4 < |u|) : mkPsi u = 0 := by
  by_contra h; exact absurd (mkPsi_supp u h).2 (not_le.mpr hu)

lemma mkPiece_hasCompactSupport (m : ℝ → ℂ) (j : ℤ) : HasCompactSupport (mkPiece m j) := by
  have h2j : 0 < (2:ℝ)^j := zpow_pos (by norm_num) j
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(4*(2:ℝ)^j)) (4*(2:ℝ)^j))
    isCompact_Icc
  intro ξ hξ
  have hΨ : mkPsi ((2:ℝ)^(-j) * ξ) ≠ 0 := fun hc => hξ (by rw [mkPiece, hc, mul_zero])
  have h := (mkPsi_supp ((2:ℝ)^(-j) * ξ) hΨ).2
  have h2nj : (2:ℝ)^(-j) = ((2:ℝ)^j)⁻¹ := by rw [zpow_neg]
  rw [h2nj, abs_mul, abs_of_pos (inv_pos.mpr h2j)] at h
  rw [Set.mem_Icc]
  rw [inv_mul_le_iff₀ h2j] at h
  exact abs_le.mp (h.trans_eq (mul_comm _ _))

lemma mkPieceG_hasCompactSupport (m : ℝ → ℂ) (j : ℤ) : HasCompactSupport (mkPieceG m j) := by
  have h2j : 0 < (2:ℝ)^j := zpow_pos (by norm_num) j
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(4*(2:ℝ)^j)) (4*(2:ℝ)^j))
    isCompact_Icc
  intro ξ hξ
  have h : mkPsi ((2:ℝ)^(-j) * ξ) ≠ 0 := by
    intro hc; refine hξ ?_; rw [mkPieceG, hc]; simp
  have hle := (mkPsi_supp ((2:ℝ)^(-j) * ξ) h).2
  have h2nj : (2:ℝ)^(-j) = ((2:ℝ)^j)⁻¹ := by rw [zpow_neg]
  rw [h2nj, abs_mul, abs_of_pos (inv_pos.mpr h2j)] at hle
  rw [Set.mem_Icc]
  rw [inv_mul_le_iff₀ h2j] at hle
  exact abs_le.mp (hle.trans_eq (mul_comm _ _))

lemma mkPiece_integrable {m : ℝ → ℂ} {A : ℝ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ, ‖m ξ‖ ≤ A)
    (j : ℤ) : Integrable (mkPiece m j) :=
  (hm.continuous.mul (mkPsi_contDiff.continuous.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    (mkPiece_hasCompactSupport m j)

lemma mkPieceG_integrable {m : ℝ → ℂ} {A : ℝ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ, ‖m ξ‖ ≤ A)
    (j : ℤ) : Integrable (mkPieceG m j) :=
  (((Complex.continuous_ofReal.mul hm.continuous).mul
    (mkPsi_contDiff.continuous.comp (continuous_const.mul continuous_id)))).integrable_of_hasCompactSupport
    (mkPieceG_hasCompactSupport m j)

lemma mkPiece_x_integrable {m : ℝ → ℂ} {A : ℝ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ, ‖m ξ‖ ≤ A)
    (j : ℤ) : Integrable (fun x : ℝ => x • mkPiece m j x) := by
  have hcont : Continuous (fun x : ℝ => x • (mkPiece m j x)) :=
    continuous_id.smul (hm.continuous.mul (mkPsi_contDiff.continuous.comp (continuous_const.mul continuous_id)))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine (mkPiece_hasCompactSupport m j).mono ?_
  intro x hx
  simp only [Function.mem_support, Pi.smul_apply] at hx ⊢
  intro hc; rw [hc] at hx; simp at hx

/-- **Decay of a dyadic piece's kernel.** -/
lemma mkPiece_decay {m : ℝ → ℂ} {A CΨ : ℝ} (hm : ContDiff ℝ 2 m) (hA : 0 ≤ A) (hCΨ : 0 ≤ CΨ)
    (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hΨb : ∀ ξ, ‖mkPsi ξ‖ ≤ CΨ) (hΨ1 : ∀ ξ, ‖deriv mkPsi ξ‖ ≤ CΨ)
    (hΨ2 : ∀ ξ, ‖iteratedDeriv 2 mkPsi ξ‖ ≤ CΨ)
    (j : ℤ) (x : ℝ) (hx : x ≠ 0) :
    ‖FourierTransform.fourier (mkPiece m j) x‖ ≤ (2 * Real.pi * |x|) ^ (-2 : ℤ) * (63 * A * CΨ * (2:ℝ)^(-j)) :=
  dlb_piece_kernel_bound_two hm mkPsi_contDiff hA hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2
    (fun ξ hξ => mkPsi_supp ξ hξ) j x hx

/-- **Size of a dyadic piece's kernel.** -/
lemma mkPiece_sup {m : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (j : ℤ) (x : ℝ) :
    ‖FourierTransform.fourier (mkPiece m j) x‖ ≤ A * ((2:ℝ)^j * ∫ y : ℝ, ‖mkPsi y‖) :=
  dlb_piece_kernel_bound_zero hA hmb mkPsi_integrable j x

/-- **The Fourier transform of `ξ ↦ ξ m ξ Ψ(2^{-j}ξ)` is the derivative of the kernel.** -/
lemma mkPiece_deriv {m : ℝ → ℂ} {A : ℝ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (j : ℤ) :
    deriv (FourierTransform.fourier (mkPiece m j))
      = fun z => (-2 * Real.pi * Complex.I) * FourierTransform.fourier (mkPieceG m j) z := by
  have h := Real.deriv_fourier (mkPiece_integrable hm hmb j) (mkPiece_x_integrable hm hmb j)
  rw [h]
  funext z
  have hfun : (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x:ℂ)) • mkPiece m j x)
      = fun x : ℝ => (-2 * Real.pi * Complex.I) * mkPieceG m j x := by
    funext x; simp only [mkPieceG, mkPiece, Pi.mul_apply]; rw [smul_eq_mul]; ring
  rw [hfun, mk_fourier_const_mul]

/-- Sup bound for the derivative of a dyadic piece's kernel. -/
lemma mkPiece_deriv_sup {m : ℝ → ℂ} {A : ℝ} (hm : ContDiff ℝ 2 m) (hA : 0 ≤ A)
    (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (j : ℤ) (z : ℝ) :
    ‖deriv (FourierTransform.fourier (mkPiece m j)) z‖ ≤ 2 * Real.pi * (4 * A * (2:ℝ)^j * ((2:ℝ)^j * ∫ y : ℝ, ‖mkPsi y‖)) := by
  rw [mkPiece_deriv hm hmb j]
  simp only
  rw [norm_mul]
  have h := march_piece_grad_sup (show (0:ℝ) ≤ A from hA) (m := m) (φ := mkPsi) hmb
    mkPsi_integrable (fun ξ hξ => (mkPsi_supp ξ hξ).2) j z
  have h2π : ‖(-2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [show (-2 * (Real.pi:ℂ) * Complex.I) = ((-(2*Real.pi) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)]
  rw [h2π]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Decay bound for the derivative of a dyadic piece's kernel. -/
lemma mkPiece_deriv_decay {m : ℝ → ℂ} {A CΨ : ℝ} (hm : ContDiff ℝ 2 m) (hA : 0 ≤ A) (hCΨ : 0 ≤ CΨ)
    (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hΨb : ∀ ξ, ‖mkPsi ξ‖ ≤ CΨ) (hΨ1 : ∀ ξ, ‖deriv mkPsi ξ‖ ≤ CΨ)
    (hΨ2 : ∀ ξ, ‖iteratedDeriv 2 mkPsi ξ‖ ≤ CΨ)
    (j : ℤ) (z : ℝ) (hz : z ≠ 0) :
    ‖deriv (FourierTransform.fourier (mkPiece m j)) z‖ ≤ 2 * Real.pi * ((2 * Real.pi * |z|) ^ (-2 : ℤ) * (378 * A * CΨ)) := by
  rw [mkPiece_deriv hm hmb j]
  simp only
  rw [norm_mul]
  have h := march_piece_grad_decay hm mkPsi_contDiff hA hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2
    (fun ξ hξ => mkPsi_van ξ hξ) (fun ξ hξ => mkPsi_supp ξ hξ) j z hz
  have h2π : ‖(-2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [show (-2 * (Real.pi:ℂ) * Complex.I) = ((-(2*Real.pi) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)]
  rw [h2π]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ## The Hörmander estimate for the dyadic pieces -/

/-- The kernel of the `j`-th piece. -/
def mkKJ (m : ℝ → ℂ) (j : ℤ) : ℝ → ℂ := FourierTransform.fourier (mkPiece m j)

/-- `∫⁻_{|z| ≥ a} ofReal (min c1 (c2 (z^2)^{-1})) ≤ ofReal (4 √(c1 c2))`. -/
lemma lintegral_min_inv_sq_le {a c1 c2 : ℝ} (ha : 0 < a) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    ∫⁻ z in {z : ℝ | a ≤ |z|}, ENNReal.ofReal (min c1 (c2 * (z^2)⁻¹))
      ≤ ENNReal.ofReal (4 * Real.sqrt (c1 * c2)) := by
  have hrpos : 0 < Real.sqrt (c1 / c2) := Real.sqrt_pos.mpr (div_pos hc1 hc2)
  have hr2 : Real.sqrt (c1 / c2) ^ 2 = c1 / c2 := Real.sq_sqrt (le_of_lt (div_pos hc1 hc2))
  have hA : c1 / Real.sqrt (c1 / c2) = Real.sqrt (c1 * c2) := by
    rw [div_eq_iff (ne_of_gt hrpos), mul_comm,
      ← Real.sqrt_mul (le_of_lt (div_pos hc1 hc2))]
    rw [show c1 / c2 * (c1 * c2) = c1 ^ 2 by field_simp, Real.sqrt_sq hc1.le]
  have hB : c2 * Real.sqrt (c1 / c2) = Real.sqrt (c1 * c2) := by
    nth_rewrite 1 [show c2 = Real.sqrt (c2^2) from (Real.sqrt_sq hc2.le).symm]
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ c2^2)]
    rw [show c2^2 * (c1/c2) = c1*c2 by field_simp]
  have hSU : {z : ℝ | a ≤ |z|}
      = {z : ℝ | a ≤ |z| ∧ |z| ≤ 1/Real.sqrt (c1/c2)}
        ∪ {z : ℝ | a ≤ |z| ∧ 1/Real.sqrt (c1/c2) < |z|} := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hz : |z| ≤ 1/Real.sqrt (c1/c2)
      · exact Or.inl ⟨h, hz⟩
      · exact Or.inr ⟨h, not_le.mp hz⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hmeas1 : MeasurableSet {z : ℝ | a ≤ |z| ∧ |z| ≤ 1/Real.sqrt (c1/c2)} :=
    (measurableSet_le measurable_const continuous_id.abs.measurable).inter
      (measurableSet_le continuous_id.abs.measurable measurable_const)
  have hmeas2 : MeasurableSet {z : ℝ | a ≤ |z| ∧ 1/Real.sqrt (c1/c2) < |z|} :=
    (measurableSet_le measurable_const continuous_id.abs.measurable).inter
      (measurableSet_lt measurable_const continuous_id.abs.measurable)
  have hdisj : Disjoint {z : ℝ | a ≤ |z| ∧ |z| ≤ 1/Real.sqrt (c1/c2)}
      {z : ℝ | a ≤ |z| ∧ 1/Real.sqrt (c1/c2) < |z|} := by
    rw [Set.disjoint_left]
    intro z h1 h2
    exact absurd h2.2 (not_lt.mpr h1.2)
  rw [hSU, lintegral_union hmeas2 hdisj]
  have h1 : ∫⁻ z in {z : ℝ | a ≤ |z| ∧ |z| ≤ 1/Real.sqrt (c1/c2)},
        ENNReal.ofReal (min c1 (c2 * (z^2)⁻¹))
      ≤ ENNReal.ofReal c1 * ENNReal.ofReal (2/Real.sqrt (c1/c2)) := by
    calc ∫⁻ z in {z : ℝ | a ≤ |z| ∧ |z| ≤ 1/Real.sqrt (c1/c2)},
          ENNReal.ofReal (min c1 (c2 * (z^2)⁻¹))
        ≤ ∫⁻ z in {z : ℝ | a ≤ |z| ∧ |z| ≤ 1/Real.sqrt (c1/c2)}, ENNReal.ofReal c1 :=
          lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      _ = ENNReal.ofReal c1 * (MeasureTheory.volume {z : ℝ | a ≤ |z| ∧ |z| ≤ 1/Real.sqrt (c1/c2)}) :=
          MeasureTheory.setLIntegral_const _ _
      _ ≤ ENNReal.ofReal c1 * MeasureTheory.volume {z : ℝ | |z| ≤ 1/Real.sqrt (c1/c2)} := by
          refine mul_le_mul_of_nonneg_left (MeasureTheory.measure_mono ?_) (by positivity)
          intro z hz; exact hz.2
      _ = ENNReal.ofReal c1 * ENNReal.ofReal (2/Real.sqrt (c1/c2)) := by
          rw [dl3_volume_abs_le, show (2:ℝ)*(1/Real.sqrt (c1/c2)) = 2/Real.sqrt (c1/c2) by ring]
  have h2 : ∫⁻ z in {z : ℝ | a ≤ |z| ∧ 1/Real.sqrt (c1/c2) < |z|},
        ENNReal.ofReal (min c1 (c2 * (z^2)⁻¹))
      ≤ ENNReal.ofReal c2 * ENNReal.ofReal (2*Real.sqrt (c1/c2)) := by
    calc ∫⁻ z in {z : ℝ | a ≤ |z| ∧ 1/Real.sqrt (c1/c2) < |z|},
          ENNReal.ofReal (min c1 (c2 * (z^2)⁻¹))
        ≤ ∫⁻ z in {z : ℝ | a ≤ |z| ∧ 1/Real.sqrt (c1/c2) < |z|},
            ENNReal.ofReal (c2 * (z^2)⁻¹) :=
          lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ = ∫⁻ z in {z : ℝ | a ≤ |z| ∧ 1/Real.sqrt (c1/c2) < |z|},
            ENNReal.ofReal c2 * ENNReal.ofReal ((z^2)⁻¹) := by
          apply lintegral_congr; intro z; rw [ENNReal.ofReal_mul hc2.le]
      _ = ENNReal.ofReal c2 * ∫⁻ z in {z : ℝ | a ≤ |z| ∧ 1/Real.sqrt (c1/c2) < |z|},
            ENNReal.ofReal ((z^2)⁻¹) := by
          rw [MeasureTheory.lintegral_const_mul]
          measurability
      _ ≤ ENNReal.ofReal c2 * ∫⁻ z in {z : ℝ | 1/Real.sqrt (c1/c2) < |z|},
            ENNReal.ofReal ((z^2)⁻¹) := by
          refine mul_le_mul_of_nonneg_left (lintegral_mono_set ?_) (by positivity)
          intro z hz; exact hz.2
      _ = ENNReal.ofReal c2 * ENNReal.ofReal (2*Real.sqrt (c1/c2)) := by
          rw [dl3_lintegral_abs_tail_inv_sq _ (by positivity),
            show 2/(1/Real.sqrt (c1/c2)) = 2*Real.sqrt (c1/c2) by field_simp]
  refine (add_le_add h1 h2).trans ?_
  have e1 : ENNReal.ofReal c1 * ENNReal.ofReal (2/Real.sqrt (c1/c2))
      = ENNReal.ofReal (2 * (c1/Real.sqrt (c1/c2))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have e2 : ENNReal.ofReal c2 * ENNReal.ofReal (2*Real.sqrt (c1/c2))
      = ENNReal.ofReal (2 * (c2*Real.sqrt (c1/c2))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  rw [e1, e2, ← ENNReal.ofReal_add (by positivity) (by positivity), hA, hB]
  apply ENNReal.ofReal_le_ofReal; linarith

/-- Pointwise bound for the kernel difference of a dyadic piece (value regime). -/
lemma mkPiece_fine_diff {m : ℝ → ℂ} {A CΨ : ℝ} (hm : ContDiff ℝ 2 m) (hA : 0 ≤ A)
    (hCΨ : 0 ≤ CΨ) (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hΨb : ∀ ξ, ‖mkPsi ξ‖ ≤ CΨ) (hΨ1 : ∀ ξ, ‖deriv mkPsi ξ‖ ≤ CΨ)
    (hΨ2 : ∀ ξ, ‖iteratedDeriv 2 mkPsi ξ‖ ≤ CΨ)
    (j : ℤ) (L : ℝ) (hL : 0 < L) (w : ℝ) (hw : |w| ≤ L/2) (z : ℝ) (hz : 50*L ≤ |z|) :
    ‖mkKJ m j (z - w) - mkKJ m j z‖
      ≤ 5 * (2 * Real.pi * |z|) ^ (-2 : ℤ) * (63 * A * CΨ * (2:ℝ)^(-j)) := by
  have hzpos : 0 < |z| := by linarith [hL, hz]
  have hzw : |z|/2 ≤ |z - w| := by
    have h1 : |z| ≤ |w| + |z - w| := by
      calc |z| = |w + (z - w)| := by ring_nf
        _ ≤ |w| + |z - w| := abs_add_le _ _
    have h2 : |w| ≤ |z|/2 := by nlinarith [hz, hw, hL, abs_nonneg z, abs_nonneg w]
    linarith
  have hzwpos : 0 < |z - w| := by linarith [hzpos, hzw]
  have h1 := mkPiece_decay hm hA hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2 j (z - w) (abs_pos.mp hzwpos)
  have h2 := mkPiece_decay hm hA hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2 j z (abs_pos.mp hzpos)
  have h4 : (2 * Real.pi * |z - w|) ^ (-2 : ℤ) ≤ 4 * (2 * Real.pi * |z|) ^ (-2 : ℤ) := by
    have hmain : (2 * Real.pi * |z - w|) ^ (-2 : ℤ) ≤ (2 * Real.pi * (|z|/2)) ^ (-2 : ℤ) := by
      have hle : 2 * Real.pi * (|z|/2) ≤ 2 * Real.pi * |z - w| := by nlinarith [hzw, Real.pi_pos]
      have h2 : 0 < (2 * Real.pi * (|z|/2))^2 := by positivity
      have h3 : (2 * Real.pi * (|z|/2))^2 ≤ (2 * Real.pi * |z - w|)^2 :=
        pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * Real.pi * (|z|/2)) hle 2
      calc (2 * Real.pi * |z - w|) ^ (-2 : ℤ) = ((2 * Real.pi * |z - w|)^2)⁻¹ := by
            rw [zpow_neg, zpow_ofNat]
        _ ≤ ((2 * Real.pi * (|z|/2))^2)⁻¹ := inv_anti₀ h2 h3
        _ = (2 * Real.pi * (|z|/2)) ^ (-2 : ℤ) := by rw [zpow_neg, zpow_ofNat]
    have hs : (2 * Real.pi * (|z|/2)) ^ (-2 : ℤ) = 4 * (2 * Real.pi * |z|) ^ (-2 : ℤ) := by
      rw [show 2 * Real.pi * (|z|/2) = (2 * Real.pi * |z|) * (1/2) by ring, mul_zpow]
      have hh : ((1:ℝ)/2) ^ (-2 : ℤ) = 4 := by rw [zpow_neg, zpow_ofNat]; norm_num
      rw [hh]; ring
    linarith [hmain, le_of_eq hs]
  calc ‖mkKJ m j (z - w) - mkKJ m j z‖ ≤ ‖mkKJ m j (z - w)‖ + ‖mkKJ m j z‖ := norm_sub_le _ _
    _ ≤ 4 * (2 * Real.pi * |z|) ^ (-2 : ℤ) * (63 * A * CΨ * (2:ℝ)^(-j))
        + (2 * Real.pi * |z|) ^ (-2 : ℤ) * (63 * A * CΨ * (2:ℝ)^(-j)) := by
        refine add_le_add ?_ h2
        exact h1.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
    _ = 5 * (2 * Real.pi * |z|) ^ (-2 : ℤ) * (63 * A * CΨ * (2:ℝ)^(-j)) := by ring

/-- Integral bound for the kernel difference of a dyadic piece (value regime). -/
lemma mkPiece_fine_integral {m : ℝ → ℂ} {A CΨ : ℝ} (hm : ContDiff ℝ 2 m) (hA : 0 ≤ A)
    (hCΨ : 0 ≤ CΨ) (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hΨb : ∀ ξ, ‖mkPsi ξ‖ ≤ CΨ) (hΨ1 : ∀ ξ, ‖deriv mkPsi ξ‖ ≤ CΨ)
    (hΨ2 : ∀ ξ, ‖iteratedDeriv 2 mkPsi ξ‖ ≤ CΨ)
    (j : ℤ) (L : ℝ) (hL : 0 < L) (w : ℝ) (hw : |w| ≤ L/2) :
    ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
      ≤ ENNReal.ofReal (A * CΨ * (2:ℝ)^(-j) / L) := by
  have hpt : ∀ z ∈ {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
      ≤ ENNReal.ofReal (5 * (2 * Real.pi * |z|) ^ (-2 : ℤ) * (63 * A * CΨ * (2:ℝ)^(-j))) := by
    intro z hz
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (mkPiece_fine_diff hm hA hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2 j L hL w hw z hz)
  have hfun : (fun z : ℝ => ENNReal.ofReal (5 * (2 * Real.pi * |z|) ^ (-2 : ℤ) * (63 * A * CΨ * (2:ℝ)^(-j))))
      = fun z : ℝ => ENNReal.ofReal (5 * 63 * A * CΨ * (2:ℝ)^(-j) / (2 * Real.pi)^2) * ENNReal.ofReal ((z^2)⁻¹) := by
    funext z
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (2 * Real.pi * |z|) ^ (-2 : ℤ) = ((2 * Real.pi)^2)⁻¹ * (z^2)⁻¹ by
      rw [zpow_neg, zpow_ofNat, mul_pow, sq_abs, mul_inv]]
    ring
  calc ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
      ≤ ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
          ENNReal.ofReal (5 * (2 * Real.pi * |z|) ^ (-2 : ℤ) * (63 * A * CΨ * (2:ℝ)^(-j))) :=
        MeasureTheory.setLIntegral_mono (by measurability) hpt
    _ = ENNReal.ofReal (5 * 63 * A * CΨ * (2:ℝ)^(-j) / (2 * Real.pi)^2)
          * ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ENNReal.ofReal ((z^2)⁻¹) := by
        rw [hfun, MeasureTheory.lintegral_const_mul]; measurability
    _ ≤ ENNReal.ofReal (5 * 63 * A * CΨ * (2:ℝ)^(-j) / (2 * Real.pi)^2)
          * ENNReal.ofReal (4/(50*L)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ENNReal.ofReal ((z^2)⁻¹)
            ≤ ∫⁻ z in {z : ℝ | 25*L < |z|}, ENNReal.ofReal ((z^2)⁻¹) := by
              refine lintegral_mono_set ?_
              intro z hz
              simp only [Set.mem_setOf_eq] at hz ⊢
              linarith [hz, hL]
          _ = ENNReal.ofReal (2/(25*L)) := dl3_lintegral_abs_tail_inv_sq _ (by positivity)
          _ ≤ ENNReal.ofReal (4/(50*L)) := by
              apply ENNReal.ofReal_le_ofReal
              rw [show (2:ℝ)/(25*L) = 4/(50*L) by field_simp; ring]
    _ = ENNReal.ofReal (5 * 63 * A * CΨ * (2:ℝ)^(-j) / (2 * Real.pi)^2 * (4/(50*L))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (A * CΨ * (2:ℝ)^(-j) / L) := by
        apply ENNReal.ofReal_le_ofReal
        have hkey : 5 * 63 * A * CΨ * (2:ℝ)^(-j) / (2 * Real.pi)^2 * (4/(50*L))
            = (5*63*4/((2*Real.pi)^2 * 50)) * (A * CΨ * (2:ℝ)^(-j) / L) := by ring
        rw [hkey]
        have hle1 : 5*63*4/((2*Real.pi)^2 * 50) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [Real.pi_gt_three]
        calc (5*63*4/((2*Real.pi)^2 * 50)) * (A * CΨ * (2:ℝ)^(-j) / L)
            ≤ 1 * (A * CΨ * (2:ℝ)^(-j) / L) :=
              mul_le_mul_of_nonneg_right hle1 (by positivity)
          _ = A * CΨ * (2:ℝ)^(-j) / L := one_mul _

/-- Sum of a geometric series over the integers at most `j₀`. -/
lemma sum_zpow_two_le {s : Finset ℤ} {j₀ : ℤ} (h : ∀ j ∈ s, j ≤ j₀) :
    ∑ j ∈ s, (2:ℝ)^j ≤ (2:ℝ)^(j₀+1) := by
  have h2N : (0:ℝ) < 2 := by norm_num
  have hcast : ∀ j ∈ s, (2:ℝ)^j = (2:ℝ)^(j₀) * ((1:ℝ)/2)^((j₀ - j).toNat) := by
    intro j hj
    have hj' : j ≤ j₀ := h j hj
    have hjn : (0:ℤ) ≤ j₀ - j := by omega
    have hnat : ((j₀ - j).toNat : ℤ) = j₀ - j := Int.toNat_of_nonneg hjn
    have hsplit : (j₀ : ℤ) = j + ((j₀ - j).toNat : ℤ) := by rw [hnat]; ring
    have h2j0 : (2:ℝ)^(j₀) = (2:ℝ)^j * (2:ℝ)^((j₀ - j).toNat) := by
      nth_rewrite 1 [hsplit]
      rw [zpow_add₀ (ne_of_gt h2N), zpow_natCast]
    rw [h2j0, mul_assoc, ← mul_pow, show (2:ℝ)*(1/2) = 1 by norm_num, one_pow, mul_one]
  have hinj : ∀ j ∈ s, ∀ k ∈ s, (j₀ - j).toNat = (j₀ - k).toNat → j = k := by
    intro j hj k hk hjk
    have h1 : (0:ℤ) ≤ j₀ - j := by have := h j hj; omega
    have h2 : (0:ℤ) ≤ j₀ - k := by have := h k hk; omega
    have : (j₀ - j : ℤ) = (j₀ - k : ℤ) := by
      rw [← Int.toNat_of_nonneg h1, ← Int.toNat_of_nonneg h2, hjk]
    omega
  have hsum1 : ∑ j ∈ s, ((1:ℝ)/2)^((j₀ - j).toNat)
      = ∑ n ∈ s.image (fun j : ℤ => (j₀ - j).toNat), ((1:ℝ)/2)^n := by
    rw [Finset.sum_image]; intro x hx y hy hxy; exact hinj x hx y hy hxy
  have hsum2 : ∑ n ∈ s.image (fun j : ℤ => (j₀ - j).toNat), ((1:ℝ)/2)^n ≤ 2 := by
    refine ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum _
      (fun n _ => by positivity)).trans ?_
    have hg : (∑' n : ℕ, ((1:ℝ)/2)^n) = 2 := by
      rw [tsum_geometric_of_lt_one (r := (1:ℝ)/2) (by norm_num) (by norm_num)]
      norm_num
    exact le_of_eq hg
  rw [Finset.sum_congr rfl hcast, ← Finset.mul_sum, hsum1]
  calc (2:ℝ)^(j₀) * ∑ n ∈ s.image (fun j : ℤ => (j₀ - j).toNat), ((1:ℝ)/2)^n
      ≤ (2:ℝ)^(j₀) * 2 := mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (2:ℝ)^(j₀+1) := by rw [zpow_add_one₀ (ne_of_gt h2N)]

/-- Pointwise bound for the kernel difference of a dyadic piece (gradient regime). -/
lemma mkPiece_coarse_diff {m : ℝ → ℂ} {A CΨ : ℝ} (hm : ContDiff ℝ 2 m) (hA : 0 ≤ A)
    (hCΨ : 0 ≤ CΨ) (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hΨb : ∀ ξ, ‖mkPsi ξ‖ ≤ CΨ) (hΨ1 : ∀ ξ, ‖deriv mkPsi ξ‖ ≤ CΨ)
    (hΨ2 : ∀ ξ, ‖iteratedDeriv 2 mkPsi ξ‖ ≤ CΨ)
    (j : ℤ) (L : ℝ) (hL : 0 < L) (w : ℝ) (hw : |w| ≤ L/2) (z : ℝ) (hz : 50*L ≤ |z|) :
    ‖mkKJ m j (z - w) - mkKJ m j z‖
      ≤ |w| * min (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1))
                (1000 * A * CΨ * (z^2)⁻¹) := by
  have hMnn : (0:ℝ) ≤ ∫ y : ℝ, ‖mkPsi y‖ := integral_nonneg (fun y => norm_nonneg _)
  have hseg : ∀ u ∈ Set.uIcc (z - w) z, |z|/2 ≤ |u| := by
    intro u hu
    have huz : |u - z| ≤ |w| := by
      rw [Set.mem_uIcc] at hu
      rw [abs_le]
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [h1, le_abs_self w], by linarith [h2, abs_nonneg w]⟩
      · exact ⟨by linarith [h1, abs_nonneg w], by linarith [h2, neg_le_abs w]⟩
    have h2 : |w| ≤ |z|/2 := by
      have : L ≤ |z|/50 := by linarith [hz]
      linarith [hw, this, abs_nonneg z, hL]
    have h3 : |z| ≤ |u| + |u - z| := by
      calc |z| = |(z - u) + u| := by ring_nf
        _ ≤ |z - u| + |u| := abs_add_le _ _
        _ = |u| + |u - z| := by rw [abs_sub_comm]; ring
    linarith
  have hdiff : ∀ u ∈ Set.uIcc (z - w) z, DifferentiableAt ℝ (mkKJ m j) u := fun u _ =>
    (Real.hasDerivAt_fourier (mkPiece_integrable hm hmb j) (mkPiece_x_integrable hm hmb j) u).differentiableAt
  have hbound : ∀ u ∈ Set.uIcc (z - w) z,
      ‖deriv (mkKJ m j) u‖ ≤ min (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1))
        (1000 * A * CΨ * (z^2)⁻¹) := by
    intro u hu
    have hu2 : |z|/2 ≤ |u| := hseg u hu
    have hupos : 0 < |u| := by linarith [hu2, hL, hz]
    have h1 := mkPiece_deriv_sup hm hA hmb j u
    have h2 := mkPiece_deriv_decay hm hA hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2 j u (abs_pos.mp hupos)
    refine le_min ?_ ?_
    · have h4j : (4:ℝ)^j = (2:ℝ)^j * (2:ℝ)^j := by
        have hh : (4:ℝ) = (2:ℝ)^(2:ℤ) := by norm_num
        rw [hh, ← zpow_mul]
        rw [show (2:ℤ) * j = j + j by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      rw [h4j]
      refine h1.trans ?_
      have hx : (0:ℝ) ≤ (2:ℝ)^j := zpow_nonneg (by norm_num) j
      have hpi8 : 2*Real.pi*4 ≤ 1000 := by nlinarith [Real.pi_lt_four]
      have hb : A * ((2:ℝ)^j * ((2:ℝ)^j * (∫ y : ℝ, ‖mkPsi y‖)))
          ≤ A * ((2:ℝ)^j * ((2:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖)+1))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hx) hx) hA
        linarith [hMnn]
      have heq : 2 * Real.pi * (4 * A * (2:ℝ)^j * ((2:ℝ)^j * ∫ y : ℝ, ‖mkPsi y‖))
          = (2*Real.pi*4) * (A * ((2:ℝ)^j * ((2:ℝ)^j * (∫ y : ℝ, ‖mkPsi y‖)))) := by ring
      rw [heq]
      exact (mul_le_mul hpi8 hb (by positivity) (by norm_num)).trans_eq (by ring)
    · refine h2.trans ?_
      have hzp : (0:ℝ) < z^2 := by
        have : (0:ℝ) < |z| := by linarith [hL, hz]
        exact sq_pos_of_ne_zero (abs_pos.mp this)
      have huinv : (u^2)⁻¹ ≤ 4 * (z^2)⁻¹ := by
        have huz2 : z^2/4 ≤ u^2 := by
          have h : (|z|/2)^2 ≤ |u|^2 := by nlinarith [hu2, abs_nonneg u, abs_nonneg z]
          rw [div_pow, sq_abs, sq_abs] at h; linarith [h]
        have h4 : (0:ℝ) < z^2/4 := by positivity
        have h5 := inv_anti₀ h4 huz2
        rwa [show (z^2/4)⁻¹ = 4*(z^2)⁻¹ by rw [div_eq_mul_inv, mul_inv]; ring] at h5
      have hdec : (2*Real.pi*|u|)^(-2:ℤ) = ((2*Real.pi)^2)⁻¹ * (u^2)⁻¹ := by
        rw [zpow_neg, zpow_ofNat, mul_pow, sq_abs, mul_inv]
      rw [hdec]
      have hcoef : 2*Real.pi * ((2*Real.pi)^2)⁻¹ = (2*Real.pi)⁻¹ := by
        have hne : (2:ℝ)*Real.pi ≠ 0 := by positivity
        rw [show (2*Real.pi)^2 = (2*Real.pi)*(2*Real.pi) by ring, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ hne, one_mul]
      rw [show 2*Real.pi * (((2*Real.pi)^2)⁻¹ * (u^2)⁻¹ * (378*A*CΨ))
          = (2*Real.pi)⁻¹ * ((u^2)⁻¹ * (378*A*CΨ)) by rw [← hcoef]; ring]
      have hnum : (2*Real.pi)⁻¹ * (4:ℝ) * 378 ≤ 1000 := by
        rw [show (2*Real.pi)⁻¹*4*378 = 1512/(2*Real.pi) by rw [div_eq_mul_inv]; ring]
        rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
      have hnn : (0:ℝ) ≤ A*CΨ*(z^2)⁻¹ := by positivity
      calc (2*Real.pi)⁻¹ * ((u^2)⁻¹ * (378*A*CΨ))
          ≤ (2*Real.pi)⁻¹ * ((4 * (z^2)⁻¹) * (378*A*CΨ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right huinv (by positivity)) (by positivity)
        _ = ((2*Real.pi)⁻¹*4*378) * (A*CΨ*(z^2)⁻¹) := by ring
        _ ≤ 1000 * (A*CΨ*(z^2)⁻¹) := mul_le_mul_of_nonneg_right hnum hnn
        _ = 1000*A*CΨ*(z^2)⁻¹ := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := mkKJ m j) (s := Set.uIcc (z - w) z) (x := z) (y := z - w)
    hdiff hbound (convex_uIcc (z - w) z) Set.right_mem_uIcc Set.left_mem_uIcc
  rw [show ‖(z - w) - z‖ = |w| by rw [show (z-w) - z = -w by ring, norm_neg, Real.norm_eq_abs]] at hmvt
  exact hmvt.trans_eq (mul_comm _ _)

/-- Integral bound for the kernel difference of a dyadic piece (gradient regime). -/
lemma mkPiece_coarse_integral {m : ℝ → ℂ} {A CΨ : ℝ} (hm : ContDiff ℝ 2 m) (hA : 0 < A)
    (hCΨ : 0 < CΨ) (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hΨb : ∀ ξ, ‖mkPsi ξ‖ ≤ CΨ) (hΨ1 : ∀ ξ, ‖deriv mkPsi ξ‖ ≤ CΨ)
    (hΨ2 : ∀ ξ, ‖iteratedDeriv 2 mkPsi ξ‖ ≤ CΨ)
    (j : ℤ) (L : ℝ) (hL : 0 < L) (w : ℝ) (hw : |w| ≤ L/2) :
    ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
      ≤ ENNReal.ofReal (|w| * 4 * Real.sqrt (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1)
          * (1000 * A * CΨ))) := by
  have hMnn : (0:ℝ) ≤ ∫ y : ℝ, ‖mkPsi y‖ := integral_nonneg (fun y => norm_nonneg _)
  have hc1 : 0 < 1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1) := by positivity
  have hc2 : 0 < 1000 * A * CΨ := by positivity
  have hpt : ∀ z ∈ {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
      ≤ ENNReal.ofReal (|w| * min (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1))
          (1000 * A * CΨ * (z^2)⁻¹)) := by
    intro z hz
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (mkPiece_coarse_diff hm hA.le hCΨ.le hmb hm1 hm2 hΨb hΨ1 hΨ2 j L hL w hw z hz)
  have hfun : (fun z : ℝ => ENNReal.ofReal (|w| * min (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1))
          (1000 * A * CΨ * (z^2)⁻¹)))
      = fun z : ℝ => ENNReal.ofReal |w| * ENNReal.ofReal (min (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1))
          (1000 * A * CΨ * (z^2)⁻¹)) := by
    funext z; rw [ENNReal.ofReal_mul (abs_nonneg w)]
  calc ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
      ≤ ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ENNReal.ofReal (|w| * min (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1))
          (1000 * A * CΨ * (z^2)⁻¹)) := MeasureTheory.setLIntegral_mono (by measurability) hpt
    _ = ENNReal.ofReal |w| * ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ENNReal.ofReal (min (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1))
          (1000 * A * CΨ * (z^2)⁻¹)) := by
        rw [hfun, MeasureTheory.lintegral_const_mul]; measurability
    _ ≤ ENNReal.ofReal |w| * ENNReal.ofReal (4 * Real.sqrt ((1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1)) * (1000 * A * CΨ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact lintegral_min_inv_sq_le (by positivity : (0:ℝ) < 50*L) hc1 hc2
    _ = ENNReal.ofReal (|w| * 4 * Real.sqrt (1000 * A * (4:ℝ)^j * ((∫ y : ℝ, ‖mkPsi y‖) + 1)
          * (1000 * A * CΨ))) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg w)]; congr 1; ring

lemma mkKJ_continuous {m : ℝ → ℂ} {A : ℝ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ, ‖m ξ‖ ≤ A)
    (j : ℤ) : Continuous (mkKJ m j) :=
  Commons.Analysis.CalderonZygmund.continuous_fourier_of_integrable (mkPiece_integrable hm hmb j)

/-- Hörmander condition for a finite sum of dyadic pieces of a Mikhlin symbol. -/
theorem mk_hormander {m : ℝ → ℂ} {A CΨ : ℝ} (hm : ContDiff ℝ 2 m) (hA : 0 < A)
    (hCΨ : 0 < CΨ) (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (hm1 : ∀ ξ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (hm2 : ∀ ξ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A)
    (hΨb : ∀ ξ, ‖mkPsi ξ‖ ≤ CΨ) (hΨ1 : ∀ ξ, ‖deriv mkPsi ξ‖ ≤ CΨ)
    (hΨ2 : ∀ ξ, ‖iteratedDeriv 2 mkPsi ξ‖ ≤ CΨ)
    (D : Finset ℤ) (L : ℝ) (hL : 0 < L) (w : ℝ) (hw : |w| ≤ L/2) :
    ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
      ‖(∑ j ∈ D, mkKJ m j (z - w)) - (∑ j ∈ D, mkKJ m j z)‖ₑ
      ≤ ENNReal.ofReal (5000 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) := by
  obtain ⟨j₀, hj₀₁, hj₀₂⟩ := dlb_exists_zpow_bracket (by norm_num : (1:ℝ) < 2)
    (by positivity : (0:ℝ) < (1/L)^2)
  rw [Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1/L)] at hj₀₁ hj₀₂
  have hMnn : (0:ℝ) ≤ ∫ y : ℝ, ‖mkPsi y‖ := integral_nonneg (fun y => norm_nonneg _)
  have hXnn : (0:ℝ) ≤ (1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ) := by positivity
  have hsqrt : Real.sqrt (((∫ y : ℝ, ‖mkPsi y‖) + 1) * CΨ)
      ≤ (1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ) := by
    have h1 : Real.sqrt (((∫ y : ℝ, ‖mkPsi y‖) + 1) * CΨ)
        ≤ ((∫ y : ℝ, ‖mkPsi y‖) + 1) * CΨ + 1 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith [hMnn, hCΨ.le,
        mul_nonneg (show (0:ℝ) ≤ (∫ y : ℝ, ‖mkPsi y‖) + 1 by positivity) hCΨ.le]
    have h2 : ((∫ y : ℝ, ‖mkPsi y‖) + 1) * CΨ + 1 ≤ (1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ) := by
      rw [mul_add, mul_one, add_mul, one_mul, add_mul, one_mul]; linarith [hMnn]
    linarith [h1, h2]
  have hcont : ∀ j : ℤ, Continuous (fun z : ℝ => mkKJ m j (z - w) - mkKJ m j z) := fun j =>
    ((mkKJ_continuous hm hmb j).comp
        (continuous_id.sub (continuous_const : Continuous (fun _ : ℝ => w)))).sub
      (mkKJ_continuous hm hmb j)
  have hmeas : ∀ j : ℤ, Measurable (fun z : ℝ => ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ) :=
    fun j => (hcont j).enorm.measurable
  have hbase : ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
        ‖(∑ j ∈ D, mkKJ m j (z - w)) - (∑ j ∈ D, mkKJ m j z)‖ₑ
      ≤ ∑ j ∈ D, ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ := by
    calc ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
          ‖(∑ j ∈ D, mkKJ m j (z - w)) - (∑ j ∈ D, mkKJ m j z)‖ₑ
        ≤ ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
            ∑ j ∈ D, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ := by
          refine MeasureTheory.setLIntegral_mono
            (Finset.measurable_sum D (fun j _ => hmeas j)) (fun z _ => ?_)
          rw [← Finset.sum_sub_distrib]
          exact enorm_sum_le D (fun j => mkKJ m j (z - w) - mkKJ m j z)
      _ = ∑ j ∈ D, ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ :=
          MeasureTheory.lintegral_finsetSum D (fun j _ => hmeas j)
  have hDlo : ∑ j ∈ D.filter (fun j => j ≤ j₀), ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
        ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
      ≤ ENNReal.ofReal (4000 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) := by
    calc ∑ j ∈ D.filter (fun j => j ≤ j₀), ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
          ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
        ≤ ∑ j ∈ D.filter (fun j => j ≤ j₀),
            ENNReal.ofReal (|w| * 4 * Real.sqrt (1000*A*(4:ℝ)^j*((∫ y : ℝ, ‖mkPsi y‖)+1) * (1000*A*CΨ))) :=
          Finset.sum_le_sum (fun j _ => mkPiece_coarse_integral hm hA hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2 j L hL w hw)
      _ = ENNReal.ofReal (∑ j ∈ D.filter (fun j => j ≤ j₀),
            |w| * 4 * Real.sqrt (1000*A*(4:ℝ)^j*((∫ y : ℝ, ‖mkPsi y‖)+1) * (1000*A*CΨ))) :=
          (ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)).symm
      _ ≤ ENNReal.ofReal (4000 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) := by
          apply ENNReal.ofReal_le_ofReal
          have hstep : ∀ j ∈ D.filter (fun j => j ≤ j₀),
              |w| * 4 * Real.sqrt (1000*A*(4:ℝ)^j*((∫ y : ℝ, ‖mkPsi y‖)+1) * (1000*A*CΨ))
              ≤ (|w| * 4000 * A * ((1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ))) * (2:ℝ)^j := by
            intro j _
            have h4j : (4:ℝ)^j = (2:ℝ)^j * (2:ℝ)^j := by
              have hh : (4:ℝ) = (2:ℝ)^(2:ℤ) := by norm_num
              rw [hh, ← zpow_mul]
              rw [show (2:ℤ)*j = j + j by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
            have hX : 1000*A*(4:ℝ)^j*((∫ y : ℝ, ‖mkPsi y‖)+1) * (1000*A*CΨ)
                = (1000*A*(2:ℝ)^j)^2 * (((∫ y : ℝ, ‖mkPsi y‖)+1)*CΨ) := by
              rw [h4j]; ring
            have hs : Real.sqrt (1000*A*(4:ℝ)^j*((∫ y : ℝ, ‖mkPsi y‖)+1) * (1000*A*CΨ))
                = 1000*A*(2:ℝ)^j * Real.sqrt (((∫ y : ℝ, ‖mkPsi y‖) + 1) * CΨ) := by
              have hpos : (0:ℝ) ≤ 1000*A*(2:ℝ)^j := by
                have h2j : (0:ℝ) < (2:ℝ)^j := zpow_pos (by norm_num) j
                positivity
              rw [hX, Real.sqrt_mul (sq_nonneg (1000*A*(2:ℝ)^j)), Real.sqrt_sq hpos]
            rw [hs]
            nlinarith [hsqrt, hXnn, abs_nonneg w, hA,
              mul_nonneg (abs_nonneg w) (mul_nonneg hA.le (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) j)),
              zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) j]
          calc ∑ j ∈ D.filter (fun j => j ≤ j₀),
                |w| * 4 * Real.sqrt (1000*A*(4:ℝ)^j*((∫ y : ℝ, ‖mkPsi y‖)+1) * (1000*A*CΨ))
              ≤ ∑ j ∈ D.filter (fun j => j ≤ j₀),
                  (|w| * 4000 * A * ((1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ))) * (2:ℝ)^j :=
                Finset.sum_le_sum hstep
            _ = (|w| * 4000 * A * ((1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ)))
                  * ∑ j ∈ D.filter (fun j => j ≤ j₀), (2:ℝ)^j := by
                rw [Finset.mul_sum]
            _ ≤ (|w| * 4000 * A * ((1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ))) * (2:ℝ)^(j₀+1) := by
                refine mul_le_mul_of_nonneg_left
                  (sum_zpow_two_le (fun j hj => (Finset.mem_filter.mp hj).2)) (by positivity)
            _ ≤ ((L/2) * 4000 * A * ((1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ))) * (2/L) := by
                refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
                · nlinarith [hw, show (0:ℝ) ≤ 4000*A*((1 + ∫ y : ℝ, ‖mkPsi y‖) * (1 + CΨ)) by positivity]
                · rw [zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]
                  calc (2:ℝ)^j₀ * 2 ≤ (1/L) * 2 := mul_le_mul_of_nonneg_right hj₀₁ (by norm_num)
                    _ = 2/L := by ring
            _ = 4000 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖) := by
                field_simp
  have hDhi : ∑ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
        ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
      ≤ ENNReal.ofReal (2 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) := by
    calc ∑ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
          ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ
        ≤ ∑ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), ENNReal.ofReal (A*CΨ*(2:ℝ)^(-j)/L) :=
          Finset.sum_le_sum (fun j _ => mkPiece_fine_integral hm hA.le hCΨ.le hmb hm1 hm2 hΨb hΨ1 hΨ2 j L hL w hw)
      _ = ENNReal.ofReal (∑ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), A*CΨ*(2:ℝ)^(-j)/L) :=
          (ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)).symm
      _ ≤ ENNReal.ofReal (2 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) := by
          apply ENNReal.ofReal_le_ofReal
          have hstep : ∀ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), A*CΨ*(2:ℝ)^(-j)/L
              ≤ (A*CΨ/L) * (2:ℝ)^(-j) := fun j _ =>
                le_of_eq (by rw [div_eq_mul_inv, div_eq_mul_inv]; ring)
          calc ∑ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), A*CΨ*(2:ℝ)^(-j)/L
              ≤ ∑ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), (A*CΨ/L) * (2:ℝ)^(-j) := Finset.sum_le_sum hstep
            _ = (A*CΨ/L) * ∑ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), (2:ℝ)^(-j) := by rw [Finset.mul_sum]
            _ ≤ (A*CΨ/L) * (2:ℝ)^(-j₀) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                simpa using dl3_lacunary_high_sum (1:ℝ) (by norm_num) j₀
                  (D.filter (fun j => ¬ (j ≤ j₀))) (fun j hj => not_le.mp (Finset.mem_filter.mp hj).2)
            _ ≤ (A*CΨ/L) * (2*L) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                rw [zpow_neg, inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < (2:ℝ)^j₀)]
                have h := (div_le_iff₀ hL).mp hj₀₂
                rw [zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)] at h
                linarith [h]
            _ = 2 * A * CΨ := by field_simp
            _ ≤ 2 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖) := by
                nlinarith [hMnn, hCΨ.le, hA.le, mul_nonneg hA.le hCΨ.le, mul_nonneg hA.le hMnn]
  calc ∫⁻ z in {z : ℝ | 50*L ≤ |z|},
        ‖(∑ j ∈ D, mkKJ m j (z - w)) - (∑ j ∈ D, mkKJ m j z)‖ₑ
      ≤ ∑ j ∈ D, ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ := hbase
    _ = (∑ j ∈ D.filter (fun j => j ≤ j₀), ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ)
        + (∑ j ∈ D.filter (fun j => ¬ (j ≤ j₀)), ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ) :=
        (Finset.sum_filter_add_sum_filter_not D (fun j => j ≤ j₀)
          (fun j => ∫⁻ z in {z : ℝ | 50*L ≤ |z|}, ‖mkKJ m j (z - w) - mkKJ m j z‖ₑ)).symm
    _ ≤ ENNReal.ofReal (4000 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖))
        + ENNReal.ofReal (2 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) :=
        add_le_add hDlo hDhi
    _ = ENNReal.ofReal (4000 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)
        + 2 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (5000 * A * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [hMnn, hCΨ.le, hA.le]

/-! ## The truncation and its dyadic decomposition -/

/-- The finite dyadic partition of unity used to truncate the symbol. -/
def mkTrunc (N : ℕ) : ℝ → ℂ :=
  fun ξ => ∑ i ∈ Finset.range (2*N), mkPsi ((2:ℝ)^(-(-(N:ℤ) + (i:ℤ))) * ξ)

lemma mkTrunc_tel (N : ℕ) (ξ : ℝ) :
    mkTrunc N ξ
      = (((mkRhoB ((2:ℝ)^(-(N:ℤ)) * ξ) - mkRhoB ((2:ℝ)^(N:ℤ) * ξ) : ℝ)) : ℂ) := by
  have hterm : ∀ i ∈ Finset.range (2*N),
      mkPsi ((2:ℝ)^(-(-(N:ℤ) + (i:ℤ))) * ξ)
        = (((mkRhoB ((2:ℝ)^(-(-(N:ℤ) + ((i:ℤ)+1))) * ξ)
            - mkRhoB ((2:ℝ)^(-(-(N:ℤ) + (i:ℤ))) * ξ) : ℝ)) : ℂ) := by
    intro i _
    have h1 : (2:ℝ)^(-(-(N:ℤ) + (i:ℤ))) * ξ / 2
        = (2:ℝ)^(-(-(N:ℤ) + ((i:ℤ)+1))) * ξ := by
      rw [show -(-(N:ℤ) + ((i:ℤ)+1)) = -(-(N:ℤ) + (i:ℤ)) - 1 by ring,
        zpow_sub_one₀ (by norm_num : (2:ℝ) ≠ 0)]
      ring
    rw [mkPsi, h1]
  rw [mkTrunc, Finset.sum_congr rfl hterm, ← Complex.ofReal_sum]
  congr 1
  have hsum2 : (∑ i ∈ Finset.range (2*N),
        (mkRhoB ((2:ℝ)^(-(-(N:ℤ) + ((i:ℤ)+1))) * ξ)
          - mkRhoB ((2:ℝ)^(-(-(N:ℤ) + (i:ℤ))) * ξ)))
      = ∑ i ∈ Finset.range (2*N),
        ((fun j : ℕ => mkRhoB ((2:ℝ)^(-(-(N:ℤ) + (j:ℤ))) * ξ)) (i+1)
          - (fun j : ℕ => mkRhoB ((2:ℝ)^(-(-(N:ℤ) + (j:ℤ))) * ξ)) i) := by
    apply Finset.sum_congr rfl; intro i _
    have hcast : ((i:ℤ)+1) = ((i+1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast]
  rw [hsum2]
  simp only []
  rw [Finset.sum_range_sub (f := fun j : ℕ => mkRhoB ((2:ℝ)^(-(-(N:ℤ) + (j:ℤ))) * ξ))]
  congr 1
  · rw [show -(-(N:ℤ) + ((2*N : ℕ) : ℤ)) = -(N:ℤ) by push_cast; ring]
  · rw [show -(-(N:ℤ) + ((0:ℕ) : ℤ)) = (N:ℤ) by push_cast; ring]

lemma mkTrunc_contDiff (N : ℕ) : ContDiff ℝ 2 (mkTrunc N) := by
  have hfun : mkTrunc N
      = fun ξ : ℝ => (((mkRhoB ((2:ℝ)^(-(N:ℤ)) * ξ) - mkRhoB ((2:ℝ)^(N:ℤ) * ξ) : ℝ)) : ℂ) := by
    funext ξ; exact mkTrunc_tel N ξ
  rw [hfun]
  have h1 : ContDiff ℝ 2 (fun ξ : ℝ => (2:ℝ)^(-(N:ℤ)) * ξ) := contDiff_const.mul contDiff_id
  have h2 : ContDiff ℝ 2 (fun ξ : ℝ => (2:ℝ)^(N:ℤ) * ξ) := contDiff_const.mul contDiff_id
  exact Complex.ofRealCLM.contDiff.comp
    (((mkRhoB.contDiff (n := 2)).comp h1).sub ((mkRhoB.contDiff (n := 2)).comp h2))

lemma mkTrunc_norm_le (N : ℕ) (ξ : ℝ) : ‖mkTrunc N ξ‖ ≤ 1 := by
  rw [mkTrunc_tel, Complex.norm_real, Real.norm_eq_abs, abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · linarith [mkRhoB.le_one (x := (2:ℝ)^(-(N:ℤ)) * ξ), mkRhoB.nonneg (x := (2:ℝ)^(N:ℤ) * ξ)]
  · linarith [mkRhoB.le_one (x := (2:ℝ)^(N:ℤ) * ξ), mkRhoB.nonneg (x := (2:ℝ)^(-(N:ℤ)) * ξ)]

lemma mkTrunc_eventually_zero (N : ℕ) : ∀ ξ : ℝ, (2:ℝ)^(N+1) < |ξ| → mkTrunc N ξ = 0 := by
  intro ξ h
  rw [mkTrunc_tel]
  have h2Nj : (0:ℝ) < (2:ℝ)^N := by positivity
  have hpow : (2:ℝ)^(N+1) = (2:ℝ)^N * 2 := pow_succ 2 N
  have hle : (2:ℝ) * (2:ℝ)^N ≤ |ξ| := by rw [mul_comm, ← hpow]; exact le_of_lt h
  have ha : mkRhoB ((2:ℝ)^(-(N:ℤ)) * ξ) = 0 := by
    apply mkRhoB_zero
    have hcast : (2:ℝ)^(-(N:ℤ)) = ((2:ℝ)^N)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2:ℝ)^(-(N:ℤ))), hcast, inv_mul_eq_div,
      le_div_iff₀ h2Nj]
    exact hle
  have hb : mkRhoB ((2:ℝ)^(N:ℤ) * ξ) = 0 := by
    apply mkRhoB_zero
    have hcast : (2:ℝ)^(N:ℤ) = (2:ℝ)^N := zpow_natCast 2 N
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) _), hcast]
    have h1 : (1:ℝ) ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    rw [hpow] at h
    nlinarith [h, h1, abs_nonneg ξ]
  rw [ha, hb, sub_self, Complex.ofReal_zero]

lemma mkTrunc_hasCompactSupport (N : ℕ) : HasCompactSupport (mkTrunc N) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-((2:ℝ)^(N+1))) ((2:ℝ)^(N+1))) isCompact_Icc (fun ξ hξ => ?_)
  rw [Set.mem_Icc]
  have hpos : (0:ℝ) < (2:ℝ)^(N+1) := by positivity
  constructor
  · by_contra h; rw [not_le] at h
    exact hξ (mkTrunc_eventually_zero N ξ (by rw [abs_of_neg (by linarith : ξ < 0)]; linarith))
  · by_contra h; rw [not_le] at h
    exact hξ (mkTrunc_eventually_zero N ξ (by rw [abs_of_pos (by linarith : (0:ℝ) < ξ)]; exact h))

lemma mkTrunc_integrable (N : ℕ) : Integrable (mkTrunc N) :=
  (mkTrunc_contDiff N).continuous.integrable_of_hasCompactSupport (mkTrunc_hasCompactSupport N)

/-! ## The `L^p` bound, `1 < p < 2` -/

/-- The truncated symbol `m · mkTrunc N`. -/
def mkSymb (m : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun ξ => m ξ * mkTrunc N ξ

lemma mkSymb_integrable {m : ℝ → ℂ} {A : ℝ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ, ‖m ξ‖ ≤ A)
    (N : ℕ) : Integrable (mkSymb m N) := by
  have hcont : Continuous (mkSymb m N) :=
    hm.continuous.mul (mkTrunc_contDiff N).continuous
  refine hcont.integrable_of_hasCompactSupport ?_
  refine (mkTrunc_hasCompactSupport N).mono ?_
  intro ξ hξ
  simp only [Function.mem_support, mkSymb, Pi.mul_apply] at hξ ⊢
  intro hc; exact hξ (by rw [hc, mul_zero])

lemma mkSymb_norm_le {m : ℝ → ℂ} {A : ℝ} (hmb : ∀ ξ, ‖m ξ‖ ≤ A) (N : ℕ) (ξ : ℝ) :
    ‖mkSymb m N ξ‖ ≤ A := by
  rw [mkSymb, norm_mul]
  calc ‖m ξ‖ * ‖mkTrunc N ξ‖ ≤ A * 1 :=
        mul_le_mul (hmb ξ) (mkTrunc_norm_le N ξ) (norm_nonneg _) (le_trans (norm_nonneg _) (hmb ξ))
    _ = A := mul_one A

lemma czKern_mkPiece (m : ℝ → ℂ) (j : ℤ) (z : ℝ) :
    czKern (mkPiece m j) z = mkKJ m j (-z) := by
  rw [czKern, mkKJ, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [smul_eq_mul, czE]
  rw [show (↑(-2 * Real.pi * ξ * (-z)) * Complex.I : ℂ)
      = 2 * Real.pi * Complex.I * (z * ξ) by push_cast; ring]
  ring

lemma mkSymb_eq_sum (m : ℝ → ℂ) (N : ℕ) :
    mkSymb m N = ∑ i ∈ Finset.range (2*N), mkPiece m (-(N:ℤ) + (i:ℤ)) := by
  funext ξ
  rw [mkSymb, mkTrunc, Finset.mul_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mkPiece]

lemma czKern_mkSymb (m : ℝ → ℂ) {A : ℝ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ, ‖m ξ‖ ≤ A)
    (N : ℕ) :
    czKern (mkSymb m N) = fun z => ∑ i ∈ Finset.range (2*N), mkKJ m (-(N:ℤ) + (i:ℤ)) (-z) := by
  funext z
  rw [czKern, mkSymb_eq_sum]
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro i _
    exact czKern_mkPiece m (-(N:ℤ) + (i:ℤ)) z
  · intro i _
    refine Integrable.mono' (mkPiece_integrable hm hmb (-(N:ℤ) + (i:ℤ))).norm ?_ ?_
    · exact ((hm.continuous.mul (mkPsi_contDiff.continuous.comp
          (continuous_const.mul continuous_id))).mul (continuous_czE z)).aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul, norm_czE, mul_one]

lemma mkTrunc_eventually_one (ξ : ℝ) (hξ : ξ ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop, mkTrunc N ξ = 1 := by
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  have htend : Filter.Tendsto (fun N : ℕ => ((2:ℝ)^N)) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [htend.eventually_ge_atTop (max |ξ| (2/|ξ|))] with N hN
  rw [mkTrunc_tel]
  have h1 : mkRhoB ((2:ℝ)^(-(N:ℤ)) * ξ) = 1 := by
    apply mkRhoB_one
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) _), zpow_neg, zpow_natCast,
      inv_mul_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^N)]
    simpa using le_trans (le_max_left _ _) hN
  have h2 : mkRhoB ((2:ℝ)^(N:ℤ) * ξ) = 0 := by
    apply mkRhoB_zero
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) _), zpow_natCast]
    have h2' : 2/|ξ| ≤ (2:ℝ)^N := le_trans (le_max_right _ _) hN
    have h3 : 2 ≤ (2:ℝ)^N * |ξ| := by
      have hmul := mul_le_mul_of_nonneg_right h2' hξpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hξpos)] at hmul
    linarith [h3]
  rw [h1, h2, sub_zero, Complex.ofReal_one]

lemma mkPiece_continuous (m : ℝ → ℂ) (hm : Continuous m) (j : ℤ) : Continuous (mkPiece m j) :=
  hm.mul (mkPsi_contDiff.continuous.comp (continuous_const.mul continuous_id))

lemma mkSymb_measurable {m : ℝ → ℂ} (hm : ContDiff ℝ 2 m) (N : ℕ) :
    Measurable (mkSymb m N) :=
  (hm.continuous.mul (mkTrunc_contDiff N).continuous).measurable

lemma czKern_eq_fourier_neg (g : ℝ → ℂ) :
    czKern g = fun z => FourierTransform.fourier g (-z) := by
  funext z
  simp only [czKern, czE]
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul]
  rw [show (↑(-2 * Real.pi * ξ * (-z)) * Complex.I : ℂ) = 2 * Real.pi * Complex.I * (z * ξ) by
    push_cast; ring]
  ring

lemma czKern_mkSymb_continuous {m : ℝ → ℂ} {A : ℝ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ, ‖m ξ‖ ≤ A)
    (N : ℕ) : Continuous (czKern (mkSymb m N)) := by
  rw [czKern_eq_fourier_neg]
  exact (Commons.Analysis.CalderonZygmund.continuous_fourier_of_integrable
    (mkSymb_integrable hm hmb N)).comp continuous_neg

/-- Fatou-type bound for `eLpNorm`: if `gN → g` pointwise a.e. and `eLpNorm (gN N) p ≤ M` for
all `N`, then `eLpNorm g p ≤ M`. -/
theorem eLpNorm_le_of_tendsto_ae {g : ℝ → ℂ} {gN : ℕ → ℝ → ℂ} {p : ℝ} (hp : 0 < p) {M : ℝ≥0∞}
    (hmN : ∀ N, AEStronglyMeasurable (gN N) volume)
    (h : ∀ᵐ x ∂volume, Tendsto (fun N => gN N x) atTop (𝓝 (g x)))
    (hb : ∀ N, eLpNorm (gN N) (ENNReal.ofReal p) volume ≤ M) :
    eLpNorm g (ENNReal.ofReal p) volume ≤ M := by
  have hp0 : (ENNReal.ofReal p) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpt : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbpow : ∀ N, (∫⁻ x, ‖gN N x‖ₑ ^ p) ≤ M ^ p := by
    intro N
    have h1 := hb N
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hmN N),
      ENNReal.toReal_ofReal hp.le] at h1
    have h2 := ENNReal.rpow_le_rpow h1 hp.le
    rw [← ENNReal.rpow_mul] at h2
    rw [show (1 / p) * p = 1 by rw [div_mul_cancel₀ 1 hp.ne']] at h2
    simpa using h2
  have hgm : AEStronglyMeasurable g volume := aestronglyMeasurable_of_tendsto_ae _ hmN h
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hgm,
    ENNReal.toReal_ofReal hp.le]
  have hmain : (∫⁻ x, ‖g x‖ₑ ^ p) ≤ M ^ p := by
    calc ∫⁻ x, ‖g x‖ₑ ^ p
        = ∫⁻ x, Filter.liminf (fun N => ‖gN N x‖ₑ ^ p) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [h] with x hx
          exact (((ENNReal.continuous_rpow_const (y := p)).tendsto ‖g x‖ₑ).comp hx.enorm).liminf_eq.symm
      _ ≤ Filter.liminf (fun N => ∫⁻ x, ‖gN N x‖ₑ ^ p) atTop :=
          lintegral_liminf_le' (fun N =>
            (ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable (hmN N).enorm)
      _ ≤ M ^ p := by
          refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall (fun n => bot_le)⟩ ?_
          intro b hb'
          rcases (hb'.and (Filter.Eventually.of_forall hbpow)).exists with ⟨N, h1, h2⟩
          exact le_trans h1 h2
  calc (∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p)
      ≤ (M ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hmain (by positivity)
    _ = M := by
        rw [← ENNReal.rpow_mul]
        rw [show p * (1 / p) = 1 by rw [mul_one_div, div_self hp.ne']]
        rw [ENNReal.rpow_one]


/-- The Mikhlin multiplier theorem for `A = 1` and `1 < p < 2`. -/
theorem mk_lp_one {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ), ContDiff ℝ 2 m → (∀ ξ : ℝ, ‖m ξ‖ ≤ 1) →
      (∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ 1) → (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ 1) →
      ∀ G : SchwartzMap ℝ ℂ,
      MeasureTheory.eLpNorm
        (fun x : ℝ => ∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)
        (ENNReal.ofReal p) MeasureTheory.volume
      ≤ ENNReal.ofReal C *
        MeasureTheory.eLpNorm (fun x : ℝ => G x) (ENNReal.ofReal p) MeasureTheory.volume := by
  obtain ⟨CΨ, hCΨ, hΨb, hΨ1, hΨ2⟩ := mkPsi_bounds
  have hbump : (0:ℝ) ≤ ∫ y : ℝ, ‖mkPsi y‖ := integral_nonneg (fun y => norm_nonneg _)
  set Aker : ℝ := 5000 * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖) with hAker
  have hAkerpos : (0:ℝ) < Aker := by rw [hAker]; positivity
  set C0 : ℝ := (12 * (24 * 1 ^ 2 + 4 * Aker + 100) * 2 ^ (p - 1) / (p - 1)
      + 16 * 1 ^ 2 / (2 - p)) ^ (1 / p) with hC0
  have hC0pos : (0:ℝ) < C0 := by rw [hC0]; positivity
  refine ⟨C0, hC0pos, fun m hm hmb hm1 hm2 G => ?_⟩
  -- Hörmander condition for the truncated kernel
  have hker : ∀ N : ℕ, ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L/2 →
      (∫⁻ x in {x : ℝ | 50*L ≤ |x|},
        ‖czKern (mkSymb m N) (x - y) - czKern (mkSymb m N) x‖ₑ)
      ≤ ENNReal.ofReal (Aker * 1) := by
    intro N L hL y hy
    rw [mul_one, hAker]
    set D : Finset ℤ := (Finset.range (2*N)).image (fun i : ℕ => (-(N:ℤ) + (i:ℤ))) with hD
    have hsumD : ∀ z : ℝ, (∑ j ∈ D, mkKJ m j z) = ∑ i ∈ Finset.range (2*N), mkKJ m (-(N:ℤ) + (i:ℤ)) z := by
      intro z
      rw [hD, Finset.sum_image]
      intro a _ b _ hab
      have h : (a:ℤ) = (b:ℤ) := by linarith [hab]
      exact_mod_cast h
    have hmeasS : MeasurableSet {x : ℝ | 50*L ≤ |x|} := measurableSet_le measurable_const continuous_id.abs.measurable
    rw [(lintegral_set_comp_neg (fun x => ‖czKern (mkSymb m N) (x - y) - czKern (mkSymb m N) x‖ₑ)
          hmeasS (fun x => by simp only [Set.mem_setOf_eq, abs_neg])).symm]
    rw [show (fun x : ℝ => ‖czKern (mkSymb m N) (-x - y) - czKern (mkSymb m N) (-x)‖ₑ)
          = fun x : ℝ => ‖(∑ j ∈ D, mkKJ m j (x - (-y))) - (∑ j ∈ D, mkKJ m j x)‖ₑ from by
      funext x
      rw [czKern_mkSymb m hm hmb N]
      simp only []
      have hA : (∑ i ∈ Finset.range (2*N), mkKJ m (-(N:ℤ)+(i:ℤ)) (-(-x-y)))
          = ∑ j ∈ D, mkKJ m j (x + y) := by
        rw [show (-(-x-y) : ℝ) = x + y by ring, ← hsumD (x+y)]
      have hB : (∑ i ∈ Finset.range (2*N), mkKJ m (-(N:ℤ)+(i:ℤ)) (-(-x)))
          = ∑ j ∈ D, mkKJ m j x := by
        rw [show (-(-x) : ℝ) = x by ring, ← hsumD x]
      rw [hA, hB]
      simp only [sub_neg_eq_add]]
    simpa using mk_hormander hm (by norm_num : (0:ℝ) < 1) hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2 D L hL (-y)
      (by rw [abs_neg]; exact hy)
  -- the bound for each truncation
  have hN : ∀ N : ℕ, MeasureTheory.eLpNorm
        (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) (ENNReal.ofReal p) MeasureTheory.volume
      ≤ ENNReal.ofReal C0 * MeasureTheory.eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) MeasureTheory.volume := by
    intro N
    have h := cz_lp_small_general (H := ℂ) (mkSymb m N) 1 (∫ ξ : ℝ, ‖mkSymb m N ξ‖)
      Aker 1 zero_lt_one (le_refl 1) hAkerpos
      (fun ξ => mkSymb_norm_le hmb N ξ)
      (mkSymb_integrable hm hmb N) (czKern_mkSymb_continuous hm hmb N).measurable
      (fun z => by
        calc ‖czKern (mkSymb m N) z‖
            ≤ ∫ ξ : ℝ, ‖mkSymb m N ξ * czE z ξ‖ := norm_integral_le_integral_norm _
          _ = ∫ ξ : ℝ, ‖mkSymb m N ξ‖ := by
              apply integral_congr_ae
              filter_upwards with ξ; rw [norm_mul, norm_czE, mul_one])
      (fun L hL w hw => hker N L hL w hw)
      hp1 hp2 (G : ℝ → ℂ) G.integrable
    simpa only [hC0, hAker, mul_one] using h
  -- dominated convergence in the frequency variable
  have hpt : ∀ x : ℝ, Filter.Tendsto (fun N : ℕ => (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) x)
      Filter.atTop (𝓝 (∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)) := by
    intro x
    have hpt' : ∀ N : ℕ, (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) x
        = ∫ ξ : ℝ, (mkSymb m N ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      intro N
      rw [czOp_czKern_eq_mult (mkSymb m N) (mkSymb_integrable hm hmb N) (G : ℝ → ℂ) G.integrable]
    simp only [hpt']
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun ξ => ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖) (fun N => ?_) ?_ (fun N => ?_) ?_
    · have hcont : Continuous (fun ξ : ℝ => (mkSymb m N ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ) :=
        ((hm.continuous.mul (mkTrunc_contDiff N).continuous).mul (continuous_czE x)).smul (by
          rw [← SchwartzMap.fourier_coe G]; exact (FourierTransform.fourier G).continuous)
      exact hcont.aestronglyMeasurable
    · have hFGint : Integrable (fun ξ : ℝ => ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖) := by
        rw [← SchwartzMap.fourier_coe G]
        exact (FourierTransform.fourier G).integrable.norm
      exact hFGint
    · filter_upwards with ξ
      calc ‖(mkSymb m N ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ‖
          = ‖mkSymb m N ξ‖ * ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖ := by
            rw [norm_smul, norm_mul, norm_czE, mul_one]
        _ ≤ 1 * ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖ :=
            mul_le_mul_of_nonneg_right (mkSymb_norm_le hmb N ξ) (norm_nonneg _)
        _ = ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖ := one_mul _
    · filter_upwards [show ∀ᵐ ξ : ℝ ∂(MeasureTheory.volume), ξ ≠ 0 from by
        rw [MeasureTheory.ae_iff]; simp] with ξ hξ
      have ht := mkTrunc_eventually_one ξ hξ
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [ht] with N hN'
      simp only [mkSymb, hN', mul_one]
  -- Fatou
  have hp0 : (0:ℝ) < p := by linarith
  exact eLpNorm_le_of_tendsto_ae (g := fun x : ℝ => ∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)
    (gN := fun N x => (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) x) hp0
    (fun N => by
      exact aestronglyMeasurable_czConv ((czKern_mkSymb_continuous hm hmb N).aestronglyMeasurable)
          G.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall hpt) hN


/-- The Hörmander smoothness condition for the truncated kernel `czKern (mkSymb m N)`, when `m`
satisfies Mikhlin's condition with constant `1`. -/
theorem mkSymb_hormander {m : ℝ → ℂ} {CΨ : ℝ} (hm : ContDiff ℝ 2 m) (hCΨ : 0 < CΨ)
    (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ 1) (hm1 : ∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ 1)
    (hm2 : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ 1)
    (hΨb : ∀ ξ : ℝ, ‖mkPsi ξ‖ ≤ CΨ) (hΨ1 : ∀ ξ : ℝ, ‖deriv mkPsi ξ‖ ≤ CΨ)
    (hΨ2 : ∀ ξ : ℝ, ‖iteratedDeriv 2 mkPsi ξ‖ ≤ CΨ) :
    ∀ N : ℕ, ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L/2 →
      (∫⁻ x in {x : ℝ | 50*L ≤ |x|},
        ‖czKern (mkSymb m N) (x - y) - czKern (mkSymb m N) x‖ₑ)
      ≤ ENNReal.ofReal (5000 * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖)) := by
  intro N L hL y hy
  set D : Finset ℤ := (Finset.range (2*N)).image (fun i : ℕ => (-(N:ℤ) + (i:ℤ))) with hD
  have hsumD : ∀ z : ℝ, (∑ j ∈ D, mkKJ m j z) = ∑ i ∈ Finset.range (2*N), mkKJ m (-(N:ℤ) + (i:ℤ)) z := by
    intro z
    rw [hD, Finset.sum_image]
    intro a _ b _ hab
    have h : (a:ℤ) = (b:ℤ) := by linarith [hab]
    exact_mod_cast h
  have hmeasS : MeasurableSet {x : ℝ | 50*L ≤ |x|} := measurableSet_le measurable_const continuous_id.abs.measurable
  rw [(lintegral_set_comp_neg (fun x => ‖czKern (mkSymb m N) (x - y) - czKern (mkSymb m N) x‖ₑ)
        hmeasS (fun x => by simp only [Set.mem_setOf_eq, abs_neg])).symm]
  rw [show (fun x : ℝ => ‖czKern (mkSymb m N) (-x - y) - czKern (mkSymb m N) (-x)‖ₑ)
        = fun x : ℝ => ‖(∑ j ∈ D, mkKJ m j (x - (-y))) - (∑ j ∈ D, mkKJ m j x)‖ₑ from by
    funext x
    rw [czKern_mkSymb m hm hmb N]
    simp only []
    have hA : (∑ i ∈ Finset.range (2*N), mkKJ m (-(N:ℤ)+(i:ℤ)) (-(-x-y)))
        = ∑ j ∈ D, mkKJ m j (x + y) := by
      rw [show (-(-x-y) : ℝ) = x + y by ring, ← hsumD (x+y)]
    have hB : (∑ i ∈ Finset.range (2*N), mkKJ m (-(N:ℤ)+(i:ℤ)) (-(-x)))
        = ∑ j ∈ D, mkKJ m j x := by
      rw [show (-(-x) : ℝ) = x by ring, ← hsumD x]
    rw [hA, hB]
    simp only [sub_neg_eq_add]]
  simpa using mk_hormander hm (by norm_num : (0:ℝ) < 1) hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2 D L hL (-y)
    (by rw [abs_neg]; exact hy)

/-- A.e.-strong-measurability of the truncated multiplier operator applied to a Schwartz function. -/
theorem mkSymb_aestronglyMeasurable {m : ℝ → ℂ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ 1)
    (G : SchwartzMap ℝ ℂ) (N : ℕ) :
    AEStronglyMeasurable (fun x : ℝ => (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) x) volume :=
  aestronglyMeasurable_czConv ((czKern_mkSymb_continuous hm hmb N).aestronglyMeasurable)
    G.continuous.aestronglyMeasurable

/-- Pointwise convergence, in the frequency variable, of the truncated operators to the full
multiplier operator. -/
theorem mkSymb_tendsto {m : ℝ → ℂ} (hm : ContDiff ℝ 2 m) (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ 1)
    (G : SchwartzMap ℝ ℂ) :
    ∀ x : ℝ, Filter.Tendsto (fun N : ℕ => (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) x)
      Filter.atTop (𝓝 (∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)) := by
  intro x
  have hpt' : ∀ N : ℕ, (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) x
      = ∫ ξ : ℝ, (mkSymb m N ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ := by
    intro N
    rw [czOp_czKern_eq_mult (mkSymb m N) (mkSymb_integrable hm hmb N) (G : ℝ → ℂ) G.integrable]
  simp only [hpt']
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun ξ => ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖) (fun N => ?_) ?_ (fun N => ?_) ?_
  · have hcont : Continuous (fun ξ : ℝ => (mkSymb m N ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ) :=
      ((hm.continuous.mul (mkTrunc_contDiff N).continuous).mul (continuous_czE x)).smul (by
        rw [← SchwartzMap.fourier_coe G]; exact (FourierTransform.fourier G).continuous)
    exact hcont.aestronglyMeasurable
  · have hFGint : Integrable (fun ξ : ℝ => ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖) := by
      rw [← SchwartzMap.fourier_coe G]
      exact (FourierTransform.fourier G).integrable.norm
    exact hFGint
  · filter_upwards with ξ
    calc ‖(mkSymb m N ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ‖
        = ‖mkSymb m N ξ‖ * ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖ := by
          rw [norm_smul, norm_mul, norm_czE, mul_one]
      _ ≤ 1 * ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖ :=
          mul_le_mul_of_nonneg_right (mkSymb_norm_le hmb N ξ) (norm_nonneg _)
      _ = ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖ := one_mul _
  · filter_upwards [show ∀ᵐ ξ : ℝ ∂(MeasureTheory.volume), ξ ≠ 0 from by
      rw [MeasureTheory.ae_iff]; simp] with ξ hξ
    have ht := mkTrunc_eventually_one ξ hξ
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [ht] with N hN'
    simp only [mkSymb, hN', mul_one]

/-- The Mikhlin multiplier theorem for `A = 1` and `p = 2`. -/
theorem mk_lp_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ), ContDiff ℝ 2 m → (∀ ξ : ℝ, ‖m ξ‖ ≤ 1) →
      ∀ G : SchwartzMap ℝ ℂ,
      MeasureTheory.eLpNorm
        (fun x : ℝ => ∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)
        (ENNReal.ofReal 2) MeasureTheory.volume
      ≤ ENNReal.ofReal C *
        MeasureTheory.eLpNorm (fun x : ℝ => G x) (ENNReal.ofReal 2) MeasureTheory.volume := by
  refine ⟨1, one_pos, fun m hm hmb G => ?_⟩
  have hN : ∀ N : ℕ, MeasureTheory.eLpNorm
        (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) (ENNReal.ofReal 2) MeasureTheory.volume
      ≤ ENNReal.ofReal 1 * MeasureTheory.eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal 2) MeasureTheory.volume := by
    intro N
    have h := czOp_czKern_L2 (mkSymb m N) 1 (by norm_num) (fun ξ => mkSymb_norm_le hmb N ξ)
      (mkSymb_integrable hm hmb N) (G : ℝ → ℂ) G.integrable
    simpa using h
  exact eLpNorm_le_of_tendsto_ae
    (g := fun x : ℝ => ∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)
    (gN := fun N x => (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) x) (by norm_num : (0:ℝ) < 2)
    (fun N => mkSymb_aestronglyMeasurable hm hmb G N)
    (Filter.Eventually.of_forall (mkSymb_tendsto hm hmb G)) hN


/-- The Mikhlin multiplier theorem for `A = 1` and `2 < p`, by duality. -/
theorem mk_lp_large {p : ℝ} (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ), ContDiff ℝ 2 m → (∀ ξ : ℝ, ‖m ξ‖ ≤ 1) →
      (∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ 1) → (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ 1) →
      ∀ G : SchwartzMap ℝ ℂ,
      MeasureTheory.eLpNorm
        (fun x : ℝ => ∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)
        (ENNReal.ofReal p) MeasureTheory.volume
      ≤ ENNReal.ofReal C *
        MeasureTheory.eLpNorm (fun x : ℝ => G x) (ENNReal.ofReal p) MeasureTheory.volume := by
  obtain ⟨CΨ, hCΨ, hΨb, hΨ1, hΨ2⟩ := mkPsi_bounds
  set Aker : ℝ := 5000 * (1 + CΨ) * (1 + ∫ y : ℝ, ‖mkPsi y‖) with hAker
  have hAkerpos : (0:ℝ) < Aker := by rw [hAker]; positivity
  have hp1 : (0:ℝ) < p - 1 := by linarith
  set C0 : ℝ := (12 * (24 * 1 ^ 2 + 4 * Aker + 100) * 2 ^ (p / (p - 1) - 1) / (p / (p - 1) - 1)
      + 16 * 1 ^ 2 / (2 - p / (p - 1))) ^ (1 / (p / (p - 1))) with hC0
  have hC0pos : (0:ℝ) < C0 := by
    rw [hC0]
    refine Real.rpow_pos_of_pos ?_ _
    have h1 : (0:ℝ) < p / (p - 1) - 1 := by rw [sub_pos, lt_div_iff₀ hp1]; linarith
    have h2 : (0:ℝ) < 2 - p / (p - 1) := by rw [sub_pos, div_lt_iff₀ hp1]; linarith
    positivity
  have hp'1 : 1 < p / (p - 1) := by rw [lt_div_iff₀ hp1]; linarith
  have hp'2 : p / (p - 1) < 2 := by rw [div_lt_iff₀ hp1]; linarith
  refine ⟨C0, hC0pos, fun m hm hmb hm1 hm2 G => ?_⟩
  have hker0 : ∀ N : ℕ, ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L/2 →
      (∫⁻ x in {x : ℝ | 50*L ≤ |x|},
        ‖czKern (mkSymb m N) (x - y) - czKern (mkSymb m N) x‖ₑ) ≤ ENNReal.ofReal Aker := by
    intro N L hL y hy
    rw [hAker]
    exact mkSymb_hormander hm hCΨ hmb hm1 hm2 hΨb hΨ1 hΨ2 N L hL y hy
  have hdual : ∀ N : ℕ, ∀ g : ℝ → ℂ, Integrable g →
      MeasureTheory.eLpNorm (czOp (czKernConj (mkSymb m N)) g)
        (ENNReal.ofReal (p / (p - 1))) MeasureTheory.volume
      ≤ ENNReal.ofReal C0 * MeasureTheory.eLpNorm g (ENNReal.ofReal (p / (p - 1))) MeasureTheory.volume := by
    intro N g hg
    have hmc_int : Integrable (fun ξ : ℝ => (starRingEnd ℂ) (mkSymb m N ξ)) :=
      integrable_star_comp _ (mkSymb_integrable hm hmb N)
    have hker_conj : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L/2 →
        (∫⁻ x in {x : ℝ | 50*L ≤ |x|},
          ‖czKernConj (mkSymb m N) (x - y) - czKernConj (mkSymb m N) x‖ₑ) ≤ ENNReal.ofReal Aker :=
      czKern_conj_hker (mkSymb m N) (mkSymb_integrable hm hmb N) Aker (hker0 N)
    have h := cz_lp_small_general (H := ℂ) (fun ξ : ℝ => (starRingEnd ℂ) (mkSymb m N ξ)) 1
      (∫ ξ : ℝ, ‖mkSymb m N ξ‖) Aker 1 zero_lt_one (le_refl 1) hAkerpos
      (fun ξ => by rw [Complex.norm_conj]; exact mkSymb_norm_le hmb N ξ)
      hmc_int
      (by
        rw [czKern_conj (mkSymb m N) (mkSymb_integrable hm hmb N)]
        exact (Complex.continuous_conj.comp
          ((czKern_mkSymb_continuous hm hmb N).comp continuous_neg)).measurable)
      (fun z => by
        rw [czKern_conj (mkSymb m N) (mkSymb_integrable hm hmb N), Complex.norm_conj]
        calc ‖czKern (mkSymb m N) (-z)‖
            ≤ ∫ ξ : ℝ, ‖mkSymb m N ξ * czE (-z) ξ‖ := norm_integral_le_integral_norm _
          _ = ∫ ξ : ℝ, ‖mkSymb m N ξ‖ := by
              apply integral_congr_ae
              filter_upwards with ξ; rw [norm_mul, norm_czE, mul_one])
      (fun L hL y hy => by have := hker_conj L hL y hy; simpa only [mul_one, czKernConj] using this)
      hp'1 hp'2 g hg
    simpa only [hC0, czKernConj, mul_one] using h
  have hN : ∀ N : ℕ, MeasureTheory.eLpNorm
        (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) (ENNReal.ofReal p) MeasureTheory.volume
      ≤ ENNReal.ofReal C0 * MeasureTheory.eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) MeasureTheory.volume := by
    intro N
    have hKbdd : ∀ z : ℝ, ‖czKern (mkSymb m N) z‖ ≤ ∫ ξ : ℝ, ‖mkSymb m N ξ‖ := fun z => by
      calc ‖czKern (mkSymb m N) z‖
          ≤ ∫ ξ : ℝ, ‖mkSymb m N ξ * czE z ξ‖ := norm_integral_le_integral_norm _
        _ = ∫ ξ : ℝ, ‖mkSymb m N ξ‖ := by
            apply integral_congr_ae
            filter_upwards with ξ; rw [norm_mul, norm_czE, mul_one]
    have hKm' : Measurable (czKernConj (mkSymb m N)) := by
      rw [czKernConj, czKern_conj (mkSymb m N) (mkSymb_integrable hm hmb N)]
      exact (Complex.continuous_conj.comp
        ((czKern_mkSymb_continuous hm hmb N).comp continuous_neg)).measurable
    exact cz_lp_large (H := ℂ) (mkSymb m N) (czKernConj (mkSymb m N)) C0 (∫ ξ : ℝ, ‖mkSymb m N ξ‖)
      (integral_nonneg (fun ξ => norm_nonneg _)) hKbdd
      (czKern_mkSymb_continuous hm hmb N).measurable hKm' (mkSymb_integrable hm hmb N)
      (fun F g hg => czOp_czKern_adjoint_pairing (mkSymb m N) (∫ ξ : ℝ, ‖mkSymb m N ξ‖) hKbdd
        (czKern_mkSymb_continuous hm hmb N).measurable (mkSymb_integrable hm hmb N) F g hg)
      hp (hdual N) G
  exact eLpNorm_le_of_tendsto_ae
    (g := fun x : ℝ => ∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)
    (gN := fun N x => (czOp (czKern (mkSymb m N)) (G : ℝ → ℂ)) x) (by linarith : (0:ℝ) < p)
    (fun N => mkSymb_aestronglyMeasurable hm hmb G N)
    (Filter.Eventually.of_forall (mkSymb_tendsto hm hmb G)) hN

/-- The Mikhlin multiplier theorem for `A = 1`, all `1 < p < ∞`. -/
theorem mk_lp_sym {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ), ContDiff ℝ 2 m → (∀ ξ : ℝ, ‖m ξ‖ ≤ 1) →
      (∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ 1) → (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ 1) →
      ∀ G : SchwartzMap ℝ ℂ,
      MeasureTheory.eLpNorm
        (fun x : ℝ => ∫ ξ : ℝ, (m ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) ξ)
        (ENNReal.ofReal p) MeasureTheory.volume
      ≤ ENNReal.ofReal C *
        MeasureTheory.eLpNorm (fun x : ℝ => G x) (ENNReal.ofReal p) MeasureTheory.volume := by
  by_cases hp2 : p < 2
  · exact mk_lp_one hp hp2
  · simp only [not_lt] at hp2
    by_cases h2 : p = 2
    · subst h2
      obtain ⟨C, hC, hb⟩ := mk_lp_two
      exact ⟨C, hC, fun m hm hmb _ _ G => hb m hm hmb G⟩
    · exact mk_lp_large (lt_of_le_of_ne hp2 (Ne.symm h2))

/-- **Mikhlin's multiplier theorem** on the real line, in the form needed for Bourgain's
polynomial ergodic theorem: if `m` is `C²` and satisfies the Mikhlin conditions with constant
`A ≥ 0`, then the multiplier operator `T_m G(x) = ∫ ξ, m(ξ) e^{2πi x ξ} 𝓕G(ξ) dξ` is bounded on
`L^p(ℝ)` with norm at most `C A ‖G‖_p`, uniformly in `m` and `A`. -/
theorem mikhlin_multiplier_lp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (A : ℝ), 0 ≤ A → ContDiff ℝ 2 m →
      (∀ ξ : ℝ, ‖m ξ‖ ≤ A) →
      (∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ A) →
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A) →
      ∀ (G : SchwartzMap ℝ ℂ),
        MeasureTheory.eLpNorm
            (fun x : ℝ => ∫ ξ : ℝ,
              (m ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
                • (FourierTransform.fourier (G : ℝ → ℂ) ξ))
            (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ≤ ENNReal.ofReal (C * A) *
              MeasureTheory.eLpNorm (fun x : ℝ => G x) (ENNReal.ofReal p)
                (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ := mk_lp_sym hp
  refine ⟨C0, hC0pos, fun m A hA hm hmb hm1 hm2 G => ?_⟩
  by_cases hA0 : A = 0
  · subst hA0
    have hmzero : m = 0 := by
      funext ξ
      exact norm_le_zero_iff.mp (hmb ξ)
    rw [hmzero]
    have hz : (fun x : ℝ => ∫ ξ : ℝ,
          ((0 : ℝ → ℂ) ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
            • (FourierTransform.fourier (G : ℝ → ℂ) ξ)) = 0 := by
      funext x
      simp
    rw [hz]
    simp
  · have hApos : (0:ℝ) < A := lt_of_le_of_ne hA (Ne.symm hA0)
    set m' : ℝ → ℂ := fun ξ => (A : ℂ)⁻¹ * m ξ with hm'def
    have hAnorm : ‖(A : ℂ)⁻¹‖ = A⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hA]
    have hAmul : ∀ ξ : ℝ, m ξ = (A : ℂ) * m' ξ := by
      intro ξ
      rw [hm'def]
      simp only
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hApos.ne'), one_mul]
    have hm'CD : ContDiff ℝ 2 m' := by
      rw [hm'def]
      exact ContDiff.mul contDiff_const hm
    have hm'b : ∀ ξ : ℝ, ‖m' ξ‖ ≤ 1 := by
      intro ξ
      rw [hm'def]
      simp only
      rw [norm_mul, hAnorm]
      calc A⁻¹ * ‖m ξ‖ ≤ A⁻¹ * A := mul_le_mul_of_nonneg_left (hmb ξ) (by positivity)
        _ = 1 := inv_mul_cancel₀ hApos.ne'
    have hm'1 : ∀ ξ : ℝ, |ξ| * ‖deriv m' ξ‖ ≤ 1 := by
      intro ξ
      have hd : deriv m' ξ = (A : ℂ)⁻¹ * deriv m ξ := by
        rw [hm'def]
        exact deriv_const_mul _ (hm.contDiffAt.differentiableAt (by norm_num))
      rw [hd, norm_mul, hAnorm]
      calc |ξ| * (A⁻¹ * ‖deriv m ξ‖) = A⁻¹ * (|ξ| * ‖deriv m ξ‖) := by ring
        _ ≤ A⁻¹ * A := mul_le_mul_of_nonneg_left (hm1 ξ) (by positivity)
        _ = 1 := inv_mul_cancel₀ hApos.ne'
    have hm'2 : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m' ξ‖ ≤ 1 := by
      intro ξ
      have hd : iteratedDeriv 2 m' ξ = (A : ℂ)⁻¹ * iteratedDeriv 2 m ξ := by
        rw [hm'def]
        exact iteratedDeriv_const_mul _ hm.contDiffAt
      rw [hd, norm_mul, hAnorm]
      calc |ξ| ^ 2 * (A⁻¹ * ‖iteratedDeriv 2 m ξ‖) = A⁻¹ * (|ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖) := by ring
        _ ≤ A⁻¹ * A := mul_le_mul_of_nonneg_left (hm2 ξ) (by positivity)
        _ = 1 := inv_mul_cancel₀ hApos.ne'
    have hTm : (fun x : ℝ => ∫ ξ : ℝ,
          (m ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
            • (FourierTransform.fourier (G : ℝ → ℂ) ξ))
        = (A : ℂ) • (fun x : ℝ => ∫ ξ : ℝ,
          (m' ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
            • (FourierTransform.fourier (G : ℝ → ℂ) ξ)) := by
      funext x
      show (∫ ξ : ℝ, (m ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
            • (FourierTransform.fourier (G : ℝ → ℂ) ξ))
        = (A : ℂ) • (∫ ξ : ℝ, (m' ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
            • (FourierTransform.fourier (G : ℝ → ℂ) ξ))
      rw [← MeasureTheory.integral_smul]
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hAmul ξ, smul_smul]
      congr 1
      ring
    have h0 := hC0 m' hm'CD hm'b hm'1 hm'2 G
    simp only [czE] at h0
    have hAnorme : ‖(A : ℂ)‖ₑ = ENNReal.ofReal A := by
      rw [enorm_eq_ofReal_norm', Complex.norm_real, Real.norm_of_nonneg hA]
    rw [hTm, MeasureTheory.eLpNorm_const_smul]
    calc ‖(A : ℂ)‖ₑ * MeasureTheory.eLpNorm
            (fun x : ℝ => ∫ ξ : ℝ, (m' ξ * czE x ξ) • (FourierTransform.fourier (G : ℝ → ℂ) ξ))
            (ENNReal.ofReal p) MeasureTheory.volume
        ≤ ‖(A : ℂ)‖ₑ * (ENNReal.ofReal C0 *
            MeasureTheory.eLpNorm (fun x : ℝ => G x) (ENNReal.ofReal p) MeasureTheory.volume) :=
          mul_le_mul_of_nonneg_left h0 bot_le
      _ = ENNReal.ofReal (C0 * A) *
            MeasureTheory.eLpNorm (fun x : ℝ => G x) (ENNReal.ofReal p) MeasureTheory.volume := by
          rw [hAnorme, ← mul_assoc, ← ENNReal.ofReal_mul hA, mul_comm A C0]

end
end Commons.Analysis.Fourier
