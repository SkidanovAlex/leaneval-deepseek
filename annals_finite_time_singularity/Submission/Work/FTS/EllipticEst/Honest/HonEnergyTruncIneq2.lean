import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyDefs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.weight_algebra_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Junk-friendly comparison lemmas for the integrals over `Iz`

The Bochner integral of a non-integrable function is `0` (`MeasureTheory.integral_undef`), so a
pointwise comparison `f ≤ g` does **not** imply `∫f ≤ ∫g` unless one knows that the dominating
function `g` is integrable.  The two lemmas below exploit exactly that: the hypotheses are
`g` integrable, `g ≥ 0` (a.e.) and `f ≤ g` (a.e.); the conclusion holds both when `f` is
integrable (monotonicity of the integral) and when it is not (then `∫f = 0` and the claim reduces
to the nonnegativity of `∫g`). -/

theorem setIntegral_le_of_ae_le_of_nonneg {f g : ℝ → ℝ}
    (hle : f ≤ᵐ[volume.restrict Work.Spaces.Iz] g)
    (hg0 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] g)
    (hg : IntegrableOn g Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, g z := by
  by_cases hf : Integrable f (volume.restrict Work.Spaces.Iz)
  · exact integral_mono_ae hf hg hle
  · rw [integral_undef hf]
    exact integral_nonneg_of_ae hg0

theorem neg_setIntegral_le_of_ae_le {f G : ℝ → ℝ}
    (hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), -G z ≤ f z)
    (hG0 : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 ≤ G z)
    (hG : IntegrableOn G Work.Spaces.Iz) :
    -(∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, G z := by
  by_cases hf : Integrable f (volume.restrict Work.Spaces.Iz)
  · have h2 := integral_mono_ae hf.neg hG (hle.mono fun z hz => by
      simp only [Pi.neg_apply]; linarith)
    have h3 : (∫ x in Work.Spaces.Iz, (-f) x) = -(∫ x in Work.Spaces.Iz, f x) := by
      simp only [Pi.neg_apply]
      rw [integral_neg]
    rw [h3] at h2
    exact h2
  · rw [integral_undef hf]
    have h0 := integral_nonneg_of_ae hG0
    linarith

/-- The set `{0}` is null inside `Iz`, so a.e. statements on `Iz` may always assume `z > 0`. -/
theorem ae_pos_of_mem_Iz : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
  intro z hz
  simp only [Set.mem_setOf_eq, not_imp, Set.mem_Ici, Set.mem_singleton_iff] at hz
  exact le_antisymm (le_of_not_gt hz.2) hz.1

/-- The a.e. form (for the ambient measure) of `ae_pos_of_mem_Iz`, suited to
`MeasureTheory.setIntegral_congr_ae`. -/
theorem ae_pos_of_mem_Iz_vol : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Work.Spaces.Iz → 0 < z := by
  refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Work.Spaces.Iz)
    (p := fun z => 0 < z) measurableSet_Ici).mp ?_
  exact ae_pos_of_mem_Iz

/-- The a.e. form (for the ambient measure) of `ae_mem_Ioo_Iθ'`, suited to
`MeasureTheory.setIntegral_congr_ae`. -/
theorem ae_mem_Ioo_of_mem_Iθ_vol :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Work.Spaces.Iθ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Work.Spaces.Iθ)
    (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) measurableSet_Icc).mp ?_
  exact ae_mem_Ioo_Iθ'

/-! ## Elementary bounds for the radial weights -/

/-- `|(z w²)'| ≤ 3 w²` for `z > 0`. -/
theorem deriv_zwSq_abs_le (z : ℝ) (hz : 0 < z) :
    |deriv (fun x : ℝ => x * (Work.Spaces.w x) ^ 2) z| ≤ 3 * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨-, -, -, h4, -⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  rw [h4 z (ne_of_gt hz)]
  have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    rw [Work.Spaces.w, div_pow]; ring
  rw [hw]
  have hz4 : (0:ℝ) < z^4 := by positivity
  have h1z : (0:ℝ) < (1+z)^3 := by positivity
  rw [abs_div, abs_of_pos hz4, abs_mul, abs_of_pos h1z]
  rw [div_le_iff₀ hz4]
  have h : |z - 3| ≤ 3 * (1 + z) := by
    rw [abs_le]; constructor <;> nlinarith
  calc |z - 3| * (1 + z) ^ 3 ≤ (3 * (1 + z)) * (1 + z) ^ 3 :=
        mul_le_mul_of_nonneg_right h (le_of_lt h1z)
    _ = 3 * ((1 + z) ^ 4 / z ^ 4) * z ^ 4 := by field_simp

/-- `|(z² w²)'| ≤ 2 z w²` for `z > 0`. -/
theorem deriv_zsqwSq_abs_le (z : ℝ) (hz : 0 < z) :
    |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z| ≤ 2 * z * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨-, -, h3, -, -⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  rw [h3 z (ne_of_gt hz)]
  have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    rw [Work.Spaces.w, div_pow]; ring
  rw [hw]
  have hz3 : (0:ℝ) < z^3 := by positivity
  have h1z : (0:ℝ) < (1+z)^3 := by positivity
  rw [abs_div, abs_of_pos hz3, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos h1z]
  rw [div_le_iff₀ hz3]
  have h : |z - 1| ≤ 1 + z := by
    rw [abs_le]; constructor <;> linarith
  calc 2 * |z - 1| * (1 + z) ^ 3 ≤ 2 * (1 + z) * (1 + z) ^ 3 := by
        nlinarith [h, h1z]
    _ = 2 * z * ((1 + z) ^ 4 / z ^ 4) * z ^ 3 := by field_simp

/-- `(w)²` is `C^∞` near every `z > 0`. -/
theorem contDiffAt_w_sq {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffAt ℝ n (fun x : ℝ => (Work.Spaces.w x) ^ 2) z := by
  have hw : ContDiffAt ℝ n (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) z :=
    ((contDiffAt_const.add contDiffAt_id).pow 2).div (contDiffAt_id.pow 2)
      (by positivity)
  simpa only [Work.Spaces.w] using hw.pow 2

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
theorem iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_eq_iterate]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply]
  rfl

/-! ## The two product rules for the truncated radial weights -/

/-- First-order product rule for `φ · w² · z`. -/
theorem TruncCutDerivOne (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℝ) (hz : 0 < z) :
    deriv (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x) z
      = deriv φ z * (z * (Work.Spaces.w z) ^ 2)
        + φ z * deriv (fun x : ℝ => x * (Work.Spaces.w x) ^ 2) z := by
  have hφd : DifferentiableAt ℝ φ z := (hφ.contDiffAt).differentiableAt (by norm_num)
  have hWd : DifferentiableAt ℝ (fun x : ℝ => x * (Work.Spaces.w x) ^ 2) z :=
    (contDiffAt_id.mul (contDiffAt_w_sq hz 1)).differentiableAt (by norm_num)
  have hfun : (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x)
      = fun x : ℝ => φ x * (x * (Work.Spaces.w x) ^ 2) := by funext x; ring
  rw [hfun, deriv_fun_mul hφd hWd]

/-- Second-order product rule for `φ · w² · z²`. -/
theorem TruncCutDerivTwo (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℝ) (hz : 0 < z) :
    deriv (deriv (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x ^ 2)) z
      = deriv (deriv φ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        + 2 * deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
        + φ z * deriv (deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)) z := by
  have hφ2 : ContDiffAt ℝ 2 φ z := hφ.contDiffAt
  have hW2 : ContDiffAt ℝ 2 (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z :=
    (contDiffAt_id.pow 2).mul (contDiffAt_w_sq hz 2)
  have hfun : (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x ^ 2)
      = fun x : ℝ => φ x * (x ^ 2 * (Work.Spaces.w x) ^ 2) := by funext x; ring
  rw [hfun]
  have hleib := iteratedDeriv_fun_mul (n := 2) (x := z) hφ2 hW2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at hleib
  have hLHS : deriv (deriv (fun x : ℝ => φ x * (x ^ 2 * (Work.Spaces.w x) ^ 2))) z
      = iteratedDeriv 2 (fun x : ℝ => φ x * (x ^ 2 * (Work.Spaces.w x) ^ 2)) z := by
    rw [iteratedDeriv_two_eq]
  rw [hLHS, hleib]
  norm_num
  rw [iteratedDeriv_two_eq φ]
  rw [iteratedDeriv_two_eq (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)]
  ring

/-! ## The two cutoff-derivative bounds of the truncation error -/

/-- The derivatives of `cut n` are bounded after multiplication by the powers of `z` that make
them of the same homogeneity as `w²`. -/
theorem cut_deriv_mul_bdd (n : ℕ) :
    (∃ C : ℝ, ∀ z : ℝ, |deriv (Work.FTS.EllipticEst.cut n) z| * z ≤ C) ∧
    (∃ C : ℝ, ∀ z : ℝ, |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * z ^ 2 ≤ C) := by
  have hφ : ContDiff ℝ Work.Stability.smoothOrder (Work.FTS.EllipticEst.cut n) :=
    Work.FTS.EllipticEst.cut_contDiff n
  have hone : (1 : WithTop ℕ∞) + 1 ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hzero : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞) := by simp
  have hd1 : ContDiffOn ℝ 1 (deriv (Work.FTS.EllipticEst.cut n)) (Set.Ioi 0) :=
    (hφ.contDiffOn.mono (Set.subset_univ _)).deriv_of_isOpen isOpen_Ioi hone
  have hc1 : ContinuousOn (deriv (Work.FTS.EllipticEst.cut n))
      (Set.Icc (1 / (n + 1 : ℝ)) (3 * (n + 1 : ℝ))) :=
    hd1.continuousOn.mono (fun z hz => lt_of_lt_of_le (by positivity) hz.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  have hn1 : (1:ℝ) ≤ (n:ℝ) + 1 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hmem0 : (3 * (n + 1 : ℝ)) ∈ Set.Icc (1 / (n + 1 : ℝ)) (3 * (n + 1 : ℝ)) := by
    refine ⟨?_, le_rfl⟩
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ((n:ℝ) + 1))]
    nlinarith
  have hM0 : 0 ≤ M := by
    have := hM _ hmem0
    rw [Real.norm_eq_abs] at this
    exact le_trans (abs_nonneg _) this
  have hd2 : ContDiffOn ℝ 0 (deriv (deriv (Work.FTS.EllipticEst.cut n))) (Set.Ioi 0) :=
    hd1.deriv_of_isOpen isOpen_Ioi hzero
  have hc2 : ContinuousOn (deriv (deriv (Work.FTS.EllipticEst.cut n)))
      (Set.Icc (1 / (n + 1 : ℝ)) (3 * (n + 1 : ℝ))) :=
    hd2.continuousOn.mono (fun z hz => lt_of_lt_of_le (by positivity) hz.1)
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  have hM20 : 0 ≤ M2 := by
    have := hM2 _ hmem0
    rw [Real.norm_eq_abs] at this
    exact le_trans (abs_nonneg _) this
  have hfar1 : ∀ z : ℝ, z < 1 / (n + 1 : ℝ) → deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
    intro z hz
    have hy0 : (fun w => Work.FTS.EllipticEst.cut n w) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hz] with w hw
      exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt hw)
    rw [hy0.deriv_eq]; simp
  have hfar1' : ∀ z : ℝ, 3 * (n + 1 : ℝ) < z → deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
    intro z hz
    have hy0 : (fun w => Work.FTS.EllipticEst.cut n w) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt hw)
    rw [hy0.deriv_eq]; simp
  have hfar2 : ∀ z : ℝ, z < 1 / (n + 1 : ℝ) →
      deriv (deriv (Work.FTS.EllipticEst.cut n)) z = 0 := by
    intro z hz
    have hy0 : (fun w => deriv (Work.FTS.EllipticEst.cut n) w) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hz] with w hw
      exact hfar1 w hw
    rw [hy0.deriv_eq]; simp
  have hfar2' : ∀ z : ℝ, 3 * (n + 1 : ℝ) < z →
      deriv (deriv (Work.FTS.EllipticEst.cut n)) z = 0 := by
    intro z hz
    have hy0 : (fun w => deriv (Work.FTS.EllipticEst.cut n) w) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact hfar1' w hw
    rw [hy0.deriv_eq]; simp
  constructor
  · refine ⟨M * (3 * (n + 1 : ℝ)), fun z => ?_⟩
    by_cases hz : z ∈ Set.Icc (1 / (n + 1 : ℝ)) (3 * (n + 1 : ℝ))
    · have h1 := hM z hz
      rw [Real.norm_eq_abs] at h1
      have hz0 : 0 ≤ z := le_trans (by positivity) hz.1
      calc |deriv (Work.FTS.EllipticEst.cut n) z| * z ≤ M * z :=
            mul_le_mul_of_nonneg_right h1 hz0
        _ ≤ M * (3 * (n + 1 : ℝ)) := mul_le_mul_of_nonneg_left hz.2 hM0
    · have hlt : z < 1 / (n + 1 : ℝ) ∨ 3 * (n + 1 : ℝ) < z := by
        rcases lt_or_ge z (1 / (n + 1 : ℝ)) with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge fun h2 => hz ⟨h, h2⟩)
      rw [hlt.elim (hfar1 z) (hfar1' z), abs_zero, zero_mul]
      exact mul_nonneg hM0 (by positivity)
  · refine ⟨M2 * (3 * (n + 1 : ℝ)) ^ 2, fun z => ?_⟩
    by_cases hz : z ∈ Set.Icc (1 / (n + 1 : ℝ)) (3 * (n + 1 : ℝ))
    · have h1 := hM2 z hz
      rw [Real.norm_eq_abs] at h1
      have hz0 : 0 ≤ z := le_trans (by positivity) hz.1
      have hz2 : z ^ 2 ≤ (3 * (n + 1 : ℝ)) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hz0, abs_of_nonneg (by positivity)]
        exact hz.2
      calc |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * z ^ 2 ≤ M2 * z ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ ≤ M2 * (3 * (n + 1 : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hz2 hM20
    · have hlt : z < 1 / (n + 1 : ℝ) ∨ 3 * (n + 1 : ℝ) < z := by
        rcases lt_or_ge z (1 / (n + 1 : ℝ)) with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge fun h2 => hz ⟨h, h2⟩)
      rw [hlt.elim (hfar2 z) (hfar2' z), abs_zero, zero_mul]
      exact mul_nonneg hM20 (by positivity)

/-! ## Slicewise honesty of the source `F` and the angular AM–GM

These are the ingredients that turn the pointwise (in `θ`) AM–GM `F·Ψ ≤ (F²+Ψ²)/2` into a
comparison of the iterated integrals. -/

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-- The `θ`-slice of `∂_θθΨ` is a.e. strongly measurable. -/
theorem aesm_pthIter2_slice (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo]
  exact (continuousOn_pthIter2' h hz).aestronglyMeasurable measurableSet_Ioo

/-- The `θ`-slice of `bslOp α Ψ` is a.e. strongly measurable, for `z > 0`. -/
theorem aesm_bslOp_slice (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Work.Elliptic.bslOp α Ψ z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hS := smoothOpen_of_forall h.sm
  have h1 : AEStronglyMeasurable (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (volume.restrict Work.Spaces.Iθ) := SmoothOpen.aesm_slice_pzIter hS 2 hz
  have h2 : AEStronglyMeasurable (fun θ => Work.Spaces.pz Ψ z θ)
      (volume.restrict Work.Spaces.Iθ) := SmoothOpen.aesm_slice_pzIter hS 1 hz
  have h3 : AEStronglyMeasurable (fun θ => Ψ z θ) (volume.restrict Work.Spaces.Iθ) :=
    SmoothOpen.aesm_slice_pzIter hS 0 hz
  have h4 := aesm_pthIter2_slice h hz
  have h5 := aesm_pth_tan_mul h hz
  have hgoal : (fun θ => Work.Elliptic.bslOp α Ψ z θ)
      = fun θ => (-(α ^ 2 * z ^ 2)) * Work.Spaces.pzIter 2 Ψ z θ
          - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
          + (-(Work.Spaces.pthIter 2 Ψ z θ)
            + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ) := by
    funext θ
    rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
  rw [hgoal]
  exact (((h1.const_mul _).sub (h2.const_mul _)).add
    (((h4.neg).add h5).sub (h3.const_mul 6)))

/-- The `θ`-slice of the source `F` is a.e. strongly measurable, for `z > 0`. -/
theorem aesm_F_slice (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => F z θ) (volume.restrict Work.Spaces.Iθ) := by
  refine (aesm_bslOp_slice h hz).congr ?_
  filter_upwards [ae_mem_Ioo_Iθ'] with θ hθ
  exact h.eq z hz θ hθ.1 hθ.2

/-- `(F z ·)²` is integrable on the angular interval, for `z > 0` (honesty of the source). -/
theorem hon_F_slice_sq_integrable (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (F z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_sigma (aesm_F_slice h hz) (hon_memF_sigma h hz)

/-- `F z · · Ψ z ·` is integrable on the angular interval, for `z > 0`. -/
theorem hon_F_mul_psi_slice_integrable (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => F z θ * Ψ z θ) Work.Spaces.Iθ := by
  have hF2 := hon_F_slice_sq_integrable h hz
  have hP2 := integrableOn_sq_psi' h hz
  have hmaj : IntegrableOn (fun θ => (1/2) * ((F z θ)^2 + (Ψ z θ)^2)) Work.Spaces.Iθ :=
    (hF2.add hP2).const_mul (1/2)
  refine hmaj.mono' ((aesm_F_slice h hz).mul (aesm_psi_slice h hz)) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_mul]
  have hsq := sq_nonneg (|F z θ| - |Ψ z θ|)
  have h1 : (F z θ)^2 = |F z θ|^2 := (sq_abs _).symm
  have h2 : (Ψ z θ)^2 = |Ψ z θ|^2 := (sq_abs _).symm
  rw [h1, h2]
  nlinarith [hsq, abs_nonneg (F z θ), abs_nonneg (Ψ z θ)]

/-- **The slicewise AM–GM**: for `z > 0`, `∫_θ FΨ ≤ (1/2)∫_θ F² + (1/2)∫_θ Ψ²`. -/
theorem hon_slice_amgm (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ)
      ≤ (1/2) * (∫ θ in Work.Spaces.Iθ, (F z θ)^2)
        + (1/2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ)^2) := by
  have hFP := hon_F_mul_psi_slice_integrable h hz
  have hF2 := hon_F_slice_sq_integrable h hz
  have hP2 := integrableOn_sq_psi' h hz
  have hmaj : IntegrableOn (fun θ => (1/2) * ((F z θ)^2 + (Ψ z θ)^2)) Work.Spaces.Iθ :=
    (hF2.add hP2).const_mul (1/2)
  have hle : (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (1/2) * ((F z θ)^2 + (Ψ z θ)^2) :=
    integral_mono_ae hFP hmaj (Filter.Eventually.of_forall fun θ => by
      have hsq := sq_nonneg (F z θ - Ψ z θ)
      nlinarith [hsq])
  rw [integral_const_mul, integral_add hF2 hP2] at hle
  linarith

/-- **Strong measurability of the slice mass `z ↦ ∫_θ Ψ(z,θ)²`.** -/
theorem aesm_P2 (h : Hon α F Ψ) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Ψ p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) :=
    ((h.sm 0).continuousOn).pow 2
  have h2 := (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  simpa using h2

/-- The weight `(w)²` is measurable. -/
theorem measurable_wSq : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  have : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp only [Work.Spaces.w]
  rw [this]
  exact (((measurable_const.add measurable_id).pow_const 2).div
    (measurable_id.pow_const 2)).pow_const 2

/-- **`φ w² · P2` is integrable** as soon as `w² · P2` is, for `0 ≤ φ ≤ 1`. -/
theorem integrableOn_phi_wSq_P2 {φ : ℝ → ℝ} (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hφ1 : ∀ z : ℝ, φ z ≤ 1) (hφc : Continuous φ) (h : Hon α F Ψ)
    (hP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz := by
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have haesm : AEStronglyMeasurable (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) (volume.restrict Work.Spaces.Iz) :=
    ((hφc.measurable.aestronglyMeasurable).mul measurable_wSq.aestronglyMeasurable).mul (aesm_P2 h)
  refine hP.mono' haesm ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (hφ0 z) (sq_nonneg _)) (hP2nn z))]
  calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ 1 * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hφ1 z) (sq_nonneg _)) (hP2nn z)
    _ = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) := by ring

/-! ## The two truncation-error integrals are honest -/

/-- The second truncation-error integral (the `φ'`-term against `z w²`) is integrable. -/
theorem integrableOn_truncErr_E2 (h : Hon α F Ψ) (φ : ℝ → ℝ)
    (hC1 : ∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C)
    (hP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    IntegrableOn (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz := by
  obtain ⟨C, hC⟩ := hC1
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have haesm : AEStronglyMeasurable (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) (volume.restrict Work.Spaces.Iz) :=
    (((measurable_deriv φ).abs.aestronglyMeasurable).mul
      ((measurable_id.mul measurable_wSq).aestronglyMeasurable)).mul (aesm_P2 h)
  refine (hP.const_mul (max C 0)).mono' haesm ?_
  filter_upwards [ae_pos_of_mem_Iz] with z hz
  have hCz : |deriv φ z| * z ≤ C := hC z
  have hCmax : |deriv φ z| * z ≤ max C 0 := le_trans hCz (le_max_left _ _)
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hW1 : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (le_of_lt hz) hw2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      = (|deriv φ z| * z) * ((Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by ring
    _ ≤ max C 0 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hCmax (mul_nonneg hw2 (hP2nn z))

/-- The first truncation-error integral (the `φ'`- and `φ''`-terms against `z² w²` and `w²`) is
integrable. -/
theorem integrableOn_truncErr_E1 (h : Hon α F Ψ) (φ : ℝ → ℝ)
    (hC1 : ∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C)
    (hC2 : ∃ C : ℝ, ∀ z : ℝ, |deriv (deriv φ) z| * z ^ 2 ≤ C)
    (hP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    IntegrableOn (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz := by
  obtain ⟨C₁, hC₁⟩ := hC1
  obtain ⟨C₂, hC₂⟩ := hC2
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have haesm : AEStronglyMeasurable (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) (volume.restrict Work.Spaces.Iz) := by
    have hA : AEStronglyMeasurable (fun z => 2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|)
        (volume.restrict Work.Spaces.Iz) :=
      (((measurable_deriv φ).abs.const_mul 2).aestronglyMeasurable).mul
        ((measurable_deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)).abs.aestronglyMeasurable)
    have hB : AEStronglyMeasurable (fun z => |deriv (deriv φ) z|
        * (z ^ 2 * (Work.Spaces.w z) ^ 2)) (volume.restrict Work.Spaces.Iz) :=
      ((measurable_deriv (deriv φ)).abs.aestronglyMeasurable).mul
        (((measurable_id.pow_const 2).mul measurable_wSq).aestronglyMeasurable)
    exact (hA.add hB).mul (aesm_P2 h)
  refine (hP.const_mul (max (4 * C₁ + C₂) 0)).mono' haesm ?_
  filter_upwards [ae_pos_of_mem_Iz] with z hz
  have hW2' := deriv_zsqwSq_abs_le z hz
  have hC₁z : |deriv φ z| * z ≤ C₁ := hC₁ z
  have hC₂z : |deriv (deriv φ) z| * z ^ 2 ≤ C₂ := hC₂ z
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hznn : 0 ≤ z := le_of_lt hz
  have hcoef : (2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
      + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2 := by
    have h1 : 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        ≤ 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2 := by
      calc 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          ≤ 2 * |deriv φ z| * (2 * z * (Work.Spaces.w z) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hW2' (by positivity)
        _ = 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2 := by ring
    have h2 : |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C₂ * (Work.Spaces.w z) ^ 2 := by
      calc |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          = (|deriv (deriv φ) z| * z ^ 2) * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ C₂ * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hC₂z hw2
    have h3 : 4 * (|deriv φ z| * z) * (Work.Spaces.w z) ^ 2 ≤ 4 * C₁ * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hw2
    have h4 : (4 * C₁ + C₂) * (Work.Spaces.w z) ^ 2 ≤ max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hw2
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ (max (4 * C₁ + C₂) 0 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef (hP2nn z)
    _ = max (4 * C₁ + C₂) 0 * ((Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by ring

/-! ## The three truncation bounds

Each is of the "junk-friendly" shape: the pointwise bound holds a.e., the dominating function is
nonnegative a.e. and integrable, so the comparison of the iterated integrals follows whether or not
the bounded side is integrable. -/

/-- The source pairing `∫_z φ w² ∫_θ FΨ` obeys the angular AM–GM. -/
theorem trunc_A_le (h : Hon α F Ψ) {φ : ℝ → ℝ} (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hPc : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hS : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ))
      ≤ (1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
        + (1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
  have hgint : IntegrableOn (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
      + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) Work.Spaces.Iz :=
    (hS.const_mul (1 / 2)).add (hPc.const_mul (1 / 2))
  have hg0 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
      + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) :=
    Filter.Eventually.of_forall fun z => by
      have h1 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 :=
        integral_nonneg fun θ => sq_nonneg _
      have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
        integral_nonneg fun θ => sq_nonneg _
      have h4 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2) :=
        mul_nonneg (mul_nonneg (hφ0 z) h1) h2
      have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
        mul_nonneg (mul_nonneg (hφ0 z) h1) h3
      first | simp only [Pi.zero_apply] | skip
      linarith
  have hle : (fun z => φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ))
      ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
        + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) := by
    filter_upwards [ae_pos_of_mem_Iz] with z hz
    have hamgm := hon_slice_amgm h hz
    have hw : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (hφ0 z) (sq_nonneg _)
    calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ)
        = (φ z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ) := by ring
      _ ≤ (φ z * (Work.Spaces.w z) ^ 2)
            * ((1 / 2) * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
              + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hamgm hw
      _ = (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))
          + (1 / 2) * (φ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by ring
  have hmain := setIntegral_le_of_ae_le_of_nonneg hle hg0 hgint
  rw [integral_add (hS.const_mul (1 / 2)) (hPc.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul] at hmain
  exact hmain

/-- The second-order truncation term obeys the paper's pointwise weight bound. -/
theorem trunc_B2_le (h : Hon α F Ψ) {φ : ℝ → ℝ} (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hφ2 : ContDiff ℝ 2 φ)
    (hE1 : IntegrableOn (fun z => (2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hPc : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (∫ z in Work.Spaces.Iz, (2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 6 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have hgint : IntegrableOn (fun z => ((2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
      Work.Spaces.Iz :=
    hE1.add (hPc.const_mul 6)
  have hg0 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z => ((2 * |deriv φ z|
        * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) :=
    Filter.Eventually.of_forall fun z => by
      have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
        integral_nonneg fun θ => sq_nonneg _
      have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ 2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
        add_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) h2))
      have h4 : 0 ≤ (2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) := mul_nonneg h3 h1
      have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
        mul_nonneg (mul_nonneg (hφ0 z) h2) h1
      first | simp only [Pi.zero_apply] | skip
      linarith
  have hle : (fun z => deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => ((2 * |deriv φ z|
          * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) := by
    filter_upwards [ae_pos_of_mem_Iz] with z hz
    obtain ⟨-, -, -, -, -, hW2le, -, -, -, -, -⟩ :=
      Work.FTS.EllipticEst.weight_algebra_fts
    have hW2 := hW2le z hz
    have hderiv := TruncCutDerivTwo φ hφ2 z hz
    have hP2 := hP2nn z
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hw2z : 0 ≤ z ^ 2 * (Work.Spaces.w z) ^ 2 := mul_nonneg (sq_nonneg _) hw2
    have hb1 : deriv (deriv φ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hw2z
    have hb2 : 2 * deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
        ≤ 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z| := by
      have h0 : deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
          ≤ |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z| := by
        rw [← abs_mul]
        exact le_abs_self _
      linarith [h0]
    have hb3 : φ z * deriv (deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)) z
        ≤ 6 * (φ z * (Work.Spaces.w z) ^ 2) := by
      have hh := mul_le_mul_of_nonneg_left hW2 (hφ0 z)
      linarith [hh]
    have hsum : deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
        ≤ (2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          + 6 * (φ z * (Work.Spaces.w z) ^ 2) := by
      rw [hderiv]
      linarith [hb1, hb2, hb3]
    calc deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ ((2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          + 6 * (φ z * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
          mul_le_mul_of_nonneg_right hsum hP2
      _ = ((2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 6 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by ring
  have hmain := setIntegral_le_of_ae_le_of_nonneg hle hg0 hgint
  rw [integral_add hE1 (hPc.const_mul 6), integral_const_mul] at hmain
  exact hmain

/-- The first-order truncation term obeys the paper's pointwise weight bound. -/
theorem trunc_B1_le (h : Hon α F Ψ) {φ : ℝ → ℝ} (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    (hφ2 : ContDiff ℝ 2 φ)
    (hE2 : IntegrableOn (fun z => |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hPc : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz) :
    -(∫ z in Work.Spaces.Iz,
        deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 3 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
  have hP2nn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have hgint : IntegrableOn (fun z => (|deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + 3 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
      Work.Spaces.Iz :=
    hE2.add (hPc.const_mul 3)
  have hg0 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] (fun z => (|deriv φ z|
      * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + 3 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) := by
    filter_upwards [ae_pos_of_mem_Iz] with z hz
    have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (le_of_lt hz) h2
    have h4 : 0 ≤ |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) h3) h1
    have h5 : 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      mul_nonneg (mul_nonneg (hφ0 z) h2) h1
    first | simp only [Pi.zero_apply] | skip
    linarith
  -- the pointwise lower bound
  have hle : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      -((|deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        + 3 * (φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
      ≤ deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) := by
    filter_upwards [ae_pos_of_mem_Iz] with z hz
    obtain ⟨-, -, -, -, -, -, hW1le, -, -, -, -⟩ :=
      Work.FTS.EllipticEst.weight_algebra_fts
    have hW1 := hW1le z hz
    have hderiv := TruncCutDerivOne φ hφ2 z hz
    have hP2 := hP2nn z
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hz1 : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (le_of_lt hz) hw2
    -- the two nonnegative contributions to `deriv (φ w² z) z + |deriv φ z| (z w²) + 3 φ w²`
    have hA : 0 ≤ (deriv φ z + |deriv φ z|) * (z * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (by linarith [neg_le_abs (deriv φ z)]) hz1
    have hB : 0 ≤ φ z
        * (deriv (fun z => z * (Work.Spaces.w z) ^ 2) z + 3 * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (hφ0 z) (by linarith [hW1])
    rw [hderiv]
    nlinarith [hA, hB, hP2, mul_nonneg (add_nonneg hA hB) hP2]
  have hmain := neg_setIntegral_le_of_ae_le hle hg0 hgint
  rw [integral_add hE2 (hPc.const_mul 3), integral_const_mul] at hmain
  exact hmain


/-! ## The general form of the truncated inequality, and the main statement -/

/-- **The truncated energy inequality for an abstract weight `φ` with the five properties of
`cut n`.**  This is the mathematical content of `HonEnergyTruncIneq2`; the cut-off is plugged in
afterwards. -/
theorem HonEnergyTruncIneq_aux (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Hon α F Ψ) (φ : ℝ → ℝ)
    (hφ0 : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1)
    (hφc : Continuous φ) (hφ2 : ContDiff ℝ 2 φ)
    (hC1 : ∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C)
    (hC2 : ∃ C : ℝ, ∀ z : ℝ, |deriv (deriv φ) z| * z ^ 2 ≤ C)
    (hid : TruncId α Ψ φ)
    (hP : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hX : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hS : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)) Work.Spaces.Iz) :
    TruncX α Ψ φ ≤ TruncSrc α F φ
      + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) * TruncP Ψ (fun _ => 1)
      + TruncErr α Ψ φ := by
  have hα : 0 < α := h.hα
  rw [TruncX, TruncSrc, TruncP, TruncErr]
  simp only [one_mul]
  -- the two integrability statements coming from the honesty of the mass
  have hPc : IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz :=
    integrableOn_phi_wSq_P2 hφ0 hφ1 hφc h hP
  have hE1 := integrableOn_truncErr_E1 h φ hC1 hC2 hP
  have hE2 := integrableOn_truncErr_E2 h φ hC1 hP
  -- the three comparisons
  have hA := trunc_A_le h hφ0 hPc hS
  have hB2 := trunc_B2_le h hφ0 hφ2 hE1 hPc
  have hB1 := trunc_B1_le h hφ0 hφ2 hE2 hPc
  -- the two elementary nonnegativities
  have hCnn : 0 ≤ ∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2) :=
    integral_nonneg fun z => mul_nonneg (mul_nonneg (hφ0 z) (sq_nonneg _))
      (integral_nonneg fun θ => sq_nonneg _)
  have hPcf : (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
    setIntegral_le_of_ae_le_of_nonneg
      (f := fun z => φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      (g := fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      (Filter.Eventually.of_forall fun z => by
        have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
          integral_nonneg fun θ => sq_nonneg _
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hφ1 z) h2) h3
        simpa using this)
      (Filter.Eventually.of_forall fun z => by
        exact mul_nonneg (sq_nonneg _) (integral_nonneg fun θ => sq_nonneg _)) hP
  -- the identity, with the left-hand side rewritten along `bslOp α Ψ = F`
  have hAeq : (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Ψ z θ))
      = ∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ) := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ici ?_
    filter_upwards [ae_pos_of_mem_Iz_vol] with z hz hzI
    have hzpos : 0 < z := hz hzI
    have hinner : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Ψ z θ)
        = ∫ θ in Work.Spaces.Iθ, F z θ * Ψ z θ := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [ae_mem_Ioo_of_mem_Iθ_vol] with θ hθ hθI
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hθ hθI
      rw [h.eq z hzpos θ hθ'.1 hθ'.2]
    rw [hinner]
  rw [TruncId] at hid
  rw [hAeq] at hid
  -- the coefficient arithmetic
  have hcoef : 0 ≤ α * (5 + α) / 2 := by nlinarith
  have hK : 0 ≤ 13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α) := by nlinarith
  have h5 : 0 ≤ α ^ 2 / 2 := by positivity
  nlinarith [hid, hA, hB2, hB1, hCnn, hPcf,
    mul_le_mul_of_nonneg_left hPcf hK,
    mul_le_mul_of_nonneg_left hB2 h5,
    mul_le_mul_of_nonneg_left hB1 hcoef]

/-- **The truncated form of the honest `w²`-weighted energy inequality** (with the integrability
of the two dominant integrals as explicit hypotheses, so that none of the integrals below is the
junk value `0`).  Assume the truncated energy identity `TruncId α Ψ (cut n)` — proved for every
honest `C^∞` weight by `HonTruncIdentitySmooth` — and `Hon α F Ψ`, together with the honesty of the
`w²`-mass `∫_z w²∫_θ Ψ²` and of the two dominant truncated integrals.  Then, using `bslOp α Ψ = F`
on the open quadrant, the pointwise weight bounds `|(z²w²)''| ≤ 6w²`, `|(zw²)'| ≤ 3w²`, `cut n ≤ 1`
and the AM–GM inequality `∫W FΨ ≤ (1/2)∫W F² + (1/2)∫W Ψ²`, one obtains the truncated energy
inequality with the explicit truncation error `TruncErr α Ψ (cut n)` and the explicit constant
`13/2 + 3α² + (3/2)α(5+α)`. -/
theorem HonEnergyTruncIneq2 (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) (n : ℕ)
    (hid : Work.FTS.EllipticEst.Honest.TruncId α Ψ (Work.FTS.EllipticEst.cut n))
    (hP : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hX : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Ψ z θ) ^ 2)) Work.Spaces.Iz)
    (hS : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)) Work.Spaces.Iz) :
    Work.FTS.EllipticEst.Honest.TruncX α Ψ (Work.FTS.EllipticEst.cut n)
      ≤ Work.FTS.EllipticEst.Honest.TruncSrc α F (Work.FTS.EllipticEst.cut n)
        + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
            * Work.FTS.EllipticEst.Honest.TruncP Ψ (fun _ => 1)
        + Work.FTS.EllipticEst.Honest.TruncErr α Ψ (Work.FTS.EllipticEst.cut n) := by
  have hcut2 : ContDiff ℝ 2 (Work.FTS.EllipticEst.cut n) :=
    (Work.FTS.EllipticEst.cut_contDiff n).of_le (by simp [Work.Stability.smoothOrder])
  obtain ⟨hC1, hC2⟩ := cut_deriv_mul_bdd n
  exact HonEnergyTruncIneq_aux α F Ψ h (Work.FTS.EllipticEst.cut n)
    (fun z => Work.FTS.EllipticEst.cut_nonneg n z)
    (fun z => Work.FTS.EllipticEst.cut_le_one n z)
    hcut2.continuous hcut2 hC1 hC2 hid hP hX hS

end Work.FTS.EllipticEst.Honest
