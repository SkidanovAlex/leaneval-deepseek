import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.L12Add
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RowsN0Aux

/-! ## Row 1 of the design table, unconditionally

Row 1 (`|N₀₁ + N₀₂|_{ℋ⁴} ≤ Cα²`) is the only one of the seven rows that mentions *no* interface
clause at all: it is a statement about the concrete functions `N01`, `N02` of `F_*` alone, and
it is therefore **true independently of the defect documented above**.  It is proved here as a
standalone lemma, so that a repaired N4 interface can consume it directly. -/

/-- **Row 1 of design §3.4, unconditionally.**  For `0 < α ≤ 1`,
`|N₀₁ + N₀₂|_{ℋ⁴} ≤ K α²` with a universal `K` (the constant of
`Work.Construction.H4N_GammaTerm_le`).

The pair `N01 + N02` collapses (on the open quadrant, by `N0_first_two_eq'`) to the quadratic
vanishing function `8α²c2m(θ)z²Γ(α,θ)/(c(α)(1+z)⁴)`, whose `ℋ⁴`-norm is `O(α²)`; the identity
holds on `Iz × Iθ` and `HkSq` only sees the open quadrant (`HkSq_congr_open`). -/
theorem N0fix_bound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2 := by
  obtain ⟨C, hC, hle⟩ := Work.Construction.H4N_GammaTerm_le
  refine ⟨C, hC, fun α hα hα1 => ?_⟩
  have hcongr : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N0fix α)
      = Work.Spaces.HkSq α 4 (fun z θ => 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2
          * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 4)) := by
    refine Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ hθ2 => ?_)
    show Work.FTS.Nonlin.N0fix α z θ = 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2
      * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 4)
    rw [Work.FTS.Nonlin.N0fix]
    simp only [Work.Construction.N01, Work.Construction.N02]
    rw [show (3 / (2 * α)) * Work.Construction.s2 θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          + -Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = (3 / (2 * α)) * Work.Construction.s2 θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ from by ring]
    exact Work.Construction.N0_first_two_eq' hα hα1 (le_of_lt hz)
      ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N0fix α)
      = Work.Construction.H4N α (fun z θ => 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2
          * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 4)) := by
    simp only [Work.FTS.Nonlin.Xn, Work.Construction.H4N, Work.Spaces.HkNorm, hcongr]
  rw [hXn]
  exact hle α hα hα1

/-! ## Two honest fundamentals, and the row 2 derivation

The lemmas below are independent of the defect of §`RowCtx`: they are statements about the
weighted `ℋ⁴`-norm that a *repaired* interface needs as well. -/

/-- Multiplication by a constant commutes with `deriv`, unconditionally: `deriv` is `0` where
the function is not differentiable, and `c • f` is differentiable at `z` iff `f` is (for
`c ≠ 0`), so the two junk values agree. -/
theorem deriv_const_mul' (c : ℝ) (g : ℝ → ℝ) (z : ℝ) :
    deriv (fun z' => c * g z') z = c * deriv g z := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; simp
  · by_cases hg : DifferentiableAt ℝ g z
    · exact deriv_const_mul c hg
    · have hnon : ¬ DifferentiableAt ℝ (fun z' => c * g z') z := by
        intro h
        have h2 : DifferentiableAt ℝ (fun z' => c⁻¹ * (c * g z')) z := h.const_mul c⁻¹
        have heq : (fun z' => c⁻¹ * (c * g z')) = g := by
          funext z'
          rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        rw [heq] at h2
        exact hg h2
      rw [deriv_zero_of_not_differentiableAt hnon,
        deriv_zero_of_not_differentiableAt hg, mul_zero]

/-- `D_z^i` commutes with multiplication by a constant. -/
theorem DzIter_const_mul (i : ℕ) (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
    funext z θ
    show z * deriv (fun z' => c * Work.Spaces.DzIter i g z' θ) z
      = c * (z * deriv (fun z' => Work.Spaces.DzIter i g z' θ) z)
    rw [deriv_const_mul']
    ring

/-- `D_θ^i` commutes with multiplication by a constant. -/
theorem DthIter_const_mul (i : ℕ) (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
    funext z θ
    show Real.sin (2 * θ) * deriv (fun θ' => c * Work.Spaces.DthIter i g z θ') θ
      = c * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i g z θ') θ)
    rw [deriv_const_mul']
    ring

/-- The mixed operators `D_z^j D_θ^i` commute with multiplication by a constant. -/
theorem mixed_const_mul (j i : ℕ) (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.mixed j i g z θ := by
  simp only [Work.Spaces.mixed]
  rw [DthIter_const_mul i c g, DzIter_const_mul j c (Work.Spaces.DthIter i g)]

/-- **The `ℋ⁴`-integrand is `2`-homogeneous under scalar multiplication**: `D_z`, `D_θ` commute
with multiplication by a constant, so every slot of the integrand is multiplied by `c²`.  The
identity is pointwise and needs no regularity (`deriv_const_mul'`). -/
theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  have hDza : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.DzIter i f z θ :=
    fun i => congrFun (congrFun (DzIter_const_mul i c f) z) θ
  have hmixa : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed j i f z θ :=
    fun j i => congrFun (congrFun (mixed_const_mul j i c f) z) θ
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  simp only [hDza, hmixa]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring

/-- **`HkSq` scales quadratically** (hence `HkNorm` by `|c|`): the pointwise identity
`HkIntegrand_const_mul` inside the two integrals, using that a constant factors out of the
Bochner integral. -/
theorem HkSq_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => c * f z θ) = c ^ 2 * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
      = c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => HkIntegrand_const_mul α k c f z θ)
  simp only [Work.Spaces.HkSq, Work.Spaces.Iz]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => hinner z),
    MeasureTheory.integral_const_mul]

/-- **The `ℋ⁴`-norm scales by `|c|`.**  (This replaces the interface clause `N4RegQ.smul`,
which asks for `RegQ` of the scaled function; the identity here is unconditional.) -/
theorem Xn_const_mul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => c * f z θ)
      = |c| * Work.FTS.Nonlin.Xn α f := by
  simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, HkSq_const_mul,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ c ^ 2)]
  rw [Real.sqrt_sq_eq_abs]




end RowsN0Aux

end Work.FTS.Nonlinear.Pieces
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

set_option autoImplicit false

/-! ## Elementary tools -/

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * |a| * |b| ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  calc |a * b| = |a| * |b| := abs_mul a b
    _ ≤ (|a| ^ 2 + |b| ^ 2) / 2 := by linarith
    _ = (a ^ 2 + b ^ 2) / 2 := by rw [sq_abs a, sq_abs b]

/-- `SmoothQuad` data are continuous on the open quadrant `(0,∞) × (0,π/2)`. -/
private lemma continuousOn_uncurry_of_smoothQuad_prv {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h := hsm
  rw [Work.FTS.LocData.SmoothQuad] at h
  refine h.continuousOn.mono (fun p hp => ?_)
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2⟩

/-- The angular slice `θ ↦ g(s,θ)` of a `SmoothQuad` datum is a.e. strongly measurable. -/
private lemma aesm_slice_of_smoothQuad {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_uncurry_of_smoothQuad_prv hsm) hs

/-- On the open quadrant, `g(s,θ)² ≤ HkIntegrand α 4 g s θ`: the `D_z⁰`-term of the integrand
is `(g · w/sin(2θ)^{η/2})²`, and `w ≥ 1`, `sin(2θ)^{η/2} ≤ 1` make the weight at least `1`. -/
private lemma sq_le_HkIntegrand_four (α : ℝ) (g : ℝ → ℝ → ℝ) {s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hSpos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hSle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsin.le (Real.sin_le_one _) (by have := Work.Spaces.eta_pos; linarith)
  have hw1 : 1 ≤ Work.Spaces.w s := Work.Elliptic.one_le_w hs
  set A : ℝ := Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hA
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ hSpos]
    linarith
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
  simp only [Work.Spaces.DzIter_zero] at hkey
  rw [← hA] at hkey
  calc (g s θ) ^ 2 = (g s θ) ^ 2 * 1 := by ring
    _ ≤ (g s θ) ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hA1]) (sq_nonneg _)
    _ = (g s θ * A) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := hkey

/-! ## The three integrability inputs -/

/-- The angular slice `θ ↦ F_*(s,θ)·K(θ)` is integrable on `Iθ`, for every `s`
(continuity on the compact `Iθ`: `Γ(θ) = (sinθcos²θ)^{α/3}` is continuous there for `α > 0`). -/
private lemma integrableOn_slice_Fstar_mul_K (α : ℝ) (hα : 0 < α) (s : ℝ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Construction.Fstar α s θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have hGam : ContinuousOn (fun θ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.Gam
    intro θ _
    exact (Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))).comp_continuousWithinAt
      (by fun_prop)
  have hF : ContinuousOn (fun θ => Work.Construction.Fstar α s θ) Work.Spaces.Iθ := by
    simp only [Work.Construction.Fstar]
    exact ((continuousOn_const.mul (hGam.div_const (Work.Spaces.c α))).mul continuousOn_const)
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.K; fun_prop
  exact hF.mul hK

/-- For `s > 0` the square slice `θ ↦ g(s,θ)²` is integrable on `Iθ`, from `SmoothQuad g` and
`HkMem α 4 g` alone (no continuity at the angular boundary is available for `SmoothQuad` data). -/
private lemma integrableOn_sq_slice_of_HkMem (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ := by
  refine (hmem.1 s hs.le).mono' ((aesm_slice_of_smoothQuad hsm hs).pow 2) ?_
  filter_upwards [Work.Elliptic.ae_restrict_Iθ_of_Ioo
    (fun θ h0 h1 => sq_le_HkIntegrand_four α g hs h0 h1)] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hθ

/-- For `s > 0` the angular slice `θ ↦ K(θ)·g(s,θ)` is integrable on `Iθ`: `K` is bounded, so
the product is dominated by `(K² + g(s,·)²)/2`. -/
private lemma integrableOn_slice_K_mul_g (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * g s θ) Work.Spaces.Iθ := by
  have hKcont : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K; fun_prop
  have hKsq : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.K θ) ^ 2) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hKcont.continuousOn.pow 2)
  have hsq := integrableOn_sq_slice_of_HkMem α g hsm hmem hs
  have hmaj : MeasureTheory.Integrable
      (fun θ => ((Work.Spaces.K θ) ^ 2 + (g s θ) ^ 2) / 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((show MeasureTheory.Integrable
        (fun θ => (Work.Spaces.K θ) ^ 2 + (g s θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from hKsq.add hsq)).div_const 2
  refine hmaj.mono' ?_ ?_
  · exact (hKcont.aestronglyMeasurable.restrict).mul (aesm_slice_of_smoothQuad hsm hs)
  · filter_upwards with θ
    rw [Real.norm_eq_abs]
    exact abs_mul_le_half_sq (Work.Spaces.K θ) (g s θ)

/-- For `s > 0` the slice `θ ↦ K(θ)·g(s,θ)/s` is integrable on `Iθ`. -/
private lemma integrableOn_slice_g (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * g s θ / s) Work.Spaces.Iθ :=
  (integrableOn_slice_K_mul_g α g hsm hmem hs).div_const s

/-- `F_*(s)/s = 2 (1+s)^{-2}` for `s > 0` — the elementary form of the model density. -/
private lemma Fstar_div_self_eq (s : ℝ) (hs : 0 < s) :
    Work.FM.Fstar s / s = 2 * (s + 1) ^ (-2 : ℝ) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have h2 : (s + 1) ^ (-2 : ℝ) = 1 / (s + 1) ^ 2 := by
    simp only [Real.rpow_neg (le_of_lt hs1), Real.rpow_ofNat, one_div]
  rw [h2]
  unfold Work.FM.Fstar
  field_simp
  ring

/-- The `L₁₂`-density of `F_*` is integrable on `(z,∞)` for `z ≥ 0`: pointwise it is
`α·F_*(s)/s = 2α/(1+s)²`, and `s ↦ (1+s)^{-2}` is integrable on `(z,∞)` for `z > -1`. -/
private lemma integrableOn_L12dens_Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ}
    (hz : 0 ≤ z) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.Construction.Fstar α))
      (Set.Ioi z) := by
  have hA : MeasureTheory.IntegrableOn (fun s : ℝ => (s + 1) ^ (-2 : ℝ)) (Set.Ioi z) :=
    integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := z) (m := 1) (by norm_num) (by linarith)
  refine MeasureTheory.IntegrableOn.congr_fun (hA.const_mul (2 * α)) ?_ measurableSet_Ioi
  intro s hs
  rw [Work.Construction.L12dens_Fstar hα hα1 s, Fstar_div_self_eq s (lt_of_le_of_lt hz hs)]
  ring

/-! ## The main theorem -/

theorem L12FK_add_ge0 {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.Nonlin.GalClass α g) :
    (∀ z : ℝ, 0 ≤ z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z) ∧
    (∀ z : ℝ, 0 ≤ z → Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z) := by
  have hsq : Work.FTS.LocData.SmoothQuad g := hg.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    (Work.FTS.GalerkinFix.RegQ.regQ_mono hg.reg (by norm_num)).2.1
  have haxis := hg.axis
  constructor
  · -- additivity of `L₁₂`
    intro z hz
    have h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α s θ / s) Work.Spaces.Iθ :=
      fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s
    have h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * g s θ / s) Work.Spaces.Iθ :=
      fun s hs => integrableOn_slice_g α g hsq hmem4 (lt_of_le_of_lt hz hs)
    have h3 : MeasureTheory.IntegrableOn
        (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) (Set.Ioi z) :=
      integrableOn_L12dens_Fstar α hα hα1 hz
    have h4 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi z) := by
      have h0 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0) := by
        refine (Work.FTS.H2.L12densIntegrable α g hα hα1 hsq hmem4).congr_fun ?_ measurableSet_Ioi
        intro s _
        exact Work.FTS.H2.L12dens_eq_FM_K g s
      exact h0.mono_set (Set.Ioi_subset_Ioi hz)
    have key := (Work.FTS.LocData.L12_add_mul (c := 1) (a := Work.Construction.Fstar α) (b := g)
      (z := z) h1 h2 h3 h4).1
    exact key
  · -- additivity of the angular moment
    intro z hz
    have hFint : MeasureTheory.IntegrableOn
        (fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
      integrableOn_slice_Fstar_mul_K α hα z
    have hgint : MeasureTheory.IntegrableOn (fun θ => g z θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
      rcases eq_or_lt_of_le hz with h0 | hpos
      · subst h0
        refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero ?_
          measurableSet_Icc
        intro θ hθ
        show (0 : ℝ) = g 0 θ * Work.Spaces.K θ
        rw [(haxis θ hθ).1]
        ring
      · refine MeasureTheory.IntegrableOn.congr_fun
          (integrableOn_slice_K_mul_g α g hsq hmem4 hpos) ?_ measurableSet_Icc
        intro θ _
        ring
    have key : (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.Fstar α z θ + g z θ) * Work.Spaces.K θ)
        = (∫ θ in Work.Spaces.Iθ, Work.Construction.Fstar α z θ * Work.Spaces.K θ)
          + ∫ θ in Work.Spaces.Iθ, g z θ * Work.Spaces.K θ := by
      have hpt : (fun θ => (Work.Construction.Fstar α z θ + g z θ) * Work.Spaces.K θ)
          = fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ
              + g z θ * Work.Spaces.K θ := by
        funext θ; ring
      rw [hpt]
      exact MeasureTheory.integral_add hFint hgint
    simpa only [Work.Construction.FK, Work.Construction.Ftot] using key

end Work.FTS.Nonlinear.Pieces
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rows =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)
open Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Rows 1--7** of design §3.4: the `N₀`-block, with a single constant `K`. -/
structure N0Rows (IP : ℝ → Fn → Fn → ℝ) (α K : ℝ) (g Φs Φg : Fn) : Prop where
  /-- row 1: `|N₀₁+N₀₂|_{ℋ⁴} ≤ Kα²` (tex 1398--1402) -/
  r1 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2
  /-- row 2: `|N₀₃|_{ℋ⁴} ≤ Kα^{-1}X²` (tex 1404--1406) -/
  r2 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N03g α g)
    ≤ K * (α ^ (-(1 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  /-- row 3: `|N₀₄ᵃ|_{ℋ⁴} ≤ K√α X` (tex 1410--1412) -/
  r3 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04aF α g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  /-- row 4: `|(N₀₄ᵇ, g)| ≤ Kα^{-3/2}X³` (tex 1414) -/
  r4 : |IP α (Work.FTS.Nonlin.N04bF α g) g|
    ≤ K * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  /-- row 5: `|N₀₅ᵃ|_{ℋ⁴} ≤ K√α X` (tex 1416--1418) -/
  r5 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  /-- row 6: `|(N₀₅ᵇ, g)| ≤ Kα^{-1/2}X³` (tex 1419) -/
  r6 : |IP α (Work.FTS.Nonlin.N05bF α g) g|
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  /-- row 7: `|(N₀₆, g)| ≤ K√α X²` (tex 1421--1423) -/
  r7 : |IP α (Work.FTS.Nonlin.N06F α g) g|
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)

/-- **Rows 8--26** of design §3.4: the `N`-block (the four-way split of `N₁, …, N₅`). -/
structure NRows (IP : ℝ → Fn → Fn → ℝ) (α K : ℝ) (g Φs Φg : Fn) : Prop where
  r8 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg)
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  r9 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gs α g Φg)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r10 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r11 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2
  r12 : |IP α (Work.FTS.Nonlin.N2gg α g Φg) g|
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  r13 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
    ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r14 : |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)
  r15 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2
  r16 : |IP α (Work.FTS.Nonlin.N3gg α g Φg) g|
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 3)
  r17 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
    ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r18 : |IP α (Work.FTS.Nonlin.N3sg α Φs g) g|
    ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2)
  r19 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3
  r20 : |IP α (Work.FTS.Nonlin.N4gg α g) g|
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  r21 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
    ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r22 : |IP α (Work.FTS.Nonlin.N4sg α g) g|
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)
  r23 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * α ^ 3
  r24 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g) ≤ K * Work.FTS.Nonlin.Xn α g ^ 2
  r25 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g)
      + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r26 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ K * α ^ 2

/-- **The auxiliary rows**: the `ℋ⁴`-bound of `AK` (`rak`) and the three zero-mode estimates
`rl0`--`rl2` of design §3.5 (`L-N4.6`), with a single constant `K`. -/
structure AuxRows (IP : ℝ → Fn → Fn → ℝ) (α K : ℝ) (g Φs Φg : Fn) : Prop where
  /-- the `ℋ⁴`-bound of `AK` (design §3.2) -/
  rak : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ K
  /-- `L-N4.6`: `|L₁₂(N₀)(0)| ≤ K(α² + √α X + α^{-3/2}X²)` -/
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  /-- `L-N4.6`: `|L₁₂(N)(0)| ≤ K(α² + √α X + α^{-3/2}X²)` -/
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  /-- `L-N4.6`: `|L₁₂(3D_θg/(1+z))(0)| ≤ K X` (tex 1517--1521) -/
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
    ≤ K * Work.FTS.Nonlin.Xn α g

/-! ## The glue -/


end Work.FTS.Nonlinear.Pieces
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.LintEngine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-! ## Pointwise facts -/

theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hc2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * |Real.sin θ| * |Real.cos θ ^ 2| ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hc2 (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

theorem abs_sin_two_mul_deriv_Gam_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 4 * α / 3 := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero, zero_mul, abs_zero]
    positivity
  rcases lt_or_eq_of_le hθ.2 with h1 | h1
  · have h := Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩
    rw [Work.Spaces.dthU] at h
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
      rw [Work.Spaces.qfun, abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
    rw [h, abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hG0]
    calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ α * (4 / 3) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hq hα.le) hG1 hG0 (by positivity)
      _ = 4 * α / 3 := by ring
  · rw [h1, show 2 * (π / 2) = π from by ring, Real.sin_pi, zero_mul, abs_zero]
    positivity

theorem abs_K_mul_deriv_Gam_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
  have hK : Work.Spaces.K θ = (3 / 2) * Real.cos θ * Real.sin (2 * θ) := by
    rw [Work.Spaces.K, Real.sin_two_mul]; ring
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h2 := abs_sin_two_mul_deriv_Gam_le hα hθ
  rw [hK,
    show (3 / 2) * Real.cos θ * Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
        = (3 / 2) * Real.cos θ
            * (Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ) from by ring,
    abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  calc (3 / 2) * |Real.cos θ|
        * |Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ|
      ≤ (3 / 2) * 1 * (4 * α / 3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcos (by norm_num)) h2 (abs_nonneg _) (by norm_num)
    _ = 2 * α := by ring

/-- **The pointwise size of `F_*` and `D_zF_*`.** -/
theorem FstarPt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α z θ| ≤ 20 * α * (z / (1 + z) ^ 2) ∧
    |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 40 * α * (z / (1 + z) ^ 2) := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  have hzc : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have hGc : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hc0]; nlinarith
  have hGcnn : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hG0 hc0.le
  constructor
  · rw [Work.Construction.Fstar, Work.FM.Fstar,
      abs_of_nonneg (mul_nonneg (mul_nonneg hα.le hGcnn) (by positivity))]
    calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2)
        ≤ α * 10 * (2 * z / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGc hα.le) (by positivity)
      _ = 20 * α * (z / (1 + z) ^ 2) := by ring
  · have heq : (fun z' => Work.Construction.Fstar α z' θ)
        = fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z' := by
      funext z'
      rw [Work.Construction.Fstar]
    have hder : deriv (fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
          * Work.FM.Fstar z') z
        = (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * (2 * (1 - z) / (1 + z) ^ 3) :=
      ((Work.FM.hasDerivAt_Fstar z (by linarith)).const_mul
        (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))).deriv
    have hfac : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * deriv Work.FM.Fstar z := by
      rw [Work.Spaces.Dz, Work.Spaces.pz, heq, hder, Work.FM.deriv_Fstar z (by linarith)]
      ring
    have hd : |deriv Work.FM.Fstar z| ≤ 2 / (1 + z) ^ 2 := by
      rw [Work.FM.deriv_Fstar z (by linarith)]
      have h1 : |1 - z| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ 3), div_le_iff₀ (by positivity)]
      calc 2 * |1 - z| ≤ 2 * (1 + z) := by linarith
        _ = 2 / (1 + z) ^ 2 * (1 + z) ^ 3 := by first | (field_simp; ring) | field_simp | ring
    have h1 : |α * (Work.Spaces.Gam α θ / Work.Spaces.c α)| ≤ 10 * α := by
      rw [abs_mul, abs_of_pos hα, abs_of_nonneg hGcnn]
      calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) ≤ α * 10 :=
            mul_le_mul_of_nonneg_left hGc hα.le
        _ = 10 * α := by ring
    rw [hfac, abs_mul, abs_mul, abs_of_nonneg hz]
    calc z * |α * (Work.Spaces.Gam α θ / Work.Spaces.c α)| * |deriv Work.FM.Fstar z|
        ≤ z * (10 * α) * (2 / (1 + z) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hz) hd (abs_nonneg _) (by positivity)
      _ = 20 * α * (z / (1 + z) ^ 2) := by first | (field_simp; ring) | field_simp | ring
      _ ≤ 40 * α * (z / (1 + z) ^ 2) := by
          have h : 0 ≤ α * (z / (1 + z) ^ 2) := mul_nonneg hα.le hzc
          nlinarith [h]

/-! ## The measure-theoretic engines -/

/-- An angular bound which is constant in `θ` integrates to `ofReal (2 D)`. -/
theorem inner_le_const {g : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g θ ≤ D) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (g θ)) ≤ ENNReal.ofReal (2 * D) := by
  have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (g θ))
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal D :=
    MeasureTheory.lintegral_mono_ae (h.mono fun θ hθ => ENNReal.ofReal_le_ofReal hθ)
  refine h1.trans ?_
  rw [MeasureTheory.setLIntegral_const, Work.Spaces.Iθ, Real.volume_Icc,
    show (π / 2 - 0 : ℝ) = π / 2 by ring, ← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_le_four])


/-- The radial weight `r⁻¹` against a bound `C·r/(1+r)²`: the product is `C/(1+r)²`,
whose integral over `(0,∞)` is at most `2` (`Work.FTS.H2.InvOneAddSq`). -/
theorem outer_le {C : ℝ} (hC : 0 ≤ C) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * r / (1 + r) ^ 2))
      ≤ ENNReal.ofReal (2 * C) := by
  obtain ⟨hint, hle⟩ := Work.FTS.H2.InvOneAddSq
  have hcongr : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * r / (1 + r) ^ 2)
        = ENNReal.ofReal C * ENNReal.ofReal ((1 / (1 + r)) ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hrw : r⁻¹ * (C * r / (1 + r) ^ 2) = C * (1 / (1 + r)) ^ 2 := by
      field_simp
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le), ← ENNReal.ofReal_mul hC, hrw]
  rw [MeasureTheory.lintegral_congr_ae hcongr]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hkey : ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 / (1 + r)) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun r => by positivity)
  rw [← hkey]
  calc ENNReal.ofReal C * ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
      ≤ ENNReal.ofReal C * ENNReal.ofReal 2 :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle)
          (show (0 : ENNReal) ≤ ENNReal.ofReal C from bot_le)
    _ = ENNReal.ofReal (2 * C) := by rw [← ENNReal.ofReal_mul hC]; ring_nf

/-- The radial weight `r⁻¹` against a bound `C|ρ r| r/(1+r)²`, where `ρ` is only known
through its weighted `L¹`-bound `∫ |ρ|/(1+r)² ≤ 2X` and the integrability of that
function. -/
theorem outer_le_radial {ρ : ℝ → ℝ} {X C : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hint : MeasureTheory.IntegrableOn (fun z => |ρ z| / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)))
    (hle : (∫ z in Set.Ioi (0 : ℝ), |ρ z| / (1 + z) ^ 2) ≤ 2 * X) :
    (∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * |ρ r| * r / (1 + r) ^ 2))
      ≤ ENNReal.ofReal (4 * C * X) := by
  have hcongr : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * |ρ r| * r / (1 + r) ^ 2)
        = ENNReal.ofReal C * ENNReal.ofReal (|ρ r| / (1 + r) ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hrw : r⁻¹ * (C * |ρ r| * r / (1 + r) ^ 2) = C * (|ρ r| / (1 + r) ^ 2) := by
      field_simp
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le), ← ENNReal.ofReal_mul hC, hrw]
  rw [MeasureTheory.lintegral_congr_ae hcongr]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hkey : ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), |ρ z| / (1 + z) ^ 2)
      = ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (|ρ z| / (1 + z) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => by positivity)
  rw [← hkey]
  calc ENNReal.ofReal C * ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), |ρ z| / (1 + z) ^ 2)
      ≤ ENNReal.ofReal C * ENNReal.ofReal (2 * X) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle)
          (show (0 : ENNReal) ≤ ENNReal.ofReal C from bot_le)
    _ = ENNReal.ofReal (C * (2 * X)) := by rw [ENNReal.ofReal_mul hC]
    _ ≤ ENNReal.ofReal (4 * C * X) := ENNReal.ofReal_le_ofReal (by nlinarith)

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.splitsDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

/-! ## Differentiability of the slices of a `SmoothQuad` function -/

/-- The `z`-slice of a `SmoothQuad` function is differentiable at every `z > -1`, at every
`θ ∈ (0, π/2)`. -/
theorem differentiableAt_slice_z {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun z' => f z' θ) z :=
  (((hf.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds hz))

/-- The `θ`-slice of a `SmoothQuad` function is differentiable at every `θ ∈ (0, π/2)`, at every
`z > -1`. -/
theorem differentiableAt_slice_θ {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ :=
  (((hf.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioo.mem_nhds hθ))

/-- `∂_θ` is additive on the sum of two functions whose `θ`-slices are differentiable. -/
theorem pth_add_of_diff {f h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hh : DifferentiableAt ℝ (fun θ' => h z θ') θ) :
    Work.Spaces.pth (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pth f z θ + Work.Spaces.pth h z θ := by
  simp only [Work.Spaces.pth]
  rw [show (fun θ' => f z θ' + h z θ') = (fun θ' => f z θ') + (fun θ' => h z θ') from rfl,
    deriv_add hf hh]

/-- `∂_z` is additive on the sum of two functions whose `z`-slices are differentiable. -/
theorem pz_add_of_diff {f h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hh : DifferentiableAt ℝ (fun z' => h z' θ) z) :
    Work.Spaces.pz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz h z θ := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => f z' θ + h z' θ) = (fun z' => f z' θ) + (fun z' => h z' θ) from rfl,
    deriv_add hf hh]

/-- `∂_θ` is additive on a sum of `SmoothQuad` functions (on the quadrant). -/
theorem pth_add_of_smoothQuad {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    (hh : Work.FTS.LocData.SmoothQuad h) {z θ : ℝ} (hz : z ∈ Set.Ioi (-1 : ℝ))
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pth (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pth f z θ + Work.Spaces.pth h z θ :=
  pth_add_of_diff (differentiableAt_slice_θ hf hz hθ) (differentiableAt_slice_θ hh hz hθ)

/-- `∂_z` is additive on a sum of `SmoothQuad` functions (on the quadrant). -/
theorem pz_add_of_smoothQuad {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    (hh : Work.FTS.LocData.SmoothQuad h) {z θ : ℝ} (hz : z ∈ Set.Ioi (-1 : ℝ))
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz h z θ :=
  pz_add_of_diff (differentiableAt_slice_z hf hz hθ) (differentiableAt_slice_z hh hz hθ)

/-- `D_z = z ∂_z` is additive as soon as `∂_z` is. -/
theorem Dz_add_of_diff {f h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpz : Work.Spaces.pz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz h z θ) :
    Work.Spaces.Dz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.Dz f z θ + Work.Spaces.Dz h z θ := by
  simp only [Work.Spaces.Dz, hpz]; ring

/-- `D_θ f = s2 θ · ∂_θ f` (the `sin (2θ)` of `Construction.s2`). -/
theorem Dth_eq_s2_mul (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.Dth f z θ = Work.Construction.s2 θ * Work.Spaces.pth f z θ := rfl

/-! ## The derivative of `z ↦ L₁₂(F_*)` -/

/-- `z ↦ L₁₂(F_*)(z) = 2α/(1+z)` is differentiable at every `z > 0`. -/
theorem differentiableAt_L12_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ}
    (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z := by
  have hev : (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z')
      =ᶠ[𝓝 z] (fun z' => 2 * α / (1 + z')) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.Construction.L12_Fstar_eq hα hα1 hz'.le
  exact (Filter.EventuallyEq.differentiableAt_iff hev).mpr
    ((differentiableAt_const (2 * α)).div
      ((differentiableAt_const (1 : ℝ)).add differentiableAt_id) (by intro h; linarith))

/-! ## Additivity of `ℛ`, `U`, `V` in their argument -/

/-- `ℛ` is additive in its argument, provided `∂_z` and `∂_θ` are additive for the pair. -/
theorem Rop_add_of_diff {α : ℝ} {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpz : Work.Spaces.pz (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pz Ψ₁ z θ + Work.Spaces.pz Ψ₂ z θ)
    (hpth : Work.Spaces.pth (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pth Ψ₁ z θ + Work.Spaces.pth Ψ₂ z θ) :
    Work.Construction.Rop α (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Construction.Rop α Ψ₁ z θ + Work.Construction.Rop α Ψ₂ z θ := by
  simp only [Work.Construction.Rop, hpz, hpth]
  ring

/-- `U` is additive in its argument. -/
theorem Uop_add_of_diff {α : ℝ} {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpz : Work.Spaces.pz (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pz Ψ₁ z θ + Work.Spaces.pz Ψ₂ z θ) :
    Work.Construction.Uop α (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Construction.Uop α Ψ₁ z θ + Work.Construction.Uop α Ψ₂ z θ := by
  simp only [Work.Construction.Uop, hpz]
  ring

/-- `V` is additive in its argument. -/
theorem Vop_add_of_diff {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpth : Work.Spaces.pth (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pth Ψ₁ z θ + Work.Spaces.pth Ψ₂ z θ) :
    Work.Construction.Vop (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Construction.Vop Ψ₁ z θ + Work.Construction.Vop Ψ₂ z θ := by
  simp only [Work.Construction.Vop, hpth]
  ring

/-! ## The corrected splits -/


/-! ## What the split really needs

The three lemmas below compute the *difference* between an operator applied to the sum `Ψ` of the
two straightened stream functions and the sum of the operators applied to the two pieces.  They
are pure algebra (no additivity is assumed!), and they are what shows that the four-way split of
`N` is equivalent to the additivity of `∂_z` on `Φ̃_*` and `Φ̃_g`. -/





end Work.FTS.Nonlinear.Pieces
end
end
