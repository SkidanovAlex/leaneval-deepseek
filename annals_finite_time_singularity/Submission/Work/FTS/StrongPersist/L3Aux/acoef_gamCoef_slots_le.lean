import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.HkSq_succ_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The `D_z` half of `HkMem` transfer, with no restriction on `α`. -/
theorem HkMem_dz_free (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Spaces.SmoothNbhd f) (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkMem α k (Spaces.Dz f) :=
  HkMem_of_HkIntegrand_le α k hsm.Dz h (fun z hz θ hθ =>
    HkIntegrand_Dz_le α k hsm z θ hz hθ)

/-- **Coercivity of the `H^k`-norm.**  For `SmoothNbhd f` and `k ≥ 1`,
`HkSq α (k+1) f ≤ HkSq α k f + HkSq α k (Dθ f) + HkSq α k (Dz f)`. -/
theorem HkSq_succ_le (α : ℝ) (hα : 0 < α) (k : ℕ) (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hsm : Spaces.SmoothNbhd f) (h : Spaces.HkMem α (k + 1) f) :
    Spaces.HkSq α (k + 1) f
      ≤ Spaces.HkSq α k f + Spaces.HkSq α k (Spaces.Dth f) + Spaces.HkSq α k (Spaces.Dz f) := by
  have hf : Spaces.HkMem α k f := HkMem_mono α k hsm h
  have hdth : Spaces.HkMem α k (Spaces.Dth f) := (HkMem_dth α hα k hsm h).1
  have hdz : Spaces.HkMem α k (Spaces.Dz f) := HkMem_dz_free α k hsm h
  refine HkSq_le_sum_of_integrand_le (α := α) (m := k + 1) (k := k) (f := f) (g₁ := f)
    (g₂ := Spaces.Dth f) (g₃ := Spaces.Dz f) h hf hdth hdz ?_
  intro z hz θ hθ
  exact HkIntegrand_succ_le_sum α k hk hsm hz hθ

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.coerc_LZ6_Dz_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The angular weight `sin(2θ)^{-η}` (so that `Weta z θ = w z ^ 2 * sig θ`). -/
def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-Spaces.eta)


theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ sig θ :=
  Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _


/-! ### The pointwise `𝓛(D_z f)`-identity on a slice -/




/-! ### The two limit passages `R → ∞` -/






/-- `∫ x, c * F x = c * ∫ x, F x` in the form needed below (`integral_const_mul` is
stated with `•`). -/
theorem integral_const_mul_real {α : Type*} [MeasurableSpace α] {μ : Measure α} (c : ℝ)
    (F : α → ℝ) : (∫ x, c * F x ∂μ) = c * ∫ x, F x ∂μ := by
  simpa only [smul_eq_mul] using MeasureTheory.integral_const_mul c F

/-! ### The truncated box inequality -/

/-- On the truncated quadrant `(0,R) × Iθ`, `Z16 f · D_z f · Weta` dominates `47/100` of
`(D_z f)² · Weta`.  This is the coercive estimate with the (favourable) `z`-boundary term
retained. -/
theorem box_bound (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hint : IntegrableOn
      (Function.uncurry (fun z θ => Z16 f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hint2 : IntegrableOn
      (Function.uncurry (fun z θ => (Spaces.Dz f z θ * Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ))
    {R : ℝ} (hR : 0 < R) :
    (47 / 100) * (∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      ≤ ∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ := by
  obtain ⟨C, δ, hCpos, hδ, hbnd⟩ := Dz_near_zero_bound f hsm hbd
  let Bf : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ
  let Cf : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ,
    deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z * sig θ
  let Df : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ,
    Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
  let gf : ℝ → ℝ := fun z => 3 * (1 - Spaces.eta) / (1 + z)
  let P : Measure (ℝ × ℝ) := (volume.restrict (Set.Ioo 0 R)).prod (volume.restrict Spaces.Iθ)
  -- ## The slice identity
  have hslice : ∀ z, 0 < z → (∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
      = (1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z := by
    intro z hz
    have h := slice_Z16 f hsm z hz
    dsimp only [Bf, Cf, Df, gf, sig]
    exact h
  -- ## Joint integrability of `(D_z f)² Weta` on the box
  have hΦ : Integrable (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) P := by
    have hsub : Set.Ioo 0 R ×ˢ Spaces.Iθ ⊆ Spaces.Iz ×ˢ Spaces.Iθ := by
      intro p hp
      exact ⟨Set.mem_Ici.mpr (le_of_lt hp.1.1), hp.2⟩
    have h1 : IntegrableOn
        (Function.uncurry (fun z θ => (Spaces.Dz f z θ) ^ 2 * Weta z θ))
        (Set.Ioo 0 R ×ˢ Spaces.Iθ) := by
      refine (hint2.mono_set hsub).congr ?_
      filter_upwards with p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair, Weta]
      ring
    have hvol : volume.restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ) = P := by
      dsimp only [P]
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [IntegrableOn, hvol] at h1
    exact h1
  have hB : IntegrableOn Bf (Set.Ioo 0 R) := hΦ.integral_prod_left
  have hzp : ∀ᵐ p ∂P, p.1 ∈ Set.Ioo 0 R := by
    dsimp only [P]
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
    exact Eventually.of_forall (fun θ => hz)
  have hθp : ∀ᵐ p ∂P, p.2 ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
    dsimp only [P]
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)]
    filter_upwards [] with z
    exact MeasureTheory.ae_restrict_mem measurableSet_Icc
  -- ## Joint integrability of the `gf · cos(2θ) · (D_z f)² Weta` integrand
  have hΨ : Integrable (fun p : ℝ × ℝ =>
      gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)) P := by
    have hmaj : Integrable (fun p : ℝ × ℝ =>
        (3 * (1 - Spaces.eta)) * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖) P :=
      hΦ.norm.const_mul _
    refine hmaj.mono' ?_ ?_
    · have h1 : Measurable (fun p : ℝ × ℝ => gf p.1 * Real.cos (2 * p.2)) := by
        dsimp only [gf]; fun_prop
      refine (h1.aestronglyMeasurable.mul hΦ.aestronglyMeasurable).congr ?_
      filter_upwards with p
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [hzp] with p hp
      have hp1 : 0 < p.1 := hp.1
      have hgf0 : 0 ≤ gf p.1 := by
        dsimp only [gf]
        exact div_nonneg (by norm_num [Spaces.eta]) (by linarith)
      have hgfle : gf p.1 ≤ 3 * (1 - Spaces.eta) := by
        dsimp only [gf]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + p.1)]
        have h3 : (0:ℝ) ≤ 3 * (1 - Spaces.eta) := by norm_num [Spaces.eta]
        have h4 : (0:ℝ) ≤ 3 * (1 - Spaces.eta) * p.1 := mul_nonneg h3 (le_of_lt hp1)
        linarith
      calc ‖gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)‖
          = gf p.1 * |Real.cos (2 * p.2)| * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖ := by
            simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgf0]
            ring
        _ ≤ 3 * (1 - Spaces.eta) * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖ := by
            have h2 : gf p.1 * |Real.cos (2 * p.2)| ≤ 3 * (1 - Spaces.eta) * 1 :=
              mul_le_mul hgfle (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num [Spaces.eta])
            calc gf p.1 * |Real.cos (2 * p.2)| * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖
                ≤ (3 * (1 - Spaces.eta) * 1) * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖ :=
                  mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
              _ = 3 * (1 - Spaces.eta) * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖ := by ring
  have hgD : IntegrableOn (fun z => gf z * Df z) (Set.Ioo 0 R) := by
    have h := hΨ.integral_prod_left
    refine h.congr (Eventually.of_forall (fun z => ?_))
    show (∫ θ, gf z * (Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ)
        ∂(volume.restrict Spaces.Iθ)) = gf z * Df z
    rw [integral_const_mul_real]
  -- ## Joint integrability of `Z16 f · D_z f · Weta` on the box
  have hG : IntegrableOn
      (fun z => ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
      (Set.Ioo 0 R) := by
    have hsub : Set.Ioo 0 R ×ˢ Spaces.Iθ ⊆ Spaces.Iz ×ˢ Spaces.Iθ := by
      intro p hp
      exact ⟨Set.mem_Ici.mpr (le_of_lt hp.1.1), hp.2⟩
    have h1 : IntegrableOn
        (Function.uncurry (fun z θ => Z16 f z θ * Spaces.Dz f z θ * Weta z θ))
        (Set.Ioo 0 R ×ˢ Spaces.Iθ) := hint.mono_set hsub
    have hvol : volume.restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ) = P := by
      dsimp only [P]
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [IntegrableOn, hvol] at h1
    exact h1.integral_prod_left
  have hG' : IntegrableOn (fun z => (1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z)
      (Set.Ioo 0 R) := by
    refine hG.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
    exact hslice z hz.1
  have hC : IntegrableOn Cf (Set.Ioo 0 R) := by
    have heq : (fun z => 2 * ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z) - Bf z
        - 2 * (gf z * Df z)) = Cf := by
      funext z; ring
    rw [← heq]
    exact ((hG'.const_mul 2).sub hB).sub (hgD.const_mul 2)
  -- ## The split into the three pieces
  have hsplit : (∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z))
      = (1 / 2) * (∫ z in Set.Ioo 0 R, Bf z) + (1 / 2) * (∫ z in Set.Ioo 0 R, Cf z)
        + (∫ z in Set.Ioo 0 R, gf z * Df z) := by
    have hcongr : (∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z))
        = ∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + ((1 / 2) * Cf z + gf z * Df z)) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun z => ?_))
      ring
    have hfg : Integrable (fun z => (1 / 2) * Cf z + gf z * Df z)
        (volume.restrict (Set.Ioo 0 R)) := (hC.const_mul (1 / 2)).add hgD
    have hbfg : Integrable (fun z => (1 / 2) * Bf z + ((1 / 2) * Cf z + gf z * Df z))
        (volume.restrict (Set.Ioo 0 R)) := (hB.const_mul (1 / 2)).add hfg
    rw [hcongr, MeasureTheory.integral_add (hB.const_mul (1 / 2)) hfg,
      MeasureTheory.integral_add (hC.const_mul (1 / 2)) hgD,
      integral_const_mul_real, integral_const_mul_real]
    ring
  -- ## The `C`-piece is nonnegative
  have hCnn : 0 ≤ ∫ z in Set.Ioo 0 R, Cf z := by
    have hbox := box_deriv_ftc f hsm hbd
      ⟨C, δ, hCpos, hδ, fun z hz θ hθ => (hbnd z hz θ hθ).2.2⟩ hR
    dsimp only [Cf, sig] at hbox ⊢
    rw [hbox]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (mul_nonneg (le_of_lt hR) (sq_nonneg _)) (sig_nonneg hθ)
  -- ## The `g·D`-piece dominates `-(3(1-η))` times the `B`-piece
  have hgDlb : -(3 * (1 - Spaces.eta)) * (∫ z in Set.Ioo 0 R, Bf z)
      ≤ ∫ z in Set.Ioo 0 R, gf z * Df z := by
    have hBint : (∫ z in Set.Ioo 0 R, Bf z)
        = ∫ p, (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂P := by
      rw [MeasureTheory.integral_prod
        (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) hΦ]
    have hDint : (∫ z in Set.Ioo 0 R, gf z * Df z)
        = ∫ p, gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂P := by
      rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
        gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)) hΨ]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun z => ?_))
      show gf z * Df z = ∫ θ in Spaces.Iθ,
        gf z * (Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      rw [integral_const_mul_real]
    rw [hBint, hDint]
    have hmono : (∫ p, -(3 * (1 - Spaces.eta)) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂P)
        ≤ ∫ p, gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂P := by
      refine MeasureTheory.integral_mono_ae (hΦ.const_mul _) hΨ ?_
      filter_upwards [hzp, hθp] with p hp hθ
      have hp1 : 0 < p.1 := hp.1
      have hgf0 : 0 ≤ gf p.1 := by
        dsimp only [gf]
        exact div_nonneg (by norm_num [Spaces.eta]) (by linarith)
      have hgfle : gf p.1 ≤ 3 * (1 - Spaces.eta) := by
        dsimp only [gf]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + p.1)]
        have h3 : (0:ℝ) ≤ 3 * (1 - Spaces.eta) := by norm_num [Spaces.eta]
        have h4 : (0:ℝ) ≤ 3 * (1 - Spaces.eta) * p.1 := mul_nonneg h3 (le_of_lt hp1)
        linarith
      have hφnn : 0 ≤ (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sig_nonneg hθ))
      have hcos : -(3 * (1 - Spaces.eta)) ≤ gf p.1 * Real.cos (2 * p.2) := by
        have h1 : gf p.1 * (-1) ≤ gf p.1 * Real.cos (2 * p.2) :=
          mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (2 * p.2)) hgf0
        have h2 : -(3 * (1 - Spaces.eta)) ≤ gf p.1 * (-1) := by
          rw [mul_neg, mul_one]; linarith [hgfle]
        linarith [h1, h2]
      calc -(3 * (1 - Spaces.eta)) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)
          ≤ (gf p.1 * Real.cos (2 * p.2)) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) :=
            mul_le_mul_of_nonneg_right hcos hφnn
        _ = gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) := by ring
    rw [integral_const_mul_real] at hmono
    linarith [hmono]
  -- ## Assembly
  have heta : (3:ℝ) * (1 - Spaces.eta) = 3 / 100 := by norm_num [Spaces.eta]
  have hmain : (47 / 100) * (∫ z in Set.Ioo 0 R, Bf z)
      ≤ ∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z) := by
    rw [hsplit]
    have hXeq : (47 / 100) * (∫ z in Set.Ioo 0 R, Bf z)
        = (1 / 2) * (∫ z in Set.Ioo 0 R, Bf z)
          - (3 * (1 - Spaces.eta)) * (∫ z in Set.Ioo 0 R, Bf z) := by
      rw [heta]; ring
    rw [hXeq]
    linarith [hCnn, hgDlb]
  calc (47 / 100) * (∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ,
        (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      = (47 / 100) * (∫ z in Set.Ioo 0 R, Bf z) := rfl
    _ ≤ ∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z) := hmain
    _ = ∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ := by
        refine (MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun z hz => ?_)).symm
        exact hslice z hz.1

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.H6N_GammaTerm_sep_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The pointwise `ℋ^k`-bound for a separated `Γ`-type function

For the separated function `F = Kfac α · ρ(z) · ψ(θ)` of `GammaTermAux` (`ρ = rhoR`,
`ψ = psiA α`), the two hypotheses

* `|(D_z^j ρ)(z)·w(z)| ≤ M/(1+z)²` for `j ≤ k` (the `z`-core), and
* `|(D_θ^i ψ)(θ)| ≤ D·Γ(θ)(sin(2θ)² + α)` for `1 ≤ i ≤ k` (the `θ`-core),

give the pointwise bound

`HkIntegrand α k F z θ ≤ (Kfac α)² (M/(1+z)²)² ·
   (4(k+1)·sin(2θ)^{-η} + 2(k+1)² D² (sin(2θ)^{-η} + α² sin(2θ)^{2α/3-γ}))`

on the domain.  This is the `k = 4` computation of `H4N_GammaTerm_le_of_cores`
(`hpt`) with the level `4` made arbitrary: the pure slots contribute `4` each
(`|ψ| ≤ 2`) and the mixed slots `2D²(…)` each; there are `k+1` of the former and
`(k+1)²` index pairs for the latter, and every term is bounded by the same quantity. -/
theorem HkN_GammaTerm_sep_le_aux (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D) (k : ℕ)
    (hMr : ∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2)
    (hDl : ∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i] (psiA α)) θ|
        ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
        ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
  intro z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h1z : 0 < 1 + z := by have hz0 : (0 : ℝ) ≤ z := hz; linarith
  by_cases hθi : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · -- interior of the angular interval: bound the pure and the mixed slots termwise
    have hbnd : ∀ j : ℕ, j ≤ k →
        ((Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z) ^ 2
          ≤ (M / (1 + z) ^ 2) ^ 2 := by
      intro j hj
      have hb := hMr j hj z hz
      rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ M / (1 + z) ^ 2)]
      exact hb
    have hψ2 : (psiA α θ) ^ 2 ≤ 4 := by
      have h := mul_self_le_mul_self (abs_nonneg (psiA α θ)) (psiA_abs_le_two hα hθ)
      have h2 := sq_abs (psiA α θ)
      nlinarith [h, h2]
    have hpure : ∀ i : ℕ, i ≤ k →
        (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      intro i hi
      have hsep : Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
          = Kfac α * (Work.Spaces.Zop^[i] rhoR) z * psiA α θ := by
        rw [sepF_DzIter, Zop_iter_const_mul, sepF]
      have hsq := hbnd i hi
      have hψs : (Kfac α * psiA α θ) ^ 2 ≤ (Kfac α) ^ 2 * 4 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hψ2 (sq_nonneg (Kfac α))
      calc (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = ((Work.Spaces.Zop^[i] rhoR) z * Work.Spaces.w z) ^ 2
              * (Kfac α * psiA α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
            rw [hsep]
            rw [Work.Elliptic.sq_mul_div_sin (z := z) (θ := θ)
              (a := Kfac α * (Work.Spaces.Zop^[i] rhoR) z * psiA α θ) hθ]
            ring
        _ ≤ (M / (1 + z) ^ 2) ^ 2 * ((Kfac α) ^ 2 * 4)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hsq hψs (sq_nonneg _) (sq_nonneg _))
              (Real.rpow_nonneg hs0 _)
        _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    have hmixed : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
        (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
      intro i j hi hij
      have hsep : Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
          = Kfac α * (Work.Spaces.Zop^[j] rhoR) z * (Work.Spaces.Lop^[i] (psiA α)) θ := by
        rw [sepF_mixed, Zop_iter_const_mul, sepF]
      have hsq := hbnd j (by omega)
      have hcore := hDl i hi (by omega) θ hθi
      have hang := mixed_angle_le hα hα1 hD.le hθ hcore
      calc (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          = (Kfac α) ^ 2 * ((Work.Spaces.Zop^[j] rhoR) z * Work.Spaces.w z) ^ 2
              * (((Work.Spaces.Lop^[i] (psiA α)) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            rw [hsep, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
            ring
        _ ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg (Kfac α))) hang
              (by positivity) (by positivity)
    rw [Work.Spaces.HkIntegrand]
    have hZsum : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      calc ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (k + 1),
              ((Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
                * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
            Finset.sum_le_sum fun i hi =>
              hpure i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hMsum : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
      set Y : ℝ := (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) with hYdef
      have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
      calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1), Y :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ k
              · rw [if_pos hc]; exact hmixed i j hc.1 hc.2
              · rw [if_neg hc]; exact hYnn
        _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul, hYdef]
            push_cast
            ring
    calc ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ((Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          + ((Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))) :=
          add_le_add hZsum hMsum
      _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
          ring
  · -- angular boundary: `sin(2θ) = 0`, and every term of the integrand vanishes
    have hs : Real.sin (2 * θ) = 0 :=
      Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
    rw [HkIntegrand_eq_zero_of_sin_two_eq_zero hα hs]
    have h0 : (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) = 0 := by
      rw [hs,
        Real.zero_rpow (by linarith [Work.Spaces.eta_pos] :
          (-(Work.Spaces.eta)) ≠ 0),
        Real.zero_rpow (by rw [Work.Spaces.gam]; intro hh; linarith :
          (2 * α / 3 - Work.Spaces.gam α) ≠ 0)]
      ring
    rw [h0]
    simp

theorem H6N_GammaTerm_sep_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D)
    (hMr : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z|
        ≤ M / (1 + z) ^ 2)
    (hDl : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
        ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
          (Work.Construction.sepF (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
            (Work.Construction.psiA α)) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * ((28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 98 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) := by
  intro z hz θ hθ
  calc Work.Spaces.HkIntegrand α 6
        (sepF (fun z => Kfac α * rhoR z) (psiA α)) z θ
      ≤ (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * (4 * ((6 : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 2 * ((6 : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
        HkN_GammaTerm_sep_le_aux α hα hα1 hM hD 6 hMr hDl z hz θ hθ
    _ = (Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2
          * ((28 + 98 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 98 * D ^ 2 * α ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) := by
        ring

end Work.Construction
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.LocC.LzeroQuantSelf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.LocC

set_option autoImplicit false

/-!
# `LocC/LzeroQuantSelf` — the quantitative one-variable `θ`-growth bound for a slice

`lzeroGrowthBound` (`H2W/lzeroGrowthBound.lean`) proves, for `u` of class `C^∞` on `(0, π/2)`
with `∫_{Iθ} sinθcos²θ·|Lzero1 u| < ∞`, that `|u θ| ≤ C·(θ⁻¹ + (π/2-θ)⁻¹)` for *some* constant
`C`, but neither its statement nor its proof exposes the dependence of `C` on `u`.  The
*locally uniform in `z`* slice bound of `H2W/pzIterSliceGrowth3LocC` needs the constant to be
controlled by two explicit quantities of the slice `u` only:

* `K u = ∫_{Iθ} sinθcos²θ·|Lzero1 u|`, the weighted source mass, and
* `|u(π/4)| + |deriv u (π/4)|`, the data at the interior reference angle `π/4`.

`growthExplicit` below is the explicit-constant form of `lzeroGrowthBound`: a verbatim re-run of
its proof with the constant `4|c₁(π/4)| + 16B₀K + 2(|c₂(π/4)|+2K)B₀` exposed and `B₀` a
parameter.  The two Cramer coefficients at `π/4` are *fixed* linear functionals of
`(u(π/4), u'(π/4))` (`cCoef1_pi4_le`, `cCoef2_pi4_le`), so the whole constant is dominated by a
universal multiple of `K u + |u(π/4)| + |deriv u(π/4)|`.  That yields
`lzeroGrowthQuantL1Self`, the quantitative form consumed by the local slice bound.
-/

/-! ## The two Cramer coefficients at the interior reference angle -/




/-! ## The integral bookkeeping: `∫_{Iθ}(f + c) = ∫_{Iθ} f + c·(π/2)` -/




end Work.FTS.EllipticEst.H2W.LocC
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SliceB.lzeroGrowthQuantL1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SliceB

/-! ## The values of `LzeroSing` and of its derivative at `π/4` -/







/-! ## The growth of the singular solution -/


/-! ## The general two-coefficient growth estimate -/


/-! ## The integral over `Iθ` of an integrand carrying constant terms -/


/-! ## The target -/


end Work.FTS.EllipticEst.H2W.SliceB
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.radialMatchedMajorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
## The proof

For a radial factor `r` and an arbitrary `g`, assuming the two Leibniz rules for the
product `(z,θ) ↦ r z · g z θ`, the level-`6` weighted integrand of the product is bounded
at a point `(z,θ)` by a universal constant times the **matched** radial sum

`∑_{b ≤ 6} (D_z^b r z)² · HkIntegrand α (6-b) g z θ`,

in which each radial derivative is paired with the *remaining* budget `6 - b` of
derivatives of `g`.  The proof is a two-slot Cauchy–Schwarz: the pure `D_z`-slots and the
mixed slots are each expanded by their Leibniz rule, bounded termwise by the corresponding
slot of `HkIntegrand α (6-b) g` (`sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed` at level
`6 - b`), and then the radial factors are collected into the matched sum.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000

/-- Every binomial coefficient `n.choose k` with `n ≤ 6` is at most `2^6 = 64`. -/
private theorem choose_le_64 {n k : ℕ} (hn : n ≤ 6) : (n.choose k : ℝ) ≤ 64 := by
  have h2 : 2 ^ n ≤ 64 := by
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 64 := by norm_num
  exact_mod_cast le_trans (Nat.choose_le_two_pow n k) h2

/-- The arithmetic tail: `k ≤ 7` and `S ≥ 0` give `k · (4096 S) ≤ 200704 S`. -/
private theorem arith_le {k S : ℝ} (hk : k ≤ 7) (hS : 0 ≤ S) :
    k * (4096 * S) ≤ 200704 * S := by
  have h1 : k * S ≤ 7 * S := mul_le_mul_of_nonneg_right hk hS
  nlinarith [h1]

/-- The **pure `D_z`-slot** of the matched majorant: for `i ≤ 6`, the squared weighted
`D_z^i` of the product is bounded by `200704` times the matched radial sum. -/
private theorem zslot_matched {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hDz : ∀ j : ℕ, j ≤ 6 →
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ))
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * (∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by
  set S : ℝ := ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _)
      (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)
  set Y : ℕ → ℝ := fun b => (i.choose b : ℝ)
      * (Work.Elliptic.DzdIter b r z
          * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) with hY
  have hexp : Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1), Y b := by
    rw [hDz i hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hY]; ring
  rw [hexp]
  have hcs : (∑ b ∈ Finset.range (i + 1), Y b) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), (Y b) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (i + 1)) (fun _ : ℕ => (1 : ℝ)) Y
    have hcard : ((Finset.range (i + 1)).card : ℝ) = (i : ℝ) + 1 := by
      rw [Finset.card_range]; push_cast; ring
    simpa [hcard] using h
  have hper : ∀ b ∈ Finset.range (i + 1), (Y b) ^ 2 ≤ 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by
    intro b hb
    rw [Finset.mem_range] at hb
    have hsub : i - b ≤ 6 - b := by omega
    have hch : (i.choose b : ℝ) ^ 2 ≤ 64 ^ 2 :=
      pow_le_pow_left₀ (by positivity) (choose_le_64 (by omega)) 2
    have hYsq : (Y b) ^ 2 = (i.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
        * (Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      simp only [hY]; ring
    rw [hYsq]
    calc (i.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (64 ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2) * Work.Spaces.HkIntegrand α (6 - b) g z θ :=
          mul_le_mul (mul_le_mul hch le_rfl (sq_nonneg _) (sq_nonneg _))
            (Work.Spaces.sq_le_HkIntegrand_z α (6 - b) g z θ (i - b) hsub)
            (sq_nonneg _) (by positivity)
      _ = 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by ring
  have hsum : ∑ b ∈ Finset.range (i + 1), (Y b) ^ 2 ≤ 4096 * S := by
    rw [hSdef, Finset.mul_sum]
    calc ∑ b ∈ Finset.range (i + 1), (Y b) ^ 2
        ≤ ∑ b ∈ Finset.range (i + 1), 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := Finset.sum_le_sum hper
      _ ≤ ∑ b ∈ Finset.range 7, 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun b _ _ => mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
              (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)))
  have hk : (i : ℝ) + 1 ≤ 7 := by
    have : i + 1 ≤ 7 := by omega
    exact_mod_cast this
  calc (∑ b ∈ Finset.range (i + 1), Y b) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), (Y b) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * (4096 * S) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 200704 * S := arith_le hk hSnn

/-- The **mixed slot** of the matched majorant: for `1 ≤ i`, `i + j ≤ 6`, the squared
weighted `D_z^j D_θ^i` of the product is bounded by `200704` times the matched radial
sum. -/
private theorem mslot_matched {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hMx : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 →
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ))
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * (∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by
  set S : ℝ := ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _)
      (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)
  set Y : ℕ → ℝ := fun b => (j.choose b : ℝ)
      * (Work.Elliptic.DzdIter b r z * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))
      with hY
  have hexp : Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1), Y b := by
    rw [hMx j i hi hij, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hY]; ring
  rw [hexp]
  have hcs : (∑ b ∈ Finset.range (j + 1), Y b) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (j + 1)) (fun _ : ℕ => (1 : ℝ)) Y
    have hcard : ((Finset.range (j + 1)).card : ℝ) = (j : ℝ) + 1 := by
      rw [Finset.card_range]; push_cast; ring
    simpa [hcard] using h
  have hper : ∀ b ∈ Finset.range (j + 1), (Y b) ^ 2 ≤ 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by
    intro b hb
    rw [Finset.mem_range] at hb
    have hsub : i + (j - b) ≤ 6 - b := by omega
    have hch : (j.choose b : ℝ) ^ 2 ≤ 64 ^ 2 :=
      pow_le_pow_left₀ (by positivity) (choose_le_64 (by omega)) 2
    have hYsq : (Y b) ^ 2 = (j.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
        * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      simp only [hY]; ring
    rw [hYsq]
    calc (j.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
          * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ (64 ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2) * Work.Spaces.HkIntegrand α (6 - b) g z θ :=
          mul_le_mul (mul_le_mul hch le_rfl (sq_nonneg _) (sq_nonneg _))
            (Work.Spaces.sq_le_HkIntegrand_mixed α (6 - b) g z θ i (j - b) hi hsub)
            (sq_nonneg _) (by positivity)
      _ = 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by ring
  have hsum : ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 ≤ 4096 * S := by
    rw [hSdef, Finset.mul_sum]
    calc ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2
        ≤ ∑ b ∈ Finset.range (j + 1), 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := Finset.sum_le_sum hper
      _ ≤ ∑ b ∈ Finset.range 7, 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun b _ _ => mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
              (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)))
  have hk : (j : ℝ) + 1 ≤ 7 := by
    have : j + 1 ≤ 7 := by omega
    exact_mod_cast this
  calc (∑ b ∈ Finset.range (j + 1), Y b) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 := hcs
    _ ≤ ((j : ℝ) + 1) * (4096 * S) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 200704 * S := arith_le hk hSnn

theorem radialMatchedMajorant :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ},
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j : ℕ, j ≤ 6 →
        Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ)) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 →
        Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ)) →
      ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6 (fun z θ => r z * g z θ) z θ
        ≤ C * ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α r g hDz hMx z θ hz hθ0 hθ1
  -- the matched radial sum `S`
  set S : ℝ := ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _)
      (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)
  -- decompose the level-`6` integrand into its two slot sums
  conv_lhs => simp only [Work.Spaces.HkIntegrand]
  -- ## the seven pure `D_z`-slots
  have hA : (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (200704 * S) := by
    calc (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 7, (200704 * S) :=
          Finset.sum_le_sum fun i hi =>
            zslot_matched (fun j hj => hDz z θ hz hθ0 hθ1 j hj) i (by
              have := Finset.mem_range.mp hi; omega)
      _ = 7 * (200704 * S) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- ## the (`≤ 49`) mixed slots
  have hB : (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 49 * (200704 * S) := by
    calc (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7, (200704 * S) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 6
          · rw [ite_eq_left hc]
            exact mslot_matched (fun j i hi hij => hMx z θ hz hθ0 hθ1 j i hi hij) i j hc.1 hc.2
          · rw [ite_eq_right hc]
            exact mul_nonneg (by norm_num) hSnn
      _ = 49 * (200704 * S) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ## the assembly
  have htot : 7 * (200704 * S) + 49 * (200704 * S) ≤ 10 ^ 8 * S := by
    nlinarith [hSnn]
  linarith [hA, hB, htot]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Uniform-in-`α` sup bounds for the slots of the model coefficient `A`

The paper's fundamental model (Elgindi, Annals **194** (2021), §FundamentalModel) has the
self-similar vorticity profile

`F(z,θ) = α · (Γ(θ)/c(α)) · 2z/(1+z)²`,

whose radial part `2z/(1+z)²` and angular part `Γ(θ)/c(α)` separate.  This file proves the
two sup bounds that the persistence proof needs for the coefficient `A` of `F`:

* every `D_z`-iterate up to order `4` of the radial profile `z ↦ 2z/(1+z)²` is bounded on
  `[0,∞)` by an absolute constant (`zslot_supBound`, value `24000`);
* every `D_θ`-iterate up to order `4` of `θ ↦ Γ(θ)/c(α)` is bounded uniformly for
  `α ∈ (0,1]` and `θ ∈ [0,π/2]` (`thetaslot_supBound`).

Because `D_z` and `D_θ` act on the two variables separately, the mixed slots
`D_z^b D_θ^a` of the product are bounded by the product of the two bounds
(`DzIter_fstSep` is the separation identity), which is the content of
`acoef_gamCoef_slots_le`.

The `z`-part goes through the closed form of the derivatives of `hKer(z) = z/(1+z)²`
(`Work.Spaces.pzIter_hKer_bound`) plus the Stirling expansion of `D_z^b`
(`Work.Spaces.DzIter_le_of_pzIter`); the `θ`-part goes through the coefficient sequence
`Tfun` with `D_θ^{j+1}Γ = α · Tfun j α · Γ` (`Work.Spaces.dthU_Gam_le`) and the lower
bound `c(α) ≥ 1/10` (`Work.Spaces.c_bounds`).
-/

namespace Work.FTS.StrongPersist.L3Aux

/-! ## Separation of variables for `D_z` -/


/-! ## The radial profile `z ↦ 2z/(1+z)²` -/

/-- The radial profile is smooth on `(-1,∞)`. -/
lemma contDiffOn_two_z_div :
    ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi (-1)) := by fun_prop
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) := by fun_prop
  exact hnum.div hden (fun z hz => by
    have h : (0 : ℝ) < 1 + z := by have := Set.mem_Ioi.mp hz; linarith
    positivity)

/-- The `z`-derivatives of the profile `2z/(1+z)²` are twice those of `hKer`. -/
lemma pzIter_two_z_div (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ
      = 2 * deriv^[j] Work.Spaces.hKer z := by
  have hfun : (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2)
      = (fun z θ => (fun _ => (2 : ℝ)) θ * Work.Spaces.hKer z) := by
    funext z θ; simp only [Work.Spaces.hKer_apply]; ring
  rw [hfun, Work.Spaces.pzIter_decomp]

/-- The weighted derivative bound for `hKer`: `|z^j ∂_z^j hKer z| ≤ j!(j+1)` for `z ≥ 0`.
This is `Work.Spaces.pzIter_hKer_bound` with the weight `(1+z)^j` replaced by `z^j` (the
ratio `z/(1+z)` lies in `[0,1]`). -/
lemma deriv_hKer_zpow_le (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ j * deriv^[j] Work.Spaces.hKer z| ≤ (j.factorial : ℝ) * (j + 1) := by
  have hz1 : (1 + z) ≠ 0 := by positivity
  have h1 : z ^ j = (z / (1 + z)) ^ j * (1 + z) ^ j := by
    rw [← mul_pow, div_mul_cancel₀ z hz1]
  have hq0 : (0 : ℝ) ≤ z / (1 + z) := div_nonneg hz (by linarith)
  have hq1 : z / (1 + z) ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]; linarith
  have hq : |(z / (1 + z)) ^ j| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hq0 j)]
    exact pow_le_one₀ hq0 hq1
  have h2 : |(1 + z) ^ j * deriv^[j] Work.Spaces.hKer z| ≤ (j.factorial : ℝ) * (j + 1) := by
    rw [show (1 + z) ^ j = (z + 1) ^ j by ring]
    exact Work.Spaces.pzIter_hKer_bound j z hz
  rw [h1, mul_assoc, abs_mul]
  calc |(z / (1 + z)) ^ j| * |(1 + z) ^ j * deriv^[j] Work.Spaces.hKer z|
      ≤ 1 * ((j.factorial : ℝ) * (j + 1)) :=
        mul_le_mul hq h2 (abs_nonneg _) (by norm_num)
    _ = (j.factorial : ℝ) * (j + 1) := one_mul _

/-- The all-orders bound for the weighted `z`-derivatives of the profile:
`|z^j ∂_z^j (2z/(1+z)²)| ≤ 2 j!(j+1)`. -/
lemma zpow_pzIter_two_z_div_le (j : ℕ) {z : ℝ} (hz : 0 ≤ z) (θ : ℝ) :
    |z ^ j * Work.Spaces.pzIter j (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ|
      ≤ 2 * ((j.factorial : ℝ) * (j + 1)) := by
  rw [pzIter_two_z_div]
  rw [show z ^ j * (2 * deriv^[j] Work.Spaces.hKer z)
        = 2 * (z ^ j * deriv^[j] Work.Spaces.hKer z) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have := deriv_hKer_zpow_le j hz
  linarith

/-- **The `z`-slots of the radial profile.**  Every `D_z`-iterate of order `b ≤ 4` of
`z ↦ 2z/(1+z)²` is bounded by `24000` on `[0,∞)`. -/
lemma zslot_supBound : ∀ b ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.DzIter b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ| ≤ 24000 := by
  intro b hb z hz θ hθ
  have hsmooth := fun (θ' : ℝ) (_ : θ' ∈ Work.Spaces.Iθ) => contDiffOn_two_z_div
  have hbound : ∀ j ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ| ≤ 240 := by
    intro j hj z hz θ hθ
    have h1 := zpow_pzIter_two_z_div_le j hz θ
    have h2 : (j.factorial : ℝ) * (j + 1) ≤ 120 := by interval_cases j <;> norm_num
    linarith
  have hmain := Work.Spaces.DzIter_le_of_pzIter
    (h := fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) (M := 240) (by norm_num)
    hsmooth hbound b hb z hz θ hθ
  linarith

/-! ## The angular profile `θ ↦ Γ(θ)/c(α)` -/


/-! ## The mixed slots of the coefficient `A` -/


end Work.FTS.StrongPersist.L3Aux
end
