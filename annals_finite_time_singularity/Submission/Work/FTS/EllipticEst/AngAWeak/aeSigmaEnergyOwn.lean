/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AngAWeak/aeSigmaEnergyOwn` — the `σ`-weighted radial energy inequality in the `AeData` class

The target of this module is

`∃ C > 0, ∀ α u G, AeData α u G → α ^ 2 * HkSq α 0 (z ∂_z u) ≤ C * (HkSq α 0 G + HkSq α 0 u)`

(the paper's Step 1 of `prop:H2` in the almost-everywhere class).  The sibling
`Submission/Work/FTS/EllipticEst/H2W/Ae/aeSigmaEnergy.lean` proves the same statement from two
`sorry`ed inputs (`H2W.Ae.aeSigmaCutoffSeq`, `H2W.Ae.aeTruncSigmaIdAe`) and the *stale*
`H2W.Ae.hkMem_gradU` (whose import cone is broken in the current tree).

Here the three inputs are supplied from the axiom-clean siblings:

* the truncated `σ`-identity is the *proved* `Dispatch.sigTruncIdentD` (the `θ`-integrated radial
  integration by parts, kept as a leaf of the shared library), whose five joint-integrability
  hypotheses are discharged from the proved `Dispatch.aeJointIntegrableF`;
* the slicewise `σ`-coercivity of `Lzero1` is the *proved* `Frontier.aeSigmaSliceLowerFts`;
* the cut-off family and its two uniform coefficient bounds are built from the proved
  `AngSecond.cut_deriv_uniform` and `AngularW.cutZ2Deriv2` together with the two explicit
  product-rule bounds `deriv_WcutZ_le`, `deriv_deriv_WcutZ2_le` proved below;
* `HkMem α 0 u` and `HkMem α 0 (z∂_zu)` come from the proved `Dispatch.hkMem_uM` and
  `Dispatch.hkMem_gradUD`.

The final arithmetic (the limit `n → ∞` of the truncated inequalities) is adapted from the
sibling's assembly.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF
import Submission.Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyTools
import Submission.Work.FTS.EllipticEst.Frontier.aeSigmaSliceLowerFts
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.AngularW.cutZ2Deriv2
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.Honest.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "sg" => Work.FTS.EllipticEst.sEta

/-! ## The angular weight and the level-`0` integrand -/

/-- The angular weight `σ = sin(2θ)^{-η} ≥ 1` on the open interval. -/
private theorem one_le_sEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ sg θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc : (-(Work.Spaces.eta) : ℝ) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs h1 hc
  rw [Real.one_rpow] at h
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- `σ` is `C²` on the open interval. -/
private theorem contDiffOn_sEta_Ioo :
    ContDiffOn ℝ 2 (fun θ : ℝ => sg θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have h := hsin.rpow (contDiffOn_const (c := -(Work.Spaces.eta))) (fun θ hθ => hne θ hθ)
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- `σ` is continuous on the open interval. -/
private theorem continuousOn_sEta_Ioo :
    ContinuousOn (fun θ : ℝ => sg θ) (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_sEta_Ioo.continuousOn

/-- `w z ≥ 1` for `z > 0`. -/
private theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (pow_pos hz 2)]
  nlinarith [hz]

/-- The level-`0` integrand is `w(z)² · f² σ`. -/
private theorem HkIntegrand_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sg θ) :=
  Work.FTS.EllipticEst.Dispatch.HkIntegrand_zero_D α f hθ

/-! ## `HkSq α 0` as the `w²`-weighted slice integral -/

/-- **`HkSq α 0 g` in the `w²`-weighted slice form**, and the integrability of the integrand. -/
private theorem hksq_slice_eq {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * sg θ)) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * sg θ)) = Work.Spaces.HkSq α 0 g := by
  obtain ⟨hint, hval⟩ := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral hg
  refine ⟨?_, ?_⟩
  · refine hint.congr_fun (fun z _ => ?_) measurableSet_Ici
    simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig,
      Work.FTS.EllipticEst.sEta]
  · rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * sg θ))
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z *
          (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) from by
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig,
        Work.FTS.EllipticEst.sEta]]
    exact hval

/-- The slice mass `z ↦ ∫_θ u² σ` is nonnegative. -/
private theorem sliceMass_nonneg (f : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * sg θ := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Dispatch.sEta_nonneg_Iθ_D hθ)


/-! ## Regularity of the radial weight `w²` -/

/-- `z ↦ w z ^ 2` is `C²` on `(0,∞)`. -/
private theorem contDiffOn_w_sq_two :
    ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContDiffOn.div ?_ ?_ ?_
    · exact (contDiffOn_const.add contDiffOn_id).pow 2
    · exact contDiffOn_id.pow 2
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  have h2 := h1.pow 2
  rw [show (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2)) ^ 2 by
    funext y; simp only [Pi.pow_apply]; rw [Work.Spaces.w]]
  exact h2

/-- `z ↦ z² w z²` is `C²` on `(0,∞)`. -/
private theorem contDiffOn_w_sq_mul_sq :
    ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  rw [show (fun z : ℝ => z ^ 2 * (Work.Spaces.w z) ^ 2)
      = (id ^ 2) * (fun z : ℝ => (Work.Spaces.w z) ^ 2) by
    funext y; simp only [Pi.mul_apply, Pi.pow_apply, id_eq]]
  exact (contDiffOn_id.pow 2).mul contDiffOn_w_sq_two

/-- **The second-derivative product rule on `(0,∞)`.** -/
private theorem deriv_deriv_mul_Ioi (χ φ : ℝ → ℝ)
    (hχ : DifferentiableOn ℝ χ (Set.Ioi 0)) (hφ : DifferentiableOn ℝ φ (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z)
    (hdχ : DifferentiableAt ℝ (deriv χ) z) (hdφ : DifferentiableAt ℝ (deriv φ) z) :
    deriv (deriv (χ * φ)) z
      = deriv (deriv χ) z * φ z + 2 * deriv χ z * deriv φ z + χ z * deriv (deriv φ) z := by
  have heq2 : (fun y => deriv (χ * φ) y) =ᶠ[𝓝 z]
      (fun y => deriv χ y * φ y + χ y * deriv φ y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact deriv_mul ((hχ y hy).differentiableAt (isOpen_Ioi.mem_nhds hy))
      ((hφ y hy).differentiableAt (isOpen_Ioi.mem_nhds hy))
  change deriv (fun y => deriv (χ * φ) y) z = _
  rw [Filter.EventuallyEq.deriv_eq heq2]
  have hfun : (fun y => deriv χ y * φ y + χ y * deriv φ y)
      = (fun y => deriv χ y * φ y) + (fun y => χ y * deriv φ y) := by
    funext y; rfl
  rw [hfun]
  have h1 : HasDerivAt (fun y => deriv χ y * φ y)
      (deriv (deriv χ) z * φ z + deriv χ z * deriv φ z) z :=
    hdχ.hasDerivAt.mul ((hφ z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have h2 : HasDerivAt (fun y => χ y * deriv φ y)
      (deriv χ z * deriv φ z + χ z * deriv (deriv φ) z) z :=
    ((hχ z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt.mul hdφ.hasDerivAt
  rw [(h1.add h2).deriv]
  ring

/-- **Uniform coefficient bound for the first-order transfer term** `(χ w² z)'`. -/
private theorem deriv_WcutZ_le {χ : ℝ → ℝ} {K : ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχ01 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hK : ∀ z, |z * deriv χ z| ≤ K) :
    ∀ z, 0 < z → |deriv (fun y => Work.FTS.EllipticEst.Dispatch.WcutZ χ y) z|
      ≤ (K + 3) * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨hFa, hFb, hFc, hFd, hFe, hFf, hFg, hFh, hFi, hFj, hFk⟩ :=
    Work.FTS.EllipticEst.weight_algebra_fts
  intro z hz
  have hz' : z ≠ 0 := ne_of_gt hz
  have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    rw [Work.Spaces.w, div_pow]; ring
  have hφnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hφd : DifferentiableAt ℝ (fun y : ℝ => (Work.Spaces.w y) ^ 2) z :=
    (contDiffOn_w_sq_two.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hgd : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z :=
    differentiableAt_id.mul hφd
  have hfun : (fun y => Work.FTS.EllipticEst.Dispatch.WcutZ χ y)
      = fun y => χ y * (y * (Work.Spaces.w y) ^ 2) := by
    funext y
    simp only [Work.FTS.EllipticEst.Dispatch.WcutZ, Work.FTS.EllipticEst.Dispatch.Wcut]
    ring
  have hfun2 : (fun y => χ y * (y * (Work.Spaces.w y) ^ 2))
      = χ * (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) := by
    funext y; rfl
  rw [hfun, hfun2, deriv_mul ((hχ.differentiable (by norm_num)) z) hgd]
  have hb1 : |deriv χ z * (z * (Work.Spaces.w z) ^ 2)| ≤ K * (Work.Spaces.w z) ^ 2 := by
    rw [show deriv χ z * (z * (Work.Spaces.w z) ^ 2)
        = (z * deriv χ z) * (Work.Spaces.w z) ^ 2 from by ring,
      abs_mul, abs_of_nonneg hφnn]
    exact mul_le_mul_of_nonneg_right (hK z) hφnn
  have hb2 : |χ z * deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z|
      ≤ 3 * (Work.Spaces.w z) ^ 2 := by
    rw [hFd z hz', abs_mul]
    have hχz : |χ z| ≤ 1 := by rw [abs_of_nonneg (hχ01 z)]; exact hχ1 z
    calc |χ z| * |(z - 3) * (1 + z) ^ 3 / z ^ 4| ≤ 1 * |(z - 3) * (1 + z) ^ 3 / z ^ 4| :=
          mul_le_mul_of_nonneg_right hχz (abs_nonneg _)
      _ ≤ 3 * (Work.Spaces.w z) ^ 2 := by
          rw [one_mul, hw]
          have hz3 : |z - 3| ≤ 3 * (1 + z) := by rw [abs_le]; constructor <;> linarith
          rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1+z)^3),
            abs_of_nonneg (by positivity : (0:ℝ) ≤ z^4)]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < z^4)]
          have h15 : |z - 3| * (1 + z) ^ 3 ≤ 3 * (1 + z) ^ 4 := by
            have h1 : (0:ℝ) < (1+z)^3 := by positivity
            nlinarith [hz3, h1]
          calc |z - 3| * (1 + z) ^ 3 ≤ 3 * (1 + z) ^ 4 := h15
            _ = 3 * ((1 + z) ^ 4 / z ^ 4) * z ^ 4 := by field_simp
  calc |deriv χ z * (z * (Work.Spaces.w z) ^ 2)
        + χ z * deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z| ≤ _ + _ := abs_add_le _ _
    _ ≤ K * (Work.Spaces.w z) ^ 2 + 3 * (Work.Spaces.w z) ^ 2 := add_le_add hb1 hb2
    _ = (K + 3) * (Work.Spaces.w z) ^ 2 := by ring

/-- **Uniform coefficient bound for the second-order transfer term** `(χ w² z²)''`. -/
private theorem deriv_deriv_WcutZ2_le {χ : ℝ → ℝ} {K K₂ : ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχ01 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hK : ∀ z, |z * deriv χ z| ≤ K) (hK₂ : ∀ z, |z ^ 2 * deriv (deriv χ) z| ≤ K₂) :
    ∀ z, 0 < z → |deriv (deriv (fun y => Work.FTS.EllipticEst.Dispatch.WcutZ2 χ y)) z|
      ≤ (K₂ + 4 * K + 6) * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨hFa, hFb, hFc, hFd, hFe, hFf, hFg, hFh, hFi, hFj, hFk⟩ :=
    Work.FTS.EllipticEst.weight_algebra_fts
  intro z hz
  have hz' : z ≠ 0 := ne_of_gt hz
  have hw : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    rw [Work.Spaces.w, div_pow]; ring
  have hφnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  set F : ℝ → ℝ := fun y => y ^ 2 * (Work.Spaces.w y) ^ 2 with hFdef
  have hFcd : ContDiffOn ℝ 2 F (Set.Ioi 0) := contDiffOn_w_sq_mul_sq
  have hFdiff : DifferentiableOn ℝ F (Set.Ioi 0) := hFcd.differentiableOn (by norm_num)
  have hdF : DifferentiableAt ℝ (deriv F) z :=
    ((hFcd.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hχdiff : DifferentiableOn ℝ χ (Set.Ioi 0) :=
    (hχ.contDiffOn).differentiableOn (by norm_num)
  have hdχ : DifferentiableAt ℝ (deriv χ) z :=
    (((hχ.contDiffOn).deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hfun : (fun y => Work.FTS.EllipticEst.Dispatch.WcutZ2 χ y) = fun y => χ y * F y := by
    funext y
    simp only [Work.FTS.EllipticEst.Dispatch.WcutZ2, Work.FTS.EllipticEst.Dispatch.Wcut, hFdef]
    ring
  have hfun2 : (fun y => χ y * F y) = χ * F := by funext y; rfl
  rw [hfun, hfun2, deriv_deriv_mul_Ioi χ F hχdiff hFdiff hz hdχ hdF]
  have hFz : F z = z ^ 2 * (Work.Spaces.w z) ^ 2 := rfl
  have hb1 : |deriv (deriv χ) z * F z| ≤ K₂ * (Work.Spaces.w z) ^ 2 := by
    rw [hFz, show deriv (deriv χ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        = (z ^ 2 * deriv (deriv χ) z) * (Work.Spaces.w z) ^ 2 from by ring,
      abs_mul, abs_of_nonneg hφnn]
    exact mul_le_mul_of_nonneg_right (hK₂ z) hφnn
  have hb2 : |2 * deriv χ z * deriv F z| ≤ 4 * K * (Work.Spaces.w z) ^ 2 := by
    have hFder : deriv F z = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 := hFc z hz'
    have h1 : deriv F z / z = 2 * (z - 1) * (1 + z) ^ 3 / z ^ 4 := by
      rw [hFder]; field_simp
    have h2 : |deriv F z / z| ≤ 2 * (Work.Spaces.w z) ^ 2 := by
      rw [h1, hw]
      have hz1 : |z - 1| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
      rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1+z)^3),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ z^4)]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < z^4)]
      have h15 : 2 * |z - 1| * (1 + z) ^ 3 ≤ 2 * (1 + z) ^ 4 := by
        have h1' : (0:ℝ) < (1+z)^3 := by positivity
        nlinarith [hz1, h1']
      calc 2 * |z - 1| * (1 + z) ^ 3 ≤ 2 * (1 + z) ^ 4 := h15
        _ = 2 * ((1 + z) ^ 4 / z ^ 4) * z ^ 4 := by field_simp
    calc |2 * deriv χ z * deriv F z| = 2 * |z * deriv χ z| * |deriv F z / z| := by
          rw [show 2 * deriv χ z * deriv F z
              = 2 * (z * deriv χ z) * (deriv F z / z) from by field_simp]
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ 2 * K * (2 * (Work.Spaces.w z) ^ 2) := by
          have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hK z) (by norm_num)) h2 (abs_nonneg _)
            (by positivity)
      _ = 4 * K * (Work.Spaces.w z) ^ 2 := by ring
  have hb3 : |χ z * deriv (deriv F) z| ≤ 6 * (Work.Spaces.w z) ^ 2 := by
    have hle := hFf z hz
    have hge := hFh z hz
    have hχz : |χ z| ≤ 1 := by rw [abs_of_nonneg (hχ01 z)]; exact hχ1 z
    rw [abs_mul]
    calc |χ z| * |deriv (deriv F) z| ≤ 1 * (6 * (Work.Spaces.w z) ^ 2) := by
          refine mul_le_mul hχz ?_ (abs_nonneg _) (by norm_num)
          rw [abs_of_nonneg hge]; exact hle
      _ = 6 * (Work.Spaces.w z) ^ 2 := by ring
  calc |deriv (deriv χ) z * F z + 2 * deriv χ z * deriv F z + χ z * deriv (deriv F) z|
      ≤ |deriv (deriv χ) z * F z| + |2 * deriv χ z * deriv F z|
        + |χ z * deriv (deriv F) z| := by
        have h1 := abs_add_le (deriv (deriv χ) z * F z + 2 * deriv χ z * deriv F z)
          (χ z * deriv (deriv F) z)
        have h2 := abs_add_le (deriv (deriv χ) z * F z) (2 * deriv χ z * deriv F z)
        linarith
    _ ≤ K₂ * (Work.Spaces.w z) ^ 2 + 4 * K * (Work.Spaces.w z) ^ 2
          + 6 * (Work.Spaces.w z) ^ 2 := by linarith [hb1, hb2, hb3]
    _ = (K₂ + 4 * K + 6) * (Work.Spaces.w z) ^ 2 := by ring


/-! ## The proved truncated `σ`-identity with its honesty hypotheses discharged -/

/-- `|a b| ≤ (a² + b²)/2`. -/
private theorem abs_mul_le_half {a b : ℝ} : |a * b| ≤ (1 / 2) * (a ^ 2 + b ^ 2) := by
  have h := abs_mul a b
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- `w(z)² σ θ f² = HkIntegrand α 0 f`. -/
private theorem wsq_sigma_mul_sq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * sg θ * (f z θ) ^ 2 = Work.Spaces.HkIntegrand α 0 f z θ := by
  rw [HkIntegrand_eq α f hθ]; ring

/-- Commutation of the two factors inside the slice mass. -/
private theorem sliceMass_comm (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * sg θ)
      = ∫ θ in Work.Spaces.Iθ, sg θ * (f z θ) ^ 2 :=
  setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-- **The pairing bound** `|w²σ · f g| ≤ (Hk(f) + Hk(g))/2`. -/
private theorem wsq_sigma_mul_abs_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |(Work.Spaces.w z) ^ 2 * sg θ * (f z θ * g z θ)|
      ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0 f z θ
          + Work.Spaces.HkIntegrand α 0 g z θ) := by
  have hσnn : 0 ≤ sg θ := Work.FTS.EllipticEst.Dispatch.sEta_nonneg_Iθ_D hθ
  have hw2nn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have ham := abs_mul_le_half (a := f z θ) (b := g z θ)
  calc |(Work.Spaces.w z) ^ 2 * sg θ * (f z θ * g z θ)|
      = (Work.Spaces.w z) ^ 2 * sg θ * |f z θ * g z θ| := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hw2nn hσnn)]
    _ ≤ (Work.Spaces.w z) ^ 2 * sg θ * ((1 / 2) * ((f z θ) ^ 2 + (g z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left ham (mul_nonneg hw2nn hσnn)
    _ = (1 / 2) * ((Work.Spaces.w z) ^ 2 * sg θ * (f z θ) ^ 2
          + (Work.Spaces.w z) ^ 2 * sg θ * (g z θ) ^ 2) := by ring
    _ = (1 / 2) * (Work.Spaces.HkIntegrand α 0 f z θ
          + Work.Spaces.HkIntegrand α 0 g z θ) := by
        rw [wsq_sigma_mul_sq α f hθ, wsq_sigma_mul_sq α g hθ]

/-- **The truncated `σ`-weighted energy identity** in the `AeData` class: the proved leaf
`Dispatch.sigTruncIdentD` with its five joint-integrability hypotheses discharged from the class
by `Dispatch.aeJointIntegrableF` and the two coefficient bounds. -/
private theorem sigId {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχcpt : HasCompactSupport χ)
    (hχ0 : ∃ δ : ℝ, 0 < δ ∧ ∀ z, z ≤ δ → χ z = 0)
    (hχ01 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    {K₃ K₄ : ℝ} (hK₃ : ∀ z, 0 < z → |deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 χ)) z|
      ≤ K₃ * (Work.Spaces.w z) ^ 2)
    (hK₄ : ∀ z, 0 < z → |deriv (Work.FTS.EllipticEst.Dispatch.om1 χ) z|
      ≤ K₄ * (Work.Spaces.w z) ^ 2) :
    (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om χ z *
        (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ)))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om2 χ z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om χ z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 χ)) z *
              (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2))
        + ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (Work.FTS.EllipticEst.Dispatch.om1 χ) z *
              (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2)) := by
  have hU : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall hA.smooth
  have hD : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Ae.grad u) := hU.Dz
  have hA2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hU
  have hbslSm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hU
  have hGsm : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl hbslSm
      (fun z θ hz hθ hθ' => hA.eq z hz θ hθ hθ')
  have hmu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
  have hmd : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
  have hIu := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hU hmu
  have hId := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hD hmd
  have hIg := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hGsm hA.memG
  have hIa := Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hA2 hA.memRad2
  have hσc : ContinuousOn (fun p : ℝ × ℝ => sg p.2) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_sEta_Ioo.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hWc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Dispatch.Wcut χ p.1)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.Dispatch.contDiffOn_two_Wcut hχ).continuousOn.comp
      continuous_fst.continuousOn (fun p hp => hp.1)
  have hσaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => sg p.2)
      Work.FTS.EllipticEst.Dispatch.nuFts :=
    Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hσc
  have hdaesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      deriv (Work.FTS.EllipticEst.Dispatch.om1 χ) p.1) Work.FTS.EllipticEst.Dispatch.nuFts := by
    refine Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 ?_
    have hcd : ContDiffOn ℝ 2 (Work.FTS.EllipticEst.Dispatch.om1 χ) (Set.Ioi 0) := by
      have h2 : ContDiffOn ℝ 2
          (fun z : ℝ => z * Work.FTS.EllipticEst.Dispatch.Wcut χ z) (Set.Ioi 0) :=
        contDiffOn_id.mul (Work.FTS.EllipticEst.Dispatch.contDiffOn_two_Wcut hχ)
      refine h2.congr ?_
      intro z hz
      simp only [Work.FTS.EllipticEst.Dispatch.om1, Work.FTS.EllipticEst.Dispatch.om,
        Work.FTS.EllipticEst.Dispatch.Wcut]
      ring
    exact ((hcd.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).continuousOn).comp
      continuous_fst.continuousOn (fun p hp => hp.1)
  have hUaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1 p.2)
      Work.FTS.EllipticEst.Dispatch.nuFts :=
    Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hU.continuousOn
  have hU2aesm : AEStronglyMeasurable (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Dispatch.nuFts := hUaesm.pow 2
  have hcc : ContinuousOn (fun p : ℝ × ℝ =>
      deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 χ)) p.1) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.Dispatch.continuousOn_deriv_deriv_WcutZ2 hχ).comp
      continuous_fst.continuousOn (fun p hp => hp.1)
  have huc : ContinuousOn (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
    hU.continuousOn.pow 2
  obtain ⟨hJF1, hJF2, hJF3, hJF4, hJF5, hJF6, hJF7⟩ :=
    Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF α u G hA χ hχ hχcpt hχ0 hχ01 hχ1
  -- ## hJ1: the source pairing
  have hJ1n : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.EllipticEst.Dispatch.om χ p.1 *
        (sg p.2 * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2)))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
    refine (hIg.add hIu).mono' ?_ ?_
    · exact Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0
        (hWc.mul (hσc.mul (hbslSm.continuousOn.mul hU.continuousOn)))
    · filter_upwards [Work.FTS.EllipticEst.Dispatch.ae_mem_Ioo_nu,
        Work.FTS.EllipticEst.Dispatch.ae_mem_Ioi_nu] with p hp hp1
      obtain ⟨z, θ⟩ := p
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
      have hbsl : Work.Elliptic.bslOp α u z θ = G z θ := hA.eq z hp1 θ hp.1 hp.2
      have hrew : Work.FTS.EllipticEst.Dispatch.om χ z * (sg θ * (G z θ * u z θ))
          = χ z * ((Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ)) := by
        simp only [Work.FTS.EllipticEst.Dispatch.om]; ring
      rw [hbsl, hrew, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ01 z)]
      calc χ z * |(Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ)|
          ≤ 1 * ((1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
              + Work.Spaces.HkIntegrand α 0 u z θ)) :=
            mul_le_mul (by linarith [hχ1 z]) (wsq_sigma_mul_abs_le (f := G) (g := u) hθI)
              (abs_nonneg _) (by norm_num)
        _ ≤ Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ := by
            linarith [Work.Spaces.HkIntegrand_nonneg α 0 G z θ,
              Work.Spaces.HkIntegrand_nonneg α 0 u z θ]
  -- ## hJ2: the radial first-order slot
  have hJ2n : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (Work.FTS.EllipticEst.Dispatch.om χ p.1 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
    refine hId.mono' ?_ ?_
    · exact hσaesm.mul (Work.FTS.EllipticEst.Dispatch.aesm_Wcut_sq hχ hD.continuousOn)
    · filter_upwards [Work.FTS.EllipticEst.Dispatch.ae_mem_Ioo_nu,
        Work.FTS.EllipticEst.Dispatch.ae_mem_Ioi_nu] with p hp hp1
      obtain ⟨z, θ⟩ := p
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
      have hrew : sg θ * (Work.FTS.EllipticEst.Dispatch.om χ z * (z * Work.Spaces.pz u z θ) ^ 2)
          = χ z * ((Work.Spaces.w z) ^ 2 * sg θ
              * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
                * (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)) := by
        simp only [Work.FTS.EllipticEst.H2W.Ae.grad, Work.FTS.EllipticEst.Dispatch.om]
        ring
      rw [hrew, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ01 z)]
      calc χ z * |(Work.Spaces.w z) ^ 2 * sg θ
            * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
              * (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)|
          ≤ 1 * ((1 / 2) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
              + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)) :=
            mul_le_mul (by linarith [hχ1 z])
              (wsq_sigma_mul_abs_le (f := Work.FTS.EllipticEst.H2W.Ae.grad u)
                (g := Work.FTS.EllipticEst.H2W.Ae.grad u) hθI) (abs_nonneg _) (by norm_num)
        _ ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ := by
            linarith [Work.Spaces.HkIntegrand_nonneg α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ]
  -- ## hJ3: the radial second-order transfer term
  have hJ3n : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 χ)) p.1 * (u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
    refine (hIu.const_mul K₃).mono' ?_ ?_
    · exact hσaesm.mul (Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0
        (hcc.mul huc))
    · filter_upwards [Work.FTS.EllipticEst.Dispatch.ae_mem_Ioo_nu,
        Work.FTS.EllipticEst.Dispatch.ae_mem_Ioi_nu] with p hp hp1
      obtain ⟨z, θ⟩ := p
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
      have hσnn : 0 ≤ sg θ := Work.FTS.EllipticEst.Dispatch.sEta_nonneg_Iθ_D hθI
      rw [Real.norm_eq_abs]
      calc |sg θ * (deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 χ)) z * (u z θ) ^ 2)|
          = |deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 χ)) z| * (sg θ * (u z θ) ^ 2) := by
            rw [abs_mul, abs_of_nonneg hσnn]
            rw [abs_mul, abs_of_nonneg (sq_nonneg (u z θ))]
            ring
        _ ≤ K₃ * Work.Spaces.HkIntegrand α 0 u z θ := by
            rw [← wsq_sigma_mul_sq α u hθI]
            calc |deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 χ)) z| * (sg θ * (u z θ) ^ 2)
                ≤ (K₃ * (Work.Spaces.w z) ^ 2) * (sg θ * (u z θ) ^ 2) :=
                  mul_le_mul_of_nonneg_right (hK₃ z hp1) (mul_nonneg hσnn (sq_nonneg _))
              _ = K₃ * ((Work.Spaces.w z) ^ 2 * sg θ * (u z θ) ^ 2) := by ring
  -- ## hJ4: the radial first-order transfer term
  have hJ4n : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (deriv (Work.FTS.EllipticEst.Dispatch.om1 χ) p.1 * (u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
    refine (hIu.const_mul K₄).mono' ?_ ?_
    · exact hσaesm.mul (hdaesm.mul hU2aesm)
    · filter_upwards [Work.FTS.EllipticEst.Dispatch.ae_mem_Ioo_nu,
        Work.FTS.EllipticEst.Dispatch.ae_mem_Ioi_nu] with p hp hp1
      obtain ⟨z, θ⟩ := p
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
      have hσnn : 0 ≤ sg θ := Work.FTS.EllipticEst.Dispatch.sEta_nonneg_Iθ_D hθI
      rw [Real.norm_eq_abs]
      calc |sg θ * (deriv (Work.FTS.EllipticEst.Dispatch.om1 χ) z * (u z θ) ^ 2)|
          = |deriv (Work.FTS.EllipticEst.Dispatch.om1 χ) z| * (sg θ * (u z θ) ^ 2) := by
            rw [abs_mul, abs_of_nonneg hσnn]
            rw [abs_mul, abs_of_nonneg (sq_nonneg (u z θ))]
            ring
        _ ≤ K₄ * Work.Spaces.HkIntegrand α 0 u z θ := by
            rw [← wsq_sigma_mul_sq α u hθI]
            calc |deriv (Work.FTS.EllipticEst.Dispatch.om1 χ) z| * (sg θ * (u z θ) ^ 2)
                ≤ (K₄ * (Work.Spaces.w z) ^ 2) * (sg θ * (u z θ) ^ 2) :=
                  mul_le_mul_of_nonneg_right (hK₄ z hp1) (mul_nonneg hσnn (sq_nonneg _))
              _ = K₄ * ((Work.Spaces.w z) ^ 2 * sg θ * (u z θ) ^ 2) := by ring
  -- ## hJ5: the angular self-form pairing
  have hJ5n : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Dispatch.om χ p.1 *
      (sg p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
    refine (((hIg.add hIu).add (hIa.add hId)).const_mul 4).mono' ?_ ?_
    · refine (hσaesm.mul hJF7.aestronglyMeasurable).congr ?_
      filter_upwards with p
      simp only [Pi.mul_apply, Function.uncurry, Work.FTS.EllipticEst.Dispatch.om,
        Work.FTS.EllipticEst.Dispatch.Wcut]
      ring
    · filter_upwards [Work.FTS.EllipticEst.Dispatch.ae_mem_Ioo_nu,
        Work.FTS.EllipticEst.Dispatch.ae_mem_Ioi_nu] with p hp hp1
      obtain ⟨z, θ⟩ := p
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
      have hw2nn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hαnn : 0 ≤ α := le_of_lt hA.hα
      have hα4 : α ≤ 1 / 4 := hA.hα4
      have hL : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + α * (5 + α) * z * Work.Spaces.pz u z θ := by
        have h := hA.eq z hp1 θ hp.1 hp.2
        rw [Work.Elliptic.bslOp_apply] at h
        linarith
      have hsplit : Work.FTS.EllipticEst.Dispatch.om χ z * (sg θ * (Work.Elliptic.Lzero u z θ * u z θ))
          = χ z * ((Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ))
            + α ^ 2 * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)))
            + (α * (5 + α)) * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ * u z θ))) := by
        rw [hL]
        simp only [Work.FTS.EllipticEst.Dispatch.om, Work.FTS.EllipticEst.H2W.Ae.grad]
        ring
      rw [hsplit, Real.norm_eq_abs]
      have ht1 : |χ z * ((Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ))|
          ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
              + Work.Spaces.HkIntegrand α 0 u z θ) := by
        rw [abs_mul, abs_of_nonneg (hχ01 z)]
        calc χ z * |(Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ)|
            ≤ 1 * ((1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)) :=
              mul_le_mul (by linarith [hχ1 z]) (wsq_sigma_mul_abs_le (f := G) (g := u) hθI)
                (abs_nonneg _) (by norm_num)
          _ = (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
                + Work.Spaces.HkIntegrand α 0 u z θ) := by ring
      have ht2 : |α ^ 2 * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
            * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)))|
          ≤ α ^ 2 * ((1 / 2) * (Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ)) := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg α)]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg α)
        rw [abs_mul, abs_of_nonneg (hχ01 z)]
        calc χ z * |(Work.Spaces.w z) ^ 2 * sg θ
              * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)|
            ≤ 1 * ((1 / 2) * (Work.Spaces.HkIntegrand α 0
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)) :=
              mul_le_mul (by linarith [hχ1 z])
                (wsq_sigma_mul_abs_le (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
                  (g := u) hθI) (abs_nonneg _) (by norm_num)
          _ = (1 / 2) * (Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ) := by ring
      have ht3 : |(α * (5 + α)) * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
            * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ * u z θ)))|
          ≤ (α * (5 + α)) * ((1 / 2) * (Work.Spaces.HkIntegrand α 0
              (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ)) := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hαnn (by linarith [hαnn]))]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hαnn (by linarith [hαnn]))
        rw [abs_mul, abs_of_nonneg (hχ01 z)]
        calc χ z * |(Work.Spaces.w z) ^ 2 * sg θ
              * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ * u z θ)|
            ≤ 1 * ((1 / 2) * (Work.Spaces.HkIntegrand α 0
                  (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)) :=
              mul_le_mul (by linarith [hχ1 z])
                (wsq_sigma_mul_abs_le (f := Work.FTS.EllipticEst.H2W.Ae.grad u) (g := u) hθI)
                (abs_nonneg _) (by norm_num)
          _ = (1 / 2) * (Work.Spaces.HkIntegrand α 0
                (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ) := by ring
      have htri : |χ z * ((Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ))
            + α ^ 2 * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)))
            + (α * (5 + α)) * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ * u z θ)))|
          ≤ |χ z * ((Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ))|
            + |α ^ 2 * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)))|
            + |(α * (5 + α)) * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ * u z θ)))| := by
        have h1 := abs_add_le (χ z * ((Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ))
            + α ^ 2 * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ))))
          ((α * (5 + α)) * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ * u z θ))))
        have h2 := abs_add_le (χ z * ((Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ)))
          (α ^ 2 * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ))))
        linarith
      have hGnn := Work.Spaces.HkIntegrand_nonneg α 0 G z θ
      have hUnn := Work.Spaces.HkIntegrand_nonneg α 0 u z θ
      have hAnn := Work.Spaces.HkIntegrand_nonneg α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
      have hDnn := Work.Spaces.HkIntegrand_nonneg α 0
        (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      have hα2le : α ^ 2 ≤ 1 := by nlinarith [hα4, hαnn]
      have hα5 : α * (5 + α) ≤ 4 := by nlinarith [hα4, hαnn]
      calc |χ z * ((Work.Spaces.w z) ^ 2 * sg θ * (G z θ * u z θ))
            + α ^ 2 * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)))
            + (α * (5 + α)) * (χ z * ((Work.Spaces.w z) ^ 2 * sg θ
                * ((Work.FTS.EllipticEst.H2W.Ae.grad u) z θ * u z θ)))|
          ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ)
            + α ^ 2 * ((1 / 2) * (Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ))
            + (α * (5 + α)) * ((1 / 2) * (Work.Spaces.HkIntegrand α 0
                (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)) := by linarith [htri, ht1, ht2, ht3]
        _ ≤ 4 * (Work.Spaces.HkIntegrand α 0 G z θ + Work.Spaces.HkIntegrand α 0 u z θ
            + (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
              + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)) := by
            have hA1 : (0 : ℝ) ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ) := by linarith
            have hD1 : (0 : ℝ) ≤ (1 / 2) * (Work.Spaces.HkIntegrand α 0
                (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ) := by linarith
            have e1 := mul_le_mul_of_nonneg_right hα2le hA1
            have e2 := mul_le_mul_of_nonneg_right hα5 hD1
            have e3 : (1 / 2) * (Work.Spaces.HkIntegrand α 0 G z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)
                ≤ 4 * ((Work.Spaces.HkIntegrand α 0 G z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)
                + (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)) := by
              linarith [hGnn, hUnn, hAnn, hDnn]
            have e4 : (1 / 2) * (Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)
                ≤ 4 * ((Work.Spaces.HkIntegrand α 0 G z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)
                + (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)) := by
              linarith [hGnn, hUnn, hAnn, hDnn]
            have e5 : (1 / 2) * (Work.Spaces.HkIntegrand α 0
                (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)
                ≤ 4 * ((Work.Spaces.HkIntegrand α 0 G z θ
                + Work.Spaces.HkIntegrand α 0 u z θ)
                + (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ)) := by
              linarith [hGnn, hUnn, hAnn, hDnn]
            linarith [e1, e2, e3, e4, e5]
  -- ## the identity
  have hmsig : Work.FTS.EllipticEst.Dispatch.msig = Work.FTS.EllipticEst.Dispatch.nuFts := by
    simp only [Work.FTS.EllipticEst.Dispatch.msig, Work.FTS.EllipticEst.Dispatch.nuFts]
    rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))]
  have hsl : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0) :=
    fun θ hθ => Work.FTS.EllipticEst.Dispatch.slice_z_smooth_D hA hθ 2
  have hJ1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.EllipticEst.Dispatch.om χ p.1 *
        (sg p.2 * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2)))
      Work.FTS.EllipticEst.Dispatch.msig := by rw [hmsig]; exact hJ1n
  have hJ2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (Work.FTS.EllipticEst.Dispatch.om χ p.1 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.msig := by rw [hmsig]; exact hJ2n
  have hJ3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 χ)) p.1 * (u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.msig := by rw [hmsig]; exact hJ3n
  have hJ4 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (deriv (Work.FTS.EllipticEst.Dispatch.om1 χ) p.1 * (u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.msig := by rw [hmsig]; exact hJ4n
  have hJ5 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Dispatch.om χ p.1 *
      (sg p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)))
      Work.FTS.EllipticEst.Dispatch.msig := by rw [hmsig]; exact hJ5n
  exact Work.FTS.EllipticEst.Dispatch.sigTruncIdentD α u G χ hχ hχcpt hχ0 hA.eq
    hJ1 hJ2 hJ3 hJ4 hJ5 hsl


/-! ## The assembly: from the truncated identity to the untruncated estimate -/

/-- The angular AM--GM pairing bound. -/
private theorem thetaPairing {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * sg θ) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * sg θ) Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, sg θ * (f θ * g θ)|
      ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * sg θ)
        + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * sg θ)) := by
  have hstep1 : |∫ θ in Work.Spaces.Iθ, sg θ * (f θ * g θ)|
      ≤ ∫ θ in Work.Spaces.Iθ, |sg θ * (f θ * g θ)| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun θ => sg θ * (f θ * g θ))
  have hint : MeasureTheory.IntegrableOn (fun θ => (1 / 2) *
      ((f θ) ^ 2 * sg θ + (g θ) ^ 2 * sg θ)) Work.Spaces.Iθ := (hf.add hg).const_mul _
  have hstep2 : (∫ θ in Work.Spaces.Iθ, |sg θ * (f θ * g θ)|)
      ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2) * ((f θ) ^ 2 * sg θ + (g θ) ^ 2 * sg θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hint ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have hσ : 0 ≤ sg θ := Work.FTS.EllipticEst.Dispatch.sEta_nonneg_Iθ_D hθ
    change |sg θ * (f θ * g θ)| ≤ (1 / 2) * ((f θ) ^ 2 * sg θ + (g θ) ^ 2 * sg θ)
    rw [abs_mul, abs_of_nonneg hσ]
    calc sg θ * |f θ * g θ| = |f θ * g θ| * sg θ := by ring
      _ ≤ ((1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2)) * sg θ :=
          mul_le_mul_of_nonneg_right (abs_mul_le_half (a := f θ) (b := g θ)) hσ
      _ = (1 / 2) * ((f θ) ^ 2 * sg θ + (g θ) ^ 2 * sg θ) := by ring
  have hsplit : (∫ θ in Work.Spaces.Iθ, (1 / 2) * ((f θ) ^ 2 * sg θ + (g θ) ^ 2 * sg θ))
      = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * sg θ)
        + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * sg θ)) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hf hg]
  linarith [hstep1, hstep2, hsplit]

/-- A weighted comparison bound: a coefficient bounded by `C w²` pairs against a nonnegative
slice mass. -/
private theorem weighted_le_of_bound {c m : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * m z) Work.Spaces.Iz)
    (hmnn : ∀ z, 0 ≤ m z)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |c z| ≤ C * (Work.Spaces.w z) ^ 2) :
    |∫ z in Work.Spaces.Iz, c z * m z| ≤ C * (∫ z in Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * m z) := by
  have hstep1 : |∫ z in Work.Spaces.Iz, c z * m z|
      ≤ ∫ z in Work.Spaces.Iz, |c z * m z| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun z => c z * m z)
  have hint : MeasureTheory.IntegrableOn
      (fun z => C * ((Work.Spaces.w z) ^ 2 * m z)) Work.Spaces.Iz := hmint.const_mul C
  have hstep2 : (∫ z in Work.Spaces.Iz, |c z * m z|)
      ≤ ∫ z in Work.Spaces.Iz, C * ((Work.Spaces.w z) ^ 2 * m z) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => abs_nonneg _) hint ?_
    filter_upwards [hbound] with z hz
    rw [abs_mul]
    calc |c z| * |m z| ≤ (C * (Work.Spaces.w z) ^ 2) * m z :=
          mul_le_mul hz (by rw [abs_of_nonneg (hmnn z)]) (abs_nonneg _)
            (mul_nonneg hC (sq_nonneg _))
      _ = C * ((Work.Spaces.w z) ^ 2 * m z) := by ring
  have hsplit : (∫ z in Work.Spaces.Iz, C * ((Work.Spaces.w z) ^ 2 * m z))
      = C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * m z) :=
    MeasureTheory.integral_const_mul C _
  linarith [hstep1, hstep2, hsplit]

/-- Slice integrability of the `σ`-weighted square from `HkMem`. -/
private theorem sliceIntegrable_of_HkMem {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * sg θ) Work.Spaces.Iθ := by
  have h := hg.1 z (Set.mem_Ici.mpr hz.le)
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have h1 : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    positivity
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 0 g z θ)
      Work.Spaces.Iθ := h.const_mul _
  refine h1.congr_fun ?_ measurableSet_Icc
  intro θ hθ
  change ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 0 g z θ = (g z θ) ^ 2 * sg θ
  have hwz : Work.Spaces.w z ≠ 0 := by
    intro h0
    exact hw (by rw [h0]; norm_num)
  rw [HkIntegrand_eq α g hθ]
  field_simp

/-- The `θ`-integral of the level-`0` integrand at level `0`. -/
private theorem integral_HkIntegrand_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * sg θ) := by
  rw [← MeasureTheory.integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => HkIntegrand_eq α g hθ)

/-- `cut n` is `C²`. -/
private theorem cutSeq_contDiff_two (n : ℕ) : ContDiff ℝ 2 (Work.FTS.EllipticEst.cut n) := by
  have h := Work.FTS.EllipticEst.cut_contDiff n
  rw [Work.Stability.smoothOrder] at h
  exact h.of_le (WithTop.coe_le_coe.mpr le_top)

/-- The cut-off family of the truncation argument. -/
private theorem cutSeq : ∃ (χ : ℕ → ℝ → ℝ) (C : ℝ), 0 < C ∧
    (∀ n : ℕ, ContDiff ℝ 2 (χ n)) ∧
    (∀ (n : ℕ) (z : ℝ), 0 ≤ χ n z ∧ χ n z ≤ 1) ∧
    (∀ (n : ℕ) (z : ℝ), z ∉ Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) → χ n z = 0) ∧
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun n : ℕ => χ n z) Filter.atTop (nhds 1)) ∧
    (∀ (n : ℕ) (z : ℝ), 0 < z →
      |deriv (deriv (fun z' => χ n z' * (Work.Spaces.w z') ^ 2 * z' ^ 2)) z|
        ≤ C * (Work.Spaces.w z) ^ 2) ∧
    (∀ (n : ℕ) (z : ℝ), 0 < z →
      |deriv (fun z' => χ n z' * (Work.Spaces.w z') ^ 2 * z') z| ≤ C * (Work.Spaces.w z) ^ 2) := by
  obtain ⟨K, hKpos, hK1, hKlim, _hK0⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  obtain ⟨K2, hK2pos, hK2bd⟩ := Work.FTS.EllipticEst.AngularW.cutZ2Deriv2
  refine ⟨fun n => Work.FTS.EllipticEst.cut n, K2 + 4 * K + 6 + (K + 3),
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have h := Work.FTS.EllipticEst.cut_contDiff n
    rw [Work.Stability.smoothOrder] at h
    exact h.of_le (WithTop.coe_le_coe.mpr le_top)
  · intro n z
    exact ⟨Work.FTS.EllipticEst.cut_nonneg n z, Work.FTS.EllipticEst.cut_le_one n z⟩
  · intro n z hz
    rcases not_and_or.mp hz with h | h
    · exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt (not_le.mp h))
    · exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt (not_le.mp h))
  · intro z hz
    exact hKlim z hz
  · intro n z hz
    have h1 := deriv_deriv_WcutZ2_le (χ := Work.FTS.EllipticEst.cut n) (K := K) (K₂ := K2)
      (cutSeq_contDiff_two n) (fun z => Work.FTS.EllipticEst.cut_nonneg n z)
      (fun z => Work.FTS.EllipticEst.cut_le_one n z) (fun z => hK1 n z) (fun z => hK2bd n z) z hz
    calc |deriv (deriv (fun z' => Work.FTS.EllipticEst.cut n z' * (Work.Spaces.w z') ^ 2 * z' ^ 2)) z|
        = |deriv (deriv (Work.FTS.EllipticEst.Dispatch.WcutZ2 (Work.FTS.EllipticEst.cut n))) z| := by
          rfl
      _ ≤ (K2 + 4 * K + 6) * (Work.Spaces.w z) ^ 2 := h1
      _ ≤ (K2 + 4 * K + 6 + (K + 3)) * (Work.Spaces.w z) ^ 2 := by
          have h : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
          nlinarith [h]
  · intro n z hz
    have h1 := deriv_WcutZ_le (χ := Work.FTS.EllipticEst.cut n) (K := K)
      (cutSeq_contDiff_two n) (fun z => Work.FTS.EllipticEst.cut_nonneg n z)
      (fun z => Work.FTS.EllipticEst.cut_le_one n z) (fun z => hK1 n z) z hz
    calc |deriv (fun z' => Work.FTS.EllipticEst.cut n z' * (Work.Spaces.w z') ^ 2 * z') z|
        = |deriv (Work.FTS.EllipticEst.Dispatch.WcutZ (Work.FTS.EllipticEst.cut n)) z| := by rfl
      _ ≤ (K + 3) * (Work.Spaces.w z) ^ 2 := h1
      _ ≤ (K2 + 4 * K + 6 + (K + 3)) * (Work.Spaces.w z) ^ 2 := by
          have h : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
          nlinarith [h, hK2pos, hKpos]



/-! ## The final assembly -/

private theorem Lzero_slice_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero u z θ = Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ := by
  simp only [Work.Elliptic.Lzero, Work.FTS.EllipticEst.Lzero1, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- Almost every point of `Iz` is positive. -/
private theorem ae_pos_of_mem_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-- **The dominated-convergence limit of the truncated radial energy.** -/
private theorem tendsto_radial (u : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hXint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)) Work.Spaces.Iz)
    (χ : ℕ → ℝ → ℝ) (hχdiff : ∀ n, ContDiff ℝ 2 (χ n))
    (hχ01 : ∀ n z, 0 ≤ χ n z ∧ χ n z ≤ 1)
    (hχlim : ∀ z, 0 < z → Filter.Tendsto (fun n => χ n z) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => ∫ z in Work.Spaces.Iz, χ n z * (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)) Filter.atTop
      (nhds (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ))) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)) ?_ hXint ?_ ?_
  · intro n
    have hpz : ContinuousOn (Function.uncurry (Work.Spaces.pz u))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Work.FTS.EllipticEst.smoothOpen_of_forall hsm).pz.forall 1).continuousOn
    have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)),
        0 < Real.sin (2 * p.2) := fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
    have hσcont : ContinuousOn (fun p : ℝ × ℝ => sg p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_sEta_Ioo.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 * sg p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((continuousOn_fst.mul hpz).pow 2).mul hσcont
    have h3 : AEStronglyMeasurable (fun z : ℝ =>
        ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    have h1 : AEStronglyMeasurable (fun z : ℝ => χ n z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      ((hχdiff n).continuous).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      refine Measurable.aestronglyMeasurable ?_
      show Measurable fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2
      fun_prop
    exact (h1.mul h2).mul h3
  · intro n
    filter_upwards with z
    have hφ : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hχ1 : χ n z ≤ 1 := (hχ01 n z).2
    have hmi : 0 ≤ ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
          mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Dispatch.sEta_nonneg_Iθ_D hθ)))
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hχ01 n z).1 hφ) hmi)]
    calc χ n z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)
        ≤ 1 * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ) := by
          refine mul_le_mul_of_nonneg_right ?_ hmi
          exact mul_le_mul_of_nonneg_right hχ1 hφ
      _ = (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ) := by ring
  · filter_upwards [ae_pos_of_mem_Iz] with z hz
    have h1 : Filter.Tendsto (fun n => χ n z * (Work.Spaces.w z) ^ 2) Filter.atTop
        (nhds (1 * (Work.Spaces.w z) ^ 2)) :=
      (hχlim z hz).mul tendsto_const_nhds
    have h2 := h1.mul_const (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)
    simpa only [one_mul] using h2
/-- **The `σ`-weighted radial energy inequality** in the almost-everywhere class. -/
theorem aeSigmaEnergyOwn : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
  obtain ⟨χ, C, hCpos, hχdiff, hχ01, hχsupp, hχlim, hχbd1, hχbd2⟩ := cutSeq
  obtain ⟨K, hKpos, hKcoer⟩ := Work.FTS.EllipticEst.Frontier.aeSigmaSliceLowerFts
  have hC0 : 0 ≤ C := le_of_lt hCpos
  have hK0 : 0 ≤ K := le_of_lt hKpos
  refine ⟨1 / 2 + K + C / 2 + 3 * C, by positivity, ?_⟩
  intro α u G hA
  have hα1 : α ≤ 1 := by have h := hA.hα4; linarith
  have hα0 : 0 ≤ α := le_of_lt hA.hα
  have hmu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
  have hmd : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hA
  obtain ⟨hUint, hUval⟩ := hksq_slice_eq hmu
  obtain ⟨hGint, hGval⟩ := hksq_slice_eq hA.memG
  obtain ⟨hXint, hXval⟩ := hksq_slice_eq hmd
  have hXint' : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)) Work.Spaces.Iz := by
    simpa only [Work.FTS.EllipticEst.H2W.Ae.grad] using hXint
  have hXval' : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ))
      = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
    simpa only [Work.FTS.EllipticEst.H2W.Ae.grad] using hXval
  -- ## the a.e. slice coercivity
  have hcoer : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      -(K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ))
        ≤ ∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ) := by
    have h0 := hKcoer α u G hA
    rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    filter_upwards [h0] with z hz
    have hz' : -(K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ))
        ≤ ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * u z θ * sg θ := by
      linarith [hz]
    have hconv : (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ))
        = ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * u z θ * sg θ :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [Lzero_slice_eq]; ring)
    rw [hconv]
    exact hz'
  -- ## (1) the source pairing
  have hB1 : ∀ n : ℕ, (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
        (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ)))
      ≤ (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    intro n
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ))|
          ≤ (1 / 2) * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * sg θ)
              + (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      have hτ := thetaPairing (f := fun θ => G z θ) (g := fun θ => u z θ)
        (sliceIntegrable_of_HkMem hA.memG hz) (sliceIntegrable_of_HkMem hmu hz)
      have hφ : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hχz := hχ01 n z
      calc |Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ))|
          = χ n z * (Work.Spaces.w z) ^ 2
            * |∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ)| := by
            rw [show Work.FTS.EllipticEst.Dispatch.om (χ n) z
                = χ n z * (Work.Spaces.w z) ^ 2 from rfl]
            rw [abs_mul, abs_of_nonneg (mul_nonneg hχz.1 hφ)]
        _ ≤ 1 * (Work.Spaces.w z) ^ 2 * ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * sg θ)
              + (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hχz.2 hφ) hτ (abs_nonneg _) ?_
            positivity
        _ = (1 / 2) * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * sg θ)
              + (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) := by ring
    have hmono : (∫ z in Work.Spaces.Iz, |Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ))|)
        ≤ ∫ z in Work.Spaces.Iz, (1 / 2) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * sg θ)
              + (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
        ((hGint.add hUint).const_mul (1 / 2)) hpt
    have hval : (∫ z in Work.Spaces.Iz, (1 / 2) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * sg θ)
              + (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)))
        = (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hGint hUint, hGval, hUval]
    have h1 : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ)))
        ≤ |∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ))| := le_abs_self _
    have h2 : |∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ))|
        ≤ ∫ z in Work.Spaces.Iz, |Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ))| := by
      simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
        (fun z => Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ)))
    linarith [h1, h2, hmono, hval]

  -- ## (2) the angular self-form term, via the slicewise coercivity
  have hB2 : ∀ n : ℕ, -(∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
        (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
      ≤ K * Work.Spaces.HkSq α 0 u := by
    intro n
    have hUaesm : AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have hU0 : Work.FTS.EllipticEst.SmoothOpen u :=
        Work.FTS.EllipticEst.smoothOpen_of_forall hA.smooth
      have hcont : ContinuousOn (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2 * sg p.2)
          Work.FTS.EllipticEst.Q0 :=
        (hU0.continuousOn.pow 2).mul
          (contDiffOn_sEta_Ioo.continuousOn.comp continuous_snd.continuousOn
            (fun p hp => hp.2))
      exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    have hχaesm : AEStronglyMeasurable (fun z : ℝ => χ n z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      ((hχdiff n).continuous).aestronglyMeasurable
    have hφaesm : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      refine Measurable.aestronglyMeasurable ?_
      show Measurable fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2
      fun_prop
    by_cases hint : MeasureTheory.Integrable
        (fun z => Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
    · have hneg : MeasureTheory.Integrable
          (fun z => -(Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ))))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := hint.neg
      have hmaj : MeasureTheory.Integrable
          (fun z => K * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := hUint.const_mul K
      have hχKint : MeasureTheory.Integrable
          (fun z => Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
        · exact (hχaesm.mul hφaesm).mul (hUaesm.const_mul K)
        · filter_upwards [ae_pos_of_mem_Iz] with z hz
          have hφ : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
          have hχz := hχ01 n z
          have hUz : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ :=
            sliceMass_nonneg u z
          rw [show Work.FTS.EllipticEst.Dispatch.om (χ n) z
              = χ n z * (Work.Spaces.w z) ^ 2 from rfl]
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hχz.1 hφ)
            (mul_nonneg hK0 hUz))]
          calc χ n z * (Work.Spaces.w z) ^ 2 * (K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ))
              ≤ 1 * (Work.Spaces.w z) ^ 2 * (K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) := by
                refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hK0 hUz)
                exact mul_le_mul_of_nonneg_right hχz.2 hφ
            _ = K * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) := by
                ring
      have hmono : (∫ z in Work.Spaces.Iz, -(Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ))))
          ≤ ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
              (K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) := by
        refine MeasureTheory.integral_mono_ae hneg hχKint ?_
        filter_upwards [hcoer] with z hz
        have hφ : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have hχz := hχ01 n z
        have hprod : 0 ≤ χ n z * (Work.Spaces.w z) ^ 2 := mul_nonneg hχz.1 hφ
        have hz' : -(Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
            = χ n z * (Work.Spaces.w z) ^ 2
              * (-(∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ))) := by
          rw [show Work.FTS.EllipticEst.Dispatch.om (χ n) z
              = χ n z * (Work.Spaces.w z) ^ 2 from rfl]
          ring
        rw [hz']
        refine mul_le_mul_of_nonneg_left ?_ hprod
        linarith [hz]
      have hval : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ))) ≤ K * Work.Spaces.HkSq α 0 u := by
        have h1 : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
              (K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)))
            ≤ ∫ z in Work.Spaces.Iz, K * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ (hUint.const_mul K) ?_
          · filter_upwards with z
            have hφ : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
            have hχz := hχ01 n z
            exact mul_nonneg (mul_nonneg hχz.1 hφ) (mul_nonneg hK0 (sliceMass_nonneg u z))
          · filter_upwards with z
            have hφ : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
            have hχz := hχ01 n z
            have hUz : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ := sliceMass_nonneg u z
            rw [show Work.FTS.EllipticEst.Dispatch.om (χ n) z
                = χ n z * (Work.Spaces.w z) ^ 2 from rfl]
            calc χ n z * (Work.Spaces.w z) ^ 2 * (K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ))
                ≤ 1 * (Work.Spaces.w z) ^ 2 * (K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) := by
                  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hK0 hUz)
                  exact mul_le_mul_of_nonneg_right hχz.2 hφ
              _ = K * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) := by
                  ring
        have h2 : (∫ z in Work.Spaces.Iz, K * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ))) = K * Work.Spaces.HkSq α 0 u := by
          rw [MeasureTheory.integral_const_mul, hUval]
        linarith [h1, h2]
      have h3 : -(∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
          = ∫ z in Work.Spaces.Iz, -(Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ))) := by
        rw [MeasureTheory.integral_neg]
      linarith [hmono, hval, h3]
    · have hzero : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ))) = 0 :=
        MeasureTheory.integral_undef hint
      have hpos : 0 ≤ K * Work.Spaces.HkSq α 0 u :=
        mul_nonneg hK0 (Work.Spaces.HkSq_nonneg α 0 u)
      rw [hzero]; linarith [hpos]
  -- ## (3) the `(z²w²)''` transfer term
  have hB3 : ∀ n : ℕ, (∫ z in Work.Spaces.Iz,
        deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
          (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) ≤ C * Work.Spaces.HkSq α 0 u := by
    intro n
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z| ≤ C * (Work.Spaces.w z) ^ 2 := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      exact hχbd1 n z hz
    have h := weighted_le_of_bound
      (c := fun z => deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z)
      (m := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ) (C := C) hC0 hUint
      (fun z => sliceMass_nonneg u z) hb
    have h2 : |∫ z in Work.Spaces.Iz,
        deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
          (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)| ≤ C * Work.Spaces.HkSq α 0 u := by
      simpa only [hUval] using h
    linarith [le_abs_self (∫ z in Work.Spaces.Iz,
      deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
        (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)), h2]
  -- ## (4) the `(zw²)'` transfer term
  have hB4 : ∀ n : ℕ, -(∫ z in Work.Spaces.Iz,
        deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
          (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)) ≤ C * Work.Spaces.HkSq α 0 u := by
    intro n
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z| ≤ C * (Work.Spaces.w z) ^ 2 := by
      filter_upwards [ae_pos_of_mem_Iz] with z hz
      exact hχbd2 n z hz
    have h := weighted_le_of_bound
      (c := fun z => deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z)
      (m := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ) (C := C) hC0 hUint
      (fun z => sliceMass_nonneg u z) hb
    have h2 : |∫ z in Work.Spaces.Iz,
        deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
          (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)| ≤ C * Work.Spaces.HkSq α 0 u := by
      simpa only [hUval] using h
    linarith [neg_le_abs (∫ z in Work.Spaces.Iz,
      deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
        (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ)), h2]
  -- ## the per-`n` bound
  have hkey : ∀ n : ℕ, α ^ 2 * (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Dispatch.om2 (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2))
      ≤ (1 / 2 + K + C / 2 + 3 * C) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    intro n
    have hχ0n : ∃ δ : ℝ, 0 < δ ∧ ∀ z, z ≤ δ → χ n z = 0 := by
      refine ⟨1 / (2 * ((n : ℝ) + 1)), by positivity, fun z hz => ?_⟩
      refine hχsupp n z ?_
      intro hmem
      have h1 : 1 / ((n : ℝ) + 1) ≤ z := hmem.1
      have h2n : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h3 : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        linarith
      have hzlt : z < 1 / ((n : ℝ) + 1) := lt_of_le_of_lt hz h3
      exact absurd hmem.1 (not_le.mpr hzlt)
    have hχcn : HasCompactSupport (χ n) := by
      have hsub : Function.support (χ n)
          ⊆ Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) := by
        intro z hz
        by_contra hz'
        exact hz (hχsupp n z hz')
      have hts : tsupport (χ n) ⊆ Set.Icc (1 / ((n : ℝ) + 1)) (3 * ((n : ℝ) + 1)) :=
        closure_minimal hsub isClosed_Icc
      exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hts
    have hid := sigId hA (hχdiff n) hχcn hχ0n (fun z => (hχ01 n z).1) (fun z => (hχ01 n z).2)
      (fun z hz => hχbd1 n z hz) (fun z hz => hχbd2 n z hz)
    have h1 : α ^ 2 * (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om2 (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2))
        = (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (G z θ * u z θ)))
          - (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Dispatch.om (χ n) z *
              (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
          + (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
                (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2))
          - ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
                (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2)) := by
      linarith [hid]
    have h1' := hB1 n
    have h2' := hB2 n
    have h3' := hB3 n
    have h4' := hB4 n
    have e1 : 0 ≤ α ^ 2 / 2 := by positivity
    have e2 : 0 ≤ (α * (5 + α)) / 2 := by nlinarith [hα0]
    have h3'c : (∫ z in Work.Spaces.Iz,
          deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2)) ≤ C * Work.Spaces.HkSq α 0 u := by
      rw [show (∫ z in Work.Spaces.Iz,
            deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
              (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2))
          = ∫ z in Work.Spaces.Iz,
            deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
              (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ) from by
        refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        congr 1
        exact (sliceMass_comm u z).symm]
      exact h3'
    have h4'c : -(∫ z in Work.Spaces.Iz,
          deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2)) ≤ C * Work.Spaces.HkSq α 0 u := by
      rw [show (∫ z in Work.Spaces.Iz,
            deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
              (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2))
          = ∫ z in Work.Spaces.Iz,
            deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
              (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * sg θ) from by
        refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        congr 1
        exact (sliceMass_comm u z).symm]
      exact h4'
    have h3'' : (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
          deriv (deriv (Work.FTS.EllipticEst.Dispatch.om2 (χ n))) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2))
        ≤ (α ^ 2 / 2) * (C * Work.Spaces.HkSq α 0 u) :=
      mul_le_mul_of_nonneg_left h3'c e1
    have h4'' : ((α * (5 + α)) / 2) * (-(∫ z in Work.Spaces.Iz,
          deriv (Work.FTS.EllipticEst.Dispatch.om1 (χ n)) z *
            (∫ θ in Work.Spaces.Iθ, sg θ * (u z θ) ^ 2)))
        ≤ ((α * (5 + α)) / 2) * (C * Work.Spaces.HkSq α 0 u) :=
      mul_le_mul_of_nonneg_left h4'c e2
    have hUnn := Work.Spaces.HkSq_nonneg α 0 u
    have hGnn := Work.Spaces.HkSq_nonneg α 0 G
    have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα1, hα0]
    have hα5 : α * (5 + α) ≤ 6 := by nlinarith [hα1, hα0]
    have hC1 : (α ^ 2 / 2) * (C * Work.Spaces.HkSq α 0 u) ≤ (C / 2) * Work.Spaces.HkSq α 0 u := by
      have hle : α ^ 2 / 2 * C ≤ C / 2 := by nlinarith [hα2, hC0]
      rw [show (α ^ 2 / 2) * (C * Work.Spaces.HkSq α 0 u)
          = (α ^ 2 / 2 * C) * Work.Spaces.HkSq α 0 u from by ring]
      exact mul_le_mul_of_nonneg_right hle hUnn
    have hC2 : ((α * (5 + α)) / 2) * (C * Work.Spaces.HkSq α 0 u)
        ≤ (3 * C) * Work.Spaces.HkSq α 0 u := by
      have hle : (α * (5 + α)) / 2 * C ≤ 3 * C := by nlinarith [hα5, hC0]
      rw [show ((α * (5 + α)) / 2) * (C * Work.Spaces.HkSq α 0 u)
          = ((α * (5 + α)) / 2 * C) * Work.Spaces.HkSq α 0 u from by ring]
      exact mul_le_mul_of_nonneg_right hle hUnn
    rw [h1]
    have hKc0 : 0 ≤ 1 / 2 + K + C / 2 + 3 * C := by linarith
    nlinarith [h1', h2', h3'', h4'', hC1, hC2, hGnn, hUnn, hKc0]
  -- ## the limit
  have hlim : Filter.Tendsto (fun n => α ^ 2 * (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Dispatch.om2 (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2)))
      Filter.atTop (nhds (α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))) := by
    have h0 : Filter.Tendsto (fun n => ∫ z in Work.Spaces.Iz, χ n z * (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ))
        Filter.atTop (nhds (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ))) := by
      have hbase : Filter.Tendsto (fun n => ∫ z in Work.Spaces.Iz, χ n z * (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ))
          Filter.atTop (nhds (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ))) :=
        tendsto_radial u hA.smooth hXint' χ hχdiff hχ01 hχlim
      exact hbase
    have h1 : (fun n => α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.Dispatch.om2 (χ n) z *
          (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2)))
        = fun n => α ^ 2 * (∫ z in Work.Spaces.Iz, χ n z * (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)) := by
      funext n
      congr 1
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      rw [show (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)
          = z ^ 2 * (∫ θ in Work.Spaces.Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2) from by
        rw [← MeasureTheory.integral_const_mul]
        exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
      rw [show Work.FTS.EllipticEst.Dispatch.om2 (χ n) z
          = χ n z * (Work.Spaces.w z) ^ 2 * z ^ 2 from rfl]
      ring
    rw [h1, ← hXval']
    exact h0.const_mul (α ^ 2)
  exact le_of_tendsto' hlim hkey


end Work.FTS.EllipticEst.AngAWeak
