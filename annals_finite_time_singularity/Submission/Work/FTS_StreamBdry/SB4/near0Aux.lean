import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_RegExport.RXT.starUop
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.near0Aux` — auxiliary Lipschitz bounds for `near0`

The fragmentary Lipschitz bounds in the radial variable used by `Work.FTS_StreamBdry.SB4.near0`:

* `near0_lip_star` — the `U`-slot of the star summand `Φ̃_* = PhiTs αG Φs` is Lipschitz on `(0,1]`
  (from `RXT.starUop`, i.e. the `𝒲^{4,∞}`-bound of `StarPkgo2.UszW`);
* `near0_Uprime_thetaFstar`, `near0_lip_theta_fstar` — the explicit value of `U'(Θ(F_*))` and the
  resulting Lipschitz bound with constant `2`;
* `near0_hasDerivAt_Theta`, `near0_diff_pz_of_joint`, `near0_diff_pz_Theta` — radial
  differentiability of `Θ αG F` and of its `z`-derivative;
* `near0_lip_of_dz_bound` — a bound on `D_z` of `U'(Φ)` on `(0,1]` gives a Lipschitz bound for
  `U'(Φ)(·,θ)` (mean value inequality).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB4

set_option maxHeartbeats 800000

/-! ## §1 The star summand `Φ̃_*` -/

/-- **Lipschitz bound for the `U`-slot of the star summand.**  From the `𝒲^{4,∞}`-bound on
`((z+1)/z)·U'(Φ̃_*)` (`StarPkgo2.UszW`, via `RXT.starUop`) the `z`-derivative of `U'(Φ̃_*)`
is bounded by `C₁·(max Cs 1·αG)` on `(0,1]`, hence `U'(Φ̃_*)` is Lipschitz there. -/
lemma near0_lip_star {a Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn}
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.StreamBdryIface.Uprime (Work.FTS.Regularity.pExp a)
          (Work.FTS.Nonlin.PhiTs (Work.FTS.Regularity.pExp a) Φs) z θ
        - Work.FTS.StreamBdryIface.Uprime (Work.FTS.Regularity.pExp a)
          (Work.FTS.Nonlin.PhiTs (Work.FTS.Regularity.pExp a) Φs) z' θ|
        ≤ C * |z - z'| := by
  set αG := Work.FTS.Regularity.pExp a with hαGdef
  have hαG : 0 < αG := by rw [hαGdef, Work.FTS.Regularity.pExp]; linarith
  have hαG1 : αG ≤ 1 := by rw [hαGdef, Work.FTS.Regularity.pExp]; linarith
  obtain ⟨C1, hC1, hC1b⟩ := Work.FTS_RegExport.RXT.starUop hαG hαG1 hStar
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs αG Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hαG hαG1 hStar.smooth).1
  have hCnn : (0 : ℝ) ≤ C1 * (max Cs 1 * αG) :=
    mul_nonneg hC1 (mul_nonneg (le_trans zero_le_one (le_max_right Cs 1)) hαG.le)
  refine ⟨C1 * (max Cs 1 * αG), hCnn, ?_⟩
  intro z hz z' hz' θ hθ
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
    · -- the open quadrant
      have hdiff : ∀ w ∈ Set.Icc (min z z') (max z z'),
          DifferentiableAt ℝ (fun w' : ℝ => Work.FTS.StreamBdryIface.Uprime αG
            (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w := by
        intro w hw
        have hw0 : 0 < w := lt_of_lt_of_le (lt_min hz.1 hz'.1) hw.1
        have h1 : DifferentiableAt ℝ (fun w' : ℝ => Work.FTS.Nonlin.PhiTs αG Φs w' θ) w :=
          (hsm.hasDerivAt_slice ⟨hθ0, hθ2⟩ hw0).differentiableAt
        have h2 : DifferentiableAt ℝ
            (fun w' : ℝ => Work.Spaces.pz (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w :=
          ((hsm.pz).hasDerivAt_slice ⟨hθ0, hθ2⟩ hw0).differentiableAt
        have hA : DifferentiableAt ℝ (fun w' : ℝ => αG * w') w :=
          differentiableAt_id.const_mul αG
        have h3 : DifferentiableAt ℝ (fun w' : ℝ => -3 * Work.FTS.Nonlin.PhiTs αG Φs w' θ
            - αG * w' * Work.Spaces.pz (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w :=
          (h1.const_mul (-3)).sub (hA.mul h2)
        simpa only [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop] using
          h3.div_const (Work.Construction.s2 θ)
      have hbd : ∀ w ∈ Set.Icc (min z z') (max z z'),
          ‖deriv (fun w' : ℝ => Work.FTS.StreamBdryIface.Uprime αG
            (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w‖ ≤ C1 * (max Cs 1 * αG) := by
        intro w hw
        have hw0 : 0 < w := lt_of_lt_of_le (lt_min hz.1 hz'.1) hw.1
        have hwle : w ≤ 1 := le_trans hw.2 (max_le hz.2 hz'.2)
        have h := hC1b 1 0 (by norm_num) w θ hw0 hθ0 hθ2
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_zero, Work.Spaces.Dz, Work.Spaces.pz] at h
        rw [abs_mul, abs_of_pos hw0, min_eq_left hwle] at h
        rw [Real.norm_eq_abs]
        have h3 : |deriv (fun w' : ℝ => Work.FTS.StreamBdryIface.Uprime αG
              (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w| * w ≤ C1 * (max Cs 1 * αG) * w := by
          rwa [mul_comm w] at h
        exact (mul_le_mul_iff_of_pos_right hw0).mp h3
      have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd (convex_Icc _ _)
        (left_mem_Icc.mpr (min_le_max)) (right_mem_Icc.mpr (min_le_max))
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmain
      rcases le_total z z' with hle | hle
      · rw [max_eq_right hle, min_eq_left hle] at hmain
        calc |Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z θ
                - Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z' θ|
            = |Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z' θ
                - Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z θ| :=
              abs_sub_comm _ _
          _ ≤ C1 * (max Cs 1 * αG) * |z' - z| := hmain
          _ = C1 * (max Cs 1 * αG) * |z - z'| := by rw [abs_sub_comm z' z]
      · rw [max_eq_left hle, min_eq_right hle] at hmain
        exact hmain
    · -- θ = π/2
      have h0 : Work.Construction.s2 θ = 0 := by
        rw [Work.Construction.s2_eq, hθ2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
      exact mul_nonneg hCnn (abs_nonneg _)
  · -- θ = 0
    have h0 : Work.Construction.s2 θ = 0 := by
      rw [← hθ0, Work.Construction.s2_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
    simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
    exact mul_nonneg hCnn (abs_nonneg _)

/-! ## §2 The summand `Θ(F_*)` -/

/-- `U'(Θ(F_*))` has the explicit value `-3/(2(1+z)) + αG z/(2(1+z)²)`. -/
lemma near0_Uprime_thetaFstar {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
        = -(3 / 2) * (1 + z)⁻¹ + (αG / 2) * z * ((1 + z)⁻¹) ^ 2 := by
  intro z θ hzθ
  have hz : 0 < z := hzθ.1
  have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.s2_pos_of_Qd hzθ)
  have h1z : (1 + z) ≠ 0 := by positivity
  have hLz : Work.Construction.L12 (Work.Construction.Fstar αG) z = 2 * αG / (1 + z) :=
    Work.Construction.L12_Fstar_eq hαG hαG1 hz.le
  have hev : (fun w => Work.Construction.L12 (Work.Construction.Fstar αG) w)
      =ᶠ[𝓝 z] (fun w => 2 * αG / (1 + w)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact Work.Construction.L12_Fstar_eq hαG hαG1 hw.le
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-1 / (1 + z) ^ 2) z := h1.inv (by positivity)
  have h3 : HasDerivAt (fun y : ℝ => 2 * αG * (1 + y)⁻¹)
      (2 * αG * (-1 / (1 + z) ^ 2)) z := h2.const_mul _
  have h4 : (fun y : ℝ => 2 * αG / (1 + y)) = fun y : ℝ => 2 * αG * (1 + y)⁻¹ := by
    funext y; rw [div_eq_mul_inv]
  have h6 : HasDerivAt (fun y : ℝ => 2 * αG / (1 + y)) (-(2 * αG) / (1 + z) ^ 2) z := by
    have h3' := h3
    rw [← h4] at h3'
    have h7 : 2 * αG * (-1 / (1 + z) ^ 2) = -(2 * αG) / (1 + z) ^ 2 := by ring
    rw [h7] at h3'
    exact h3'
  have hL : HasDerivAt (fun w => Work.Construction.L12 (Work.Construction.Fstar αG) w)
      (-(2 * αG) / (1 + z) ^ 2) z :=
    (Filter.EventuallyEq.hasDerivAt_iff hev).2 h6
  have hpz' : deriv (fun w => 1 / (4 * αG) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar αG) w) z
      = 1 / (4 * αG) * Work.Construction.s2 θ * (-(2 * αG) / (1 + z) ^ 2) :=
    (hL.const_mul (1 / (4 * αG) * Work.Construction.s2 θ)).deriv
  simp only [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop, Work.Construction.Theta,
    Work.Spaces.pz]
  rw [hpz', hLz]
  field_simp
  ring

/-- **Lipschitz bound for the `U`-slot of `Θ(F_*)`.**  From the explicit value of `U'(Θ(F_*))`
one gets the Lipschitz constant `2` on `(0,1]`. -/
lemma near0_lip_theta_fstar {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1) :
    ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
        - Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z' θ|
        ≤ 2 * |z - z'| := by
  intro z hz z' hz' θ hθ
  have hz1 : 0 < z := hz.1
  have hz2 : z ≤ 1 := hz.2
  have hz'1 : 0 < z' := hz'.1
  have hz'2 : z' ≤ 1 := hz'.2
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
    · rw [near0_Uprime_thetaFstar hαG hαG1 z θ ⟨hz.1, hθ0, hθ2⟩,
        near0_Uprime_thetaFstar hαG hαG1 z' θ ⟨hz'.1, hθ0, hθ2⟩]
      have hz0 : (1 + z) ≠ 0 := by positivity
      have hz0' : (1 + z') ≠ 0 := by positivity
      have hkey1 : (1 + z)⁻¹ - (1 + z')⁻¹ = (z' - z) * (((1 + z) * (1 + z'))⁻¹) := by
        field_simp
        ring
      have hkey2 : z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2
          = (z - z') * (1 - z * z') * (((1 + z) ^ 2 * (1 + z') ^ 2)⁻¹) := by
        field_simp
        ring
      have hb1 : |((1 + z) * (1 + z'))⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)]
        nlinarith
      have hb2 : |(1 - z * z')| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith
      have hb3 : |((1 + z) ^ 2 * (1 + z') ^ 2)⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)]
        have h1 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith
        have h2 : (1 : ℝ) ≤ (1 + z') ^ 2 := by nlinarith
        nlinarith
      have e1 : |(1 + z)⁻¹ - (1 + z')⁻¹| ≤ |z - z'| := by
        rw [hkey1, abs_mul, abs_sub_comm z' z]
        calc |z - z'| * |((1 + z) * (1 + z'))⁻¹| ≤ |z - z'| * 1 :=
              mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
          _ = |z - z'| := mul_one _
      have e2 : |z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2| ≤ |z - z'| := by
        rw [hkey2, abs_mul, abs_mul]
        calc |z - z'| * |1 - z * z'| * |((1 + z) ^ 2 * (1 + z') ^ 2)⁻¹|
            ≤ |z - z'| * 1 * 1 := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hb2 (abs_nonneg _)) hb3
                (abs_nonneg _) ?_
              positivity
          _ = |z - z'| := by ring
      have hsplit : (-(3 / 2) * (1 + z)⁻¹ + (αG / 2) * z * ((1 + z)⁻¹) ^ 2)
            - (-(3 / 2) * (1 + z')⁻¹ + (αG / 2) * z' * ((1 + z')⁻¹) ^ 2)
          = (-(3 / 2)) * ((1 + z)⁻¹ - (1 + z')⁻¹)
            + (αG / 2) * (z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2) := by ring
      rw [hsplit]
      have h32 : |(-(3 / 2) : ℝ)| = 3 / 2 := by norm_num
      have hα2 : |αG / 2| = αG / 2 := abs_of_nonneg (by linarith)
      calc |(-(3 / 2)) * ((1 + z)⁻¹ - (1 + z')⁻¹)
            + (αG / 2) * (z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2)|
          ≤ |(-(3 / 2)) * ((1 + z)⁻¹ - (1 + z')⁻¹)|
            + |(αG / 2) * (z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2)| := abs_add_le _ _
        _ = (3 / 2) * |(1 + z)⁻¹ - (1 + z')⁻¹|
            + (αG / 2) * |z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2| := by
            rw [abs_mul, abs_mul, h32, hα2]
        _ ≤ (3 / 2) * |z - z'| + (αG / 2) * |z - z'| :=
            add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num))
              (mul_le_mul_of_nonneg_left e2 (by linarith))
        _ ≤ 2 * |z - z'| := by nlinarith [abs_nonneg (z - z')]
    · have h0 : Work.Construction.s2 θ = 0 := by
        rw [Work.Construction.s2_eq, hθ2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
      positivity
  · have h0 : Work.Construction.s2 θ = 0 := by
      rw [← hθ0, Work.Construction.s2_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
    simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
    positivity

/-! ## §3 Radial differentiability of the summands -/

/-- `Θ αG F` is differentiable in the radial variable as soon as `L12 F` is. -/
lemma near0_hasDerivAt_Theta {αG : ℝ} {F : ℝ → ℝ → ℝ} {θ z : ℝ}
    (h : DifferentiableAt ℝ (fun w => Work.Construction.L12 F w) z) :
    HasDerivAt (fun w => Work.Construction.Theta αG F w θ)
      (Work.Spaces.pz (Work.Construction.Theta αG F) z θ) z := by
  have hc : DifferentiableAt ℝ (fun w => 1 / (4 * αG) * Work.Construction.s2 θ
      * Work.Construction.L12 F w) z := h.const_mul _
  simpa only [Work.Construction.Theta, Work.Spaces.pz] using hc.hasDerivAt

/-- The radial slice of `∂_z Φ` is differentiable when `Φ` is jointly `C³` on the quadrant. -/
lemma near0_diff_pz_of_joint {Φ : ℝ → ℝ → ℝ} {θ w : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hw : 0 < w)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Φ) Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun w' => Work.Spaces.pz Φ w' θ) w := by
  have hslice : ContDiffOn ℝ 3 (fun w' => Φ w' θ) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθ h3
  have hd : ContDiffOn ℝ 2 (derivWithin (fun w' => Φ w' θ) (Set.Ioi 0)) (Set.Ioi 0) :=
    hslice.derivWithin (uniqueDiffOn_Ioi 0) (by norm_num)
  have hdiff : DifferentiableAt ℝ (derivWithin (fun w' => Φ w' θ) (Set.Ioi 0)) w :=
    (hd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hw)
  have hev : (fun w' => Work.Spaces.pz Φ w' θ) =ᶠ[𝓝 w]
      derivWithin (fun w' => Φ w' θ) (Set.Ioi 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with w' hw'
    simp only [Work.Spaces.pz, derivWithin_of_isOpen isOpen_Ioi hw']
  exact (hev.differentiableAt_iff).mpr hdiff

/-- Radial differentiability of `∂_z (Θ αG F)` from the differentiability of `L12dens F`. -/
lemma near0_diff_pz_Theta {αG : ℝ} {F : ℝ → ℝ → ℝ} {θ z : ℝ} (hz : 0 < z)
    (h : ∀ w : ℝ, 0 < w → HasDerivAt (fun w' => Work.Construction.L12 F w')
        (-(Work.Construction.L12dens F w)) w)
    (hd : ∀ w : ℝ, 0 < w → DifferentiableAt ℝ (fun w' => Work.Construction.L12dens F w') w) :
    DifferentiableAt ℝ (fun w' => Work.Spaces.pz (Work.Construction.Theta αG F) w' θ) z := by
  have hev : (fun w' => Work.Spaces.pz (Work.Construction.Theta αG F) w' θ)
      =ᶠ[𝓝 z] (fun w' => 1 / (4 * αG) * Work.Construction.s2 θ
        * (-(Work.Construction.L12dens F w'))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w' hw'
    rw [Work.Spaces.pz]
    show deriv (fun w'' => 1 / (4 * αG) * Work.Construction.s2 θ
        * Work.Construction.L12 F w'') w'
      = 1 / (4 * αG) * Work.Construction.s2 θ * (-(Work.Construction.L12dens F w'))
    rw [deriv_const_mul _ (h w' hw').differentiableAt, (h w' hw').deriv]
  have h2 : DifferentiableAt ℝ (fun w' => 1 / (4 * αG) * Work.Construction.s2 θ
      * (-(Work.Construction.L12dens F w'))) z := ((hd z hz).neg).const_mul _
  exact (hev.differentiableAt_iff).mpr h2

/-! ## §4 Lipschitz bounds from `D_z`-bounds -/

/-- A bound on the `D_z`-derivative of `U'(Φ)` on `(0,1]` gives a Lipschitz bound for
`U'(Φ)(·,θ)`, provided the slices are differentiable. -/
lemma near0_lip_of_dz_bound {αG C : ℝ} (hC : 0 ≤ C) {Φ : ℝ → ℝ → ℝ}
    (hdiff : ∀ w θ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w)
    (hbd : ∀ w θ, (w, θ) ∈ Work.Construction.Qd → w ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.FTS.StreamBdryIface.Uprime αG Φ z θ) w θ| ≤ C * w) :
    ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.FTS.StreamBdryIface.Uprime αG Φ z θ
        - Work.FTS.StreamBdryIface.Uprime αG Φ z' θ| ≤ C * |z - z'| := by
  intro z hz z' hz' θ hθ
  have hdiff' : ∀ w ∈ Set.Icc (min z z') (max z z'),
      DifferentiableAt ℝ (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (lt_min hz.1 hz'.1) hw.1
    exact hdiff w θ ⟨hw0, hθ.1, hθ.2⟩
  have hbd' : ∀ w ∈ Set.Icc (min z z') (max z z'),
      ‖deriv (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w‖ ≤ C := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (lt_min hz.1 hz'.1) hw.1
    have hwle : w ≤ 1 := le_trans hw.2 (max_le hz.2 hz'.2)
    have h := hbd w θ ⟨hw0, hθ.1, hθ.2⟩ hwle
    rw [Real.norm_eq_abs]
    have hD : Work.Spaces.Dz (fun z θ => Work.FTS.StreamBdryIface.Uprime αG Φ z θ) w θ
        = w * deriv (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w := by
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [hD, abs_mul, abs_of_pos hw0] at h
    have h3 : |deriv (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w| * w ≤ C * w := by
      rwa [mul_comm w] at h
    exact (mul_le_mul_iff_of_pos_right hw0).mp h3
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff' hbd' (convex_Icc _ _)
    (left_mem_Icc.mpr (min_le_max)) (right_mem_Icc.mpr (min_le_max))
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmain
  rcases le_total z z' with hle | hle
  · rw [max_eq_right hle, min_eq_left hle] at hmain
    calc |Work.FTS.StreamBdryIface.Uprime αG Φ z θ
            - Work.FTS.StreamBdryIface.Uprime αG Φ z' θ|
        = |Work.FTS.StreamBdryIface.Uprime αG Φ z' θ
            - Work.FTS.StreamBdryIface.Uprime αG Φ z θ| := abs_sub_comm _ _
      _ ≤ C * |z' - z| := hmain
      _ = C * |z - z'| := by rw [abs_sub_comm z' z]
  · rw [max_eq_left hle, min_eq_right hle] at hmain
    exact hmain


end Work.FTS_StreamBdry.SB4
