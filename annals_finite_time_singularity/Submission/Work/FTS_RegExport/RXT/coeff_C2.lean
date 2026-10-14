import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.st1_stdata2
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.weakSliceZContinuousAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.VelLipAux.coeff_contDiffOn_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR7.VelLipAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The order-one elementary calculus on the open quadrant

These are the order-one counterparts of the `C²`-calculus lemmas of
`Work.FTS_RegExport.RXT.C2Assemble` (whose inputs are `C³` stream functions): the partial
derivatives lose exactly one order and `tan` is `C¹` on the open quadrant. -/

/-- `∂_z` on the open quadrant lowers the differentiability order by one. -/
theorem contDiffOn_uncurry_pz_one {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_pz_fin Work.FTS.EllipticEst.isOpen_Q0 hG

/-- `∂_θ` on the open quadrant lowers the differentiability order by one. -/
theorem contDiffOn_uncurry_pth_one {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth G)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0 hG

/-- `tan θ` is `C¹` on the open quadrant. -/
theorem contDiffOn_one_tan_Q0 :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 :=
  Work.FTS_RegExport.RXT.contDiffOn_tan_Q0.of_le (by norm_num)

/-- `Uop α Ψ = -3Ψ - α z ∂_zΨ` is `C¹` on the open quadrant for a `C²` stream function. -/
theorem contDiffOn_uncurry_Uop_one {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Uop α Ψ))
      Work.FTS.EllipticEst.Q0 := by
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_pz_one hΨ
  have h1 : ContDiffOn ℝ 1 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    hΨ.of_le (by norm_num)
  have h2 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => α * p.1 * Work.Spaces.pz Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := α)).mul contDiffOn_fst).mul hpz
  refine (((contDiffOn_const (c := (-3 : ℝ))).mul h1).sub h2).congr ?_
  intro p _
  simp only [Function.uncurry, Work.Construction.Uop]

/-- `Vop Ψ = ∂_θΨ - tan θ · Ψ` is `C¹` on the open quadrant for a `C²` stream function. -/
theorem contDiffOn_uncurry_Vop_one {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Vop Ψ))
      Work.FTS.EllipticEst.Q0 := by
  have hpth : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth Ψ))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_pth_one hΨ
  have h1 : ContDiffOn ℝ 1 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    hΨ.of_le (by norm_num)
  exact hpth.sub (contDiffOn_one_tan_Q0.mul h1)

/-- `sin (2θ)` is `C¹` on the open quadrant. -/
theorem contDiffOn_one_sin_two_Q0 :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
  (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn

/-- **`C¹`-regularity of the two R7 coefficient slices.**  From the `C²`-regularity of the
stream-function slice `slice Φ τ` on the open quadrant and the `C²`-regularity of the radial
profile `L₁₂(Ftau αG G τ)` on `(0,∞)`, the two transport coefficients `Vz7 αG μ G Φ · · τ` and
`Vθ7 αG Φ · · τ / sin(2θ)` are `C¹` (jointly in `(z,θ)`) on the open quadrant `Q0`.

Route: this is the order-1 shadow of the already-proved
`Work.FTS_RegExport.RXT.coeff_C2_assembly` (which is the order-2 statement and needs a `C³`
stream function). Unfold `Vz7 = (1 - μ τ) + L12(Ftau αG G τ)·c2m + 2αG·Vop Φ̃` with
`Φ̃ = PhiTil αG (Ftau αG G τ) (slice Φ τ)` and `Vθ7/sin 2θ = 2·Uop αG (slice Φ τ)/sin 2θ`:
* `Theta αG (Ftau αG G τ) = (1/(4αG))·sin(2θ)·L₁₂(Ftau αG G τ)(z)` is `C²` on `Q0` (product of a
  smooth `θ`-factor with the `C²` radial function `hL12`, pulled back along `fst`), so
  `Φ̃ = slice Φ τ − Theta` is `C²` there;
* `pth Φ̃` is therefore `C¹`, and `Vop Φ̃ = pth Φ̃ − tan θ · Φ̃` is `C¹`
  (`Work.FTS_RegExport.RXT.contDiffOn_tan_Q0`, and order-reduction lemmas such as
  `Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin`,
  `Work.FTS.StrongEps.contDiffOn_uncurry_pz_fin` — see `RXT/C2Assemble.lean`);
* `L₁₂(F)(z)·c2m θ` is `C¹` (indeed `C²`) since `L₁₂` is `C²` on `(0,∞)` and `c2m` is
  `C²` (`RXT.contDiffOn_c2m`);
* `Uop αG (slice Φ τ) = −3·slice Φ τ − αG·z·pz(slice Φ τ)` is `C¹` from `hΦ2` (the `z`-partial
  loses exactly one order), and division by `sin(2θ)` is legitimate on `Q0`
  (`RXT.sin_two_pos_Q0`).

The `αG ≠ 0` hypothesis is needed only for the constant `1/(4αG)` in `Theta`. -/
theorem coeff_contDiffOn_one {αG : ℝ} {μ : ℝ → ℝ}
    {G Φ : Work.FTS.Galerkin.Fam} {τ : ℝ} (hαG : αG ≠ 0)
    (hΦ2 : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice Φ τ))
      Work.FTS.EllipticEst.Q0)
    (hL12 : ContDiffOn ℝ 2
      (Work.Construction.L12 (Work.Construction.Ftau αG G τ)) (Set.Ioi 0)) :
    ContDiffOn ℝ 1 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ)) Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 1 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.Vθ7 αG Φ z θ τ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := by
  have hc2m : ContDiffOn ℝ 1 Work.Construction.c2m (Set.Ioo 0 (π / 2)) :=
    Work.FTS_RegExport.RXT.contDiffOn_c2m.of_le (by norm_num)
  -- `Θ` is `C²` on the open quadrant
  have hsin2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (1 / (4 * αG)) * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn)
  have hL12fst : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      Work.Construction.L12 (Work.Construction.Ftau αG G τ) p.1)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_slice_fst hL12
  have hTheta : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)))
      Work.FTS.EllipticEst.Q0 := by
    refine (hsin2.mul hL12fst).congr ?_
    intro p _
    simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  -- `Φ̃ = Φ - Θ` is `C²` on the open quadrant
  have hPsi : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.PhiTil αG
      (Work.Construction.Ftau αG G τ) (Work.FTS.Galerkin.slice Φ τ)))
      Work.FTS.EllipticEst.Q0 := hΦ2.sub hTheta
  have hVop : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Ftau αG G τ)
        (Work.FTS.Galerkin.slice Φ τ)))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_Vop_one hPsi
  have hUop : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Uop αG
      (Work.FTS.Galerkin.slice Φ τ))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_Uop_one hΦ2
  refine ⟨?_, ?_⟩
  · -- `Vz7`
    have hLmul : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
        Work.Construction.L12 (Work.Construction.Ftau αG G τ) p.1
          * Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS_RegExport.RXT.contDiffOn_slice_fst
        (hL12.of_le (by norm_num))).mul
        (hc2m.comp contDiffOn_snd (fun p hp => hp.2))
    have hV : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
        (2 * αG) * Work.Construction.Vop (Work.Construction.PhiTil αG
          (Work.Construction.Ftau αG G τ) (Work.FTS.Galerkin.slice Φ τ)) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul hVop
    refine (((contDiffOn_const (c := 1 - μ τ)).add hLmul).add hV).congr ?_
    intro p _
    simp only [Function.uncurry, Work.FTS.RegExportIface.Vz7,
      Work.FTS.RegExportIface.phiTil]
  · -- `Vθ7 / sin (2θ)`
    refine (((contDiffOn_const (c := (2 : ℝ))).mul hUop).div contDiffOn_one_sin_two_Q0
      (fun p hp => ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 hp))).congr ?_
    intro p _
    simp only [Pi.div_apply, Function.uncurry, Work.FTS.RegExportIface.Vθ7]

end Work.FTS_RegExport.RXR7.VelLipAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.CoeffCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.CoeffCore` — local helpers for `coeff_jets`

* `mixed` of a constant function, and scalar homogeneity of `mixed`;
* the derivative of the angular coefficient `c2m`;
* the `C²`-smoothness on the open quadrant of every *piece* of the three transport
  coefficients (the same assembly as `RXT.coeff_C2_assembly`, but exposing the pieces);
* the `Θ`-split `Uop α Φ = Uop α Φ̃ + Uop α (Θ α F_τ)` on the open quadrant.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR ΦR μR)
open Work.FTS_RegExport.RXT (v2_PhiT v2_SlotR v2_SlotV v2_SlotU)
open Work.FTS.Regularity (pExp)
open Work.Construction (L12 FK Ftau Theta Uop Vop Rop c2m Fstar)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## §1 `mixed` of constants and constant multiples -/

/-- `D_z`-iterates of a constant function. -/
theorem DzIter_const_fun (c : ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun _ _ : ℝ => c) = fun _ _ => if j = 0 then c else 0 := by
  induction j with
  | zero => simp
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        funext z θ
        simp [Work.Spaces.Dz, Work.Spaces.pz]
      · have hn0 : n ≠ 0 := by omega
        have hz : (fun _ _ : ℝ => (if n = 0 then c else 0)) = fun _ _ => (0 : ℝ) := by
          funext z θ; simp [hn0]
        rw [hz]
        funext z θ
        simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- `D_θ`-iterates of a constant function. -/
theorem DthIter_const_fun (c : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => c) = fun _ _ => if i = 0 then c else 0 := by
  induction i with
  | zero => simp
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]
      · have hn0 : n ≠ 0 := by omega
        have hz : (fun _ _ : ℝ => (if n = 0 then c else 0)) = fun _ _ => (0 : ℝ) := by
          funext z θ; simp [hn0]
        rw [hz]
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- The `mixed`-jets of a constant function are bounded by the constant. -/
theorem abs_mixed_const_le (c : ℝ) (j i : ℕ) (z θ : ℝ) :
    |Work.Spaces.mixed j i (fun _ _ : ℝ => c) z θ| ≤ |c| := by
  rw [Work.Spaces.mixed, DthIter_const_fun c i,
    DzIter_const_fun (if i = 0 then c else 0) j]
  by_cases hj : j = 0 <;> by_cases hi : i = 0 <;> simp [hj, hi]

/-- Scalar homogeneity of the mixed operator. -/
theorem coeff_mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  funext z θ
  simp only [Work.Spaces.mixed, Work.FTS.StrongEps.DthIter_const_mul c f i,
    Work.FTS.StrongEps.DzIter_const_mul c _ j]

/-- A constant multiple of a `mixed`-jet is bounded by `|c|` times a bound of the jet. -/
theorem abs_mixed_const_mul_le' {c M : ℝ} {f : ℝ → ℝ → ℝ} {j i : ℕ} {z θ : ℝ}
    (h : |Work.Spaces.mixed j i f z θ| ≤ M) :
    |Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ| ≤ |c| * M := by
  rw [coeff_mixed_const_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

/-- The nonnegative-`c` form of `abs_mixed_const_mul_le'`. -/
theorem abs_mixed_const_mul_le {c M : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ → ℝ} {j i : ℕ} {z θ : ℝ}
    (h : |Work.Spaces.mixed j i f z θ| ≤ M) :
    |Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ| ≤ c * M := by
  have := abs_mixed_const_mul_le' (c := c) h
  rwa [abs_of_nonneg hc] at this

/-- Additivity of the mixed operator in the *lambda* form (for `rw`). -/
theorem mixed_add_lam {f h : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 (Function.uncurry f) Q0)
    (hh : ContDiffOn ℝ 2 (Function.uncurry h) Q0)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hzθ : (z, θ) ∈ Q0) :
    Work.Spaces.mixed j i (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i h z θ :=
  mixed_add_pt hf hh hji hzθ

/-- A Lipschitz-type pointwise bound on a set gives continuity there. -/
theorem continuousOn_of_abs_sub_le {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) {s : Set ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ C * |x - y|) : ContinuousOn f s := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨ε / (C + 1), by positivity, ?_⟩
  intro y hy hxy
  have h2 : |y - x| < ε / (C + 1) := by
    have hxy' : dist y x < ε / (C + 1) := hxy
    rw [Real.dist_eq] at hxy'
    simpa [abs_sub_comm] using hxy'
  have h1 : |f y - f x| ≤ C * |y - x| := h y hy x hx
  have h3 : C * |y - x| ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (le_of_lt h2) hC
  have h4 : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ hC1]
    nlinarith
  have hgoal : dist (f y) (f x) < ε := by
    rw [Real.dist_eq]
    linarith
  simpa using hgoal

/-- The derivative of the angular coefficient `c2m` is bounded by `4`. -/
theorem abs_deriv_c2m_le (θ : ℝ) : |deriv c2m θ| ≤ 4 := by
  have hderiv1 : deriv (fun θ : ℝ => Real.cos (2 * θ)) θ = -2 * Real.sin (2 * θ) := by
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) θ).const_mul (2 : ℝ)
    have hcomp : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-(Real.sin (2 * θ) * 2)) θ := by
      simpa [Function.comp_def] using (Real.hasDerivAt_cos (2 * θ)).comp θ hlin
    rw [hcomp.deriv]
    ring
  have hderiv2 : deriv (fun θ : ℝ => Real.sin θ ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
    have hcomp : HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2)
        (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
    rw [hcomp.deriv]
    norm_num
  have h1 : DifferentiableAt ℝ (fun θ : ℝ => Real.cos (2 * θ)) θ := by fun_prop
  have h2 : DifferentiableAt ℝ (fun θ : ℝ => Real.sin θ ^ 2) θ := by fun_prop
  have h4 : deriv c2m θ = -3 * Real.sin (2 * θ) := by
    rw [show (c2m : ℝ → ℝ) = ((fun θ : ℝ => Real.cos (2 * θ))
      - (fun θ : ℝ => Real.sin θ ^ 2)) from by funext θ'; rfl]
    rw [deriv_sub h1 h2, hderiv1, hderiv2, Real.sin_two_mul]
    ring
  rw [h4, abs_mul, show |(-3 : ℝ)| = 3 by norm_num]
  have h5 : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  nlinarith [abs_nonneg (Real.sin (2 * θ))]

/-! ## §3 The `Θ`-split of `Uop` -/

/-- On the open quadrant, `Uop α Φ` splits along `Φ = Φ̃ + Θ`. -/
theorem uop_split_theta {g : Fam} {τ z θ : ℝ} (hzθ : (z, θ) ∈ Q0)
    (hPsi : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0)
    (hTheta : ContDiffOn ℝ 3 (Function.uncurry (Theta (pExp α)
      (Ftau (pExp α) (GR α g) τ))) Q0) :
    Uop (pExp α) (slice (ΦR α Φs E g) τ) z θ
      = Uop (pExp α) (v2_PhiT α Φs E g τ) z θ
        + Uop (pExp α) (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ := by
  have hfun : slice (ΦR α Φs E g) τ = fun z θ => v2_PhiT α Φs E g τ z θ
      + Theta (pExp α) (Ftau (pExp α) (GR α g) τ) z θ := by
    funext z' θ'
    simp only [Work.FTS.Galerkin.slice, v2_PhiT, Work.Construction.PhiTil]
    ring
  have hd1 : DifferentiableAt ℝ (fun z' => v2_PhiT α Φs E g τ z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hPsi.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt
        (by norm_num))
  have hd2 : DifferentiableAt ℝ (fun z' => Theta (pExp α)
      (Ftau (pExp α) (GR α g) τ) z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hTheta.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt
        (by norm_num))
  rw [hfun]
  simp only [Uop, Work.Spaces.pz]
  rw [show (fun z' : ℝ => (fun z θ => v2_PhiT α Φs E g τ z θ
        + Theta (pExp α) (Ftau (pExp α) (GR α g) τ) z θ) z' θ)
      = (fun z' => v2_PhiT α Φs E g τ z' θ)
        + (fun z' => Theta (pExp α) (Ftau (pExp α) (GR α g) τ) z' θ) from rfl,
    deriv_add hd1 hd2]
  ring

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.CoeffSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.CoeffSmooth` — the `C²`-regularity of the coefficient pieces

Every *piece* of the three transport coefficients (and the residual `Φ̃_τ` and the singular part
`Θ(F_τ)`) is `C²` (resp. `C³`) on the open quadrant.  This is the assembly of
`RXT.coeff_C2_assembly` with the pieces exposed, and it is stated as an explicit list of
conjuncts so that the bound lemmas of `Sys.CoeffBounds` can consume the ones they need.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR ΦR μR)
open Work.FTS_RegExport.RXT (v2_PhiT v2_SlotR v2_SlotV v2_SlotU)
open Work.FTS.Regularity (pExp)
open Work.Construction (L12 FK Ftau Theta Uop Vop Rop c2m Fstar)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- `K` is continuous on the closed angular interval (the weight of `𝔽K`). -/
theorem sys_continuousOn_K_Iθ : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
  ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn

/-! ## §2 Smoothness of the pieces -/

/-- Every piece of the three transport coefficients is `C²` on the open quadrant. -/
theorem coeff_pieces_contDiffOn {g : Fam} {τ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    (hτ : 0 ≤ τ) :
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * pExp α
        * Vop (v2_PhiT α Φs E g τ) z θ)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z
        * c2m θ)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z
        / pExp α)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (Real.sin θ) ^ 2
        * FK (Ftau (pExp α) (GR α g) τ) z)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Rop (pExp α)
        (v2_PhiT α Φs E g τ) z θ)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ))) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ))) Q0 ∧
      ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0 ∧
      ContDiffOn ℝ 3 (Function.uncurry (Theta (pExp α) (Ftau (pExp α) (GR α g) τ))) Q0 := by
  have hαG : (0 : ℝ) < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hΦ3 := Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) hEL3 hStar hOK τ hτ
  have hF2 := Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (C₀ := C₀) hα hα13 hOK τ hτ
  obtain ⟨Cf, hCf0, hbd⟩ := Work.FTS_RegExport.RXT.Ftau_bounds (C₀ := C₀) hα hα13 hOK τ hτ
  have hFK2 : ContDiffOn ℝ 2 (FK (Ftau (pExp α) (GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      sys_continuousOn_K_Iθ hF2 hbd
  have hL12 : ContDiffOn ℝ 3 (L12 (Ftau (pExp α) (GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2
  have hL2 : ContDiffOn ℝ 2 (L12 (Ftau (pExp α) (GR α g) τ)) (Set.Ioi 0) :=
    hL12.of_le (by norm_num)
  have hsin2θ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hsin3 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hsin2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Q0 :=
    ((Real.contDiff_sin.contDiffOn).pow 2).comp contDiffOn_snd (fun p hp => hp.2)
  have hTheta : ContDiffOn ℝ 3 (Function.uncurry (Theta (pExp α)
      (Ftau (pExp α) (GR α g) τ))) Q0 := by
    have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (1 / (4 * pExp α)) * Real.sin (2 * p.2)) Q0 :=
      contDiffOn_const.mul hsin3
    have h2 := Work.FTS_RegExport.RXT.contDiffOn_slice_fst hL12
    refine (h1.mul h2).congr ?_
    intro p _
    simp only [Function.uncurry, Theta, Work.Construction.s2]
  have hPsi : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0 := by
    have h := hΦ3.sub hTheta
    refine h.congr ?_
    intro p _
    simp only [Function.uncurry, Pi.sub_apply, v2_PhiT, Work.Construction.PhiTil]
  -- the radial and angular pieces, in uncurried form
  have hLmul : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      L12 (Ftau (pExp α) (GR α g) τ) p.1 * c2m p.2) Q0 :=
    (Work.FTS_RegExport.RXT.contDiffOn_slice_fst hL2).mul
      (Work.FTS_RegExport.RXT.contDiffOn_c2m.comp contDiffOn_snd (fun p hp => hp.2))
  have hLf : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      L12 (Ftau (pExp α) (GR α g) τ) p.1) Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_slice_fst hL2
  have hLdiv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      L12 (Ftau (pExp α) (GR α g) τ) p.1 / pExp α) Q0 :=
    hLf.div_const (pExp α)
  have hFKmul : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (Real.sin p.2) ^ 2
      * FK (Ftau (pExp α) (GR α g) τ) p.1) Q0 :=
    hsin2.mul (hFK2.comp contDiffOn_fst (fun p hp => hp.1))
  have hVop := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hPsi
  have hUop := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (α := pExp α) hPsi
  have hUopT := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (α := pExp α) hTheta
  have hRop := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop (α := pExp α) hPsi
  have hV2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ) * pExp α
      * Vop (v2_PhiT α Φs E g τ) p.1 p.2) Q0 :=
    contDiffOn_const.mul hVop
  have hR2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ)
      * Rop (pExp α) (v2_PhiT α Φs E g τ) p.1 p.2) Q0 :=
    contDiffOn_const.mul hRop
  have hUdiv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ) * Uop (pExp α)
      (v2_PhiT α Φs E g τ) p.1 p.2 / Real.sin (2 * p.2)) Q0 :=
    (contDiffOn_const.mul hUop).div hsin2θ
      (fun p hp => ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 hp))
  have hUdivT : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ) * Uop (pExp α)
      (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) p.1 p.2 / Real.sin (2 * p.2)) Q0 :=
    (contDiffOn_const.mul hUopT).div hsin2θ
      (fun p hp => ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 hp))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hPsi, hTheta⟩
  · refine ((contDiffOn_const (c := 1 - μR α Φs E g τ)).add hLmul).congr ?_
    intro p _
    simp only [Function.uncurry, Pi.add_apply]
  · refine hV2.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hLmul.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hLf.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hLdiv.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine ((contDiffOn_const (c := 1 + μR α Φs E g τ)).sub hLdiv).congr ?_
    intro p _
    simp only [Function.uncurry, Pi.sub_apply]
  · refine hFKmul.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine (((contDiffOn_const (c := 1 + μR α Φs E g τ)).sub hLdiv).add hFKmul).congr ?_
    intro p _
    simp only [Function.uncurry, Pi.add_apply, Pi.sub_apply]
  · refine hR2.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hUdiv.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hUdivT.congr ?_
    intro p _
    simp only [Function.uncurry]

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.GdotExp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.GdotExp` -- the expansion of the transport operator (S5b, core)

`mixed_transport_expand`: the Leibniz expansion of `D_z^j D_θ^i` applied to the transport
expression `a·D_zX + d·D_θX + c·X`, in the *shifted* form in which the principal parts are
`a·mixed (j+1) i X` and `d·mixed j (i+1) X`.  This is the finite-order (`C²`/`C³`) instance of
the iterated Leibniz rule for the two derivation-like operators `D_z = z ∂_z`, `D_θ = sin 2θ ∂_θ`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7 ω phiTil)
open Work.FTS.RegExportIface.RXT (VR bR cR SigR μR GR ΦR idx)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## The expansion of the transport operator on the jets -/

/-! ## The expansion of the transport operator on the jets -/

theorem mixed_transport_expand {a d c X : ℝ → ℝ → ℝ}
    (ha : ContDiffOn ℝ 2 (Function.uncurry a) Q0)
    (hd : ContDiffOn ℝ 2 (Function.uncurry d) Q0)
    (hc : ContDiffOn ℝ 2 (Function.uncurry c) Q0)
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) Q0)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ
        + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ) z θ
      = (∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
          ((i.choose u : ℝ) * (j.choose v : ℝ)) *
            (Work.Spaces.mixed v u a z θ * Work.Spaces.mixed (j - v + 1) (i - u) X z θ))
        + (∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
            ((i.choose u : ℝ) * (j.choose v : ℝ)) *
              (Work.Spaces.mixed v u d z θ * Work.Spaces.mixed (j - v) (i - u + 1) X z θ))
        + (∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
            ((i.choose u : ℝ) * (j.choose v : ℝ)) *
              (Work.Spaces.mixed v u c z θ * Work.Spaces.mixed (j - v) (i - u) X z θ)) := by
  have hzθ : (z, θ) ∈ Q0 := Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hX2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.Dz X)) Q0 :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_Dz_of_succ
      Work.FTS.EllipticEst.isOpen_Q0 hX
  have hX2' : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.Dth X)) Q0 :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_Dth_of_succ
      Work.FTS.EllipticEst.isOpen_Q0 hX
  have hX2'' : ContDiffOn ℝ 2 (Function.uncurry X) Q0 := hX.of_le (by norm_num)
  have hu1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => a z θ * Work.Spaces.Dz X z θ)) Q0 :=
    ha.mul hX2
  have hu2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => d z θ * Work.Spaces.Dth X z θ)) Q0 :=
    hd.mul hX2'
  have hu3 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => c z θ * X z θ)) Q0 := hc.mul hX2''
  have hadd : Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ
        + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ) z θ
      = Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ) z θ
        + Work.Spaces.mixed j i (fun z θ => d z θ * Work.Spaces.Dth X z θ) z θ
        + Work.Spaces.mixed j i (fun z θ => c z θ * X z θ) z θ := by
    rw [show (fun z θ : ℝ => a z θ * Work.Spaces.Dz X z θ
          + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ)
        = ((fun z θ => a z θ * Work.Spaces.Dz X z θ)
            + (fun z θ => d z θ * Work.Spaces.Dth X z θ))
          + (fun z θ => c z θ * X z θ) from rfl]
    have h12 : ContDiffOn ℝ 2 (Function.uncurry ((fun z θ => a z θ * Work.Spaces.Dz X z θ)
        + (fun z θ => d z θ * Work.Spaces.Dth X z θ))) Q0 := hu1.add hu2
    rw [mixed_add_pt h12 hu3 (Nat.add_comm j i ▸ hji) hzθ]
    rw [mixed_add_pt hu1 hu2 (Nat.add_comm j i ▸ hji) hzθ]
  have hexp1 : Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ) z θ
      = ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
          ((i.choose u : ℝ) * (j.choose v : ℝ)) *
            (Work.Spaces.mixed v u a z θ * Work.Spaces.mixed (j - v + 1) (i - u) X z θ) := by
    rw [GdotAux.mixed_mul_le2 ha hX2 hji hz hθ0 hθ1]
    apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro v hv
    rw [GdotAux.mixed_Dz_shift hX (p := j - v) (q := i - u) (by
      have hu' : u ≤ i := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hu
      have hv' : v ≤ j := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv
      omega) hz hθ0 hθ1]
    try ring
  have hexp2 : Work.Spaces.mixed j i (fun z θ => d z θ * Work.Spaces.Dth X z θ) z θ
      = ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
          ((i.choose u : ℝ) * (j.choose v : ℝ)) *
            (Work.Spaces.mixed v u d z θ * Work.Spaces.mixed (j - v) (i - u + 1) X z θ) := by
    rw [GdotAux.mixed_mul_le2 hd hX2' hji hz hθ0 hθ1]
    apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro v hv
    rw [mixed_Dth_succ (j - v) (i - u) X]
  have hexp3 : Work.Spaces.mixed j i (fun z θ => c z θ * X z θ) z θ
      = ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1),
          ((i.choose u : ℝ) * (j.choose v : ℝ)) *
            (Work.Spaces.mixed v u c z θ * Work.Spaces.mixed (j - v) (i - u) X z θ) :=
    GdotAux.mixed_mul_le2 hc hX2'' hji hz hθ0 hθ1
  rw [hadd, hexp1, hexp2, hexp3]
  try ring


end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.RHSDefs` — the `(E)`-form of the equation

The profile `F(σ)`, the right-hand side `RHS σ = −(Vz·D_zF + bR·D_θF + cs·F)`, and the identity
`gdot g σ = RHS σ` on the open quadrant, from the hypothesis `hEqF` (the `(E)`-form of the
equation as produced by RX-R7/S5a).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! ## §2 The `(E)`-form of the equation and the right-hand side `RHS` -/

/-- The `τ`-slice of the extended profile `F_* + g̃(·,·,σ)` (`g̃` the `extG`-extension of the
sanitised family). -/
noncomputable def profExt (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.Regularity.profFull α
    (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ σ

@[simp] theorem profExt_apply (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ z θ : ℝ) :
    profExt α g σ z θ = Work.FTS.Regularity.profFull α
      (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ σ := rfl

/-- The profile `F(σ) = F_* + gS α (tauExt g)(σ)` at fake time `σ`. -/
noncomputable def FtauS (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
    (Work.FTS.RegExportIface.RXT.GR α g) σ

@[simp] theorem FtauS_apply (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ z θ : ℝ) :
    FtauS α g σ z θ = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + Work.FTS.RegExportIface.RXT.GR α g z θ σ := rfl

/-- **The right-hand side** `−(Vz·D_zF + bR·D_θF + cs·F)` of the `(E)`-form of the equation,
with `F = F(σ)` and `D_θ = sin(2θ)·∂_θ` (so that no division by `sin 2θ` occurs). -/
noncomputable def RHS (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    - ( Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ
          * Work.Spaces.Dz (FtauS α g σ) z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
          * Work.Spaces.Dth (FtauS α g σ) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * FtauS α g σ z θ )

@[simp] theorem RHS_apply (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ z θ : ℝ) :
    RHS α Φs E g σ z θ
      = - ( Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ
              * Work.Spaces.Dz (FtauS α g σ) z θ
            + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * Work.Spaces.Dth (FtauS α g σ) z θ
            + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * FtauS α g σ z θ ) := rfl

/-- The extended profile agrees with `F(σ)` on the open quadrant. -/
theorem profExt_eq_FtauS {α : ℝ} {g : Work.FTS.Galerkin.Fam} {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ z θ : ℝ, 0 < z → profExt α g σ z θ = FtauS α g σ z θ := by
  intro z θ hz
  rw [profExt_apply, Work.FTS.Regularity.profFull_apply, FtauS_apply,
    Work.FTS.RegPkgGal.extG_of_pos hz hσ]

/-- The `z`-partials of the two profiles agree at every interior point (they agree on `z > 0`). -/
theorem pz_profExt_eq {α : ℝ} {g : Work.FTS.Galerkin.Fam} {σ : ℝ} (hσ : 0 ≤ σ) {z θ : ℝ}
    (hz : 0 < z) :
    Work.Spaces.pz (profExt α g σ) z θ = Work.Spaces.pz (FtauS α g σ) z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact profExt_eq_FtauS (α := α) (g := g) hσ z' θ hz'

/-- The `θ`-partials of the two profiles agree at every interior point (they agree on
`0 < θ < π/2`). -/
theorem pth_profExt_eq {α : ℝ} {g : Work.FTS.Galerkin.Fam} {σ : ℝ} (hσ : 0 ≤ σ) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.Spaces.pth (profExt α g σ) z θ = Work.Spaces.pth (FtauS α g σ) z θ := by
  rw [Work.Spaces.pth, Work.Spaces.pth]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ, hθπ⟩] with θ' hθ'
  exact profExt_eq_FtauS (α := α) (g := g) hσ z θ' hz

/-- **The `τ`-derivative of the profile is the right-hand side.**  From the `(E)`-form of the
equation (`hEqF`, with `Vθ7 = bR·sin 2θ` and `D_θ = sin 2θ·∂_θ`), on the open quadrant. -/
theorem gdot_eq_RHS {α S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hEqF : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => profExt α g s z θ)
        (-(Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ
            * Work.Spaces.Dz (profExt α g τ) z θ
          + Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (profExt α g τ) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ
            * profExt α g τ z θ)) τ) :
    ∀ z θ σ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < σ → σ ≤ S →
      Work.FTS.Galerkin.gdot g σ z θ = RHS α Φs E g σ z θ := by
  intro z θ σ hz hθ hθπ hσ hσS
  have hσ0 : 0 ≤ σ := hσ.le
  have hsin : Real.sin (2 * θ) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  -- (1) the `τ`-derivative of the extension is `gdot`
  have hderiv : deriv (fun s => profExt α g s z θ) σ = Work.FTS.Galerkin.gdot g σ z θ := by
    have hfun : (fun s => profExt α g s z θ)
        =ᶠ[nhds σ] (fun s => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + g z θ s) := by
      filter_upwards [isOpen_Ioi.mem_nhds hσ] with s hs
      rw [profExt_apply, Work.FTS.Regularity.profFull_apply,
        Work.FTS.RegPkgGal.extG_of_pos hz hs.le,
        Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hs.le hz hθ.le hθπ.le]
    rw [hfun.deriv_eq, deriv_const_add]
    rfl
  -- (2) the jet conversions
  have hDz : Work.Spaces.Dz (profExt α g σ) z θ
      = Work.Spaces.Dz (FtauS α g σ) z θ := by
    rw [Work.Spaces.Dz, Work.Spaces.Dz, pz_profExt_eq (α := α) (g := g) hσ0 hz]
  have hpth : Work.Spaces.pth (profExt α g σ) z θ
      = Work.Spaces.pth (FtauS α g σ) z θ := pth_profExt_eq hσ0 hz hθ hθπ
  have hval : profExt α g σ z θ = FtauS α g σ z θ := profExt_eq_FtauS hσ0 z θ hz
  have hDth : Work.Spaces.Dth (FtauS α g σ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (FtauS α g σ) z θ := rfl
  have e2 : Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
        * Work.Spaces.pth (profExt α g σ) z θ
      = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        * Work.Spaces.Dth (FtauS α g σ) z θ := by
    have hVθ : Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
        = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ * Real.sin (2 * θ) := by
      simp only [Work.FTS.RegExportIface.RXT.bR]
      rw [div_mul_cancel₀ _ hsin]
    rw [hVθ, hpth, hDth]
    ring
  have hh := (hEqF z θ σ hz hθ hθπ hσ hσS).deriv
  rw [hderiv] at hh
  rw [hh, hDz, e2, hval, RHS_apply]

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.coeff_C2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.coeff_C2` — S4: spatial `C²` of the coefficient slices

The three transport coefficients `VR`, `bR`, `cR` of `(E)` are jointly `C²` in `(z,θ)` on the
open quadrant `Q0`, for every `τ ≥ 0`.  The inputs are

* `psiCan_C3` (the stream function is `C³`, `C2Psi.contDiffOn_slice_PhiR_Q0`);
* `LimApprox` + the class-`C` interior trade-off (`MixedUniform.mixed_uniform`), which give
  uniform bounds for `F(τ) = F_* + g(τ)` and its `D_z`-derivatives (`Ftau_bounds`);
* the parametric-integral lemma `contDiffOn_two_integral_Itheta` (`𝔽K(F(τ))` is `C²`) and
  the primitive lemma `contDiffOn_succ_integral_Ioi` (`L₁₂(F(τ))` is `C³`, `C2Radial`).

The assembly is `C2Final.coeff_C2_assembly`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR ΦR μR VR bR cR)

set_option autoImplicit false

theorem continuousOn_K_Iθ : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
  ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn

theorem coeff_C2 {α C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαGne : Work.FTS.Regularity.pExp α ≠ 0 := ne_of_gt hαG
  have hΦ3 := contDiffOn_slice_PhiR_Q0 (α := α) hEL3 hStar hOK τ hτ
  have hF2 := contDiffOn_Ftau_Q0 (C₀ := C₀) hα hα13 hOK τ hτ
  obtain ⟨C, hC0, hbd⟩ := Ftau_bounds (C₀ := C₀) hα hα13 hOK τ hτ
  have hFK2 : ContDiffOn ℝ 2
      (Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ))
      (Set.Ioi 0) :=
    contDiffOn_two_integral_Itheta (φ := Work.Spaces.K) continuousOn_K_Iθ hF2 hbd
  have hL12 : ContDiffOn ℝ 3
      (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ))
      (Set.Ioi 0) := contDiffOn_three_L12 hFK2
  exact coeff_C2_assembly (α := α) (αG := Work.FTS.Regularity.pExp α) (C₀ := C₀) (Cs := Cs)
    hαGne hΦ3 hFK2 hL12

end Work.FTS_RegExport.RXT
end
end
