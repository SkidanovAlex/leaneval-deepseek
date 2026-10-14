import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.st1_stdata2
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.r7VelLip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Unfoldings of the operators at the slots used below -/

/-- `D_z f = z ∂_z f` at the first slot. -/
theorem mixed_one_zero_eq (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 0 X z θ = z * deriv (fun z' => X z' θ) z := by
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter,
    Work.Spaces.DthIter_zero, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]

/-- `D_θ f = sin(2θ) ∂_θ f` at the first slot. -/
theorem mixed_zero_one_eq (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 X z θ = Real.sin (2 * θ) * deriv (fun θ' => X z θ') θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero,
    Work.Spaces.Dth, Work.Spaces.pth]

/-- The plain `θ`-partial as a one-variable derivative. -/
theorem pth_unfold (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth X z θ = deriv (fun θ' => X z θ') θ := rfl

/-- `K` is continuous on the closed angular interval. -/
theorem continuousOn_K_Iθ_Iθ : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
  ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn

/-- **RX-R7, the `hVlipU` field.**  A `τ`-uniform Lipschitz constant for the transport
velocity `p ↦ (Vz7ᵣ p.1 p.2 τ, Vθ7ᵣ p.1 p.2 τ)` (where `Vz7ᵣ` is `Vz7` at `(pExp α, μR, GR, ΦR)`
and `Vθ7ᵣ` is `Vθ7` at `(pExp α, ΦR)`) on the half-strip `(Lz7,∞) × (0,π/2)`, for every
`τ ∈ [0,S]`.

Route: a mean-value argument on the *convex* set `(Lz7,∞) × (0,π/2)`, from
(a) differentiability of both coefficient functions on that set for each `τ`, and
(b) bounds on the two partial derivatives of each, read off `VelPkg.dbnd` (`hVP S hS`):
`pth Vz7ᵣ` is bounded by `M`; the `z`-partial of `Vz7ᵣ`, which is
`mixed 1 0 Vz7ᵣ` divided by `z`, is bounded by `M` divided by `Lz7` (using `|mixed 1 0 Vz7ᵣ| ≤ M`
and `z > Lz7`); the `z`-partial of `Vθ7ᵣ` is `sin(2θ)` times `mixed 1 0 (Vθ7ᵣ/sin 2θ)` divided by
`z`, hence bounded by `M` divided by `Lz7`; and the `θ`-partial of `Vθ7ᵣ` is
`2cos(2θ)·(Vθ7ᵣ/sin 2θ) + mixed 0 1 (Vθ7ᵣ/sin 2θ)`, bounded by `3M` (using `|Vθ7ᵣ| ≤ M·sin 2θ`
from `bnd`).  Any constant dominating these four numbers works, e.g. `M + M/Lz7 + 3M`.

For (a): `Vz7ᵣ` unfolds to the sum of the constant `1 - μ τ`, of `L12(Ftau (pExp α) (GR α g) τ)`
evaluated at `z` times `c2m θ`, and of `2·pExp α` times `Vop` of `phiTil`; `Vθ7ᵣ` unfolds to
`2·Uop (pExp α)` of the `τ`-slice of `ΦR α Φs E g`.  Differentiability in `(z,θ)` follows from
`RXT.contDiffOn_three_L12` (needs `C²` of the slice of `GR α g` at `τ`, available from
`hOK.1.1.c4`, plus a bound, e.g. `RXT.Ftau_bounds`) and from `(hVP S hS).c2`, the
`C²`-regularity of the slice of `ΦR α Φs E g` on `Q0`; the same assembly as
`Work.FTS_RegExport.RXT.Sys.CoeffSmooth.coeff_pieces_contDiffOn`, which uses `hEL3` and `hStar`
only to feed `contDiffOn_slice_PhiR_Q0` — replaceable by `(hVP S hS).c2`. -/
theorem r7VelLip {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {S Lz7 : ℝ} (hS : 0 < S) (hLz7 : 0 < Lz7) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR7.μR α Φs E g) (Work.FTS_RegExport.RXR7.GR α g)
      (Work.FTS_RegExport.RXR7.ΦR α Φs E g) S) :
    ∃ K : NNReal, ∀ τ ∈ Set.Icc (0 : ℝ) S, LipschitzOnWith K
      (fun p : ℝ × ℝ => (Work.FTS_RegExport.RXR7.Vz7R α Φs E g p.1 p.2 τ,
        Work.FTS_RegExport.RXR7.Vθ7R α Φs E g p.1 p.2 τ))
      (Set.prod (Set.Ioi Lz7) (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
  have hαGpos : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαGne : Work.FTS.Regularity.pExp α ≠ 0 := ne_of_gt hαGpos
  -- the two `τ`-uniform constants of `VelPkg`
  obtain ⟨Mdb, hMdb⟩ := (hVP S hS).dbnd
  obtain ⟨Mbnd, hMbnd⟩ := (hVP S hS).bnd
  have hMdbnn : 0 ≤ Mdb := by
    have h := (hMdb 0 ⟨le_refl 0, hS.le⟩ 1 0 (by norm_num) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).1
    exact le_trans (abs_nonneg _) h
  have hMbndnn : 0 ≤ Mbnd := by
    have h := (hMbnd 1 (Real.pi / 4) 0 (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (le_refl 0)).1
    exact le_trans (abs_nonneg _) h
  set C : ℝ := Mdb / Lz7 + Mdb + Mdb / Lz7 + (2 * Mbnd + Mdb) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have h1 : 0 ≤ Mdb / Lz7 := div_nonneg hMdbnn hLz7.le
    linarith
  refine ⟨⟨C, hCnn⟩, ?_⟩
  intro τ hτ
  have hτ0 : 0 ≤ τ := hτ.1
  -- ## the smoothness inputs, at the fixed `τ`
  have hΦ2 : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice (ΦR α Φs E g) τ))
      Work.FTS.EllipticEst.Q0 := (hVP S hS).c2 τ hτ
  have hF2 := Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (C₀ := C₀) hα hα13 hOK τ hτ0
  obtain ⟨Cf, -, hbd⟩ := Work.FTS_RegExport.RXT.Ftau_bounds (C₀ := C₀) hα hα13 hOK τ hτ0
  have hFK2 : ContDiffOn ℝ 2 (Work.Construction.FK
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      continuousOn_K_Iθ_Iθ hF2 hbd
  have hL12 : ContDiffOn ℝ 2 (Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ)) (Set.Ioi 0) :=
    (Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2).of_le (by norm_num)
  obtain ⟨hFz_cd0, hb_cd0⟩ := Work.FTS_RegExport.RXR7.VelLipAux.coeff_contDiffOn_one
    (αG := Work.FTS.Regularity.pExp α)
    (μ := μR α Φs E g) (G := GR α g) (Φ := ΦR α Φs E g) hαGne hΦ2 hL12
  -- ## the three functions of the mean-value argument
  set Fz : ℝ → ℝ → ℝ := fun z θ => Vz7R α Φs E g z θ τ with hFz
  set Fθ : ℝ → ℝ → ℝ := fun z θ => Vθ7R α Φs E g z θ τ with hFθ
  set b : ℝ → ℝ → ℝ := fun z θ => Fθ z θ / Real.sin (2 * θ) with hb
  have hFz_cd : ContDiffOn ℝ 1 (Function.uncurry Fz) Work.FTS.EllipticEst.Q0 := by
    simpa only [hFz, Vz7R] using hFz_cd0
  have hb_cd : ContDiffOn ℝ 1 (Function.uncurry b) Work.FTS.EllipticEst.Q0 := by
    simpa only [hb, hFθ, Vθ7R] using hb_cd0
  have hFθ_cd : ContDiffOn ℝ 1 (Function.uncurry Fθ) Work.FTS.EllipticEst.Q0 := by
    have hsin : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    refine ((hsin.mul hb_cd).congr fun p hp => ?_)
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hs : Real.sin (2 * p.2) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    simp only [Pi.mul_apply, Function.uncurry, hb, hFθ]
    rw [mul_comm, div_mul_cancel₀ _ hs]
  -- ## the four partial-derivative bounds
  have hz1 : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < π / 2 →
      |deriv (fun z' => Fz z' θ) z| ≤ Mdb / Lz7 := by
    intro z θ hz hθ0 hθ1
    have hz0 : 0 < z := lt_trans hLz7 hz
    have hmix : |Work.Spaces.mixed 1 0 Fz z θ| ≤ Mdb := by
      have h := (hMdb τ hτ 1 0 (by norm_num) z θ hz0 hθ0 hθ1).1
      simpa only [hFz, Vz7R] using h
    have h2 : |deriv (fun z' => Fz z' θ) z| ≤ Mdb / z := by
      rw [mixed_one_zero_eq, abs_mul, abs_of_pos hz0] at hmix
      rw [le_div_iff₀ hz0]
      linarith
    have h3 : Mdb / z ≤ Mdb / Lz7 := by
      rw [div_le_div_iff₀ hz0 hLz7]
      exact mul_le_mul_of_nonneg_left (le_of_lt hz) hMdbnn
    linarith
  have hz2 : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < π / 2 →
      |deriv (fun θ' => Fz z θ') θ| ≤ Mdb := by
    intro z θ hz hθ0 hθ1
    have hz0 : 0 < z := lt_trans hLz7 hz
    have h := (hMdb τ hτ 0 0 (by norm_num) z θ hz0 hθ0 hθ1).2.2.2
    simpa only [hFz, Vz7R, pth_unfold] using h
  have hz3 : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < π / 2 →
      |deriv (fun z' => Fθ z' θ) z| ≤ Mdb / Lz7 := by
    intro z θ hz hθ0 hθ1
    have hz0 : 0 < z := lt_trans hLz7 hz
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ0, hθ1⟩
    have hbdz : DifferentiableAt ℝ (fun z' => b z' θ) z :=
      Work.Spaces.differentiableAt_curry_left
        ((hb_cd.differentiableOn (by norm_num)).differentiableAt
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem))
    have hpz : deriv (fun z' => Fθ z' θ) z
        = Real.sin (2 * θ) * deriv (fun z' => b z' θ) z := by
      have hfun : (fun z' => Fθ z' θ) = fun z' => Real.sin (2 * θ) * b z' θ := by
        funext z'
        simp only [hb, hFθ]
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hs)]
      rw [hfun]
      exact (hbdz.hasDerivAt.const_mul (Real.sin (2 * θ))).deriv
    have hmix : |Work.Spaces.mixed 1 0 b z θ| ≤ Mdb := by
      have h := (hMdb τ hτ 1 0 (by norm_num) z θ hz0 hθ0 hθ1).2.1
      simpa only [hb, hFθ, Vθ7R] using h
    have hpzb : |deriv (fun z' => b z' θ) z| ≤ Mdb / Lz7 := by
      rw [mixed_one_zero_eq, abs_mul, abs_of_pos hz0] at hmix
      have h2 : |deriv (fun z' => b z' θ) z| ≤ Mdb / z := by
        rw [le_div_iff₀ hz0]
        linarith
      have h3 : Mdb / z ≤ Mdb / Lz7 := by
        rw [div_le_div_iff₀ hz0 hLz7]
        exact mul_le_mul_of_nonneg_left (le_of_lt hz) hMdbnn
      linarith
    calc |deriv (fun z' => Fθ z' θ) z|
        = |Real.sin (2 * θ)| * |deriv (fun z' => b z' θ) z| := by rw [hpz, abs_mul]
      _ ≤ 1 * (Mdb / Lz7) := by
          exact mul_le_mul (Real.abs_sin_le_one _) hpzb (abs_nonneg _) (by norm_num)
      _ = Mdb / Lz7 := one_mul _
  have hz4 : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < π / 2 →
      |deriv (fun θ' => Fθ z θ') θ| ≤ 2 * Mbnd + Mdb := by
    intro z θ hz hθ0 hθ1
    have hz0 : 0 < z := lt_trans hLz7 hz
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ0, hθ1⟩
    have hbdθ : DifferentiableAt ℝ (fun θ' => b z θ') θ :=
      Work.Spaces.differentiableAt_curry_right
        ((hb_cd.differentiableOn (by norm_num)).differentiableAt
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem))
    -- the product rule in `θ` for `Vθ7ᵣ = sin(2θ)·b`
    have hsin : HasDerivAt (fun θ' => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
      have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ :=
        hasDerivAt_const_mul (x := θ) (2 : ℝ)
      have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
      have h4 : (2 : ℝ) * Real.cos (2 * θ) = Real.cos (2 * θ) * 2 := by ring
      rw [h4]
      simpa only [Function.comp_def] using h
    have hfun : (fun θ' => Fθ z θ') =ᶠ[𝓝 θ]
        (fun θ' => Real.sin (2 * θ') * b z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩] with θ' hθ'
      have hs' : Real.sin (2 * θ') ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1])
          (by linarith [hθ'.2]))
      simp only [hb, hFθ]
      rw [mul_comm, div_mul_cancel₀ _ hs']
    have hderiv : deriv (fun θ' => Fθ z θ') θ
        = 2 * Real.cos (2 * θ) * b z θ
          + Real.sin (2 * θ) * deriv (fun θ' => b z θ') θ :=
      ((hsin.mul hbdθ.hasDerivAt).congr_of_eventuallyEq hfun).deriv
    have hbnd : |b z θ| ≤ Mbnd := by
      have h := (hMbnd z θ τ hz0 hθ0 hθ1 hτ0).2.1
      have hbeq : b z θ = Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
          (ΦR α Φs E g) z θ τ / Real.sin (2 * θ) := by
        simp only [hb, hFθ, Vθ7R]
      rw [hbeq, abs_div, abs_of_pos hs, div_le_iff₀ hs]
      linarith
    have hmixθ : |Real.sin (2 * θ) * deriv (fun θ' => b z θ') θ| ≤ Mdb := by
      have h := (hMdb τ hτ 0 1 (by norm_num) z θ hz0 hθ0 hθ1).2.1
      rw [mixed_zero_one_eq] at h
      simpa only [hb, hFθ, Vθ7R] using h
    have h1 : |2 * Real.cos (2 * θ) * b z θ| ≤ 2 * Mbnd := by
      have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
      calc |2 * Real.cos (2 * θ) * b z θ| = 2 * |Real.cos (2 * θ)| * |b z θ| := by
            rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * 1 * Mbnd := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hbnd
              (abs_nonneg _) (by norm_num)
        _ = 2 * Mbnd := by ring
    calc |deriv (fun θ' => Fθ z θ') θ|
        = |2 * Real.cos (2 * θ) * b z θ
            + Real.sin (2 * θ) * deriv (fun θ' => b z θ') θ| := by rw [hderiv]
      _ ≤ |2 * Real.cos (2 * θ) * b z θ|
            + |Real.sin (2 * θ) * deriv (fun θ' => b z θ') θ| := abs_add_le _ _
      _ ≤ 2 * Mbnd + Mdb := add_le_add h1 hmixθ
  -- ## differentiability of the one-variable slices
  have hdFz : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Fz z' θ) z ∧ DifferentiableAt ℝ (fun θ' => Fz z θ') θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : 0 < z := lt_trans hLz7 hz
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ0, hθ1⟩
    have hd : DifferentiableAt ℝ (Function.uncurry Fz) (z, θ) :=
      (hFz_cd.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
    exact ⟨Work.Spaces.differentiableAt_curry_left hd,
      Work.Spaces.differentiableAt_curry_right hd⟩
  have hdFθ : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Fθ z' θ) z ∧ DifferentiableAt ℝ (fun θ' => Fθ z θ') θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : 0 < z := lt_trans hLz7 hz
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ0, hθ1⟩
    have hd : DifferentiableAt ℝ (Function.uncurry Fθ) (z, θ) :=
      (hFθ_cd.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
    exact ⟨Work.Spaces.differentiableAt_curry_left hd,
      Work.Spaces.differentiableAt_curry_right hd⟩
  -- ## the mean-value argument with the explicit `τ`-uniform constant
  have hMz : 0 ≤ Mdb / Lz7 := div_nonneg hMdbnn hLz7.le
  have hNz : 0 ≤ Mdb / Lz7 := div_nonneg hMdbnn hLz7.le
  have hNθ : 0 ≤ 2 * Mbnd + Mdb := by linarith
  have hK : Mdb / Lz7 + Mdb + Mdb / Lz7 + (2 * Mbnd + Mdb) ≤ (⟨C, hCnn⟩ : NNReal) := by
    show Mdb / Lz7 + Mdb + Mdb / Lz7 + (2 * Mbnd + Mdb) ≤ C
    rw [hC]
  exact Work.FTS_RegExport.RXR7.VelLipAux.lipschitz_pair_of_deriv_bounds_le
    (Fz := Fz) (Fθ := Fθ) (Lz := Lz7)
    (Mz := Mdb / Lz7) (Mθ := Mdb) (Nz := Mdb / Lz7) (Nθ := 2 * Mbnd + Mdb)
    (K := ⟨C, hCnn⟩) hLz7 hMz hMdbnn hNz hNθ hK hdFz hdFθ hz1 hz2 hz3 hz4

end Work.FTS_RegExport.RXR7
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.CoeffBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.CoeffBounds` — the order-`≤ 2` jet bounds of the coefficients

For a fixed fake time `τ` the three transport coefficients are written as explicit sums of a
constant, a radial `L₁₂`/`FK`-piece and a slot `Vop Φ̃`, `Uop Φ̃/sin 2θ`, `Rop Φ̃` of the residual
(plus the explicit `Θ`-parts).  Each of the four bounds (the three coefficient families and
`∂_θVz7`) is reduced here to the corresponding bound of the *slots* (`Sys.velVanish2`), of the
explicit pieces (`Sys.explicit_pieces_coeff`), of the `|μ| ≤ 1/2` clock bound and of the
`C²`-regularity of the pieces (`Sys.CoeffSmooth`), which are supplied as hypotheses.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7)
open Work.FTS.RegExportIface.RXT (GR ΦR μR)
open Work.FTS_RegExport.RXT (v2_PhiT v2_SlotR v2_SlotV v2_SlotU)
open Work.FTS.Regularity (pExp)
open Work.Construction (L12 FK Ftau Theta Uop Vop Rop c2m Fstar)

set_option autoImplicit false

variable {α Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- The clock bound gives `|1 ∓ μ| ≤ 3/2`. -/
theorem one_sub_abs_le {μ : ℝ} (h : |μ| ≤ 1 / 2) : |1 - μ| ≤ 3 / 2 := by
  have := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

/-- The clock bound gives `|1 + μ| ≤ 3/2`. -/
theorem one_add_abs_le {μ : ℝ} (h : |μ| ≤ 1 / 2) : |1 + μ| ≤ 3 / 2 := by
  have := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

/-- **`Vz7`'s order-`≤ 2` jets.** -/
theorem Vz7_jets_le {g : Fam} {τ Mslot Cexp : ℝ}
    (hαG : 0 < pExp α)
    (hsmA : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)) Q0)
    (hsmB : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * pExp α
        * Vop (v2_PhiT α Φs E g τ) z θ)) Q0)
    (hsmP1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)) Q0)
    (hμbd : |μR α Φs E g τ| ≤ 1 / 2)
    (hslotV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotV α (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot)
    (hexp1 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ =>
        L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ| ≤ Cexp) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ 3 / 2 + Cexp + 2 * pExp α * Mslot := by
  intro j i hji z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Q0 := ⟨hz, hθ, hθ2⟩
  have hEq : EqOn (Function.uncurry (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ))
      (Function.uncurry (fun z θ => ((1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)
        + 2 * pExp α * Vop (v2_PhiT α Φs E g τ) z θ)) Q0 := by
    intro p hp
    simp only [Function.uncurry, Vz7, v2_PhiT, Work.FTS.RegExportIface.phiTil,
      Work.Construction.PhiTil]
  rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hEq j i z θ hzθ,
    mixed_add_lam hsmA hsmB hji hzθ]
  have h1 : |Work.Spaces.mixed j i (fun z θ => (1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ|
      ≤ |1 - μR α Φs E g τ| + Cexp := by
    rw [mixed_add_lam (contDiffOn_const) hsmP1 hji hzθ]
    exact le_trans (abs_add_le _ _)
      (add_le_add (abs_mixed_const_le _ j i z θ) (hexp1 j i hji z θ hz hθ hθ2))
  have h2 : |Work.Spaces.mixed j i (fun z θ => 2 * pExp α
        * Vop (v2_PhiT α Φs E g τ) z θ) z θ| ≤ 2 * pExp α * Mslot := by
    rw [coeff_mixed_const_mul]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * pExp α)]
    exact mul_le_mul_of_nonneg_left (hslotV j i hji z θ hz hθ hθ2) (by linarith)
  have hsum := abs_add_le (Work.Spaces.mixed j i (fun z θ => (1 - μR α Φs E g τ)
      + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ)
    (Work.Spaces.mixed j i (fun z θ => 2 * pExp α
      * Vop (v2_PhiT α Φs E g τ) z θ) z θ)
  have hm := one_sub_abs_le hμbd
  linarith

/-- **`Vθ7/sin 2θ`'s order-`≤ 2` jets.** -/
theorem Vth_jets_le {g : Fam} {τ Mslot Cexp : ℝ}
    (hαG : 0 < pExp α)
    (hsmU1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ))) Q0)
    (hsmU2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ))) Q0)
    (hsmPsi : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0)
    (hsmTheta : ContDiffOn ℝ 3 (Function.uncurry (Theta (pExp α) (Ftau (pExp α) (GR α g) τ))) Q0)
    (hslotU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotU α (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot)
    (hexp4 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)) z θ| ≤ Cexp) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
        / Real.sin (2 * θ)) z θ| ≤ 2 * Mslot + 2 * Cexp := by
  intro j i hji z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Q0 := ⟨hz, hθ, hθ2⟩
  have hEq : EqOn (Function.uncurry (fun z θ => Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
      / Real.sin (2 * θ)))
      (Function.uncurry (fun z θ => 2 * Uop (pExp α)
          (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)
        + 2 * Uop (pExp α) (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ
            / Real.sin (2 * θ))) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    simp only [Function.uncurry, Vθ7, Work.FTS.Galerkin.slice]
    rw [uop_split_theta (Φs := Φs) (E := E) (g := g) ⟨hz', hθ', hθ2'⟩ hsmPsi hsmTheta]
    ring
  rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hEq j i z θ hzθ,
    mixed_add_lam hsmU1 hsmU2 hji hzθ]
  have h1 : |Work.Spaces.mixed j i (fun z θ => 2 * Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)) z θ| ≤ 2 * Mslot := by
    have hcongr : EqOn (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)))
        (Function.uncurry (fun z θ => 2 * (Uop (pExp α)
          (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)))) Q0 := by
      intro p hp
      simp only [Function.uncurry]
      ring
    rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hcongr j i z θ hzθ,
      coeff_mixed_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hU : |Work.Spaces.mixed j i (fun z θ => Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)) z θ| ≤ Mslot := by
      change |Work.Spaces.mixed j i (v2_SlotU α
        (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot
      exact hslotU j i hji z θ hz hθ hθ2
    exact mul_le_mul_of_nonneg_left hU (by norm_num)
  have h2 : |Work.Spaces.mixed j i (fun z θ => 2 * Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)) z θ|
      ≤ 2 * Cexp := by
    have hcongr : EqOn (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)))
        (Function.uncurry (fun z θ => 2 * (Uop (pExp α)
          (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)))) Q0 := by
      intro p hp
      simp only [Function.uncurry]
      ring
    rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hcongr j i z θ hzθ,
      coeff_mixed_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hexp4 j i hji z θ hz hθ hθ2) (by norm_num)
  have hsum := abs_add_le (Work.Spaces.mixed j i (fun z θ => 2 * Uop (pExp α)
      (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)) z θ)
    (Work.Spaces.mixed j i (fun z θ => 2 * Uop (pExp α)
      (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)) z θ)
  linarith

/-- **`cs7`'s order-`≤ 2` jets.** -/
theorem Cs_jets_le {g : Fam} {τ Mslot Cexp : ℝ}
    (hαG : 0 < pExp α)
    (hsmA' : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) Q0)
    (hsmB' : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (Real.sin θ) ^ 2
        * FK (Ftau (pExp α) (GR α g) τ) z)) Q0)
    (hsmA'B' : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z)) Q0)
    (hsmC' : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Rop (pExp α)
        (v2_PhiT α Φs E g τ) z θ)) Q0)
    (hsmLdiv : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) Q0)
    (hμbd : |μR α Φs E g τ| ≤ 1 / 2)
    (hslotR : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotR α (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot)
    (hexp2 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ =>
        L12 (Ftau (pExp α) (GR α g) τ) z) z θ| ≤ Cexp)
    (hexp3 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => (Real.sin θ) ^ 2 * FK
        (Ftau (pExp α) (GR α g) τ) z) z θ| ≤ Cexp) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => cs7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ 3 / 2 + Cexp / pExp α + Cexp + 2 * Mslot := by
  intro j i hji z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Q0 := ⟨hz, hθ, hθ2⟩
  -- the field as a sum of the three pieces
  have hEq : EqOn (Function.uncurry (fun z θ => cs7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ))
      (Function.uncurry (fun z θ => (((1 + μR α Φs E g τ)
          - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z)
        + (-1) * (2 * Rop (pExp α) (v2_PhiT α Φs E g τ) z θ))) Q0 := by
    intro p hp
    simp only [Function.uncurry, cs7, v2_PhiT, Work.FTS.RegExportIface.phiTil,
      Work.Construction.PhiTil]
    ring
  rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hEq j i z θ hzθ,
    mixed_add_lam hsmA'B' (contDiffOn_const.mul hsmC') hji hzθ]
  -- the `Rop`-piece
  have h3 : |Work.Spaces.mixed j i (fun z θ => (-1) * (2 * Rop (pExp α)
        (v2_PhiT α Φs E g τ) z θ)) z θ| ≤ 2 * Mslot := by
    have hR0 : |Work.Spaces.mixed j i (Rop (pExp α) (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot := by
      change |Work.Spaces.mixed j i (v2_SlotR α
        (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot
      exact hslotR j i hji z θ hz hθ hθ2
    have hR : |Work.Spaces.mixed j i (fun z θ => 2 * Rop (pExp α)
        (v2_PhiT α Φs E g τ) z θ) z θ| ≤ 2 * Mslot :=
      abs_mixed_const_mul_le (c := (2 : ℝ)) (by norm_num)
        (f := Rop (pExp α) (v2_PhiT α Φs E g τ)) hR0
    have h2 := abs_mixed_const_mul_le' (c := (-1 : ℝ))
      (f := fun z θ => 2 * Rop (pExp α) (v2_PhiT α Φs E g τ) z θ) hR
    simpa using h2
  -- the explicit pieces
  have h1 : |Work.Spaces.mixed j i (fun z θ => ((1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z) z θ|
      ≤ 3 / 2 + Cexp / pExp α + Cexp := by
    rw [mixed_add_lam hsmA' hsmB' hji hzθ]
    have hA' : |Work.Spaces.mixed j i (fun z θ => (1 + μR α Φs E g τ)
          - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α) z θ|
        ≤ 3 / 2 + Cexp / pExp α := by
      have hcongr : EqOn (Function.uncurry (fun z θ => (1 + μR α Φs E g τ)
          - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α))
          (Function.uncurry (fun z θ => (1 + μR α Φs E g τ)
            + (-1) * (L12 (Ftau (pExp α) (GR α g) τ) z / pExp α))) Q0 := by
        intro p hp
        simp only [Function.uncurry]
        ring
      rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hcongr j i z θ hzθ,
        mixed_add_lam contDiffOn_const (contDiffOn_const.mul hsmLdiv) hji hzθ]
      have hLdiv' : |Work.Spaces.mixed j i (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z
            / pExp α) z θ| ≤ Cexp / pExp α := by
        have hcongr2 : EqOn (Function.uncurry (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z
            / pExp α))
            (Function.uncurry (fun z θ => (pExp α)⁻¹
              * L12 (Ftau (pExp α) (GR α g) τ) z)) Q0 := by
          intro p hp
          simp only [Function.uncurry]
          ring
        rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hcongr2 j i z θ hzθ,
          coeff_mixed_const_mul]
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hαG.le)]
        calc (pExp α)⁻¹ * |Work.Spaces.mixed j i (fun z θ =>
              L12 (Ftau (pExp α) (GR α g) τ) z) z θ|
            ≤ (pExp α)⁻¹ * Cexp :=
              mul_le_mul_of_nonneg_left (hexp2 j i hji z θ hz hθ hθ2)
                (inv_nonneg.mpr hαG.le)
          _ = Cexp / pExp α := by rw [inv_mul_eq_div]
      have hneg : |Work.Spaces.mixed j i (fun z θ => (-1)
            * (L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) z θ| ≤ Cexp / pExp α := by
        have h := abs_mixed_const_mul_le' (c := (-1 : ℝ))
          (f := fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z / pExp α) hLdiv'
        simpa using h
      have hsum2 := abs_add_le (Work.Spaces.mixed j i (fun _ _ : ℝ =>
          (1 + μR α Φs E g τ)) z θ)
        (Work.Spaces.mixed j i (fun z θ => (-1)
          * (L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) z θ)
      have hm := one_add_abs_le hμbd
      have hc := abs_mixed_const_le (1 + μR α Φs E g τ) j i z θ
      linarith
    have hsum2 := abs_add_le (Work.Spaces.mixed j i (fun z θ => (1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α) z θ)
      (Work.Spaces.mixed j i (fun z θ => (Real.sin θ) ^ 2 * FK
        (Ftau (pExp α) (GR α g) τ) z) z θ)
    have hb := hexp3 j i hji z θ hz hθ hθ2
    linarith
  have hsum := abs_add_le (Work.Spaces.mixed j i (fun z θ => ((1 + μR α Φs E g τ)
      - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
      + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z) z θ)
    (Work.Spaces.mixed j i (fun z θ => (-1) * (2 * Rop (pExp α)
      (v2_PhiT α Φs E g τ) z θ)) z θ)
  linarith

/-- **`∂_θVz7`'s bound.** -/
theorem Vz7_pth_le {g : Fam} {τ CF Mpth : ℝ}
    (hαG : 0 < pExp α)
    (hsmA : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)) Q0)
    (hsmB : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * pExp α
        * Vop (v2_PhiT α Φs E g τ) z θ)) Q0)
    (hMpth : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth (fun z θ => Vop (v2_PhiT α Φs E g τ) z θ) z θ| ≤ Mpth)
    (hCF0 : 0 ≤ CF)
    (hL12bd : ∀ z : ℝ, 0 < z → |L12 (Ftau (pExp α) (GR α g) τ) z| ≤ CF) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ CF * 4 + 2 * pExp α * Mpth := by
  intro z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Q0 := ⟨hz, hθ, hθ2⟩
  have hMpth : |Work.Spaces.pth (fun z θ => Vop (v2_PhiT α Φs E g τ) z θ) z θ| ≤ Mpth :=
    hMpth z θ hz hθ hθ2
  have hL12bd' : |L12 (Ftau (pExp α) (GR α g) τ) z| ≤ CF := hL12bd z hz
  have hEq : EqOn (Function.uncurry (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ))
      (Function.uncurry (fun z θ => ((1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)
        + 2 * pExp α * Vop (v2_PhiT α Φs E g τ) z θ)) Q0 := by
    intro p hp
    simp only [Function.uncurry, Vz7, v2_PhiT, Work.FTS.RegExportIface.phiTil,
      Work.Construction.PhiTil]
  have hDthSplit : Work.Spaces.Dth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ) z θ
      = Work.Spaces.Dth (fun z θ => (1 - μR α Φs E g τ)
          + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ
        + Work.Spaces.Dth (fun z θ => 2 * pExp α
          * Vop (v2_PhiT α Φs E g τ) z θ) z θ := by
    rw [Dth_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hEq hzθ]
    exact Dth_split_of_eqOn hsmA hsmB hEq z θ hzθ
  have hsin : Real.sin (2 * θ) ≠ 0 := ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 hzθ)
  have hD1 : Work.Spaces.Dth (fun z θ => (1 - μR α Φs E g τ)
      + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ
      = Real.sin (2 * θ) * (L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ) := by
    have hd1 : DifferentiableAt ℝ (fun _ : ℝ => (1 - μR α Φs E g τ)) θ :=
      differentiableAt_const _
    have hd2 : DifferentiableAt ℝ (fun θ' => L12 (Ftau (pExp α) (GR α g) τ) z
        * c2m θ') θ := by
      have hc := Work.FTS_RegExport.RXT.contDiffOn_c2m.differentiableOn (by norm_num) θ
        ⟨hθ, hθ2⟩
      exact (differentiableAt_const _).mul (hc.differentiableAt (isOpen_Ioo.mem_nhds ⟨hθ, hθ2⟩))
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [show (fun θ' : ℝ => (1 - μR α Φs E g τ) + L12 (Ftau (pExp α) (GR α g) τ) z
          * c2m θ') = ((fun _ : ℝ => (1 - μR α Φs E g τ))
          + (fun θ' => L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ')) from rfl,
      deriv_add hd1 hd2, deriv_const, Work.Construction.deriv_const_mul_fun]
    ring
  have hD2 : Work.Spaces.Dth (fun z θ => 2 * pExp α
      * Vop (v2_PhiT α Φs E g τ) z θ) z θ
      = 2 * pExp α * Work.Spaces.Dth (Vop (v2_PhiT α Φs E g τ)) z θ := by
    rw [Work.FTS.StrongEps.Dth_const_mul (2 * pExp α) (Vop (v2_PhiT α Φs E g τ))]
  have hpthEq : Work.Spaces.pth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ) z θ
      = L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ
        + 2 * pExp α * Work.Spaces.pth (Vop (v2_PhiT α Φs E g τ)) z θ := by
    have hDth : Work.Spaces.Dth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ
        = Real.sin (2 * θ) * ((L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ)
          + 2 * pExp α * Work.Spaces.pth (Vop (v2_PhiT α Φs E g τ)) z θ) := by
      rw [hDthSplit, hD1, hD2, Work.Spaces.Dth]
      ring
    have hDthDef : Work.Spaces.Dth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (fun z θ => Vz7 (pExp α) (μR α Φs E g)
          (GR α g) (ΦR α Φs E g) z θ τ) z θ := rfl
    rw [hDthDef] at hDth
    exact mul_left_cancel₀ hsin hDth
  rw [hpthEq]
  have hmul : |L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ| ≤ CF * 4 := by
    rw [abs_mul]
    exact mul_le_mul hL12bd' (abs_deriv_c2m_le θ) (abs_nonneg _) hCF0
  have hmul2 : |2 * pExp α * Work.Spaces.pth (Vop (v2_PhiT α Φs E g τ)) z θ|
      ≤ 2 * pExp α * Mpth := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * pExp α)]
    exact mul_le_mul_of_nonneg_left hMpth (by linarith)
  have hsum := abs_add_le (L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ)
    (2 * pExp α * Work.Spaces.pth (Vop (v2_PhiT α Φs E g τ)) z θ)
  linarith

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.RHSSmooth` — smoothness of `F(σ)` and of `RHS σ`

`F_* = α(Γ/c)(2z/(1+z)²)` is `C^n` on the open quadrant for every `n`; the slice of the
sanitiser `GR α g` is `C^n` for `n ≤ 4` (`RegPkgMin.c4` + agreement with `g` on the quadrant);
hence `F(σ)` is `C^n` (`n ≤ 4`) and `RHS σ` is `C²` there.  Also the linearity of the mixed
operators on the three summands `Afun`, `Bfun`, `Cfun` of `RHS`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! ## §3 Smoothness of the profile and of the right-hand side on the open quadrant -/

/-- `F_* = α·(Γ/c)·(2z/(1+z)²)` is `C^n` on the open quadrant. -/
theorem contDiffOn_Fstar_Q0 (n : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ n (Function.uncurry (Work.Construction.Fstar α))
      Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Gam_Q0 α n
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 :=
    hGam.div contDiffOn_const (fun _ _ => hc)
  have h2 : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.ftau_contDiffOn_FM_Fstar n).comp contDiffOn_fst
      (fun p hp => hp.1)
  exact (h2.mul h3).congr (fun _ _ => rfl)

/-- The sanitiser `GR α g` has the same `C^n` slices as `g` on the open quadrant. -/
theorem contDiffOn_slice_GR_Q0 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {n : ℕ} (hn : n ≤ 4) (σ : ℝ) (hσ : 0 ≤ σ) :
    ContDiffOn ℝ n (Function.uncurry (Work.FTS.Galerkin.slice
      (Work.FTS.RegExportIface.RXT.GR α g) σ)) Work.FTS.EllipticEst.Q0 := by
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g σ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 σ hσ
  refine (h4.of_le (Nat.cast_le.mpr hn)).congr ?_
  intro p hp
  exact Work.FTS_RegExport.RXT.ftau_slice_GR_eq hσ hp.1 hp.2.1.le hp.2.2.le

/-- `F(σ) = F_* + gS α (tauExt g)(σ)` is `C^n` on the open quadrant for `n ≤ 4`. -/
theorem contDiffOn_FtauS_Q0 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {n : ℕ} (hn : n ≤ 4) (σ : ℝ) (hσ : 0 ≤ σ) :
    ContDiffOn ℝ n (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hF : ContDiffOn ℝ n
      (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_Fstar_Q0 n hβ hβ1
  have hG : ContDiffOn ℝ n (Function.uncurry (Work.FTS.Galerkin.slice
      (Work.FTS.RegExportIface.RXT.GR α g) σ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_slice_GR_Q0 hOK hn σ hσ
  refine (hF.add hG).congr (fun p _ => ?_)
  show Work.Construction.Fstar (Work.FTS.Regularity.pExp α) p.1 p.2
      + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) σ p.1 p.2
    = FtauS α g σ p.1 p.2
  simp only [FtauS_apply, Work.FTS.Galerkin.slice]

/-- **`RHS` is `C²` on the open quadrant.**  It is a sum of products of the three coefficients
(`C²` by `hC2`) with `D_zF`, `D_θF`, `F` (`C²` because `F` is `C³`, `contDiffOn_FtauS_Q0`). -/
theorem contDiffOn_RHS {α C₀ S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : σ ∈ Set.Ioc (0:ℝ) S) :
    ContDiffOn ℝ 2 (Function.uncurry (RHS α Φs E g σ)) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨h1, h2, h3⟩ := hC2 σ hσ.1.le
  have hQ3 : ContDiffOn ℝ 3 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_FtauS_Q0 hα hα13 hOK (by norm_num) σ hσ.1.le
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    hQ3.of_le (by norm_num)
  have hDz : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dz (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  have hDth : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dth (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  have hA := h1.mul hDz
  have hB := h2.mul hDth
  have hC := h3.mul hQ2
  refine ((hA.add hB).add hC).neg.congr (fun p _ => ?_)
  show - (Work.FTS.RegExportIface.RXT.VR α Φs E g p.1 p.2 σ
        * Work.Spaces.Dz (FtauS α g σ) p.1 p.2
      + Work.FTS.RegExportIface.RXT.bR α Φs E g p.1 p.2 σ
        * Work.Spaces.Dth (FtauS α g σ) p.1 p.2
      + Work.FTS.RegExportIface.RXT.cR α Φs E g p.1 p.2 σ * FtauS α g σ p.1 p.2)
    = RHS α Φs E g σ p.1 p.2
  rw [RHS_apply]

/-! ## §4 The uniform local jet bounds for `RHS` -/

/-- The first summand of `RHS`: `Vz·D_zF`. -/
noncomputable def Afun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ
    * Work.Spaces.Dz (FtauS α g σ) z θ

/-- The second summand of `RHS`: `bR·D_θF`. -/
noncomputable def Bfun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
    * Work.Spaces.Dth (FtauS α g σ) z θ

/-- The third summand of `RHS`: `cs·F`. -/
noncomputable def Cfun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * FtauS α g σ z θ

theorem RHS_eq_neg_sum (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (σ z θ : ℝ) :
    RHS α Φs E g σ z θ
      = - ((Afun α Φs E g σ z θ + Bfun α Φs E g σ z θ) + Cfun α Φs E g σ z θ) := by
  rw [RHS_apply]
  rfl

theorem RHS_eq_neg_sum_fun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) :
    RHS α Φs E g σ
      = fun z θ => - ((Afun α Φs E g σ + Bfun α Φs E g σ) + Cfun α Φs E g σ) z θ := by
  funext z θ
  rw [RHS_eq_neg_sum]
  rfl

/-- **The summands of `RHS` are `C²` on the open quadrant** (needed for the linearity of the
mixed operators on the sum). -/
theorem contDiffOn_Afun {α C₀ S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : σ ∈ Set.Ioc (0:ℝ) S) :
    ContDiffOn ℝ 2 (Function.uncurry (Afun α Φs E g σ)) Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (Bfun α Φs E g σ)) Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (Cfun α Φs E g σ)) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨h1, h2, h3⟩ := hC2 σ hσ.1.le
  have hQ3 : ContDiffOn ℝ 3 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_FtauS_Q0 hα hα13 hOK (by norm_num) σ hσ.1.le
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    hQ3.of_le (by norm_num)
  have hDz : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dz (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  have hDth : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dth (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  refine ⟨?_, ?_, ?_⟩
  · exact (h1.mul hDz).congr (fun _ _ => rfl)
  · exact (h2.mul hDth).congr (fun _ _ => rfl)
  · exact (h3.mul hQ2).congr (fun _ _ => rfl)

/-- **Linearity of the mixed operators on `RHS σ`**: the jet of `RHS σ` is the sum of the jets of
its three summands, with a sign. -/
theorem mixed_RHS_eq {α C₀ S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : σ ∈ Set.Ioc (0:ℝ) S) {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (RHS α Φs E g σ) z θ
      = - (Work.Spaces.mixed j i (Afun α Φs E g σ) z θ
          + Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ
          + Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ) := by
  obtain ⟨hA2, hB2, hC2'⟩ := contDiffOn_Afun hα hα13 hOK hC2 hσ
  have hAB : ContDiffOn ℝ 2 (Function.uncurry (Afun α Φs E g σ + Bfun α Φs E g σ))
      Work.FTS.EllipticEst.Q0 := hA2.add hB2
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθπ⟩
  have hsum : Work.Spaces.mixed j i ((Afun α Φs E g σ + Bfun α Φs E g σ) + Cfun α Φs E g σ) z θ
      = Work.Spaces.mixed j i (Afun α Φs E g σ) z θ
        + Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ
        + Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ := by
    have hji' : i + j ≤ 2 := by rw [Nat.add_comm]; exact hji
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
        Work.FTS.EllipticEst.isOpen_Q0 hAB hC2' i j hji' (z, θ) hp
    have h2 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
        Work.FTS.EllipticEst.isOpen_Q0 hA2 hB2 i j hji' (z, θ) hp
    rw [h1, h2]
  have hneg := congrFun (congrFun (mixed_neg j i
    ((Afun α Φs E g σ + Bfun α Φs E g σ) + Cfun α Φs E g σ)) z) θ
  rw [RHS_eq_neg_sum_fun, hneg, hsum]

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.jetBasic` — the elementary `mixed`-jet facts

This file proves the standing "basic jet" conjunction consumed by the coefficient-jet
statements of the `RXJets` chapter:

* the `mixed`-jets (`D_z^kD_θ^l`) of a function constant in `(z,θ)` vanish unless `k = l = 0`
  (and then equal the constant), together with the joint continuity of that family on the
  slab `slb S` when the constant is allowed to depend on `τ`;
* the `C²`-regularity on `(0,π/2)` of the two angular profiles `c2m` and `sin²`;
* the continuity of the angular iterates `D_θ^l b` (`l ≤ 2`) of a `C²` function `b` of `θ`
  alone (via the one-variable operator `dthU φ = sin(2·)·φ'`);
* the joint continuity on `slb S` of the `mixed`-jets of a *radial* datum `c·a(z,τ)` and of a
  *separable* datum `a(z,τ)·b(θ)`, in terms of the joint continuity of the `D_z`-jets of `a`
  and the continuity of the `θ`-iterates of `b`.
-/

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false

/-! ## §1 `mixed`-jets of constants -/

/-- The `mixed`-jets of a constant function: only the `(0,0)`-jet survives. -/
theorem jetMixedConst (c : ℝ) (k l : ℕ) :
    Work.Spaces.mixed k l (fun _ _ : ℝ => c) = fun _ _ => if k = 0 ∧ l = 0 then c else 0 := by
  rw [Work.Spaces.mixed, Work.FTS_RegExport.RXT.Sys.DthIter_const_fun c l,
    Work.FTS_RegExport.RXT.Sys.DzIter_const_fun (if l = 0 then c else 0) k]
  funext z θ
  by_cases hk : k = 0 <;> by_cases hl : l = 0 <;> simp [hk, hl]

/-- **Joint continuity of the `mixed`-jets of a `τ`-dependent constant.**  If `c` is continuous
on `[0,S]`, then `p ↦ D_z^kD_θ^l (fun _ _ => c p.2.2)` is continuous on the slab `slb S`. -/
theorem jetContOnMixedConst {S : ℝ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Icc 0 S))
    (k l : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun _ _ : ℝ => c p.2.2) p.1 p.2.1) (slb S) := by
  have hfun : (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun _ _ : ℝ => c p.2.2) p.1 p.2.1)
      = fun p : ℝ × ℝ × ℝ => if k = 0 ∧ l = 0 then c p.2.2 else 0 := by
    funext p
    rw [jetMixedConst]
  rw [hfun]
  by_cases h : k = 0 ∧ l = 0
  · have h2 : (fun p : ℝ × ℝ × ℝ => if k = 0 ∧ l = 0 then c p.2.2 else (0 : ℝ))
        = fun p : ℝ × ℝ × ℝ => c p.2.2 := by
      funext p; simp [h]
    rw [h2]
    have h3 : Continuous fun p : ℝ × ℝ × ℝ => p.2.2 := by fun_prop
    have := hc.comp h3.continuousOn mapsTo_slab_τ
    simpa [Function.comp_def] using this
  · have h2 : (fun p : ℝ × ℝ × ℝ => if k = 0 ∧ l = 0 then c p.2.2 else (0 : ℝ))
        = fun _ : ℝ × ℝ × ℝ => (0 : ℝ) := by
      funext p; simp [h]
    rw [h2]
    exact continuousOn_const

/-! ## §2 The two angular profiles are `C²` -/

/-- `c2m` is `C²` on the open angular interval. -/
theorem jetContDiffOnC2m :
    ContDiffOn ℝ 2 Work.Construction.c2m (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  Work.FTS_RegExport.RXT.contDiffOn_c2m

/-- `sin²` is `C²` on the open angular interval. -/
theorem jetContDiffOnSinsq :
    ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Real.contDiff_sin.contDiffOn).pow 2

/-! ## §3 Continuity of the angular iterates of a `C²` angular datum

The two-variable operator `D_θ = sin(2θ)·∂_θ` agrees on a function of `θ` alone with the
one-variable operator `Spaces.dthU φ = sin(2·)·φ'` (`Work.FTS.LocData.DthIter_rad_eq`), and
`dthU` lowers the `C^n`-order by one.  Hence for `l ≤ 2` the iterate `D_θ^l b` is continuous
on `(0,π/2)` as soon as `b` is `C²` there. -/

/-- **Continuity of the angular iterates** `D_θ^l b`, `l ≤ 2`, for a `C²` angular datum `b`. -/
theorem jetContOnDthIterAng {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ 2 b (Set.Ioo (0 : ℝ) (Real.pi / 2))) (l : ℕ) (hl : l ≤ 2) :
    ContinuousOn (fun θ => Work.Spaces.DthIter l (fun _ θ' => b θ') 0 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hs : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hrepr : (fun θ => Work.Spaces.DthIter l (fun _ θ' => b θ') 0 θ)
      = Work.Spaces.dthU^[l] b :=
    funext fun θ => Work.FTS.LocData.DthIter_rad_eq l b 0 θ
  rw [hrepr]
  have hd1 : ContDiffOn ℝ 1 (deriv b) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hb.deriv_of_isOpen hs (m := (1 : ℕ∞ω)) (by norm_num)
  have hderivb : ContinuousOn (deriv b) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hb.continuousOn_deriv_of_isOpen hs (by norm_num)
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
  interval_cases l
  · show ContinuousOn (Work.Spaces.dthU^[0] b) (Set.Ioo (0 : ℝ) (Real.pi / 2))
    rw [Function.iterate_zero]
    exact hb.continuousOn
  · show ContinuousOn (Work.Spaces.dthU^[1] b) (Set.Ioo (0 : ℝ) (Real.pi / 2))
    rw [Function.iterate_one]
    have h : Work.Spaces.dthU b = fun θ : ℝ => Real.sin (2 * θ) * deriv b θ :=
      funext fun θ => Work.Spaces.dthU_apply b θ
    rw [h]
    exact hsin.mul hderivb
  · show ContinuousOn (Work.Spaces.dthU^[2] b) (Set.Ioo (0 : ℝ) (Real.pi / 2))
    rw [show Work.Spaces.dthU^[2] b = Work.Spaces.dthU (Work.Spaces.dthU^[1] b) from rfl,
      Function.iterate_one]
    have hsin1 : ContDiffOn ℝ 1 (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
    have hC1 : ContDiffOn ℝ 1 (Work.Spaces.dthU b) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h := hsin1.mul hd1
      refine h.congr fun θ _ => ?_
      rw [Work.Spaces.dthU_apply]
    have hderivdth : ContinuousOn (deriv (Work.Spaces.dthU b))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hC1.continuousOn_deriv_of_isOpen hs (by norm_num)
    have h : Work.Spaces.dthU (Work.Spaces.dthU b)
        = fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.dthU b) θ :=
      funext fun θ => Work.Spaces.dthU_apply (Work.Spaces.dthU b) θ
    rw [h]
    exact hsin.mul hderivdth

/-! ## §4 The `mixed`-jets of a separable datum -/

/-- The `θ`-iterated operator commutes with multiplication by a `z`-only factor. -/
theorem jetDthIterMulLeftZ (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-- `D_θ^i` of a function of `θ` alone does not depend on the radial variable. -/
theorem jetDthIterZIndep (G : ℝ → ℝ) :
    ∀ (i : ℕ) (z z' θ : ℝ),
      Work.Spaces.DthIter i (fun _ θ' => G θ') z θ
        = Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ := by
  intro i
  induction i with
  | zero => intro z z' θ; rfl
  | succ i ih =>
      intro z z' θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z θ') θ
        = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ') θ
      rw [show (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z θ')
          = (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ')
          from funext (fun θ' => ih z z' θ')]

/-- The `z`-iterated operator commutes with multiplication by a `θ`-only factor. -/
theorem jetDzIterMulThetaFactor (j : ℕ) (A : ℝ → ℝ) (B : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A θ * B z θ)
      = fun z θ => A θ * Work.Spaces.DzIter j B z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-- **The `mixed`-jets of a separable datum `h(z)·G(θ)` split** into the product of the radial
jet `D_z^j h` (the one-variable operator `DzdIter`) and the angular jet `D_θ^i G`. -/
theorem jetMixedSep (h : ℝ → ℝ) (G : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => h z * G θ) z θ
      = Work.Elliptic.DzdIter j h z * Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ := by
  rw [Work.Spaces.mixed, jetDthIterMulLeftZ i h (fun _ θ' => G θ')]
  rw [show (fun z θ => h z * Work.Spaces.DthIter i (fun _ θ' => G θ') z θ)
      = fun z θ => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ * h z from by
    funext z θ
    rw [mul_comm, jetDthIterZIndep G i z 0 θ]]
  rw [jetDzIterMulThetaFactor j (fun θ => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ)
    (fun z _ => h z)]
  simp only
  rw [Work.Elliptic.DzIter_rad h j z θ, mul_comm]

/-- **The `mixed`-jets of a radial datum** `h(z)` vanish as soon as one `θ`-derivative is
taken. -/
theorem jetMixedRadial (h : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z _ => h z) z θ
      = if i = 0 then Work.Elliptic.DzdIter j h z else 0 := by
  by_cases hi : i = 0
  · subst hi
    rw [Work.Spaces.mixed, Work.Spaces.DthIter_zero]
    simp only [↓reduceIte]
    exact Work.Elliptic.DzIter_rad h j z θ
  · have hi1 : 1 ≤ i := by omega
    rw [Work.Spaces.mixed, if_neg hi]
    exact congrFun (congrFun (Work.Elliptic.mixed_rad_eq_zero h hi1) z) θ

/-- Pointwise linearity of `mixed` in a constant factor. -/
theorem jetMixedConstMulPt (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ = c * Work.Spaces.mixed j i f z θ := by
  rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul]

/-- The `D_z`-jets of the radial datum, as a function on the slab. -/
theorem jetContOnDzdIterProj {S : ℝ} {a : ℝ → ℝ → ℝ} {k : ℕ}
    (ha : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => a z p.2) p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1) (slb S) := by
  have hφ : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) := by fun_prop
  have := ha.comp hφ.continuousOn mapsTo_slab_zτ
  simpa [Function.comp_def] using this

/-! ## §5 The basic jet conjunction -/

theorem jetBasic :
    (∀ (c : ℝ) (k l : ℕ), Work.Spaces.mixed k l (fun _ _ : ℝ => c)
        = fun _ _ => if k = 0 ∧ l = 0 then c else 0) ∧
    (∀ {S : ℝ} {c : ℝ → ℝ}, ContinuousOn c (Set.Icc 0 S) → ∀ (k l : ℕ),
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed k l (fun _ _ : ℝ => c p.2.2) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S)) ∧
    ContDiffOn ℝ 2 Work.Construction.c2m (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    (∀ {b : ℝ → ℝ}, ContDiffOn ℝ 2 b (Set.Ioo (0 : ℝ) (Real.pi / 2)) → ∀ (l : ℕ), l ≤ 2 →
      ContinuousOn (fun θ => Work.Spaces.DthIter l (fun _ θ' => b θ') 0 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2))) ∧
    (∀ {S c : ℝ} {a : ℝ → ℝ → ℝ} {k l : ℕ},
      ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => a z p.2) p.1)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S) → k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed k l (fun z θ => c * a z p.2.2) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S)) ∧
    (∀ {S : ℝ} {a : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {k l : ℕ},
      ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => a z p.2) p.1)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S) →
      ContinuousOn (fun θ => Work.Spaces.DthIter l (fun _ θ' => b θ') 0 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed k l (fun z θ => a z p.2.2 * b θ) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jetMixedConst
  · intro S c hc k l
    exact jetContOnMixedConst hc k l
  · exact jetContDiffOnC2m
  · exact jetContDiffOnSinsq
  · intro b hb l hl
    exact jetContOnDthIterAng hb l hl
  · intro S c a k l ha hkl
    have hfun : (fun p : ℝ × ℝ × ℝ =>
          Work.Spaces.mixed k l (fun z θ => c * a z p.2.2) p.1 p.2.1)
        = fun p : ℝ × ℝ × ℝ =>
          c * (if l = 0 then Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1 else 0) := by
      funext p
      rw [jetMixedConstMulPt c (fun z θ => a z p.2.2) k l p.1 p.2.1]
      congr 1
      exact jetMixedRadial (fun z => a z p.2.2) k l p.1 p.2.1
    rw [hfun]
    by_cases hl : l = 0
    · have h2 : (fun p : ℝ × ℝ × ℝ =>
          c * (if l = 0 then Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1 else (0 : ℝ)))
          = fun p : ℝ × ℝ × ℝ =>
            c * Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1 := by
        funext p; rw [if_pos hl]
      rw [h2]
      exact (jetContOnDzdIterProj ha).const_mul c
    · have h2 : (fun p : ℝ × ℝ × ℝ =>
          c * (if l = 0 then Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1 else (0 : ℝ)))
          = fun _ : ℝ × ℝ × ℝ => (0 : ℝ) := by
        funext p; rw [if_neg hl]; ring
      rw [h2]
      exact continuousOn_const
  · intro S a b k l ha hb
    have hfun : (fun p : ℝ × ℝ × ℝ =>
          Work.Spaces.mixed k l (fun z θ => a z p.2.2 * b θ) p.1 p.2.1)
        = fun p : ℝ × ℝ × ℝ =>
          Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1
            * Work.Spaces.DthIter l (fun _ θ' => b θ') 0 p.2.1 := by
      funext p
      exact jetMixedSep (fun z => a z p.2.2) b k l p.1 p.2.1
    rw [hfun]
    have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.DthIter l (fun _ θ' => b θ') 0 p.2.1) (slb S) := by
      have hθ : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) := by fun_prop
      have := hb.comp hθ.continuousOn (mapsTo_slab_θ (S := S))
      simpa [Function.comp_def] using this
    exact (jetContOnDzdIterProj ha).mul h2

end Work.FTS_RegExport.RXT0.RXJets
end
end
