import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR7.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXR7.VelLipAux.coeff_contDiffOn_one
import Submission.Work.FTS_RegExport.RXR7.VelLipAux.lipschitz_pair_of_deriv_bounds_le

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
