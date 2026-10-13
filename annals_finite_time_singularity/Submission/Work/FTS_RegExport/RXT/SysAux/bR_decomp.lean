import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXT.SysAux.dense_diffAt
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Sanitize

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.bR_decomp`

The `Θ`-decomposition `bR = 2·Uop β Φ̃/sin 2θ + 2·Uop β (Θ β F)/sin 2θ` of the `θ`-coefficient
`bR = Vθ7/sin 2θ = 2·Uop β (slice Φ σ)/sin 2θ`, where `Φ = ΦR α Φs E g` is the *full* stream
function — an arbitrary function of `(z,θ)` as far as the hypotheses go, so that the additivity
`Uop β Φ = Uop β Φ̃ + Uop β (Θ β F)` (equivalently `deriv_sub` on the `z`-slices) is **not**
available as a hypothesis.  It is recovered from `hC2` (the `C²`-ness of the three coefficients)
by the following density argument, whose structural input is
`SysAux/dense_diffAt.exists_differentiableAt_of_slice_identity`:

* the *correction* `Corr := bR - 2·Uop β Φ̃/sin 2θ - 2·Uop β (Θ β F)/sin 2θ` vanishes at every
  `z` at which the `z`-slice of `Φ` is differentiable (`deriv_sub`, twice);
* the set of such `z` has empty complement-interior (because on an interval where the slice is
  nowhere differentiable the definition `sin 2θ·bR = -6Φ - 2β z ∂_zΦ` forces `Φ` to agree with
  the `C²` function `-sin 2θ·bR/6`), so it is dense in `(0,∞)`;
* `Corr` is continuous on `(0,∞)`: the only non-obvious continuity is that of
  `Uop β Φ̃`, which follows from `Uop Ψ = cot θ·(Vop Ψ - Rop β Ψ)` together with the *closed
  forms* `Vz7 = (1-μ) + L₁₂(F)c2m + 2β Vop Φ̃` and `cs7 = (1+μ) - L₁₂(F)/β + sin²θ·𝔽K(F) - 2 Rop β Φ̃`
  of the two `C²` coefficients `VR`, `cR` given by `hC2`.  (This is where the two *extra*
  conjuncts of `hC2` — not just the `bR` one — are used: they are the *only* source of the
  continuity of the perturbed slots `Vop Φ̃`, `Rop β Φ̃`.)  The continuity of the `Θ`-part is
  obtained from `L₁₂(F) ∈ C³(0,∞)`, which is a consequence of `DynOK'` alone
  (`contDiffOn_Ftau_Q0` + `Ftau_bounds` + `contDiffOn_two_integral_Itheta` +
  `C2Radial.contDiffOn_three_L12`).
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two auxiliary lemmas -/

/-- A continuous function on `(0,∞)` whose zero set meets every open subinterval of `(0,∞)`
vanishes identically. -/
private lemma dense_eq_zero_of_continuousOn {f : ℝ → ℝ}
    (hd : ∀ a c : ℝ, 0 < a → a < c → ∃ w ∈ Set.Ioo a c, f w = 0)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z → f z = 0 := by
  intro z hz
  classical
  have hδ0 : ∀ n : ℕ, 0 < min (z / 2) (1 / ((n : ℝ) + 1)) :=
    fun n => lt_min (by linarith) (by positivity)
  have hδle : ∀ n : ℕ, min (z / 2) (1 / ((n : ℝ) + 1)) ≤ z / 2 := fun n => min_le_left _ _
  have hex : ∀ n : ℕ, ∃ w : ℝ,
      w ∈ Set.Ioo (z - min (z / 2) (1 / ((n : ℝ) + 1))) (z + min (z / 2) (1 / ((n : ℝ) + 1)))
        ∧ f w = 0 := by
    intro n
    exact hd _ _ (by have := hδle n; linarith) (by have := hδ0 n; linarith)
  let w : ℕ → ℝ := fun n => Classical.choose (hex n)
  have hw : ∀ n : ℕ, w n ∈ Set.Ioo (z - min (z / 2) (1 / ((n : ℝ) + 1)))
      (z + min (z / 2) (1 / ((n : ℝ) + 1))) ∧ f (w n) = 0 := fun n =>
    Classical.choose_spec (hex n)
  have hδlim : Tendsto (fun n : ℕ => min (z / 2) (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => le_min (by linarith) (by positivity))
      (fun n => min_le_right _ _) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have habs : ∀ n : ℕ, ‖w n - z‖ ≤ min (z / 2) (1 / ((n : ℝ) + 1)) := by
    intro n
    have h1 := (hw n).1
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hlim0 : Tendsto (fun n : ℕ => w n - z) atTop (𝓝 0) :=
    squeeze_zero_norm' (Filter.Eventually.of_forall habs) hδlim
  have hlimw : Tendsto w atTop (𝓝 z) := by
    have h := hlim0.add (tendsto_const_nhds (x := z) : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
    simpa using h
  have hcont : ContinuousAt f z := hf.continuousAt (isOpen_Ioi.mem_nhds hz)
  have htend : Tendsto (fun n : ℕ => f (w n)) atTop (𝓝 (f z)) := hcont.tendsto.comp hlimw
  have hconst : (fun n : ℕ => f (w n)) = fun _ : ℕ => (0 : ℝ) := funext fun n => (hw n).2
  rw [hconst] at htend
  exact (tendsto_nhds_unique
    (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    htend).symm

/-- **The correction vanishes at the differentiability points of the slice**:  at every `z` at
which the `z`-slice of the full stream function `Φ` is differentiable (and where `L₁₂(F)` is
differentiable), all of `Φ̃ = Φ - Θ(F)`, `Θ(F)` are differentiable there too and `deriv_sub` gives
the additivity `Uop β Φ = Uop β Φ̃ + Uop β (Θ β F)` of the split of `bR`. -/
private lemma corr_zero_of_diffAt {α : ℝ} (hα : 0 < α)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {σ θ z : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hzd : DifferentiableAt ℝ
      (fun z' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z' θ σ) z)
    (hLd : DifferentiableAt ℝ (fun z' => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z) :
    Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
      - 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
          / Real.sin (2 * θ))
      - 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ))
      = 0 := by
  have hs2 : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθπ, Real.pi_pos]))
  have hβne : Work.FTS.Regularity.pExp α ≠ 0 :=
    ne_of_gt (Work.FTS.Regularity.pExp_pos hα)
  have hBd : DifferentiableAt ℝ (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ) z := by
    have h2 : (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ)
        = fun z' => ((1 / (4 * Work.FTS.Regularity.pExp α)) * Real.sin (2 * θ))
            * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z' := by
      funext z'
      simp only [Work.Construction.Theta, Work.Construction.s2]
    rw [h2]
    exact hLd.const_mul _
  have hderiv : deriv (fun z' => Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ z' θ) z
      = deriv (fun z' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z' θ σ) z
        - deriv (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ) z := by
    have hfun : (fun z' => Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ z' θ)
        = (fun z' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z' θ σ)
          - (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ) := by
      funext z'
      simp only [Work.FTS.RegExportIface.phiTil, Work.Construction.PhiTil,
        Work.FTS.Galerkin.slice, Pi.sub_apply]
    rw [hfun, deriv_sub hzd hBd]
  simp only [Work.FTS.RegExportIface.RXT.bR, Work.FTS.RegExportIface.Vθ7,
    Work.Construction.Uop, Work.Spaces.pz, Work.FTS.Galerkin.slice]
  rw [hderiv]
  simp only [Work.FTS.RegExportIface.phiTil, Work.Construction.PhiTil, Work.FTS.Galerkin.slice,
    Work.Construction.Theta, Work.Construction.s2]
  field_simp
  ring

/-! ## The regularity of `L₁₂(F(σ))` and `𝔽K(F(σ))`, from `DynOK'` -/

/-- `L₁₂(F)` is `C³` on `(0,∞)` and `𝔽K(F)` is `C²` on `(0,∞)`, for the full profile
`F = Ftau β (GR α g) σ`, as a consequence of `DynOK'` alone: it suffices that `F` be `C²` on the
open quadrant and bounded, `Ftau_bounds`. -/
theorem L12FK_of_DynOK {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ContinuousOn (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) ∧
      ContinuousOn (fun z => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) ∧
      ContinuousOn (deriv (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) := by
  have hF2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK σ hσ
  obtain ⟨Cb, -, hbnd⟩ :=
    Work.FTS_RegExport.RXT.Ftau_bounds (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hα hα13 hOK σ hσ
  have hKcont : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
    ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
  have hFK2 : ContDiffOn ℝ 2 (fun z => Work.Construction.FK
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K) hKcont hF2 hbnd
  have hL3 : ContDiffOn ℝ 3 (fun z => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2
  have hder : ContinuousOn (deriv (fun z => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z)) (Set.Ioi 0) := by
    have h3 : ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) := by
      rw [show (2 : WithTop ℕ∞) + 1 = 3 from by norm_num]
      exact hL3
    exact (((contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := (2 : WithTop ℕ∞))
      isOpen_Ioi).mp h3).2.2).continuousOn
  exact ⟨hL3.continuousOn, hFK2.continuousOn, hder, hL3.differentiableOn (by norm_num)⟩

/-! ## The continuity of the two pieces of the correction -/

/-- The continuity of the perturbed slot `Uop β Φ̃` (from the closed forms of `Vz7`, `cs7` and
`Uop Ψ = cot θ·(Vop Ψ - Rop β Ψ)`) and of the singular slot `2·Uop β (Θ β F)/sin 2θ` (from the
`C³`-regularity of `L₁₂(F)`), at fixed `θ ∈ (0, π/2)`. -/
theorem bR_slotcont_of_DynOK {α C₀ : ℝ} (hα : 0 < α)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hL12con : ContinuousOn (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0))
    (hFKcon : ContinuousOn (fun z => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0))
    (hL12diff : DifferentiableOn ℝ (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0))
    (hderivL12con : ContinuousOn (deriv (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z)) (Set.Ioi 0))
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    ContinuousOn (fun z => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
        z θ) (Set.Ioi 0) ∧
      ContinuousOn (fun z => 2 * Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)) (Set.Ioi 0) := by
  have hβne : Work.FTS.Regularity.pExp α ≠ 0 :=
    ne_of_gt (Work.FTS.Regularity.pExp_pos hα)
  have hsinθ : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos]))
  have hcosθ : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    exact ne_of_gt h
  have hs2 : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hVopC : ContinuousOn (fun z => Work.Construction.Vop (Work.FTS.RegExportIface.phiTil
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
      (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ) (Set.Ioi 0) := by
    have hVRc : ContinuousOn (fun z => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ) (Set.Ioi 0) :=
      (((hC2 σ hσ).1).comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ)))
        (fun w hw => ⟨hw, hθ, hθπ⟩)).continuousOn
    have hid : (fun z => Work.Construction.Vop (Work.FTS.RegExportIface.phiTil
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ)
        = fun z => (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ
            - (1 - Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
            - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) σ) z * Work.Construction.c2m θ)
          / (2 * Work.FTS.Regularity.pExp α) := by
      funext z
      simp only [Work.FTS.RegExportIface.Vz7]
      field_simp
      ring
    rw [hid]
    exact ((hVRc.sub continuousOn_const).sub (hL12con.mul_const _)).div_const _
  have hRopC : ContinuousOn (fun z => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
      z θ) (Set.Ioi 0) := by
    have hcRc : ContinuousOn (fun z => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ) (Set.Ioi 0) :=
      (((hC2 σ hσ).2.2).comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ)))
        (fun w hw => ⟨hw, hθ, hθπ⟩)).continuousOn
    have hid : (fun z => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
        z θ)
        = fun z => ((1 + Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
            - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) σ) z / Work.FTS.Regularity.pExp α
            + (Real.sin θ) ^ 2 * Work.Construction.FK
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) σ) z
            - Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ) / 2 := by
      funext z
      simp only [Work.FTS.RegExportIface.cs7]
      field_simp
      ring
    rw [hid]
    exact (((continuousOn_const.add continuousOn_const).sub
      (hL12con.div_const _)).add (continuousOn_const.mul hFKcon)).sub hcRc |>.div_const _
  have hUopC : ContinuousOn (fun z => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
      z θ) (Set.Ioi 0) := by
    have halg : ∀ z, Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
        = (Real.cos θ / Real.sin θ) * (Work.Construction.Vop (Work.FTS.RegExportIface.phiTil
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
            (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
          - Work.Construction.Rop (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.phiTil
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
            (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ) := by
      intro z
      simp only [Work.Construction.Uop, Work.Construction.Vop, Work.Construction.Rop,
        Work.Spaces.pth, Work.Spaces.pz, Real.tan_eq_sin_div_cos]
      field_simp
      ring
    exact ContinuousOn.congr ((hVopC.sub hRopC).mul_const (Real.cos θ / Real.sin θ)) (fun z _ => by
      rw [halg z]
      simp only [Pi.sub_apply]
      ring_nf)
  refine ⟨hUopC, ?_⟩
  have hcontRHS : ContinuousOn (fun z => -(3 / (2 * Work.FTS.Regularity.pExp α))
      * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z
      - (1 / 2) * (z * deriv (fun z' => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z)) (Set.Ioi 0) :=
    (continuousOn_const.mul hL12con).sub
      (continuousOn_const.mul (continuousOn_id.mul hderivL12con))
  refine ContinuousOn.congr hcontRHS (fun z hz => ?_)
  have hd : DifferentiableAt ℝ (fun z' => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z :=
    (hL12diff z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have h1 : (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ)
      = fun z' => ((1 / (4 * Work.FTS.Regularity.pExp α)) * Real.sin (2 * θ))
          * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z' := by
    funext z'
    simp only [Work.Construction.Theta, Work.Construction.s2]
  simp only [Work.Construction.Uop, Work.Spaces.pz]
  rw [h1, deriv_const_mul _ hd]
  simp only [Work.Construction.Theta, Work.Construction.s2]
  field_simp
  ring_nf

/-! ## The core: the decomposition from the continuity of the correction -/

/-- **The `Θ`-decomposition of `bR` from the continuity of the correction.**  The hypotheses
beyond `hC2` are exactly what the density argument consumes: `hL12diff` makes `Θ β F`
differentiable, and `hUopC`/`hUC` are the two continuity statements for the pieces of the
correction other than `bR` (provided by `bR_slotcont_of_DynOK`). -/
theorem bR_decomp_of_infra {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) S)
    (hL12diff : ∀ w : ℝ, 0 < w → DifferentiableAt ℝ (fun z' => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z') w)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hUopC : ContinuousOn (fun z => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ)
        (Set.Ioi 0))
    (hUC : ContinuousOn (fun z => 2 * Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)) (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        = 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
              z θ / Real.sin (2 * θ))
          + 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)) := by
  intro z hz
  let Φt : ℝ → ℝ → ℝ := Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ
  let Θt : ℝ → ℝ → ℝ := Work.Construction.Theta (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ)
  let Corr : ℝ → ℝ := fun w => Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ
      - 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) Φt w θ / Real.sin (2 * θ))
      - 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) Θt w θ / Real.sin (2 * θ))
  have hbRc2 : ContDiffOn ℝ 2
      (fun w : ℝ => Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ) (Set.Ioi 0) :=
    ((hC2 σ hσ.1).2.1).comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ)))
      (fun w hw => ⟨hw, hθ, hθπ⟩)
  have hbRcont : ContinuousOn (fun w : ℝ => Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ)
      (Set.Ioi 0) := hbRc2.continuousOn
  have hbd : DifferentiableOn ℝ (fun w : ℝ => Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ)
      (Set.Ioi 0) := hbRc2.differentiableOn (by norm_num)
  have hU1 : ContinuousOn (fun w : ℝ => 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
      Φt w θ / Real.sin (2 * θ))) (Set.Ioi 0) := by
    refine ContinuousOn.congr (hUopC.const_mul (2 / Real.sin (2 * θ))) ?_
    intro w _
    ring
  have hU2 : ContinuousOn (fun w : ℝ => 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
      Θt w θ / Real.sin (2 * θ))) (Set.Ioi 0) := by
    refine ContinuousOn.congr hUC ?_
    intro w _
    ring
  have hCorrC : ContinuousOn Corr (Set.Ioi 0) := (hbRcont.sub hU1).sub hU2
  have hb : ∀ w : ℝ, 0 < w → Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ
      = 2 * (-3 * Work.FTS.RegExportIface.RXT.ΦR α Φs E g w θ σ
          - Work.FTS.Regularity.pExp α * w
            * deriv (fun z' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z' θ σ) w)
        / Real.sin (2 * θ) := by
    intro w hw
    simp only [Work.FTS.RegExportIface.RXT.bR, Work.FTS.RegExportIface.Vθ7,
      Work.Construction.Uop, Work.Spaces.pz, Work.FTS.Galerkin.slice]
  have hdens : ∀ a c : ℝ, 0 < a → a < c → ∃ w ∈ Set.Ioo a c, Corr w = 0 := by
    intro a c ha hac
    obtain ⟨w, hw, hdw⟩ := exists_differentiableAt_of_slice_identity
      (β := Work.FTS.Regularity.pExp α) (θ := θ)
      (b := fun z θ' => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ' σ)
      (Φ := fun z θ' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z θ' σ)
      (Work.FTS.Regularity.pExp_pos hα) hθ hθπ hb hbd ha hac
    exact ⟨w, hw, corr_zero_of_diffAt hα hθ hθπ hdw (hL12diff w (lt_trans ha hw.1))⟩
  have hCorr0 : ∀ w : ℝ, 0 < w → Corr w = 0 :=
    dense_eq_zero_of_continuousOn hdens hCorrC
  have hfin : Corr z = 0 := hCorr0 z hz
  simp only [Corr] at hfin
  linarith

/-- **The `Θ`-decomposition of the `θ`-coefficient.**  The coefficient
`bR = Vθ7/sin 2θ = 2·Uop β (slice Φ σ)/sin 2θ` (with `Φ = ΦR α Φs E g` the *full* stream function,
an arbitrary function of `(z,θ)`) splits as the perturbation part `2·Uop β Φ̃/sin 2θ`
(`Φ̃ = phiTil β (GR α g) (ΦR α Φs E g) σ`) plus the closed-form singular part
`2·Uop β (Θ β F)/sin 2θ` (`F = Ftau β (GR α g) σ`) — i.e. the "additivity of `Uop`" that is *not*
available as a hypothesis, recovered from `hC2` (`bR` is `C²`) by the density argument of
`SysAux/dense_diffAt`. -/
theorem bR_decomp {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0)
    (hw : ∃ C : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :
    ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        = 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
              z θ / Real.sin (2 * θ))
          + 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)) := by
  intro σ hσ z θ hz hθ hθπ
  obtain ⟨hL12con, hFKcon, hderivL12con, hL12diff⟩ := L12FK_of_DynOK hα hα13 hOK hσ.1
  obtain ⟨hUopC, hUC⟩ := bR_slotcont_of_DynOK (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hα hC2 hσ.1
    hL12con hFKcon hL12diff hderivL12con hθ hθπ
  exact bR_decomp_of_infra (C₀ := C₀) (S := S) hα hα13 hS hC2 hσ
    (fun w hw' => (hL12diff w hw').differentiableAt (isOpen_Ioi.mem_nhds hw')) hθ hθπ hUopC hUC z hz

end Work.FTS_RegExport.RXT.SysAux
