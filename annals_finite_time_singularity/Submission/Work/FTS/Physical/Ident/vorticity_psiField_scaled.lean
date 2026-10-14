import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.vorticity_psiField_bslOp
import Submission.Work.R1G3.bslOp_scale
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {f g : ℝ → ℝ → ℝ}

/-! ## The dilation and the difference quotient -/

/-- The dilation `(dil c f) z θ = f (c z) θ` of `f` in the radial variable. -/
def dil (c : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f (c * z) θ

/-- The radial difference quotient `(dq c f) z θ = (f (c z) θ - f z θ)/(c-1)`. -/
def dq (c : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (f (c * z) θ - f z θ) / (c - 1)

@[simp] theorem dil_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : dil c f z θ = f (c * z) θ := rfl

@[simp] theorem dq_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    dq c f z θ = (f (c * z) θ - f z θ) / (c - 1) := rfl




/-! ## Smoothness -/

theorem smoothOpen_dil {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 0 < c) :
    SmoothOpen (dil c f) := by
  rw [smoothOpen_iff_forall] at hf ⊢
  intro n
  have hmap : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((c * p.1, p.2) : ℝ × ℝ)) Q0 := by
    fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => ((c * p.1, p.2) : ℝ × ℝ)) Q0 Q0 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact mem_Q0.mpr ⟨mul_pos hc hz, hθ0, hθ1⟩
  have hcomp := (hf n).comp hmap hmaps
  convert hcomp using 1
  funext p
  rfl

theorem smoothOpen_dq {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 0 < c) :
    SmoothOpen (dq c f) := by
  have hfun : dq c f = fun z θ => (dil c f z θ - f z θ) / (c - 1) := rfl
  rw [hfun]
  exact ((smoothOpen_dil hf hc).sub hf).div_const _

/-! ## The `z`-derivatives of a dilation

All the statements are pointwise on the open quadrant, where the slices of `f` are smooth. -/


theorem slice_diff_θ {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ :=
  (hf.curry_θ hz).differentiableOn (by simp) |>.differentiableAt (Ioo_mem_nhds hθ.1 hθ.2)

theorem hasDerivAt_dil {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 0 < c) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun z' : ℝ => f (c * z') θ) (c * Work.Spaces.pz f (c * z) θ) z := by
  have h1 : HasDerivAt (fun z' : ℝ => f z' θ) (Work.Spaces.pz f (c * z) θ) (c * z) :=
    hf.hasDerivAt_slice hθ (mul_pos hc hz)
  have h2 : HasDerivAt (fun z' : ℝ => c * z') c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have h3 := h1.comp z h2
  simpa only [Function.comp_def, mul_comm] using h3

theorem pz_dil {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 0 < c) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (dil c f) z θ = c * Work.Spaces.pz f (c * z) θ := by
  have h := hasDerivAt_dil hf hc hz hθ
  rw [show Work.Spaces.pz (dil c f) z θ = deriv (fun z' : ℝ => f (c * z') θ) z from rfl]
  exact h.deriv

theorem hasDerivAt_dil_pzIter {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 0 < c)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter j f (c * z') θ)
      (c * Work.Spaces.pzIter (j + 1) f (c * z) θ) z := by
  have h1 : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter j f z' θ)
      (Work.Spaces.pzIter (j + 1) f (c * z) θ) (c * z) :=
    (hf.pzIter j).hasDerivAt_slice hθ (mul_pos hc hz)
  have h2 : HasDerivAt (fun z' : ℝ => c * z') c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have h3 := h1.comp z h2
  simpa only [Function.comp_def, mul_comm] using h3

theorem pzIter_dil {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pzIter j (dil c f) z θ = c ^ j * Work.Spaces.pzIter j f (c * z) θ := by
  induction j with
  | zero => intro z θ _ _; simp
  | succ j ih =>
    intro z θ hz hθ
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
    show deriv (fun z' : ℝ => Work.Spaces.pzIter j (dil c f) z' θ) z
        = c ^ (j + 1) * Work.Spaces.pzIter (j + 1) f (c * z) θ
    have hev : (fun z' : ℝ => Work.Spaces.pzIter j (dil c f) z' θ)
        =ᶠ[𝓝 z] (fun z' : ℝ => c ^ j * Work.Spaces.pzIter j f (c * z') θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      rw [ih z' θ hz' hθ]
    rw [hev.deriv_eq]
    rw [deriv_const_mul_field]
    rw [(hasDerivAt_dil_pzIter hf hc j hz hθ).deriv]
    ring




/-! ## The `θ`-derivatives of a dilation (they pass through) -/

theorem pthIter_dil (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.pthIter i (dil c f) = fun z θ => Work.Spaces.pthIter i f (c * z) θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ]
    funext z θ
    show deriv (fun θ' : ℝ => Work.Spaces.pthIter i (dil c f) z θ') θ
        = deriv (fun θ' : ℝ => Work.Spaces.pthIter i f (c * z) θ') θ
    congr 1
    funext θ'
    exact congrFun (congrFun ih z) θ'

theorem Lzero_dil {f : ℝ → ℝ → ℝ} (c : ℝ) :
    Work.Elliptic.Lzero (dil c f) = fun z θ => Work.Elliptic.Lzero f (c * z) θ := by
  have hτ : (fun z θ => Real.tan θ * (dil c f) z θ)
      = dil c (fun z θ => Real.tan θ * f z θ) := by
    funext z θ; rfl
  funext z θ
  rw [show Work.Elliptic.Lzero (dil c f) z θ
      = -(Work.Spaces.pthIter 2 (dil c f) z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * (dil c f) z θ) z θ
        - 6 * (dil c f) z θ from rfl]
  rw [hτ]
  rw [show Work.Spaces.pth (dil c (fun z θ => Real.tan θ * f z θ)) z θ
      = Work.Spaces.pthIter 1 (dil c (fun z θ => Real.tan θ * f z θ)) z θ from rfl]
  rw [pthIter_dil c (fun z θ => Real.tan θ * f z θ) 1]
  rw [pthIter_dil c f 2]
  rfl

theorem bslOp_dil {f : ℝ → ℝ → ℝ} (α : ℝ) (hf : SmoothOpen f) {c : ℝ} (hc : 0 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Elliptic.bslOp α (dil c f) z θ = Work.Elliptic.bslOp α f (c * z) θ := by
  intro z θ hz hθ
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.bslOp_apply,
    pzIter_dil hf hc 2 z θ hz hθ, pz_dil hf hc hz hθ]
  have h2 : Work.Elliptic.Lzero (dil c f) z θ = Work.Elliptic.Lzero f (c * z) θ :=
    congrFun (congrFun (Lzero_dil c) z) θ
  rw [h2]
  ring

/-! ## The angular moment of a dilation -/


/-! ## The difference quotient

The `z`-derivatives of a difference quotient are difference quotients of the derivatives; the
`θ`-derivatives pass through.  Everything is pointwise on the open quadrant. -/

theorem pz_dq {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (dq c f) z θ
        = (c * Work.Spaces.pz f (c * z) θ - Work.Spaces.pz f z θ) / (c - 1) := by
  intro z θ hz hθ
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hsub := (hasDerivAt_dil hf hcpos hz hθ).sub (hf.hasDerivAt_slice hθ hz)
  have hdiv := hsub.div_const (c - 1)
  rw [show Work.Spaces.pz (dq c f) z θ
      = deriv (fun z' : ℝ => (f (c * z') θ - f z' θ) / (c - 1)) z from rfl]
  exact hdiv.deriv

theorem pzIter_two_dq {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pzIter 2 (dq c f) z θ
        = (c ^ 2 * Work.Spaces.pzIter 2 f (c * z) θ - Work.Spaces.pzIter 2 f z θ)
            / (c - 1) := by
  intro z θ hz hθ
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hev : (fun z' : ℝ => Work.Spaces.pz (dq c f) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ =>
        (c * Work.Spaces.pz f (c * z') θ - Work.Spaces.pz f z' θ) / (c - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact pz_dq hf hc z' θ hz' hθ
  rw [Work.Spaces.pzIter_succ]
  show deriv (fun z' : ℝ => Work.Spaces.pz (dq c f) z' θ) z = _
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun z' : ℝ => c * Work.Spaces.pz f (c * z') θ)
      (c * (c * Work.Spaces.pzIter 2 f (c * z) θ)) z :=
    (hasDerivAt_dil_pzIter hf hcpos 1 hz hθ).const_mul c
  have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz f z' θ) (Work.Spaces.pzIter 2 f z θ) z :=
    (hf.pz).hasDerivAt_slice hθ hz
  have hgoal : HasDerivAt
      (fun z' : ℝ => (c * Work.Spaces.pz f (c * z') θ - Work.Spaces.pz f z' θ) / (c - 1))
      ((c * (c * Work.Spaces.pzIter 2 f (c * z) θ) - Work.Spaces.pzIter 2 f z θ) / (c - 1)) z :=
    (h1.sub h2).div_const (c - 1)
  rw [hgoal.deriv]
  ring

theorem zsq_pzIter_two_dq {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      z ^ 2 * Work.Spaces.pzIter 2 (dq c f) z θ
        = dq c (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ := by
  intro z θ hz hθ
  rw [pzIter_two_dq hf hc z θ hz hθ, dq_apply]
  have hnz : c * z ≠ 0 := ne_of_gt (mul_pos (lt_trans zero_lt_one hc) hz)
  have hne : c - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp

theorem pth_dq {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pth (dq c f) z θ
        = (Work.Spaces.pth f (c * z) θ - Work.Spaces.pth f z θ) / (c - 1) := by
  intro z θ hz hθ'
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have h1 := slice_diff_θ hf (mul_pos hcpos hz) hθ'
  have h2 := slice_diff_θ hf hz hθ'
  have hgoal : HasDerivAt (fun θ' : ℝ => (f (c * z) θ' - f z θ') / (c - 1))
      ((Work.Spaces.pth f (c * z) θ - Work.Spaces.pth f z θ) / (c - 1)) θ :=
    (h1.hasDerivAt.sub h2.hasDerivAt).div_const (c - 1)
  show deriv (fun θ' : ℝ => (f (c * z) θ' - f z θ') / (c - 1)) θ = _
  exact hgoal.deriv

theorem pthIter_two_dq {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {c : ℝ} (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pthIter 2 (dq c f) z θ
        = (Work.Spaces.pthIter 2 f (c * z) θ - Work.Spaces.pthIter 2 f z θ) / (c - 1) := by
  intro z θ hz hθ
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hev : (fun θ' : ℝ => Work.Spaces.pth (dq c f) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ =>
        (Work.Spaces.pth f (c * z) θ' - Work.Spaces.pth f z θ') / (c - 1)) := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with θ' hθ'
    exact pth_dq hf hc z θ' hz hθ'
  rw [Work.Spaces.pthIter_succ]
  show deriv (fun θ' : ℝ => Work.Spaces.pth (dq c f) z θ') θ = _
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth f (c * z) θ')
      (Work.Spaces.pthIter 2 f (c * z) θ) θ :=
    (slice_diff_θ (hf.pth) (mul_pos hcpos hz) hθ).hasDerivAt
  have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth f z θ')
      (Work.Spaces.pthIter 2 f z θ) θ :=
    (slice_diff_θ (hf.pth) hz hθ).hasDerivAt
  have hgoal : HasDerivAt
      (fun θ' : ℝ => (Work.Spaces.pth f (c * z) θ' - Work.Spaces.pth f z θ') / (c - 1))
      ((Work.Spaces.pthIter 2 f (c * z) θ - Work.Spaces.pthIter 2 f z θ) / (c - 1)) θ :=
    (h1.sub h2).div_const (c - 1)
  exact hgoal.deriv

theorem bslOp_dq {f : ℝ → ℝ → ℝ} (α : ℝ) (hf : SmoothOpen f) {c : ℝ} (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Elliptic.bslOp α (dq c f) z θ
        = (Work.Elliptic.bslOp α f (c * z) θ - Work.Elliptic.bslOp α f z θ) / (c - 1) := by
  intro z θ hz hθ
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hp : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    ((smoothOpen_iff_forall f).mp hf 2).contDiffAt (isOpen_Q0.mem_nhds hp)
  have hcd' : ContDiffAt ℝ 2 (Function.uncurry (dil c f)) (z, θ) :=
    ((smoothOpen_iff_forall (dil c f)).mp (smoothOpen_dil hf hcpos) 2).contDiffAt
      (isOpen_Q0.mem_nhds hp)
  have hfun : dq c f = fun z θ => (c - 1)⁻¹ * ((dil c f) z θ - f z θ) := by
    funext z' θ'
    rw [dq_apply]
    simp only [dil_apply]
    ring
  rw [hfun]
  rw [Work.R1G3.bslOp_const_mul α (c - 1)⁻¹ (fun z θ => (dil c f) z θ - f z θ) z θ
    (by simpa only [Function.uncurry] using hcd'.sub hcd)]
  rw [Work.FTS.EllipticEst.bslOp_sub α (dil c f) f z θ hcos hcd' hcd]
  rw [bslOp_dil α hf hcpos z θ hz hθ]
  field_simp

end Work.FTS.EllipticEst.Cores.Dil
end
end
-- ===== merged: Submission.Work.FTS.Physical.Ident.vorticity_psiField_scaled =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.Physical.Ident

/-- **The curl identity at the rescaled stream function.**  For the stream function
`ψ(r,z) = ρ(r,z)²·Φ(ρ(r,z)^p/B, θ(r,z))` — the ansatz of the dynamic rescaling — the vorticity off
the axis is `-(bslOp p Φ (ρ(x)^p/B, θ(x))) • e_θ(x)`. -/
theorem vorticity_psiField_scaled {p B : ℝ} (hB : B ≠ 0) {Φ : ℝ → ℝ → ℝ}
    (x : Work.Cyl.R3) (hx : 0 < Work.Cyl.radial x)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2)
      (Work.Cyl.rho x ^ p / B, Work.Cyl.theta x)) :
    FiniteTimeSingularity.vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
        * Φ (Work.Cyl.rhoP r z ^ p / B) (Work.Cyl.thetaP r z))) x
      = -(Work.Elliptic.bslOp p Φ (Work.Cyl.rho x ^ p / B) (Work.Cyl.theta x))
          • Work.Cyl.eTheta x := by
  -- the rescaled stream function is `Φ_B(ρ^p)` with `Φ_B(w,θ) = Φ(w/B,θ)`
  have hfun : (fun r z => Work.Cyl.rhoP r z ^ 2 * Φ (Work.Cyl.rhoP r z ^ p / B)
        (Work.Cyl.thetaP r z))
      = fun r z => Work.Cyl.rhoP r z ^ 2
          * (fun w θ' => Φ (w / B) θ') (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z) := rfl
  rw [hfun]
  -- the `C²` hypothesis transported to `Φ_B` at `(ρ(x)^p, θ(x))`
  have hΦB : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (fun w θ' => Φ (w / B) θ') q.1 q.2)
      (Work.Cyl.rho x ^ p, Work.Cyl.theta x) := by
    have hcomp : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (q.1 / B, q.2))
        (Work.Cyl.rho x ^ p, Work.Cyl.theta x) :=
      (contDiffAt_fst.div_const B).prodMk contDiffAt_snd
    exact hΦ.comp (Work.Cyl.rho x ^ p, Work.Cyl.theta x) hcomp
  rw [Work.R1G.vorticity_psiField_bslOp p (fun w θ' => Φ (w / B) θ') x hx hΦB,
    Work.R1G3.bslOp_scale p B hB Φ (Work.Cyl.rho x ^ p) (Work.Cyl.theta x) hΦ]

end Work.FTS.Physical.Ident
end
