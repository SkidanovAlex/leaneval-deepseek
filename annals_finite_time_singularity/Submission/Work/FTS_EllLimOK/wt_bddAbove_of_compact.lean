import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.HalfInfra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.Half

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Elementary local helpers (replacing lemmas that live in the heavy `DivSinPerZ`) -/

/-- `sin(2θ) > 0` on `(0, π/2)`. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])





/-! ## The half-strip -/





/-! ## `⊤`-smoothness on an open set is preserved by the operators

The proofs are those of `Work.Spaces.SmoothNbhd.Dz`, `.Dth`, `.DzIter`, `.DthIter`, with the
fixed neighbourhood `nbhU` replaced by an arbitrary open set `V`. -/

theorem contDiffOn_uncurry_Dz {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz f)) V := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) V :=
    ContDiffOn.fderiv_of_isOpen h hV (by simp)
  have hev : ContDiffOn ℝ ⊤
      (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      y.1 * (fderiv ℝ (Function.uncurry f) y) (1, 0)) V :=
    (contDiff_fst.contDiffOn).mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt h (hV.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun z' => Function.uncurry f (z', y.2)) y.1
      = (fderiv ℝ (Function.uncurry f) y) (1, 0) :=
    Work.Spaces.deriv_slice_fst (Function.uncurry f) y.1 y.2 hdiff
  show y.1 * deriv (fun z' => Function.uncurry f (z', y.2)) y.1
      = y.1 * (fderiv ℝ (Function.uncurry f) y) (1, 0)
  rw [hderiv]

theorem contDiffOn_uncurry_Dth {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dth f)) V := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) V :=
    ContDiffOn.fderiv_of_isOpen h hV (by simp)
  have hev : ContDiffOn ℝ ⊤
      (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  have hsin : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => Real.sin (2 * y.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      Real.sin (2 * y.2) * (fderiv ℝ (Function.uncurry f) y) (0, 1)) V := hsin.mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt h (hV.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun θ' => Function.uncurry f (y.1, θ')) y.2
      = (fderiv ℝ (Function.uncurry f) y) (0, 1) :=
    Work.Spaces.deriv_slice_snd (Function.uncurry f) y.1 y.2 hdiff
  show Real.sin (2 * y.2) * deriv (fun θ' => Function.uncurry f (y.1, θ')) y.2
      = Real.sin (2 * y.2) * (fderiv ℝ (Function.uncurry f) y) (0, 1)
  rw [hderiv]

theorem contDiffOn_uncurry_DzIter {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter n f)) V := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [Work.Spaces.DzIter_succ]; exact contDiffOn_uncurry_Dz hV ih

theorem contDiffOn_uncurry_DthIter {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter n f)) V := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [Work.Spaces.DthIter_succ]; exact contDiffOn_uncurry_Dth hV ih


/-! ## Congruence of the operators under equality on an open set -/

theorem pz_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) {p : ℝ × ℝ} (hp : p ∈ V) :
    Work.Spaces.pz g p.1 p.2 = Work.Spaces.pz g' p.1 p.2 := by
  have hnb : ∀ᶠ z' in 𝓝 p.1, (z', p.2) ∈ V :=
    (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun z' => Function.uncurry g (z', p.2)) =ᶠ[𝓝 p.1]
      (fun z' => Function.uncurry g' (z', p.2)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  have := hslice.deriv_eq
  simpa only [Work.Spaces.pz, Function.uncurry] using this

theorem Dz_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz g)) (Function.uncurry (Work.Spaces.Dz g')) V := by
  intro p hp
  have hpz := pz_congrOn hV h hp
  show p.1 * Work.Spaces.pz g p.1 p.2 = p.1 * Work.Spaces.pz g' p.1 p.2
  rw [hpz]

theorem Dth_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) V := by
  intro p hp
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => Function.uncurry g (p.1, θ')) =ᶠ[𝓝 p.2]
      (fun θ' => Function.uncurry g' (p.1, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have hd := hslice.deriv_eq
  exact congrArg (fun t => Real.sin (2 * p.2) * t) hd

theorem DthIter_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i g))
      (Function.uncurry (Work.Spaces.DthIter i g')) V := by
  induction i with
  | zero => exact h
  | succ i ih => simpa only [Work.Spaces.DthIter_succ] using Dth_congrOn hV ih

/-! ## `∂_θ` commutes with the iterates of `D_z` on an open set -/

/-- `∂_θ (D_z g) = D_z (∂_θ g)` at a point where `g` is `C²`. -/
theorem pth_Dz_apply_of {g : ℝ → ℝ → ℝ} {y : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) y) :
    Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2 = Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2 := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2
      = y.1 * Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2 := by
    show deriv (fun θ' => y.1 * Work.Spaces.pz g y.1 θ') y.2
      = y.1 * deriv (fun θ' => Work.Spaces.pz g y.1 θ') y.2
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2
      = Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 :=
    (Work.Spaces.pz_pth_comm (f := g) hg).symm
  have h4 : Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2
      = y.1 * Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 := rfl
  rw [h1, h3, h4]

theorem pth_DzIter_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f))) V := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
    intro y hy
    have hs : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j f)) V :=
      contDiffOn_uncurry_DzIter hV h j
    have hstep : Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f))) y :=
      pth_Dz_apply_of ((ContDiffOn.contDiffAt hs (hV.mem_nhds hy)).of_le (by norm_num))
    have hcongr : Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f))) y :=
      Dz_congrOn hV ih hy
    show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j+1) f)) y
        = Function.uncurry (Work.Spaces.DzIter (j+1) (Work.Spaces.pth f)) y
    rw [show Work.Spaces.DzIter (j+1) f = Work.Spaces.Dz (Work.Spaces.DzIter j f) from rfl,
        show Work.Spaces.DzIter (j+1) (Work.Spaces.pth f)
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f)) from rfl]
    exact hstep.trans hcongr

/-! ## `D_θ` commutes with the iterates of `D_z` (the other direction) -/

theorem Dz_Dth_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth f)))
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz f))) V := by
  intro y hy
  exact Work.Spaces.Dz_Dth_comm ((ContDiffOn.contDiffAt h (hV.mem_nhds hy)).of_le (by norm_num))

theorem Dth_DzIter_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth f))) V := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      have hc : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2 :=
        Dz_Dth_comm_eqOn hV (contDiffOn_uncurry_DzIter hV h b) hy
      have hpz := pz_congrOn hV ih hy
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [← hc]
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [hpz]

theorem DthIter_DzIter_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i f))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hDth : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_congrOn hV ih hy
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_DzIter_comm_eqOn hV (contDiffOn_uncurry_DthIter hV h i) b hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
      rw [hDth, hstep]

/-! ## The slice of an iterated `D_z`-derivative, at `z > 0` -/




/-! ## The commutation of `D_z^j` with `D_θ^i` across division by `sin 2θ`, for `z > 0` -/








/-! ## Continuity of the slices of the quotient on `(0, π/2)` -/



/-! ## The `H^k`-integrand at `z = 0` -/

@[simp] theorem w_zero : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]

/-- At `z = 0` the radial weight vanishes, and with it every summand of the `H^k`-integrand:
the integrand is identically zero. -/
@[simp] theorem HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, w_zero, zero_div, mul_zero, Work.Spaces.Wt, Work.Spaces.wTheta]
  simp

/-- The same for the weighted mixed summand. -/
@[simp] theorem Wt_zero_z (α : ℝ) (θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  simp [Work.Spaces.Wt]

/-! ## The pure-`D_z` termwise estimate at `z > 0` -/



/-! ## A.e. strong measurability of the `H^k`-integrand of the quotient -/


end Work.Blocks.Half
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.hardySigmaBoundaryCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

/-- `sin (2θ) > 0` for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])


end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.TraceStmt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- **The trace-class version of the open-quadrant single-function interpolation estimate.**  The
hypotheses are those of `Work.EllipticEst.Core.i0Aux.InterpOpen` together with the vanishing of
the angular *limits* of `G` and of `D_zG` at both endpoints (only the values `G z 0 = G z (π/2)`
are required by `InterpOpen`, which admits slices whose interior limits do not vanish). -/
def InterpOpenTraceStmt (C : ℝ) : Prop :=
  ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen G →
    (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    Work.EllipticEst.Core.i0Aux.SliceHonestOpen G →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z)
      Work.Spaces.Iz →
    α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.K5c.TraceOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.K5c

/-- **The trace-class version of the open-quadrant single-function interpolation estimate**:
the paper's §7 estimate `α² ∫_z mixIntS G ≤ C (α⁴ ∫_z ddIntS G + ∫_z ttIntS G + α² ∫_z dIntS G)`
for data `G` which are `C^∞` on the open quadrant, vanish at the two angular boundary lines,
whose slices of `G` **and of `D_zG`** have vanishing traces at both endpoints (for every
`z > 0`), and which satisfy `SliceHonestOpen` plus the four outer integrability hypotheses. -/
def InterpOpenTrace (C : ℝ) : Prop :=
  ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen G →
    (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    Work.EllipticEst.Core.i0Aux.SliceHonestOpen G →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z)
      Work.Spaces.Iz →
    α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))


end Work.FTS.EllSol.PkgK5.K5c
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.HkIntegrand_integral_le_pth2_pth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Auxiliary vocabulary for the proof

`Sfun` is the sum of the three fixed integrable angular weights produced by the boundary
conditions in `slicePhi`; `Bdom` is the dominating function by which a single angular
integrand (at a fixed radial level `z`, with a fixed value `M` of the `H^k`-integral of
`∂_θ² f`) is bounded. -/

/-- `Sfun α θ = sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ}`: the three fixed integrable
terms attached to `sliceA u` in `slicePhi`. -/
private def Sfun (α θ : ℝ) : ℝ :=
  Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
    + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)










end Work.FTS.EllipticEst.Blocks
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.slice_d_bound_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.ThetaU

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false



end Work.FTS.EllipticEst.ThetaU
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.l1_cauchy_pz_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

/-
Box-local version of `Work.FTS.StrongEps.LocUnif.D5.l1_cauchy_pz`: the smoothness hypothesis
`SmoothOpen (L n)` (which forces every point of the box to lie in the open quadrant
`(0,∞) × (0,π/2)`, hence demands `d < π/2`) is replaced by exactly the facts its proof uses:
the two one-variable derivative relations on the box and the continuity of `∂_z L n` and
`∂_z² L n` on the box.  The proof is a verbatim copy of `l1_cauchy_pz`'s proof (same file
`Submission/Work/FTS/StrongEps/LocUnif/D5/l1_cauchy_pz.lean`, with the helper `l1_box_le`
reproduced or imported), with `hsm`-derived facts replaced by the new hypotheses and all
`Q0`-membership bookkeeping deleted.
-/
theorem l1_cauchy_pz_gen {a b a₀ b₀ c d M : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a < b)
    (hbb₀ : b < b₀) (hcd : c < d) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hder : ∀ n : ℕ, ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a₀ b₀,
      HasDerivAt (fun z' => L n z' θ) (Work.Spaces.pz (L n) z θ) z)
    (hder2 : ∀ n : ℕ, ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a₀ b₀,
      HasDerivAt (fun z' => Work.Spaces.pz (L n) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (L n)) z θ) z)
    (hcont : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hcont2 : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (h1 : ∀ n : ℕ, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M)
    (h2 : ∀ n : ℕ, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε := by
  intro ε hε
  have ha_pos : 0 < a := lt_trans ha₀ ha₀a
  have hdc : 0 < d - c := by linarith
  -- constants
  set c₁ : ℝ := 2 * (b - a) * (d - c) with hc₁def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; positivity
  set M₄ : ℝ := 4 * M with hM₄def
  have hM₄nn : 0 ≤ M₄ := by rw [hM₄def]; linarith
  set K₂ : ℝ := M₄ + (b₀ - a) * (d - c) / 4 with hK₂def
  have hK₂nn : 0 ≤ K₂ := by
    rw [hK₂def]
    have h : 0 ≤ (b₀ - a) * (d - c) := by nlinarith [hM₄nn]
    linarith
  set hh : ℝ := min ((b₀ - b) / 2) (ε / (2 * (K₂ + 1))) with hhhdef
  have hhhpos : 0 < hh := by
    rw [hhhdef]
    exact lt_min (by linarith) (by positivity)
  have hhhle₁ : hh ≤ (b₀ - b) / 2 := by rw [hhhdef]; exact min_le_left _ _
  have hhhle₂ : hh ≤ ε / (2 * (K₂ + 1)) := by rw [hhhdef]; exact min_le_right _ _
  have hbhh : b + hh ≤ b₀ := by linarith
  have hK₂hh : hh * K₂ ≤ ε / 2 := by
    have h1 : K₂ ≤ K₂ + 1 := by linarith
    have h3 : hh * K₂ ≤ hh * (K₂ + 1) := mul_le_mul_of_nonneg_left h1 hhhpos.le
    have h4 : hh * (K₂ + 1) ≤ (ε / (2 * (K₂ + 1))) * (K₂ + 1) :=
      mul_le_mul_of_nonneg_right hhhle₂ (by linarith)
    have h5 : (ε / (2 * (K₂ + 1))) * (K₂ + 1) = ε / 2 := by
      field_simp
    linarith
  set δ : ℝ := ε * hh / (2 * c₁) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδeq : c₁ * δ / hh = ε / 2 := by
    have hc₁ne : c₁ ≠ 0 := ne_of_gt hc₁pos
    have hhne : hh ≠ 0 := ne_of_gt hhhpos
    rw [hδdef]
    field_simp
  -- the uniform-convergence threshold
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      dist (Llim p.1 p.2) (L n p.1 p.2) < δ / 2 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hconv) (δ / 2) (by linarith)
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => hN n hn⟩
  refine ⟨N, fun n m hn hm => ?_⟩
  -- the box inclusions
  have hsubbox : Set.Icc a (b + hh) ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
    Set.prod_mono (Set.Icc_subset_Icc ha₀a.le hbhh) Subset.rfl
  -- the pointwise bound on the difference
  have hPbound : ∀ z ∈ Set.Icc a (b + hh), ∀ θ ∈ Set.Icc c d,
      |L n z θ - L m z θ| ≤ δ := by
    intro z hz θ hθ
    have hz' : (z, θ) ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      ⟨⟨le_trans ha₀a.le hz.1, le_trans hz.2 hbhh⟩, hθ⟩
    have h1 := hN n hn (z, θ) hz'
    have h2 := hN m hm (z, θ) hz'
    have h3 : dist (L n z θ) (L m z θ) < δ := by
      calc dist (L n z θ) (L m z θ)
          ≤ dist (L n z θ) (Llim z θ) + dist (Llim z θ) (L m z θ) := dist_triangle _ _ _
        _ = dist (Llim z θ) (L n z θ) + dist (Llim z θ) (L m z θ) := by
            rw [dist_comm (L n z θ) (Llim z θ)]
        _ < δ / 2 + δ / 2 := add_lt_add h1 h2
        _ = δ := by ring
    rw [Real.dist_eq] at h3
    exact le_of_lt h3
  -- the derivative relations, from `hder` / `hder2`
  have hGderiv : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + hh),
      HasDerivAt (fun z' => L n z' θ - L m z' θ)
        (Work.Spaces.pz (L n) z θ - Work.Spaces.pz (L m) z θ) z := by
    intro θ hθ z hz
    have hz' : z ∈ Set.Icc a₀ b₀ :=
      ⟨le_trans ha₀a.le hz.1, le_trans hz.2 hbhh⟩
    exact (hder n θ hθ z hz').sub (hder m θ hθ z hz')
  have hG'deriv : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + hh),
      HasDerivAt (fun z' => Work.Spaces.pz (L n) z' θ - Work.Spaces.pz (L m) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (L n)) z θ
          - Work.Spaces.pz (Work.Spaces.pz (L m)) z θ) z := by
    intro θ hθ z hz
    have hz' : z ∈ Set.Icc a₀ b₀ :=
      ⟨le_trans ha₀a.le hz.1, le_trans hz.2 hbhh⟩
    exact (hder2 n θ hθ z hz').sub (hder2 m θ hθ z hz')
  -- joint continuity
  have hGcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    (hcont n).sub (hcont m)
  have hG'cont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
        - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    (hcont2 n).sub (hcont2 m)
  -- the `L²` bound on the difference
  have hIntN : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ((hcont2 n).pow 2)
  have hIntM : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ((hcont2 m).pow 2)
  have hreN : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2 ≤ M := by
    have h := h2 n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntN
      (Filter.Eventually.of_forall fun p => sq_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  have hreM : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 ≤ M := by
    have h := h2 m
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntM
      (Filter.Eventually.of_forall fun p => sq_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  have hcomb : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
        - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 ≤ M₄ := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => 2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
          + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
        (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
      (hIntN.const_mul 2).add (hIntM.const_mul 2)
    have hpt : ∀ᵐ p ∂(volume.restrict (Set.Icc a₀ b₀ ×ˢ Set.Icc c d)),
        (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
          - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2
        ≤ 2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
          + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 :=
      Filter.Eventually.of_forall fun p => by nlinarith [sq_nonneg (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2 + Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2)]
    have hstep : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
            - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2
        ≤ ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
            + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun p => sq_nonneg _) hmaj hpt
    have hsplit : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
            + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
        = 2 * (∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
            (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
          + 2 * (∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
            (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2) := by
      rw [MeasureTheory.integral_add (hIntN.const_mul 2) (hIntM.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hsplit] at hstep
    rw [hM₄def]
    linarith
  -- the engine
  have hmain := l1_box_le ha₀a.le (le_of_lt hab) hbhh hhhpos (le_of_lt hcd)
    hPbound hGderiv hG'deriv hGcont hG'cont hcomb
  have hreal : ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
      |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2| ≤ ε := by
    have hK₂' : M₄ + (b - a + hh) * (d - c) / 4 ≤ K₂ := by
      rw [hK₂def]
      have hle : b - a + hh ≤ b₀ - a := by linarith
      have hmul : (b - a + hh) * (d - c) ≤ (b₀ - a) * (d - c) :=
        mul_le_mul_of_nonneg_right hle hdc.le
      have hdiv : (b - a + hh) * (d - c) / 4 ≤ (b₀ - a) * (d - c) / 4 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      linarith
    have hstep : hh * (M₄ + (b - a + hh) * (d - c) / 4) ≤ hh * K₂ :=
      mul_le_mul_of_nonneg_left hK₂' hhhpos.le
    have hstep' : hh * (M₄ + (b - a + hh) * (d - c) / 4) ≤ ε / 2 := le_trans hstep hK₂hh
    have h1 : 2 * (b - a) * (d - c) * δ / hh = c₁ * δ / hh := by rw [hc₁def]
    rw [h1] at hmain
    linarith [hmain, hstep', hδeq]
  -- convert the real bound into the lower integral
  have hIntabs : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    have hsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      Set.prod_mono (Set.Icc_subset_Icc ha₀a.le (le_of_lt hbb₀)) Subset.rfl
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((hGcont.mono hsub).abs)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntabs
    (Filter.Eventually.of_forall fun p => abs_nonneg _)]
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mpr hreal

end Work.FTS.StrongEps.LocUnif.D5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.divz_mixed_leibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-! ## Leibniz for `D_z^j D_θ^i` on a product with a `z`-only factor

`D_θ = sin(2θ) ∂_θ` differentiates only in the angle, so a factor `Φ z` which depends on the
radius alone passes through every iterate `D_θ^i`:

`D_θ^i (Φ z · G z θ) = Φ z · D_θ^i G z θ`.

This is the unconditional `deriv_const_mul` recursion (`deriv_const_mul_field`), so no
smoothness is needed here.  Feeding it into the Leibniz rule for `D_z^j` on the product
`Φ z · (D_θ^i G z θ)` (`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, which needs the two
factors to be `C^∞` on the open quadrant) gives the identity
`D_z^j D_θ^i (Φ·G) = ∑_b C(j,b) D_z^b Φ · D_z^{j-b} D_θ^i G`. -/

/-- A `z`-only factor factors out of every iterate of the angular operator `D_θ`. -/
private theorem DthIter_zOnly_mul (Φ : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => Φ z * H z θ)
      = fun z θ => Φ z * Work.Spaces.DthIter i H z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const_mul_field]
    ring

theorem divz_mixed_leibniz (Φ : ℝ → ℝ) (G : ℝ → ℝ → ℝ) (j i : ℕ)
    (hΦ : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Φ z))
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => Φ z * G z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
            (Work.Spaces.DzIter b (fun z _ => Φ z) z θ
              * Work.Spaces.mixed (j - b) i G z θ) := by
  intro z θ hz hθ0 hθ1
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => Φ z * G z θ)) z θ = _
  rw [DthIter_zOnly_mul Φ G i]
  rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz j (fun z _ => Φ z)
    (Work.Spaces.DthIter i G) hΦ (hG.DthIter i) z θ hz hθ0 hθ1]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [Work.Spaces.mixed]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS_EllLimOK.AssemblyAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The right-hand side of the tower formula for `bslOp` -/

/-- The expression for `bslOp α Ψ` in terms of the tower entries `F c d = D_z^c D_θ^d Ψ`
(`c + d ≤ 2`): the content of `BslOp_tower`. -/
def lhsfun (α : ℝ) (F : ℕ → ℕ → ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  -(α ^ 2) * (F 2 0 z θ - F 1 0 z θ) - (α * (5 + α)) * F 1 0 z θ
    - (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2
    + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ))
    + (Real.tan θ ^ 2 - 5) * F 0 0 z θ

/-! ## The six analytic inputs -/

/-- The six analytic inputs of the assembly, in the shape in which the sibling modules prove them.
(Fields: uniform bounds/equicontinuity of the order-`≤ 2` jet family from `LocalBound`; the tower
relations of the limits; the tower relations of a single smooth function; the identification of the
limits with the mixed derivatives of the bottom entry; `C²` of the bottom entry; the `bslOp`-formula
in terms of the tower.) -/
structure LimInputs : Prop where
  /-- Uniform boundedness and uniform equicontinuity of the six order-`≤ 2` jets on compacta. -/
  extract : ∀ {C : ℝ} {G : ℕ → ℝ → ℝ → ℝ},
    (∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) →
    (∀ (n : ℕ) (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (G n) z θ| ≤ C * wt z θ) →
    (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C' : ℝ,
        ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ‖fam6 G n p‖ ≤ C') ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ∀ q : ℝ × ℝ, q ∈ K →
          dist p q < δ → ‖fam6 G n p - fam6 G n q‖ < ε)
  /-- The tower relations of the limits along a locally uniformly convergent jet family. -/
  tower : ∀ {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ},
    (∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) →
    (∀ (c d : ℕ), c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ)
  /-- The tower relations of a single smooth function. -/
  smoothTower : ∀ {G : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen G →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => Work.Spaces.mixed c d G z' θ)
          (Work.Spaces.mixed (c + 1) d G z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d G z θ')
          (Work.Spaces.mixed c (d + 1) G z θ / Real.sin (2 * θ)) θ)
  /-- The identification of the tower entries with the mixed derivatives of the bottom entry. -/
  identify : ∀ {F : ℕ → ℕ → ℝ → ℝ → ℝ},
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) →
    ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F c d z θ = Work.Spaces.mixed c d (F 0 0) z θ
  /-- `C²` of the bottom entry of the tower. -/
  c2 : ∀ {F : ℕ → ℕ → ℝ → ℝ → ℝ},
    (∀ (c d : ℕ), c + d ≤ 2 → ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2)
      Work.FTS.EllipticEst.Q0) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) →
    ContDiffOn ℝ 2 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0
  /-- The formula for `bslOp` in terms of the tower. -/
  bsl : ∀ (α : ℝ) {Ψ : ℝ → ℝ → ℝ} {F : ℕ → ℕ → ℝ → ℝ → ℝ},
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) →
    ∀ {z θ : ℝ}, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Elliptic.bslOp α Ψ z θ = lhsfun α F z θ

/-! ## Locality of the iterated operators -/

lemma DthIter_congrOn_Q0 {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) V := by
  induction i with
  | zero => exact h
  | succ i ih =>
    intro p hp
    show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i f) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i g) p.1 p.2
    rw [Work.Spaces.pth_congr_of_isOpen hV ih hp]

lemma DzIter_congrOn_Q0 {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j g)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro p hp
    show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j f) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
    rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

lemma mixed_congrOn_Q0 {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i f))
      (Function.uncurry (Work.Spaces.mixed j i g)) V := by
  intro p hp
  have h1 : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) V := DthIter_congrOn_Q0 hV h i
  have h2 := DzIter_congrOn_Q0 hV h1 j hp
  simpa only [Work.Spaces.mixed] using h2

/-! ## Decay from the growth bound -/


/-! ## The limit of the tower formula -/


end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.integrableOn_deriv_cos_mul_sq_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `(∂_θ (cos θ · Ψ z θ))² sin(2θ)^{-η}` from the `Vop`-counterpart

The `θ`-reconstruction of `Work.FTS_EllLimOK.Reconstruct` records that `Vop Ψ = ∂_θΨ - tan θ · Ψ`
is `1/cos θ` times the derivative of `θ ↦ cos θ · Ψ z θ`:

`cos θ · Vop Ψ z θ = ∂_θ (cos θ · Ψ z θ)`.  (`cos_mul_Vop_eq`.)

Hence everywhere on the open angular interval

`(∂_θ (cos θ · Ψ z θ))² sin(2θ)^{-η} = cos²θ · (Vop Ψ z θ)² · sin(2θ)^{-η}
  ≤ (Vop Ψ z θ)² sin(2θ)^{-η}`,

because `cos²θ ≤ 1` and `sin(2θ)^{-η} ≥ 0` there.  So the integrability of the `Vop`-integrand
on the *closed* interval `Iθ = [0,π/2]` (the hypothesis supplied by the `ℋ⁰`-memberships, whose
weight is integrable at `θ = 0`) transfers to the integrability of the derivative-integrand on
the *open* interval `(0,π/2)`.

The identity `cos θ · Vop Ψ = ∂_θ (cos θ · Ψ)` needs the `θ`-derivatives of the slice at the
interior points only, which is exactly what `SmoothOpen.curry_θ` supplies (the *analyticity* of
`SmoothOpen` is of course irrelevant here, but only `C^∞`-on-the-open-quadrant is used).  The
a.e. strong measurability of the left-hand side is free: `deriv` of anything is Borel measurable
(`measurable_deriv`).
-/

namespace Work.FTS_EllLimOK.Pinning

open MeasureTheory Set Filter

theorem integrableOn_deriv_cos_mul_sq_rpow {η : ℝ} {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) (hz : 0 < z)
    (h : MeasureTheory.IntegrableOn
      (fun θ => (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) := by
  -- the `Vop`-integrand is integrable on the smaller, open interval as well
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) :=
    h.mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- the derivative of `θ ↦ cos θ · Ψ z θ` is `cos θ · Vop Ψ z θ` on the open interval
  have hderiv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun s => Real.cos s * Ψ z s) θ = Real.cos θ * Work.Construction.Vop Ψ z θ := by
    intro θ hθ
    have hslice : HasDerivAt (fun s : ℝ => Ψ z s) (Work.Spaces.pth Ψ z θ) θ :=
      (((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => Real.cos s * Ψ z s)
        (-Real.sin θ * Ψ z θ + Real.cos θ * Work.Spaces.pth Ψ z θ) θ :=
      (Real.hasDerivAt_cos θ).mul hslice
    refine (h3.congr_deriv ?_).deriv
    rw [Work.FTS_EllLimOK.cos_mul_Vop_eq Ψ hθ]
    ring
  refine MeasureTheory.Integrable.mono'
    (μ := volume.restrict (Set.Ioo 0 (Real.pi / 2)))
    (g := fun θ => (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
    hGint ?_ ?_
  · -- measurability: `deriv` is Borel measurable, and so are the two weight factors
    refine Measurable.aestronglyMeasurable ?_
    refine ((measurable_deriv _).pow_const 2).mul ?_
    exact Measurable.pow (Real.measurable_sin.comp
      ((measurable_const : Measurable fun _ : ℝ => (2:ℝ)).mul measurable_id))
      (measurable_const : Measurable fun _ : ℝ => (-η))
  · -- the pointwise domination, everywhere on the open interval
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hd := hderiv θ hθ
    have hsinpos : 0 < Real.sin (2 * θ) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    have hsinnn : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hsinpos.le _
    have hFnn : 0 ≤ (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) :=
      mul_nonneg (sq_nonneg _) hsinnn
    have hle : (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
      rw [hd, mul_pow]
      calc (Real.cos θ) ^ 2 * (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
          ≤ 1 * (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (Real.cos_sq_le_one θ) (sq_nonneg _)) hsinnn
        _ = (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    exact hle

end Work.FTS_EllLimOK.Pinning
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.integrableOn_div_cos_sq_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `(Ψ z θ / cos θ)²` on the angular interval, from `ℋ⁰`-membership

The `ℋ⁰`-weighted integrand of `g` is

`HkIntegrand α 0 g z θ = (g z θ · w(z) / sin(2θ)^{η/2})²`

(`Work.FTS_EllLimOK.HkIntegrand_zero_eq`), and on the *interior* of the quadrant the weight
`w(z)/sin(2θ)^{η/2}` is `≥ 1` (`Work.FTS_EllLimOK.one_le_weight`): for every `z > 0` the
weighted integrand therefore dominates `(g z θ)²` *pointwise* on `(0, π/2)`.  Since
`HkMem α 0 g` provides the integrability of the weighted integrand on the *closed* angular
interval `Iθ = [0, π/2]`, domination yields the integrability of `(g z ·)²` on the open
interval — the a.e. strong measurability of `(g z ·)²` coming from continuity of the slice.

Applied to `g z θ = Ψ z θ / cos θ` with `Ψ` smooth on the open quadrant (whose `θ`-slice at
`z > 0` is continuous on `(0, π/2)`, and `cos` does not vanish there) this is exactly the
statement consumed by the pinning argument at the corner `θ = π/2`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Pinning

set_option autoImplicit false



end Work.FTS_EllLimOK.Pinning
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.vopRated =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `vopRated` — the rated `Vop`-bound on the slice `(0, π/2)`

For a function `f : ℝ → ℝ` whose logarithmic derivative along `θ` is bounded,
`|f' θ - tan θ · f θ| ≤ K` on `(0, π/2)`, and which vanishes at `θ = 0⁺` and whose
product with `cos` vanishes at `θ → (π/2)⁻`, the function itself is dominated by
`K · tan θ` and by `K · (1 - sin θ)/cos θ`:

* `|f θ| ≤ K · tan θ` (the "rated" bound: the singularity at `0` is at worst that of the
  homogeneous solution `1/cos θ`, tested against the vanishing at `0⁺`);
* `|f θ| ≤ K · (1 - sin θ)/cos θ` (the boundary condition at `π/2`: there
  `1 - sin θ = cos²θ/(1 + sin θ)`, so the bound is `K · cos θ/(1 + sin θ)`).

The mechanism is the multiplicative integrating factor `g θ = cos θ · f θ`, for which
`g' θ = cos θ · (f' θ - tan θ · f θ)`, hence `|g'| ≤ K cos θ`.  The two conclusions are the
four comparisons

* `g ≤ K sin θ` and `-g ≤ K sin θ`, both from the limit `0` at `0⁺` (left-endpoint
  comparison, `le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT`),
* `g ≤ K (1 - sin θ)` and `-g ≤ K (1 - sin θ)`, both from the limit `0` at `(π/2)⁻`
  (right-endpoint comparison, `le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT`),

combined with `|g θ| = cos θ · |f θ|` (`cos θ > 0` on `(0, π/2)`).
-/

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open scoped Real Topology
open Filter Set

theorem vopRated {f f' : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (f' θ) θ)
    (hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f' θ - Real.tan θ * f θ| ≤ K)
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * f θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ K * (Real.sin θ / Real.cos θ)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |f θ| ≤ K * ((1 - Real.sin θ) / Real.cos θ)) := by
  have hπ2 : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcospos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
  -- ## the derivative of the integrating factor `g θ = cos θ · f θ`
  have hgd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ : ℝ => Real.cos θ * f θ) (Real.cos θ * (f' θ - Real.tan θ * f θ)) θ := by
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := ne_of_gt (hcospos θ hθ)
    refine ((Real.hasDerivAt_cos θ).mul (hder θ hθ)).congr_deriv ?_
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hgbd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.cos θ * (f' θ - Real.tan θ * f θ)| ≤ K * Real.cos θ := by
    intro θ hθ
    calc |Real.cos θ * (f' θ - Real.tan θ * f θ)|
        = Real.cos θ * |f' θ - Real.tan θ * f θ| := by
          rw [abs_mul, abs_of_pos (hcospos θ hθ)]
      _ ≤ Real.cos θ * K := mul_le_mul_of_nonneg_left (hbound θ hθ) (le_of_lt (hcospos θ hθ))
      _ = K * Real.cos θ := by ring
  -- ## the two endpoint limits, as limits of the integrating factor
  have hlim0 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * f θ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Filter.Tendsto (fun θ : ℝ => Real.cos θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa [Real.cos_zero] using
        (Real.continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using hc.mul h0
  have hlim0Ks : Filter.Tendsto (fun θ : ℝ => K * Real.sin θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.sin_zero] using
      ((Real.continuous_sin.tendsto 0).mono_left nhdsWithin_le_nhds).const_mul K
  have hlimKc : Filter.Tendsto (fun θ : ℝ => K * (1 - Real.sin θ)) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have hs : Filter.Tendsto (fun θ : ℝ => Real.sin θ) (𝓝[<] (Real.pi / 2)) (𝓝 1) := by
      simpa [Real.sin_pi_div_two] using
        (Real.continuous_sin.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
    have h1' : Filter.Tendsto (fun θ : ℝ => 1 - Real.sin θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
      have hconst : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] (Real.pi / 2)) (𝓝 1) :=
        tendsto_const_nhds
      simpa using hconst.sub hs
    simpa using h1'.const_mul K
  -- ## the four comparison functions
  have hA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Real.cos θ * f θ - K * Real.sin θ ≤ 0 := by
    refine le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT (a := 0) (b := Real.pi / 2) (c := 0) hπ2
      (h := fun θ : ℝ => Real.cos θ * f θ - K * Real.sin θ)
      (h' := fun θ : ℝ => Real.cos θ * (f' θ - Real.tan θ * f θ) - K * Real.cos θ)
      ?_ ?_ ?_ (le_refl 0)
    · intro x hx
      exact (hgd x hx).sub ((Real.hasDerivAt_sin x).const_mul K)
    · intro x hx
      have h1 := hgbd x hx
      have h2 := le_abs_self (Real.cos x * (f' x - Real.tan x * f x))
      linarith
    · simpa using hlim0.sub hlim0Ks
  have hB : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      -(Real.cos θ * f θ) - K * Real.sin θ ≤ 0 := by
    refine le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT (a := 0) (b := Real.pi / 2) (c := 0) hπ2
      (h := fun θ : ℝ => -(Real.cos θ * f θ) - K * Real.sin θ)
      (h' := fun θ : ℝ => -(Real.cos θ * (f' θ - Real.tan θ * f θ)) - K * Real.cos θ)
      ?_ ?_ ?_ (le_refl 0)
    · intro x hx
      exact (hgd x hx).neg.sub ((Real.hasDerivAt_sin x).const_mul K)
    · intro x hx
      have h1 := hgbd x hx
      have h2 := neg_le_abs (Real.cos x * (f' x - Real.tan x * f x))
      linarith
    · simpa using hlim0.neg.sub hlim0Ks
  have hC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Real.cos θ * f θ - K * (1 - Real.sin θ) ≤ 0 := by
    refine le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT (a := 0) (b := Real.pi / 2) (c := 0) hπ2
      (h := fun θ : ℝ => Real.cos θ * f θ - K * (1 - Real.sin θ))
      (h' := fun θ : ℝ => Real.cos θ * (f' θ - Real.tan θ * f θ) + K * Real.cos θ)
      ?_ ?_ ?_ (le_refl 0)
    · intro x hx
      have h := (hgd x hx).sub (((Real.hasDerivAt_sin x).const_sub 1).const_mul K)
      refine h.congr_deriv ?_
      ring
    · intro x hx
      have h1 := (abs_le.mp (hgbd x hx)).1
      linarith
    · simpa using h1.sub hlimKc
  have hD : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      -(Real.cos θ * f θ) - K * (1 - Real.sin θ) ≤ 0 := by
    refine le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT (a := 0) (b := Real.pi / 2) (c := 0) hπ2
      (h := fun θ : ℝ => -(Real.cos θ * f θ) - K * (1 - Real.sin θ))
      (h' := fun θ : ℝ => -(Real.cos θ * (f' θ - Real.tan θ * f θ)) + K * Real.cos θ)
      ?_ ?_ ?_ (le_refl 0)
    · intro x hx
      have h := (hgd x hx).neg.sub (((Real.hasDerivAt_sin x).const_sub 1).const_mul K)
      refine h.congr_deriv ?_
      ring
    · intro x hx
      have h1 := (abs_le.mp (hgbd x hx)).2
      linarith
    · simpa using h1.neg.sub hlimKc
  -- ## assembly
  constructor
  · intro θ hθ
    have hc := hcospos θ hθ
    have hgabs : Real.cos θ * |f θ| ≤ K * Real.sin θ := by
      have habs : |Real.cos θ * f θ| ≤ K * Real.sin θ :=
        abs_le.mpr ⟨by linarith [hB θ hθ], by linarith [hA θ hθ]⟩
      rwa [abs_mul, abs_of_pos hc] at habs
    have hkey : |f θ| ≤ K * Real.sin θ / Real.cos θ := by
      rw [le_div_iff₀ hc]
      calc |f θ| * Real.cos θ = Real.cos θ * |f θ| := by ring
        _ ≤ K * Real.sin θ := hgabs
    calc |f θ| ≤ K * Real.sin θ / Real.cos θ := hkey
      _ = K * (Real.sin θ / Real.cos θ) := by ring
  · intro θ hθ
    have hc := hcospos θ hθ
    have hgabs : Real.cos θ * |f θ| ≤ K * (1 - Real.sin θ) := by
      have habs : |Real.cos θ * f θ| ≤ K * (1 - Real.sin θ) :=
        abs_le.mpr ⟨by linarith [hD θ hθ], by linarith [hC θ hθ]⟩
      rwa [abs_mul, abs_of_pos hc] at habs
    have hkey : |f θ| ≤ K * (1 - Real.sin θ) / Real.cos θ := by
      rw [le_div_iff₀ hc]
      calc |f θ| * Real.cos θ = Real.cos θ * |f θ| := by ring
        _ ≤ K * (1 - Real.sin θ) := hgabs
    calc |f θ| ≤ K * (1 - Real.sin θ) / Real.cos θ := hkey
      _ = K * ((1 - Real.sin θ) / Real.cos θ) := by ring

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ThetaJets.integral_Ktheta_dzIter_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ThetaJets

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. The angular factor is nonnegative on `Iθ` -/


/-! ## 2. The factorisation of the angular integrand -/


/-! ## 3. Angular Cauchy–Schwarz -/


/-! ## 4. The pointwise (in `s`) bound on the angular integral -/


/-! ## 5. The target -/


end Work.FTS_EllLimOK.ThetaJets
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

open Set MeasureTheory

/-! ## Non-vanishing of the denominators on the open quadrant -/

private lemma z_ne_zero_of_mem_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    p.1 ≠ 0 :=
  ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

private lemma th_mul_ne_zero_of_mem_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    p.2 * (Real.pi / 2 - p.2) ≠ 0 := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (mul_pos h0 (by linarith [Real.pi_pos]))

private lemma sin_two_ne_zero_of_mem_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Real.sin (2 * p.2) ≠ 0 := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-! ## Continuity on the open quadrant -/

/-- The growth weight `wt` is continuous on the open quadrant. -/
lemma continuousOn_wt :
    ContinuousOn (fun p : ℝ × ℝ => wt p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hnum : ContinuousOn (fun p : ℝ × ℝ => 1 + 1 / p.1 + 1 / (p.2 * (Real.pi / 2 - p.2)))
      Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.add (continuousOn_const.div continuousOn_fst
        (fun p hp => z_ne_zero_of_mem_Q0 hp))).add
      (continuousOn_const.div
        (continuousOn_snd.mul (continuousOn_const.sub continuousOn_snd))
        (fun p hp => th_mul_ne_zero_of_mem_Q0 hp))
  have hden : ContinuousOn (fun p : ℝ × ℝ => 1 + p.1) Work.FTS.EllipticEst.Q0 :=
    continuousOn_const.add continuousOn_fst
  have h := hnum.div hden (fun p hp => by
    have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1; linarith)
  exact h

/-- The augmented growth weight `wt · (1/z + 1/sin 2θ)` is continuous on the open quadrant. -/
lemma continuousOn_wt_mul :
    ContinuousOn (fun p : ℝ × ℝ => wt p.1 p.2 * (1 / p.1 + 1 / Real.sin (2 * p.2)))
      Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  refine continuousOn_wt.mul ?_
  exact (continuousOn_const.div continuousOn_fst
      (fun p hp => z_ne_zero_of_mem_Q0 hp)).add
    (continuousOn_const.div hsin (fun p hp => sin_two_ne_zero_of_mem_Q0 hp))

/-! ## The main statement -/

theorem wt_bddAbove_of_compact {K : Set (ℝ × ℝ)} (hKc : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ M N : ℝ, (∀ p ∈ K, Work.FTS_EllLimOK.wt p.1 p.2 ≤ M) ∧
      (∀ p ∈ K, Work.FTS_EllLimOK.wt p.1 p.2 * (1 / p.1 + 1 / Real.sin (2 * p.2)) ≤ N) := by
  have hM : ∃ M : ℝ, ∀ p ∈ K, wt p.1 p.2 ≤ M := by
    rcases (hKc.image_of_continuousOn (continuousOn_wt.mono hKQ)).bddAbove with ⟨M, hM⟩
    exact ⟨M, fun p hp => hM ⟨p, hp, rfl⟩⟩
  have hN : ∃ N : ℝ, ∀ p ∈ K,
      wt p.1 p.2 * (1 / p.1 + 1 / Real.sin (2 * p.2)) ≤ N := by
    rcases (hKc.image_of_continuousOn (continuousOn_wt_mul.mono hKQ)).bddAbove with ⟨N, hN⟩
    exact ⟨N, fun p hp => hN ⟨p, hp, rfl⟩⟩
  exact ⟨hM.choose, hN.choose, hM.choose_spec, hN.choose_spec⟩

end Work.FTS_EllLimOK
end
