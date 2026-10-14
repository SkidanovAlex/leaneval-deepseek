import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.cone_max_int
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.Sys.pw_identity_mine
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.st1_of_weighted
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.transport_weighted_proved
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Joint.ProfBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false

/-! ## §2  The slab identity `Prof α g = F_* + g` -/

/-- On the open quadrant and for `τ ≥ 0`, the full profile `Prof α g = profFull α (extG (GR α g))`
agrees with `F_* + g`: the sanitiser `gS` and the right-Taylor extension `tauExt` are inert there
and the `z ≤ 0` branch of `extG` is inactive. -/
theorem Prof_eq {α : ℝ} {g : Fam} {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ Real.pi / 2) (hτ : 0 ≤ τ) :
    Prof α g z θ τ = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + g z θ τ := by
  simp only [Prof, Work.FTS.Regularity.profFull_apply, GR,
    Work.FTS.FinalV2.extG_gS_of_mem α (Work.FTS.FinalV2.tauExt g) hθ0 hθ1,
    Work.FTS.RegPkgGal.extG_of_pos hz hτ,
    Work.FTS.FinalV2.tauExt_of_nonneg g hτ]


/-! ## §3  Joint continuity of the order-`≤ 3` jets (from `RXT.jc3`) -/

theorem mixedJets_contOn {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) {j i : ℕ}
    (hji : j + i ≤ 3) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (slice g p.2.2) p.1 p.2.1)
      (R7Slab S) :=
  Work.FTS_RegExport.RXT.jc3 hα hα13 hOK S hS j i hji

/-! ## §4  Smoothness of the explicit profile `F_*` -/

/-- `F_* = α (Γ/c) 2z/(1+z)²` is `C^∞` on the open quadrant. -/
theorem Fstar_contDiffAt {α : ℝ} {n : WithTop ℕ∞} {q : ℝ × ℝ}
    (h1 : 0 < q.1) (h2 : 0 < q.2) (h3 : q.2 < Real.pi / 2) :
    ContDiffAt ℝ n (fun q' : ℝ × ℝ =>
      Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q'.1 q'.2) q := by
  have hsin : 0 < Real.sin q.2 :=
    Real.sin_pos_of_pos_of_lt_pi h2 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos q.2 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h3⟩
  have hbase : Real.sin q.2 * Real.cos q.2 ^ 2 ≠ 0 := by positivity
  have h1' : ContDiffAt ℝ n (fun q' : ℝ × ℝ => Real.sin q'.2 * Real.cos q'.2 ^ 2) q :=
    ((Real.contDiff_sin.contDiffAt).comp q contDiffAt_snd).mul
      (((Real.contDiff_cos.contDiffAt).comp q contDiffAt_snd).pow 2)
  have h2' : ContDiffAt ℝ n
      (fun q' : ℝ × ℝ => (Real.sin q'.2 * Real.cos q'.2 ^ 2) ^
        ((Work.FTS.Regularity.pExp α) / 3)) q :=
    h1'.rpow_const_of_ne hbase
  have h4 : ContDiffAt ℝ n (fun q' : ℝ × ℝ =>
      (Real.sin q'.2 * Real.cos q'.2 ^ 2) ^ ((Work.FTS.Regularity.pExp α) / 3)
        * (Work.Spaces.c (Work.FTS.Regularity.pExp α))⁻¹) q := h2'.mul contDiffAt_const
  have h5 : ContDiffAt ℝ n (fun q' : ℝ × ℝ => 2 * q'.1 / (1 + q'.1) ^ 2) q :=
    (((contDiffAt_const (x := q) (c := (2 : ℝ))).mul contDiffAt_fst).div
      (((contDiffAt_const (x := q) (c := (1 : ℝ))).add contDiffAt_fst).pow 2) (by positivity))
  have h6 := (contDiffAt_const (x := q) (c := Work.FTS.Regularity.pExp α)).mul (h4.mul h5)
  have hfun : (fun q' : ℝ × ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q'.1 q'.2)
      = fun q' : ℝ × ℝ => Work.FTS.Regularity.pExp α *
          (((Real.sin q'.2 * Real.cos q'.2 ^ 2) ^ ((Work.FTS.Regularity.pExp α) / 3)
            * (Work.Spaces.c (Work.FTS.Regularity.pExp α))⁻¹) * (2 * q'.1 / (1 + q'.1) ^ 2)) := by
    funext q'
    rw [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.Gam, div_eq_mul_inv]
    ring
  rw [hfun]
  exact h6

/-- `F_*` is differentiable on the open quadrant. -/
theorem Fstar_differentiableAt {α : ℝ} {q : ℝ × ℝ}
    (h1 : 0 < q.1) (h2 : 0 < q.2) (h3 : q.2 < Real.pi / 2) :
    DifferentiableAt ℝ (fun q' : ℝ × ℝ =>
      Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q'.1 q'.2) q :=
  (Fstar_contDiffAt (n := 1) h1 h2 h3).differentiableAt one_ne_zero

/-! ## §5  The candidate derivative field of the profile -/

/-- The `z`-coordinate of the candidate derivative of `Prof` on the slab. -/
def FPz (α : ℝ) (g : Fam) (p : ℝ × ℝ × ℝ) : ℝ :=
  Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) p.1 p.2.1
    + Work.Spaces.mixed 1 0 (slice g p.2.2) p.1 p.2.1 / p.1

/-- The `θ`-coordinate of the candidate derivative of `Prof` on the slab. -/
def FPt (α : ℝ) (g : Fam) (p : ℝ × ℝ × ℝ) : ℝ :=
  Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) p.1 p.2.1
    + Work.Spaces.mixed 0 1 (slice g p.2.2) p.1 p.2.1 / Real.sin (2 * p.2.1)

/-- The `τ`-coordinate of the candidate derivative of `Prof` on the slab (from the transport
form of the profile equation). -/
def FR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (p : ℝ × ℝ × ℝ) : ℝ :=
  -K7 α Φs E g p.1 p.2.1 p.2.2

/-- The candidate derivative of the R7 profile at a point of the slab. -/
def ProfD (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (p : ℝ × ℝ × ℝ) :
    (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  tripleCLM (FPz α g p) (FPt α g p) (FR α Φs E g p)


/-- `mixed 1 0 f = z ∂_z f`. -/
theorem mixed_one_zero (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 0 f z θ = z * Work.Spaces.pz f z θ := rfl

/-- `mixed 0 1 f = sin(2θ) ∂_θ f`. -/
theorem mixed_zero_one (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ := rfl



/-- The non-vanishing of `sin 2θ` on the slab. -/
theorem sin_two_ne_zero {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-! ## §6  Joint continuity of the candidate field on the slab -/

/-- The `z`-coordinate `FPz` is continuous on the slab. -/
theorem FPz_contOn {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hFz : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (R7Slab S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => FPz α g p) (R7Slab S) := by
  refine hFz.add ?_
  refine (mixedJets_contOn hS hα hα13 hOK (j := 1) (i := 0) (by norm_num)).div
    continuous_fst.continuousOn (fun p hp => ne_of_gt hp.1)

/-- The `θ`-coordinate `FPt` is continuous on the slab. -/
theorem FPt_contOn {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hFt : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (R7Slab S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => FPt α g p) (R7Slab S) := by
  refine hFt.add ?_
  refine (mixedJets_contOn hS hα hα13 hOK (j := 0) (i := 1) (by norm_num)).div
    ((Real.continuous_sin.comp (continuous_const.mul (continuous_fst.comp continuous_snd))).continuousOn)
    (fun p hp => sin_two_ne_zero hp.2.1.1 hp.2.1.2)

/-- The candidate field is continuous on the slab. -/
theorem ProfD_contOn {α : ℝ} {Φs' : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hPz : ContinuousOn (fun p : ℝ × ℝ × ℝ => FPz α g p) (R7Slab S))
    (hPt : ContinuousOn (fun p : ℝ × ℝ × ℝ => FPt α g p) (R7Slab S))
    (hK : ContinuousOn (fun p : ℝ × ℝ × ℝ => K7 α Φs' E g p.1 p.2.1 p.2.2) (R7Slab S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => ProfD α Φs' E g p) (R7Slab S) := by
  have hfun : (fun p : ℝ × ℝ × ℝ => ProfD α Φs' E g p)
      = fun p => FPz α g p • p1 + FPt α g p • p2 + (-K7 α Φs' E g p.1 p.2.1 p.2.2) • p3 := by
    funext p; rfl
  rw [hfun]
  exact ((hPz.smul continuousOn_const).add (hPt.smul continuousOn_const)).add
    (hK.neg.smul continuousOn_const)

end Work.FTS_RegExport.RXR7
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Support.K7cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR7.Support.K7cont`

Joint continuity of the R7 right-hand side

`K7 α Φs E g z θ τ = Vz7ᵣ·D_z(Prof) + Vθ7ᵣ·∂_θ(Prof) + cs7ᵣ·Prof`

on the slab `R7Slab S = (0,∞) × (0,π/2) × [0,S]` — the input (A) of `RXR7.r7Joint`.

The two ingredients are:
* `VelPkg.cont` gives continuity of the three coefficients `(Vz7ᵣ, Vθ7ᵣ, cs7ᵣ)` on the closed
  angular box `(0,∞) × [0,π/2] × [0,S]`, hence on the slab (a subset);
* on the slab the R7 profile is `F_*(z,θ) + g(z,θ,τ)` (`extG_gS_of_mem` + `extG_of_pos` +
  `tauExt_of_nonneg`), and then `D_z(Prof) = D_z(F_*) + D_z(g)`, `∂_θ(Prof) = ∂_θ(F_*) +
  ∂_θ(g)`.  The `F_*`-parts are `τ`-independent and smooth on the open quadrant
  (`contDiffOn_Fstar_Q0`; `contDiffOn_zero_uncurry_pz` turns that into continuity of the
  partials), while the `g`-parts are `mixed 1 0 (slice g τ)` and `mixed 0 1 (slice g τ)`
  (the `θ`-one divided by `sin 2θ ≠ 0`), which are continuous on the slab by `RXT.jc3`
  (orders 0, 1).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR7.Support

/-- The projection `(z,θ,τ) ↦ (z,θ)` is continuous. -/
private theorem continuous_proj : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) :=
  continuous_fst.prodMk (continuous_fst.comp continuous_snd)

/-- Continuity of the curried `z`-partial of a `C¹` function on the open quadrant, as a
function on the R7 slab (which projects onto `Q0`). -/
theorem continuousOn_pz_of_contDiffOn_one {f : ℝ → ℝ → ℝ} {S : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.pz f p.1 p.2.1)
      (Work.FTS_RegExport.RXR7.R7Slab S) := by
  have hq : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pz f q.1 q.2)
      Work.FTS.EllipticEst.Q0 := by
    have h0 := Work.FTS_RegExport.RXT.contDiffOn_zero_uncurry_pz
      Work.FTS.EllipticEst.isOpen_Q0 hf
    rw [contDiffOn_zero] at h0
    exact h0
  have hmap : Set.MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1))
      (Work.FTS_RegExport.RXR7.R7Slab S) Work.FTS.EllipticEst.Q0 :=
    fun p hp => ⟨hp.1, hp.2.1⟩
  have h := hq.comp continuous_proj.continuousOn hmap
  simpa [Function.comp_def] using h

/-- Continuity of the curried `θ`-partial of a `C¹` function on the open quadrant, as a
function on the R7 slab. -/
theorem continuousOn_pth_of_contDiffOn_one {f : ℝ → ℝ → ℝ} {S : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.pth f p.1 p.2.1)
      (Work.FTS_RegExport.RXR7.R7Slab S) := by
  have hq : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pth f q.1 q.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfd : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry f) q)
        Work.FTS.EllipticEst.Q0 :=
      hf.continuousOn_fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 le_rfl
    have hcomp : ContinuousOn
        (fun q : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) q) (0, 1))
        Work.FTS.EllipticEst.Q0 :=
      hfd.clm_apply continuousOn_const
    refine hcomp.congr fun q hq => ?_
    exact Work.Spaces.pth_eq_fderiv
      ((hf.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq))
  have hmap : Set.MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1))
      (Work.FTS_RegExport.RXR7.R7Slab S) Work.FTS.EllipticEst.Q0 :=
    fun p hp => ⟨hp.1, hp.2.1⟩
  have h := hq.comp continuous_proj.continuousOn hmap
  simpa [Function.comp_def] using h

/-- On the R7 slab the profile is the explicit `F_*` plus the modulation `g`. -/
theorem profR_eq_slab {α : ℝ} {g : Work.FTS.Galerkin.Fam} {S z θ τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.FTS_RegExport.RXR7.Prof α g z θ τ
      = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + g z θ τ := by
  rw [Work.FTS_RegExport.RXR7.Prof, Work.FTS.Regularity.profFull_apply]
  rw [Work.FTS.FinalV2.extG_gS_of_mem α (Work.FTS.FinalV2.tauExt g) hθ0.le hθπ.le]
  rw [Work.FTS.RegPkgGal.extG_of_pos hz hτ.1]
  rw [Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]

/-- The `z`-partial of the R7 profile, decomposed on the slab. -/
theorem pz_profR_eq_slab {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {S z θ τ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.Spaces.pz (fun z θ => Work.FTS_RegExport.RXR7.Prof α g z θ τ) z θ
      = Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ
        + Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := by
  have hcdF : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_Fstar_Q0 (Work.FTS.Regularity.pExp_pos hα)
      (Work.FTS.Regularity.pExp_le_one hα13)
  have hdF : DifferentiableAt ℝ
      (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ) z :=
    Work.Spaces.differentiableAt_curry_left (G := fun z θ =>
      Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
      ((hcdF.differentiableOn two_ne_zero).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, hθ0, hθπ⟩))
  have hc4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ.1
  have hdG : DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
    have h0 : DifferentiableAt ℝ (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (z, θ) :=
      (hc4.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, hθ0, hθπ⟩)
    simpa using Work.Spaces.differentiableAt_curry_left (G := Work.FTS.Galerkin.slice g τ) h0
  have hcongr : deriv (fun z' => Work.FTS_RegExport.RXR7.Prof α g z' θ τ) z
      = deriv (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ
          + g z' θ τ) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact profR_eq_slab hτ hz' hθ0 hθπ
  have hsum : deriv (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ
        + g z' θ τ) z
      = deriv (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ) z
        + deriv (fun z' => g z' θ τ) z := by
    have h : (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ + g z' θ τ)
        = (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ)
          + (fun z' => g z' θ τ) := rfl
    rw [h]
    exact deriv_add hdF hdG
  rw [Work.Spaces.pz, hcongr, hsum]
  rfl

/-- The `θ`-partial of the R7 profile, decomposed on the slab. -/
theorem pth_profR_eq_slab {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {S z θ τ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.Spaces.pth (fun z θ => Work.FTS_RegExport.RXR7.Prof α g z θ τ) z θ
      = Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ
        + Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ := by
  have hcdF : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_Fstar_Q0 (Work.FTS.Regularity.pExp_pos hα)
      (Work.FTS.Regularity.pExp_le_one hα13)
  have hdF : DifferentiableAt ℝ
      (fun θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (G := fun z θ =>
      Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
      ((hcdF.differentiableOn two_ne_zero).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, hθ0, hθπ⟩))
  have hc4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ.1
  have hdG : DifferentiableAt ℝ (fun θ' => g z θ' τ) θ := by
    have h0 : DifferentiableAt ℝ (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (z, θ) :=
      (hc4.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, hθ0, hθπ⟩)
    simpa using Work.Spaces.differentiableAt_curry_right (G := Work.FTS.Galerkin.slice g τ) h0
  have hcongr : deriv (fun θ' => Work.FTS_RegExport.RXR7.Prof α g z θ' τ) θ
      = deriv (fun θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ'
          + g z θ' τ) θ := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθπ⟩] with θ' hθ'
    exact profR_eq_slab hτ hz hθ'.1 hθ'.2
  have hsum : deriv (fun θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ'
        + g z θ' τ) θ
      = deriv (fun θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ') θ
        + deriv (fun θ' => g z θ' τ) θ := by
    have h : (fun θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ' + g z θ' τ)
        = (fun θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ')
          + (fun θ' => g z θ' τ) := rfl
    rw [h]
    exact deriv_add hdF hdG
  rw [Work.Spaces.pth, hcongr, hsum]
  rfl

/-- On the slab the `θ`-partial of the modulation slice is `mixed 0 1` divided by `sin 2θ`. -/
theorem pth_slice_eq {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hsin : Real.sin (2 * θ) ≠ 0) :
    Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ
      = Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ / Real.sin (2 * θ) := by
  have hDth : Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ := rfl
  rw [hDth]
  exact (mul_div_cancel_left₀ (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z θ) hsin).symm

/-- The `D_z`-decomposition of the profile on the slab. -/
theorem Dz_profR_eq_slab {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {S z θ τ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hτ : τ ∈ Set.Icc (0 : ℝ) S) (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR7.Prof α g z θ τ) z θ
      = Work.Spaces.Dz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ
        + Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ := by
  have h := pz_profR_eq_slab (Φs := Φs) (E := E) hα hα13 hOK hτ hz hθ0 hθπ
  rw [Work.Spaces.Dz, Work.Spaces.Dz, h, Work.Spaces.mixed_zero_right,
    Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  ring

theorem K7cont {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR7.μR α Φs E g) (Work.FTS_RegExport.RXR7.GR α g)
      (Work.FTS_RegExport.RXR7.ΦR α Φs E g) S) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.FTS_RegExport.RXR7.K7 α Φs E g p.1 p.2.1 p.2.2)
      (Work.FTS_RegExport.RXR7.R7Slab S) := by
  -- the explicit profile `F_*` is `C¹` on the open quadrant
  have hF1 : ContDiffOn ℝ 1
      (Function.uncurry (fun z θ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.contDiffOn_Fstar_Q0 (Work.FTS.Regularity.pExp_pos hα)
      (Work.FTS.Regularity.pExp_le_one hα13)).of_le (by norm_num)
  -- the three transport coefficients, from `VelPkg.cont` (open angular box since the 10-11 repair)
  have hsub : Work.FTS_RegExport.RXR7.R7Slab S ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) S :=
    fun p hp => hp
  have hcont := hVP.cont.mono hsub
  have hVz : ContinuousOn
      (fun p : ℝ × ℝ × ℝ => Work.FTS_RegExport.RXR7.Vz7R α Φs E g p.1 p.2.1 p.2.2)
      (Work.FTS_RegExport.RXR7.R7Slab S) :=
    continuous_fst.comp_continuousOn hcont
  have hVth : ContinuousOn
      (fun p : ℝ × ℝ × ℝ => Work.FTS_RegExport.RXR7.Vθ7R α Φs E g p.1 p.2.1 p.2.2)
      (Work.FTS_RegExport.RXR7.R7Slab S) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn hcont
  have hcs : ContinuousOn
      (fun p : ℝ × ℝ × ℝ => Work.FTS_RegExport.RXR7.cs7R α Φs E g p.1 p.2.1 p.2.2)
      (Work.FTS_RegExport.RXR7.R7Slab S) :=
    (continuous_snd.comp continuous_snd).comp_continuousOn hcont
  -- the profile itself
  have hFc : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Construction.Fstar (Work.FTS.Regularity.pExp α) p.1 p.2.1)
      (Work.FTS_RegExport.RXR7.R7Slab S) := by
    have hmap : Set.MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1))
        (Work.FTS_RegExport.RXR7.R7Slab S) Work.FTS.EllipticEst.Q0 :=
      fun p hp => ⟨hp.1, hp.2.1⟩
    have h := hF1.continuousOn.comp continuous_proj.continuousOn hmap
    simpa [Function.comp_def, Function.uncurry] using h
  have hGc : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Work.FTS_RegExport.RXR7.R7Slab S) := by
    have h := Work.FTS_RegExport.RXT.jc3 hα hα13 hOK S hS 0 0 (by norm_num)
    convert h using 1
    ext p
    simp
  have hProf : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.FTS_RegExport.RXR7.Prof α g p.1 p.2.1 p.2.2)
      (Work.FTS_RegExport.RXR7.R7Slab S) :=
    (hFc.add hGc).congr fun p hp => profR_eq_slab hp.2.2 hp.1 hp.2.1.1 hp.2.1.2
  -- the `z`-derivative
  have hDzF : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.Dz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (Work.FTS_RegExport.RXR7.R7Slab S) :=
    (continuous_fst.continuousOn).mul (continuousOn_pz_of_contDiffOn_one hF1)
  have hDzG : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g p.2.2) p.1 p.2.1)
      (Work.FTS_RegExport.RXR7.R7Slab S) :=
    Work.FTS_RegExport.RXT.jc3 hα hα13 hOK S hS 1 0 (by norm_num)
  have hDz : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR7.Prof α g z θ p.2.2) p.1 p.2.1)
      (Work.FTS_RegExport.RXR7.R7Slab S) :=
    (hDzF.add hDzG).congr fun p hp =>
      Dz_profR_eq_slab hα hα13 hOK hp.2.2 hp.1 hp.2.1.1 hp.2.1.2
  -- the `θ`-derivative
  have hPthF : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (Work.FTS_RegExport.RXR7.R7Slab S) :=
    continuousOn_pth_of_contDiffOn_one hF1
  have hPthG : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pth (Work.FTS.Galerkin.slice g p.2.2) p.1 p.2.1)
      (Work.FTS_RegExport.RXR7.R7Slab S) := by
    have hnum : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g p.2.2) p.1 p.2.1)
        (Work.FTS_RegExport.RXR7.R7Slab S) :=
      Work.FTS_RegExport.RXT.jc3 hα hα13 hOK S hS 0 1 (by norm_num)
    have hden : ContinuousOn (fun p : ℝ × ℝ × ℝ => Real.sin (2 * p.2.1))
        (Work.FTS_RegExport.RXR7.R7Slab S) :=
      (Real.continuous_sin.comp
        (continuous_const.mul (continuous_fst.comp continuous_snd))).continuousOn
    refine (hnum.div hden ?_).congr fun p hp => ?_
    · intro p hp
      exact ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_of_mem hp.2.1.1 hp.2.1.2)
    · exact pth_slice_eq (ne_of_gt
        (Work.FTS_RegExport.RXT.sin_two_pos_of_mem hp.2.1.1 hp.2.1.2))
  have hPth : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pth (fun z θ => Work.FTS_RegExport.RXR7.Prof α g z θ p.2.2) p.1 p.2.1)
      (Work.FTS_RegExport.RXR7.R7Slab S) :=
    (hPthF.add hPthG).congr fun p hp =>
      pth_profR_eq_slab hα hα13 hOK hp.2.2 hp.1 hp.2.1.1 hp.2.1.2
  exact ((hVz.mul hDz).add (hVth.mul hPth)).add (hcs.mul hProf)

end Work.FTS_RegExport.RXR7.Support
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox`

The profile `F(τ) = Ftau (pExp α) (GR α g) τ = F_* + g(τ)` of the strong route is an admissible
*datum* for the radial `L₁₂`/`𝔽K` jet calculus: on every horizon `[0,S]` the four clauses of
`DatumHyp F C` (open-quadrant `C²`-regularity, the three pointwise jet bounds `DatumBnd`, the
`L¹`-integrability of the `L₁₂`-density, and its integral bound) hold with a single constant `C`
independent of `τ`.

Everything comes from the `LimApprox` clause of `DynOK'` (the approximating class-`C` families)
and the standing `C²`-regularity hypothesis `hc2` on the slices:

* `Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved` bounds every slot `D_z^bD_θ^a` (`a+b ≤ 2`)
  of `slice g τ` by `Cw · z^{3/2}/(1+z)²` — the decay that makes the `L₁₂`-density integrable at
  `z = 0`;
* `Work.FTS_RegExport.RXT.Sys.Ftau_jets_bounded_of_LimApprox` (same argument as the proved
  `Ftau_bounds`, with `DynOK'` weakened to `LimApprox`) gives `DatumBnd F C_db`;
* `Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le` bounds the density pointwise by the
  elementary majorant `3(π/2)(20/(1+s)² + Cw·s^{1/2}/(1+s)²)`, whose integral is controlled by
  `Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable`;
* `Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds` makes the density continuous on
  `(0,∞)`, which supplies the a.e. strong measurability needed for `Integrable.mono'`.

The final constant is `max 1 C_db + 120 + 18·Cw`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false

/-! ## §1 Elementary bounds on the profile `F_*` -/

/-- The coefficient `α·Γ(θ)/c(α)` of `F_*` is bounded by `10` on `θ ∈ Iθ`: `0 ≤ Γ ≤ 1` and
`c(α) ≥ 1/10`. -/
theorem abs_Fstar_coeff_le_ten {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |α| * |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  rw [abs_of_nonneg hα.le, abs_of_nonneg (div_nonneg hGam.1 hcpos.le)]
  rw [← mul_div_assoc, div_le_iff₀ hcpos]
  nlinarith [hα, hα1, hGam.1, hGam.2, hc.1]

/-- **Pointwise bound of the reference profile**: `|F_*(z,θ)| ≤ 10·|F_{*,rad}(z)|` on
`θ ∈ Iθ`. -/
theorem abs_Fstar_le_ten {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α z θ| ≤ 10 * |Work.FM.Fstar z| := by
  have hcoef := abs_Fstar_coeff_le_ten hα hα1 hθ
  rw [Work.Construction.Fstar, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- The radial factor `2z/(1+z)²` of the reference profile is bounded by `2` on `z ≥ 0`. -/
theorem abs_FM_Fstar_le_two {z : ℝ} (hz : 0 ≤ z) : |Work.FM.Fstar z| ≤ 2 := by
  rw [Work.FM.Fstar, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (1 + z), sq_nonneg z]

/-- The radial weight `z^{3/2}/(1+z)²` is bounded by `Z^{3/2}` for `z ∈ (0,Z]`. -/
theorem weight_le_rpow {z Z : ℝ} (hz : 0 < z) (h : z ≤ Z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ Z ^ ((3 : ℝ) / 2) := by
  have h1 : z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ z ^ ((3 : ℝ) / 2) := by
    rw [div_le_iff₀ (by positivity)]
    have hz2 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
    nlinarith [Real.rpow_nonneg hz.le ((3 : ℝ) / 2)]
  have h2 : z ^ ((3 : ℝ) / 2) ≤ Z ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hz.le h (by norm_num)
  linarith

/-- The `L₁₂`-density is the angular moment `Q_0` divided by `z`. -/
theorem L12dens_eq_thetaIntegral (f : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.Construction.L12dens f s
      = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * f s θ) / s := by
  rw [Work.Construction.L12dens, Work.FTS_RegExport.RXT.L12Iter.L12dens_eq_Qang_zero]
  simp only [Work.Elliptic.Qang, Work.Spaces.DzIter_zero]

/-! ## §2 The target -/

/-- **The profile `F(τ)` is a datum on `[0,S]`.** -/
theorem Ftau_datum_of_LimApprox {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (S : ℝ) (hS : 0 < S)
    (hc2 : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Work.FTS_RegExport.RXT.Sys.DatumHyp
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) C := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  -- §2.1 the standing bounds: weighted slots of the approximants, and the jet bounds of `F(τ)`
  have hT : 0 < max S 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved (αG := Work.FTS.Regularity.pExp α)
      (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hp0 hp1 hA (max S 1) hT
  obtain ⟨Cdb, -, hCdb⟩ := Ftau_jets_bounded_of_LimApprox hα hα13 hA S hS hc2
  obtain ⟨hmaj_int, hmaj_val⟩ := majorant_Ioi_integrable hCw0
  refine ⟨max 1 Cdb + 120 + 18 * Cw, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max 1 Cdb := le_max_left _ _
    have h2 : (0 : ℝ) ≤ 120 + 18 * Cw := by linarith
    linarith
  · intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) (max S 1) := ⟨hτ.1, le_trans hτ.2 (le_max_left _ _)⟩
    have hτnn : 0 ≤ τ := hτ.1
    -- §2.2 `GR` agrees with `g` on the closed quadrant
    have hGR : ∀ z θ : ℝ, 0 < z → 0 ≤ θ → θ ≤ Real.pi / 2 →
        Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ
          = Work.FTS.Galerkin.slice g τ z θ :=
      fun z θ hz h0 h1 => Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτnn hz h0 h1
    -- the weighted bound for the `GR`-slice
    have hub : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
          ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
      intro z θ hz h1 h2
      rw [hGR z θ hz h1.le h2.le]
      have h := hCw τ hτT 0 0 (by norm_num) z θ hz h1 h2
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
    -- §2.3 `C²`-regularity of the `GR`-slice, and of `F(τ)`, on the open quadrant
    have hGRc : ContDiffOn ℝ 2
        (Function.uncurry (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ))
        Work.FTS.EllipticEst.Q0 :=
      (hc2 τ hτ).congr (fun p hp => hGR p.1 p.2 hp.1 hp.2.1.le hp.2.2.le)
    have hFc : ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) Work.FTS.EllipticEst.Q0 := by
      have h1 : ContDiffOn ℝ 2
          (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
          Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hp0 hp1
      have h2 := h1.add hGRc
      refine h2.congr (fun p _ => ?_)
      simp only [Function.uncurry, Work.Construction.Ftau, Work.FTS.Galerkin.slice]
    -- §2.4 the pointwise bound of the `L₁₂`-density of `F(τ)`
    have hpt : ∀ s : ℝ, 0 < s →
        |Work.Construction.L12dens (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) s|
          ≤ 3 * (Real.pi / 2)
              * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
      intro s hs
      have h := abs_L12dens_Fstar_add_le (α := Work.FTS.Regularity.pExp α) hp0 hp1 hCw0
        (u := Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ) hub hs
      have hfun : Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ
          = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
              + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ := rfl
      rw [hfun]
      exact h
    -- §2.5 continuity of the angular moment, hence of the density, on `(0,∞)`
    have hQcont : ContinuousOn (fun s => ∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ * Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ s θ) (Set.Ioi 0) := by
      intro s₀ hs₀
      refine (continuousAt_Qang_of_bounds (f := Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) hs₀
        hFc.continuousOn (A := 20 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2)) ?_).continuousWithinAt
      intro z θ hz hθ0 hθ1
      have hz0 : 0 < z := lt_of_lt_of_le (by linarith [show (0 : ℝ) < s₀ from hs₀] :
        (0 : ℝ) < s₀ / 2) hz.1.le
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
      have h1 : |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
          ≤ 10 * |Work.FM.Fstar z| := abs_Fstar_le_ten hp0 hp1 hθI
      have h2 : |Work.FM.Fstar z| ≤ 2 := abs_FM_Fstar_le_two hz0.le
      have h3 : |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
          ≤ Cw * (2 * s₀) ^ ((3 : ℝ) / 2) :=
        le_trans (hub z θ hz0 hθ0 hθ1)
          (mul_le_mul_of_nonneg_left (weight_le_rpow hz0 hz.2.le) hCw0)
      rw [Work.Construction.Ftau]
      calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
            + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
          ≤ |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
            + |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ| :=
            abs_add_le _ _
        _ ≤ 10 * |Work.FM.Fstar z| + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := add_le_add h1 h3
        _ ≤ 10 * 2 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := by
            have h10 : 10 * |Work.FM.Fstar z| ≤ 10 * 2 :=
              mul_le_mul_of_nonneg_left h2 (by norm_num)
            linarith
        _ = 20 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := by ring
    have hdens_eq : ∀ s : ℝ, Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s
        = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ s θ) / s :=
      fun s => L12dens_eq_thetaIntegral _ s
    have hcont : ContinuousOn (Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) :=
      (hQcont.div continuousOn_id (fun s hs => ne_of_gt hs)).congr
        (fun s _ => hdens_eq s)
    -- §2.6 integrability of the density, and the integral bound
    have hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' hmaj_int
        (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [Real.norm_eq_abs]
      exact hpt s hs
    have hbnd : (∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s|)
          ≤ max 1 Cdb + 120 + 18 * Cw := by
      have h1 : (∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s|)
            ≤ ∫ s in Set.Ioi 0, 3 * (Real.pi / 2)
                * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun s => abs_nonneg _)) hmaj_int ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
        exact hpt s hs
      have h2 : (1 : ℝ) ≤ max 1 Cdb := le_max_left _ _
      have h3 : (0 : ℝ) ≤ 18 * Cw := by linarith
      linarith [hmaj_val, h1, h2, h3]
    -- §2.7 the datum
    have hCdb_le : Cdb ≤ max 1 Cdb + 120 + 18 * Cw := by
      have h0 : (0 : ℝ) ≤ 120 + 18 * Cw := by linarith
      have h1 : Cdb ≤ max 1 Cdb := le_max_right _ _
      linarith
    have hDbnd : Work.FTS_RegExport.RXT.Sys.DatumBnd (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)
        (max 1 Cdb + 120 + 18 * Cw) := by
      intro z θ hz h1 h2
      obtain ⟨a1, a2, a3⟩ := hCdb τ hτ z θ hz h1 h2
      exact ⟨le_trans a1 hCdb_le, le_trans a2 hCdb_le, le_trans a3 hCdb_le⟩
    exact ⟨hFc, hDbnd, hint, hbnd⟩

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FtauSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.FtauSlot` — uniform slot bounds for the profiles `F(τ) = F_* + slice (gn n) τ`

The mixed/radial slots `D_z^k (F_* + slice (gn n) τ)` of order `k ≤ 2` are bounded by a
constant which does not depend on `n`, `τ`, `z` or `θ`: the reference part by the radial jet
bound `FstarJet7` (`|D_z^j F_*| ≤ 10 M`), the perturbation part by the weighted bound
`Cw · z^{3/2}/(1+z)² ≤ Cw` of `Standing.app_slot_le`, and the sum by the additivity
`ftau_DzIter_one_add` / `ftau_DzIter_two_add` of `D_z^k` on the open quadrant.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- `SW z ≤ 1` for `z > 0`. -/
theorem SW_le_one {z : ℝ} (hz : 0 < z) : SW z ≤ 1 := by
  have hpos : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [SW, div_le_iff₀ hpos]
  by_cases h : 1 ≤ z
  · have h1 : z ^ ((3 : ℝ) / 2) ≤ z ^ 2 := by
      rw [← Real.rpow_natCast z 2]
      exact Real.rpow_le_rpow_of_exponent_le h (by norm_num)
    have h2 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
    linarith
  · have hz1 : z < 1 := not_le.mp h
    have h1 : z ^ ((3 : ℝ) / 2) ≤ 1 := by
      have h0 : z ^ ((3 : ℝ) / 2) ≤ (1 : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hz.le hz1.le (by norm_num)
      simpa using h0
    have h2 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith
    linarith

/-- The additivity of `D_z^k` on `F_* + u` on the open quadrant, for `k ≤ 2`. -/
theorem DzIter_Fstar_add {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {u : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {k : ℕ} (hk : k ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter k
          (fun z θ => Work.Construction.Fstar β z θ + u z θ) z θ
        = Work.Spaces.DzIter k (Work.Construction.Fstar β) z θ
          + Work.Spaces.DzIter k u z θ := by
  have hF2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hβ hβ1
  have hF1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 := hF2.of_le (by norm_num)
  have h4' : ContDiffOn ℝ 2 (Function.uncurry u) Work.FTS.EllipticEst.Q0 :=
    h4.of_le (by norm_num)
  have h4'' : ContDiffOn ℝ 1 (Function.uncurry u) Work.FTS.EllipticEst.Q0 :=
    h4.of_le (by norm_num)
  interval_cases k
  · intro z θ hz h1 h2; rfl
  · exact Work.FTS_RegExport.RXT.ftau_DzIter_one_add hF1 h4''
  · exact Work.FTS_RegExport.RXT.ftau_DzIter_two_add hF2 h4'


end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12Calc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.L12Calc` — the `L₁₂`-calculus for the profile `F(τ) = F_* + slice g τ`

* `dens_Fstar`, `abs_Fstar_le` — the density of the reference profile and its pointwise bound;
* `dens_add` — `L₁₂dens (F_* + u) = L₁₂dens F_* + L₁₂dens u` for `u` in the standing class;
* `abs_L12_le_majorant` — `|L₁₂ u z| ≤ 3(π/2) C₀ · 3` for `u` in the standing class;
* `abs_L12_Fstar_add_le` — the same for `F_* + u`;
* `dens_tendsto`, `L12_tendsto` — the convergence of the density and of `L₁₂` along the
  approximating families of `LimApprox` (dominated convergence in `θ`, then in `s`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 The density of the reference profile -/

/-- `SW s / s = s^{1/2}/(1+s)²`. -/
theorem SW_div (s : ℝ) (hs : 0 < s) : SW s / s = s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 := by
  have h := Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs
  simpa only [SW, Work.FTS_RegExport.RXT.L12Iter.Rwt] using h

/-- `|F_*(z,θ)| ≤ 20β z/(1+z)²` for `θ ∈ Iθ`, `z > 0`. -/
theorem abs_Fstar_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar β z θ| ≤ 20 * β * (z / (1 + z) ^ 2) := by
  have hc := (Work.Spaces.c_bounds β hβ hβ1).1
  have hg := Work.Spaces.Gam_bounds β θ hβ hθ
  have hcpos : 0 < Work.Spaces.c β := by linarith
  have hrad : 0 ≤ 2 * z / (1 + z) ^ 2 := by positivity
  have h1 : |Work.Spaces.Gam β θ / Work.Spaces.c β| ≤ 10 := by
    rw [abs_of_nonneg (div_nonneg hg.1 hcpos.le), div_le_iff₀ hcpos]
    nlinarith [hg.2, hc]
  rw [Work.Construction.Fstar, Work.FM.Fstar, abs_mul, abs_mul,
    abs_of_pos hβ, abs_of_nonneg hrad]
  calc β * |Work.Spaces.Gam β θ / Work.Spaces.c β| * (2 * z / (1 + z) ^ 2)
      ≤ β * 10 * (2 * z / (1 + z) ^ 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hβ.le) hrad
    _ = 20 * β * (z / (1 + z) ^ 2) := by ring

/-- The density of the reference profile. -/
theorem dens_Fstar {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (Work.Construction.Fstar β) s = 2 * β / (1 + s) ^ 2 := by
  have hcne : Work.Spaces.c β ≠ 0 := by
    have h := (Work.Spaces.c_bounds β hβ hβ1).1
    intro h0; rw [h0] at h; norm_num at h
  have hsne : s ≠ 0 := ne_of_gt hs
  have h1s : (1 : ℝ) + s ≠ 0 := by positivity
  have hc : (∫ θ in Icc 0 (Real.pi / 2), Work.Spaces.K θ * Work.Spaces.Gam β θ)
      = Work.Spaces.c β := by
    rw [Work.Spaces.c]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => by ring)
  rw [Work.Construction.L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar β s θ / s
      = (Work.Spaces.K θ * Work.Spaces.Gam β θ)
          * (β * (2 * s / (1 + s) ^ 2) / s / Work.Spaces.c β) := by
    intro θ; rw [Work.Construction.Fstar, Work.FM.Fstar]; ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
    MeasureTheory.integral_mul_const, hc]
  field_simp

/-! ## §2 Additivity of the density for `F_* + u` -/

/-- **Additivity of the `L₁₂`-density on `F_* + u`**, for `u` in the standing class. -/
theorem dens_add {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {u : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ C0 * SW z)
    {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (fun z θ => Work.Construction.Fstar β z θ + u z θ) s
      = 2 * β / (1 + s) ^ 2 + Work.Construction.L12dens u s := by
  have hFstar_cont : ContinuousOn (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hβ hβ1).continuousOn
  have hu_cont : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0 := h4.continuousOn
  have hK_cont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  -- integrability of the reference part
  have hintF : Integrable (fun θ => Work.Spaces.K θ * Work.Construction.Fstar β s θ / s)
      (volume.restrict (Icc 0 (Real.pi / 2))) := by
    refine Integrable.mono' (integrable_const (3 * (20 * β * (1 / (1 + s) ^ 2)))) ?_ ?_
    · refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
        (g := fun x θ => Work.Spaces.K θ * Work.Construction.Fstar β x θ / s) ?_ hs
      have hfun : Function.uncurry
          (fun x θ => Work.Spaces.K θ * Work.Construction.Fstar β x θ / s)
          = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Construction.Fstar β p.1 p.2 / s := rfl
      rw [hfun]
      exact (hK_cont.mul hFstar_cont).div_const s
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        have hK0 : Work.Spaces.K 0 = 0 := by
          rw [Work.Spaces.K, Real.sin_zero]; ring
        rw [hK0, zero_mul, zero_div, norm_zero]
        positivity
      rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
          rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
        rw [hK1, zero_mul, zero_div, norm_zero]
        positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul]
      have hF := abs_Fstar_le (β := β) (z := s) (θ := θ) hβ hβ1 hs
        ⟨h0.le, h1.le⟩
      have hK := abs_K_le_three θ
      have hprod : |Work.Spaces.K θ| * |Work.Construction.Fstar β s θ|
          ≤ 3 * (20 * β * (s / (1 + s) ^ 2)) :=
        mul_le_mul hK hF (abs_nonneg _) (by norm_num)
      calc |Work.Spaces.K θ| * |Work.Construction.Fstar β s θ| / s
          ≤ 3 * (20 * β * (s / (1 + s) ^ 2)) / s :=
            div_le_div_of_nonneg_right hprod hs.le
        _ = 3 * (20 * β * (1 / (1 + s) ^ 2)) := by
            field_simp
  -- integrability of the `u` part
  have hintU : Integrable (fun θ => Work.Spaces.K θ * u s θ / s)
      (volume.restrict (Icc 0 (Real.pi / 2))) := by
    have hbound : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.K θ * u s θ / s| ≤ 3 * (C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
      intro θ hθ0 hθ1
      rw [abs_div, abs_of_pos hs, abs_mul]
      have hF := hbd 0 (by norm_num) s θ hs hθ0 hθ1
      have hK := abs_K_le_three θ
      have hprod : |Work.Spaces.K θ| * |u s θ| ≤ 3 * (C0 * SW s) :=
        mul_le_mul hK hF (abs_nonneg _) (by norm_num)
      refine le_trans (div_le_div_of_nonneg_right hprod hs.le) (le_of_eq ?_)
      calc 3 * (C0 * SW s) / s = 3 * C0 * (SW s / s) := by field_simp
        _ = 3 * (C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
            rw [SW_div s hs]; ring
    refine Integrable.mono' (integrable_const (3 * (C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))))
      ?_ ?_
    · refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
        (g := fun x θ => Work.Spaces.K θ * u x θ / s) ?_ hs
      have hfun : Function.uncurry (fun x θ => Work.Spaces.K θ * u x θ / s)
          = fun p : ℝ × ℝ => Work.Spaces.K p.2 * u p.1 p.2 / s := rfl
      rw [hfun]
      exact (hK_cont.mul hu_cont).div_const s
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        have hK0 : Work.Spaces.K 0 = 0 := by
          rw [Work.Spaces.K, Real.sin_zero]; ring
        rw [hK0, zero_mul, zero_div, norm_zero]
        positivity
      rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
          rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
        rw [hK1, zero_mul, zero_div, norm_zero]
        positivity
      exact hbound θ h0 h1
  rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Construction.L12dens,
    Work.FM.L12dens]
  have hFs : (∫ θ in Icc 0 (Real.pi / 2),
        Work.Spaces.K θ * Work.Construction.Fstar β s θ / s)
      = 2 * β / (1 + s) ^ 2 := dens_Fstar hβ hβ1 hs
  have hcongr : (∫ θ in Icc 0 (Real.pi / 2), Work.Spaces.K θ
        * (Work.Construction.Fstar β s θ + u s θ) / s)
      = (∫ θ in Icc 0 (Real.pi / 2), Work.Spaces.K θ * Work.Construction.Fstar β s θ / s)
        + (∫ θ in Icc 0 (Real.pi / 2), Work.Spaces.K θ * u s θ / s) := by
    rw [← MeasureTheory.integral_add hintF hintU]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  rw [hcongr, hFs]

/-! ## §3 Bounds for `L₁₂` -/

/-- **The `L₁₂`-bound for a datum of the standing class.** -/
theorem abs_L12_le_majorant {u : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ C0 * SW z)
    {z : ℝ} (hz : 0 < z) :
    |Work.Construction.L12 u z| ≤ 3 * (Real.pi / 2) * C0 * 3 := by
  obtain ⟨hmajint, hmajbd⟩ := majorant_tail hz
  have hInt : Integrable (Work.FM.L12dens Work.Spaces.K u) (volume.restrict (Set.Ioi z)) :=
    Work.FTS_RegExport.RXT.L12Iter.L12dens_integrableOn hC0 h4 hbd hz
  have hbd' : ∀ s ∈ Set.Ioi z,
      |Work.FM.L12dens Work.Spaces.K u s|
        ≤ 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) :=
    fun s hs => Work.FTS_RegExport.RXT.L12Iter.abs_L12dens_le hC0 h4 hbd (lt_trans hz hs)
  have h1 : |Work.Construction.L12 u z|
      ≤ ∫ s in Set.Ioi z, |Work.FM.L12dens Work.Spaces.K u s| := by
    rw [Work.Construction.L12, Work.FM.L12]
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi z))
        (f := fun s => Work.FM.L12dens Work.Spaces.K u s))
  have hmajint' : Integrable
      (fun s : ℝ => 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      (volume.restrict (Set.Ioi z)) := hmajint.const_mul _
  have h2 : ∫ s in Set.Ioi z, |Work.FM.L12dens Work.Spaces.K u s|
      ≤ ∫ s in Set.Ioi z, 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
    refine MeasureTheory.integral_mono_ae hInt.abs hmajint' ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact hbd' s hs
  have h3 : ∫ s in Set.Ioi z, 3 * (Real.pi / 2) * C0 * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)
      = 3 * (Real.pi / 2) * C0
          * ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  have h4' : 3 * (Real.pi / 2) * C0 * ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
      ≤ 3 * (Real.pi / 2) * C0 * 3 := by
    refine mul_le_mul_of_nonneg_left hmajbd ?_
    positivity
  linarith [h1, h2, le_of_eq h3, h4']

/-- **The `L₁₂`-bound for `F_* + u`**, `u` in the standing class. -/
theorem abs_L12_Fstar_add_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {u : ℝ → ℝ → ℝ}
    {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hHk : Work.Spaces.HkMem β 4 u)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ C0 * SW z)
    {z : ℝ} (hz : 0 < z) :
    |Work.Construction.L12 (fun z θ => Work.Construction.Fstar β z θ + u z θ) z|
      ≤ 2 * β + 3 * (Real.pi / 2) * C0 * 3 := by
  rw [Work.FTS_RegExport.RXT.L12_Fstar_add_c4 hβ hβ1 h4 hHk hz.le]
  have hFs : Work.Construction.L12 (Work.Construction.Fstar β) z = 2 * β / (1 + z) :=
    Work.Construction.L12_Fstar_eq hβ hβ1 hz.le
  have h1 : 2 * β / (1 + z) ≤ 2 * β := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + z)]
    nlinarith [hβ]
  have h2 := abs_L12_le_majorant hC0 h4 hbd hz
  calc |Work.Construction.L12 (Work.Construction.Fstar β) z
        + Work.Construction.L12 u z|
      ≤ |Work.Construction.L12 (Work.Construction.Fstar β) z|
          + |Work.Construction.L12 u z| := abs_add_le _ _
    _ ≤ 2 * β + 3 * (Real.pi / 2) * C0 * 3 := by
        rw [hFs, abs_of_pos (by positivity : (0 : ℝ) < 2 * β / (1 + z))]
        linarith


/-! ## §4 Convergence of the density and of `L₁₂` along the approximating families -/

/-- **Dominated convergence in `θ`**: the `L₁₂`-density of `F(n) = F_* + slice (gn n) τ`
converges to that of `F = F_* + slice h τ`. -/
theorem dens_tendsto {β Cw : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hCw : 0 ≤ Cw)
    {gn : ℕ → Fam} {h : Fam} {τ : ℝ}
    (h4 : ∀ n : ℕ,
      ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop (𝓝 (slice h τ z θ)))
    {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun n => Work.Construction.L12dens (Work.Construction.Ftau β (gn n) τ) s)
      Filter.atTop (𝓝 (Work.Construction.L12dens (Work.Construction.Ftau β h τ) s)) := by
  have hFstar_cont : ContinuousOn (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hβ hβ1).continuousOn
  have hK_cont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hMn : 0 ≤ 20 * β * (1 / (1 + s) ^ 2) + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
    positivity
  have hFtau_eq : ∀ (n : ℕ) (x θ : ℝ),
      Work.Construction.Ftau β (gn n) τ x θ
        = Work.Construction.Fstar β x θ + slice (gn n) τ x θ := fun n x θ => rfl
  have hFtau_eq' : ∀ (x θ : ℝ),
      Work.Construction.Ftau β h τ x θ
        = Work.Construction.Fstar β x θ + slice h τ x θ := fun x θ => rfl
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc 0 (Real.pi / 2)))
    (F := fun n a => Work.Spaces.K a * Work.Construction.Ftau β (gn n) τ s a / s)
    (f := fun a => Work.Spaces.K a * Work.Construction.Ftau β h τ s a / s)
    (bound := fun _ => 3 * (20 * β * (1 / (1 + s) ^ 2)
      + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
    ?_ ?_ ?_ ?_
  · -- measurability
    intro n
    refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0
      (g := fun x θ => Work.Spaces.K θ * Work.Construction.Ftau β (gn n) τ x θ / s) ?_ hs
    have hfun : Function.uncurry
        (fun x θ => Work.Spaces.K θ * Work.Construction.Ftau β (gn n) τ x θ / s)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2
            * Work.Construction.Ftau β (gn n) τ p.1 p.2 / s := rfl
    rw [hfun]
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => Work.Construction.Ftau β (gn n) τ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      have hfun2 : (fun p : ℝ × ℝ => Work.Construction.Ftau β (gn n) τ p.1 p.2)
          = fun p : ℝ × ℝ =>
              Work.Construction.Fstar β p.1 p.2 + slice (gn n) τ p.1 p.2 := by
        funext p; rw [hFtau_eq]
      rw [hfun2]
      exact hFstar_cont.add (h4 n).continuousOn
    exact (hK_cont.mul hcont).div_const s
  · -- integrability of the constant bound
    exact MeasureTheory.integrable_const _
  · -- the a.e. domination
    intro n
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun a ha => ?_)
    rcases eq_or_lt_of_le ha.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      rw [hK0, zero_mul, zero_div, norm_zero]
      positivity
    rcases eq_or_lt_of_le ha.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      rw [hK1, zero_mul, zero_div, norm_zero]
      positivity
    have hcongr : Work.Spaces.K a * Work.Construction.Ftau β (gn n) τ s a / s
        = Work.Spaces.K a * (Work.Construction.Fstar β s a + slice (gn n) τ s a) / s := by
      rw [hFtau_eq n s a]
    rw [Real.norm_eq_abs, hcongr, abs_div, abs_of_pos hs, abs_mul]
    have hFs := abs_Fstar_le (β := β) (z := s) (θ := a) hβ hβ1 hs ⟨h0.le, h1.le⟩
    have hu := hbd n 0 (by norm_num) s a hs h0 h1
    have hsum : |Work.Construction.Fstar β s a + slice (gn n) τ s a|
        ≤ 20 * β * (s / (1 + s) ^ 2) + Cw * SW s := by
      refine le_trans (abs_add_le _ _) (add_le_add hFs hu)
    have hK := abs_K_le_three a
    have hprod : |Work.Spaces.K a| * |Work.Construction.Fstar β s a + slice (gn n) τ s a|
        ≤ 3 * (20 * β * (s / (1 + s) ^ 2) + Cw * SW s) :=
      mul_le_mul hK hsum (abs_nonneg _) (by norm_num)
    refine le_trans (div_le_div_of_nonneg_right hprod hs.le) (le_of_eq ?_)
    calc 3 * (20 * β * (s / (1 + s) ^ 2) + Cw * SW s) / s
        = 3 * (20 * β * (1 / (1 + s) ^ 2) + Cw * (SW s / s)) := by field_simp
      _ = 3 * (20 * β * (1 / (1 + s) ^ 2)
            + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by rw [SW_div s hs]
  · -- the a.e. convergence of the integrands
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun a ha => ?_)
    rcases eq_or_lt_of_le ha.1 with h0 | h0
    · subst h0
      have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
      simp only [hK0, zero_mul, zero_div]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le ha.2 with h1 | h1
    · subst h1
      have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      simp only [hK1, zero_mul, zero_div]
      exact tendsto_const_nhds
    have ht := hconv s a ⟨hs, h0, h1⟩
    exact (tendsto_const_nhds.mul (tendsto_const_nhds.add ht)).div_const s

/-- **The `L₁₂`-convergence along the approximating families.** -/
theorem L12_tendsto {β Cw : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hCw : 0 ≤ Cw)
    {gn : ℕ → Fam} {h : Fam} {τ : ℝ}
    (h4 : ∀ n : ℕ,
      ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop (𝓝 (slice h τ z θ)))
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n => Work.Construction.L12 (Work.Construction.Ftau β (gn n) τ) z)
      Filter.atTop (𝓝 (Work.Construction.L12 (Work.Construction.Ftau β h τ) z)) := by
  have hz0 : 0 ≤ z := hz.le
  have hp2 : Integrable (fun s : ℝ => (s ^ 2)⁻¹) (volume.restrict (Set.Ioi z)) := by
    have hp := integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2 : ℝ)) < -1) hz
    refine hp.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hz hs
    rw [Real.rpow_neg (le_of_lt hs0), Real.rpow_two]
  have hmaj : Integrable
      (fun s : ℝ => 2 * β * (s ^ 2)⁻¹ + 3 * (Real.pi / 2) * Cw
        * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) (volume.restrict (Set.Ioi z)) :=
    (hp2.const_mul _).add ((majorant_tail hz).1.const_mul _)
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi z))
    (F := fun n s => Work.FM.L12dens Work.Spaces.K
      (Work.Construction.Ftau β (gn n) τ) s)
    (f := fun s => Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau β h τ) s)
    (bound := fun s => 2 * β * (s ^ 2)⁻¹ + 3 * (Real.pi / 2) * Cw
      * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
    ?_ hmaj ?_ ?_
  · -- measurability of the densities
    intro n
    have hcont : ContinuousOn
        (fun s : ℝ => 2 * β / (1 + s) ^ 2
          + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s) (Set.Ioi 0) := by
      have h1 : ContinuousOn (fun s : ℝ => 2 * β / (1 + s) ^ 2) (Set.Ioi 0) :=
        continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
          (fun s hs => pow_ne_zero 2
            (ne_of_gt (by have hs' : (0 : ℝ) < s := hs; linarith)))
      exact h1.add (Work.FTS_RegExport.RXT.L12Iter.L12dens_continuousOn hCw (h4 n)
        (hbd n))
    have haesm : AEStronglyMeasurable
        (fun s : ℝ => 2 * β / (1 + s) ^ 2
          + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        (volume.restrict (Set.Ioi z)) :=
      (hcont.mono (Set.Ioi_subset_Ioi hz0)).aestronglyMeasurable measurableSet_Ioi
    refine haesm.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hz hs
    have h := dens_add (β := β) hβ hβ1 hCw (h4 n) (hbd n) (u := slice (gn n) τ) hs0
    exact h.symm
  · -- domination
    intro n
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hz hs
    have h := dens_add (β := β) hβ hβ1 hCw (h4 n) (hbd n) (u := slice (gn n) τ) hs0
    have hle : |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s|
        ≤ 3 * (Real.pi / 2) * Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) :=
      Work.FTS_RegExport.RXT.L12Iter.abs_L12dens_le hCw (h4 n) (hbd n) hs0
    have hFs : 2 * β / (1 + s) ^ 2 ≤ 2 * β * (s ^ 2)⁻¹ := by
      have hspos : (0 : ℝ) < s ^ 2 := by positivity
      have hle1 : 1 / (1 + s) ^ 2 ≤ 1 / s ^ 2 :=
        one_div_le_one_div_of_le hspos
          (by have h1 : (0 : ℝ) ≤ 1 + 2 * s := by linarith
              nlinarith [h1])
      calc 2 * β / (1 + s) ^ 2 = 2 * β * (1 / (1 + s) ^ 2) := by ring
        _ ≤ 2 * β * (1 / s ^ 2) := mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ = 2 * β * (s ^ 2)⁻¹ := by rw [one_div]
    have hEq : Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau β (gn n) τ) s
        = 2 * β / (1 + s) ^ 2 + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s := h
    have hkey : |Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau β (gn n) τ) s|
        ≤ 2 * β * (s ^ 2)⁻¹ + 3 * (Real.pi / 2) * Cw
          * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
      rw [hEq]
      calc |2 * β / (1 + s) ^ 2 + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s|
          ≤ |2 * β / (1 + s) ^ 2|
              + |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s| := abs_add_le _ _
        _ ≤ 2 * β * (s ^ 2)⁻¹ + 3 * (Real.pi / 2) * Cw
              * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
            refine add_le_add ?_ hle
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * β / (1 + s) ^ 2)]
            exact hFs
    rw [Real.norm_eq_abs]
    exact hkey
  · -- a.e. convergence
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact dens_tendsto (β := β) hβ hβ1 hCw h4 hbd hconv (lt_trans hz hs)

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.app_diff_w =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

theorem app_diff_w {α T L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Work.FTS.Galerkin.Fam}
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (gn n) τ))
    (hlip : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ (τ' : ℝ), τ' ∈ Set.Icc (0 : ℝ) T →
      Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ
        - Work.FTS.Galerkin.slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ (τ' : ℝ),
      τ' ∈ Set.Icc (0 : ℝ) T → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|
        ≤ Cw * SW z * |τ - τ'| := by
  -- The `Standing.app_diff_le` estimate, restricted to `τ, τ' ∈ [0,T]`, with the constant
  -- `max L 0` so that no sign hypothesis on `L` is needed: the weighted interior `L^∞`–`ℋ⁴`
  -- trade-off applied to the difference slot, whose `ℋ⁴`-norm is controlled by `hlip`.
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right L 0), ?_⟩
  intro n τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hcls := hcl n τ hτ
  have hcls' := hcl n τ' hτ'
  obtain ⟨hsm, hm, hb⟩ := Work.FTS_RegExport.RXR1.classC_sub_hyp hcls hcls'
  have h4 : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ))
      Work.FTS.EllipticEst.Q0 := hsm.forall 4
  have h1 := hC _ h4 hm hb b a hab z θ hz hθ0 hθ1
  have hsub := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open hcls.reg hcls'.reg b a
    z θ hz hθ0 hθ1
  have hHk : Work.Spaces.HkNorm α 4
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) ≤ L * |τ - τ'| :=
    hlip n τ hτ τ' hτ'
  have hHk' : Work.Spaces.HkNorm α 4
      (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ)
      ≤ max L 0 * |τ - τ'| :=
    le_trans hHk (mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _))
  have h3 : 0 ≤ C * SW z := mul_nonneg hC0 (SW_nonneg hz.le)
  have h5 : |Work.Spaces.mixed b a (slice (gn n) τ) z θ
      - Work.Spaces.mixed b a (slice (gn n) τ') z θ|
      = |Work.Spaces.mixed b a
          (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ| := by rw [hsub]
  rw [h5]
  calc |Work.Spaces.mixed b a
        (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ|
      ≤ C * SW z * Work.Spaces.HkNorm α 4
          (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) := h1
    _ ≤ C * SW z * (max L 0 * |τ - τ'|) := mul_le_mul_of_nonneg_left hHk' h3
    _ = C * max L 0 * SW z * |τ - τ'| := by ring

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.weighted_integrated_mp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.weighted_integrated_mp` — T5c of the RX-St1 leaf plan

The weighted, vector, integrated maximum principle in `(z,θ)`: the pulled-back unknown
`φ_k = w_k/ω` (`pw α (w k)`) satisfies, in the logarithmic coordinates
`s = log z`, `ψ = log tan θ`, the *integrated* transport identity

`φ_k(τ₂) − φ_k(τ₁) = ∫_{τ₁}^{τ₂}[f_k − (a·∂_sφ_k + b·∂_ψφ_k + c·φ_k)]`

with `f_k = R_k/om` bounded by `C·∑_j|φ_j| + Kσ`, coefficients `a = Vz`, `b = 2·b`,
`c = 2Vz/(1+z) + 2α·c2m(θ)·b` bounded by `2|M|`, `2|M|`, `(2+4α)|M|` respectively
(`pw_regularity`, `pw_identity_mine`, `pw_bounds`), so the general integrated supra-cone maximum
principle `cone_max_int` gives `|φ_k| ≤ exp(2((2+4α)|M| + n·C⁺)·τ)(K₀⁺ + τKσ⁺)`, and
transferring back (`ω(cz s, cth ψ) = om α s ψ > 0`, `z = eˢ`, `θ = arctan e^ψ`) gives the
claim.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

set_option maxHeartbeats 2000000

theorem weighted_integrated_mp {n : ℕ} {w wz wθ R : Fin n → ℝ → ℝ → ℝ → ℝ}
    {Vz b : ℝ → ℝ → ℝ → ℝ} {S M C K₀ Kσ α : ℝ} (hα : 0 < α) (hS : 0 < S)
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => w k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hz : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      HasDerivAt (fun z' => w k z' θ τ) (wz k z θ τ / z) z)
    (hθ : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      HasDerivAt (fun θ' => w k z θ' τ) (wθ k z θ τ / Real.sin (2 * θ)) θ)
    (hcz : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wz k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hcθ : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wθ k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hV : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun τ => Vz z θ τ) (Set.Icc 0 S) ∧ ContinuousOn (fun τ => b z θ τ) (Set.Icc 0 S))
    (hVb : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |Vz z θ τ| ≤ M ∧ |b z θ τ| ≤ M)
    (hRi : ∀ k z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      IntervalIntegrable (fun τ => R k z θ τ) MeasureTheory.volume 0 S)
    (hRb : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |R k z θ τ| ≤ C * ∑ j, |w j z θ τ| + Kσ * Work.FTS.RegExportIface.ω α z θ)
    (hId : ∀ k z θ τ₁ τ₂, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      w k z θ τ₂ - w k z θ τ₁
        = ∫ σ in τ₁..τ₂, (R k z θ σ - (Vz z θ σ * wz k z θ σ + b z θ σ * wθ k z θ σ)))
    (h0 : ∀ k z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → |w k z θ 0| ≤ K₀ * Work.FTS.RegExportIface.ω α z θ) :
    ∃ K : ℝ, ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |w k z θ τ| ≤ K * Work.FTS.RegExportIface.ω α z θ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, fun k => k.elim0⟩
  -- ## The three pull-back inputs
  obtain ⟨hpwcont, hpwscont, hpwψcont, hpws, hpwψ⟩ :=
    pw_regularity (n := n) (S := S) (α := α) hα hcont hz hθ hcz hcθ
  have hpwI := pw_identity_mine (n := n) (S := S) (α := α) hα hId
  obtain ⟨hcoefA, hcoefB, hcoefC, hsrc, hinit⟩ := pw_bounds (n := n) hα hS hVb hRb h0
  -- ## Interval-integrability of the pulled-back source
  have hfi : ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      IntervalIntegrable (fun σ => srcF α (R k) s ψ σ) MeasureTheory.volume τ₁ τ₂ := by
    intro k s ψ τ₁ τ₂ h1 h2 h3
    have hR : IntervalIntegrable (fun σ => R k (cz s) (cth ψ) σ) MeasureTheory.volume 0 S :=
      hRi k (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)
    have hRs : IntervalIntegrable (fun σ => R k (cz s) (cth ψ) σ) MeasureTheory.volume τ₁ τ₂ :=
      hR.mono_set (by
        rw [Set.uIcc_of_le h2, Set.uIcc_of_le (le_of_lt hS)]
        exact Set.Icc_subset_Icc (by linarith) h3)
    have h2' := hRs.div_const (om α s ψ)
    simpa only [srcF] using h2'
  -- ## τ-continuity of the pulled-back coefficients
  have hab : ∀ s ψ, ContinuousOn (fun τ => coefA Vz s ψ τ) (Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun τ => coefB b s ψ τ) (Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun τ => coefC α Vz b s ψ τ) (Set.Icc (0:ℝ) S) := by
    intro s ψ
    obtain ⟨hV1, hb1⟩ := hV (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)
    refine ⟨hV1, ?_, ?_⟩
    · simpa only [coefB] using hb1.const_mul (2 : ℝ)
    · have h1 : ContinuousOn (fun τ : ℝ => 2 * Vz (cz s) (cth ψ) τ / (1 + cz s))
          (Set.Icc (0:ℝ) S) := (hV1.const_mul (2 : ℝ)).div_const (1 + cz s)
      have h2 : ContinuousOn (fun τ : ℝ =>
          α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)) (Set.Icc (0:ℝ) S) :=
        (hb1.const_mul (2 : ℝ)).const_mul (α * Work.Construction.c2m (cth ψ))
      have h3 : ContinuousOn (fun τ : ℝ => 2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
          + α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)) (Set.Icc (0:ℝ) S) :=
        h1.add h2
      convert h3 using 1
      ext τ
      simp only [coefC]
  -- ## The integrated supra-cone maximum principle
  have hcone := cone_max_int (n := n)
    (φ := fun k => pw α (w k)) (φs := fun k => pws α (wz k) (w k))
    (φψ := fun k => pwψ α (wθ k) (w k)) (f := fun k => srcF α (R k))
    (a := coefA Vz) (b := coefB b) (c := coefC α Vz b)
    (T := S) (A := 2 * |M|) (C := (2 + 4 * α) * |M|) (C₀ := max C 0)
    (F := max Kσ 0) (K₀ := max K₀ 0)
    hS (by positivity) (by positivity) (le_max_right C 0) (le_max_right Kσ 0) (le_max_right K₀ 0)
    hpwcont hpwscont hpwψcont hpws hpwψ hab hcoefA hcoefB hcoefC hsrc hfi hpwI hinit
  -- ## Transfer back to `(z,θ)` and to `ω`
  refine ⟨Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S)
    * (max K₀ 0 + S * max Kσ 0), ?_⟩
  intro k z θ τ hz0 hθ0 hθπ hτ
  obtain ⟨s, hs⟩ := exists_exp z hz0
  obtain ⟨ψ, hψ⟩ := exists_arctan_exp θ hθ0 hθπ
  rw [← hs, ← hψ]
  have hom : 0 < om α s ψ := om_pos (α := α) hα
  have hC'nn : 0 ≤ 2 * ((2 + 4 * α) * |M| + ↑n * max C 0) := by positivity
  have h1 := hcone k s ψ τ hτ
  have hKσnn : 0 ≤ max Kσ 0 := le_max_right Kσ 0
  have hK₀nn : 0 ≤ max K₀ 0 := le_max_right K₀ 0
  have hexp : Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * τ)
      ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hτ.1, hτ.2, hC'nn]
  have hsum : max K₀ 0 + τ * max Kσ 0 ≤ max K₀ 0 + S * max Kσ 0 := by
    have h := mul_le_mul_of_nonneg_right hτ.2 hKσnn
    linarith
  have hnn : 0 ≤ max K₀ 0 + τ * max Kσ 0 := by
    have h := mul_nonneg hτ.1 hKσnn
    linarith
  have h2 : |pw α (w k) s ψ τ| ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S)
      * (max K₀ 0 + S * max Kσ 0) := by
    calc |pw α (w k) s ψ τ|
        ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * τ)
            * (max K₀ 0 + τ * max Kσ 0) := h1
      _ ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S)
            * (max K₀ 0 + S * max Kσ 0) :=
          mul_le_mul hexp hsum hnn (by positivity)
  have hw : |w k (cz s) (cth ψ) τ| = |pw α (w k) s ψ τ| * om α s ψ := by
    have h1' : pw α (w k) s ψ τ = w k (cz s) (cth ψ) τ / om α s ψ := rfl
    rw [h1', abs_div, abs_of_pos hom]
    exact (div_mul_cancel₀ _ (ne_of_gt hom)).symm
  have hgoal : |w k (cz s) (cth ψ) τ| ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S)
      * (max K₀ 0 + S * max Kσ 0) * om α s ψ := by
    rw [hw]
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt hom)
  exact hgoal

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.L12FtauTauLip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RXT0.L12FtauTauLip`

The `τ`-Lipschitz bound for `L₁₂(F(τ))` on a compact radial interval `[a,b]`, `a > 0`,
deduced from the *density* Lipschitz bound

  `|L12dens (F τ) r − L12dens (F τ') r| ≤ C · (SW r / r) · |τ − τ'|   (r > 0)`

together with the integrability of the densities on `(z,∞)`.

The only analytic input is the tail bound `∫_{(z,∞)} SW r / r ≤ 3` (i.e.
`∫_{(z,∞)} r^{1/2}/(1+r)² ≤ 3`, the module `majorant_tail`), which is what turns a
pointwise Lipschitz bound of the density into a Lipschitz bound of the tail integral
`L₁₂`: on `(z,∞) ⊆ (a,∞)` the integral of the majorant is bounded by `3`.

The general statement is isolated as `L12_lip_of_dens_lip` (no hypothesis on `f`, `g`
beyond the two integrability clauses, so it is reusable for any family).
-/

namespace Work.FTS_RegExport.RXT0

open MeasureTheory Set Filter
open scoped Real Topology

/-- `SW s / s = s^{1/2}/(1+s)²`. -/
private theorem SW_div' (s : ℝ) (hs : 0 < s) :
    Work.FTS_RegExport.RXT.Sys.L12FKaux.SW s / s = s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 := by
  have h := Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs
  simpa only [Work.FTS_RegExport.RXT.Sys.L12FKaux.SW,
    Work.FTS_RegExport.RXT.L12Iter.Rwt] using h

/-- The tail bound `∫_{(z,∞)} SW r / r ≤ 3` and the integrability of the integrand. -/
private theorem SW_div_tail {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun r : ℝ => Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) (Set.Ioi z) ∧
      ∫ r in Set.Ioi z, Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r ≤ 3 := by
  obtain ⟨hint, hval⟩ := Work.FTS_RegExport.RXT.Sys.L12FKaux.majorant_tail hz
  have hcongr : ∀ r ∈ Set.Ioi z,
      (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) r
        = (fun r : ℝ => Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) r :=
    fun r hr => (SW_div' r (lt_trans hz hr)).symm
  refine ⟨hint.congr ?_, ?_⟩
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact hcongr r hr
  · rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun r hr => (hcongr r hr).symm)]
    exact hval

/-- **The `L₁₂`-difference bound from a density bound.**  If the density of `L₁₂ f`
differs from that of `L₁₂ g` pointwise by at most `C · (SW r / r) · c` and both densities
are integrable on `(z,∞)`, then on every compact interval `[a,b]` with `a > 0` the values
of `L₁₂` differ by at most `3 C c`.  (No regularity of `f`, `g` is needed; the number `3`
is the tail bound `∫_{(z,∞)} SW r/r ≤ 3`.) -/
theorem L12_lip_of_dens_lip {f g : ℝ → ℝ → ℝ} {C c : ℝ} (hC0 : 0 ≤ C) (hc : 0 ≤ c)
    (hlip : ∀ r : ℝ, 0 < r →
      |Work.Construction.L12dens f r - Work.Construction.L12dens g r|
        ≤ C * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) * c)
    (hf : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi z))
    (hg : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens g) (Set.Ioi z)) :
    ∀ a b : ℝ, 0 < a → a ≤ b → ∀ z ∈ Set.Icc a b,
      |Work.Construction.L12 f z - Work.Construction.L12 g z| ≤ C * 3 * c := by
  intro a b ha hab z hz
  have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
  have hFint : Integrable (Work.Construction.L12dens f) (volume.restrict (Set.Ioi z)) := hf z hz0
  have hGint : Integrable (Work.Construction.L12dens g) (volume.restrict (Set.Ioi z)) := hg z hz0
  have hL12 : Work.Construction.L12 f z
      = ∫ r in Set.Ioi z, Work.Construction.L12dens f r := rfl
  have hL12' : Work.Construction.L12 g z
      = ∫ r in Set.Ioi z, Work.Construction.L12dens g r := rfl
  have hsub : (∫ r in Set.Ioi z, Work.Construction.L12dens f r)
        - (∫ r in Set.Ioi z, Work.Construction.L12dens g r)
      = ∫ r in Set.Ioi z, (Work.Construction.L12dens f r - Work.Construction.L12dens g r) :=
    (MeasureTheory.integral_sub hFint hGint).symm
  have habs : ∀ r ∈ Set.Ioi z,
      |Work.Construction.L12dens f r - Work.Construction.L12dens g r|
        ≤ C * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) * c :=
    fun r hr => hlip r (lt_trans hz0 hr)
  have hInt1 : Integrable
      (fun r => |Work.Construction.L12dens f r - Work.Construction.L12dens g r|)
      (volume.restrict (Set.Ioi z)) := (hFint.sub hGint).abs
  have hInt2 : Integrable
      (fun r => C * c * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r))
      (volume.restrict (Set.Ioi z)) :=
    (SW_div_tail hz0).1.const_mul (C * c)
  have hmono : ∫ r in Set.Ioi z,
        |Work.Construction.L12dens f r - Work.Construction.L12dens g r|
      ≤ ∫ r in Set.Ioi z, C * c * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) := by
    refine MeasureTheory.integral_mono_ae hInt1 hInt2 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using habs r hr
  have hconst : ∫ r in Set.Ioi z, C * c * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r)
      = C * c * ∫ r in Set.Ioi z, Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r :=
    MeasureTheory.integral_const_mul _ _
  have htail : ∫ r in Set.Ioi z, Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r ≤ 3 :=
    (SW_div_tail hz0).2
  rw [hL12, hL12', hsub]
  calc |∫ r in Set.Ioi z, (Work.Construction.L12dens f r - Work.Construction.L12dens g r)|
      ≤ ∫ r in Set.Ioi z, |Work.Construction.L12dens f r - Work.Construction.L12dens g r| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r in Set.Ioi z, C * c * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) := hmono
    _ = C * c * ∫ r in Set.Ioi z, Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r := hconst
    _ ≤ C * c * 3 := mul_le_mul_of_nonneg_left htail (mul_nonneg hC0 hc)
    _ = C * 3 * c := by ring

theorem L12FtauTauLip {g : Work.FTS.Galerkin.Fam} {α : ℝ} (S : ℝ) (hS : 0 < S)
    (hQ : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ r : ℝ, 0 < r →
        |Work.Construction.L12dens (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) r
          - Work.Construction.L12dens (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ') r|
        ≤ C * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) * |τ - τ'|)
    (hint : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi z)) :
    ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, ∀ z ∈ Set.Icc a b,
        |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z
          - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ') z| ≤ C * |τ - τ'| := by
  obtain ⟨C, hC0, hC⟩ := hQ
  intro a b ha hab
  refine ⟨C * 3, by linarith [hS], ?_⟩
  intro τ hτ τ' hτ' z hz
  exact L12_lip_of_dens_lip
      (f := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ)
      (g := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ')
      (C := C) (c := |τ - τ'|) hC0 (abs_nonneg _)
      (fun r hr => hC τ hτ τ' hτ' r hr)
      (fun z hz => hint τ hτ z hz) (fun z hz => hint τ' hτ' z hz) a b ha hab z hz

end Work.FTS_RegExport.RXT0
end
