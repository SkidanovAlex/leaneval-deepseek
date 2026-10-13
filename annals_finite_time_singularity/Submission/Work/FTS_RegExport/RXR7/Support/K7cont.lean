import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXR7.Defs
import Submission.Work.FTS_RegExport.RXT.jc3
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.C2Psi

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
