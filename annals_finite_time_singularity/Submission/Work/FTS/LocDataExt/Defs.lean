import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.CoercivityStep.Step
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.lineDerivOp_smulLeftCLM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.EllipticEst.InteriorRegularity.Q0

open scoped SchwartzMap Topology
open MeasureTheory Set Filter

/-- The pointwise Leibniz rule for the line derivative, for two complex-valued functions that are
differentiable at the point in question. -/
theorem lineDeriv_mul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f k : E → ℂ} {x m : E} (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x) :
    lineDeriv ℝ (fun y => f y * k y) x m = f x * lineDeriv ℝ k x m + lineDeriv ℝ f x m * k x := by
  have hmul : DifferentiableAt ℝ (fun y => f y * k y) x := hf.mul hk
  rw [hf.lineDeriv_eq_fderiv, hk.lineDeriv_eq_fderiv, hmul.lineDeriv_eq_fderiv,
    fderiv_fun_mul hf hk]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring



end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The coordinate map `(s,θ) ↦ coords s θ` -/

theorem continuous_coords : Continuous (fun p : ℝ × ℝ => coords p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => coords p.1 p.2) =
      fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1 := by
    funext p
    ext i
    fin_cases i <;> simp [coords, e0, e1]
  rw [h]
  exact (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

theorem coords_zero (s θ : ℝ) : (coords s θ) 0 = s := by simp [coords]

theorem coords_one (s θ : ℝ) : (coords s θ) 1 = θ := by simp [coords]

theorem coords_injective : Function.Injective (fun p : ℝ × ℝ => coords p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h' : coords a b = coords c d := h
  have h0 : (coords a b) 0 = (coords c d) 0 := congrArg (fun v : E2 => v 0) h'
  have h1 : (coords a b) 1 = (coords c d) 1 := congrArg (fun v : E2 => v 1) h'
  rw [coords_zero, coords_zero] at h0
  rw [coords_one, coords_one] at h1
  exact Prod.ext h0 h1

theorem measurable_coords_fst : Measurable fun x : E2 => x 0 :=
  (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).measurable

theorem measurable_coords_snd : Measurable fun x : E2 => x 1 :=
  (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)).measurable

theorem coords_measurableEmbedding :
    MeasurableEmbedding (fun p : ℝ × ℝ => coords p.1 p.2) := by
  refine ⟨coords_injective, continuous_coords.measurable, ?_⟩
  intro s hs
  have hg : Measurable fun x : E2 => (x 0, x 1) :=
    measurable_coords_fst.prodMk measurable_coords_snd
  have h1 : (fun p : ℝ × ℝ => coords p.1 p.2) '' s = (fun x : E2 => (x 0, x 1)) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      show ((coords p.1 p.2) 0, (coords p.1 p.2) 1) ∈ s
      rw [coords_zero, coords_one]
      exact hp
    · intro hy
      refine ⟨(y 0, y 1), hy, ?_⟩
      ext i
      fin_cases i <;> simp [coords]
  rw [h1]
  exact hg hs

theorem coords_measurePreserving :
    MeasurePreserving (fun p : ℝ × ℝ => coords p.1 p.2) volume volume := by
  have h1 : MeasurePreserving ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm)
      (volume : Measure (ℝ × ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).symm
  have h2 : MeasurePreserving (WithLp.toLp 2 : (Fin 2 → ℝ) → E2)
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure E2) :=
    PiLp.volume_preserving_toLp (Fin 2)
  have h3 := h2.comp h1
  convert h3 using 2
  ext i
  fin_cases i <;> simp [coords, MeasurableEquiv.finTwoArrow_symm_apply]

/-! ## The strip -/

theorem continuous_coord_one : Continuous fun x : E2 => x 1 :=
  PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)

theorem isOpen_stripE : IsOpen stripE :=
  isOpen_Ioo.preimage continuous_coord_one

theorem mem_stripE {x : E2} : x ∈ stripE ↔ 0 < x 1 ∧ x 1 < Real.pi / 2 := Iff.rfl


/-- On `α ≠ 0` the weight `wt α` is the explicitly exponential function
`α * exp ((5+2α) s) * cos θ`. -/
theorem wt_eq_exp {α : ℝ} (hα : α ≠ 0) :
    wt α = fun x : E2 => α * Real.exp ((5 + 2 * α) * x 0) * Real.cos (x 1) := by
  funext x
  rw [wt, Real.rpow_def_of_pos (Real.exp_pos (α * x 0)), Real.log_exp]
  rw [show α * x 0 * ((5 + 2 * α) / α) = (5 + 2 * α) * x 0 by field_simp]

theorem wt_contDiff {α : ℝ} (hα : α ≠ 0) (n : ℕ) : ContDiff ℝ n (wt α) := by
  rw [wt_eq_exp hα]
  fun_prop

theorem wt_ne_zero {α : ℝ} (hα : 0 < α) {x : E2} (hx : x ∈ stripE) : wt α x ≠ 0 := by
  rw [wt]
  have h1 : 0 < Real.exp (α * x 0) ^ ((5 + 2 * α) / α) :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have h2 : 0 < Real.cos (x 1) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
  positivity

/-! ## The un-indicated pull-backs -/

@[simp] theorem Ws_apply (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : E2) :
    Ws α Ψ x = ((wt α x * Ψ (Real.exp (α * x 0)) (x 1) : ℝ) : ℂ) := rfl

@[simp] theorem Gs_apply (α : ℝ) (F : ℝ → ℝ → ℝ) (x : E2) :
    Gs α F x = ((wt α x * F (Real.exp (α * x 0)) (x 1) : ℝ) : ℂ) := rfl








/-! ## The scaled bump `cfun` -/

@[simp] theorem cfun_apply (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) (x : E2) :
    cfun x₀ ρ hρ x = (((cdb x₀ ρ hρ) x : ℝ) : ℂ) := rfl

theorem cfun_contDiff (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) : ∀ n : ℕ, ContDiff ℝ n (cfun x₀ ρ hρ) := by
  intro n
  change ContDiff ℝ n (fun x : E2 => (((cdb x₀ ρ hρ) x : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((cdb x₀ ρ hρ).contDiff (n := (n : ℕ∞)))

theorem cfun_support (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) :
    Function.support (cfun x₀ ρ hρ) = Metric.ball x₀ (2 * ρ) := by
  have h1 : Function.support (cfun x₀ ρ hρ) = Function.support (↑(cdb x₀ ρ hρ) : E2 → ℝ) := by
    ext x
    simp [Function.mem_support, cfun_apply, Complex.ofReal_eq_zero]
  rw [h1, ContDiffBump.support_eq]
  rfl

theorem cfun_tsupport (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) :
    tsupport (cfun x₀ ρ hρ) = Metric.closedBall x₀ (2 * ρ) := by
  rw [tsupport, cfun_support]
  exact closure_ball x₀ (ne_of_gt (by linarith : (0 : ℝ) < 2 * ρ))

theorem cfun_one {x₀ x : E2} {ρ : ℝ} (hρ : 0 < ρ) (hx : x ∈ Metric.closedBall x₀ ρ) :
    cfun x₀ ρ hρ x = 1 := by
  rw [cfun_apply, ContDiffBump.one_of_mem_closedBall]
  · simp
  · rwa [cdb]


theorem cfun_hasCompactSupport (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (cfun x₀ ρ hρ) := by
  simpa [HasCompactSupport, cfun_tsupport x₀ ρ hρ] using isCompact_closedBall x₀ (2 * ρ)

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.CoercivityStep.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep

set_option autoImplicit false

/-- The paper's recursion iterated four times from `H1IP`:
`IP₄ = HkIPStep 1 1 (HkIPStep 1 1 (HkIPStep 1 1 (H1IP α)))`. -/
def IP4 (α : ℝ) : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ :=
  Work.Coercivity.HkIPStep 1 1
    (Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.H1IP α)))

/-- The paper's recursion iterated three times from `H1IP`:
`IP₃ = HkIPStep 1 1 (HkIPStep 1 1 (H1IP α))`. -/
def IP3 (α : ℝ) : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ :=
  Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.H1IP α))






end Work.FTS.CoercivityStep
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.GbarSin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Auxiliary lemmas of the assembly -/

/-- A predicate which holds on the open interval `(0, π/2)` holds almost everywhere on `Iθ`
(the two endpoints `0` and `π/2` form a null set). -/
theorem ae_imp_of_mem_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume), θ ∈ Work.Spaces.Iθ → p θ := by
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := by
      by_contra hc
      exact hθ (fun h' => absurd h' hc)
    have hpθ : ¬ p θ := fun hp => hθ (fun _ => hp)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    have hcon1 : θ ≠ 0 := fun h => hcon (Or.inl h)
    have hcon2 : θ ≠ π / 2 := fun h => hcon (Or.inr h)
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    exact hpθ (h θ ⟨lt_of_le_of_ne hθI.1 (Ne.symm hcon1), lt_of_le_of_ne hθI.2 hcon2⟩)
  · have hset : ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (π / 2))

/-- The angular slice of `D_z^i F` against the weight `sinθcos²θ` is integrable on `Iθ`.
(Specialisation of the Cauchy--Schwarz bound `integrableOn_zSummand` to the bounded angular
weight `sinθcos²θ` of the moment `F_*`.) -/
theorem integrableOn_DzIter_mul_sinCos2 (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {i : ℕ} (hi : i ≤ k) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter i F z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have hsq := Work.FTS.EllipticEst.integrableOn_zSummand α k hF hmem i hi hzI
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1)
      Work.Spaces.Iθ := hsq.add hconst
  refine Integrable.mono' hsum ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (((hF.DzIter i).continuousOn).mul (by unfold Work.Elliptic.sinCos2; fun_prop)) hz
  · rw [Work.Spaces.Iθ, ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun θ hθ => ?_
    have hb := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.DzIter i F z θ) hz hθ
    simpa only [Real.norm_eq_abs] using hb

/-- The uncurried function `(r,θ) ↦ ∂_z(D_z^j F)(r,θ)·sinθcos²θ` is integrable on
`(s,z] × Iθ`: this is the Fubini hypothesis for the chain rule. -/
theorem integrable_uncurry_pz_mul_sinCos2 (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s) :
    MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h2 := Work.FTS.EllipticEst.integrable_prod_sq_restrict_open α k F hF hmem (j + 1) hj
    (a := s) (b := z) (le_of_lt hs)
  have hD : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (1 / s) * ((Work.Spaces.DzIter (j + 1) F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (h2.add (MeasureTheory.integrable_const (1 : ℝ))).const_mul (1 / s)
  refine Integrable.mono' hD ?_ ?_
  · exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
        * Work.Elliptic.sinCos2 p.2)
      ((((hF.DzIter j).pz).continuousOn).mul (by unfold Work.Elliptic.sinCos2; fun_prop))
      (le_of_lt hs)
  · have hprod : (MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Set.Ioc s z ×ˢ Work.Spaces.Iθ) := MeasureTheory.Measure.prod_restrict _ _
    rw [hprod]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod measurableSet_Icc) fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := hp
    have hr : 0 < p.1 := lt_of_lt_of_le hs (le_of_lt hp1.1)
    have hDz : Work.Spaces.DzIter (j + 1) F p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hb := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.DzIter (j + 1) F p.1 θ) hr hp2
    have hstep : |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
          * Work.Elliptic.sinCos2 p.2|
        = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1 := by
      rw [eq_div_iff hr.ne']
      calc |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2| * p.1
          = |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2|
              * |p.1| := by rw [abs_of_pos hr]
        _ = |(Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
              * Work.Elliptic.sinCos2 p.2) * p.1| := (abs_mul _ _).symm
        _ = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| := by
            rw [hDz]; congr 1; ring
    have hle : |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1
        ≤ |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s :=
      div_le_div_of_nonneg_left (abs_nonneg _) hs (le_of_lt hp1.1)
    calc ‖Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        = |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2| :=
          Real.norm_eq_abs _
      _ = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1 := hstep
      _ ≤ |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s := hle
      _ ≤ (1 / s) * ((Work.Spaces.DzIter (j + 1) F p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1) := by
          rw [show |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s
              = (1 / s) * |Work.Spaces.DzIter (j + 1) F p.1 p.2
                  * Work.Elliptic.sinCos2 p.2| by ring]
          exact mul_le_mul_of_nonneg_left hb (by positivity)

/-! ## The chain rule -/

/-- **The chain rule for the angular moment along `D_z`.**  For `F` smooth on the open
quadrant with `F ∈ ℋ^k` and `j + 1 ≤ k`, the moment `F_*(D_z^j F)` is an antiderivative of
`F_*(D_z^{j+1} F)/r`: `F_*(D_z^j F)(z) - F_*(D_z^j F)(s) = ∫_s^z F_*(D_z^{j+1} F)(r)/r dr`
for `0 < s ≤ z`. -/
theorem FstarDzIter_chain_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := by
  rcases eq_or_lt_of_le hsz with hsz0 | hszlt
  · rw [← hsz0, sub_self, intervalIntegral.integral_same]
  have hzpos : 0 < z := lt_of_lt_of_le hs (le_of_lt hszlt)
  have hjle : j ≤ k := Nat.le_of_succ_le hj
  have hIz := integrableOn_DzIter_mul_sinCos2 α k F hF hmem hjle hzpos
  have hIs := integrableOn_DzIter_mul_sinCos2 α k F hF hmem hjle hs
  have hFub := integrable_uncurry_pz_mul_sinCos2 α k F hF hmem j hj (s := s) (z := z) hs
  have h1 : Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
          - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.Fstar]
    rw [show (fun θ : ℝ => (Work.Spaces.DzIter j F z θ - Work.Spaces.DzIter j F s θ)
          * Work.Elliptic.sinCos2 θ)
        = fun θ => Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ
            - Work.Spaces.DzIter j F s θ * Work.Elliptic.sinCos2 θ from by
      funext θ; ring]
    rw [MeasureTheory.integral_sub hIz hIs]
  have h2 : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
        - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ
      = ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
          * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
    refine ae_imp_of_mem_Ioo fun θ hθ => ?_
    rw [Work.FTS.EllipticEst.DzIter_slice_FTC_open hF j hs hsz hθ]
  have h3 : ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
        * Work.Elliptic.sinCos2 θ
      = ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    exact (intervalIntegral.integral_mul_const (Work.Elliptic.sinCos2 θ)
      (fun r => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)).symm
  have h4 : ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ
      = ∫ r in s..z, ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := by
    refine (MeasureTheory.intervalIntegral_integral_swap (a := s) (b := z)
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun r θ => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
        * Work.Elliptic.sinCos2 θ) ?_).symm
    rwa [Set.uIoc_of_le hsz]
  have h5 : ∫ r in s..z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ)
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hsr : s ≤ r := le_trans (le_of_eq (min_eq_left hsz).symm) hr.1
    have hr0 : 0 < r := lt_of_lt_of_le hs hsr
    have hval : Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r
        = r * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
            * Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.Fstar]
      rw [show (fun θ : ℝ => Work.Spaces.DzIter (j + 1) F r θ * Work.Elliptic.sinCos2 θ)
          = fun θ => r * (Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
              * Work.Elliptic.sinCos2 θ) from by
        funext θ; simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]; ring]
      rw [MeasureTheory.integral_const_mul]
    rw [hval, mul_div_cancel_left₀ _ hr0.ne']
  calc Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
          - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ := h1
    _ = ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
          * Work.Elliptic.sinCos2 θ := h2
    _ = ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := h3
    _ = ∫ r in s..z, ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := h4
    _ = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := h5

end Work.FTS.EllipticEst.Cert.GbarSin
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.FnLintegralLeHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary facts used below

The statement of the target lemma is an estimate of the `z`-`lintegral` of
`φ z · w z²` against the *slice* `θ`-`lintegral` of `G z θ² · sin(2θ)^{-η}` by the level-`0`
quantity `HkSq α 0 G`.  The pointwise input is that `HkIntegrand α 0 G z θ` is exactly
`w z² · (G z θ² · sin(2θ)^{-η})`, the weight `w z²` being a `θ`-independent factor. -/

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is nonnegative on `[0, π/2]`. -/
theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _

/-- **The level-`0` integrand, with the radial factor pulled out.**  On `Iθ`,
`HkIntegrand α 0 G z θ = w z² · (G z θ² · sin(2θ)^{-η})`. -/
theorem HkIntegrand_zero_eq_w2_sEta (α : ℝ) (G : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 G z θ
      = (Work.Spaces.w z) ^ 2 * ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.sq_profile_eq G z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.sEta]
  ring

/-- The radial weight vanishes at `z = 0` (Lean's totalised division). -/
theorem w_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

theorem FnLintegralLeHkSq {α : ℝ} {G : ℝ → ℝ → ℝ} (hG : Work.Spaces.HkMem α 0 G)
    (φ : ℝ → ℝ) (hφnn : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
  -- The unweighted `θ`-slice of the `H⁰`-energy of `G`.
  let S : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  -- `HkMem α 0 G` identifies `HkSq α 0 G` with the `z`-integral of `w z² · S z`.
  have hslice := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral (α := α) (g := G) hG
  have h_int_outer : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * S z) Work.Spaces.Iz := hslice.1
  have h_eq_outer : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * S z)
      = Work.Spaces.HkSq α 0 G := hslice.2
  -- The `θ`-integrand is nonnegative a.e., hence so is every slice `S z`.
  have hnn_θ : ∀ z : ℝ, 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro z
    refine (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc).mpr ?_
    exact Filter.Eventually.of_forall
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  have S_nonneg : ∀ z : ℝ, 0 ≤ S z := fun z =>
    MeasureTheory.integral_nonneg_of_ae (hnn_θ z)
  -- On `z > 0` the unweighted slice is honest: it is a multiple of `HkIntegrand α 0 G z ·`.
  have hInt : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := by
    intro z hz
    have hHk : MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 G z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hG.1 z (Set.mem_Ici.mpr (le_of_lt hz))
    have hconst : MeasureTheory.Integrable
        (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 0 G z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hHk.const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun hconst ?_ measurableSet_Icc
    intro θ hθ
    change ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 0 G z θ
      = (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [HkIntegrand_zero_eq_w2_sEta α G hθ]
    have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.AngSecond.w_pos hz))
    rw [inv_mul_cancel_left₀ hw2]
  -- Pointwise comparison of the `z`-integrands on the half-line.
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * S z) := by
    intro z hz
    rcases lt_or_eq_of_le (Set.mem_Ici.mp hz) with hzpos | hz0
    · -- `z > 0`: turn the inner `lintegral` into `ofReal (S z)` and multiply out.
      have hinner : (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          = ENNReal.ofReal (S z) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hInt z hzpos) (hnn_θ z)).symm
      rw [hinner, ← ENNReal.ofReal_mul (mul_nonneg (hφnn z) (sq_nonneg _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hSw : 0 ≤ (Work.Spaces.w z) ^ 2 * S z := mul_nonneg (sq_nonneg _) (S_nonneg z)
      have h1 : φ z * ((Work.Spaces.w z) ^ 2 * S z) ≤ (Work.Spaces.w z) ^ 2 * S z := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hφ1 z) hSw
      calc (φ z * (Work.Spaces.w z) ^ 2) * S z
          = φ z * ((Work.Spaces.w z) ^ 2 * S z) := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * S z := h1
    · -- `z = 0`: the radial weight vanishes, so both sides are `0`.
      subst hz0
      rw [w_zero]
      simp
  -- `HkSq α 0 G` is the `z`-`lintegral` of `ofReal (w z² · S z)`.
  have h_rhs : ENNReal.ofReal (Work.Spaces.HkSq α 0 G)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * S z) := by
    rw [← h_eq_outer]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_outer
      (Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (S_nonneg z)))
  calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * S z) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        refine (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mpr ?_
        exact Filter.Eventually.of_forall (fun z hz => hpt z hz)
    _ = ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := h_rhs.symm

end Work.FTS.EllipticEst.H2W.AeProof
end
-- ===== merged: Submission.Work.FTS.LocData.ZfarFstar.ZfarPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ZfarDzIterBound {Kc : ℝ}
    (hKc : ∀ (L : ℝ), 1 ≤ L → ∀ (c : ℕ), c ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Kc)
    (hKc1 : 1 ≤ Kc)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (L : ℝ) (hL : 1 ≤ L)
    (z : ℝ) (hz1 : 1 ≤ z) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (i : ℕ) (hi : i ≤ 4) :
    |Work.Spaces.DzIter i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      * Work.Spaces.w z| ≤ 64 * Kc * α * Work.Spaces.Gam α θ / z := by
  have hz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact Set.mem_Ici.mpr (by linarith)
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hzpos : 0 < z := by linarith
  set G0 : ℝ → ℝ := fun z => (1 : ℝ) - Work.Stability.chi (z / L) with hG0
  set G : ℝ → ℝ → ℝ := fun z _ => G0 z with hG
  set F : ℝ → ℝ → ℝ := Work.Construction.Fstar α with hF
  have hfun : Work.Stability.zfar L (Work.Construction.Fstar α) = fun z θ => G z θ * F z θ := by
    funext z θ
    rw [Work.Stability.zfar_apply]
  have hzfar : Work.Spaces.DzIter i (Work.Stability.zfar L (Work.Construction.Fstar α))
      = Work.Spaces.DzIter i (fun z θ => G z θ * F z θ) := by rw [hfun]
  have hleib := Work.FTS.LocData.DzIter_mul_smoothQuad i G F hz
    (ZFBase.contDiffOn_slice_oneSubChi L) (ZFBase.contDiffOn_slice_Fstar α θ)
  rw [hzfar, hleib]
  have hterm : ∀ b ∈ Finset.range (i + 1),
      |(i.choose b : ℝ) * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)|
        * |Work.Spaces.w z| ≤ (i.choose b : ℝ) * (Kc * (4 * α * Work.Spaces.Gam α θ / z)) := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hb4 : b ≤ 4 := le_trans hbi hi
    have hib4 : i - b ≤ 4 := le_trans (Nat.sub_le i b) hi
    have hc0 : (0 : ℝ) ≤ (i.choose b : ℝ) := Nat.cast_nonneg _
    have hA : |Work.Spaces.DzIter b G z θ| ≤ Kc := hKc L hL b hb4 z hz θ
    have hB : |Work.Spaces.DzIter (i - b) F z θ * Work.Spaces.w z|
        ≤ 4 * α * Work.Spaces.Gam α θ / z := ZFBase.DzIter_Fstar_w_le α hα hα1 hib4 hz1 hθ
    have hBw : |Work.Spaces.DzIter (i - b) F z θ| * |Work.Spaces.w z|
        ≤ 4 * α * Work.Spaces.Gam α θ / z := by simpa only [abs_mul] using hB
    have heq : |(i.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)|
        * |Work.Spaces.w z|
        = (i.choose b : ℝ) * (|Work.Spaces.DzIter b G z θ|
            * (|Work.Spaces.DzIter (i - b) F z θ| * |Work.Spaces.w z|)) := by
      simp only [abs_mul, abs_of_nonneg hc0]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hA hBw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (le_trans (by norm_num) hKc1)) hc0
  calc |(∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
        * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)) * Work.Spaces.w z|
      = |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)| * |Work.Spaces.w z| := by
        rw [abs_mul]
    _ ≤ (∑ b ∈ Finset.range (i + 1), |(i.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)|) * |Work.Spaces.w z| :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ = ∑ b ∈ Finset.range (i + 1), |(i.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)|
          * |Work.Spaces.w z| := by
        rw [Finset.sum_mul]
    _ ≤ ∑ b ∈ Finset.range (i + 1),
          (i.choose b : ℝ) * (Kc * (4 * α * Work.Spaces.Gam α θ / z)) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ i * (Kc * (4 * α * Work.Spaces.Gam α θ / z)) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose i
    _ ≤ 64 * Kc * α * Work.Spaces.Gam α θ / z := by
        have h2i : (2 : ℝ) ^ i ≤ 16 := by
          calc (2 : ℝ) ^ i ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hi
            _ = 16 := by norm_num
        have hX : 0 ≤ Kc * (4 * α * Work.Spaces.Gam α θ / z) := by positivity
        calc (2 : ℝ) ^ i * (Kc * (4 * α * Work.Spaces.Gam α θ / z))
            ≤ 16 * (Kc * (4 * α * Work.Spaces.Gam α θ / z)) :=
              mul_le_mul_of_nonneg_right h2i hX
          _ = 64 * Kc * α * Work.Spaces.Gam α θ / z := by ring

theorem ZfarMixedBound {Kc : ℝ}
    (hKc : ∀ (L : ℝ), 1 ≤ L → ∀ (c : ℕ), c ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Kc)
    (hKc1 : 1 ≤ Kc)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (L : ℝ) (hL : 1 ≤ L)
    (z : ℝ) (hz1 : 1 ≤ z) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) (hi : 1 ≤ i) (j : ℕ) (hij : i + j ≤ 4) :
    |Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      * Work.Spaces.w z| ≤ 6400000 * Kc * α * Work.Spaces.Gam α θ / z := by
  have hz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact Set.mem_Ici.mpr (by linarith)
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hzpos : 0 < z := by linarith
  have hi4 : i ≤ 4 := by omega
  set G0 : ℝ → ℝ := fun z => (1 : ℝ) - Work.Stability.chi (z / L) with hG0
  set G : ℝ → ℝ → ℝ := fun z _ => G0 z with hG
  set F : ℝ → ℝ → ℝ := Work.Construction.Fstar α with hF
  have hfun : Work.Stability.zfar L (Work.Construction.Fstar α) = fun z θ => G z θ * F z θ := by
    funext z θ
    rw [Work.Stability.zfar_apply]
  have hDth : Work.Spaces.DthIter i (Work.Stability.zfar L (Work.Construction.Fstar α))
      = fun z θ => G z θ * Work.Spaces.DthIter i F z θ := by
    rw [hfun]
    exact ZFBase.DthIter_mul_left_z i G0 F
  have hzfar : Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α))
      = Work.Spaces.DzIter j (fun z θ => G z θ * Work.Spaces.DthIter i F z θ) := by
    rw [Work.Spaces.mixed, hDth]
  have hleib := Work.FTS.LocData.DzIter_mul_smoothQuad j G
    (fun z θ => Work.Spaces.DthIter i F z θ) hz
    (ZFBase.contDiffOn_slice_oneSubChi L) (ZFBase.contDiffOn_slice_DthIter_Fstar α i θ)
  rw [hzfar, hleib]
  have hterm : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|
        * |Work.Spaces.w z|
        ≤ (j.choose b : ℝ) * (Kc * (400000 * α * Work.Spaces.Gam α θ / z)) := by
    intro b hb
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hb4 : b ≤ 4 := by omega
    have hjb4 : j - b ≤ 4 := le_trans (Nat.sub_le j b) (by omega)
    have hc0 : (0 : ℝ) ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
    have hA : |Work.Spaces.DzIter b G z θ| ≤ Kc := hKc L hL b hb4 z hz θ
    have hB : |Work.Spaces.mixed (j - b) i (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
        ≤ 400000 * α * Work.Spaces.Gam α θ / z :=
      ZFBase.mixed_Fstar_w_le α hα hα1 hjb4 hi4 hz1 hθ
    have hBw : |Work.Spaces.DzIter (j - b)
          (fun z θ => Work.Spaces.DthIter i F z θ) z θ| * |Work.Spaces.w z|
        ≤ 400000 * α * Work.Spaces.Gam α θ / z := by
      have hB' : |Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter i F) z θ * Work.Spaces.w z|
          ≤ 400000 * α * Work.Spaces.Gam α θ / z := hB
      simpa only [abs_mul] using hB'
    have heq : |(j.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|
        * |Work.Spaces.w z|
        = (j.choose b : ℝ) * (|Work.Spaces.DzIter b G z θ|
            * (|Work.Spaces.DzIter (j - b)
                (fun z θ => Work.Spaces.DthIter i F z θ) z θ| * |Work.Spaces.w z|)) := by
      simp only [abs_mul, abs_of_nonneg hc0]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hA hBw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (le_trans (by norm_num) hKc1)) hc0
  calc |(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Spaces.DzIter b G z θ
          * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ))
        * Work.Spaces.w z|
      = |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|
          * |Work.Spaces.w z| := by
        rw [abs_mul]
    _ ≤ (∑ b ∈ Finset.range (j + 1), |(j.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|)
          * |Work.Spaces.w z| :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ = ∑ b ∈ Finset.range (j + 1), |(j.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|
          * |Work.Spaces.w z| := by
        rw [Finset.sum_mul]
    _ ≤ ∑ b ∈ Finset.range (j + 1),
          (j.choose b : ℝ) * (Kc * (400000 * α * Work.Spaces.Gam α θ / z)) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ j * (Kc * (400000 * α * Work.Spaces.Gam α θ / z)) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ 6400000 * Kc * α * Work.Spaces.Gam α θ / z := by
        have h2j : (2 : ℝ) ^ j ≤ 16 := by
          calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 16 := by norm_num
        have hX : 0 ≤ Kc * (400000 * α * Work.Spaces.Gam α θ / z) := by positivity
        calc (2 : ℝ) ^ j * (Kc * (400000 * α * Work.Spaces.Gam α θ / z))
            ≤ 16 * (Kc * (400000 * α * Work.Spaces.Gam α θ / z)) :=
              mul_le_mul_of_nonneg_right h2j hX
          _ = 6400000 * Kc * α * Work.Spaces.Gam α θ / z := by ring

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocDataExt.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false

/-- Functions of the self-similar variables `(z,θ)`, curried. -/
abbrev Fn : Type := ℝ → ℝ → ℝ

/-! ## The two radial factors -/

/-- **The radial factor of the far part of the profile**:
`zfarR L z = (1 - χ(z/L))·FM.Fstar z`, so that the far part of the reference profile is

  `zfar L F_* = (α/c)·Γ(θ)·zfarR L z`

(`zfar_Fstar_eq`).  It vanishes for `z ≤ L` (`χ(z/L) = 1` there) and for `z ≥ 2L`
(`χ = 0` there), so it is a compactly supported `C^∞` function of `z`. -/
noncomputable def zfarR (L : ℝ) : ℝ → ℝ :=
  fun z => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z

@[simp] theorem zfarR_apply (L z : ℝ) :
    zfarR L z = (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z := rfl

/-- **The radial factor of the perturbation** `locG`:

  `locG α L β (hLoc α) = locR α L β (z)·Γ(θ)`,  `locR α L β z = -(α/c)·zfarR L z + β·bumpZ z`

where `bumpZ` is the radial factor `χ(4z-5)` of the bump `hLoc` (support `[3/4, 7/4]`). -/
noncomputable def locR (α L β : ℝ) : ℝ → ℝ :=
  fun z => -(α / Work.Spaces.c α) * zfarR L z + β * Work.FTS.LocData.bumpZ z

@[simp] theorem locR_apply (α L β z : ℝ) :
    locR α L β z = -(α / Work.Spaces.c α) * zfarR L z + β * Work.FTS.LocData.bumpZ z := rfl

/-! ## The factorisations -/

/-- **The far part is separable**: `zfar L F_* = (α/c)·Γ(θ)·zfarR L z`. -/
theorem zfar_Fstar_eq (α L : ℝ) :
    Work.Stability.zfar L (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α) * zfarR L z * Work.Spaces.Gam α θ := by
  funext z θ
  rw [Work.Stability.zfar_apply, zfarR_apply, Work.Construction.Fstar]
  ring

/-- **The perturbation is separable**: `locG α L β (hLoc α) = locR α L β (z)·Γ(θ)`. -/
theorem locG_eq_locR_Gam (α L β : ℝ) :
    Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)
      = fun z θ => locR α L β z * Work.Spaces.Gam α θ := by
  funext z θ
  rw [Work.FTS.LocData.locG_apply, Work.FTS.LocData.locData_apply,
    Work.FTS.LocData.hLoc_apply, locR_apply, zfarR_apply, Work.Construction.Fstar]
  ring

/-- `zfarR L` vanishes for `z ≤ L`. -/
theorem zfarR_eq_zero_of_le {L z : ℝ} (hL : 0 < L) (hz0 : 0 ≤ z) (hz : z ≤ L) :
    zfarR L z = 0 := by
  have h1 : |z / L| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hz0 (le_of_lt hL)), div_le_one hL]
    exact hz
  rw [zfarR_apply, Work.Stability.chi_eq_one h1]
  ring

/-- **`zfarR L` is the plain profile beyond the far scale**: for `z ≥ 2L` the cut-off factor is
`1`, so the far part agrees with `FM.Fstar` there. -/
theorem zfarR_eq_FM_Fstar_of_ge {L z : ℝ} (hL : 0 < L) (hz : 2 * L ≤ z) :
    zfarR L z = Work.FM.Fstar z := by
  have h1 : 2 ≤ |z / L| := by
    rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hL)), le_div_iff₀ hL]
    linarith
  rw [zfarR_apply, Work.Stability.chi_eq_zero h1]
  ring

/-- The radial bump `bumpZ` of the localised datum vanishes for `z ≤ 3/4`. -/
theorem bumpZ_eq_zero_of_le {z : ℝ} (hz : z ≤ 3 / 4) :
    Work.FTS.LocData.bumpZ z = 0 := by
  rw [Work.FTS.LocData.bumpZ_apply, Work.Stability.chi_eq_zero]
  have h2 : |4 * z - 5| = -(4 * z - 5) := abs_of_nonpos (by linarith)
  rw [h2]; linarith

/-- The radial bump `bumpZ` of the localised datum vanishes for `z ≥ 7/4`. -/
theorem bumpZ_eq_zero_of_ge {z : ℝ} (hz : 7 / 4 ≤ z) :
    Work.FTS.LocData.bumpZ z = 0 := by
  rw [Work.FTS.LocData.bumpZ_apply, Work.Stability.chi_eq_zero]
  have h2 : |4 * z - 5| = 4 * z - 5 := abs_of_nonneg (by linarith)
  rw [h2]; linarith

/-- **`locR` vanishes near the axis**: for `z ≤ min L (3/4)` both summands vanish. -/
theorem locR_eq_zero_of_le {α L β z : ℝ} (hL : 0 < L) (hz0 : 0 ≤ z) (hzL : z ≤ L)
    (hzb : z ≤ 3 / 4) : locR α L β z = 0 := by
  rw [locR_apply, zfarR_eq_zero_of_le hL hz0 hzL, mul_zero, bumpZ_eq_zero_of_le hzb,
    mul_zero, add_zero]

/-- Beyond the far scale the bump has died, so `locR` is the (rescaled) plain profile. -/
theorem locR_eq_of_ge {α L β z : ℝ} (hL : 0 < L) (hz : 2 * L ≤ z) (hzb : 7 / 4 ≤ z) :
    locR α L β z = -(α / Work.Spaces.c α) * Work.FM.Fstar z := by
  rw [locR_apply, zfarR_eq_FM_Fstar_of_ge hL hz, bumpZ_eq_zero_of_ge hzb, mul_zero, add_zero]

/-! ## Smoothness of the separable pieces -/

/-- A function of `z` alone which is `C^∞` on `(-1,∞)` is in the class `SmoothQuad` of the
localised-data chapter. -/
theorem smoothQuad_of_fstOn {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder f (Set.Ioi (-1))) :
    Work.FTS.LocData.SmoothQuad (fun z _ => f z) := by
  rw [Work.FTS.LocData.SmoothQuad]
  exact hf.comp contDiffOn_fst (fun p hp => hp.1)

/-- The angular factor `Γ` is `SmoothQuad`. -/
theorem smoothQuad_Gam (α : ℝ) :
    Work.FTS.LocData.SmoothQuad (fun _ θ => Work.Spaces.Gam α θ) :=
  Work.FTS.LocData.smoothQuad_of_snd (Work.FTS.LocData.contDiffOn_Gam_Ioo α)

/-- **A separable function `ρ(z)·Γ(θ)` is `SmoothQuad`** as soon as its radial factor is. -/
theorem smoothQuad_sepGam {ρ : ℝ → ℝ} {α : ℝ}
    (hρ : ContDiffOn ℝ Work.Stability.smoothOrder ρ (Set.Ioi (-1))) :
    Work.FTS.LocData.SmoothQuad (fun z θ => ρ z * Work.Spaces.Gam α θ) :=
  Work.FTS.LocData.smoothQuad_mul (smoothQuad_of_fstOn hρ) (smoothQuad_Gam α)

/-- The radial factor `zfarR L` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_zfarR (L : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (zfarR L) (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 1 - Work.Stability.chi (z / L)) (Set.Ioi (-1)) :=
    Work.FTS.LocData.ZFBase.contDiffOn_slice_oneSubChi L
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.FM.Fstar z)
      (Set.Ioi (-1)) := Work.FTS.LocData.ZFBase.contDiffOn_slice_FM_Fstar
  exact h1.mul h2

/-- The radial factor `locR α L β` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_locR (α L β : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (locR α L β) (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => -(α / Work.Spaces.c α) * zfarR L z) (Set.Ioi (-1)) :=
    ContDiffOn.const_smul (-(α / Work.Spaces.c α)) (contDiffOn_zfarR L)
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => β * Work.FTS.LocData.bumpZ z) (Set.Ioi (-1)) :=
    ContDiffOn.const_smul β (Work.FTS.LocData.contDiff_bumpZ.contDiffOn)
  refine (h1.add h2).congr (fun z _ => ?_)
  rw [locR_apply]


end Work.FTS.LocDataExt
end
end
