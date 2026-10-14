import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.DistEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap LineDeriv ContDiff

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The distributional form of the localized equation.**  This is the transcription of
`VT.localEquationLoc` (a pairing identity) into the shape required by `gain_step`. -/
theorem localEqDist {V G : E2 → ℂ} {W : Set E2}
    (hweak : ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Function.support ψ ⊆ W → ∫ x, V x * Kop ψ x = ∫ x, G x * ψ x)
    {χ χ' σ tt : E2 → ℂ} {U : Set E2}
    (hχc : HasCompactSupport χ) (hχs : ∀ n : ℕ, ContDiff ℝ n χ)
    (hχ'c : HasCompactSupport χ') (hχ's : ∀ n : ℕ, ContDiff ℝ n χ')
    (hσc : HasCompactSupport σ) (hσs : ∀ n : ℕ, ContDiff ℝ n σ)
    (httc : HasCompactSupport tt) (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (hU : IsOpen U) (htsU : tsupport χ ⊆ U) (hUsub : U ⊆ W)
    (hχ'1 : ∀ x ∈ U, χ' x = 1) (hσ1 : ∀ x ∈ U, σ x = 1)
    (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ))
    (hV : Integrable V) (hG : Integrable G)
    (hχV : Integrable (fun x => χ x * V x)) (hχ'V : Integrable (fun x => χ' x * V x))
    (hχG : Integrable (fun x => χ x * G x)) :
    Laplacian.laplacian (Td (fun x => χ x * V x) hχV)
      = (- Td (fun x => χ x * G x) hχG
          + TemperedDistribution.smulLeftCLM ℂ (rho0 χ tt)
              (Td (fun x => χ' x * V x) hχ'V)
          + TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d0 χ x)
              (LineDeriv.lineDerivOp e0 (Td (fun x => χ' x * V x) hχ'V))
          + TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d1 χ x)
              (LineDeriv.lineDerivOp e1 (Td (fun x => χ' x * V x) hχ'V)))
        + TemperedDistribution.smulLeftCLM ℂ (fun x => 5 * σ x)
            (LineDeriv.lineDerivOp e0 (Td (fun x => χ x * V x) hχV))
        + TemperedDistribution.smulLeftCLM ℂ (fun x => -(σ x * tt x))
            (LineDeriv.lineDerivOp e1 (Td (fun x => χ x * V x) hχV))
        + TemperedDistribution.smulLeftCLM ℂ (fun x => -6 * σ x)
            (Td (fun x => χ x * V x) hχV) := by
  have hpairA : Q0.Pair V χ (Td (fun x => χ x * V x) hχV) := fun ψ => Td_apply _ _ ψ
  have hpairA' : Q0.Pair V χ' (Td (fun x => χ' x * V x) hχ'V) := fun ψ => Td_apply _ _ ψ
  have hpairG : Q0.Pair G χ (Td (fun x => χ x * G x) hχG) := fun ψ => Td_apply _ _ ψ
  have hloc : Q0.LocalId V G χ χ' σ tt := by
    intro φ hφs hφc
    have hcoef : (⇑(hφc.toSchwartzMap (contDiff_infty.mpr hφs)) : E2 → ℂ) = φ :=
      funext (HasCompactSupport.toSchwartzMap_toFun hφc (contDiff_infty.mpr hφs))
    have h := localEquationLoc hweak hχc hχs hχ'c hχ's hσc hσs httc htts hU htsU hUsub
      hχ'1 hσ1 htt1 hV hG (hφc.toSchwartzMap (contDiff_infty.mpr hφs))
    rw [hcoef] at h
    exact h
  have hmain := Q0.distEq hpairA hpairA' hpairG hloc hχV hχ'V hχG hχc hχs hχ'c hχ's
    hσc hσs httc htts
  rw [hmain]
  have hσt : Function.HasTemperateGrowth σ := hasTemperateGrowth_of_cc hσc hσs
  have httt : Function.HasTemperateGrowth tt := hasTemperateGrowth_of_cc httc htts
  have hg1 : Function.HasTemperateGrowth (fun x => σ x * tt x) := hσt.mul httt
  have hg2 : Function.HasTemperateGrowth (fun x => 6 * σ x) :=
    (Function.HasTemperateGrowth.const (6 : ℂ)).mul hσt
  have hsm1 : TemperedDistribution.smulLeftCLM ℂ (fun x => -(σ x * tt x))
      (LineDeriv.lineDerivOp e1 (Td (fun x => χ x * V x) hχV))
      = -TemperedDistribution.smulLeftCLM ℂ (fun x => σ x * tt x)
        (LineDeriv.lineDerivOp e1 (Td (fun x => χ x * V x) hχV)) := by
    have h := TemperedDistribution.smulLeftCLM_neg (F := ℂ) hg1
    exact congrArg (fun L : 𝓢'(E2, ℂ) →L[ℂ] 𝓢'(E2, ℂ) =>
      L (LineDeriv.lineDerivOp e1 (Td (fun x => χ x * V x) hχV))) h
  have hsm2 : TemperedDistribution.smulLeftCLM ℂ (fun x => -6 * σ x)
      (Td (fun x => χ x * V x) hχV)
      = -TemperedDistribution.smulLeftCLM ℂ (fun x => 6 * σ x)
        (Td (fun x => χ x * V x) hχV) := by
    have hfun : (fun x : E2 => -6 * σ x) = (fun x : E2 => -(6 * σ x)) := by
      funext x
      rw [neg_mul]
    rw [hfun]
    have h := TemperedDistribution.smulLeftCLM_neg (F := ℂ) hg2
    exact congrArg (fun L : 𝓢'(E2, ℂ) →L[ℂ] 𝓢'(E2, ℂ) =>
      L (Td (fun x => χ x * V x) hχV)) h
  rw [hsm1, hsm2]
  have hρ : (fun x => d0 (d0 χ) x + d1 (d1 χ) x - 5 * d0 χ x + tt x * d1 χ x) = rho0 χ tt :=
    rfl
  rw [← hρ]
  abel

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.RegQAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Nonlin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Monotonicity in the order -/

/-- **`RegQ` descends in the order**: `RegQ α k f → l ≤ k → RegQ α l f`. -/
theorem regQ_mono {α : ℝ} {k l : ℕ} {f : ℝ → ℝ → ℝ} (hkl : l ≤ k)
    (hf : RegQ α k f) : RegQ α l f :=
  Work.FTS.GalerkinFix.RegQ.regQ_mono hf hkl

/-! ## Scalar homogeneity of the iterated operators (unconditional) -/

private theorem deriv_const_mul' (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul']

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul']

private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih, Dz_const_mul]

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih, Dth_const_mul]

/-- **The mixed operators are scalar homogeneous** (unconditionally). -/
theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## Additivity of the iterated operators on the open quadrant (`SmoothQuad` data) -/

private lemma DzIter_congr_quad {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, -1 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n F z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

private lemma DthIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => a z θ + b z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n a z θ') θ :=
        ha.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        hb.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd : deriv (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n a z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

private lemma DzIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DzIter j a z θ + Work.Spaces.DzIter j b z θ := by
  induction j with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => a z θ + b z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n a z' θ) z :=
        ha.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        hb.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd : deriv (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n a z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- **The mixed operators `D_z^jD_θ^i` are additive on the open quadrant** for `SmoothQuad`
data. -/
theorem mixed_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (j i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.mixed j i a z θ + Work.Spaces.mixed j i b z θ := by
  intro z θ hz h1 h2
  have hcongr := DzIter_congr_quad (j := j)
    (F := Work.Spaces.DthIter i (fun z θ => a z θ + b z θ))
    (G := fun z θ => Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ)
    (fun z θ hz h1 h2 => DthIter_add_quad ha hb i z θ hz h1 h2) z θ hz h1 h2
  have hadd := DzIter_add_quad (ha.DthIter i) (hb.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## `RegQ` is closed under multiplication by a constant -/

private theorem bdryTraces_smul {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (htr : BdryTraces α k f) : BdryTraces α k (fun z θ => c * f z θ) := by
  intro a b hab
  have hfab := htr a b hab
  have hfun : ∀ z θ, Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed b a f z θ := by
    intro z θ
    rw [mixed_const_mul]
  have hz : ∀ θ, (fun z => z * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ
        * Work.Spaces.w z) ^ 2)
      = fun z => c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) := by
    intro θ
    funext z
    show z * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ * Work.Spaces.w z) ^ 2
      = c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
    rw [hfun z θ]; ring
  have ht : ∀ z, (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2)
      = fun θ => c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    intro z
    funext θ
    show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2
      = c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2)
    rw [hfun z θ]; ring
  constructor
  · intro θ hθ
    have h := hfab.1 θ hθ
    constructor
    · rw [hz θ]
      simpa using h.1.const_mul (c ^ 2)
    · rw [hz θ]
      simpa using h.2.const_mul (c ^ 2)
  · intro z hzmem
    have h := hfab.2 z hzmem
    constructor
    · rw [ht z]
      simpa using h.1.const_mul (c ^ 2)
    · rw [ht z]
      simpa using h.2.const_mul (c ^ 2)

/-- **`RegQ` is closed under multiplication by a constant.** -/
theorem regQ_smul {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) : RegQ α k (fun z θ => c * f z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_const_mul c hf.1,
    Work.FTS.LocData.HkMem_const_mul α k c hf.2.1, bdryTraces_smul c hf.2.2⟩

/-! ## `RegQ` is closed under addition -/

/-- `SmoothQuad` data is `SmoothOpen` (the open quadrant is contained in the half-strip of
`SmoothQuad`). -/
private theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) : Work.FTS.EllipticEst.SmoothOpen f := by
  refine hf.mono ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp1]), hp2⟩

/-- **`ℋ^k` is closed under addition** for `SmoothOpen` data (the `α`-generic version, with the
domination of `HkIntegrand_add_le_open`). -/
theorem HkMem_add_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  have hfg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hf hg
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (hfg.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · have htarget : MeasureTheory.IntegrableOn
        (fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
        Work.Spaces.Iz :=
      (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
    refine MeasureTheory.Integrable.congr htarget ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    exact Work.FTS.EllipticEst.HkIntegrand_add_le_open α k hf hg hz hθ

/-- Additivity of `BdryTraces`: by `mixed_add_quad` the boundary limits of the sum are those
of the sum of the limits, and `z ≥ 0` resp. `sin(2θ)^{1-γ} ≥ 0` let the squeeze theorem
conclude. -/
theorem bdryTraces_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (htf : BdryTraces α k f) (htg : BdryTraces α k g) :
    BdryTraces α k (fun z θ => f z θ + g z θ) := by
  intro a b hab
  have hfab := htf a b hab
  have hgab := htg a b hab
  have hpt : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ :=
    fun z θ hz h1 h2 => mixed_add_quad hsmf hsmg b a z θ (by linarith) h1 h2
  have hwsq : ∀ z θ, (Work.Spaces.w z
        * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ)) ^ 2
      ≤ 2 * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2
        + 2 * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2 := by
    intro z θ
    nlinarith [sq_nonneg (Work.Spaces.w z * Work.Spaces.mixed b a f z θ
        - Work.Spaces.w z * Work.Spaces.mixed b a g z θ)]
  have hssq : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) → (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α))
        * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ) ^ 2
      ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2)
        + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2) := by
    intro z θ hθ
    have h1 : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _
    nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ), h1]
  constructor
  · intro θ hθ
    have hA := hfab.1 θ hθ
    have hB := hgab.1 θ hθ
    have hlim : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hA.1.const_mul 2).add (hB.1.const_mul 2)
    have hlimT : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) atTop (𝓝 0) := by
      simpa using (hA.2.const_mul 2).add (hB.2.const_mul 2)
    have hsq : Tendsto (fun z => z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
          * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hzmem
        show 0 ≤ z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
        rw [hpt z θ (Set.mem_Ioi.mp hzmem) hθ.1 hθ.2]
        exact mul_nonneg (le_of_lt (Set.mem_Ioi.mp hzmem)) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with z hzmem
        show z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
          ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        rw [hpt z θ (Set.mem_Ioi.mp hzmem) hθ.1 hθ.2]
        nlinarith [hwsq z θ, le_of_lt (Set.mem_Ioi.mp hzmem)]
    have hsqT : Tendsto (fun z => z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
          * Work.Spaces.w z) ^ 2) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimT ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hzmem
        show 0 ≤ z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (le_of_lt hzmem) (sq_nonneg _)
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hzmem
        show z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
          ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        nlinarith [hwsq z θ, le_of_lt hzmem]
    exact ⟨hsq, hsqT⟩
  · intro z hzmem
    have hA := hfab.2 z hzmem
    have hB := hgab.2 z hzmem
    have hlim : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2) + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hA.1.const_mul 2).add (hB.1.const_mul 2)
    have hlimL : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2) + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
      simpa using (hA.2.const_mul 2).add (hB.2.const_mul 2)
    have hmemGT : Set.Ioo 0 (π / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
    have hmemLT : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) := Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
    have hsq : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [hmemGT] with θ hθ
        show 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _) (sq_nonneg _)
      · filter_upwards [hmemGT] with θ hθ
        show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
          ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact hssq z θ hθ
    have hsqL : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2)
        (𝓝[<] (π / 2)) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimL ?_ ?_
      · filter_upwards [hmemLT] with θ hθ
        show 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _) (sq_nonneg _)
      · filter_upwards [hmemLT] with θ hθ
        show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
          ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact hssq z θ hθ
    exact ⟨hsq, hsqL⟩

/-- **`RegQ` is closed under addition.** -/
theorem regQ_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_add hf.1 hg.1,
    HkMem_add_open α k
      (smoothOpen_of_smoothQuad hf.1)
      (smoothOpen_of_smoothQuad hg.1) hf.2.1 hg.2.1,
    bdryTraces_add hf.1 hg.1 hf.2.2 hg.2.2⟩

/-! ## Derived closure properties -/

/-- `RegQ` contains the zero profile. -/
theorem regQ_zero (α : ℝ) (k : ℕ) : RegQ α k (fun _ _ : ℝ => (0 : ℝ)) := by
  have hsm : Work.FTS.LocData.SmoothQuad (fun _ _ : ℝ => (0 : ℝ)) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ × ℝ => (0 : ℝ)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
    exact contDiffOn_const
  refine ⟨hsm, Work.FTS.EllipticEst.HkMem_zero α k, ?_⟩
  intro a b _
  have hmix : Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
    have h := mixed_const_mul (0 : ℝ) (fun _ _ : ℝ => (1 : ℝ)) b a
    simpa using h
  have hmix_pt : ∀ z θ : ℝ, Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
    fun z θ => congrFun (congrFun hmix z) θ
  constructor
  · intro θ _
    have hz : (fun z => z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ
        * Work.Spaces.w z) ^ 2) = fun _ => (0 : ℝ) := by
      funext z
      show z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ * Work.Spaces.w z) ^ 2 = 0
      rw [hmix_pt z θ]; ring
    rw [hz]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  · intro z _
    have ht : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ
      show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2 = 0
      rw [hmix_pt z θ]; ring
    rw [ht]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

/-- `RegQ` is closed under negation. -/
theorem regQ_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hf : RegQ α k f) :
    RegQ α k (fun z θ => -f z θ) := by
  have h := regQ_smul (α := α) (k := k) (-1) hf
  simpa using h

/-- `RegQ` is closed under subtraction. -/
theorem regQ_sub {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ - g z θ) := by
  have h := regQ_add hf (regQ_neg hg)
  simpa [sub_eq_add_neg] using h

/-- `RegQ` is closed under finite linear combinations. -/
theorem regQ_finset_sum {α : ℝ} {k : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (F : ι → ℝ → ℝ → ℝ) (hF : ∀ i ∈ s, RegQ α k (F i)) :
    RegQ α k (fun z θ => ∑ i ∈ s, c i * F i z θ) := by
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ; simp
      rw [h0]
      exact regQ_zero α k
  | insert a s' ha ih =>
      have hsum : (fun z θ => ∑ i ∈ insert a s', c i * F i z θ)
          = (fun z θ => c a * F a z θ) + (fun z θ => ∑ i ∈ s', c i * F i z θ) := by
        funext z θ
        rw [Finset.sum_insert ha]; rfl
      rw [hsum]
      refine regQ_add (regQ_smul (c a) (hF a (Finset.mem_insert_self a s')))
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Step =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-- **The analytic clauses of a level-`n` coercive inner product**, in the interior class
`RegQ α n`: Cauchy–Schwarz with constant `CC`, comparability with constants `cc`, `CC`, and
coercivity of the clean operator `Lhat = 𝓛 − Transport` with constant `cc`. -/
structure CoerData (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity/comparability constant is positive. -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz/comparability constant is positive. -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ` norm. -/
  cs : ∀ f g : Fn, RegQ α n f → RegQ α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- lower comparability. -/
  lo : ∀ f : Fn, RegQ α n f → cc * Work.Spaces.HkSq α n f ≤ IP f f
  /-- upper comparability. -/
  up : ∀ f : Fn, RegQ α n f → IP f f ≤ CC * Work.Spaces.HkSq α n f
  /-- **coercivity of the clean operator `Lhat`**. -/
  coer : ∀ f : Fn, RegQ α n f → cc * Work.Spaces.HkSq α n f ≤ IP (Lhat f) f

/-- The smallness of the step coefficients, in the form produced by the paper's choice
(`c_{1,k}` arbitrary, `c_{2,k}` of the order `c_{1,k}/(C̄_k/cc)²`).  It constrains only the
*coefficients*, never the relation between the constants `cc`, `CC`, `κ`. -/
def StepSmall (cc CC κ c₁ c₂ : ℝ) : Prop :=
  c₂ * (CC * κ) ^ 2 ≤ cc ^ 2 / 4 ∧ c₂ * (CC * κ) ^ 2 ≤ c₁ * cc ^ 2 / 4

/-- **The coefficient smallness is satisfiable for every positive coercivity constant.**
This is the precise sense in which the paper's choice of *small* step coefficients replaces
the balance hypothesis of the delivered step: `StepSmall` can always be met by taking `c₂`
small, whatever the values of `cc`, `CC`, `κ`. -/
theorem exists_small_step_coeffs {cc CC κ c₁ : ℝ} (hcc : 0 < cc) (hCC : 0 < CC)
    (hc₁ : 0 < c₁) (hκ : 0 ≤ κ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ StepSmall cc CC κ c₁ c₂ := by
  rcases eq_or_lt_of_le hκ with hκ0 | hκ0
  · refine ⟨1, one_pos, ?_, ?_⟩
    · rw [← hκ0]; norm_num
      nlinarith [hcc]
    · rw [← hκ0]; norm_num
      nlinarith [hcc, hc₁]
  · have hpos : 0 < (CC * κ) ^ 2 := by positivity
    have hCCκ : 0 < CC * κ := mul_pos hCC hκ0
    set m := min (cc ^ 2 / 4) (c₁ * cc ^ 2 / 4) with hm
    have hm0 : 0 < m := lt_min (div_pos (pow_pos hcc 2) (by norm_num))
      (div_pos (mul_pos hc₁ (pow_pos hcc 2)) (by norm_num))
    have hden : (0:ℝ) < 2 * (CC * κ) ^ 2 := by nlinarith [hpos]
    refine ⟨m / (2 * (CC * κ) ^ 2), ?_, ?_, ?_⟩
    · exact div_pos hm0 hden
    · have hle : m ≤ cc ^ 2 / 4 := min_le_left _ _
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (CC * κ) ^ 2)]
      nlinarith [hle, hpos]
    · have hle : m ≤ c₁ * cc ^ 2 / 4 := min_le_right _ _
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (CC * κ) ^ 2)]
      nlinarith [hle, hpos]


end Work.FTS.CoercivityFix
end
end
-- ===== merged: Submission.Work.FTS.H2.WtoHQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace DthAux

/-- The angular weight `sin(2θ)^{-α/5}/(α + sin 2θ)` of the `𝒲^{l,∞}`-norm. -/
noncomputable def Wt (α θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))

lemma Wt_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wt α θ :=
  Work.Spaces.gamma_weight_nonneg α θ hα hθ

lemma alpha_Gam_Wt_le_one {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := by
  rw [Wt, ← mul_div_assoc]
  exact Work.Spaces.Gam_mul_weight_le α θ hα hθ

lemma sin_sq_Gam_Wt_le_one {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ π/2 := hθ.2
  set s := Real.sin (2*θ) with hs
  have hs0 : 0 ≤ s := by
    rw [hs, Real.sin_two_mul]
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
    have h2 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
    positivity
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hA : Work.Spaces.Gam α θ * (Real.sin (2*θ)) ^ (-(α / 5)) ≤ 1 :=
    GamSinRpowMulLeOne hα hα1 hθ
  have hden : 0 < α + s := by linarith
  have hnum : s^2 * (Work.Spaces.Gam α θ * (Real.sin (2*θ)) ^ (-(α / 5))) ≤ s^2 * 1 :=
    mul_le_mul_of_nonneg_left hA (sq_nonneg s)
  have hss : s^2 ≤ 1 := by
    rw [hs]
    have := Real.abs_sin_le_one (2*θ)
    nlinarith [sq_abs (Real.sin (2*θ)), abs_nonneg (Real.sin (2*θ))]
  have hkey : s^2 * Work.Spaces.Gam α θ * Wt α θ
      = s^2 * (Work.Spaces.Gam α θ * (Real.sin (2*θ)) ^ (-(α / 5))) / (α + s) := by
    rw [Wt, hs]
    ring
  rw [hkey, div_le_one hden]
  nlinarith [hnum, hss, hs0]

lemma abs_qfun_le (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 4/3 := by
  rw [Work.Spaces.qfun]
  have h1 := Real.abs_cos_le_one (2*θ)
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C^∞` on the open interval `(0,π/2)`. -/
lemma contDiffOn_Gam_Ioo' (α : ℝ) :
    ContDiffOn ℝ ⊤ (fun θ => Work.Spaces.Gam α θ) (Set.Ioo 0 (π/2)) := by
  show ContDiffOn ℝ ⊤ (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
    (Set.Ioo 0 (π / 2))
  have hbase : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).mul ((Real.contDiff_cos.contDiffOn).pow 2)
  refine hbase.rpow_const_of_ne (fun θ hθ => ?_)
  have h1 : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-! ## Locality of `dthU^m` and the Leibniz rule on the open interval -/

lemma dthU_iter_congr_open {U : Set ℝ} (hU : IsOpen U) :
    ∀ (m : ℕ) (f g : ℝ → ℝ), Set.EqOn f g U →
      Set.EqOn (Work.Spaces.dthU^[m] f) (Work.Spaces.dthU^[m] g) U := by
  intro m
  induction m with
  | zero => intro f g h; exact h
  | succ m ih =>
      intro f g h
      have hd : Set.EqOn (Work.Spaces.dthU f) (Work.Spaces.dthU g) U := by
        intro θ hθ
        rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply]
        congr 1
        exact Filter.EventuallyEq.deriv_eq (h.eventuallyEq_of_mem (hU.mem_nhds hθ))
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih _ _ hd

lemma DthIter_rad (a : ℕ) (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter a (fun _ θ => f θ) z θ = Work.Spaces.dthU^[a] f θ := by
  have h := Work.Spaces.DthIter_decomp a f (fun _ : ℝ => (1:ℝ)) z θ
  simpa using h

lemma dthU_iter_mul_Ioo (m : ℕ) (f g : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2))
    (hf : ContDiffOn ℝ ⊤ f (Set.Ioo 0 (π/2))) (hg : ContDiffOn ℝ ⊤ g (Set.Ioo 0 (π/2))) :
    Work.Spaces.dthU^[m] (f * g) θ =
      ∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
        (Work.Spaces.dthU^[a] f θ * Work.Spaces.dthU^[m-a] g θ) := by
  have h := Work.Spaces.DthIter_mul m (fun _ θ => f θ) (fun _ θ => g θ) 0 (Set.Ioo 0 (π/2))
    isOpen_Ioo (by simpa using hf) (by simpa using hg) θ hθ
  have hfun : (fun (z : ℝ) (θ : ℝ) => f θ * g θ) = (fun (_ : ℝ) (θ : ℝ) => (f * g) θ) := rfl
  rw [hfun] at h
  simp only [DthIter_rad] at h
  exact h

lemma hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(Real.sin (2 * θ)) * 2) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_cos (2 * θ)).comp θ h2
  simpa [Function.comp_def] using h

lemma dthU_comp_cos (P : ℝ → ℝ) (θ : ℝ) (hP : DifferentiableAt ℝ P (Real.cos (2*θ))) :
    Work.Spaces.dthU (fun t => P (Real.cos (2*t))) θ
      = -2 * (1 - (Real.cos (2*θ))^2) * deriv P (Real.cos (2*θ)) := by
  rw [Work.Spaces.dthU_apply]
  have hcos := hasDerivAt_cos_two θ
  have hcomp : HasDerivAt (fun t : ℝ => P (Real.cos (2*t)))
      (deriv P (Real.cos (2*θ)) * (-(Real.sin (2*θ)) * 2)) θ := by
    have h := hP.hasDerivAt.comp θ hcos
    simpa [Function.comp_def] using h
  rw [hcomp.deriv]
  have hs : (Real.sin (2*θ))^2 = 1 - (Real.cos (2*θ))^2 := by
    have := Real.sin_sq_add_cos_sq (2*θ); linarith
  linear_combination (-2 * deriv P (Real.cos (2*θ))) * hs

lemma deriv_poly2 (c : ℝ) : deriv (fun c : ℝ => -2*(1-c^2)) c = 4*c := by
  have h : HasDerivAt (fun c : ℝ => -2*(1-c^2)) (4*c) c := by
    have h1 : HasDerivAt (fun c : ℝ => (1:ℝ) - c^2) (-(2*c)) c := by
      have hp : HasDerivAt (fun c : ℝ => c^2) (2*c^(2-1)) c := hasDerivAt_pow 2 c
      have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 c := hasDerivAt_const c 1
      have := hc.sub hp
      convert this using 1 <;> ring
    have h2 := h1.const_mul (-2:ℝ)
    convert h2 using 1 <;> ring
  exact h.deriv

lemma deriv_poly3 (c : ℝ) : deriv (fun c : ℝ => -8*c*(1-c^2)) c = -8 + 24*c^2 := by
  have h : HasDerivAt (fun c : ℝ => -8*c*(1-c^2)) (-8 + 24*c^2) c := by
    have h1 : HasDerivAt (fun c : ℝ => (1:ℝ) - c^2) (-(2*c)) c := by
      have hp : HasDerivAt (fun c : ℝ => c^2) (2*c^(2-1)) c := hasDerivAt_pow 2 c
      have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 c := hasDerivAt_const c 1
      have := hc.sub hp
      convert this using 1 <;> ring
    have ha : HasDerivAt (fun c : ℝ => -8*c) (-8) c := by
      have := (hasDerivAt_id c).const_mul (-8:ℝ)
      simpa using this
    have h2 := ha.mul h1
    convert h2 using 1 <;> ring
  exact h.deriv

lemma deriv_poly4 (c : ℝ) :
    deriv (fun c : ℝ => 16*(1-c^2)*(1-3*c^2)) c = 16*(-8*c + 12*c^3) := by
  have h : HasDerivAt (fun c : ℝ => 16*(1-c^2)*(1-3*c^2)) (16*(-8*c + 12*c^3)) c := by
    have h1 : HasDerivAt (fun c : ℝ => (1:ℝ) - c^2) (-(2*c)) c := by
      have hp : HasDerivAt (fun c : ℝ => c^2) (2*c^(2-1)) c := hasDerivAt_pow 2 c
      have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 c := hasDerivAt_const c 1
      have := hc.sub hp
      convert this using 1 <;> ring
    have h3 : HasDerivAt (fun c : ℝ => (1:ℝ) - 3*c^2) (-(6*c)) c := by
      have hp : HasDerivAt (fun c : ℝ => 3*c^2) (3*(2*c^(2-1))) c :=
        (hasDerivAt_pow 2 c).const_mul 3
      have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 c := hasDerivAt_const c 1
      have := hc.sub hp
      convert this using 1 <;> ring
    have ha : HasDerivAt (fun c : ℝ => 16*(1-c^2)) (16 * (-(2*c))) c := h1.const_mul 16
    have h2 := ha.mul h3
    convert h2 using 1 <;> ring
  exact h.deriv

-- the four iterates of qfun
lemma dthU_qfun_eq (θ : ℝ) :
    Work.Spaces.dthU Work.Spaces.qfun θ = -2 * (Real.sin (2*θ))^2 := by
  rw [Work.Spaces.dthU_apply]
  have h : HasDerivAt (fun θ' : ℝ => Work.Spaces.qfun θ') (-(Real.sin (2*θ) * 2)) θ := by
    have := (hasDerivAt_cos_two θ).sub_const (1/3 : ℝ)
    simpa [Work.Spaces.qfun, Function.comp_def] using this
  rw [h.deriv]
  ring

lemma dthU_qfun_eq2 (θ : ℝ) :
    Work.Spaces.dthU^[2] Work.Spaces.qfun θ
      = -8 * (Real.sin (2*θ))^2 * Real.cos (2*θ) := by
  have h1 : Work.Spaces.dthU Work.Spaces.qfun
      = fun θ' => -2*(1 - (Real.cos (2*θ'))^2) := by
    funext θ'
    rw [dthU_qfun_eq θ']
    have hs : (Real.sin (2*θ'))^2 = 1 - (Real.cos (2*θ'))^2 := by
      have := Real.sin_sq_add_cos_sq (2*θ'); linarith
    rw [hs]
  rw [show Work.Spaces.dthU^[2] Work.Spaces.qfun
      = Work.Spaces.dthU (Work.Spaces.dthU Work.Spaces.qfun) from rfl, h1]
  rw [dthU_comp_cos (fun c : ℝ => -2*(1-c^2)) θ (by fun_prop)]
  rw [deriv_poly2]
  have hs : (Real.sin (2*θ))^2 = 1 - (Real.cos (2*θ))^2 := by
    have := Real.sin_sq_add_cos_sq (2*θ); linarith
  rw [hs]; ring

lemma dthU_qfun_eq3 (θ : ℝ) :
    Work.Spaces.dthU^[3] Work.Spaces.qfun θ
      = 16*(1-(Real.cos (2*θ))^2)*(1-3*(Real.cos (2*θ))^2) := by
  have h1 : Work.Spaces.dthU^[2] Work.Spaces.qfun
      = fun θ' => -8*(Real.cos (2*θ'))*(1 - (Real.cos (2*θ'))^2) := by
    funext θ'
    rw [dthU_qfun_eq2 θ']
    have hs : (Real.sin (2*θ'))^2 = 1 - (Real.cos (2*θ'))^2 := by
      have := Real.sin_sq_add_cos_sq (2*θ'); linarith
    rw [hs]; ring
  rw [show Work.Spaces.dthU^[3] Work.Spaces.qfun
      = Work.Spaces.dthU (Work.Spaces.dthU^[2] Work.Spaces.qfun) from rfl, h1]
  rw [dthU_comp_cos (fun c : ℝ => -8*c*(1-c^2)) θ (by fun_prop)]
  rw [deriv_poly3]
  ring

lemma dthU_qfun_eq4 (θ : ℝ) :
    Work.Spaces.dthU^[4] Work.Spaces.qfun θ
      = 128*(Real.cos (2*θ))*(1-(Real.cos (2*θ))^2)*(2-3*(Real.cos (2*θ))^2) := by
  have h1 : Work.Spaces.dthU^[3] Work.Spaces.qfun
      = fun θ' => 16*(1 - (Real.cos (2*θ'))^2)*(1 - 3*(Real.cos (2*θ'))^2) :=
    funext (fun θ' => dthU_qfun_eq3 θ')
  rw [show Work.Spaces.dthU^[4] Work.Spaces.qfun
      = Work.Spaces.dthU (Work.Spaces.dthU^[3] Work.Spaces.qfun) from rfl, h1]
  rw [dthU_comp_cos (fun c : ℝ => 16*(1-c^2)*(1-3*c^2)) θ (by fun_prop)]
  rw [deriv_poly4]
  ring

lemma sin_sq_two (θ : ℝ) : 1 - (Real.cos (2*θ))^2 = (Real.sin (2*θ))^2 := by
  have := Real.sin_sq_add_cos_sq (2*θ); linarith

lemma DthQfunBound {i : ℕ} (hi : 1 ≤ i) (hi4 : i ≤ 4) (θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[i] Work.Spaces.qfun θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  have hs : 0 ≤ (Real.sin (2*θ))^2 := sq_nonneg _
  have hc : |Real.cos (2*θ)| ≤ 1 := Real.abs_cos_le_one _
  have hc2 : (Real.cos (2*θ))^2 ≤ 1 := by
    nlinarith [hc, sq_abs (Real.cos (2*θ)), abs_nonneg (Real.cos (2*θ))]
  have h4 : |1 - 3*(Real.cos (2*θ))^2| ≤ 4 := by
    rw [abs_le]
    constructor <;> nlinarith [hc2, sq_nonneg (Real.cos (2*θ))]
  have h5 : |2 - 3*(Real.cos (2*θ))^2| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith [hc2, sq_nonneg (Real.cos (2*θ))]
  interval_cases i
  · rw [Function.iterate_one, dthU_qfun_eq]
    rw [show |(-2:ℝ) * (Real.sin (2*θ))^2| = 2 * (Real.sin (2*θ))^2 by
      rw [abs_mul, show |(-2:ℝ)| = 2 by norm_num, abs_of_nonneg hs]]
    nlinarith
  · rw [dthU_qfun_eq2]
    rw [abs_mul, abs_mul, show |(-8:ℝ)| = 8 by norm_num, abs_of_nonneg hs]
    have := mul_le_of_le_one_right (by positivity : (0:ℝ) ≤ 8 * (Real.sin (2*θ))^2) hc
    linarith
  · rw [dthU_qfun_eq3, sin_sq_two θ]
    rw [abs_mul, abs_mul, show |(16:ℝ)| = 16 by norm_num, abs_of_nonneg hs]
    nlinarith [h4, hs]
  · rw [dthU_qfun_eq4, sin_sq_two θ]
    rw [abs_mul, abs_mul, abs_mul, show |(128:ℝ)| = 128 by norm_num, abs_of_nonneg hs]
    have hstep : |Real.cos (2*θ)| * (Real.sin (2*θ))^2 * |2 - 3*(Real.cos (2*θ))^2|
        ≤ 5 * (Real.sin (2*θ))^2 := by
      have h1 : |Real.cos (2*θ)| * (Real.sin (2*θ))^2 ≤ 1 * (Real.sin (2*θ))^2 :=
        mul_le_mul_of_nonneg_right hc hs
      have h2 : |Real.cos (2*θ)| * (Real.sin (2*θ))^2 * |2 - 3*(Real.cos (2*θ))^2|
          ≤ (1 * (Real.sin (2*θ))^2) * 5 :=
        mul_le_mul h1 h5 (abs_nonneg _) (by positivity)
      linarith
    nlinarith [hstep, hs]



/-! ## The constant bookkeeping -/

/-- `TM m` dominates every `tBound j 0`, `j < m`. -/
noncomputable def TM (m : ℕ) : ℝ := (∑ j ∈ Finset.range m, Work.Spaces.tBound j 0) + 1

lemma TM_pos (m : ℕ) : 0 < TM m := by
  rw [TM]
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range m) => Work.Spaces.tBound_nonneg j 0)
  linarith


lemma tBound_le_TM {j m : ℕ} (hj : j < m) : Work.Spaces.tBound j 0 ≤ TM m := by
  rw [TM]
  have h : Work.Spaces.tBound j 0 ≤ ∑ k ∈ Finset.range m, Work.Spaces.tBound k 0 :=
    Finset.single_le_sum (fun k _ => Work.Spaces.tBound_nonneg k 0) (Finset.mem_range.mpr hj)
  linarith

/-- The uniform bound for a single summand of the Leibniz expansion. -/
noncomputable def CM (m : ℕ) (K : ℝ) : ℝ :=
  (2:ℝ)^m * ((4/3)*K + 1000*TM m + 1000)

/-- The constant for index `m+1` given the bound `K` at index `m`. -/
noncomputable def Bstep (m : ℕ) (K : ℝ) : ℝ := ((m:ℝ)+1) * CM m K

lemma Bstep_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K) : 0 ≤ Bstep m K := by
  rw [Bstep, CM]
  have h1 : 0 ≤ (4/3)*K + 1000*TM m + 1000 := by
    have := TM_pos m
    linarith
  positivity

/-! ## The main weighted estimate -/

/-- `Good m K` asserts the weighted bound for all orders `2 ≤ m' ≤ m`. -/
def Good (m : ℕ) (K : ℝ) : Prop :=
  ∀ m' : ℕ, 2 ≤ m' → m' ≤ m → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[m'] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α

/-- The bound for a single summand of the Leibniz expansion. -/
lemma summand_le (m : ℕ) (hm : 2 ≤ m) (hm4 : m ≤ 4) {K : ℝ} (hK0 : 0 ≤ K)
    (hKm : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {a : ℕ} (ha : a ≤ m) :
    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
        Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
      ≤ (4/3)*K + 1000*TM m + 1000 := by
  have hW : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    simp only [Function.iterate_zero_apply, Nat.sub_zero]
    have hIH := hKm α hα hα1 θ hθ
    have hq := abs_qfun_le θ
    have hstep : |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ) ≤ (4/3) * (K * α) := by
      have h1 : |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
            * Wt α θ)
          ≤ (4/3) * (K * α) := by
        have := mul_le_mul hq hIH (mul_nonneg (abs_nonneg _) hW) (by norm_num)
        linarith [this]
      exact h1
    have h2 : (4/3) * (K * α) ≤ (4/3) * K := by
      nlinarith [hK0, hα, hα1]
    have h3 : (0:ℝ) ≤ 1000*TM m + 1000 := by
      have := TM_pos m; linarith
    calc |Work.Spaces.qfun θ * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
        = |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
            * Wt α θ) := by rw [abs_mul]; ring
      _ ≤ (4/3) * K := le_trans hstep h2
      _ ≤ (4/3)*K + 1000*TM m + 1000 := by linarith
  · rcases eq_or_lt_of_le ha with ham | ham
    · -- `a = m`
      have ham2 : a = m := ham
      rw [ham2]
      simp only [Nat.sub_self, Function.iterate_zero_apply]
      have hB := DthQfunBound (i := m) (by omega) hm4 θ hθ
      have hs := sin_sq_Gam_Wt_le_one hα hα1 hθ
      have hs0 : 0 ≤ (Real.sin (2*θ))^2 := sq_nonneg _
      have h1 : |Work.Spaces.dthU^[m] Work.Spaces.qfun θ * Work.Spaces.Gam α θ| * Wt α θ
          ≤ 1000 * ((Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ) := by
        rw [abs_mul]
        have h2 : |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| ≤ 1000 * (Real.sin (2*θ))^2 := hB
        have h3 : 0 ≤ 1000 * (Real.sin (2*θ))^2 := by positivity
        calc |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| * |Work.Spaces.Gam α θ| * Wt α θ
            ≤ (1000 * (Real.sin (2*θ))^2) * |Work.Spaces.Gam α θ| * Wt α θ := by
              apply mul_le_mul_of_nonneg_right _ hW
              exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
          _ = 1000 * ((Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ) := by
              rw [abs_of_nonneg hG0]; ring
      have h4 : 1000 * ((Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ) ≤ 1000 := by
        nlinarith [hs]
      have h5 : (0:ℝ) ≤ (4/3)*K + 1000*TM m := by
        have := TM_pos m
        nlinarith [hK0]
      linarith [h1, h4, h5]
    · -- `1 ≤ a ≤ m-1`
      have ha1 : 1 ≤ a := hapos
      have ham' : a ≤ m - 1 := by omega
      have hm1 : 1 ≤ m - a := by omega
      have hB := DthQfunBound (i := a) ha1 (by omega) θ hθ
      have hCrude := Work.Spaces.dthU_Gam_le (m-a) hm1 α hα hα1 θ hθ
      have htB : Work.Spaces.tBound (m - a - 1) 0 ≤ TM m := tBound_le_TM (by omega)
      have hs0 : 0 ≤ (Real.sin (2*θ))^2 := sq_nonneg _
      have hkey : |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
            Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
          ≤ 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ)
            * (Real.sin (2*θ))^2 := by
        rw [abs_mul]
        have h2 : |Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ|
            ≤ α * Work.Spaces.tBound (m - a - 1) 0 * Work.Spaces.Gam α θ := hCrude
        have h3 : 0 ≤ α * Work.Spaces.tBound (m - a - 1) 0 * Work.Spaces.Gam α θ :=
          mul_nonneg (mul_nonneg (le_of_lt hα) (Work.Spaces.tBound_nonneg _ _)) hG0
        calc |Work.Spaces.dthU^[a] Work.Spaces.qfun θ| *
              |Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
            ≤ (1000 * (Real.sin (2*θ))^2) *
              (α * Work.Spaces.tBound (m - a - 1) 0 * Work.Spaces.Gam α θ) * Wt α θ := by
              apply mul_le_mul_of_nonneg_right _ hW
              exact mul_le_mul hB h2 (abs_nonneg _) (by positivity)
          _ = 1000 * (Work.Spaces.tBound (m - a - 1) 0)
                * (α * Work.Spaces.Gam α θ * Wt α θ) * (Real.sin (2*θ))^2 := by ring
      have hw1 := alpha_Gam_Wt_le_one hα hθ
      have hfin : 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ)
            * (Real.sin (2*θ))^2 ≤ 1000 * TM m := by
        have hs1 : (Real.sin (2*θ))^2 ≤ 1 := by
          have h' := Real.abs_sin_le_one (2*θ)
          nlinarith [h', sq_abs (Real.sin (2*θ)), abs_nonneg (Real.sin (2*θ))]
        have hnum : α * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := hw1
        have hc0 : 0 ≤ 1000 * Work.Spaces.tBound (m - a - 1) 0 * (α * Work.Spaces.Gam α θ * Wt α θ) :=
          mul_nonneg (mul_nonneg (by norm_num) (Work.Spaces.tBound_nonneg _ _))
            (mul_nonneg (mul_nonneg (le_of_lt hα) hG0) hW)
        calc 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ)
              * (Real.sin (2*θ))^2
            ≤ 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ) * 1 :=
              mul_le_mul_of_nonneg_left hs1 hc0
          _ = 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ) := by ring
          _ ≤ 1000 * (Work.Spaces.tBound (m - a - 1) 0) * 1 := by
              apply mul_le_mul_of_nonneg_left hnum
              exact mul_nonneg (by norm_num) (Work.Spaces.tBound_nonneg _ _)
          _ ≤ 1000 * TM m := by
              have : Work.Spaces.tBound (m - a - 1) 0 ≤ TM m := htB
              nlinarith [this]
      have h5 : (0:ℝ) ≤ (4/3)*K + 1000 := by nlinarith [hK0]
      linarith [hkey, hfin, h5]


/-- The Leibniz step: the bound at order `m+1` from the bound at order `m`. -/
lemma step_bound (m : ℕ) (hm : 2 ≤ m) (hm4 : m ≤ 4) {K : ℝ} (hK0 : 0 ≤ K)
    (hKm : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[m+1] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ Bstep m K * α := by
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  by_cases hI : θ ∈ Set.Ioo 0 (π/2)
  · have hGam_diff : ContDiffOn ℝ ⊤ (fun t => Work.Spaces.Gam α t) (Set.Ioo 0 (π/2)) :=
      contDiffOn_Gam_Ioo' α
    have hq_diff : ContDiffOn ℝ ⊤ Work.Spaces.qfun (Set.Ioo 0 (π/2)) := by
      show ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.cos (2*θ) - 1/3) (Set.Ioo 0 (π/2))
      fun_prop
    have hEqOn : Set.EqOn (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
        (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) (Set.Ioo 0 (π/2)) := by
      intro t ht
      rw [Work.Spaces.dthU_Gam α t hα ht]; ring
    have hmain : Work.Spaces.dthU^[m+1] (fun t => Work.Spaces.Gam α t) θ
        = α * (∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)) := by
      rw [Function.iterate_succ_apply]
      rw [dthU_iter_congr_open isOpen_Ioo m (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
        (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) hEqOn hI]
      simp only [Work.Spaces.dthU_iter_const_mul]
      rw [show (fun θ : ℝ => Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
          = (Work.Spaces.qfun * fun θ : ℝ => Work.Spaces.Gam α θ) from rfl]
      rw [dthU_iter_mul_Ioo m Work.Spaces.qfun (fun θ : ℝ => Work.Spaces.Gam α θ) hI
        hq_diff hGam_diff]
    have hsum : |∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ
        ≤ ((m:ℝ)+1) * CM m K := by
      have habs : |∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)|
          ≤ ∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| := by
        calc |∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)|
            ≤ ∑ a ∈ Finset.range (m+1), |(m.choose a : ℝ) *
                (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
                |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| := by
              apply Finset.sum_congr rfl
              intro a _
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose a))]
      have h2 : (∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
          ≤ ((m:ℝ)+1) * CM m K := by
        rw [Finset.sum_mul]
        calc ∑ a ∈ Finset.range (m+1), ((m.choose a : ℝ) *
                |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
            ≤ ∑ _a ∈ Finset.range (m+1), CM m K := by
              apply Finset.sum_le_sum
              intro a ha
              have ham : a ≤ m := by
                have := Finset.mem_range.mp ha
                omega
              have hX := summand_le m hm hm4 hK0 hKm hα hα1 hθ ham
              have hb : (m.choose a : ℝ) ≤ (2:ℝ)^m := by
                exact_mod_cast Nat.choose_le_two_pow m a
              have hX0 : 0 ≤ |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ :=
                mul_nonneg (abs_nonneg _) hW0
              have hCM0 : 0 ≤ CM m K := by
                rw [CM]
                have h1 : 0 ≤ (4/3)*K + 1000*TM m + 1000 := by
                  have := TM_pos m
                  linarith
                positivity
              calc ((m.choose a : ℝ) *
                    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                      Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
                  = (m.choose a : ℝ) *
                      (|Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                        Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ) := by
                    ring
                _ ≤ (2:ℝ)^m * ((4/3)*K + 1000*TM m + 1000) :=
                    mul_le_mul hb hX hX0 (by positivity)
                _ = CM m K := by rw [CM]
          _ = ((m:ℝ)+1) * CM m K := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
      exact le_trans (mul_le_mul_of_nonneg_right habs hW0) h2
    rw [hmain, abs_mul, abs_of_pos hα]
    calc α * |∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ
        = α * (|∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ) := by ring
      _ ≤ α * (((m:ℝ)+1) * CM m K) := mul_le_mul_of_nonneg_left hsum hα.le
      _ = Bstep m K * α := by rw [Bstep]; ring
  · -- angular endpoints: the weight vanishes
    have hs : Real.sin (2*θ) = 0 := by
      rcases lt_or_eq_of_le hθ.1 with h0 | h0
      · have h1 : θ = π/2 := le_antisymm hθ.2 (le_of_not_gt (fun h => hI ⟨h0, h⟩))
        rw [h1, show 2*(π/2) = π by ring, Real.sin_pi]
      · rw [← h0]; simp
    have hWz : Wt α θ = 0 := by
      rw [Wt, hs, Real.zero_rpow (by linarith : -(α/5) ≠ 0)]
      simp
    rw [hWz, mul_zero]
    exact mul_nonneg (Bstep_nonneg hK0) hα.le


lemma dthU_congr_open {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ} (h : Set.EqOn f g U) :
    Set.EqOn (Work.Spaces.dthU f) (Work.Spaces.dthU g) U := by
  intro θ hθ
  simpa using (dthU_iter_congr_open hU 1 f g h hθ)

/-- The base case: order `2`. -/
lemma Good_two : Good 2 (2 + 16/9) := by
  intro m' hm2 hm2' α hα hα1 θ hθ
  obtain rfl : m' = 2 := le_antisymm hm2' hm2
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  by_cases hI : θ ∈ Set.Ioo 0 (π/2)
  · have hident : Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ
        = α * (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) := by
      show Work.Spaces.dthU (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t)) θ = _
      have hEq : Set.EqOn (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
          (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) (Set.Ioo 0 (π/2)) :=
        fun t ht => by rw [Work.Spaces.dthU_Gam α t hα ht]; ring
      rw [dthU_congr_open isOpen_Ioo hEq hI, Work.Spaces.dthU_const_mul]
      simp only []
      have hdiffq : DifferentiableAt ℝ Work.Spaces.qfun θ :=
        (Work.Spaces.qfun_smooth.differentiable (by simp)).differentiableAt
      have hdiffG : DifferentiableAt ℝ (fun t => Work.Spaces.Gam α t) θ :=
        Work.Spaces.Gam_differentiableAt α θ hI.1 hI.2
      rw [show Work.Spaces.dthU (fun t : ℝ => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ
          = Work.Spaces.dthU (Work.Spaces.qfun * fun t : ℝ => Work.Spaces.Gam α t) θ from rfl]
      rw [Work.Spaces.dthU_mul_apply Work.Spaces.qfun (fun t : ℝ => Work.Spaces.Gam α t) θ
        hdiffq hdiffG]
      rw [dthU_qfun_eq, Work.Spaces.dthU_Gam α θ hα hI]
      ring
    rw [hident, abs_mul, abs_of_pos hα]
    have hq2 : (Work.Spaces.qfun θ)^2 ≤ 16/9 := by
      have h := abs_qfun_le θ
      nlinarith [abs_nonneg (Work.Spaces.qfun θ), sq_abs (Work.Spaces.qfun θ)]
    have hw1 := alpha_Gam_Wt_le_one hα hθ
    have hw2 := sin_sq_Gam_Wt_le_one hα hα1 hθ
    have hs0 : 0 ≤ (Real.sin (2*θ))^2 := sq_nonneg _
    have hbound : α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ * Wt α θ
        ≤ (16/9) := by
      have h2 : (Work.Spaces.qfun θ)^2 * (α * Work.Spaces.Gam α θ * Wt α θ) ≤ (16/9) * 1 :=
        mul_le_mul hq2 hw1 (mul_nonneg (mul_nonneg (le_of_lt hα) hG0) hW0) (by norm_num)
      linarith [h2]
    have hbound2 : 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ ≤ 2 := by
      have h0 : 0 ≤ (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ :=
        mul_nonneg (mul_nonneg hs0 hG0) hW0
      nlinarith [hw2, h0]
    have hX0 : 0 ≤ α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ := by positivity
    have hY0 : 0 ≤ 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ := by positivity
    have htri : |α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
          - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ| * Wt α θ
        ≤ (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ) * Wt α θ
          + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) * Wt α θ := by
      have h1 : |α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ|
          ≤ (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ)
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) := by
        have h := abs_add_le (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ)
          (-(2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ))
        rw [abs_neg, abs_of_nonneg hX0, abs_of_nonneg hY0] at h
        simpa [sub_eq_add_neg] using h
      calc |α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ| * Wt α θ
          ≤ ((α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ)
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ)) * Wt α θ :=
              mul_le_mul_of_nonneg_right h1 hW0
        _ = (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ) * Wt α θ
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) * Wt α θ := by ring
    have ha0 : 0 ≤ α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ := by positivity
    have hb0 : 0 ≤ 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ := by positivity
    calc α * |α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ| * Wt α θ
        = α * (|α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ| * Wt α θ) := by ring
      _ ≤ α * ((α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ) * Wt α θ
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) * Wt α θ) :=
            mul_le_mul_of_nonneg_left htri hα.le
      _ = α * ((α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ * Wt α θ)
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ)) := by ring
      _ ≤ α * ((16/9) + 2) := by
            apply mul_le_mul_of_nonneg_left _ hα.le
            linarith [hbound, hbound2]
      _ = (2 + 16/9) * α := by ring
  · have hs : Real.sin (2*θ) = 0 := by
      rcases lt_or_eq_of_le hθ.1 with h0 | h0
      · have h1 : θ = π/2 := le_antisymm hθ.2 (le_of_not_gt (fun h => hI ⟨h0, h⟩))
        rw [h1, show 2*(π/2) = π by ring, Real.sin_pi]
      · rw [← h0]; simp
    have hWz : Wt α θ = 0 := by
      rw [Wt, hs, Real.zero_rpow (by linarith : -(α/5) ≠ 0)]
      simp
    rw [hWz, mul_zero]
    have : (0:ℝ) < 2 + 16/9 := by norm_num
    exact mul_nonneg this.le hα.le

/-- One step of the induction. -/
lemma Good_step (m : ℕ) (hm : 2 ≤ m) (hm4 : m ≤ 4) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : Good m K) : Good (m+1) (max K (Bstep m K)) := by
  intro m' hm2 hm' α hα hα1 θ hθ
  by_cases hle : m' ≤ m
  · have h1 := hK m' hm2 hle α hα hα1 θ hθ
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  · have hm'eq : m' = m+1 := by omega
    rw [hm'eq]
    have h2 := step_bound m hm hm4 hK0 (hK m hm (le_refl m)) α hα hα1 θ hθ
    exact le_trans h2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hα.le)

noncomputable def K2 : ℝ := 2 + 16/9
noncomputable def K3 : ℝ := max K2 (Bstep 2 K2)
noncomputable def K4 : ℝ := max K3 (Bstep 3 K3)
noncomputable def K5 : ℝ := max K4 (Bstep 4 K4)

lemma K2_pos : 0 < K2 := by rw [K2]; norm_num

lemma Good_three : Good 3 K3 := by
  have := Good_step 2 (by norm_num) (by norm_num) (le_of_lt K2_pos) Good_two
  simpa [K3, K2] using this

lemma Good_four : Good 4 K4 := by
  have h3 : 0 ≤ K3 := le_of_lt (lt_of_lt_of_le K2_pos (le_max_left _ _))
  have := Good_step 3 (by norm_num) (by norm_num) h3 Good_three
  simpa [K4] using this

lemma Good_five : Good 5 K5 := by
  have h4 : 0 ≤ K4 := le_of_lt (lt_of_lt_of_le K2_pos (le_trans (le_max_left _ _) (le_max_left _ _)))
  have := Good_step 4 (by norm_num) (by norm_num) h4 Good_four
  simpa [K5] using this

lemma K5_pos : 0 < K5 := by
  have h : 0 < K2 := K2_pos
  have h3 : 0 < K3 := lt_of_lt_of_le h (le_max_left _ _)
  have h4 : 0 < K4 := lt_of_lt_of_le h3 (le_max_left _ _)
  exact lt_of_lt_of_le h4 (le_max_left _ _)

/-- The weighted bound for the `D_θ`-iterates of `Γ`. -/
theorem dthGamWeightLe :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α := by
  refine ⟨K5, K5_pos, fun m hm hm5 α hα hα1 θ hθ => ?_⟩
  exact Good_five m hm (by omega) α hα hα1 θ hθ



lemma Fstar_eq (α : ℝ) : Work.Construction.Fstar α
    = fun z θ => ((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ) * Work.Spaces.hKer z := by
  funext z θ
  simp only [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.hKer]
  ring

lemma DthIter_Dth (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (Work.Spaces.Dth f) = Work.Spaces.DthIter (j + 1) f := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have h : Work.Spaces.DthIter (j+1) (Work.Spaces.Dth f)
          = Work.Spaces.Dth (Work.Spaces.DthIter (j+1) f) := by
        rw [Work.Spaces.DthIter_succ, ih]
      rw [h]
      exact (Work.Spaces.DthIter_succ (j+1) f).symm

lemma FstarDthFactor (α : ℝ) (j k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
      = (2 * α / Work.Spaces.c α) * deriv^[k] Work.Spaces.hKer z
          * Work.Spaces.dthU^[j + 1] (fun t => Work.Spaces.Gam α t) θ := by
  have h1 : Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))
      = fun z θ => Work.Spaces.dthU^[j+1]
            (fun t => 2 * α / Work.Spaces.c α * Work.Spaces.Gam α t) θ
          * Work.Spaces.hKer z := by
    rw [DthIter_Dth, Fstar_eq]
    funext z θ
    exact Work.Spaces.DthIter_decomp (j+1) _ _ z θ
  rw [h1]
  rw [show Work.Spaces.dthU^[j+1] (fun t => 2 * α / Work.Spaces.c α * Work.Spaces.Gam α t)
      = fun t => (2 * α / Work.Spaces.c α)
          * Work.Spaces.dthU^[j+1] (fun s => Work.Spaces.Gam α s) t from
    Work.Spaces.dthU_iter_const_mul (j+1) (2 * α / Work.Spaces.c α)
      (fun s => Work.Spaces.Gam α s)]
  rw [show Work.Spaces.pzIter k (fun z θ => ((2 * α / Work.Spaces.c α)
          * Work.Spaces.dthU^[j+1] (fun s => Work.Spaces.Gam α s) θ) * Work.Spaces.hKer z) z θ
      = ((2 * α / Work.Spaces.c α)
          * Work.Spaces.dthU^[j+1] (fun s => Work.Spaces.Gam α s) θ)
          * deriv^[k] Work.Spaces.hKer z from
    Work.Spaces.pzIter_decomp k
      (fun t => (2 * α / Work.Spaces.c α)
        * Work.Spaces.dthU^[j+1] (fun s => Work.Spaces.Gam α s) t) Work.Spaces.hKer z θ]
  ring

/-! ## The two pointwise bounds for `D_θ F_*` -/

lemma Fstar_coef_leD' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    |2 * α / Work.Spaces.c α| ≤ 20 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hnum : 0 ≤ 2 * α := by linarith
  rw [abs_of_nonneg (div_nonneg hnum (le_of_lt hcpos)), div_le_iff₀ hcpos]
  nlinarith

lemma DthFstar_z_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z+1)^k * Work.Spaces.pzIter k (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ|
      ≤ (20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k+1))) * α^2 := by
  change |(z+1)^k * Work.Spaces.pzIter k
      (Work.Spaces.DthIter 0 (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ| ≤ _
  rw [FstarDthFactor α 0 k z θ]
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
    Work.Spaces.pzIter_hKer_bound k z hz
  have hcoef := Fstar_coef_leD' α hα hα1
  have hdth := Work.Spaces.dthU_Gam_le 1 (by norm_num) α hα hα1 θ hθ
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hloc : (z + 1) ^ k * ((2 * α / Work.Spaces.c α) * deriv^[k] Work.Spaces.hKer z
        * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ)
      = (2 * α / Work.Spaces.c α) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)
        * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ := by ring
  rw [hloc, abs_mul, abs_mul]
  have h1 : |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound 0 0 := by
    refine le_trans hdth ?_
    exact mul_le_of_le_one_right (mul_nonneg (le_of_lt hα) (Work.Spaces.tBound_nonneg _ _)) hGam.2
  have h2 : |2 * α / Work.Spaces.c α| * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) :=
    mul_le_mul hcoef hker (abs_nonneg _) (by positivity)
  have h3 : (20 * α) * ((k.factorial : ℝ) * (k + 1)) * |Work.Spaces.dthU^[1]
      (fun t => Work.Spaces.Gam α t) θ|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) * (α * Work.Spaces.tBound 0 0) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : |2 * α / Work.Spaces.c α| * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      * |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) * (α * Work.Spaces.tBound 0 0) :=
    le_trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) h3
  calc |2 * α / Work.Spaces.c α| * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
        * |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) * (α * Work.Spaces.tBound 0 0) := h4
    _ = (20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1))) * α^2 := by ring

lemma DthFstar_mixed_bound {K : ℝ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z+1)^k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
        * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ))|
      ≤ (20 * K * ((k.factorial : ℝ) * (k+1))) * α^2 := by
  rw [show (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
        * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ))
      = (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ * Wt α θ from by
    rw [Wt]; ring]
  rw [FstarDthFactor α j k z θ]
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
    Work.Spaces.pzIter_hKer_bound k z hz
  have hcoef := Fstar_coef_leD' α hα hα1
  have hKer0 : 0 ≤ (k.factorial : ℝ) * (k + 1) := by positivity
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hdth := hK (j+1) (by omega) (by omega) α hα hα1 θ hθ
  have hloc : (z + 1) ^ k * ((2 * α / Work.Spaces.c α) * deriv^[k] Work.Spaces.hKer z
        * Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ) * Wt α θ
      = (2 * α / Work.Spaces.c α) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)
        * (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ) := by ring
  have hmain : |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)
        * (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ)|
      ≤ (20 * K * ((k.factorial : ℝ) * (k+1))) * α^2 := by
    rw [abs_mul]
    have hAB : |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)|
        ≤ 20 * α * ((k.factorial : ℝ) * (k + 1)) := by
      rw [abs_mul]
      exact mul_le_mul hcoef hker (abs_nonneg _) (by positivity)
    have hdW : |Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ| ≤ K * α := by
      rw [abs_mul, abs_of_nonneg hW0]
      exact hdth
    calc |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)|
          * |Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ|
        ≤ (20 * α * ((k.factorial : ℝ) * (k + 1))) * (K * α) :=
          mul_le_mul hAB hdW (abs_nonneg _) (by positivity)
      _ = (20 * K * ((k.factorial : ℝ) * (k + 1))) * α^2 := by ring
  rw [hloc]
  exact hmain


/-! ## Assembly -/

/-- The universal constant of the estimate. -/
noncomputable def KD (K : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 5, 20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)))
    + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then 20 * K * ((k.factorial : ℝ) * (k + 1)) else 0)

lemma KD_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ KD K := by
  rw [KD]
  refine add_nonneg (Finset.sum_nonneg fun k _ => ?_)
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_)
  · exact mul_nonneg (mul_nonneg (by norm_num) (Work.Spaces.tBound_nonneg _ _)) (by positivity)
  · split_ifs with h
    · exact mul_nonneg (mul_nonneg (by norm_num) hK) (by positivity)
    · norm_num

lemma WlInfMem_DthFstar {K : ℝ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) := by
  constructor
  · intro k hk
    refine ⟨20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)) * α^2,
      fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact DthFstar_z_bound α hα hα1 k z θ hz hθ
  · intro j hj k hk hj1 hjk
    refine ⟨20 * K * ((k.factorial : ℝ) * (k + 1)) * α^2, fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact DthFstar_mixed_bound hK α hα hα1 j k hj1 (by omega) z θ hz hθ

lemma WlInf_DthFstar_le {K : ℝ} (hKpos : 0 < K)
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ KD K * α^2 := by
  have h2 : KD K * α^2 =
      (∑ k ∈ Finset.range 5,
          20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)) * α^2)
        + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
            (if 1 ≤ j ∧ k + j ≤ 4 then
              20 * K * ((k.factorial : ℝ) * (k + 1)) * α^2 else 0) := by
    rw [KD, add_mul]
    congr 1
    · rw [Finset.sum_mul]
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with h <;> ring
  rw [Work.Spaces.WlInf, h2]
  apply add_le_add
  · exact Finset.sum_le_sum fun k hk =>
      Work.Spaces.supAbs_le fun z hz θ hθ => DthFstar_z_bound α hα hα1 k z θ hz hθ
  · apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hcond
    · exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        DthFstar_mixed_bound hK α hα hα1 j k hcond.1 (by omega) z θ hz hθ
    · simp

end DthAux

theorem DthFstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := DthAux.dthGamWeightLe
  refine ⟨DthAux.KD K + 1, by linarith [DthAux.KD_nonneg (le_of_lt hKpos)],
    fun α hα hα1 => ⟨?_, ?_⟩⟩
  · exact DthAux.WlInfMem_DthFstar hK α hα hα1
  · refine le_trans (DthAux.WlInf_DthFstar_le hKpos hK α hα hα1) ?_
    have h0 : 0 ≤ α^2 := sq_nonneg α
    nlinarith [DthAux.KD_nonneg (le_of_lt hKpos), h0]

end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_z_W =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## The singular factor `φ(z) = (1+z)²/z · hKer z` -/

/-- `φ z = ((z+1)^2/z)·hKer z`, where `hKer z = z/(1+z)^2`.  It equals `1` for
`z ∉ {0,-1}` and `0` at `z = 0` and `z = -1`. -/
def phi (z : ℝ) : ℝ := (z + 1) ^ 2 / z * Work.Spaces.hKer z







/-! ## Vanishing of the `z`-derivatives of `φ` -/





/-! ## The weighted profile and its derivatives -/


/-- The angular factor `A(θ) = (2α/c)·Γ(θ)`. -/
def Aang (α : ℝ) (θ : ℝ) : ℝ := (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ






/-! ## The pointwise estimates -/




/-! ## Assembly -/






end Work.FTS.Nonlinear.FstarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.FstarPkg

open scoped Topology
open Work.Spaces

-- Intended full name: `Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound`
-- (declare it inside `namespace Work.FTS.Nonlinear.FstarPkg`).  Here `Hz` and `HB` are the
-- definitions of `Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs`;
-- `Hz_eq_mul_deriv` (same module) gives `Hz z = 2 * (z * deriv hKer z)` for `z > -1`, and
-- `Work.Spaces.iter_deriv_hKerClosed` / `Work.Spaces.pzIter_hKer_bound` give
-- `deriv^[m] hKer = hKerClosed m` with `|(z+1)^m hKerClosed m z| ≤ m!(m+1)` for `z ≥ 0`.
theorem Hz_deriv_bound (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z|
      ≤ Work.FTS.Nonlinear.FstarPkg.HB k := by
  -- The iterated derivatives of `Hz` in closed form, on `(-1,∞)`:
  -- `H^{(n)} = 2·(y·h^{(n+1)} + n·h^{(n)})` (Leibniz, since `y'' = 0`).
  have hiter : ∀ n : ℕ, ∀ y : ℝ, -1 < y →
      deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz y
        = 2 * (y * hKerClosed (n + 1) y + (n : ℝ) * hKerClosed n y) := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simp only [Function.iterate_zero_apply]
      have h1 : deriv Work.Spaces.hKer y = hKerClosed 1 y := by
        show deriv (fun y : ℝ => y / (1 + y) ^ 2) y = hKerClosed 1 y
        exact Work.Spaces.iter_deriv_hKerClosed 1 y hy
      rw [Work.FTS.Nonlinear.FstarPkg.Hz_eq_mul_deriv hy, h1]
      simp [zero_mul]
    | succ n ih =>
      intro y hy
      rw [Function.iterate_succ_apply']
      have hev : deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz =ᶠ[𝓝 y]
          (fun t : ℝ => 2 * (t * hKerClosed (n + 1) t + (n : ℝ) * hKerClosed n t)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
        exact ih t ht
      rw [hev.deriv_eq]
      have hyne : y ≠ -1 := by linarith
      have hd1 : HasDerivAt (fun t : ℝ => t * hKerClosed (n + 1) t)
          (1 * hKerClosed (n + 1) y + y * hKerClosed ((n + 1) + 1) y) y :=
        (hasDerivAt_id y).mul (Work.Spaces.hasDerivAt_hKerClosed (n + 1) hyne)
      have hd2 : HasDerivAt (fun t : ℝ => (n : ℝ) * hKerClosed n t)
          ((n : ℝ) * hKerClosed (n + 1) y) y :=
        (Work.Spaces.hasDerivAt_hKerClosed n hyne).const_mul (n : ℝ)
      have hd : HasDerivAt
          (fun t : ℝ => 2 * (t * hKerClosed (n + 1) t + (n : ℝ) * hKerClosed n t))
          (2 * (1 * hKerClosed (n + 1) y + y * hKerClosed ((n + 1) + 1) y
            + (n : ℝ) * hKerClosed (n + 1) y)) y :=
        (hd1.add hd2).const_mul 2
      rw [hd.deriv]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  -- The weighted bound for the closed form of `h` (`Work.Spaces.pzIter_hKer_bound`).
  have hpz : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y →
      |(y + 1) ^ n * hKerClosed n y| ≤ (n.factorial : ℝ) * (n + 1) := by
    intro n y hy
    have h := Work.Spaces.pzIter_hKer_bound n y hy
    rwa [show deriv^[n] (fun t : ℝ => t / (1 + t) ^ 2) y = hKerClosed n y from
        Work.Spaces.iter_deriv_hKerClosed n y (by linarith)] at h
  have hz1 : -1 < z := by linarith
  rw [hiter k z hz1]
  have hzp : (0 : ℝ) < z + 1 := by linarith
  -- The `z·h^{(k+1)}` term: move the factor `z` onto the weight `(z+1)^{k+1}`.
  have hpow : z * ((z + 1) ^ k * hKerClosed (k + 1) z)
      = (z / (z + 1)) * ((z + 1) ^ (k + 1) * hKerClosed (k + 1) z) := by
    field_simp
    ring
  have hr0 : 0 ≤ z / (z + 1) := div_nonneg hz (le_of_lt hzp)
  have hr1 : z / (z + 1) ≤ 1 := by
    rw [div_le_one hzp]
    linarith
  have hA : |z * ((z + 1) ^ k * hKerClosed (k + 1) z)|
      ≤ ((k + 1).factorial : ℝ) * ((k + 2 : ℕ) : ℝ) := by
    rw [hpow, abs_mul, abs_of_nonneg hr0]
    have hbase := hpz (k + 1) z hz
    have hcast : (((k + 1 : ℕ) : ℝ) + 1) = ((k + 2 : ℕ) : ℝ) := by
      push_cast
      ring
    calc (z / (z + 1)) * |(z + 1) ^ (k + 1) * hKerClosed (k + 1) z|
        ≤ 1 * (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) :=
          mul_le_mul hr1 hbase (abs_nonneg _) zero_le_one
      _ = ((k + 1).factorial : ℝ) * ((k + 2 : ℕ) : ℝ) := by rw [one_mul, hcast]
  -- The `k·h^{(k)}` term.
  have hB : |(k : ℝ) * ((z + 1) ^ k * hKerClosed k z)|
      ≤ (k : ℝ) * ((k.factorial : ℝ) * (k + 1)) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact mul_le_mul_of_nonneg_left (hpz k z hz) (Nat.cast_nonneg k)
  have hsplit : (z + 1) ^ k * (2 * (z * hKerClosed (k + 1) z + (k : ℝ) * hKerClosed k z))
      = 2 * (z * ((z + 1) ^ k * hKerClosed (k + 1) z)
        + (k : ℝ) * ((z + 1) ^ k * hKerClosed k z)) := by
    ring
  rw [hsplit]
  rw [abs_mul, abs_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)]
  calc 2 * |z * ((z + 1) ^ k * hKerClosed (k + 1) z)
        + (k : ℝ) * ((z + 1) ^ k * hKerClosed k z)|
      ≤ 2 * (|z * ((z + 1) ^ k * hKerClosed (k + 1) z)|
        + |(k : ℝ) * ((z + 1) ^ k * hKerClosed k z)|) := by
        have h := abs_add_le (z * ((z + 1) ^ k * hKerClosed (k + 1) z))
          ((k : ℝ) * ((z + 1) ^ k * hKerClosed k z))
        linarith
    _ ≤ 2 * (((k + 1).factorial : ℝ) * ((k + 2 : ℕ) : ℝ)
        + (k : ℝ) * ((k.factorial : ℝ) * (k + 1))) := by
        linarith
    _ = Work.FTS.Nonlinear.FstarPkg.HB k := by
        rw [Work.FTS.Nonlinear.FstarPkg.HB]
        push_cast
        ring

end Work.FTS.Nonlinear.FstarPkg
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.wtoHQ_of_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false


end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

theorem FaSumAE {N : Work.FTS.Galerkin.Fn} (p : Fin 20 → Work.FTS.Galerkin.Fn)
    (hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd → N r θ = ∑ k, p k r θ)
    (hin : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : Fin 20, AEMeasurable
      (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hout : ∀ k : Fin 20, AEMeasurable
      (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∑ k : Fin 20, (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)) := by
  classical
  -- ### Step 0: the split holds on all of `Iθ`, the endpoints being killed by `K`
  have hkey : ∀ (r θ : ℝ), 0 < r → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.K θ * N r θ = Work.Spaces.K θ * ∑ k : Fin 20, p k r θ := by
    intro r θ hr hθ
    by_cases h0 : θ = 0
    · subst h0
      simp [Work.Spaces.K]
    by_cases h1 : θ = Real.pi / 2
    · subst h1
      simp [Work.Spaces.K]
    · have hq : (r, θ) ∈ Work.Construction.Qd := by
        rw [Work.Construction.Qd]
        simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨hr, lt_of_le_of_ne hθ.1 (Ne.symm h0), lt_of_le_of_ne hθ.2 h1⟩
      rw [hsplit r θ hq]
  -- ### Step 1: the inner (`θ`-)integral of `N` is that of the sum, for every `r > 0`
  have hinnerEq : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        = ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ| := by
    intro r hr
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    show ENNReal.ofReal |Work.Spaces.K θ * N r θ|
      = ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|
    rw [hkey r θ hr hθ]
  -- ### Step 2: the `θ`-integral of the sum is at most the sum of the `θ`-integrals
  -- (this only uses the triangle inequality in `θ` and hence holds for *every* `r`
  -- for which the summands are `θ`-a.e.-measurable, in particular a.e. `r`)
  have hinnerSum : ∀ r : ℝ, (∀ k : Fin 20, AEMeasurable
        (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ * p k r θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) →
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
        ≤ ∑ k : Fin 20, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.Spaces.K θ * p k r θ| := by
    intro r hk
    have hstep : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ∑ k : Fin 20,
            ENNReal.ofReal |Work.Spaces.K θ * p k r θ| := by
      apply MeasureTheory.lintegral_mono
      intro θ
      have h1 : ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|
          ≤ ENNReal.ofReal (∑ k : Fin 20, |Work.Spaces.K θ * p k r θ|) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.mul_sum]
        exact Finset.abs_sum_le_sum_abs _ _
      have h2 : ENNReal.ofReal (∑ k : Fin 20, |Work.Spaces.K θ * p k r θ|)
          = ∑ k : Fin 20, ENNReal.ofReal |Work.Spaces.K θ * p k r θ| :=
        ENNReal.ofReal_sum_of_nonneg (fun k _ => abs_nonneg _)
      exact h1.trans_eq h2
    rw [MeasureTheory.lintegral_finsetSum' Finset.univ (fun k _ => hk k)] at hstep
    exact hstep
  -- ### Step 3: replace `N` by the sum in the outer (`r`-)integral (pointwise, `r > 0`)
  have hEq : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|) := by
    apply MeasureTheory.lintegral_congr_ae
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro r hr
    show ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
      = ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
    rw [hinnerEq r hr]
  rw [hEq]
  -- ### Step 4: pull `r⁻¹` and the outer integral through the finite sum
  have hae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|)
        ≤ ∑ k : Fin 20, ENNReal.ofReal r⁻¹ *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|) := by
    filter_upwards [hin] with r hrin
    rw [← Finset.mul_sum]
    exact mul_le_mul_right (hinnerSum r hrin) _
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * ∑ k : Fin 20, p k r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ∑ k : Fin 20, ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|) :=
        MeasureTheory.lintegral_mono_ae hae
    _ = ∑ k : Fin 20, ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * p k r θ|) :=
        MeasureTheory.lintegral_finsetSum' Finset.univ (fun k _ =>
          ((ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable).mul (hout k))

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.aesm_FK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

theorem aesm_FK {g : ℝ → ℝ → ℝ}
    (hg : MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK g z))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := by
  -- the angular weight `θ ↦ K θ` is measurable, hence a.e. strongly measurable
  have hK : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := by
    have : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
      simp only [Work.Spaces.K]
      fun_prop
    exact this.aestronglyMeasurable
  -- the joint integrand `(z,θ) ↦ g z θ * K θ` is a.e. strongly measurable
  have hprod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Function.uncurry g p * Work.Spaces.K p.2)
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := hg.mul hK
  -- measurability of the parametric Bochner integral in `z`
  have hz : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, Function.uncurry g (z, θ) * Work.Spaces.K θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hprod.integral_prod_right'
  -- push along `Prod.fst` (quasi-measure-preserving: the angular factor is finite)
  have hmain := hz.comp_fst (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
  show MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Construction.FK g p.1)
    ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
  exact hmain

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.aesm_Uop_of_div =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

theorem aesm_Uop_of_div {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (Work.Construction.Uop α Ψ))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := by
  -- `s2 θ = sin(2θ)` is continuous
  have hs2cont : Continuous fun θ : ℝ => Work.Construction.s2 θ := by
    simp only [Work.Construction.s2]; fun_prop
  -- its zero set is countable, hence null
  have hzero : MeasureTheory.volume {θ : ℝ | Work.Construction.s2 θ = 0} = 0 := by
    have hsub : {θ : ℝ | Work.Construction.s2 θ = 0}
        ⊆ Set.range (fun n : ℤ => (n : ℝ) * π / 2) := by
      intro θ hθ
      change Work.Construction.s2 θ = 0 at hθ
      simp only [Work.Construction.s2] at hθ
      rw [Real.sin_eq_zero_iff] at hθ
      obtain ⟨n, hn⟩ := hθ
      refine ⟨n, ?_⟩
      rw [div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)]
      linarith
    exact measure_mono_null hsub ((Set.countable_range _).measure_zero MeasureTheory.volume)
  -- the same set is null for `volume ↾ Iθ`
  have hIθzero : (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      {θ : ℝ | Work.Construction.s2 θ = 0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply (t := {θ : ℝ | Work.Construction.s2 θ = 0})
      (hs2cont.measurable (measurableSet_singleton 0))]
    exact measure_mono_null Set.inter_subset_left hzero
  have hsin : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Construction.s2 θ ≠ 0 := by
    rw [MeasureTheory.ae_iff,
      show {θ : ℝ | ¬ Work.Construction.s2 θ ≠ 0}
          = {θ : ℝ | Work.Construction.s2 θ = 0} from by
        ext θ; simp only [ne_eq, not_not]]
    exact hIθzero
  -- hence `s2 p.2 ≠ 0` for `QdMeas`-a.e. `p`
  have hmeasP : MeasurableSet {p : ℝ × ℝ | Work.Construction.s2 p.2 ≠ 0} :=
    (hs2cont.measurable.comp measurable_snd) ((measurableSet_singleton (0 : ℝ)).compl)
  have hae : ∀ᵐ p ∂QdMeas, Work.Construction.s2 p.2 ≠ 0 := by
    rw [QdMeas, MeasureTheory.Measure.ae_prod_iff_ae_ae hmeasP]
    exact Filter.Eventually.of_forall fun _ => hsin
  -- on that full-measure set the division can be undone
  have hEq : (fun p : ℝ × ℝ => Function.uncurry (fun z θ =>
        Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) p * Work.Construction.s2 p.2)
      =ᵐ[QdMeas] (fun p : ℝ × ℝ => Function.uncurry (Work.Construction.Uop α Ψ) p) := by
    filter_upwards [hae] with p hp
    show (Work.Construction.Uop α Ψ p.1 p.2 / Work.Construction.s2 p.2)
        * Work.Construction.s2 p.2 = Work.Construction.Uop α Ψ p.1 p.2
    exact div_mul_cancel₀ _ hp
  have hK : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
      QdMeas := (hs2cont.measurable.comp measurable_snd).aestronglyMeasurable
  exact (h.mul hK).congr hEq

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.aesm_star_ops =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option autoImplicit false

/-- The elliptic residual `Φ̃_* = Φ_* - Θ_*(α)` of the `F_*`-half is `C^∞` on the open
quadrant as soon as its two summands are — here `Θ_*(α) = Θ α (F_*)` is the hypothesis
`hΘ` of the statement, so no hypothesis on `α` is needed. -/
theorem smoothQuad_PhiTs_of {α : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΘ : Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α))) :
    Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) := by
  change Work.FTS.LocData.SmoothQuad
    (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
  exact Work.FTS.LocData.smoothQuad_sub hΦs hΘ

theorem aesm_star_ops {α : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΘ : Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α))) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas ∧
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas ∧
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := by
  have hPhiTs : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    smoothQuad_PhiTs_of hΦs hΘ
  obtain ⟨hR, hU, hV⟩ := smoothQuad_ops (α := α) (Ψ := Work.FTS.Nonlin.PhiTs α Φs) hPhiTs
  exact ⟨aesm_of_smoothQuad hR, aesm_of_smoothQuad hU, aesm_of_smoothQuad hV⟩

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option maxHeartbeats 1600000

/-!
# `gPt` — the pointwise size of the perturbation's elliptic outputs

The elliptic package `Work.FTS.Nonlin.EllPkgG α Ce g Φg` of the perturbation `g` bounds the
`ℋ⁴`-norms of the three coefficients

`ℛ(Φ̃_g)`, `𝒰(Φ̃_g)/sin(2θ)`, `𝒱(Φ̃_g)`   (`Φ̃_g = Work.FTS.Nonlin.PhiTg α g Φg`)

of the nonlinearity by `Ce·|g|_{ℋ⁴}`.  The nonlinear estimates of §8 of the paper need these
coefficients not only in `L²` but *pointwise* inside the quadrant, and this file supplies that:
the interior `L^∞`-`ℋ⁴` trade-off (Elgindi's Corollary `SecondDerivativesBounded`, in the
`RegQ`-form `Work.FTS.H2.LinfQ.mixed_supAbsO_le`, constant `10`),

  `|u(z,θ)| ≤ 10/√(γ-1)·|u|_{ℋ⁴} = 10·√(10/α)·|u|_{ℋ⁴}`   (`z > 0`, `0 < θ < π/2`),

because `γ - 1 = α/10`.  Composing with the `EllPkgG`-bounds and replacing `Ce` by `max Ce 0`
gives the three estimates of `gPt`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The interior `L^∞` bound with the explicit constant `10`.**

For `RegQ α 4 f` (`= SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f`, the interior class of
`Submission/Work/FTS/Vocab.lean`) and `0 < α ≤ 1`, the function itself is bounded on the open
quadrant by `10/√(γ-1)·|f|_{ℋ⁴}`.

The bound `supAbsO f ≤ 10/√(γ-1)·|f|_{ℋ⁴}` with the explicit constant `10` is
`Work.FTS.H2.mixed_supAbsO_le` (the `(b,a) = (0,0)` instance); the passage from the interior
*suppremum* to the *pointwise* statement is `Work.FTS.H2.le_supAbsO`, which needs a uniform
bound on the quadrant only in order to know that `supAbsO` is not the junk value attached to an
unbounded set.  Such a bound is available from the pointwise form
`Work.FTS.H2.HQ.LinfQpt` of the same trade-off (with its two one-dimensional Hardy ingredients
`Work.FTS.H2.HardyThetaO` and `Work.FTS.H2.hardyZ_open`), whose constant is unknown but
positive; that is all that is needed. -/
theorem abs_le_ten_sqrt_gam {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.Nonlin.RegQ α 4 f) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, _hCpos, hL⟩ := Work.FTS.H2.HQ.LinfQpt
  -- the two one-dimensional Hardy inequalities, in the shapes `LinfQpt` asks them for
  have hAng : ∀ (u : ℝ → ℝ → ℝ) (z : ℝ), Work.FTS.LocData.SmoothQuad u →
      z ∈ Set.Ioi (-1) → Tendsto (fun θ => u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      IntegrableOn (fun σ => (Work.Spaces.pth u z σ) ^ 2
        * Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), u z θ ^ 2
        ≤ 100 / (Work.Spaces.gam α - 1) * ∫ σ in Work.Spaces.Iθ,
            Work.Spaces.pth u z σ ^ 2 * Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α) :=
    fun u z hu hz h0 hint => Work.FTS.H2.HardyThetaO α hα hα1 u z hu hz h0 hint
  have hRad : ∀ (v : ℝ → ℝ), ContDiffOn ℝ 1 v (Set.Ioi 0) → Tendsto v atTop (nhds 0) →
      IntegrableOn (fun s => (s * deriv v s) ^ 2 * Work.Spaces.w s ^ 2) Work.Spaces.Iz →
      ∀ z ∈ Set.Ioi 0, v z ^ 2
        ≤ ∫ s in Work.Spaces.Iz, (s * deriv v s) ^ 2 * Work.Spaces.w s ^ 2 :=
    fun v hcd hdec hint => Work.FTS.H2.hardyZ_open hcd hdec hint
  -- a uniform (but numerically unknown) bound on the open quadrant
  have hglobal : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |f z' θ'| ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
    intro z' θ' hz' hθ' hθ''
    have h := hL α f 0 0 hα hα1 (by norm_num) hreg hAng hRad z' hz' θ' hθ' hθ''
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  intro z hz θ hθ0 hθ1
  have hsup : |f z θ| ≤ Work.FTS.H2.supAbsO f :=
    Work.FTS.H2.le_supAbsO hz hθ0 hθ1 hglobal
  have hsupb : Work.FTS.H2.supAbsO f ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
      * Work.FTS.Nonlin.Xn α f := by
    have h := Work.FTS.H2.mixed_supAbsO_le α f hα hα1 hreg.1 hreg.2.1 hreg.2.2 0 0
      (by norm_num)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  exact le_trans hsup hsupb

/-- `γ - 1 = α/10`, so `10/√(γ-1) = 10·√(10/α)` for `α > 0`. -/
theorem ten_div_sqrt_gam {α : ℝ} (hα : 0 < α) :
    10 / Real.sqrt (Work.Spaces.gam α - 1) = 10 * Real.sqrt (10 / α) := by
  have hαn : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have h10 : 0 < Real.sqrt (10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [Work.Spaces.gam_sub_one α,
    Real.sqrt_div (le_of_lt hα) 10,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 10) α]
  field_simp

theorem gPt {α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) ∧
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) ∧
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hRreg, hRbd⟩ := hell.R
  obtain ⟨hUreg, hUbd⟩ := hell.U
  obtain ⟨hVreg, hVbd⟩ := hell.V
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCemax : Ce ≤ max Ce 0 := le_max_left Ce 0
  have hcoef : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  -- the common shape of the three estimates
  have key : ∀ {f : ℝ → ℝ → ℝ}, Work.FTS.Nonlin.RegQ α 4 f →
      Work.FTS.Nonlin.Xn α f ≤ Ce * Work.FTS.Nonlin.Xn α g →
      ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
        |f z θ| ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
    intro f hreg hbd z hz θ hθ0 hθ1
    have h1 := abs_le_ten_sqrt_gam hα hα1 hreg z hz θ hθ0 hθ1
    have h2 : Work.FTS.Nonlin.Xn α f ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g :=
      le_trans hbd (mul_le_mul_of_nonneg_right hCemax hXg)
    calc |f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := h1
      _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
            * (max Ce 0 * Work.FTS.Nonlin.Xn α g) := mul_le_mul_of_nonneg_left h2 hcoef
      _ = 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
          rw [ten_div_sqrt_gam hα]; ring
  exact ⟨key hRreg hRbd, key hUreg hUbd, key hVreg hVbd⟩

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.RowInputs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `Pbd α X ≥ 0` for `0 ≤ α`, `0 ≤ X`. -/
theorem Pbd_nonneg {α X : ℝ} (hα : 0 ≤ α) (hX : 0 ≤ X) : 0 ≤ Pbd α X := by
  rw [Pbd]
  have h1 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 := mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα _) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα _) (by positivity)
  linarith


/-- `α³·X ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem cube_alpha_mul_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ 3 * X ≤ Pbd α X := by
  have h32 : α ^ 3 ≤ α ^ 2 := by
    have he : α ^ 3 = α ^ 2 * α := by ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hα1
  exact le_trans (mul_le_mul_of_nonneg_right h32 hX) (alpha_sq_mul_le_Pbd hα hX)


/-- The per-piece inputs of the design's table (§3.4) together with the exact splits of
`N₀`, `N` and `N_*` and the three zero-mode estimates of §3.5.

Every field is a statement about *concrete* functions; none of them mentions `UnifIP`.  The
constant `C` is the single universal constant of the table. -/
structure RowInputs (IP : ℝ → Fn → Fn → ℝ) (α C : ℝ) (g Φs Φg : Fn) : Prop where
  /-- the perturbation is in the `ℋ⁴`-class of the frozen vocabulary -/
  reg4 : RegQ α 4 g
  /-- row 1: `|N₀₁+N₀₂|_{ℋ⁴} ≤ Cα²` (tex 1398--1402, `H4N_GammaTerm_le`) -/
  r1 : Xn α (N0fix α) ≤ C * α ^ 2
  /-- row 2: `|N₀₃|_{ℋ⁴} ≤ Cα^{-1}X²` (tex 1404--1406) -/
  r2 : Xn α (N03g α g) ≤ C * (α ^ (-(1 : ℝ)) * Xn α g ^ 2)
  /-- row 3: `|N₀₄ᵃ|_{ℋ⁴} ≤ C√α X` (tex 1410--1412) -/
  r3 : Xn α (N04aF α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 4: `|(N₀₄ᵇ, g)| ≤ Cα^{-3/2}X³` (tex 1414, `Transport1`) -/
  r4 : |IP α (N04bF α g) g| ≤ C * (α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 5: `|N₀₅ᵃ|_{ℋ⁴} ≤ C√α X` (tex 1416--1418) -/
  r5 : Xn α (N05aF α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 6: `|(N₀₅ᵇ, g)| ≤ Cα^{-1/2}X³` (tex 1419, `Transport2`) -/
  r6 : |IP α (N05bF α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 7: `|(N₀₆, g)| ≤ C√α X²` (tex 1421--1423, `Transport3`) -/
  r7 : |IP α (N06F α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  /-- row 8: `|N₁^{gg}|_{ℋ⁴} ≤ Cα^{-1/2}X²` (tex 1450, `HProductRule` + `RemovingL12`) -/
  r8 : Xn α (N1gg α g Φg) ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2)
  /-- row 9: `|N₁^{g*}|_{ℋ⁴} ≤ C√α X` (tex 1451, `WProductRule`) -/
  r9 : Xn α (N1gs α g Φg) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 10: `|N₁^{*g}|_{ℋ⁴} ≤ C√α X` (tex 1451, `PhiStarRegularity`) -/
  r10 : Xn α (N1sg α Φs g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 11: `|N₁^{**}|_{ℋ⁴} ≤ Cα²` (tex 1452--1454, `WtoH` + `ProdW`) -/
  r11 : Xn α (N1ss α Φs) ≤ C * α ^ 2
  /-- row 12: `|(N₂^{gg}, g)| ≤ Cα^{-1/2}X³` (tex 1470, `Transport1`) -/
  r12 : |IP α (N2gg α g Φg) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 13: `|N₂^{g*}|_{ℋ⁴} ≤ Cα^{3/2}X` (tex 1471, `WProductRule`) -/
  r13 : Xn α (N2gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  /-- row 14: `|(N₂^{*g}, g)| ≤ C√α X²` (tex 1473, `SpecialTransport`) -/
  r14 : |IP α (N2sg α Φs g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  /-- row 15: `|N₂^{**}|_{ℋ⁴} ≤ Cα²` (tex 1475, `WtoH` + `WtoW`) -/
  r15 : Xn α (N2ss α Φs) ≤ C * α ^ 2
  /-- row 16: `|(N₃^{gg}, g)| ≤ C√α X³` (tex 1484, `Transport2`) -/
  r16 : |IP α (N3gg α g Φg) g| ≤ C * (Real.sqrt α * Xn α g ^ 3)
  /-- row 17: `|N₃^{g*}|_{ℋ⁴} ≤ Cα^{3/2}X` -/
  r17 : Xn α (N3gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  /-- row 18: `|(N₃^{*g}, g)| ≤ Cα^{3/2}X²` (`Transport3`) -/
  r18 : |IP α (N3sg α Φs g) g| ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g ^ 2)
  /-- row 19: `|N₃^{**}|_{ℋ⁴} ≤ Cα³` (`WtoH`) -/
  r19 : Xn α (N3ss α Φs) ≤ C * (α ^ 3)
  /-- row 20: `|(N₄^{gg}, g)| ≤ Cα^{-1/2}X³` (`Transport1`, `FKg = -D_zL₁₂g`) -/
  r20 : |IP α (N4gg α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 21: `|N₄^{gs}|_{ℋ⁴} ≤ Cα^{3/2}X` -/
  r21 : Xn α (N4gs α g) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  /-- row 22: `|(N₄^{sg}, g)| ≤ C√α X²` (`Transport3`) -/
  r22 : |IP α (N4sg α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  /-- row 23: `|N₄^{**}|_{ℋ⁴} ≤ Cα³` -/
  r23 : Xn α (N4ss α) ≤ C * (α ^ 3)
  /-- row 24: `|N₅^{gg}|_{ℋ⁴} ≤ CX²` (`radial_prod` + `angmul_radial`) -/
  r24 : Xn α (N5gg g) ≤ C * Xn α g ^ 2
  /-- row 25: `|N₅^{gs}| + |N₅^{*g}| ≤ C√α X` (`WProductRule`) -/
  r25 : Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 26: `|N₅^{**}|_{ℋ⁴} ≤ Cα²` -/
  r26 : Xn α (N5ss α) ≤ C * α ^ 2
  /-- the `ℋ⁴`-bound of `AK` (design §3.2, `AK_H4`) -/
  rak : Xn α (Work.Construction.AK α) ≤ C
  /-- `L-N4.6`, constant pieces: `|L₁₂(N₀)(0)| ≤ C(α² + √α X + α^{-3/2}X²)` -/
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  /-- `L-N4.6`, the `N`-pieces -/
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  /-- `L-N4.6`, the `3D_θg/(1+z)`-piece (θ-integration by parts, tex 1517--1521) -/
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ C * Xn α g
  /-- **the split of `N₀`** (design L-N4.3, from `N0_first_two_eq'` and `N04/N05_eq_halves`) -/
  hN0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
          + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)
  /-- **the four-way split of `N`** (design L-N4.3, from `PhiTil_split`, additivity of `FK`
  and the product rule for `∂_θ`, `D_z`) -/
  hN : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
        + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
        + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
        + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
        + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)
  /-- **the `N_*`-collapse** (design §5 T6: `N_* = -μ g - (μ+λ+μλ)D_zg` with
  `λ = lamfun μ` is `μ(D_z g - g)`) -/
  hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ

/-! ## Sum additivity of `IP` -/





end Work.FTS.Nonlin
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WtohWin.Basics =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WtohWin

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **`D_z`-derivatives are bounded by the `z^j ∂_z^j`-bounds on the open half-line**: if
`|w(z)·z^j ∂_z^j h| ≤ M` for `j ≤ i ≤ 4` at `(z,θ)`, then `|w(z)·D_z^i h| ≤ 100 M`.  This is
the open-quadrant (`SmoothOpen`) companion of `Work.FTS.H2.Q.abs_w_DzIter_le_sm`, and only
differs from it by using the Stirling expansion on `(0,∞)`
(`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`) and the evaluation point `z > 0`. -/
theorem abs_w_DzIter_le_open {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {i : ℕ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0))
    (hz : z ∈ Set.Ioi 0) (hM : 0 ≤ M) (hi : i ≤ 4)
    (hbound : ∀ k ≤ i, |w z * (z ^ k * pzIter k h z θ)| ≤ M) :
    |w z * DzIter i h z θ| ≤ 100 * M := by
  have h1 : w z * DzIter i h z θ
      = ∑ k ∈ Finset.range (i + 1),
          (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ)) := by
    rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hsmooth i z hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1]
  calc |∑ k ∈ Finset.range (i + 1), (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ))|
      ≤ (bell i : ℝ) * M := abs_sum_scoef_mul_le i M _ (fun k hk => hbound k hk)
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le i hi) hM

/-! ## The pointwise bound of the `ℋ⁴`-integrand in the open-quadrant class -/

/-- **The open-quadrant pointwise `ℋ⁴`-integrand bound.**  This is
`Work.FTS.H2.Q.hkIntegrand_le_Q` with the hypothesis `SmoothQuad f` replaced by
`SmoothOpen f`; the conclusion is identical. -/
theorem hkIntegrand_le_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {Wl : ℝ} (hWl : 0 ≤ Wl)
    (hA : ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * w z * z ^ m * pzIter m f z θ| ≤ 200000 * Wl)
    (hB : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ),
      θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * w z * z ^ l * pzIter l (DthIter i f) z θ|
        ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    ∀ (z : ℝ), z ∈ Iz → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      HkIntegrand α 4 f z θ
        ≤ Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
  intro z hz θ hθ
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθI
  by_cases hz0 : z = 0
  · subst hz0
    rw [HkIntegrand_apply_zero]
    have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(eta)) := Real.rpow_nonneg hsin _
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := Real.rpow_nonneg hsin _
    have h3 : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    have h4 : (0 : ℝ) ≤ 1 / (1 + 0) ^ 2 := by norm_num
    have h5 : (0 : ℝ) ≤ 2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
        + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) :=
      add_nonneg (mul_nonneg (by norm_num) h1)
        (mul_nonneg (by norm_num) (mul_nonneg h3 h2))
    exact mul_nonneg (mul_nonneg (sq_nonneg _) h4) h5
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have hzIoi : z ∈ Set.Ioi (0 : ℝ) := hzpos
    have hwnn : 0 ≤ w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsmoothf : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi 0) :=
      Work.FTS.OpenPkg.smoothOpen_slice_z hsm hθ
    have hsmoothD : ∀ (i : ℕ),
        ContDiffOn ℝ Work.Stability.smoothOrder (fun z => DthIter i f z θ) (Set.Ioi 0) :=
      fun i => Work.FTS.OpenPkg.smoothOpen_DthIter_slice_z hsm i hθ
    -- per-term bound: pure D_z-family
    have hZ : ∀ i ≤ 4,
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          ≤ (20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) := by
      intro i hi
      have hb : ∀ k ≤ i, |w z * (z ^ k * pzIter k f z θ)| ≤ 200000 * Wl / (1 + z) := by
        intro k hk
        have h1 := hA k (le_trans hk hi) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le k)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le k),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (w z * DzIter i f z θ) ^ 2 ≤ (20000000 * Wl / (1 + z)) ^ 2 := by
        have h2 : |w z * DzIter i f z θ| ≤ 100 * (200000 * Wl / (1 + z)) :=
          abs_w_DzIter_le_open hsmoothf hzIoi (by positivity) hi hb
        have h3 : |w z * DzIter i f z θ| ≤ 20000000 * Wl / (1 + z) := by
          convert h2 using 1; ring
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 20000000 * Wl / (1 + z))]
        exact h3
      rw [Work.Elliptic.sq_mul_div_sin hθI]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- angular bookkeeping for the mixed family
    have hsq5 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      have hne : α / 5 + α / 5 ≠ 0 := by intro h; have := hα; linarith
      rw [pow_two, Work.Elliptic.sin_two_rpow_mul' hθI hne,
        show α / 5 + α / 5 = 2 * α / 5 by ring]
    have hcomb : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        = (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := by
      have hne : 2 * α / 5 + -(gam α) ≠ 0 := by
        rw [gam]; intro h; linarith
      rw [hsq5, Work.Elliptic.sin_two_rpow_mul' hθI hne]
      ring_nf
    -- per-term bound: mixed family
    have hM : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 4 →
        (mixed j i f z θ * Wt α z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
      intro i j hi hij
      have hb : ∀ l ≤ j,
          |w z * (z ^ l * pzIter l (DthIter i f) z θ)|
            ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z) := by
        intro l hl
        have h1 := hB i l hi (by omega) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le l)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le l),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (w z * mixed j i f z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 := by
        have h2 : |w z * DzIter j (DthIter i f) z θ|
            ≤ 100 * (200000 * (Wl * ((α + Real.sin (2 * θ))
                * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) :=
          abs_w_DzIter_le_open (hsmoothD i) hzIoi (by positivity) (by omega) hb
        have h3 : |w z * mixed j i f z θ|
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z) := by
          rw [show mixed j i f = DzIter j (DthIter i f) from rfl]
          convert h2 using 1; ring
        rw [sq_le_sq,
          abs_of_nonneg (by positivity : (0 : ℝ)
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z))]
        exact h3
      have hWt : (mixed j i f z θ * Wt α z θ) ^ 2
          = (w z * mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
        rw [mul_pow, bt_Wt_sq α z θ hα hθI]
        ring
      rw [hWt]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- assemble the two sums
    rw [HkIntegrand]
    have hZsum : ∑ i ∈ Finset.range (4 + 1),
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta))) := by
      calc ∑ i ∈ Finset.range (4 + 1),
            (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (4 + 1),
              (20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) :=
            Finset.sum_le_sum fun i hi => hZ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = 5 * ((20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta))) := by
            rw [div_pow]; ring
    have hMsum : ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
        ≤ (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
      set Yv : ℝ := (20000000 * (Wl * ((α + Real.sin (2 * θ))
              * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(gam α)) with hYv
      have hYvnn : 0 ≤ Yv := by rw [hYv]; positivity
      calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), Yv := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases h : 1 ≤ i ∧ i + j ≤ 4
            · rw [if_pos h]; exact hM i j h.1 h.2
            · rw [if_neg h]; exact hYvnn
        _ = 25 * Yv := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
        _ = (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
            rw [hYv]
            have hexp :
                (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                    / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
                  = (20000000 : ℝ) ^ 2 * Wl ^ 2 * (α + Real.sin (2 * θ)) ^ 2 / (1 + z) ^ 2
                    * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(gam α))) := by
              rw [div_pow, mul_pow, mul_pow, mul_pow]
              ring
            rw [hexp, hcomb]
            ring
    calc ∑ i ∈ Finset.range (4 + 1),
            (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta)))
          + (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
              * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) :=
          add_le_add hZsum hMsum
      _ = Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by ring

end Work.FTS.OpenPkg.WtohWin
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Rational decay helpers -/

/-- `z^k/(1+z)^m → 0` for `k < m`: eventually equal to
`(z/(1+z))^k · ((1+z)^{-1})^{m-k}`, a product of a quantity tending to `1` and one to `0`. -/
theorem tendsto_pow_div_pow_atTop {k m : ℕ} (h : k < m) :
    Tendsto (fun z : ℝ => z ^ k / (1 + z) ^ m) atTop (𝓝 0) := by
  have hz1 : Tendsto (fun z : ℝ => (1 + z)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hinv : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hz1
  have hratio : Tendsto (fun z : ℝ => z / (1 + z)) atTop (𝓝 1) := by
    have hsub : Tendsto (fun z : ℝ => 1 - (1 + z)⁻¹) atTop (𝓝 (1 - 0)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    have h1 : (1 : ℝ) + z ≠ 0 := by linarith
    rw [div_eq_mul_inv]
    field_simp
    ring
  have hzero : Tendsto (fun z : ℝ => ((1 + z)⁻¹) ^ (m - k)) atTop (𝓝 0) := by
    have hp := hinv.pow (m - k)
    rw [zero_pow (by omega : m - k ≠ 0)] at hp
    exact hp
  have hprod : Tendsto (fun z : ℝ => (z / (1 + z)) ^ k * ((1 + z)⁻¹) ^ (m - k)) atTop (𝓝 0) := by
    have hh := (hratio.pow k).mul hzero
    simpa using hh
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
  have h1 : (1 : ℝ) + z ≠ 0 := by linarith
  rw [div_pow, inv_pow, div_eq_mul_inv, mul_assoc, ← mul_inv, ← pow_add,
    Nat.add_sub_cancel' h.le, div_eq_mul_inv]

/-! ## The angular moment of `Γ̄` -/


/-- **The moment condition of the angular model**: `∫_0^{π/2} Γ̄(θ) sin θ cos²θ dθ = 0`, where
`Γ̄ = Γ/c − (5/4) sin 2θ`.  This is the solvability condition of `L₀ψ = Γ̄` with Dirichlet data
(`sin θ cos²θ` spans the kernel of the formal adjoint of `L₀`), and it is also what makes the
remainder source `α²(𝒜φ)ψ` orthogonal to `sin θ cos²θ`. -/
theorem GamBar_moment {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.VocabO.GamBar α θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hGK : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := Work.Spaces.CAux.integrableOn_GamK α hα
  have hsin : IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ := by
      simp only [Work.Elliptic.sinCos2]; fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hpt : ∀ θ : ℝ, Work.FTS.VocabO.GamBar α θ * Work.Elliptic.sinCos2 θ
      = (1 / (3 * Work.Spaces.c α)) * (Work.Spaces.Gam α θ * Work.Spaces.K θ)
        - (5 / 4) * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    intro θ
    rw [Work.FTS.VocabO.GamBar, Work.Spaces.K, Work.Elliptic.sinCos2]
    field_simp
  rw [setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc fun θ _ => hpt θ]
  rw [integral_sub (hGK.const_mul _) (hsin.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ)
        = Work.Spaces.c α from rfl, Work.Elliptic.integral_sin_two_mul_sinCos2]
  have hone : (1 / (3 * Work.Spaces.c α)) * Work.Spaces.c α = 1 / 3 := by
    field_simp
  rw [hone]
  norm_num

/-! ## The profile `φ` and the source `𝒜φ` -/





/-- `φ(z) → 0` as `z → ∞`. -/
theorem tendsto_phiR_atTop : Tendsto Work.FTS.VocabO.phiR atTop (𝓝 0) := by
  have h := (tendsto_pow_div_pow_atTop (k := 1) (m := 2) (by norm_num)).const_mul (2 : ℝ)
  rw [mul_zero] at h
  have hfe : (fun z : ℝ => 2 * (z ^ 1 / (1 + z) ^ 2)) = Work.FTS.VocabO.phiR := by
    funext z; rw [Work.FTS.VocabO.phiR, pow_one]; ring
  rwa [hfe] at h

/-- The derivative of `φ`: `φ'(z) = 2(1−z)/(1+z)³`. -/
theorem deriv_phiR {z : ℝ} (hz : z ≠ -1) :
    deriv Work.FTS.VocabO.phiR z = 2 * (1 - z) / (1 + z) ^ 3 := by
  have hden : (1 + z) ≠ 0 := by
    intro h; exact hz (by linarith)
  have hnum : HasDerivAt (fun z : ℝ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
  have hden' : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h1.pow 2
    convert h2 using 1
    ring
  change deriv ((fun z : ℝ => 2 * z) / fun z => (1 + z) ^ 2) z = 2 * (1 - z) / (1 + z) ^ 3
  rw [(hnum.div hden' (pow_ne_zero 2 hden)).deriv]
  field_simp
  ring

/-- The derivative of `z ↦ 2(1−z)/(1+z)³`: `4(z−2)/(1+z)⁴`. -/
theorem deriv_phiR' {z : ℝ} (hz : z ≠ -1) :
    deriv (fun z : ℝ => 2 * (1 - z) / (1 + z) ^ 3) z = 4 * (z - 2) / (1 + z) ^ 4 := by
  have hden : (1 + z) ≠ 0 := by
    intro h; exact hz (by linarith)
  have hnum : HasDerivAt (fun z : ℝ => 2 * (1 - z)) (-2 : ℝ) z := by
    have h1 : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).const_sub 1
    have h2 := h1.const_mul (2 : ℝ)
    convert h2 using 1
    ring
  have hden' : HasDerivAt (fun z : ℝ => (1 + z) ^ 3) (3 * (1 + z) ^ 2) z := by
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h1.pow 3
    convert h2 using 1
    ring
  change deriv ((fun z : ℝ => 2 * (1 - z)) / fun z => (1 + z) ^ 3) z
      = 4 * (z - 2) / (1 + z) ^ 4
  rw [(hnum.div hden' (pow_ne_zero 3 hden)).deriv]
  field_simp
  ring

/-- The second derivative of `φ`: `φ''(z) = 4(z−2)/(1+z)⁴`. -/
theorem iteratedDeriv_two_phiR {z : ℝ} (hz : z ≠ -1) :
    iteratedDeriv 2 Work.FTS.VocabO.phiR z = 4 * (z - 2) / (1 + z) ^ 4 := by
  have hopen : ∀ᶠ z' in 𝓝 z, z' ≠ -1 := by
    filter_upwards [isOpen_ne.mem_nhds (show z ≠ -1 from hz)] with z' hz'
    exact hz'
  have hderiv : deriv Work.FTS.VocabO.phiR
      =ᶠ[𝓝 z] fun z' => 2 * (1 - z') / (1 + z') ^ 3 := by
    filter_upwards [hopen] with z' hz'
    exact deriv_phiR hz'
  have h2 : iteratedDeriv 2 Work.FTS.VocabO.phiR = deriv (deriv Work.FTS.VocabO.phiR) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, hderiv.deriv_eq]
  exact deriv_phiR' hz

/-- **The explicit form of `𝒜φ = α z²φ'' + (5+α) z φ'`**. -/
theorem phiA_eq (α z : ℝ) (hz : z ≠ -1) :
    Work.FTS.VocabO.phiA α z
      = 4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3 := by
  rw [Work.FTS.VocabO.phiA, iteratedDeriv_two_phiR hz, deriv_phiR hz]
  ring

/-- The source coefficient `𝒜φ` is bounded by `20` on `z ≥ 0`, uniformly for `0 < α ≤ 1`. -/
theorem phiA_abs_le {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) :
    |Work.FTS.VocabO.phiA α z| ≤ 20 := by
  have hz1 : z ≠ -1 := by intro h; rw [h] at hz; norm_num at hz
  have hp : (0 : ℝ) < 1 + z := by linarith
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  have habs1 : |z - 2| ≤ z + 2 := by rw [abs_le]; constructor <;> linarith [hz]
  have habs2 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith [hz]
  have hP : z ^ 2 * (z + 2) ≤ 2 * (1 + z) ^ 4 := by
    have hexp : 2 * (1 + z) ^ 4 - z ^ 2 * (z + 2)
        = 2 * z ^ 4 + 7 * z ^ 3 + 10 * z ^ 2 + 8 * z + 2 := by ring
    have hkey : (0 : ℝ) ≤ 2 * z ^ 4 + 7 * z ^ 3 + 10 * z ^ 2 + 8 * z + 2 := by positivity
    linarith
  have hQ : z * (1 + z) ≤ (1 + z) ^ 3 := by
    have hexp : (1 + z) ^ 3 - z * (1 + z) = (1 + z) * (1 + z + z ^ 2) := by ring
    have hkey : (0 : ℝ) ≤ (1 + z) * (1 + z + z ^ 2) := by positivity
    linarith
  have hnum1 : 4 * α * z ^ 2 * |z - 2| ≤ 8 * (1 + z) ^ 4 := by
    have h5 : z ^ 2 * |z - 2| ≤ z ^ 2 * (z + 2) := mul_le_mul_of_nonneg_left habs1 hz2
    have h6 : 4 * α * (z ^ 2 * |z - 2|) ≤ 4 * α * (2 * (1 + z) ^ 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h7 : 4 * α * (2 * (1 + z) ^ 4) ≤ 8 * (1 + z) ^ 4 := by
      have h8 : α * (8 * (1 + z) ^ 4) ≤ 1 * (8 * (1 + z) ^ 4) :=
        mul_le_mul_of_nonneg_right hα1 (by positivity)
      linarith
    calc 4 * α * z ^ 2 * |z - 2| = 4 * α * (z ^ 2 * |z - 2|) := by ring
      _ ≤ 4 * α * (2 * (1 + z) ^ 4) := h6
      _ ≤ 8 * (1 + z) ^ 4 := h7
  have hnum2 : 2 * (5 + α) * z * |1 - z| ≤ 12 * (1 + z) ^ 3 := by
    have hsa : 2 * (5 + α) ≤ 12 := by linarith
    have hzab : z * |1 - z| ≤ z * (1 + z) := mul_le_mul_of_nonneg_left habs2 hz
    have h6 : 2 * (5 + α) * z * |1 - z| ≤ 12 * (z * (1 + z)) := by
      have hh : 2 * (5 + α) * (z * |1 - z|) ≤ 12 * (z * (1 + z)) :=
        mul_le_mul hsa hzab (by positivity) (by positivity)
      calc 2 * (5 + α) * z * |1 - z| = 2 * (5 + α) * (z * |1 - z|) := by ring
        _ ≤ 12 * (z * (1 + z)) := hh
    have h7 : 12 * (z * (1 + z)) ≤ 12 * (1 + z) ^ 3 :=
      mul_le_mul_of_nonneg_left hQ (by norm_num)
    linarith
  have h4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have h3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hterm1 : |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| ≤ 8 := by
    rw [abs_div, abs_of_pos h4, div_le_iff₀ h4]
    have habs : |4 * α * z ^ 2 * (z - 2)| = 4 * α * z ^ 2 * |z - 2| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg hz2]
    rw [habs]
    exact hnum1
  have hterm2 : |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| ≤ 12 := by
    rw [abs_div, abs_of_pos h3, div_le_iff₀ h3]
    have habs : |2 * (5 + α) * z * (1 - z)| = 2 * (5 + α) * z * |1 - z| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg hz]
    rw [habs]
    exact hnum2
  rw [phiA_eq α z hz1]
  calc |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3|
      ≤ |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4|
        + |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| := abs_add_le _ _
    _ ≤ 20 := by linarith



/-! ## The moment of the profile, and the singular part -/


/-- `L₁₂(F_*)(z) = 2α/(1+z)` for `z ≥ 0`. -/
theorem L12_profile_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
  Work.Construction.L12_Fstar_eq hα hα1 hz

/-- The singular part `Θ = (1/4α) sin 2θ L₁₂(F_*)` is the explicit
`ThetaProfile z · sin 2θ = sin 2θ/(2(1+z))`. -/
theorem Theta_eq_thetaProfile {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 ≤ z)
    (θ : ℝ) :
    Work.Construction.Theta α (Work.Construction.Fstar α) z θ
      = ThetaProfile z * Real.sin (2 * θ) := by
  rw [Work.Construction.Theta, Work.Construction.s2, L12_profile_eq hα hα1 hz, ThetaProfile]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hz1 : (1 + z) ≠ 0 := by linarith
  field_simp
  ring

/-! ## The structural decomposition of `bslOp` on separable products -/

/-- `∂_z(A(z)·ψ(θ)) = A'(z)·ψ(θ)` (unconditional in `A`). -/
theorem pz_sep (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => A z * ψ θ) z θ = deriv A z * ψ θ := by
  rw [Work.Spaces.pz]
  exact Work.Spaces.deriv_mul_const' (ψ θ) z A

/-- `∂_z²(A(z)·ψ(θ)) = A''(z)·ψ(θ)` (unconditional in `A`). -/
theorem pzIter_two_sep (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter 2 (fun z θ => A z * ψ θ) z θ = iteratedDeriv 2 A z * ψ θ := by
  have h2 : iteratedDeriv 2 A z = deriv (deriv A) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : Work.Spaces.pzIter 2 (fun z θ => A z * ψ θ)
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => A z * ψ θ)) := rfl
  rw [h2, h1, Work.Spaces.pz]
  have hfun : (fun z' : ℝ => Work.Spaces.pz (fun z θ => A z * ψ θ) z' θ)
      = fun z' : ℝ => deriv A z' * ψ θ := by
    funext z'; exact pz_sep A ψ z' θ
  rw [hfun]
  exact Work.Spaces.deriv_mul_const' (ψ θ) z (deriv A)

/-- `∂_θ²(A(z)·ψ(θ)) = A(z)·ψ''(θ)`. -/
theorem pthIter_two_sep (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => A z * ψ θ) z θ
      = A z * deriv (fun θ' => deriv ψ θ') θ := by
  have h1 : Work.Spaces.pthIter 2 (fun z θ => A z * ψ θ)
      = Work.Spaces.pth (Work.Spaces.pth (fun z θ => A z * ψ θ)) := rfl
  rw [h1, Work.Spaces.pth]
  have hfun : (fun θ' : ℝ => Work.Spaces.pth (fun z θ => A z * ψ θ) z θ')
      = fun θ' : ℝ => A z * deriv ψ θ' := by
    funext θ'
    rw [Work.Spaces.pth]
    exact Work.Spaces.deriv_const_mul' (A z) θ' ψ
  rw [hfun, Work.Spaces.deriv_const_mul' (A z) θ (deriv ψ)]

/-- `L₀(A(z)ψ(θ)) = A(z)·L₀ψ(θ)`: the `θ`-operator does not see the radial factor. -/
theorem Lzero_sep (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun z θ => A z * ψ θ) z θ
      = A z * Work.FTS.EllipticEst.Lzero1 ψ θ := by
  have hmid : Work.Spaces.pth (fun z θ => Real.tan θ * (A z * ψ θ)) z θ
      = A z * deriv (fun θ' => Real.tan θ' * ψ θ') θ := by
    rw [Work.Spaces.pth]
    have hfun : (fun θ' : ℝ => Real.tan θ' * (A z * ψ θ'))
        = fun θ' : ℝ => A z * (Real.tan θ' * ψ θ') := by
      funext θ'; ring
    rw [hfun]
    exact Work.Spaces.deriv_const_mul' (A z) θ (fun θ' => Real.tan θ' * ψ θ')
  rw [Work.Elliptic.Lzero, pthIter_two_sep, hmid, Work.FTS.EllipticEst.Lzero1]
  ring

/-- **The separable decomposition of `bslOp`** (the algebraic core of the telescoping
identity): for `Ψ(z,θ) = A(z)·ψ(θ)`,
`bslOp α Ψ = A(z)·L₀ψ(θ) − (α z²A''(z) + (5+α) z A'(z))·ψ(θ)`. -/
theorem bslOp_sep (α : ℝ) (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp α (fun z θ => A z * ψ θ) z θ
      = A z * Work.FTS.EllipticEst.Lzero1 ψ θ
        - (α ^ 2 * z ^ 2 * iteratedDeriv 2 A z + α * (5 + α) * z * deriv A z) * ψ θ := by
  rw [Work.Elliptic.bslOp_apply, pzIter_two_sep, pz_sep, Lzero_sep]
  ring

/-- **The radial specialisation**: for `Ψ(z,θ) = A(z)·sin 2θ`,
`bslOp α Ψ = −(α z²A'' + (5+α) z A')·sin 2θ` (`sin 2θ` lies in the kernel of `L₀`). -/
theorem bslOp_radial (α : ℝ) (A : ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (fun z θ => A z * Real.sin (2 * θ)) z θ
      = -(α ^ 2 * z ^ 2 * iteratedDeriv 2 A z + α * (5 + α) * z * deriv A z)
          * Real.sin (2 * θ) := by
  rw [Work.Elliptic.bslOp_apply, pzIter_two_sep, pz_sep,
    Work.Elliptic.Lzero_sin_two_mul A z θ hθ]
  ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.H2.T1Q.SliceSupOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.T1Q

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The slicewise `L^∞`-`L²` estimate on the open angular interval.**  For `1 < γ ≤ 2` and
`u : ℝ → ℝ` of class `C¹` on the open interval `(0,π/2)`, with `u²` and
`(u')² sin(2θ)^{2-γ}` integrable (over `Iθ = [0,π/2]`), and for every `θ ∈ (0,π/2)`:

`u(θ)² ≤ (4/π)·∫_{Iθ} u² + (200/(γ-1))·∫_{Iθ} (u')² sin(2θ)^{2-γ}`.

This is `Work.FTS.H2.slice_sup_sq_le` (in `Submission/Work/FTS/H2/SupThetaInt.lean`) with the
regularity weakened from `ContDiffOn ℝ 1 u (Ioo (-1) (π/2+1))` (a neighbourhood of the *closed*
interval) to `ContDiffOn ℝ 1 u (Ioo 0 (π/2))` (the open interval), and with the conclusion
claimed only at the interior points `θ ∈ (0,π/2)`.  Route: `MeasureTheory.exists_le_setAverage`
on the set `Set.Ioo 0 (π/2)` (nonempty, finite measure) produces a point `θ₀ ∈ (0,π/2)` with
`u(θ₀)² ≤ (2/π)∫_{Ioo} u² = (2/π)∫_{Iθ} u²`; combine `u(θ)² ≤ 2u(θ₀)² + 2(u(θ)-u(θ₀))²` with
the oscillation bound `Work.FTS.H2.OscSqLe` applied on `uIcc θ θ₀ ⊆ (0,π/2)`. -/
theorem SliceSupOpen : ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
    ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ →
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (u θ) ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        + (200 / (Work.Spaces.gam α - 1)) * ∫ θ in Work.Spaces.Iθ,
            (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  intro α u hα hα1 hdiff hu2 hint
  -- Step 1: a point `θ₀ ∈ (0,π/2)` where `u²` is below its mean, via `exists_le_setAverage`.
  have hs : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hintIoo : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu2.mono_set hs
  have hvol : volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp only [sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have htop : volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  obtain ⟨θ₀, hθ₀, hle⟩ := MeasureTheory.exists_le_setAverage hvol htop hintIoo
  have havg : ⨍ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x) ^ 2
      = (2 / Real.pi) * ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x) ^ 2 := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def, Real.volume_Ioo]
    simp only [sub_zero, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      smul_eq_mul]
    congr 1
    field_simp
  rw [havg] at hle
  have hmono : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x) ^ 2)
      ≤ ∫ x in Work.Spaces.Iθ, (u x) ^ 2 := by
    refine MeasureTheory.setIntegral_mono_set hu2 ?_ ?_
    · exact Filter.Eventually.of_forall fun x => by positivity
    · exact Filter.Eventually.of_forall fun x hx => hs hx
  have hθ₀le : (u θ₀) ^ 2 ≤ (2 / Real.pi) * ∫ x in Work.Spaces.Iθ, (u x) ^ 2 := by
    calc (u θ₀) ^ 2 ≤ (2 / Real.pi) * ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x) ^ 2 := hle
      _ ≤ (2 / Real.pi) * ∫ x in Work.Spaces.Iθ, (u x) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hmono
          positivity
  intro θ hθ
  -- Step 2: the oscillation bound `OscSqLe` for `h = u` between `θ` and `θ₀`.
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hθ₀Iθ : θ₀ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ₀.1, le_of_lt hθ₀.2⟩
  have hsub : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc]
    intro x hx
    refine ⟨lt_of_lt_of_le (lt_min hθ.1 hθ₀.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt hθ.2 hθ₀.2)⟩
  have hder : ∀ x ∈ Set.uIcc θ θ₀, HasDerivAt u (deriv u x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hsub hx
    have hd : DifferentiableAt ℝ u x :=
      (hdiff.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx')
    exact hd.hasDerivAt
  have hcont : ContinuousOn (deriv u) (Set.uIcc θ θ₀) :=
    (hdiff.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  have hosc := Work.FTS.H2.OscSqLe α hα hα1 u hθIθ hθ₀Iθ hder hcont hint
  -- Step 3: `u θ = (u θ - u θ₀) + u θ₀` and the elementary square bound `add_sq_le`.
  have hsq : (u θ) ^ 2 ≤ 2 * (u θ - u θ₀) ^ 2 + 2 * (u θ₀) ^ 2 := by
    have h : ((u θ - u θ₀) + u θ₀) ^ 2 ≤ 2 * ((u θ - u θ₀) ^ 2 + (u θ₀) ^ 2) := add_sq_le
    have e : u θ = (u θ - u θ₀) + u θ₀ := by ring
    rw [e]
    linarith
  calc (u θ) ^ 2
      ≤ 2 * (u θ - u θ₀) ^ 2 + 2 * (u θ₀) ^ 2 := hsq
    _ ≤ 2 * ((100 / (Work.Spaces.gam α - 1)) *
          ∫ σ in Work.Spaces.Iθ,
            (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        + 2 * ((2 / Real.pi) * ∫ σ in Work.Spaces.Iθ, (u σ) ^ 2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hosc (by norm_num)
        · exact mul_le_mul_of_nonneg_left hθ₀le (by norm_num)
    _ = (4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (u σ) ^ 2)
        + (200 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
            (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
        ring

end Work.H2.T1Q
end
-- ===== merged: Submission.Work.H2.T1Q.SupAbsThOAesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

/-- The supremum of `|u z θ|` over the *rational* points of the open interval `(0,π/2)`, written
as a countable supremum of the values `|u z q|` (and `0` at the rationals outside the interval, so
that the index type stays `ℚ`, which is `Countable` and `Nonempty`). -/
def supRatAbs (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ⨆ (q : ℚ), (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) then |u z ((q : ℚ) : ℝ)| else 0)

/-- A countable supremum of almost-everywhere strongly measurable functions is almost-everywhere
strongly measurable; here each summand `if q ∈ (0,π/2) then |u z q| else 0` is either the
absolutely continuous image of the hypothesis `z ↦ u z q` or a constant. -/
lemma supRatAbs_aemeasurable {u : ℝ → ℝ → ℝ}
    (hmeas : ∀ q : ℚ, ((q : ℝ) ∈ Set.Ioo 0 (π / 2)) →
      AEMeasurable (fun z => u z (q : ℝ)) (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    AEMeasurable (supRatAbs u) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  unfold supRatAbs
  refine AEMeasurable.iSup (fun q : ℚ => ?_)
  by_cases hq : ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
  · have h1 : (fun z : ℝ => (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
        then |u z ((q : ℚ) : ℝ)| else 0)) = fun z => |u z ((q : ℚ) : ℝ)| := by
      funext z; rw [ite_eq_left hq]
    rw [h1]
    exact (hmeas q hq).abs
  · have h1 : (fun z : ℝ => (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
        then |u z ((q : ℚ) : ℝ)| else 0)) = fun _ => (0 : ℝ) := by
      funext z; rw [ite_eq_right hq]
    rw [h1]
    exact aemeasurable_const

/-- The rationals of the *open* interval `(0,π/2)` come arbitrarily close to any point of that
interval: a rational can be found in `(θ/2, θ) ∩ (θ-δ, θ+δ)`. -/
lemma exists_rat_mem_Ioo_near {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ, ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) ∧ |((q : ℚ) : ℝ) - θ| < δ := by
  have hθpos : 0 < θ := hθ.1
  have hθlt : θ < π / 2 := hθ.2
  have hη : 0 < min δ (θ / 2) := lt_min hδ (by linarith)
  have hlt : θ - min δ (θ / 2) < θ := by linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · have h : θ / 2 ≤ θ - min δ (θ / 2) := by
      have := min_le_right δ (θ / 2); linarith
    linarith
  · linarith
  · rw [abs_lt]
    exact ⟨by linarith [min_le_left δ (θ / 2), hδ],
      by linarith [min_le_left δ (θ / 2)]⟩

/-- On a slice where `θ ↦ u z θ` is continuous (and where the range of `|u z ·|` is bounded
above), the supremum over the open interval agrees with the supremum over its rational points. -/
lemma supAbsThO_eq_supRatAbs {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hcont : ContinuousOn (fun θ => u z θ) (Set.Ioo 0 (π / 2)))
    (hbdd : BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|}) :
    Work.FTS.H2.supAbsThO u z = supRatAbs u z := by
  have hmem4 : π / 4 ∈ Set.Ioo 0 (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmem45 : |u z (π / 4)| ∈ {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|} :=
    ⟨π / 4, hmem4, rfl⟩
  have hSne : ({y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|} : Set ℝ).Nonempty :=
    ⟨_, hmem45⟩
  have hCnn : 0 ≤ Work.FTS.H2.supAbsThO u z := by
    have h : |u z (π / 4)| ≤ Work.FTS.H2.supAbsThO u z := le_csSup hbdd hmem45
    exact le_trans (abs_nonneg _) h
  have hBddG : BddAbove (Set.range (fun q : ℚ =>
      (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) then |u z ((q : ℚ) : ℝ)| else 0))) := by
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨max C 0, ?_⟩
    rintro y ⟨q, rfl⟩
    show (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) then |u z ((q : ℚ) : ℝ)| else 0) ≤ max C 0
    by_cases hq : ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
    · rw [ite_eq_left hq]; exact le_trans (hC ⟨_, hq, rfl⟩) (le_max_left _ _)
    · rw [ite_eq_right hq]; exact le_max_right _ _
  refine le_antisymm ?_ ?_
  · unfold Work.FTS.H2.supAbsThO
    refine csSup_le hSne (fun y hy => ?_)
    obtain ⟨θ, hθ, rfl⟩ := hy
    by_contra hcon
    rw [not_le] at hcon
    have hε : 0 < (|u z θ| - supRatAbs u z) / 2 := by linarith
    have hcont' : ContinuousOn (fun θ => |u z θ|) (Set.Ioo 0 (π / 2)) := hcont.abs
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousOn_iff.mp hcont') θ hθ ((|u z θ| - supRatAbs u z) / 2) hε
    obtain ⟨q, hqIoo, hqdist⟩ := exists_rat_mem_Ioo_near hθ hδpos
    have h1 : |u z ((q : ℚ) : ℝ)| ≤ supRatAbs u z := by
      have hle := le_ciSup hBddG q
      rwa [ite_eq_left hqIoo] at hle
    have h2 : dist (|u z ((q : ℚ) : ℝ)|) (|u z θ|) < (|u z θ| - supRatAbs u z) / 2 :=
      hδ ((q : ℚ) : ℝ) hqIoo (by rw [Real.dist_eq]; exact hqdist)
    rw [Real.dist_eq, abs_sub_comm] at h2
    have h3 : |u z θ| ≤ abs (|u z θ| - |u z ((q : ℚ) : ℝ)|) + |u z ((q : ℚ) : ℝ)| := by
      have := le_abs_self (|u z θ| - |u z ((q : ℚ) : ℝ)|); linarith
    linarith
  · unfold supRatAbs
    refine ciSup_le (fun q => ?_)
    show (if ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2) then |u z ((q : ℚ) : ℝ)| else 0)
      ≤ Work.FTS.H2.supAbsThO u z
    by_cases hq : ((q : ℚ) : ℝ) ∈ Set.Ioo 0 (π / 2)
    · rw [ite_eq_left hq]
      exact le_csSup hbdd ⟨_, hq, rfl⟩
    · rw [ite_eq_right hq]
      exact hCnn


end Work.H2.T1Q
end
end
