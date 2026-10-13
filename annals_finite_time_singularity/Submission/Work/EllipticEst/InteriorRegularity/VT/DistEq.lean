/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): the distributional form of the localized
equation, i.e. the transcription of the pairing identity `VT.localEquationLoc` (the weak identity
tested against `χ · φ`, with the cut-off data `χ' ≡ 1`, `σ ≡ 1`, `tt ≡ tan θ` on an open set
`U ⊇ tsupport χ`) into the shape required by `gain_step`.

This is the `VT` instance of the abstract distributional identity `Q0.distEq` of the sibling
`Q0` workstream, whose `Pair`/`LocalId` hypotheses decouple the integration bookkeeping from the
distributional algebra.
-/
import Mathlib.Analysis.Distribution.TemperedDistribution
import Submission.Work.EllipticEst.InteriorRegularity.VT.VInteg
import Submission.Work.EllipticEst.InteriorRegularity.VT.DerivAux
import Submission.Work.EllipticEst.InteriorRegularity.VT.localEquationLoc
import Submission.Work.EllipticEst.InteriorRegularity.Q0.distEq

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
