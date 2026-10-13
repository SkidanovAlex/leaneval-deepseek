import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.AngClean.IPMem_F_Phi
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross
import Submission.Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `remov/AeIPMemsSlim` — the six `IPMem` honesties of the Step 2 identity, in the a.e. class

`Work.FTS.EllipticEst.H2W.AeWAux.aeIPMems` proves
`Work.FTS.EllipticEst.AngAWeak.AeIPMems` (the six cross-honesties of
`AngAWeak.Basic.I_identity_weak`) but imports `Honest.honCrossIPMems`, which in turn pulls in
`EllHyp_certificates` and the whole `Cert/` interface — an import cone of ~670 modules that is
irrelevant to the argument.  This module re-proves the same statement with the *minimal*
imports: the only ingredients are

* `AngClean.HkMem_zero_IPMem` (the diagonal honesty `HkMem α 0 g ⟹ IPMem g g`),
* `AngClean.IPMem_of_diag_aesm` (the polarisation `|g h| ≤ g² + h²`),
* the a.e. strong measurability of the mixed integrand off the boundary of the quadrant
  (`Honest.AesmCross.aesmSliceCross`, `aesmProdCross`, which need only `SmoothOpen`
  representatives and `AgreeOnQ`),
* `RPFresh.HkMem_of_agreeOnQ`, `FTS.LocData.HkMem_const_mul`, `SmoothOpenAdd.smoothOpen_add`,
  `HkIntegrand_add_le_open` + `LocData.HkMem_of_majorant` (for the honesty of the sums below),
* `remov.SmoothOpen_bslOp_of_smoothOpen` and `Cert.SmoothOpen_bslOp` for the `SmoothOpen`
  certificates of the profiles.

The content is a verbatim re-run of `aeIPMems`'s argument: every one of the six profiles is
`HkMem α 0` and agrees on the open quadrant with a `C^∞` profile, and the only profile which is
not a field of `AeData` is the angular term `∂_θ(tan θ·u)`, whose honesty follows from the
equation rewritten as
`∂_θ(tan θ·u) = (∂_θ²u + 6u) + ((bslOp α u + α²z²∂_zzu) + α(5+α)z∂_zu)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- Scalar multiples of `SmoothOpen` functions are `SmoothOpen`.  (A local copy of
`RPFresh.smoothOpen_const_mul`, whose module drags in the `Cert/` interface.) -/
theorem smoothOpen_const_mul_ae {c : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hf ⊢
  have h : (Function.uncurry fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

/-- **`ℋ^k` is closed under addition** for `SmoothOpen` data.  (A local copy of
`RPFresh.HkMem_add_open`, whose module drags in the `Cert/` interface.) -/
theorem hkMem_add_open_ae (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
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
  · have htarget : IntegrableOn (fun z : ℝ => 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) + 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)) Work.Spaces.Iz :=
      (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
    refine Integrable.congr htarget ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    exact Work.FTS.EllipticEst.HkIntegrand_add_le_open α k hf hg hz hθ

/-- **Cross honesty from the two diagonal honesties and open-quadrant smoothness.**  (A local
copy of `Honest.IPMem_of_HkMem_agreeOnQ`, whose module drags in the `Cert/` interface.) -/
theorem ipMem_of_HkMem_agreeOnQ_ae {α : ℝ} {g h g' h' : ℝ → ℝ → ℝ}
    (hg' : Work.FTS.EllipticEst.SmoothOpen g') (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h')
    (hmg : Work.Spaces.HkMem α 0 g) (hmh : Work.Spaces.HkMem α 0 h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h :=
  Work.FTS.EllipticEst.AngClean.IPMem_of_diag_aesm
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmg)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmh)
    (fun z hz => Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross hg' hh' hgg hhh z hz)
    (Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross hg' hh' hgg hhh)

/-- **The `IPMem` bookkeeping of the Step 2 identity in the class `AeData`**: the six pairings
occurring in `AngAWeak.Basic.I_identity_weak` against `B = ∂_θθu` are honest. -/
theorem aeIPMemsSlim : Work.FTS.EllipticEst.AngAWeak.AeIPMems := by
  intro α u G hA hmu hmuU
  have hα : 0 < α := hA.hα
  -- ### The `SmoothOpen` representatives of the profiles
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hA.smooth
  have hBS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) :=
    (huS.pth).pth
  have hQS : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter huS 2)
  have hUS : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pz huS)
  have hG1S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl huS)
  have hGop : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen huS
  have hGagree : Work.FTS.EllipticEst.AgreeOnQ G (Work.Elliptic.bslOp α u) :=
    fun z θ hz hθ0 hθ1 => (hA.eq z hz θ hθ0 hθ1).symm
  -- ### The honesty of the summands of `∂_θ(tan θ·u)`
  have hmBsl : Work.Spaces.HkMem α 0 (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ hGagree hA.memG
  have h6uS : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 6 * u z θ) :=
    smoothOpen_const_mul_ae huS
  have h6u : Work.Spaces.HkMem α 0 (fun z θ => 6 * u z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 6 hmu
  have h1S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pthIter 2 u z θ + 6 * u z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hBS h6uS
  have h1 : Work.Spaces.HkMem α 0 (fun z θ => Work.Spaces.pthIter 2 u z θ + 6 * u z θ) :=
    hkMem_add_open_ae α 0 hBS h6uS hA.memAng2 h6u
  have hα2QS : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    smoothOpen_const_mul_ae hQS
  have hα2Q : Work.Spaces.HkMem α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α ^ 2) hA.memRad2
  have h2S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add hGop hα2QS
  have h2 : Work.Spaces.HkMem α 0
      (fun z θ => Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    hkMem_add_open_ae α 0 hGop hα2QS hmBsl hα2Q
  have hαUS : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α * (5 + α) * (z * Work.Spaces.pz u z θ)) :=
    smoothOpen_const_mul_ae hUS
  have hαU : Work.Spaces.HkMem α 0 (fun z θ => α * (5 + α) * (z * Work.Spaces.pz u z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α * (5 + α)) hmuU
  have h3S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        + α * (5 + α) * (z * Work.Spaces.pz u z θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add h2S hαUS
  have h3 : Work.Spaces.HkMem α 0
      (fun z θ => (Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        + α * (5 + α) * (z * Work.Spaces.pz u z θ)) :=
    hkMem_add_open_ae α 0 h2S hαUS h2 hαU
  have h4S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Spaces.pthIter 2 u z θ + 6 * u z θ)
        + ((Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          + α * (5 + α) * (z * Work.Spaces.pz u z θ))) :=
    Work.FTS.EllipticEst.smoothOpen_add h1S h3S
  have h4 : Work.Spaces.HkMem α 0
      (fun z θ => (Work.Spaces.pthIter 2 u z θ + 6 * u z θ)
        + ((Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          + α * (5 + α) * (z * Work.Spaces.pz u z θ))) :=
    hkMem_add_open_ae α 0 h1S h3S h1 h3
  -- ### The equation identifies the sum with `∂_θ(tan θ·u)` on the open quadrant
  have hG1agree : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => (Work.Spaces.pthIter 2 u z θ + 6 * u z θ)
        + ((Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          + α * (5 + α) * (z * Work.Spaces.pz u z θ)))
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ) := by
    intro z θ _hz _hθ0 _hθ1
    simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
    ring
  have hmG1 : Work.Spaces.HkMem α 0
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ hG1agree h4
  -- ### The six pairings
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ipMem_of_HkMem_agreeOnQ_ae hGop hBS hGagree
      (fun _ _ _ _ _ => rfl) hA.memG hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae hQS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hA.memRad2 hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae hUS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hmuU hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae hG1S hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hmG1 hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae huS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hmu hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae hBS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hA.memAng2 hA.memAng2

end Work.FTS.EllipticEst.remov
