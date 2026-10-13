/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Cores/DiagEstEllT/StraightMem` — the layers of the straightened datum in `EllHypT`

The straightening of Elgindi's *RemovingL12* replaces `Ψ` by

  `V := Ψ + Gsing α F · sin 2θ`,

which solves `bslOp α V = orthSource F` and is orthogonal to `sinθcos²θ` (`OrthCond V` is the
hypothesis of the theorem `Cores/DiagEst_ellT`).  This module collects the two structural facts
about `V` that the class membership of `V` (and hence any application of the a-priori `ℋ^k`
estimate to it) needs, in the trace-free class `EllHypT`:

* `honest_Gsing_eq_neg_fstar_Psi` — the orthogonality condition pins the singular term down:
  `Gsing α F z = -(15/4)·F_*(Ψ) z` for every `z > 0` (`Cores.Fstar_eq_neg_Gsing` + the slice
  integrability from `HkMem α 0 Ψ`);
* `honest_HkMem_gsing_sin` — hence `Gsing α F · sin 2θ ∈ ℋ^k`, because `HkIntegrand` depends only
  on the *function*, and `-((15/4) F_*(Ψ)) · sin 2θ ∈ ℋ^k` is the layer certificate
  `Cert.HkMem_Fstar_sin_open` applied to `Ψ` (whose `HkMem α k Ψ` is a field of `EllHypT`).

The interest of the second statement: `F_*(F)` itself is only `C^{k-1}` in this class, so the
layer `F_*(F)·sin 2θ` is *not* smooth; but the orthogonality condition replaces
`Gsing α F = Gstar + Gbar` by a multiple of `F_*(Ψ)`, and *that* layer is honest, which is what
the membership of `V` needs.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.FiniteFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The straightened datum `V = Ψ + Gsing α F · sin 2θ` of Theorem `RemovingL12`. -/
abbrev Vfts (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)

/-- **The orthogonality condition pins the singular term to `-(15/4) F_*(Ψ)`.** -/
theorem honest_Gsing_eq_neg_fstar_Psi {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vfts α F Ψ)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.Gsing α F z = -(15 / 4) * Work.Elliptic.Fstar Ψ z := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ := honest_smoothOpen_Psi h
  have hmem0 : Work.Spaces.HkMem α 0 Ψ :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (Nat.zero_le k)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨso) h.memPsi
  intro z hz
  have hint : IntegrableOn (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 (α := α)
      hΨso.continuousOn hmem0 hz
  have h' := Work.FTS.EllipticEst.Cores.Fstar_eq_neg_Gsing (F := F) hint hOrth
  linarith [h']

/-- **The layer `Gsing α F · sin 2θ` is honestly in `ℋ^k`** in the trace-free class, under the
orthogonality condition. -/
theorem honest_HkMem_gsing_sin {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vfts α F Ψ)) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) := by
  have hα1 : α ≤ 1 := by linarith
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ := honest_smoothOpen_Psi h
  have hmem : Work.Spaces.HkMem α k
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-(15 / 4))
      (Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k Ψ hα hα1 hΨso h.memPsi)
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hmem ?_
  intro z hz θ _
  have hgs := honest_Gsing_eq_neg_fstar_Psi hα h hOrth z hz
  rw [hgs]; ring

end Work.FTS.EllipticEst.Cores.DiagEstEllT
