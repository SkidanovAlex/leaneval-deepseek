import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Cert.GbarLayer.Target
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The layer certificate**: the singular part `Ḡ(α,F)·sin 2θ` attached to the source `F` of a
solution `Ψ` of the elliptic problem lies in `ℋ^k`, with an `H^k`-norm bounded by
`C_k |F|_{H^k}` for a constant `C_k > 0` depending only on `k` (in particular independent of
`α ∈ (0,1/4]`).

The membership `Ḡ·sin 2θ ∈ ℋ^k` is `GbarLayer.layer_HkMem_Gbar_sin`.  For the norm bound it
suffices to treat the *open-quadrant* representative `bslOp α Ψ` of the source, because

* `F_*(F) = F_*(bslOp α Ψ)` on `(0,∞)` (`GbarLayer.layer_Fstar_bslOp_eq_of_sol`), hence
  `Ḡ(α,F) = Ḡ(α,bslOp α Ψ)` on `(0,∞)` (`GbarLayer.Gbar_congr`), so the two targets agree on the
  open quadrant and have equal `H^k`-squares (`HkSq_congr_open`);
* `F = bslOp α Ψ` on the open quadrant, so the same congruence applies to the sources;

and `bslOp α Ψ` is `C^∞` on the open quadrant (`SmoothOpen_bslOp`) and in `ℋ^k`
(`HkMem_congr_Q0`), which is exactly the hypothesis of `GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen`.
-/
theorem GbarSin_layer (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  obtain ⟨C, hC, hbound⟩ := GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen k
  refine ⟨C, hC, fun α F Ψ hα hα4 hHyp => ⟨?_, ?_⟩⟩
  · exact GbarLayer.layer_HkMem_Gbar_sin α k F Ψ hα hα4 hHyp
  · have hα1 : α ≤ 1 := by linarith
    -- the open-quadrant representative `bslOp α Ψ` of the source
    -- (`EllHyp.smooth` is `SmoothInt`, not `SmoothNbhd`: use the `SmoothInt` variant)
    have hSmooth : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
      SmoothOpen_bslOp_int α Ψ hHyp.smooth
    have hMem : Work.Spaces.HkMem α k (Work.Elliptic.bslOp α Ψ) :=
      GbarSin.HkMem_congr_Q0 α k hHyp.memF fun z hz θ hθ =>
        (hHyp.sol.1 z hz θ hθ.1 hθ.2).symm
    have hb := hbound α (Work.Elliptic.bslOp α Ψ) hα hα1 hSmooth hMem
    -- the `H^k`-squares of the sources agree
    have hsrc : Work.Spaces.HkSq α k F
        = Work.Spaces.HkSq α k (Work.Elliptic.bslOp α Ψ) :=
      Work.FTS.EllipticEst.HkSq_congr_open α k
        (fun z θ hz hθ hlt => (hHyp.sol.1 z hz θ hθ hlt).symm)
    -- and so do the `H^k`-squares of the targets
    have hfs : ∀ s, 0 < s →
        Work.Elliptic.Fstar F s = Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) s :=
      GbarLayer.layer_Fstar_bslOp_eq_of_sol α hHyp.sol
    have htgt : Work.Spaces.HkSq α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        = Work.Spaces.HkSq α k
          (fun z θ => Work.Elliptic.Gbar α (Work.Elliptic.bslOp α Ψ) z
            * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α k
        (fun z θ hz _ _ => by rw [GbarLayer.Gbar_congr α hfs z hz])
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, htgt, hsrc]
    exact hb

end Work.FTS.EllipticEst.Cert
