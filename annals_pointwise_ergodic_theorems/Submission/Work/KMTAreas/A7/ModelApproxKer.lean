/-
# The §5 pieces as convolution kernels

The §5 pieces `Fpiece`, `Gpiece` of `Work.Analysis.EndVar` are *differences of Ionescu--Wainger
projections* of `f`, hence (by `Work.KMTAreas.A5.kmtProj_eq_conv`, which identifies `kmtProj` with
the convolution with its kernel `kmtKern`) linear convolutions of `f` with an explicit kernel.
This module fixes that kernel and records the identification, so that the concrete halved average
`varpPiece = AhalfR TZ N X P (Fpiece …) (Gpiece …)` becomes a bilinear convolution
`bilinOp (khalf ⌊N⌋ P) (convOp κ_F f) (convOp κ_G g)`, and -- composed with the linear kernels
through `kernComp` (`BilinOpKhalf`, `ModelApproxCore_kernelComp`) -- a single bilinear convolution
`bilinOp K_1 (f, g)`.  The §6 model operator likewise becomes `bilinOp K_2 (f, g)`, so that the
single-scale model approximation is exactly the estimate of the `ℓ¹(ℤ²)` mass of `K_1 - K_2`
(via `Work.KMTAreas.A7.BilinOpLp`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTAreas.A5.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTAreas.A5

/-- The exact-height Ionescu--Wainger projection `Π_{l,≤k}` of §5 as a convolution kernel
(`Π_{l,≤k} = Π_{≤l,≤k} - Π_{≤l-1,≤k}`, with `Π_{≤-1,≤k} = 0`). -/
noncomputable def exactKer (ρ : ℝ) (l : ℕ) (k : ℤ) : ℤ → ℂ :=
  if l = 0 then kmtKern ρ 0 k else kmtKern ρ l k - kmtKern ρ (l - 1) k

/-- The continuous frequency piece of §5 as a convolution kernel: the combination of exact-height
projections appearing in `piece`. -/
noncomputable def pieceKer (ρ : ℝ) (l : ℕ) (κs : ℤ → ℤ) (a s : ℤ) : ℤ → ℂ :=
  if s = a then exactKer ρ l (κs s) else exactKer ρ l (κs s) - exactKer ρ l (κs (s - 1))

/-! ## The identifications (delegated)

The two identifications
`Fpiece (kmtPj ρ) 0 l₁ k₁ N f = convOp (pieceKer ρ l₁ (fun s => -(logN N) + s) 0 k₁) f` and the
`Gpiece` analogue are *not* true for an arbitrary (unbounded) `f`: both sides are unconditional
`tsum`s and Mathlib's `tsum` is `0` on non-summable families, whereas the left-hand sides are
differences of up to four such `tsum`s (see `Submission/Work/KMTAreas/A7/FpieceEqTm.lean`, whose
header refutes the corresponding form of the func-calculus identity for unbounded `f`).  They are
delegated as `Work.A7.ModelApproxCore_Fpiece_convOp` and `Work.A7.ModelApproxCore_Gpiece_convOp`
with the hypothesis `BoundedZ f`, which is exactly the case needed here: for `f ∈ ℓ^{p₁}`
(`1 < p₁`) boundedness is free (`Work.KMTAreas.A5.boundedZ_of_memLp`), and for `f ∉ ℓ^{p₁}` both
sides of the target estimate are trivial. -/

end

end Work.KMTAreas.A7
