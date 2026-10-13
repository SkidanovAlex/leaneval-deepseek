/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H6Pair6Aux/T5bAux2` — the Leibniz expansion of the row `T5bRow`

On the open quadrant the Leibniz rule (`T5bAux/mixedRadialThetaMul` together with the shift
`D_z^bD_θ^a(D_z f) = D_z^{b+1}D_θ^a f`) expands the differentiated coefficient as

`D_z^bD_θ^a(c₂ₘ(θ)·L₁₂(f)(z)·D_z f)
   = Σ_{k ≤ b} Σ_{i ≤ a} C(b,k)C(a,i)·(D_z^kL₁₂(f))(z)·(D_θ^ic₂ₘ)(θ)·D_z^{b-k+1}D_θ^{a-i}f`,

so the slot pairing of the row is a finite sum of the summands `t5bPiece f ρ a b k i`. -/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.mixedRadialThetaMul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **The Leibniz expansion of `D_z^bD_θ^a(c₂ₘ·L₁₂(f)·D_z f)`** on the open quadrant. -/
theorem t5bExpand {f : ℝ → ℝ → ℝ} {a b : ℕ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hCsm : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Work.Construction.c2m θ))
    (hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0))
    (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
        * Work.Spaces.Dz f z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ))
              * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                  * (Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ
                      * Work.Spaces.mixed (b - k + 1) (a - i) f z θ)) := by
  intro z θ hz hθ0 hθ1
  have hb : b ≤ 6 := by omega
  have hbase := Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.mixedRadialThetaMul
    (X := fun z => Work.Construction.L12 f z) (γ := Work.Construction.c2m)
    (f := Work.Spaces.Dz f) hXsm hCsm hso.Dz b a hb z θ hz hθ0 hθ1
  have hfun : (fun z θ : ℝ => Work.Construction.c2m θ * Work.Construction.L12 f z
        * Work.Spaces.Dz f z θ)
      = fun z θ : ℝ => Work.Construction.L12 f z
          * (Work.Construction.c2m θ * Work.Spaces.Dz f z θ) := by
    funext z θ
    ring
  rw [hfun, hbase]
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun i hi => ?_
  rw [mixedDzShift hso (b - k) (a - i) hz hθ0 hθ1]

/-- **The paired form of the expansion**: the integrand of the slot pairing of the row, as the
finite sum of the `t5bPiece` summands. -/
theorem t5bPairExpand {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hCsm : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Work.Construction.c2m θ))
    (hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0))
    (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * Work.Spaces.mixed b a (fun z θ => Work.Construction.c2m θ
          * Work.Construction.L12 f z * Work.Spaces.Dz f z θ) z θ
        * Work.Spaces.mixed b a f z θ
        = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ)) * t5bPiece f ρ a b k i (z, θ) := by
  intro z θ hz hθ0 hθ1
  rw [t5bExpand hso hCsm hXsm hab z θ hz hθ0 hθ1, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [t5bPiece]
  ring

end Work.FTS.StrongPersist.H6Pair6Aux
