import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.Core.thetaDerivDescent
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.ThetaU.PthHkIntegrandLeOpen
import Submission.Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace
import Submission.Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `D_z ∂_θ V ∈ ℋ^k` from `D_z ∂_θ² V ∈ ℋ^k`

This module proves `Work.FTS.EllSol.PkgK5.HkMem_Dz_pth_of_diag`: on the open quadrant
`(0,∞) × (0,π/2)`, the *angular Hardy/Poincaré descent*

  `D_z ∂_θ² V ∈ ℋ^k  ⟹  D_z ∂_θ V ∈ ℋ^k`

for `V` of class `C^∞` on the open quadrant whose angular `D_z`-slices `D_z^j V z ·`
(`j ≤ k+1`, `z > 0`) vanish at both endpoints `θ = 0, π/2` in the sense of *limits*, and with
`D_z ∂_θ²V` honestly in `ℋ^k` (`0 < α ≤ 1/4`).

## Route

Both `D_z` and `∂_θ` only see the *open* quadrant, and on it they commute (Clairaut):

  `∂_θ (D_z^j V) = D_z^j (∂_θ V)`      (`ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen`),

so, as functions on `(0,∞) × (0,π/2)`,

  `∂_θ² (D_z V) = ∂_θ (D_z (∂_θ V)) = D_z (∂_θ² V)`,
  `∂_θ (D_z V) = D_z (∂_θ V)`.

Since `ℋ^k`-membership only depends on the values on the open quadrant
(`RPFresh.HkMem_of_agreeOnQ`), the assertion is therefore the *per-slice* angular Poincaré
descent for the single function `f := D_z V`:

  `∂_θ² f ∈ ℋ^k  ⟹  ∂_θ f ∈ ℋ^k`,

which is `VopAux.thetaPoincareOpenTrace`, the trace (limit) form of the angular
Hardy inequality `∫ |∂_θ f|²  ≲ ∫ |∂_θ² f|²` — the vanishing of the angular slices of
`D_z^j f = D_z^{j+1} V` at `θ = 0, π/2` for `j ≤ k` being exactly the hypothesis on `V` at
levels `≤ k+1`.

Everything rests on `[propext, Classical.choice, Quot.sound]`: the three inputs
`thetaPoincareOpenTrace`, `HkMem_of_agreeOnQ` and `pth_DzIter_eqOn_of_isOpen` are
`sorry`-free.
-/

namespace Work.FTS.EllSol.PkgK5

set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Auxiliary facts -/

/-- Composition of `DzIter` with the outermost `D_z`: `D_z^j (D_z V) = D_z^{j+1} V`. -/
private lemma DzIter_Dz_eq (j : ℕ) (V : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz V) = Work.Spaces.DzIter (j + 1) V := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Work.Spaces.DzIter_succ]; exact congrArg Work.Spaces.Dz ih

/-- `AgreeOnQ` from an `EqOn` on the open quadrant. -/
private lemma agreeOnQ_of_eqOn_Q0 {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    Work.FTS.EllipticEst.AgreeOnQ F G :=
  fun z θ hz hθ hlt => h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩)

/-- `AgreeOnQ` is symmetric (it is an equality on the open quadrant). -/
private lemma agreeOnQ_symm {F G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.AgreeOnQ F G) :
    Work.FTS.EllipticEst.AgreeOnQ G F :=
  fun z θ hz hθ hlt => (h z θ hz hθ hlt).symm

/-- `AgreeOnQ` is transitive (it is an equality on the open quadrant). -/
private lemma agreeOnQ_trans {F G H : ℝ → ℝ → ℝ} (h1 : Work.FTS.EllipticEst.AgreeOnQ F G)
    (h2 : Work.FTS.EllipticEst.AgreeOnQ G H) : Work.FTS.EllipticEst.AgreeOnQ F H :=
  fun z θ hz hθ hlt => (h1 z θ hz hθ hlt).trans (h2 z θ hz hθ hlt)

theorem HkMem_Dz_pth_of_diag (k : ℕ) (hk : 1 ≤ k) :
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pthIter 2 V)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) := by
  intro α V hα0 hα4 hV hV0 hVpi htr hmem
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace k
  -- `V` and `∂_θV` are `C^n` on the open quadrant for every `n`
  have hsmV : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry V) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall hV
  have hsmPthV : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth V))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall (Work.FTS.EllipticEst.SmoothOpen.pth hV)
  -- Clairaut on the open quadrant: `∂_θ (D_z V) = D_z (∂_θ V)`
  have hcl1 : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pth (Work.Spaces.Dz V))
      (Work.Spaces.Dz (Work.Spaces.pth V)) :=
    agreeOnQ_of_eqOn_Q0
      (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
        Work.FTS.EllipticEst.isOpen_Q0 hsmV 1)
  -- and `∂_θ (D_z (∂_θ V)) = D_z (∂_θ² V)`
  have hcl2 : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth V)))
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth V))) :=
    agreeOnQ_of_eqOn_Q0
      (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
        Work.FTS.EllipticEst.isOpen_Q0 hsmPthV 1)
  -- hence `pth (pth (Dz V))` and `pth (Dz (pth V))` agree too
  have hcl1p : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz V)))
      (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth V))) := hcl1.pth
  -- Step 1: `D_z ∂_θ²V ∈ ℋ^k` implies `∂_θ² (D_z V) ∈ ℋ^k` (same function off the null set)
  have hmemA : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Spaces.Dz V)) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ
      (agreeOnQ_trans (agreeOnQ_symm hcl2) (agreeOnQ_symm hcl1p)) hmem
  -- Step 2: the trace hypothesis for `D_z V` (`DzIter j (Dz V) = DzIter (j+1) V`)
  have htr' : ∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz V) z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Spaces.Dz V) z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro j hj z hz
    have h := htr (j + 1) (by omega) z hz
    simpa only [DzIter_Dz_eq j V] using h
  have hsmDzV : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz V))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall (Work.FTS.EllipticEst.SmoothOpen.Dz hV)
  -- Step 3: the angular Poincaré descent for `f := D_z V`
  have hB : Work.Spaces.HkMem α k (Work.Spaces.pth (Work.Spaces.Dz V)) :=
    (hC α (Work.Spaces.Dz V) hα0 hα4 hsmDzV htr' hmemA).2.1
  -- Step 4: transport back across the open quadrant, `∂_θ (D_z V) = D_z (∂_θ V)`
  exact Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ hcl1 hB

end Work.FTS.EllSol.PkgK5
