/-
Copyright: work module for the Elgindi finite-time singularity project.

# Leibniz rules for a `z`-only multiplier on the open quadrant

Support module for `EpsE4Thr/E2hat_HkSq_le_uniform_O.lean` (the open-class port of the
`α`-uniform `ℋⁿ`-bound for the `D_z`-commutator defect `Ê₂`).

Here we collect the smoothness closure facts for `SmoothOpen` and the mixed Leibniz expansion

  `D_z^j D_θ^i (ψ·x) = ∑_{b ≤ j} C(j,b)·(Zop^b ψ)(z)·(D_z^{j-b}D_θ^i x)(z,θ)`

for a `z`-only factor `ψ` that is merely `C^∞` on `(0,∞)` and a datum `x` that is `C^∞` on the
*open* quadrant (`SmoothOpen`).  This is the open-class replacement of the frozen
`CoercivityFix.E2Bound.mixed_zmul`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalFields.Norm.radLeibniz
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.Spaces.MixedMulDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2hatOAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `φ(z) = z/(1+z)²` is `C^∞` on the positive half-line. -/
lemma phiZ_contDiffOn : ∀ m : ℕ,
    ContDiffOn ℝ m (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) := by
  intro m
  refine ContDiffOn.div (by fun_prop) (by fun_prop) ?_
  intro z hz
  exact pow_ne_zero 2 (by have hz' : (0 : ℝ) < z := hz; linarith)

/-- A function of `z` alone, `C^∞` on `(0,∞)`, is `SmoothOpen` as a function of `(z,θ)`. -/
lemma smoothOpen_zOnly {ψ : ℝ → ℝ}
    (hψ : ∀ m : ℕ, ContDiffOn ℝ m ψ (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => ψ z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have hfun : Function.uncurry (fun z _ : ℝ => ψ z) = fun p : ℝ × ℝ => ψ p.1 := rfl
  rw [hfun]
  exact (hψ n).comp contDiffOn_fst (fun p hp => (Set.mem_prod.mp hp).1)

/-- `SmoothOpen` is closed under multiplication. -/
lemma smoothOpen_mul {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [hfun]
  exact hf.mul hg

/-- `SmoothOpen` is closed under multiplication by a constant. -/
lemma smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => c * f z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ : ℝ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [hfun]
  exact ContDiffOn.mul (contDiffOn_const (c := c)) hf

/-- **Mixed Leibniz expansion (open quadrant) of a product with a `z`-only factor.**  For
`ψ : ℝ → ℝ` of class `C^∞` on `(0,∞)` and `x` of class `SmoothOpen` (`C^∞` on the open
quadrant `(0,∞) × (0,π/2)`), and for `z > 0`, `θ ∈ (0,π/2)`,
`D_z^j D_θ^i (ψ·x) = ∑_{b ≤ j} C(j,b)·(Zop^b ψ)(z)·(D_z^{j-b}D_θ^i x)(z,θ)`.

`D_θ^i` commutes with the `z`-only factor `ψ` (`GalFields.Norm.DthIter_zmul_rad`, which needs
no smoothness), reducing the claim to the graded `Zop`-Leibniz rule on the `z`-slice
(`GalFields.Norm.Zop_iter_mul_contDiffOn`), where both factors are `C^{j+1}` on `(0,∞)`. -/
theorem mixed_zmul_SO (j i : ℕ) (ψ : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hψ : ∀ m : ℕ, ContDiffOn ℝ m ψ (Set.Ioi 0))
    (hx : Work.FTS.EllipticEst.SmoothOpen x)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.mixed j i (fun z θ : ℝ => ψ z * x z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] ψ z * Work.Spaces.mixed (j - b) i x z θ) := by
  have hψj : ContDiffOn ℝ (((j + 1 : ℕ)) : WithTop ℕ∞) ψ (Set.Ioi (0 : ℝ)) := hψ (j + 1)
  have hgj : ContDiffOn ℝ (((j + 1 : ℕ)) : WithTop ℕ∞)
      (fun z : ℝ => Work.Spaces.DthIter i x z θ) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.GalFields.Norm.curry_z_nat_of_smoothOpen (hx.DthIter i) hθ (j + 1)
  have hL : Work.Spaces.mixed j i (fun z θ : ℝ => ψ z * x z θ) z θ
      = Work.Spaces.Zop^[j] (ψ * fun z : ℝ => Work.Spaces.DthIter i x z θ) z := by
    show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ : ℝ => ψ z * x z θ)) z θ
      = Work.Spaces.Zop^[j] (ψ * fun z : ℝ => Work.Spaces.DthIter i x z θ) z
    rw [Work.FTS.GalFields.Norm.DthIter_zmul_rad i ψ x]
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice j
      (fun z θ => ψ z * Work.Spaces.DthIter i x z θ) θ) z
  rw [hL, Work.FTS.GalFields.Norm.Zop_iter_mul_contDiffOn isOpen_Ioi hψj hgj z hz]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hstep : Work.Spaces.Zop^[j - b] (fun z : ℝ => Work.Spaces.DthIter i x z θ) z
      = Work.Spaces.mixed (j - b) i x z θ :=
    (congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b) (Work.Spaces.DthIter i x) θ) z).symm
  rw [hstep]

/-- The `D_z`-only instance of `mixed_zmul_SO`. -/
theorem DzIter_zmul_SO (j : ℕ) (ψ : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hψ : ∀ m : ℕ, ContDiffOn ℝ m ψ (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.DzIter j (fun z θ => ψ z * f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] ψ z * Work.Spaces.DzIter (j - b) f z θ) := by
  simpa only [Work.Spaces.mixed_zero_right] using mixed_zmul_SO j 0 ψ f hψ hf hz hθ

end Work.FTS.StrongEps.EpsE4Thr.E2hatOAux
