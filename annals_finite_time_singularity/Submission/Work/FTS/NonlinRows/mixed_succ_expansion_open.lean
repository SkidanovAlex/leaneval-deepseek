import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The angular multiplier `θ ↦ sin(2θ)`, as a function on `(z,θ)` (notation for the
`Sfun` of `Work.FTS.TransportS`). -/
local notation "Sfn" => Work.FTS.TransportS.Sfun

/-- **The angular commutator expansion, on the open quadrant.**  For `g` of class `SmoothOpen`
(`C^∞` on `(0,∞) × (0,π/2)`) and `z > 0`, `θ ∈ (0,π/2)`, the `(i+1)`-st angular iterate of `g`
equals the `sin(2θ)`-multiple of the `i`-th iterate of `∂_θ g` plus the lower-order commutator
corrections:

  `D_z^j D_θ^{i+1} g = sin(2θ)·D_z^j D_θ^i(∂_θ g)
      + Σ_{r<i} C(i,r+1)·L^{r+1}(sin 2·)(θ)·D_z^j D_θ^{i-r-1}(∂_θ g)`,

where `L = D_θ = sin(2θ)·∂_θ`.  This is the open-quadrant (`SmoothOpen`) analogue of
`Work.FTS.H2.mixed_succ_expansion` (which asks for analyticity of `g` on a neighbourhood of the
closed quadrant). -/
theorem mixed_succ_expansion_open (g : ℝ → ℝ → ℝ) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed j (i + 1) g z θ
      = Real.sin (2 * θ) * Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
        + ∑ r ∈ Finset.range i,
            (((i.choose (r + 1) : ℝ)
                * Work.FTS.EllipticEst.LopIter (r + 1) (fun t : ℝ => Real.sin (2 * t)) θ)
              * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ) := by
  classical
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  -- the Leibniz expansion of `D_θ^i (sin 2· · ∂_θ g)` on the open quadrant
  have hLeib : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      Work.Spaces.DthIter i (fun a b => Sfn a b * Work.Spaces.pth g a b) z' θ'
        = ∑ r ∈ Finset.range (i + 1),
            ((i.choose r : ℝ)
                * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ')
              * Work.Spaces.DthIter (i - r) (Work.Spaces.pth g) z' θ' := by
    intro z' θ' hz' hθ' hθ'1
    have hf : ∀ c ≤ i, DifferentiableOn ℝ
        (fun θ'' => Work.Spaces.DthIter c Sfn z' θ'') (Set.Ioo 0 (π / 2)) := fun c _ =>
      ((Work.FTS.TransportS.Sfun_smoothOpen.DthIter c).curry_θ hz').differentiableOn (by simp)
    have hpg : ∀ c ≤ i, DifferentiableOn ℝ
        (fun θ'' => Work.Spaces.DthIter c (Work.Spaces.pth g) z' θ'')
        (Set.Ioo 0 (π / 2)) := fun c _ =>
      (((hg.pth).DthIter c).curry_θ hz').differentiableOn (by simp)
    rw [Work.FTS.TransportS.DthIter_mul_eq_of_diffOn i Sfn (Work.Spaces.pth g)
      ⟨hθ', hθ'1⟩ hf hpg]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Work.FTS.TransportS.DthIter_Sfun_eq_LopIter r z' θ']
    ring
  -- `mixed j (i+1) g` is `D_z^j` of that Leibniz sum
  have hmixed : Work.Spaces.mixed j (i + 1) g z θ
      = Work.Spaces.DzIter j (fun z θ => ∑ r ∈ Finset.range (i + 1),
            ((i.choose r : ℝ)
                * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
              * Work.Spaces.DthIter (i - r) (Work.Spaces.pth g) z θ) z θ := by
    rw [show Work.Spaces.mixed j (i + 1) g
          = Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) g) from rfl,
      Work.FTS.TransportS.DthIter_shift]
    have hdth : Work.Spaces.Dth g = fun a b => Sfn a b * Work.Spaces.pth g a b := rfl
    rw [hdth]
    exact Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter i (fun a b => Sfn a b * Work.Spaces.pth g a b))
      (G := fun z θ => ∑ r ∈ Finset.range (i + 1),
            ((i.choose r : ℝ)
                * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
              * Work.Spaces.DthIter (i - r) (Work.Spaces.pth g) z θ) hLeib j z θ hz hθ0 hθ1
  -- `D_z^j` is distributed termwise
  have hstep3 : Work.Spaces.DzIter j (fun z θ => ∑ r ∈ Finset.range (i + 1),
        ((i.choose r : ℝ)
            * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
          * Work.Spaces.DthIter (i - r) (Work.Spaces.pth g) z θ) z θ
      = ∑ r ∈ Finset.range (i + 1),
          ((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.mixed j (i - r) (Work.Spaces.pth g) z θ :=
    Work.FTS.TransportS.DzIter_sum_const_mul (Finset.range (i + 1))
      (fun r θ => (i.choose r : ℝ)
        * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
      (fun r => Work.Spaces.DthIter (i - r) (Work.Spaces.pth g))
      (fun r _ => (hg.pth).DthIter (i - r)) j hz hθ0 hθ1
  -- the `r = 0` term of the Leibniz sum, which is the `sin(2θ)`-multiple of `D_z^j D_θ^i(∂_θ g)`
  have hfirst : ((i.choose 0 : ℝ)
        * Work.FTS.EllipticEst.LopIter 0 (fun t : ℝ => Real.sin (2 * t)) θ)
        * Work.Spaces.mixed j (i - 0) (Work.Spaces.pth g) z θ
      = Real.sin (2 * θ) * Work.Spaces.mixed j i (Work.Spaces.pth g) z θ := by
    simp
  rw [hmixed, hstep3, Finset.sum_range_succ', hfirst]
  exact add_comm _ _

end Work.FTS.NonlinRows
