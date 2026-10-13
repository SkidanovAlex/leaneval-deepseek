import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- **The finite-order Leibniz rule for `D_θ` against an angular coefficient.**

`D_θ = sin(2θ) ∂_θ` is a derivation on `θ`-slices, so its `i`-th iterate of a product
`(z,θ) ↦ c θ · X z θ` (coefficient depending on `θ` alone) expands binomially:

`D_θ^i (c·X) = ∑_{k≤i} C(i,k) · (D_θ^k c) · (D_θ^{i-k} X)` on the open quadrant `Q0`,

as soon as the two factors are `C^i` on `Q0`.  (The hypothesis is deliberately finite-order:
the analytic-order Leibniz rule `Work.Spaces.DthIter_mul` requires `C^ω` and is not applicable
to merely `C^i` data.)

This is the `j = 0` instance of the mixed Leibniz rule `mixed_mul_fin`
(`Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin`): `mixed 0 i` is `D_θ^i` by definition, and
a coefficient which does not depend on `z` has vanishing `D_z`-jets. -/
theorem dthIter_coef_mul_eqOn {i : ℕ} {c : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ i (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hc : ContDiffOn ℝ i (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => c θ * X z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ * Work.Spaces.DthIter (i - k) X z θ)))
      Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  -- The coefficient `(z,θ) ↦ c θ` and `X` are `C^i` on `Q0`; `mixed_mul_fin` with `j = 0`
  -- asks for `C^{0+i}`, which is the same regularity (`0 + i = i`).
  have hf : ContDiffOn ℝ (↑(0 : ℕ) + ↑i) (Function.uncurry (fun z θ : ℝ => c θ))
      Work.FTS.EllipticEst.Q0 := by
    rw [Nat.cast_zero, zero_add]
    change ContDiffOn ℝ (↑i) (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0
    exact hc
  have hg : ContDiffOn ℝ (↑(0 : ℕ) + ↑i) (Function.uncurry X) Work.FTS.EllipticEst.Q0 := by
    rw [Nat.cast_zero, zero_add]
    exact hX
  have h := Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin (j := 0) (i := i)
      (f := fun z θ => c θ) (g := X) (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 hf hg z θ hp
  -- `mixed 0 i` is `D_θ^i`, so the two sides now have the same shape.
  change Work.Spaces.mixed 0 i (fun z θ => c θ * X z θ) z θ
      = ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ * Work.Spaces.DthIter (i - k) X z θ)
  rw [h]
  -- Collapse the inner `range (0+1)`-sum (only `b = 0` survives) and clear the
  -- binomial coefficient `(0 choose 0) = 1`.
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_range_one]
  simp only [Work.Spaces.mixed_zero_left, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one]
  ring

end Work.FTS_RegExport.RXT.Slots.JetCalc
