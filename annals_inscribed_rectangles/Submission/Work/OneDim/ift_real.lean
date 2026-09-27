import Mathlib

open scoped Manifold ContDiff
open Set Filter

namespace Work.OneDim

/-- The inverse function theorem in dimension one, in the form used by the Whitney embedding
proof: a `C^∞` map `ℝ → ℝ` whose derivative vanishes nowhere is a local diffeomorphism.

For every `x` we take the `n`-th order inverse function theorem in the model space `ℝ`
(`ContDiffAt.toOpenPartialHomeomorph`), which exhibits `f` near `x` as an open partial
homeomorphism whose inverse is again `C^∞`.  Global smoothness of `f` together with the
non-vanishing of `deriv f` upgrades the pointwise `ContDiffAt` statement for the inverse to
`ContDiffOn` on the whole target.  Finally the manifold structure on `ℝ` is the self model
`modelWithCornersSelf ℝ ℝ`, so `ContDiffOn` on `ℝ` is `ContMDiffOn`. -/
theorem ift_real {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf' : ∀ x, deriv f x ≠ 0) :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ∞ f := by
  intro x
  have hn : (∞ : ℕ∞ω) ≠ 0 := by decide
  have hd : HasDerivAt f (deriv f x) x := ((hf.differentiable hn).differentiableAt).hasDerivAt
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv f x) (hf' x))
  have hfd : HasFDerivAt f (e : ℝ →L[ℝ] ℝ) x := hd.hasFDerivAt_equiv (hf' x)
  have hcat : ContDiffAt ℝ ∞ f x := hf.contDiffAt
  let Φ : OpenPartialHomeomorph ℝ ℝ := hcat.toOpenPartialHomeomorph f hfd hn
  have hmem : x ∈ Φ.source := hcat.mem_toOpenPartialHomeomorph_source hfd hn
  have hsymm : ContDiffOn ℝ ∞ Φ.invFun Φ.target := by
    intro b hb
    have hdb : HasDerivAt f (deriv f (Φ.invFun b)) (Φ.invFun b) :=
      ((hf.differentiable hn).differentiableAt).hasDerivAt
    have hfdb : HasFDerivAt f
        ((ContinuousLinearEquiv.unitsEquivAut ℝ
            (Units.mk0 (deriv f (Φ.invFun b)) (hf' _)) : ℝ →L[ℝ] ℝ))
        (Φ.invFun b) := hdb.hasFDerivAt_equiv (hf' _)
    have hc : ContDiffAt ℝ ∞ f (Φ.invFun b) := hf.contDiffAt
    exact (Φ.contDiffAt_symm hb hfdb hc).contDiffWithinAt
  let dif : PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ ∞ :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := ContDiffOn.contMDiffOn (hf.contDiffOn (s := Φ.source))
      contMDiffOn_invFun := ContDiffOn.contMDiffOn hsymm }
  exact ⟨dif, hmem, fun _ _ => rfl⟩

end Work.OneDim
