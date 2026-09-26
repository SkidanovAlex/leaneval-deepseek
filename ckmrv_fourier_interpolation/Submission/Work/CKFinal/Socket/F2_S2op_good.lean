import Mathlib
import Submission.Work.CKFinal.Socket.Construction
import Submission.Work.CKFinal.Socket.F2_agree_U0
import Submission.Work.CKFinal.S2op_paperLayer

namespace Work.CKFinal.Socket

open UpperHalfPlane

/-! ## `S(T-I)²` only reads a function at the three `S`-shifted points

`Work.Asymptotics.S2op_apply_eq` writes `S2op k f τ` as the second difference of the slash
`f ∣[k] S` at `τ`, `τ+1`, `τ+2`, and `Work.Kernels.slash_S_apply` evaluates that slash as
`σ ↦ f (S • σ) · σ^{-k}`.  Hence `S2op k · τ` depends on `f` only through the values of `f` at
`S • τ`, `S • (τ+1)` and `S • (τ+2)`: -/

lemma S2op_congr_three (k : ℤ) {f g : ℍ → ℂ} {τ : ℍ}
    (h0 : f (ModularGroup.S • τ) = g (ModularGroup.S • τ))
    (h1 : f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) = g (ModularGroup.S • ((1 : ℝ) +ᵥ τ)))
    (h2 : f (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) = g (ModularGroup.S • ((2 : ℝ) +ᵥ τ))) :
    Work.Asymptotics.S2op k f τ = Work.Asymptotics.S2op k g τ := by
  rw [Work.Asymptotics.S2op_apply_eq k f τ, Work.Asymptotics.S2op_apply_eq k g τ]
  simp only [Work.Kernels.slash_S_apply]
  rw [h0, h1, h2]

/-- **`S(T-I)²` annihilates the socket layer `F₂` at a good point `τ`.**

The hypotheses say that the three points `S • τ`, `S • (τ+1)`, `S • (τ+2)` at which `S(T-I)²`
reads a function land in the open set `U₀`, and that the `SL(2,ℤ)`-orbit of `S • τ` misses the
imaginary axis.  Since `j` is `SL(2,ℤ)`-invariant the same cleanliness holds at `τ` itself, so
`S2op_paperLayer` gives `S(T-I)² layerFn = 0` at `τ` for the paper layer; and by
`S2op_congr_three` we may replace `layerFn` by `F₂`, because `F2_agree_U0` identifies the two on
`U₀` and that is exactly where the three points lie. -/
theorem F2_S2op_good (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    {τ : UpperHalfPlane}
    (h0 : ModularGroup.S • τ ∈ Work.CKFinal.U0) (h1 : ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ Work.CKFinal.U0)
    (h2 : ModularGroup.S • ((2 : ℝ) +ᵥ τ) ∈ Work.CKFinal.U0)
    (hc0 : ∀ (t : ℝ) (ht : 0 < t), Work.Kernels.jInvariantFun (ModularGroup.S • τ)
      ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.CKFinal.Socket.F2 ℓ d hd r) τ = 0 := by
  -- `j` is `SL(2,ℤ)`-invariant, so cleanliness at `S • τ` is cleanliness at `τ`
  have hclean : ∀ (t : ℝ) (ht : 0 < t), Work.Kernels.jInvariantFun τ ≠
      Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht h
    exact hc0 t ht (by rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul]; exact h)
  -- the paper layer is annihilated at the clean point
  have hpl : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (Work.CKFinal.Socket.layerFn ℓ d r) τ = 0 :=
    Work.CKFinal.S2op_paperLayer ℓ d hd r τ hclean
  -- on the three points at which `S(T-I)²` reads, `F₂` coincides with the layer
  rw [S2op_congr_three ((d : ℤ) / 2)
    (F2_agree_U0 ℓ d hd r h0) (F2_agree_U0 ℓ d hd r h1) (F2_agree_U0 ℓ d hd r h2)]
  exact hpl

end Work.CKFinal.Socket
