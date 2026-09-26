/-
# The first recurrence of the socket layer `F₂`

On `Wm1` the layer is *defined* by `2·G(τ+1) - G(τ+2) - T2op gauss(τ)`, and a point of a
`T`-triple in `O` lies in `Wm1` (`Socket.T_triple_mem_Wm1`) while its two shifts do not
(`Socket.vadd_one_not_mem_Wm1`, `Socket.vadd_two_not_mem_Wm1`).  Hence the first recurrence
`T2op F₂ τ = -T2op (gaussTerm · r) τ` is *definitional* on every triple inside `O`.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Construction
import Submission.Work.CKFinal.Socket.T_triple_mem_Wm1

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- The first recurrence of the socket layer on `O`. -/
theorem F2_T2op (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    {τ : ℍ} (h1 : τ ∈ O ℓ d hd) (h2 : (1 : ℝ) +ᵥ τ ∈ O ℓ d hd)
    (h3 : (2 : ℝ) +ᵥ τ ∈ O ℓ d hd) :
    Work.Kernels.T2op (F2 ℓ d hd r) τ
      = -Work.Kernels.T2op (fun σ : ℍ => Work.Kernels.gaussTerm σ r) τ := by
  have hm : τ ∈ Wm1 ℓ d hd := T_triple_mem_Wm1 ℓ d hd h1 h2 h3
  have hn1 : (1 : ℝ) +ᵥ τ ∉ Wm1 ℓ d hd := vadd_one_not_mem_Wm1 hm
  have hn2 : (2 : ℝ) +ᵥ τ ∉ Wm1 ℓ d hd := vadd_two_not_mem_Wm1 hm
  have h2' : F2 ℓ d hd r ((2 : ℝ) +ᵥ τ) = G ℓ d hd r ((2 : ℝ) +ᵥ τ) :=
    F2_of_not_mem_Wm1 ℓ d hd r hn2
  have h1' : F2 ℓ d hd r ((1 : ℝ) +ᵥ τ) = G ℓ d hd r ((1 : ℝ) +ᵥ τ) :=
    F2_of_not_mem_Wm1 ℓ d hd r hn1
  have h0' : F2 ℓ d hd r τ
      = 2 * G ℓ d hd r ((1 : ℝ) +ᵥ τ) - G ℓ d hd r ((2 : ℝ) +ᵥ τ)
        - Work.Kernels.T2op (fun σ : ℍ => Work.Kernels.gaussTerm σ r) τ :=
    F2_of_mem_Wm1 ℓ d hd r hm
  simp only [Work.Kernels.T2op, h2', h1', h0']
  ring

end Socket
end Work.CKFinal
