import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open scoped BigOperators

noncomputable section

/-- The successive half-differences `(lam i.succ - lam i.castSucc)/2` of the flag parameters. -/
def lamStep {d : ℕ} (lam : Fin (d + 1) → ℝ) (i : Fin d) : ℝ :=
  (lam i.succ - lam i.castSucc) / 2

/-- For `m : Fin d`, the part of the `m`-th coordinate of the centroid map
`x ↦ ∑ i, lamStep lam i • c i x` coming from the indices `i` with `¬ i ≤ m`. -/
def offDiag {d : ℕ} (lam : Fin (d + 1) → ℝ) (c : Fin d → (Fin d → ℝ) → (Fin d → ℝ))
    (m : Fin d) (x : Fin d → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬ (i ≤ m)), lamStep lam i * (c i x) m

@[simp] theorem lamStep_apply {d : ℕ} (lam : Fin (d + 1) → ℝ) (i : Fin d) :
    lamStep lam i = (lam i.succ - lam i.castSucc) / 2 := rfl

@[simp] theorem offDiag_apply {d : ℕ} (lam : Fin (d + 1) → ℝ)
    (c : Fin d → (Fin d → ℝ) → (Fin d → ℝ)) (m : Fin d) (x : Fin d → ℝ) :
    offDiag lam c m x
      = ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬ (i ≤ m)),
          lamStep lam i * (c i x) m := rfl

end
end Work.BW.Minkowski2
