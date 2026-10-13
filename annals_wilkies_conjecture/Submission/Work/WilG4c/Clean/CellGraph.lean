import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG4c.Clean.Aux2

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **Cell parametrisation (BNZ §2.3).**  A cell `κ` of a cylindrical decomposition of
`ℝ^{p+N}` that lies in the open cube in its last `N` coordinates and whose fibre over `Λ` is
nonempty admits a definable surjection `Ψ` onto that fibre: each coordinate graph of `Ψ` is
`Ω`-bounded with format independent of `D` and degree polynomial in `D`, `Ψ` maps the cube
into the cube, its image lies in `κ`, and it is onto the fibre of `κ` over every `l ∈ Λ`.
The construction is the nested interpolation of the fibre ends of the iterated projections
`Fin.init^j '' κ` (supplied by `StepFiberEnds`). -/
theorem clean_StepCellGraph (S : SOMin) (p N F0 : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
    ∀ (D : ℕ) (C : Finset (Set (Fin (p + N) → ℝ))), IsCylDecomp (p + N) C →
      (∀ κ ∈ C, κ ∈ S.Ω F0 D (p + N)) →
      ∀ (κ : Set (Fin (p + N) → ℝ)), κ ∈ C → κ ⊆ inCubeSet p N →
      ∀ (Λ : Set (Fin p → ℝ)), (∀ l ∈ Λ, ∃ y : Fin N → ℝ, Fin.append l y ∈ κ) →
        ∃ Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ),
          (∀ j : Fin N,
            famGraph (fun l t => Ψ l t j) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + N + 1)) ∧
          (∀ l ∈ Λ, ∀ t ∈ openCube N, Ψ l t ∈ openCube N) ∧
          (∀ l ∈ Λ, ∀ t ∈ openCube N, Fin.append l (Ψ l t) ∈ κ) ∧
          (∀ l ∈ Λ, ∀ y : Fin N → ℝ, Fin.append l y ∈ κ → ∃ t ∈ openCube N, Ψ l t = y) := by
  obtain ⟨a, b, h⟩ := clean_stepCellGraph_aux S N p F0
  refine ⟨a, b, ?_⟩
  intro D C hC hΩ κ hκ hsub Λ hΛ
  obtain ⟨W, hWg, hWc, hWm, hWs⟩ := h D C hC hΩ κ hκ hsub Λ hΛ
  refine ⟨fun l t => W (Fin.append l t), ?_, ?_, ?_, ?_⟩
  · intro j
    have heq : (fun z : Fin (p + N) → ℝ =>
        W (Fin.append (fun i => z (Fin.castAdd N i)) (fun j => z (Fin.natAdd p j))) j)
        = (fun z : Fin (p + N) → ℝ => W z j) := by
      funext z
      rw [Fin.append_castAdd_natAdd]
    show graphOf (fun z : Fin (p + N) → ℝ =>
        W (Fin.append (fun i => z (Fin.castAdd N i)) (fun j => z (Fin.natAdd p j))) j) ∈
      S.Ω a (MvPolynomial.eval ![D, 1] b) (p + N + 1)
    rw [heq]
    exact hWg j
  · intro l hl t ht
    exact hWc l hl t ht
  · intro l hl t ht
    exact hWm l hl t ht
  · intro l hl y hy
    exact hWs l hl y hy

end Work.WilG4c
