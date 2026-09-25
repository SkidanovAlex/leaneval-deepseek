import Mathlib
import Submission.Work.LT.lr_local_defs

/-! Auxiliary definitions for `Work.LT.lr_Mpar_case` (the label-class case for the parallel
operator `M‖`).

The A-edges are indexed by `EIdx G Δ = Fin 2 × G × Fin Δ`; an A-edge `(β, g, i)` carries the
*label* `i`, and the parallel operator preserves labels (`aIdx A (nB B (0,β,g) j) i = (·, ·, i)`).
So the set of A-edges with label `i` is `Fin 2 × G` (via `(β,g) ↦ (β,g,i)`), and on it `M‖`
acts as the walk `classOpB B`.  `sA A W i` is the `0/1` indicator of the *disputed* A-edges of
label `i`, `QA A B W i` is its quadratic form `⟨s, classOpB B s⟩`, and `l1 s` is `∑ s`.
`MparForm = Σ_i QA i + Σ_j QB j` and `dispCount = Σ_i l1 (sA i) + Σ_j l1 (sB j)`; the two
decomposition lemmas live in `lr_Mpar_form_decomp` / `lr_Mpar_disp_decomp`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] {Δ : ℕ}

/-- The `0/1` indicator of the disputed A-edges with label `i`, as a function of the A-edge
`(β, g) ↦ (β, g, i)`. -/
noncomputable def sA (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (i : Fin Δ) : Fin 2 × G → ℝ :=
  fun p => if disputeA A W p.1 p.2 i then 1 else 0

/-- The `0/1` indicator of the disputed B-edges with label `j`, as a function of the B-edge
`(α, g) ↦ (α, g, j)`. -/
noncomputable def sB (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (j : Fin Δ) : Fin 2 × G → ℝ :=
  fun p => if disputeB B W p.1 p.2 j then 1 else 0

/-- The `ℓ¹`-mass `∑ s` of a function on a label class. -/
noncomputable def l1 (s : Fin 2 × G → ℝ) : ℝ := ∑ p, s p

/-- The quadratic form of `M‖` on the class of A-edges with label `i`. -/
noncomputable def QA (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (i : Fin Δ) : ℝ :=
  ∑ p : Fin 2 × G, sA A W i p * classOpB B (sA A W i) p

/-- The quadratic form of `M‖` on the class of B-edges with label `j`. -/
noncomputable def QB (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (j : Fin Δ) : ℝ :=
  ∑ p : Fin 2 × G, sB B W j p * classOpA A (sB B W j) p

end Work.LT
