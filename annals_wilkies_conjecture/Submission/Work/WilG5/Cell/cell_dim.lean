import Mathlib
import Submission.Work.WilG5.Defs
import Submission.Work.WilG5.Cell.cellpar_injective
import Submission.Work.WilG5.Cell.cellpar_proj_interior

namespace Work.WilG5.Cell

/-- The parametrising dimension of a cell is at most the `DimLE`-dimension of any set containing
it: the `d` free coordinates of `κ` are swept out by an open map (clauses 5 and 6 of `CellPar`),
so any `μ+1` of them project `X ⊇ κ` to a set with non-empty interior. -/
theorem cell_dim {n μ d : ℕ} {κ X : Set (Fin n → ℝ)} {e : Fin d → Fin n} {R : Set (Fin (d + n) → ℝ)} (hpar : Work.WilG5.CellPar n κ d e R) (hne : κ.Nonempty) (hsub : κ ⊆ X) (hX : WilkiesDesign.DimLE X μ) : d ≤ μ := by
  have he_inj : Function.Injective e := cellpar_injective hpar hne
  by_contra hcon
  have hd : μ + 1 ≤ d := by omega
  let f : Fin (μ + 1) ↪ Fin d := ⟨Fin.castLE hd, Fin.castLE_injective hd⟩
  let e' : Fin (μ + 1) ↪ Fin n := ⟨fun i => e (f i), fun a b hab => f.injective (he_inj hab)⟩
  obtain ⟨p, hp⟩ := cellpar_proj_interior hpar hne f
  have hp' : p ∈ interior ((fun x : Fin n → ℝ => x ∘ ⇑e') '' κ) := hp
  have hpX : p ∈ interior ((fun x : Fin n → ℝ => x ∘ ⇑e') '' X) :=
    interior_mono (Set.image_mono hsub) hp'
  have hempty : interior ((fun x : Fin n → ℝ => x ∘ ⇑e') '' X) = ∅ := hX e'
  rw [hempty] at hpX
  exact hpX

end Work.WilG5.Cell
