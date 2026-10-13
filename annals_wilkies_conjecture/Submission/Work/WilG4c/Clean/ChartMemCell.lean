import Mathlib
import Submission.Work.WilG4c.EngineDefs
import Submission.Work.WilG4c.Clean.Aux1
import Submission.Work.WilG4c.FibreInterp

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The per-cell chart maps into the cell.**  Let `κ ⊆ ℝ^{p+(n+1)}` be a cylindrical cell
whose fibre coordinate (the last one) takes values in `(0,1)`, and let `lo, hi` be the sharp
bounds of the fibre of `κ` over the base point: `lo b ≤ x ≤ hi b` for `x` in the fibre of `b`,
and `lo b` resp. `hi b` are approached by fibre points from above resp. below.  If the base point
`b = (l, χ l (ψ l t))` (with `t = Fin.init z`) lies in the projection of `κ`, and `M`, `W` are the
affine data of the fibre (`2 * M = lo + hi`, `2 * W - 1/2 = hi - lo`), then the chart
`z ↦ (χ (ψ l t), M (ψ l t) + (ζ - 1/2) (2 W (ψ l t) - 1/2))` of the `(n+1)`-cube, adjoined to the
parameters `l`, lies in `κ`. -/
theorem cellChart_mem_cell {p n : ℕ} {κ : Set (Fin (p + (n + 1)) → ℝ)}
    (hcell : WilkiesDesign.IsCell (p + (n + 1)) κ)
    (hI : ∀ z ∈ κ, z (Fin.last (p + n)) ∈ Set.Ioo (0 : ℝ) 1)
    (lo hi : (Fin (p + n) → ℝ) → ℝ)
    (hlo : ∀ l : Fin (p + n) → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ κ) →
      (∀ x : ℝ, Fin.snoc l x ∈ κ → lo l ≤ x ∧ x ≤ hi l) ∧
      (∀ u : ℝ, lo l < u → ∃ x : ℝ, Fin.snoc l x ∈ κ ∧ x < u) ∧
      (∀ u : ℝ, u < hi l → ∃ x : ℝ, Fin.snoc l x ∈ κ ∧ u < x))
    (χ ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ)
    (hz : z ∈ WilkiesDesign.openCube (n + 1))
    (hbase : Fin.append l (χ l (ψ l (Fin.init z))) ∈ Fin.init '' κ)
    (hM : M l (ψ l (Fin.init z)) =
      (lo (Fin.append l (χ l (ψ l (Fin.init z)))) +
        hi (Fin.append l (χ l (ψ l (Fin.init z))))) / 2)
    (hW : 2 * W l (ψ l (Fin.init z)) - 1 / 2 =
      hi (Fin.append l (χ l (ψ l (Fin.init z)))) -
        lo (Fin.append l (χ l (ψ l (Fin.init z))))) :
    Fin.append l (fun j => Work.WilG4c.cellChart χ M W ψ l z j) ∈ κ := by
  set b : Fin (p + n) → ℝ := Fin.append l (χ l (ψ l (Fin.init z))) with hb
  set w' : Fin (n + 1) → ℝ := fun j => Work.WilG4c.cellChart χ M W ψ l z j with hw'
  -- the last coordinate of the chart sweeps the fibre linearly
  have hlast : w' (Fin.last n) = lo b + (hi b - lo b) * z (Fin.last n) := by
    rw [hw']
    simp only [cellChart]
    rw [dif_pos (show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl), hM, hW]
    ring
  -- the first `n` coordinates of the chart are `χ (ψ l (Fin.init z))`
  have hinit : Fin.init w' = χ l (ψ l (Fin.init z)) := by
    rw [hw']
    funext j
    simp only [cellChart, Fin.init_def]
    rw [dif_neg (by rw [Fin.val_castSucc]; exact Nat.ne_of_lt j.isLt)]
    congr 1
  -- the fibre of `κ` over `b` is non-empty
  obtain ⟨u, hu, huinit⟩ := hbase
  have hne : (∃ x : ℝ, Fin.snoc b x ∈ κ) := by
    refine ⟨u (Fin.last (p + n)), ?_⟩
    rw [← huinit]
    rw [Fin.snoc_init_self (n := p + n) u]
    exact hu
  -- and contained in `(0,1)`
  have h01 : ∀ x : ℝ, Fin.snoc b x ∈ κ → 0 < x ∧ x < 1 := by
    intro x hx
    simpa [Fin.snoc_last] using hI (Fin.snoc b x) hx
  -- the fibre of a cell is an interval with `EReal` endpoints, or a point
  have hslice := clean_cell_slice hcell b
  -- interpolation: the affine map `s ↦ lo + (hi - lo) s` maps `(0,1)` into the fibre
  have hint := (FibreInterp (F := {x : ℝ | clean_snocM b x ∈ κ}) hne h01 hslice
    (hlo b hne).1 (hlo b hne).2.1 (hlo b hne).2.2).1
  have hζ : z (Fin.last n) ∈ Set.Ioo (0 : ℝ) 1 := hz (Fin.last n)
  have hmem : Fin.snoc b (lo b + (hi b - lo b) * z (Fin.last n)) ∈ κ := hint _ hζ
  -- identify the chart with the adjoined point
  have key : Fin.append l w' = Fin.snoc b (lo b + (hi b - lo b) * z (Fin.last n)) := by
    rw [← Fin.snoc_init_self w', Fin.append_snoc, hinit, ← hb, hlast]
  rw [key]
  exact hmem

end Work.WilG4c
