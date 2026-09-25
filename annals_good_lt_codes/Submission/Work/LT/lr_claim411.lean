import Mathlib
import Submission.Work.LT.lr_local_defs
import Submission.Work.LT.local_search_defs
import Submission.Work.LT.cover_le_lrCode
import Submission.Work.LT.lr_claim411_aux

namespace Work.LT

open Classical

/-- **Claim 4.11 (local agreement test bound).** At a vertex `v` build
`w1 (i,j) = view W (nA A v i) (i,j)` (its rows are rows of views of A-neighbours, hence in `CB`)
and `w2 (i,j) = view W (nB B v j) (i,j)` (its columns are in `CA`). Agreement testability `hagr`
gives `w ∈ tensorCode CA CB` with
`κ0 * Δ * (#rows where w1 ≠ w + #columns where w2 ≠ w) ≤ #{w1 ≠ w2}`; local optimality `hopt`
with this `w` at the vertex `(v.1, v.2.1, v.2.2)` says the number of disputed edges does not
decrease, and since only the `2Δ` edges through `v` change, this gives
`#rows where w1 ≠ w + #columns where w2 ≠ w ≥ rA v + rB v` (`rA v` is the number of A-edges
through `v` whose row differs between the two endpoints; the rows of `w1` and of the view at `v`
are indexed by the same coordinate, so the comparison is row-by-row). -/
theorem lr_claim411 {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (κ0 : ℝ) (hκ0 : 0 < κ0)
    (hagr : agreementTestable κ0 CA CB)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hW : ∀ α β g, W α β g ∈ tensorCode CA CB)
    (hopt : IsLocalOpt A B CA CB W) (v : Vtx G) :
    κ0 * Δ * ((rA A W v : ℝ) + (rB B W v : ℝ)) ≤
      ((Finset.univ.filter (fun p : Fin Δ × Fin Δ =>
        view W (nA A v p.1) p ≠ view W (nB B v p.2) p)).card : ℝ) := by
  classical
  -- The row of `w1` at index `i` is row `i` of the view of `W` at the A-neighbour of `v`.
  have hrow : ∀ i : Fin Δ, (fun j => view W (nA A v i) (i, j)) ∈ CB := by
    intro i
    have h := (CoverLe.mem_tensorCode.mp (hW (nA A v i).1 (nA A v i).2.1 (nA A v i).2.2)).1 i
    simpa only [view] using h
  -- The column of `w2` at index `j` is column `j` of the view at the B-neighbour of `v`.
  have hcol : ∀ j : Fin Δ, (fun i => view W (nB B v j) (i, j)) ∈ CA := by
    intro j
    have h := (CoverLe.mem_tensorCode.mp (hW (nB B v j).1 (nB B v j).2.1 (nB B v j).2.2)).2 j
    simpa only [view] using h
  -- Agreement testability with `w1 (i,j) = view W (nA A v i) (i,j)` and
  -- `w2 (i,j) = view W (nB B v j) (i,j)`.
  obtain ⟨w, hw_mem, hw_bound⟩ :=
    hagr (fun p : Fin Δ × Fin Δ => view W (nA A v p.1) p)
         (fun p : Fin Δ × Fin Δ => view W (nB B v p.2) p) hrow hcol
  -- Local optimality of `W` at `v` for this `w`.
  have hoptv : dispCount A B W ≤ dispCount A B (updateAt W v.1 v.2.1 v.2.2 w) :=
    hopt v.1 v.2.1 v.2.2 w hw_mem
  -- Only the `2Δ` edges through `v` change, giving the exact accounting identity.
  have hrc : rA A W v + rB B W v ≤
      (Finset.univ.filter (fun i : Fin Δ => ∃ j, view W (nA A v i) (i, j) ≠ w (i, j))).card +
      (Finset.univ.filter (fun j : Fin Δ => ∃ i, view W (nB B v j) (i, j) ≠ w (i, j))).card := by
    have h1 := dispCount_updateAt_add_lr411 A B W v w
    omega
  calc κ0 * Δ * ((rA A W v : ℝ) + (rB B W v : ℝ))
      ≤ κ0 * Δ * (((Finset.univ.filter (fun i : Fin Δ =>
              ∃ j, view W (nA A v i) (i, j) ≠ w (i, j))).card : ℝ) +
            ((Finset.univ.filter (fun j : Fin Δ =>
              ∃ i, view W (nB B v j) (i, j) ≠ w (i, j))).card : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast hrc
    _ ≤ ((Finset.univ.filter (fun p : Fin Δ × Fin Δ =>
          view W (nA A v p.1) p ≠ view W (nB B v p.2) p)).card : ℝ) := hw_bound

end Work.LT
