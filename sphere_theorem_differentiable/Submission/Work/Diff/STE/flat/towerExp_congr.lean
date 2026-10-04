import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Locality of the formal time-derivative tower `towerExp`

`Work.Diff.STE.flat.towerExp Φ j (x, Js)` is the `j`-th formal time derivative of the flat
DeTurck nonlinearity `Φ` along a solution, expressed as a function of the space point `x` and of
the spatial `2`-jets `Js = (J₀, …, J_{j-1})` of the first `j` time derivatives of the unknown
(see `Submission/Work/Diff/STE/flat/TowerDefs.lean`).

This file proves that the tower only depends on the **germ** of `Φ` along the first jet slot:
if `Φ` and `Φ'` agree on `Set.univ ×ˢ V` with `V` open, then

`towerExp Φ (j+1) (x, Js) = towerExp Φ' (j+1) (x, Js)`  whenever  `Js 0 ∈ V`.

The point is that the recursion
`towerExp Φ (j+2) p = Σᵢ (Dᵢ towerExp Φ (j+1)) (p.1, first slots)` differentiates the `(j+1)`-st
tower in the jet slots, so it needs the agreement of the towers on a *neighbourhood* of the base
point of the derivative — and that neighbourhood is exactly the open condition `Js 0 ∈ V` (`V`
open, so `Js 0 ∈ V` persists for nearby `Js`, and it is the only slot the induction hypothesis
constrains).  The smoothness hypotheses `hΦ`, `hΦ'` are not needed for this purely formal
statement; they are kept because the request is used in that form.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open Filter
open scoped Topology

/-- **The locality/induction statement.**  For every level `m + 1` of the tower, the two towers
agree at every point whose first jet slot lies in `V`. -/
theorem towerExp_congr_aux {n : ℕ}
    (Φ Φ' : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (V : Set (Work.Diff.STE.Flat.Jet n)) (hV : IsOpen V)
    (h : ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n), w ∈ V → Φ (x, w) = Φ' (x, w)) :
    ∀ m : ℕ, ∀ (p : (Fin n → ℝ) × (Fin (m + 1) → Work.Diff.STE.Flat.Jet n)),
      p.2 0 ∈ V → towerExp Φ (m + 1) p = towerExp Φ' (m + 1) p := by
  intro m
  induction m with
  | zero =>
      intro p hp
      rw [towerExp_one, towerExp_one]
      exact h p.1 (p.2 0) hp
  | succ m ih =>
      intro p hp
      rw [towerExp_succ_succ (Φ := Φ) (j := m), towerExp_succ_succ (Φ := Φ') (j := m)]
      refine Finset.sum_congr rfl fun i _ => ?_
      -- the two `(m+1)`-st towers agree on a neighbourhood of the base point of the derivative
      have hS : {Js : Fin (m + 1) → Jet n | Js 0 ∈ V} ∈
          𝓝 (fun i' : Fin (m + 1) => p.2 i'.castSucc) :=
        (continuous_apply (0 : Fin (m + 1))).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
      have hev : (fun Js : Fin (m + 1) → Jet n => towerExp Φ (m + 1) (p.1, Js))
          =ᶠ[𝓝 (fun i' : Fin (m + 1) => p.2 i'.castSucc)]
          (fun Js : Fin (m + 1) → Jet n => towerExp Φ' (m + 1) (p.1, Js)) :=
        Filter.Eventually.mono hS fun Js hJs => ih (p.1, Js) hJs
      rw [hev.fderiv_eq]

theorem towerExp_congr {n : ℕ}
    (Φ Φ' : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (V : Set (Work.Diff.STE.Flat.Jet n)) (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Set.univ ×ˢ V))
    (hΦ' : ContDiffOn ℝ (⊤ : ℕ∞) Φ' (Set.univ ×ˢ V))
    (h : ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n), w ∈ V → Φ (x, w) = Φ' (x, w))
    (j : ℕ) (x : Fin n → ℝ) (Js : Fin (j + 1) → Work.Diff.STE.Flat.Jet n)
    (hJs : Js 0 ∈ V) :
    Work.Diff.STE.flat.towerExp Φ (j + 1) (x, Js)
      = Work.Diff.STE.flat.towerExp Φ' (j + 1) (x, Js) := by
  -- the smoothness hypotheses are not needed for this formal statement
  have _ := hΦ
  have _ := hΦ'
  exact towerExp_congr_aux Φ Φ' V hV h j (x, Js) hJs

end Work.Diff.STE.flat
