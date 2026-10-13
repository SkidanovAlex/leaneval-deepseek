/-
  WilC4/Sfam_definable : the parametrised level set `Work.WilC4.Sfam Y` is `∅`-definable in
  `LRc` whenever the family `Y` is.

  `Sfam Y = {u : Fin (k+2) → ℝ | ∃ w, RatW Y (cOfF u) (u 0) w ∧ w = mOfF u}` is the set of
  tuples `u = (x, c, m)` (coordinate `0` the point `x`, coordinates `1, …, k` the parameters
  `c`, the last coordinate the value `m`) whose point lies in the level set of the doubling
  ratio of the fibre of `Y`.

  The proof is a change of variables, no quantifier bookkeeping needed: by `ratGraph_mem_iff`
  the relation `RatW` is the fibre relation of the graph `Route.RatGraph Y ⊆ ℝ^{k+2}` of the
  doubling ratio, and `RatW Y (cOfF u) (u 0) w ↔ Fin.cons (u 0) (Fin.cons w (cOfF u)) ∈
  Route.RatGraph Y`.  Since `w` is determined (`w = mOfF u`), the existential is the
  membership of the *reindexed* tuple `(x, m, c)`, so

    `Sfam Y = (fun u => u ∘ sfPhi k) ⁻¹' Route.RatGraph Y`

  for the coordinate permutation `sfPhi k : Fin (k+2) → Fin (k+2)` sending `0 ↦ 0`, `1 ↦ k+1`
  and `j + 2 ↦ j + 1`.  `Route.RatGraph Y` is `∅`-definable by `Work.WilC4.ratGraph_definable`
  (the graph of the doubling ratio of a `∅`-definable family is `∅`-definable), and preimages
  along coordinate relabellings preserve definability (`Set.Definable.preimage_comp`).
-/
import Mathlib
import Submission.Work.WilC4.ulpm_BxDefs
import Submission.Work.WilC4.ratGraph_definable

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

variable {k : ℕ}

/-- The coordinate relabelling putting the `RatGraph` tuple `(x, m, c)` on the tuple
`u = (x, c, m) : Fin (k+2) → ℝ`: coordinate `0` is the point `x`, coordinate `1` the value `m`,
and coordinate `j + 2` the parameter `c j`. -/
def sfPhi (k : ℕ) : Fin (k + 2) → Fin (k + 2) :=
  Fin.cases 0 (Fin.cases (Fin.last (k + 1)) (fun j : Fin k => Fin.succ (Fin.castSucc j)))

/-- `u ∘ sfPhi` is the `Fin.cons`-tuple `(u 0, mOfF u, cOfF u)` of `Route.RatGraph`. -/
theorem sfPhi_comp (k : ℕ) (u : Fin (k + 2) → ℝ) :
    u ∘ sfPhi k = Fin.cons (u 0) (Fin.cons (mOfF u) (cOfF u)) := by
  funext i
  refine Fin.cases ?_ (fun i₁ => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) i₁ <;> rfl

/-- `Sfam Y` is the preimage of the graph of the doubling ratio under the reindexing
`sfPhi`. -/
theorem Sfam_eq_preimage_RatGraph (Y : Set (Fin (k + 2) → ℝ)) :
    Sfam Y = (fun u : Fin (k + 2) → ℝ => u ∘ sfPhi k) ⁻¹' (Route.RatGraph Y) := by
  ext u
  rw [Set.mem_preimage, sfPhi_comp k u, ratGraph_mem_iff]
  simp only [Sfam, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact hw
  · intro h; exact ⟨mOfF u, h, rfl⟩

theorem Sfam_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.Sfam Y) := by
  rw [Sfam_eq_preimage_RatGraph Y]
  exact (ratGraph_definable hY).preimage_comp (sfPhi k)

end Work.WilC4
