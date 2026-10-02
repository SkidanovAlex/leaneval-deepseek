import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ProbBasic

/-!
# Stability of `colourClassCount` under recolouring one vertex

`colourClassCount G f v c` counts the *retained* neighbours of `v` that carry the colour `c`
(see `Submission.Work.Deep.Sparse.ProbModel`).  Recolouring a single vertex `z` can change this
count only through the neighbours of `z`: for every vertex `w ≠ z` the colour is unchanged, and
whether `w` is retained can only flip if `w` is adjacent to `z` (the only vertex whose colour
changed).  Hence, for `z ∉ N(v)`, the counts before and after the update differ by at most the
number of common neighbours of `z` and `v` that carry the colour `c`:

`|colourClassCount G (update f z x) v c - colourClassCount G f v c|
    ≤ #{y ∈ N(z) ∩ N(v) : f y = c}`.

This is the Lipschitz-type estimate used when a single coordinate of the random colouring of the
naive colouring procedure is varied.  The key point is that for two functions `g, f` that agree
off a single vertex `z`, one gets the bound with the *common* colour function `f` on the right,
because any vertex `w ∈ N(v) \ {z}` on which the two retainedness predicates disagree must be a
neighbour of `z` whose colour `f w` equals `c`.
-/

set_option autoImplicit false

namespace Work.Deep.Sparse

section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Elementary arithmetic: two naturals that bound each other up to an additive slack `t`. -/
private theorem abs_sub_le_of_le_add {a b t : ℕ} (h1 : a ≤ b + t) (h2 : b ≤ a + t) :
    |((a : ℝ) - (b : ℝ))| ≤ (t : ℝ) := by
  have e1 : (a : ℝ) ≤ (b : ℝ) + (t : ℝ) := by exact_mod_cast h1
  have e2 : (b : ℝ) ≤ (a : ℝ) + (t : ℝ) := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-- **The one-vertex recolouring estimate.**  If two colourings `g` and `f` agree everywhere except
possibly at `z`, and `z` is not a neighbour of `v`, then the `c`-colour class counts of `v` under
`g` and under `f` differ by at most the number of common neighbours of `z` and `v` of colour `c`
(measured with `f`). -/
private theorem colourClassCount_abs_le_agree_off (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (g f : V → Fin k) (v z : V) (hg : ∀ y, y ≠ z → g y = f y)
    (hz : z ∉ G.neighborFinset v) (c : Fin k) :
    |((colourClassCount G g v c : ℝ) - (colourClassCount G f v c : ℝ))|
      ≤ ((((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = c)).card : ℝ) := by
  classical
  -- membership in `N(z)` from adjacency
  have hmemz : ∀ {y : V}, G.Adj y z → y ∈ G.neighborFinset z := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset]
    exact SimpleGraph.adj_symm G hy
  -- the two counts, unfolded into filter cardinalities
  have h₁ : colourClassCount G g v c
      = ((G.neighborFinset v).filter (fun w => Retained G g w ∧ g w = c)).card := rfl
  have h₂ : colourClassCount G f v c
      = ((G.neighborFinset v).filter (fun w => Retained G f w ∧ f w = c)).card := rfl
  -- every neighbour of `v` is distinct from `z`
  have hvz : ∀ w ∈ G.neighborFinset v, w ≠ z := by
    intro w hw h
    subst h
    exact hz hw
  -- first inclusion: a `g`-counted neighbour is either `f`-counted or lies in `N(z) ∩ N(v)`
  have hsub1 : ((G.neighborFinset v).filter (fun w => Retained G g w ∧ g w = c))
      ⊆ ((G.neighborFinset v).filter (fun w => Retained G f w ∧ f w = c))
        ∪ (((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = c)) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwv, hretg, hwc⟩ := hw
    have wne : w ≠ z := hvz w hwv
    have hfwc : f w = c := by rw [← hg w wne]; exact hwc
    by_cases hretf : Retained G f w
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hwv, hretf, hfwc⟩))
    · -- `w` is not retained under `f`, so some neighbour `u` of `w` shares `w`'s `f`-colour;
      -- since `w` is retained under `g`, `u` cannot be a vertex where `g` and `f` agree, so `u = z`
      have hadjz : G.Adj w z := by
        have hneg : ¬ (∀ u : V, G.Adj w u → f u ≠ f w) := hretf
        push Not at hneg
        obtain ⟨u, hadj, hfu⟩ := hneg
        have hgune : g u ≠ f u := by
          intro h
          exact hretg u hadj (by rw [h, hfu, ← hg w wne])
        have huz : u = z := by
          by_contra hune
          exact hgune (hg u hune)
        exact huz ▸ hadj
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_inter.mpr ⟨hmemz hadjz, hwv⟩, hfwc⟩))
  -- second inclusion: the mirror image of the first
  have hsub2 : ((G.neighborFinset v).filter (fun w => Retained G f w ∧ f w = c))
      ⊆ ((G.neighborFinset v).filter (fun w => Retained G g w ∧ g w = c))
        ∪ (((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = c)) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwv, hretf, hfwc⟩ := hw
    have wne : w ≠ z := hvz w hwv
    have hgwc : g w = c := by rw [hg w wne]; exact hfwc
    by_cases hretg : Retained G g w
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hwv, hretg, hgwc⟩))
    · have hadjz : G.Adj w z := by
        have hneg : ¬ (∀ u : V, G.Adj w u → g u ≠ g w) := hretg
        push Not at hneg
        obtain ⟨u, hadj, hgu⟩ := hneg
        have huz : u = z := by
          by_contra hune
          have huf : f u = g u := (hg u hune).symm
          exact hretf u hadj (by rw [huf, hgu, hg w wne])
        exact huz ▸ hadj
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_inter.mpr ⟨hmemz hadjz, hwv⟩, hfwc⟩))
  -- cardinality bounds in `ℕ`, then the triangle-type inequality in `ℝ`
  have hle1 : colourClassCount G g v c ≤ colourClassCount G f v c
      + (((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = c)).card := by
    rw [h₁, h₂]
    exact le_trans (Finset.card_le_card hsub1) (Finset.card_union_le _ _)
  have hle2 : colourClassCount G f v c ≤ colourClassCount G g v c
      + (((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = c)).card := by
    rw [h₂, h₁]
    exact le_trans (Finset.card_le_card hsub2) (Finset.card_union_le _ _)
  exact abs_sub_le_of_le_add hle1 hle2

end

/-- Recolouring the single vertex `z` — not a neighbour of `v` — changes the number of retained
neighbours of `v` of colour `c` by at most the number of common neighbours of `z` and `v` that
carry the colour `c` under the original colouring `f`. -/
theorem colourClassCount_update_abs_le {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin k) (v : V) {z : V} (hz : z ∉ G.neighborFinset v) (x c : Fin k) :
    |((colourClassCount G (Function.update f z x) v c : ℝ) - (colourClassCount G f v c : ℝ))|
      ≤ ((((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = c)).card : ℝ) := by
  refine colourClassCount_abs_le_agree_off G (Function.update f z x) f v z ?_ hz c
  intro y hy
  rw [Function.update_apply, if_neg hy]

end Work.Deep.Sparse
