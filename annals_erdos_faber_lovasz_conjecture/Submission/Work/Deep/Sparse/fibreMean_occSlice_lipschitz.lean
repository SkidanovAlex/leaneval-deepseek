/-
# The fibre mean of `occSlice` is Lipschitz in a single outside coordinate

For a graph `G` on `V`, a colouring `f : V → Fin k`, a vertex `v` and a colour `x : Fin k`,
recolouring a vertex `z` that is *not* a neighbour of `v` changes the fibre mean of the
truncated occupancy statistic

  `Y h := occSlice G h v J = ∑_{2 ≤ j ≤ J} occW j · #{c : j ≤ colourClassCount G h v c}`

(see `Submission.Work.Deep.Sparse.NcpDefs` and `Submission.Work.Deep.Sparse.SliceDefs`) by at
most

  `occWsum J · 2 · |N(z) ∩ N(v)| / k`,

where `fibreMean A Y f` is the average of `Y` over all recolourings of the `A`-coordinates of
`f` (`fibreMean`, `Submission.Work.Deep.Sparse.SliceDefs`).

This is the *coupling* estimate used to feed the outside part of the two-step concentration
argument of the naive colouring procedure (see `NCP_CONCENTRATION_STATUS.md`): the recolouring
of `z` is measured by an `azuma_finSpace` argument on the vertices outside `N(v)`, whose
per-coordinate Lipschitz constants are these bounds.

The proof has three ingredients.

* `occSlice_update_out_le` (`Submission.Work.Deep.Sparse.occSlice_update_out_le`): for a fixed
  colouring `h`, recolouring the vertex `z` changes `occSlice G · v J` by at most
  `occWsum J · (t_{h z} + t_x)`, where `t_c = #{y ∈ N(z) ∩ N(v) : h y = c}` counts the common
  neighbours of `z` and `v` carrying the colour `c`.
* Grafting and updating commute for a coordinate `z ∉ A` (`graft_update_of_notMem`), so that the
  fibre mean of the updated colouring is the average, over the recolourings `g` of the fibre, of
  the same quantity evaluated at `graft A g f`.  Applying the pointwise estimate to every
  `graft A g f` and taking absolute values inside the average gives the fibre mean of
  `t_{f z} + t_x`.
* `fibreMean_filter_card`: the average over the fibre of the number of points of a set `S ⊆ A`
  carrying a fixed colour `c` is `|S| / k`.  Indeed, by linearity the average of the count is the
  sum over `y ∈ S` of the probability that the coordinate `y` takes the colour `c`, which is
  `1/k` by the product law of the uniform colouring of the fibre (`prob_single_and_avoid`).

The two colours that can move are `f z` (the colour `z` carried before the recolouring) and `x`
(the new colour), whence the factor `2`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.SliceDefs
import Submission.Work.Deep.Sparse.occSlice_update_out_le

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Auxiliary lemmas -/

/-- Grafting commutes with the update of a coordinate `z` lying outside `A`: the two operations
touch disjoint sets of coordinates. -/
private lemma graft_update_of_notMem {k : ℕ} {A : Finset V} {z : V} (hz : z ∉ A)
    (g : ↥A → Fin k) (f : V → Fin k) (x : Fin k) :
    graft A g (Function.update f z x) = Function.update (graft A g f) z x := by
  funext u
  by_cases hu : u ∈ A
  · have huz : u ≠ z := fun h => hz (h ▸ hu)
    simp only [graft_apply_of_mem _ _ hu, Function.update_of_ne huz]
  · by_cases huz : u = z
    · subst huz
      simp only [graft_apply_of_notMem _ _ hu, Function.update_self]
    · simp only [graft_apply_of_notMem _ _ hu, Function.update_of_ne huz]

/-- Under the uniform colouring of the fibre `↥A → Fin k`, a prescribed coordinate `a` takes a
prescribed colour `c` with probability `1/k`. -/
private lemma prob_single_colour {k : ℕ} (hk : 0 < k) (A : Finset V)
    [Nonempty (↥A → Fin k)] (a : ↥A) (c : Fin k) :
    (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | g a = c} = 1 / (k : ℝ) := by
  have h := prob_single_and_avoid (V := ↥A) (k := k) hk (x := a) (T := (∅ : Finset ↥A))
    (by simp) c
  simpa using h

/-- The fibre mean of the indicator that a fixed coordinate `y ∈ A` carries the colour `c` is
`1/k`. -/
private lemma fibreMean_single_colour {k : ℕ} (hk : 0 < k) (A : Finset V) {y : V} (hy : y ∈ A)
    (f : V → Fin k) (c : Fin k) :
    (1 / (k : ℝ) ^ A.card) * ∑ g : ↥A → Fin k, (if graft A g f y = c then (1 : ℝ) else 0)
      = 1 / (k : ℝ) := by
  classical
  haveI hne : Nonempty (↥A → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  have hcard : Fintype.card (↥A → Fin k) = k ^ A.card := by rw [card_colSpace, Fintype.card_coe]
  calc (1 / (k : ℝ) ^ A.card) * ∑ g : ↥A → Fin k, (if graft A g f y = c then (1 : ℝ) else 0)
      = ∑ g : ↥A → Fin k,
          ((k : ℝ) ^ A.card)⁻¹ * (if graft A g f y = c then (1 : ℝ) else 0) := by
        rw [one_div, Finset.mul_sum]
    _ = ∑ g : ↥A → Fin k, (if g ⟨y, hy⟩ = c then ((k : ℝ) ^ A.card)⁻¹ else 0) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [graft_apply_of_mem g f hy]
        by_cases h : g ⟨y, hy⟩ = c <;> simp [h]
    _ = (colSpace (V := ↥A) k).prob {g : ↥A → Fin k | g ⟨y, hy⟩ = c} := by
        rw [FinSpace.prob, colSpace_mass, hcard, Nat.cast_pow]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Set.indicator_apply]
        by_cases h : g ⟨y, hy⟩ = c <;> simp [h]
    _ = 1 / (k : ℝ) := prob_single_colour hk A ⟨y, hy⟩ c

/-- **The fibre mean of a colour count on a subset of `A`.**  For `S ⊆ A`, the average over the
recolourings of the fibre of the number of points of `S` carrying a fixed colour `c` is
`|S| / k`. -/
private lemma fibreMean_filter_card {k : ℕ} (hk : 0 < k) (A S : Finset V) (hSA : S ⊆ A)
    (f : V → Fin k) (c : Fin k) :
    (1 / (k : ℝ) ^ A.card) *
        ∑ g : ↥A → Fin k, (((S.filter (fun y => graft A g f y = c)).card : ℕ) : ℝ)
      = (S.card : ℝ) / (k : ℝ) := by
  classical
  have hcard : ∀ g : ↥A → Fin k,
      (((S.filter (fun y => graft A g f y = c)).card : ℕ) : ℝ)
        = ∑ y ∈ S, (if graft A g f y = c then (1 : ℝ) else 0) := by
    intro g
    exact (Finset.sum_boole (fun y => graft A g f y = c) S).symm
  calc (1 / (k : ℝ) ^ A.card) *
        ∑ g : ↥A → Fin k, (((S.filter (fun y => graft A g f y = c)).card : ℕ) : ℝ)
      = (1 / (k : ℝ) ^ A.card) *
          ∑ g : ↥A → Fin k, ∑ y ∈ S, (if graft A g f y = c then (1 : ℝ) else 0) := by
        congr 1
        exact Finset.sum_congr rfl fun g _ => hcard g
    _ = (1 / (k : ℝ) ^ A.card) *
          ∑ y ∈ S, ∑ g : ↥A → Fin k, (if graft A g f y = c then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ y ∈ S, (1 / (k : ℝ) ^ A.card) *
          ∑ g : ↥A → Fin k, (if graft A g f y = c then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ = ∑ _y ∈ S, (1 / (k : ℝ)) := by
        refine Finset.sum_congr rfl fun y hy => fibreMean_single_colour hk A (hSA hy) f c
    _ = (S.card : ℝ) / (k : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **The abstract Lipschitz estimate.**  It suffices that every recolouring of the fibre obeys
the one-vertex estimate of `occSlice_update_out_le`; the pointwise bounds are then averaged with
`fibreMean_filter_card`. -/
private theorem fibreMean_lipschitz_of_pointwise {k J : ℕ} (hk : 0 < k) (A S : Finset V)
    (f : V → Fin k) {z : V} (x : Fin k) (hz : z ∉ A) (hSA : S ⊆ A) (Y : (V → Fin k) → ℝ)
    (hY : ∀ g : ↥A → Fin k,
      |Y (Function.update (graft A g f) z x) - Y (graft A g f)|
        ≤ occWsum J * (((S.filter (fun y => graft A g f y = f z)).card : ℝ)
            + ((S.filter (fun y => graft A g f y = x)).card : ℝ))) :
    |fibreMean A Y (Function.update f z x) - fibreMean A Y f|
      ≤ occWsum J * (2 * (S.card : ℝ) / (k : ℝ)) := by
  classical
  -- Grafting commutes with the update, so the fibre mean of the updated colouring is the
  -- average of the values at the grafted colourings.
  have hU : ∀ g : ↥A → Fin k,
      graft A g (Function.update f z x) = Function.update (graft A g f) z x :=
    fun g => graft_update_of_notMem hz g f x
  have h1 : fibreMean A Y (Function.update f z x)
      = (1 / (k : ℝ) ^ A.card) * ∑ g : ↥A → Fin k, Y (Function.update (graft A g f) z x) := by
    rw [fibreMean]
    congr 1
    exact Finset.sum_congr rfl fun g _ => by rw [hU g]
  have h2 : fibreMean A Y f
      = (1 / (k : ℝ) ^ A.card) * ∑ g : ↥A → Fin k, Y (graft A g f) := rfl
  have hgoal : |fibreMean A Y (Function.update f z x) - fibreMean A Y f|
      = (1 / (k : ℝ) ^ A.card) *
          |∑ g : ↥A → Fin k,
            (Y (Function.update (graft A g f) z x) - Y (graft A g f))| := by
    rw [h1, h2, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
      abs_of_nonneg (by positivity)]
  rw [hgoal]
  have hc : (0 : ℝ) ≤ 1 / (k : ℝ) ^ A.card := by positivity
  have hsr : (1 / (k : ℝ) ^ A.card) *
        ∑ g : ↥A → Fin k, ((S.filter (fun y => graft A g f y = f z)).card : ℝ)
      = (S.card : ℝ) / (k : ℝ) := fibreMean_filter_card hk A S hSA f (f z)
  have hsx : (1 / (k : ℝ) ^ A.card) *
        ∑ g : ↥A → Fin k, ((S.filter (fun y => graft A g f y = x)).card : ℝ)
      = (S.card : ℝ) / (k : ℝ) := fibreMean_filter_card hk A S hSA f x
  calc (1 / (k : ℝ) ^ A.card) *
        |∑ g : ↥A → Fin k,
          (Y (Function.update (graft A g f) z x) - Y (graft A g f))|
      ≤ (1 / (k : ℝ) ^ A.card) *
          ∑ g : ↥A → Fin k,
            |Y (Function.update (graft A g f) z x) - Y (graft A g f)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
    _ ≤ (1 / (k : ℝ) ^ A.card) * ∑ g : ↥A → Fin k,
          occWsum J * (((S.filter (fun y => graft A g f y = f z)).card : ℝ)
            + ((S.filter (fun y => graft A g f y = x)).card : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hY g) hc
    _ = occWsum J * ((1 / (k : ℝ) ^ A.card) *
          ((∑ g : ↥A → Fin k, ((S.filter (fun y => graft A g f y = f z)).card : ℝ))
            + ∑ g : ↥A → Fin k, ((S.filter (fun y => graft A g f y = x)).card : ℝ))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        ring
    _ = occWsum J * ((S.card : ℝ) / (k : ℝ) + (S.card : ℝ) / (k : ℝ)) := by
        rw [mul_add, hsr, hsx]
    _ = occWsum J * (2 * (S.card : ℝ) / (k : ℝ)) := by
        ring

/-! ## The Lipschitz estimate for `occSlice` -/

theorem fibreMean_occSlice_lipschitz {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k J : ℕ} (f : V → Fin k)
    (v : V) {z : V} (hz : z ∉ G.neighborFinset v) (x : Fin k) :
    |fibreMean (G.neighborFinset v) (fun f' : V → Fin k => occSlice G f' v J) (Function.update f z x)
        - fibreMean (G.neighborFinset v) (fun f' : V → Fin k => occSlice G f' v J) f|
      ≤ occWsum J * (2 * (((G.neighborFinset z) ∩ (G.neighborFinset v)).card : ℝ) / (k : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0` forces `V` to be empty, contradicting the existence of `z`
    subst hk0
    exact Fin.elim0 (f z)
  refine fibreMean_lipschitz_of_pointwise (k := k) (J := J) hk (G.neighborFinset v)
    (G.neighborFinset z ∩ G.neighborFinset v) f (z := z) x hz Finset.inter_subset_right
    (fun f' => occSlice G f' v J) (fun g => ?_)
  -- the one-vertex estimate, with `f z` in place of the colour of the grafted colouring at `z`
  have h := occSlice_update_out_le (V := V) (J := J) G (graft (G.neighborFinset v) g f) v hz x
  simpa only [graft_apply_of_notMem g f hz] using h

end Work.Deep.Sparse
