import Mathlib
import Submission.Work.RatHurewicz.cellDefs
import Submission.Work.RatHurewicz.avoidAux
import Submission.Work.RatHurewicz.pathConnected_punctured_simplex
import Submission.Work.RatHurewicz.cellShape

/-!
# Charts of the strata of the model `Model D`

The model `Work.RatHurewicz.Model D` of a cycle is the quotient of
`Work.RatHurewicz.Raw D = (Σ i, Δ^{n+1}) ⊕ (Σ i, I)` by the gluing relation
`Work.RatHurewicz.modelRel D`.  A *stratum* is the relative interior of a face of a copy of
`Δ^{n+1}`; the gluing relation never identifies two distinct points of the same stratum
(`Work.RatHurewicz.stratum_inj`), so the chart map

`chartMap D i S : stratum S → Model D`,   `x ↦ Quotient.mk'' (Sum.inl ⟨i, x⟩)`,

is injective.  It is moreover an *open* map onto the `(card S - 1)`-skeleton, which is the content
of `Work.RatHurewicz.isOpen_chartNhd` in `Submission/Work/RatHurewicz/modelAvoidOrigin.lean`.
This module only fixes the vocabulary (the stratum, the chart map, the ball in a chart, the image of
a chart set) and the elementary facts about supports that the proofs use.

The main statements of the area, stated in this vocabulary:

* `Work.RatHurewicz.isOpen_chartNhd` : the image of a relatively open set of a stratum is open in
  the skeleton `skel D (card S - 1)`;
* `Work.RatHurewicz.chartNhd_punctured_pathConnected` : the punctured ball of a chart is path
  connected;
* `Work.RatHurewicz.chartNhd_paths_homotopic` : two paths inside a chart ball with the same
  endpoints are homotopic.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The support of a point of the standard simplex -/

/-- The `shapeOf` of a point of the standard simplex has as many elements as its support. -/
theorem card_shapeOf {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (x : stdSimplex ℝ ι) : (shapeOf x).card = (suppOf x).card := by
  rw [shapeOf]
  exact Finset.card_image_of_injOn fun a ha b hb h => rankIn_injOn ha hb (congrArg Prod.fst h)

/-- **Points of the standard simplex close enough to `w` contain its support.** -/
theorem exists_subset_suppOf_near (w : stdSimplex ℝ (Fin (n + 2))) :
    ∃ δ > 0, ∀ w' : stdSimplex ℝ (Fin (n + 2)), dist w' w < δ → suppOf w ⊆ suppOf w' := by
  have hset : setOf (fun w' : stdSimplex ℝ (Fin (n + 2)) => suppOf w ⊆ suppOf w')
      = ⋂ k ∈ suppOf w, setOf (fun w' : stdSimplex ℝ (Fin (n + 2)) =>
          (0 : ℝ) < (w' : Fin (n + 2) → ℝ) k) := by
    ext w'
    simp only [Set.mem_iInter]
    constructor
    · intro h k hk
      exact lt_of_le_of_ne (w'.2.1 k) (Ne.symm (mem_suppOf.mp (h hk)))
    · intro h k hk
      exact mem_suppOf.mpr (ne_of_gt (h k hk))
  have hopen : IsOpen (setOf (fun w' : stdSimplex ℝ (Fin (n + 2)) => suppOf w ⊆ suppOf w')) :=
    hset ▸ isOpen_biInter_finset fun k _ =>
      isOpen_lt continuous_const (continuous_apply k |>.comp continuous_subtype_val)
  have hself : w ∈ setOf (fun w' : stdSimplex ℝ (Fin (n + 2)) => suppOf w ⊆ suppOf w') := by
    show suppOf w ⊆ suppOf w
    exact fun _ hx => hx
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hself)
  exact ⟨δ, hδ, fun w' hw' => hball (Metric.mem_ball.mpr hw')⟩

/-- **The equal-support form.**  Points close enough to `w` whose support is no larger than that
of `w` have the same support. -/
theorem suppOf_eq_of_dist_lt (w : stdSimplex ℝ (Fin (n + 2))) :
    ∃ δ > 0, ∀ w' : stdSimplex ℝ (Fin (n + 2)), dist w' w < δ →
      (suppOf w').card ≤ (suppOf w).card → suppOf w' = suppOf w := by
  obtain ⟨δ, hδ, h⟩ := exists_subset_suppOf_near w
  exact ⟨δ, hδ, fun w' hw' hcard =>
    (Finset.eq_of_subset_of_card_le (h w' hw') hcard).symm⟩

/-! ## The stratum of a face -/

/-- **The stratum of the face spanned by `S`**: the points of the standard simplex whose support is
exactly `S` (the relative interior of that face). -/
abbrev stratum (S : Finset (Fin (n + 2))) : Type :=
  {x : stdSimplex ℝ (Fin (n + 2)) // suppOf x = S}

/-- The support of a point of a stratum is the defining finite set. -/
theorem suppOf_stratum {S : Finset (Fin (n + 2))} (x : stratum S) : suppOf (x.1) = S := x.2

/-- **The chart map** of the stratum `S` in the `i`-th copy of the simplex. -/
def chartMap (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2))) :
    C(stratum S, Model D) :=
  (topMap D i).comp ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem chartMap_apply (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (x : stratum S) : chartMap D i S x = Quotient.mk'' (Sum.inl ⟨i, x.1⟩) := rfl

/-- The part of the chart of the stratum `S` inside the ball of radius `r` around `c`. -/
def chartBall (S : Finset (Fin (n + 2))) (c : stdSimplex ℝ (Fin (n + 2))) (r : ℝ) :
    Set (stratum S) :=
  setOf (fun x => dist x.1 c < r)

theorem mem_chartBall {S : Finset (Fin (n + 2))} {c : stdSimplex ℝ (Fin (n + 2))} {r : ℝ}
    {x : stratum S} : x ∈ chartBall S c r ↔ dist x.1 c < r := Iff.rfl

theorem isOpen_chartBall (S : Finset (Fin (n + 2))) (c : stdSimplex ℝ (Fin (n + 2))) (r : ℝ) :
    IsOpen (chartBall S c r) :=
  isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const

theorem chartBall_mem_self {S : Finset (Fin (n + 2))} {c : stdSimplex ℝ (Fin (n + 2))}
    (hc : suppOf c = S) {r : ℝ} (hr : 0 < r) : (⟨c, hc⟩ : stratum S) ∈ chartBall S c r := by
  rw [mem_chartBall, dist_self]; exact hr

/-- The image of a set of the chart of `S`, as a subset of the model. -/
def chartImage (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (N : Set (stratum S)) : Set (Model D) :=
  chartMap D i S '' N

/-- The same image, as a subset of the `(card S - 1)`-skeleton. -/
def chartNhd (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (N : Set (stratum S)) : Set (↥(skel D (S.card - 1))) :=
  setOf (fun z => ∃ x ∈ N, chartMap D i S x = (z : Model D))

theorem mem_chartNhd {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    {N : Set (stratum S)} {z : ↥(skel D (S.card - 1))} :
    z ∈ chartNhd D i S N ↔ ∃ x ∈ N, chartMap D i S x = (z : Model D) := Iff.rfl

theorem mem_chartImage {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    {N : Set (stratum S)} {z : Model D} :
    z ∈ chartImage D i S N ↔ ∃ x ∈ N, chartMap D i S x = z := Iff.rfl

/-- The points of the image of the chart of `S` lie in the `(card S - 1)`-skeleton. -/
theorem chartImage_subset_skel (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (N : Set (stratum S)) : chartImage D i S N ⊆ skel D (S.card - 1) := by
  rintro z ⟨x, -, rfl⟩
  rw [chartMap_apply]
  refine ⟨Sum.inl ⟨i, x.1⟩, rfl, ?_⟩
  show (suppOf x.1).card ≤ S.card - 1 + 1
  rw [x.2]
  omega

/-- The points of `chartNhd` are the points of `chartImage` lying in the skeleton. -/
theorem chartNhd_eq_preimage (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (N : Set (stratum S)) :
    chartNhd D i S N
      = Subtype.val ⁻¹' chartImage D i S N := by
  ext z
  simp only [mem_chartNhd, Set.mem_preimage, mem_chartImage]

/-- **The chart is injective on a stratum**: two points of the same stratum of the same copy with
the same image in the model are equal. -/
theorem chartMap_injective (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2))) :
    Function.Injective (chartMap D i S) := by
  intro x y hxy
  refine Subtype.ext (eq_of_eqvGen_sameSupp (i := i) (Quotient.exact hxy) ?_)
  rw [x.2, y.2]

/-- **Openness of a chart set at a point, in the explicit `ε` form.** -/
theorem exists_dist_lt_of_isOpen {S : Finset (Fin (n + 2))} {N : Set (stratum S)}
    (hN : IsOpen N) {x : stratum S} (hx : x ∈ N) :
    ∃ ε > 0, ∀ x' : stratum S, dist x'.1 x.1 < ε → x' ∈ N := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp (hN.mem_nhds hx)
  refine ⟨ε, hε, fun x' hx' => h ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq]
  exact hx'

/-- The segment between two points of `stratum S` stays in the standard simplex. -/
theorem combo_mem_simplex {S : Finset (Fin (n + 2))} (x y : stratum S) {s : ℝ}
    (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (1 - s) • (x.1 : Fin (n + 2) → ℝ) + s • (y.1 : Fin (n + 2) → ℝ)
      ∈ stdSimplex ℝ (Fin (n + 2)) := by
  refine ⟨fun k => ?_, ?_⟩
  · have hx' : 0 ≤ (x.1 : Fin (n + 2) → ℝ) k := x.1.2.1 k
    have hy' : 0 ≤ (y.1 : Fin (n + 2) → ℝ) k := y.1.2.1 k
    have hcoe : ((1 - s) • (x.1 : Fin (n + 2) → ℝ) + s • (y.1 : Fin (n + 2) → ℝ)) k
        = (1 - s) * (x.1 : Fin (n + 2) → ℝ) k + s * (y.1 : Fin (n + 2) → ℝ) k := rfl
    rw [hcoe]
    exact add_nonneg (mul_nonneg (by linarith) hx') (mul_nonneg h0 hy')
  · have hx1 : ∑ k, (x.1 : Fin (n + 2) → ℝ) k = 1 := x.1.2.2
    have hy1 : ∑ k, (y.1 : Fin (n + 2) → ℝ) k = 1 := y.1.2.2
    have hsum : (∑ k, ((1 - s) • (x.1 : Fin (n + 2) → ℝ) + s • (y.1 : Fin (n + 2) → ℝ)) k)
        = (1 - s) * ∑ k, (x.1 : Fin (n + 2) → ℝ) k
          + s * ∑ k, (y.1 : Fin (n + 2) → ℝ) k := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => rfl
    rw [hsum, hx1, hy1]
    ring

/-- Also the segment stays in the stratum. -/
theorem suppOf_combo {S : Finset (Fin (n + 2))} (x y : stratum S) {s : ℝ}
    (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    suppOf (⟨(1 - s) • (x.1 : Fin (n + 2) → ℝ) + s • (y.1 : Fin (n + 2) → ℝ),
      combo_mem_simplex x y h0 h1⟩ : stdSimplex ℝ (Fin (n + 2))) = S := by
  rw [suppOf_eq_iff]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hx' : 0 < (x.1 : Fin (n + 2) → ℝ) k := ((suppOf_eq_iff x.1).mp x.2).1 k hk
    have hy' : 0 < (y.1 : Fin (n + 2) → ℝ) k := ((suppOf_eq_iff y.1).mp y.2).1 k hk
    show 0 < (1 - s) * (x.1 : Fin (n + 2) → ℝ) k + s * (y.1 : Fin (n + 2) → ℝ) k
    rcases eq_or_lt_of_le h1 with h | h
    · rw [h, sub_self, zero_mul, zero_add, one_mul]; exact hy'
    · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hx') (mul_nonneg h0 (le_of_lt hy'))
  · have hx' : (x.1 : Fin (n + 2) → ℝ) k = 0 := ((suppOf_eq_iff x.1).mp x.2).2 k hk
    have hy' : (y.1 : Fin (n + 2) → ℝ) k = 0 := ((suppOf_eq_iff y.1).mp y.2).2 k hk
    show (1 - s) * (x.1 : Fin (n + 2) → ℝ) k + s * (y.1 : Fin (n + 2) → ℝ) k = 0
    rw [hx', hy', mul_zero, mul_zero, add_zero]

/-- The segment between two points of a stratum, as a point of that stratum. -/
def stratumCombo {S : Finset (Fin (n + 2))} (x y : stratum S) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    stratum S :=
  ⟨⟨(1 - s) • (x.1 : Fin (n + 2) → ℝ) + s • (y.1 : Fin (n + 2) → ℝ),
      combo_mem_simplex x y h0 h1⟩, suppOf_combo x y h0 h1⟩

@[simp] theorem stratumCombo_coe {S : Finset (Fin (n + 2))} (x y : stratum S) (s : ℝ)
    (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (stratumCombo x y s h0 h1 : stdSimplex ℝ (Fin (n + 2)))
      = ⟨(1 - s) • (x.1 : Fin (n + 2) → ℝ) + s • (y.1 : Fin (n + 2) → ℝ),
          combo_mem_simplex x y h0 h1⟩ := rfl

theorem stratumCombo_apply {S : Finset (Fin (n + 2))} (x y : stratum S) (s : ℝ)
    (h0 : 0 ≤ s) (h1 : s ≤ 1) (k : Fin (n + 2)) :
    (stratumCombo x y s h0 h1).1.1 k
      = (1 - s) * (x.1 : Fin (n + 2) → ℝ) k + s * (y.1 : Fin (n + 2) → ℝ) k := rfl

end

end Work.RatHurewicz
