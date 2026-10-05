import Mathlib

set_option linter.unusedVariables false

namespace Work.RPB1a.Caratheodory.Brouwer

open Set Metric

/-!
# A square boundary lying in the unbounded component of the complement of a compact set

Let `K ⊆ ℝ × ℝ` be compact, `p` any point, and `x` a point of `Kᶜ` whose connected component in
`Kᶜ` is unbounded.  Then there is `R > 0` such that `K` is contained in the open square of radius
`R` centred at `p` (in the sup-norm `max |·- p.1| ‖·- p.2‖`) and the whole boundary square of
radius `R` is contained in that unbounded component.

The proof is the observation that the closed exterior

  `E_R = {y | R ≤ dist y p}`

of the open square is connected, is contained in `Kᶜ` as soon as `K` is contained in the open
square, and meets the unbounded component of `x` (which must leave every bounded set, in
particular the closed square `{y | dist y p ≤ R}`).  A connected set contained in `Kᶜ` lies in a
single connected component of `Kᶜ`, so `E_R` — and with it the boundary square — lies in the
component of `x`.

Note that `ℝ × ℝ` carries the product metric, i.e. the sup-metric, so
`dist y p = max |y.1 - p.1| |y.2 - p.2|`; this is `dist_prod_eq_max` below.
-/

/-- The distance on the product `ℝ × ℝ` (product/sup metric) in coordinates. -/
theorem dist_prod_eq_max (y p : ℝ × ℝ) : dist y p = max |y.1 - p.1| |y.2 - p.2| := by
  rw [Prod.dist_eq]; simp [Real.dist_eq]

/-- The closed exterior of the open square of radius `R` about `p` is the union of the two vertical
and the two horizontal "outer" half-planes. -/
private lemma exterior_eq (p : ℝ × ℝ) (R : ℝ) :
    {y : ℝ × ℝ | R ≤ dist y p}
      = ({y : ℝ × ℝ | p.1 + R ≤ y.1} ∪ {y : ℝ × ℝ | p.2 + R ≤ y.2})
        ∪ ({y : ℝ × ℝ | y.1 ≤ p.1 - R} ∪ {y : ℝ × ℝ | y.2 ≤ p.2 - R}) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  rw [dist_prod_eq_max]
  constructor
  · intro h
    rcases le_max_iff.mp h with h | h <;> rcases le_abs.mp h with h | h
    · exact Or.inl (Or.inl (by linarith))
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inl (Or.inr (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro ((h | h) | (h | h))
    · exact le_max_iff.mpr (Or.inl (le_abs.mpr (Or.inl (by linarith))))
    · exact le_max_iff.mpr (Or.inr (le_abs.mpr (Or.inl (by linarith))))
    · exact le_max_iff.mpr (Or.inl (le_abs.mpr (Or.inr (by linarith))))
    · exact le_max_iff.mpr (Or.inr (le_abs.mpr (Or.inr (by linarith))))

/-- The closed exterior `{y : ℝ × ℝ | R ≤ dist y p}` of the open square of radius `R` about `p` is
(pre)connected.  It is the union of the two opposite "L-shaped" pairs of half-planes
`{y | p.1 + R ≤ y.1} ∪ {y | p.2 + R ≤ y.2}` and `{y | y.1 ≤ p.1 - R} ∪ {y | y.2 ≤ p.2 - R}`, each of
which is a union of two half-planes meeting in a quadrant, and the two pieces meet in the quadrant
`{y | p.1 + R ≤ y.1, y.2 ≤ p.2 - R}`. -/
theorem isPreconnected_setOf_le_dist (p : ℝ × ℝ) (R : ℝ) :
    IsPreconnected {y : ℝ × ℝ | R ≤ dist y p} := by
  have hA : IsPreconnected {y : ℝ × ℝ | p.1 + R ≤ y.1} := by
    have h : {y : ℝ × ℝ | p.1 + R ≤ y.1} = Set.Ici (p.1 + R) ×ˢ Set.univ := by
      ext y; simp [Set.mem_prod]
    rw [h]; exact isPreconnected_Ici.prod isPreconnected_univ
  have hB : IsPreconnected {y : ℝ × ℝ | y.1 ≤ p.1 - R} := by
    have h : {y : ℝ × ℝ | y.1 ≤ p.1 - R} = Set.Iic (p.1 - R) ×ˢ Set.univ := by
      ext y; simp [Set.mem_prod]
    rw [h]; exact isPreconnected_Iic.prod isPreconnected_univ
  have hC : IsPreconnected {y : ℝ × ℝ | p.2 + R ≤ y.2} := by
    have h : {y : ℝ × ℝ | p.2 + R ≤ y.2} = Set.univ ×ˢ Set.Ici (p.2 + R) := by
      ext y; simp [Set.mem_prod]
    rw [h]; exact isPreconnected_univ.prod isPreconnected_Ici
  have hD : IsPreconnected {y : ℝ × ℝ | y.2 ≤ p.2 - R} := by
    have h : {y : ℝ × ℝ | y.2 ≤ p.2 - R} = Set.univ ×ˢ Set.Iic (p.2 - R) := by
      ext y; simp [Set.mem_prod]
    rw [h]; exact isPreconnected_univ.prod isPreconnected_Iic
  have hAC : IsPreconnected
      ({y : ℝ × ℝ | p.1 + R ≤ y.1} ∪ {y : ℝ × ℝ | p.2 + R ≤ y.2}) :=
    IsPreconnected.union'
      ⟨(p.1 + R + 1, p.2 + R + 1),
        by simp only [Set.mem_ofPred_eq]; linarith,
        by simp only [Set.mem_ofPred_eq]; linarith⟩ hA hC
  have hBD : IsPreconnected
      ({y : ℝ × ℝ | y.1 ≤ p.1 - R} ∪ {y : ℝ × ℝ | y.2 ≤ p.2 - R}) :=
    IsPreconnected.union'
      ⟨(p.1 - R - 1, p.2 - R - 1),
        by simp only [Set.mem_ofPred_eq]; linarith,
        by simp only [Set.mem_ofPred_eq]; linarith⟩ hB hD
  have hfin : IsPreconnected
      (({y : ℝ × ℝ | p.1 + R ≤ y.1} ∪ {y : ℝ × ℝ | p.2 + R ≤ y.2})
        ∪ ({y : ℝ × ℝ | y.1 ≤ p.1 - R} ∪ {y : ℝ × ℝ | y.2 ≤ p.2 - R})) :=
    IsPreconnected.union'
      ⟨(p.1 + R + 1, p.2 - R - 1),
        Or.inl (by simp only [Set.mem_ofPred_eq]; linarith),
        Or.inr (by simp only [Set.mem_ofPred_eq]; linarith)⟩ hAC hBD
  rwa [← exterior_eq p R] at hfin

theorem exists_square_boundary_subset_of_isCompact_isUnbounded_component
    (K : Set (ℝ × ℝ)) (hKc : IsCompact K) (p : ℝ × ℝ) {x : ℝ × ℝ} (hx : x ∈ Kᶜ)
    (hUnb : ¬ Bornology.IsBounded (connectedComponentIn (Kᶜ) x)) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ {y | max |y.1 - p.1| |y.2 - p.2| < R} ∧
      {y | max |y.1 - p.1| |y.2 - p.2| = R} ⊆ connectedComponentIn (Kᶜ) x := by
  -- `K` is contained in some closed square centred at `p`.
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall p).mp hKc.isBounded
  have hKr : ∀ y ∈ K, dist y p ≤ r := fun y hy => Metric.mem_closedBall.mp (hr hy)
  refine ⟨max r 0 + 1, by linarith [le_max_right r 0], ?_, ?_⟩
  · -- `K` lies in the open square of radius `max r 0 + 1`.
    intro y hy
    have h1 : dist y p ≤ r := hKr y hy
    have h2 : r ≤ max r 0 := le_max_left r 0
    have h3 : dist y p < max r 0 + 1 := by linarith
    rwa [dist_prod_eq_max] at h3
  · intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    -- `y` lies in the closed exterior `E` of the open square.
    have hyR : max r 0 + 1 ≤ dist y p := by
      rw [dist_prod_eq_max, hy]
    -- The unbounded component of `x` leaves the closed square, so it meets `E`.
    have hz : ∃ z ∈ connectedComponentIn (Kᶜ) x, max r 0 + 1 < dist z p := by
      by_contra hcon
      have hcon' : ∀ z ∈ connectedComponentIn (Kᶜ) x, dist z p ≤ max r 0 + 1 := by
        intro z hz
        by_contra hlt
        exact hcon ⟨z, hz, not_le.mp hlt⟩
      have hsub : connectedComponentIn (Kᶜ) x ⊆ Metric.closedBall p (max r 0 + 1) :=
        fun z hz => Metric.mem_closedBall.mpr (hcon' z hz)
      exact hUnb (Metric.isBounded_closedBall.subset hsub)
    obtain ⟨z, hzU, hzR⟩ := hz
    -- `E` is connected and contained in `Kᶜ`.
    have hEpc : IsPreconnected {w : ℝ × ℝ | max r 0 + 1 ≤ dist w p} :=
      isPreconnected_setOf_le_dist p (max r 0 + 1)
    have hEsub : {w : ℝ × ℝ | max r 0 + 1 ≤ dist w p} ⊆ (Kᶜ) := by
      intro w hw
      simp only [Set.mem_ofPred_eq] at hw
      rw [Set.mem_compl_iff]
      intro hwK
      have h1 : dist w p ≤ r := hKr w hwK
      have h2 : r ≤ max r 0 := le_max_left r 0
      linarith
    -- Hence `E` sits in the component of `z`, which is the component of `x`.
    have hsub := hEpc.subset_connectedComponentIn (le_of_lt hzR) hEsub
    have hyE : y ∈ {w : ℝ × ℝ | max r 0 + 1 ≤ dist w p} := hyR
    have hyz : y ∈ connectedComponentIn (Kᶜ) z := hsub hyE
    rwa [← connectedComponentIn_eq hzU] at hyz

end Work.RPB1a.Caratheodory.Brouwer
