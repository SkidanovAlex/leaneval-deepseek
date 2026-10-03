import Mathlib
import Submission.Work.PlanarSC.HullDefs
import Submission.Lib.Unif2.Commons.Topology.Plane.maxCell_interior_disjoint

/-!
# The hull of a dyadic polyomino is a dyadic polyomino

`compHull A` (`Submission/Work/PlanarSC/HullDefs.lean`) is the set of points whose connected
component in `Aᶜ` is bounded — for closed `A` this is `A` together with the bounded components of
`Aᶜ` ("filling in the holes").

The target of this file is: if `A = dyadicPolyomino n S` is a finite union of level-`n` closed
dyadic cells, then so is `compHull A`, at the *same* level `n`:

`compHull (dyadicPolyomino n S) = dyadicPolyomino n S'` for a finite `S'`.

The construction of `S'` is the natural one: keep the cells `dSq n p` which are *contained* in the
hull.  Two facts make this work:

* every dyadic cell is convex, so its interior is preconnected; hence for a cell `dSq n p` whose
  interior meets the hull, the whole cell lies in the hull (a preconnected subset of `Aᶜ` stays in
  one complementary component; here either `p ∈ S`, so `dSq n p ⊆ A ⊆ compHull A`, or the interior
  of the cell is disjoint from `A` and cannot cross the boundary of the hull, which is closed);
* conversely every point of the hull lies in such a cell: if it is in `A`, use a cell of `S`; if it
  is not, then `Aᶜ` is an open neighbourhood, and the point lies in the closure of the interior of
  any cell containing it, so a nearby interior point of that cell is in the same complementary
  component, hence in the hull.

Finiteness of `S'` follows because the hull of the (bounded) polyomino is contained in a closed
ball, and only finitely many level-`n` cells can meet a bounded set.

The helpers below are all prefixed `esh_` (for `exists_finset_compHull_eq`) so that they do not
collide with the sibling lemmas of colleagues in the same namespace.
-/

open Set Metric
open Commons.Topology.Plane (dSq dInt)

namespace Work.PlanarSC

/-! ## 1. Geometry of one dyadic cell -/

/-- The closed level-`n` dyadic cell `dSq n p` is convex (an intersection of two closed strips). -/
theorem esh_convex_dSq (n : ℕ) (p : ℤ × ℤ) : Convex ℝ (dSq n p) := by
  have h : dSq n p =
      {z : ℂ | z.re ∈ Set.Icc ((p.1 : ℝ) / 2 ^ n) (((p.1 : ℝ) + 1) / 2 ^ n)} ∩
        {z : ℂ | z.im ∈ Set.Icc ((p.2 : ℝ) / 2 ^ n) (((p.2 : ℝ) + 1) / 2 ^ n)} := by
    ext z
    simp only [dSq, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc]
    tauto
  rw [h]
  exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

/-- The open dyadic cell `dInt n p` is open. -/
theorem esh_isOpen_dInt (n : ℕ) (p : ℤ × ℤ) : IsOpen (dInt n p) := by
  have h : dInt n p =
      ({z : ℂ | (p.1 : ℝ) / 2 ^ n < z.re} ∩ {z : ℂ | z.re < ((p.1 : ℝ) + 1) / 2 ^ n}) ∩
      ({z : ℂ | (p.2 : ℝ) / 2 ^ n < z.im} ∩ {z : ℂ | z.im < ((p.2 : ℝ) + 1) / 2 ^ n}) := by
    ext z
    simp only [dInt, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [h]
  refine IsOpen.inter (IsOpen.inter ?_ ?_) (IsOpen.inter ?_ ?_)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt Complex.continuous_re continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact isOpen_lt Complex.continuous_im continuous_const

/-- The open dyadic cell `dInt n p` is nonempty (its centre is in it). -/
theorem esh_dInt_nonempty (n : ℕ) (p : ℤ × ℤ) : (dInt n p).Nonempty := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨⟨((p.1 : ℝ) + 1 / 2) / 2 ^ n, ((p.2 : ℝ) + 1 / 2) / 2 ^ n⟩, ?_, ?_, ?_, ?_⟩
  · show (p.1 : ℝ) / 2 ^ n < ((p.1 : ℝ) + 1 / 2) / 2 ^ n
    rw [div_lt_div_iff_of_pos_right h2n]; linarith
  · show ((p.1 : ℝ) + 1 / 2) / 2 ^ n < ((p.1 : ℝ) + 1) / 2 ^ n
    rw [div_lt_div_iff_of_pos_right h2n]; linarith
  · show (p.2 : ℝ) / 2 ^ n < ((p.2 : ℝ) + 1 / 2) / 2 ^ n
    rw [div_lt_div_iff_of_pos_right h2n]; linarith
  · show ((p.2 : ℝ) + 1 / 2) / 2 ^ n < ((p.2 : ℝ) + 1) / 2 ^ n
    rw [div_lt_div_iff_of_pos_right h2n]; linarith

/-- The open dyadic cell lies in the interior of the closed one. -/
theorem esh_dInt_subset_interior_dSq (n : ℕ) (p : ℤ × ℤ) : dInt n p ⊆ interior (dSq n p) :=
  interior_maximal (fun z hz => by
    obtain ⟨h1, h2, h3, h4⟩ := hz
    exact ⟨h1.le, h2.le, h3.le, h4.le⟩) (esh_isOpen_dInt n p)

/-- The interior of a dyadic cell is nonempty. -/
theorem esh_interior_dSq_nonempty (n : ℕ) (p : ℤ × ℤ) : (interior (dSq n p)).Nonempty :=
  (esh_dInt_nonempty n p).mono (esh_dInt_subset_interior_dSq n p)

/-- A closed dyadic cell is the closure of its interior. -/
theorem esh_closure_interior_dSq (n : ℕ) (p : ℤ × ℤ) :
    closure (interior (dSq n p)) = dSq n p := by
  rw [Convex.closure_interior_eq_closure_of_nonempty_interior (esh_convex_dSq n p)
      (esh_interior_dSq_nonempty n p),
    IsClosed.closure_eq (Commons.Topology.Plane.isClosed_dSq n p)]

/-- Every point of a closed dyadic cell is a limit point of its interior. -/
theorem esh_dSq_subset_closure_interior (n : ℕ) (p : ℤ × ℤ) :
    dSq n p ⊆ closure (interior (dSq n p)) := by
  rw [esh_closure_interior_dSq n p]

/-- The interior of a dyadic cell is preconnected (it is convex). -/
theorem esh_isPreconnected_interior_dSq (n : ℕ) (p : ℤ × ℤ) :
    IsPreconnected (interior (dSq n p)) :=
  (esh_convex_dSq n p).interior.isPreconnected

/-! ## 2. Closures -/

/-- A dyadic polyomino is closed (a finite union of closed cells). -/
theorem esh_isClosed_dyadicPolyomino (n : ℕ) (S : Finset (ℤ × ℤ)) :
    IsClosed (dyadicPolyomino n S) := by
  rw [dyadicPolyomino]
  exact isClosed_biUnion_finset (fun p _ => Commons.Topology.Plane.isClosed_dSq n p)

/-- The hull of a closed subset of the plane is closed: its complement is the union of the
unbounded components of `Aᶜ`, and components of the open set `Aᶜ` are open. -/
theorem esh_isClosed_compHull {A : Set ℂ} (hA : IsClosed A) : IsClosed (compHull A) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [compl_compHull] at hx
  simp only [Set.mem_ofPred_eq] at hx
  have hxU : x ∈ Aᶜ := by
    by_contra h
    rw [connectedComponentIn_eq_empty h] at hx
    exact hx Bornology.isBounded_empty
  have hsub : connectedComponentIn Aᶜ x ⊆ (compHull A)ᶜ := by
    intro y hy
    rw [compl_compHull]
    change ¬ Bornology.IsBounded (connectedComponentIn Aᶜ y)
    rw [← connectedComponentIn_eq hy]
    exact hx
  exact Filter.mem_of_superset
    ((hA.isOpen_compl.connectedComponentIn (x := x)).mem_nhds (mem_connectedComponentIn hxU))
    hsub

/-! ## 3. Boundedness of cells and polyominoes -/

/-- A closed dyadic cell is bounded. -/
theorem esh_isBounded_dSq (n : ℕ) (p : ℤ × ℤ) : Bornology.IsBounded (dSq n p) := by
  refine (isBounded_closedBall (x := (0 : ℂ))
    (r := 2 * |(p.1 : ℝ)| + 2 * |(p.2 : ℝ)| + 4)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨h1a, h1b, h2a, h2b⟩ := hz
  have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have ha : |(p.1 : ℝ) / 2 ^ n| ≤ |(p.1 : ℝ)| := by
    rw [abs_div, abs_of_nonneg h2pos]
    exact div_le_self (abs_nonneg _) hpow
  have hb' : |((p.1 : ℝ) + 1) / 2 ^ n| ≤ |(p.1 : ℝ)| + 1 := by
    rw [abs_div, abs_of_nonneg h2pos]
    calc |(p.1 : ℝ) + 1| / 2 ^ n ≤ |(p.1 : ℝ) + 1| := div_le_self (abs_nonneg _) hpow
      _ ≤ |(p.1 : ℝ)| + 1 := by simpa using abs_add_le (p.1 : ℝ) 1
  have hca : |(p.2 : ℝ) / 2 ^ n| ≤ |(p.2 : ℝ)| := by
    rw [abs_div, abs_of_nonneg h2pos]
    exact div_le_self (abs_nonneg _) hpow
  have hcb : |((p.2 : ℝ) + 1) / 2 ^ n| ≤ |(p.2 : ℝ)| + 1 := by
    rw [abs_div, abs_of_nonneg h2pos]
    calc |(p.2 : ℝ) + 1| / 2 ^ n ≤ |(p.2 : ℝ) + 1| := div_le_self (abs_nonneg _) hpow
      _ ≤ |(p.2 : ℝ)| + 1 := by simpa using abs_add_le (p.2 : ℝ) 1
  have hre : |z.re| ≤ 2 * |(p.1 : ℝ)| + 2 := by
    have habs : |z.re| ≤ |(p.1 : ℝ) / 2 ^ n| + |((p.1 : ℝ) + 1) / 2 ^ n| := by
      rw [abs_le]
      constructor
      · calc -(|(p.1 : ℝ) / 2 ^ n| + |((p.1 : ℝ) + 1) / 2 ^ n|)
            ≤ -|(p.1 : ℝ) / 2 ^ n| := by linarith [abs_nonneg (((p.1 : ℝ) + 1) / 2 ^ n)]
          _ ≤ (p.1 : ℝ) / 2 ^ n := neg_abs_le _
          _ ≤ z.re := h1a
      · calc z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n := h1b
          _ ≤ |((p.1 : ℝ) + 1) / 2 ^ n| := le_abs_self _
          _ ≤ |(p.1 : ℝ) / 2 ^ n| + |((p.1 : ℝ) + 1) / 2 ^ n| :=
              by linarith [abs_nonneg ((p.1 : ℝ) / 2 ^ n)]
    linarith
  have him : |z.im| ≤ 2 * |(p.2 : ℝ)| + 2 := by
    have habs : |z.im| ≤ |(p.2 : ℝ) / 2 ^ n| + |((p.2 : ℝ) + 1) / 2 ^ n| := by
      rw [abs_le]
      constructor
      · calc -(|(p.2 : ℝ) / 2 ^ n| + |((p.2 : ℝ) + 1) / 2 ^ n|)
            ≤ -|(p.2 : ℝ) / 2 ^ n| := by linarith [abs_nonneg (((p.2 : ℝ) + 1) / 2 ^ n)]
          _ ≤ (p.2 : ℝ) / 2 ^ n := neg_abs_le _
          _ ≤ z.im := h2a
      · calc z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n := h2b
          _ ≤ |((p.2 : ℝ) + 1) / 2 ^ n| := le_abs_self _
          _ ≤ |(p.2 : ℝ) / 2 ^ n| + |((p.2 : ℝ) + 1) / 2 ^ n| :=
              by linarith [abs_nonneg ((p.2 : ℝ) / 2 ^ n)]
    linarith
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 2 * |(p.1 : ℝ)| + 2 * |(p.2 : ℝ)| + 4 := by linarith

/-- A dyadic polyomino is bounded (a finite union of bounded cells). -/
theorem esh_isBounded_dyadicPolyomino (n : ℕ) (S : Finset (ℤ × ℤ)) :
    Bornology.IsBounded (dyadicPolyomino n S) := by
  rw [dyadicPolyomino]
  exact (Bornology.isBounded_biUnion_finset S).mpr (fun p _ => esh_isBounded_dSq n p)

/-! ## 4. The hull of a set inside a ball stays inside the ball -/

/-- If `A` is contained in the closed ball of radius `R ≥ 0` about `0`, then so is `compHull A`:
from a point `z` outside that ball the ray `t ↦ (1 + t) • z` is a connected unbounded subset of
`Aᶜ`, so the component of `z` in `Aᶜ` is unbounded. -/
theorem esh_compHull_subset_closedBall {A : Set ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hA : A ⊆ Metric.closedBall 0 R) : compHull A ⊆ Metric.closedBall 0 R := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  rw [not_le] at hlt
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hR hlt
  -- the ray through `z` pointing away from the origin
  have hpre0 : IsPreconnected (Set.Ici (0 : ℝ)) := (convex_Ici 0).isPreconnected
  have hcont : Continuous (fun t : ℝ => (1 + t) • z) :=
    (continuous_const.add continuous_id).smul continuous_const
  have hpre : IsPreconnected ((fun t : ℝ => (1 + t) • z) '' Set.Ici (0 : ℝ)) :=
    hpre0.image _ hcont.continuousOn
  have hraysub : ((fun t : ℝ => (1 + t) • z) '' Set.Ici (0 : ℝ)) ⊆ Aᶜ := by
    rintro w ⟨t, ht, rfl⟩
    rw [Set.mem_compl_iff]
    intro hwA
    have hw1 : ‖(1 + t) • z‖ ≤ R := by
      have := hA hwA
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have ht0 : (0 : ℝ) ≤ t := Set.mem_Ici.mp ht
    have hnorm : ‖(1 + t) • z‖ = (1 + t) * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)]
    rw [hnorm] at hw1
    have : ‖z‖ ≤ (1 + t) * ‖z‖ :=
      le_mul_of_one_le_left (le_of_lt hzpos) (by linarith : (1 : ℝ) ≤ 1 + t)
    linarith
  have hzray : z ∈ (fun t : ℝ => (1 + t) • z) '' Set.Ici (0 : ℝ) :=
    ⟨0, Set.mem_Ici.mpr (le_refl 0), by simp⟩
  have hsub : ((fun t : ℝ => (1 + t) • z) '' Set.Ici (0 : ℝ)) ⊆ connectedComponentIn Aᶜ z :=
    IsPreconnected.subset_connectedComponentIn hpre hzray hraysub
  have hrayunb : ¬ Bornology.IsBounded ((fun t : ℝ => (1 + t) • z) '' Set.Ici (0 : ℝ)) := by
    intro hb
    obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
    set t : ℝ := (max ρ 0 + 1) / ‖z‖ with ht
    have ht0 : (0 : ℝ) ≤ t := by
      rw [ht]
      exact div_nonneg (by linarith [le_max_right ρ 0]) (le_of_lt hzpos)
    have hmem : (1 + t) • z ∈ (fun t : ℝ => (1 + t) • z) '' Set.Ici (0 : ℝ) :=
      ⟨t, Set.mem_Ici.mpr ht0, rfl⟩
    have hle : ‖(1 + t) • z‖ ≤ ρ := by
      have := hρ hmem
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have htval : (1 + t) * ‖z‖ = ‖z‖ + (max ρ 0 + 1) := by
      rw [ht, add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hzpos)]
    have hnorm : ‖(1 + t) • z‖ = (1 + t) * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht0] : (0 : ℝ) ≤ 1 + t)]
    rw [hnorm, htval] at hle
    have : max ρ 0 < ‖z‖ + (max ρ 0 + 1) := by linarith [hzpos]
    linarith [le_max_left ρ 0]
  exact hrayunb ((mem_compHull.mp hz).subset hsub)

/-! ## 5. A cell whose interior meets the hull lies in the hull -/

/-- If `p ∉ S` then the interior of `dSq n p` is disjoint from the polyomino `⋃_{q ∈ S} dSq n q`:
a point of the interior of a cell determines that cell. -/
theorem esh_interior_dSq_inter_polyomino {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    (hp : p ∉ S) : interior (dSq n p) ∩ dyadicPolyomino n S = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzi, hzA⟩
  obtain ⟨q, hq, hzq⟩ := mem_dyadicPolyomino.mp hzA
  have hqp : p = q := Commons.Topology.Plane.eq_of_mem_interior_of_mem_cell hzi hzq
  rw [← hqp] at hq
  exact hp hq

/-- If a point of the hull of a polyomino lies in the interior of a cell, then that whole cell is
contained in the hull. -/
theorem esh_dSq_subset_compHull_of_mem_interior {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    {y : ℂ} (hy : y ∈ compHull (dyadicPolyomino n S)) (hyi : y ∈ interior (dSq n p)) :
    dSq n p ⊆ compHull (dyadicPolyomino n S) := by
  by_cases hp : p ∈ S
  · intro w hw
    exact subset_compHull (mem_dyadicPolyomino.mpr ⟨p, hp, hw⟩)
  · have hempty := esh_interior_dSq_inter_polyomino (n := n) (S := S) (p := p) hp
    have hsub : interior (dSq n p) ⊆ (dyadicPolyomino n S)ᶜ := by
      intro z hz
      simp only [mem_compl_iff]
      intro hzA
      exact Set.eq_empty_iff_forall_notMem.mp hempty z ⟨hz, hzA⟩
    have hint : interior (dSq n p) ⊆ compHull (dyadicPolyomino n S) := by
      intro w hw
      have hwcomp : w ∈ connectedComponentIn (dyadicPolyomino n S)ᶜ y :=
        IsPreconnected.subset_connectedComponentIn (esh_isPreconnected_interior_dSq n p) hyi hsub hw
      rw [mem_compHull, ← connectedComponentIn_eq hwcomp]
      exact mem_compHull.mp hy
    intro w hw
    have h1 : w ∈ closure (interior (dSq n p)) := esh_dSq_subset_closure_interior n p hw
    have h2 : w ∈ closure (compHull (dyadicPolyomino n S)) := closure_mono hint h1
    rwa [IsClosed.closure_eq (esh_isClosed_compHull (esh_isClosed_dyadicPolyomino n S))] at h2

/-! ## 6. Index bounds for a cell inside a ball -/

/-- If a level-`n` cell sits inside the ball of radius `R` about the origin, then its index
coordinates are bounded by `R * 2 ^ n`. -/
theorem esh_abs_le_of_dSq_subset_ball {n : ℕ} {p : ℤ × ℤ} {R : ℝ}
    (h : dSq n p ⊆ Metric.ball 0 R) :
    |(p.1 : ℝ)| ≤ R * 2 ^ n ∧ |(p.2 : ℝ)| ≤ R * 2 ^ n := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  set c : ℂ := ⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ with hc
  have hcmem : c ∈ dSq n p := by
    refine ⟨le_refl _, ?_, le_refl _, ?_⟩ <;>
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h2n)
  have hcball : ‖c‖ < R := by
    have := h hcmem
    rwa [Metric.mem_ball, dist_zero_right] at this
  have hre : |(p.1 : ℝ)| / 2 ^ n < R := by
    have h1 : |c.re| ≤ ‖c‖ := Complex.abs_re_le_norm c
    have h2 : c.re = (p.1 : ℝ) / 2 ^ n := rfl
    rw [h2, abs_div, abs_of_pos h2n] at h1
    exact lt_of_le_of_lt h1 hcball
  have him : |(p.2 : ℝ)| / 2 ^ n < R := by
    have h1 : |c.im| ≤ ‖c‖ := Complex.abs_im_le_norm c
    have h2 : c.im = (p.2 : ℝ) / 2 ^ n := rfl
    rw [h2, abs_div, abs_of_pos h2n] at h1
    exact lt_of_le_of_lt h1 hcball
  constructor
  · rw [div_lt_iff₀ h2n] at hre; linarith
  · rw [div_lt_iff₀ h2n] at him; linarith

/-! ## 7. The target -/

/-- The hull fills in the bounded components of the complement, and a finite union of level-`n`
dyadic cells has a hull which is again a finite union of level-`n` dyadic cells. -/
theorem exists_finset_compHull_eq (n : ℕ) (S : Finset (ℤ × ℤ)) :
    ∃ S' : Finset (ℤ × ℤ), compHull (dyadicPolyomino n S) = dyadicPolyomino n S' := by
  classical
  -- the polyomino is bounded, so its hull is contained in a closed ball of radius `R ≥ 0`
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    (esh_isBounded_dyadicPolyomino n S)
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRsub : dyadicPolyomino n S ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hbdd : compHull (dyadicPolyomino n S) ⊆ Metric.closedBall 0 R :=
    esh_compHull_subset_closedBall hR0 hRsub
  -- every point of the hull is covered by a cell which lies in the hull
  have hsat : ∀ z ∈ compHull (dyadicPolyomino n S),
      ∃ p : ℤ × ℤ, z ∈ dSq n p ∧ dSq n p ⊆ compHull (dyadicPolyomino n S) := by
    intro z hz
    by_cases hzA : z ∈ dyadicPolyomino n S
    · obtain ⟨p, hp, hzp⟩ := mem_dyadicPolyomino.mp hzA
      exact ⟨p, hzp, fun w hw => subset_compHull (mem_dyadicPolyomino.mpr ⟨p, hp, hw⟩)⟩
    · have hzU : z ∈ (dyadicPolyomino n S)ᶜ := hzA
      have hopen : IsOpen (connectedComponentIn (dyadicPolyomino n S)ᶜ z) :=
        (esh_isClosed_dyadicPolyomino n S).isOpen_compl.connectedComponentIn
      obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hopen z (mem_connectedComponentIn hzU)
      obtain ⟨p, hzp⟩ := Commons.Topology.Plane.dyadicCell_grid_cover n z
      by_cases hzi : z ∈ interior (dSq n p)
      · exact ⟨p, hzp, esh_dSq_subset_compHull_of_mem_interior hz hzi⟩
      · have hcl : z ∈ closure (interior (dSq n p)) := esh_dSq_subset_closure_interior n p hzp
        obtain ⟨u, hu, hzu⟩ := Metric.mem_closure_iff.mp hcl ε hεpos
        have hucomp : u ∈ compHull (dyadicPolyomino n S) := by
          have hucomp' : u ∈ connectedComponentIn (dyadicPolyomino n S)ᶜ z :=
            hε (by rw [Metric.mem_ball, dist_comm]; exact hzu)
          rw [mem_compHull, ← connectedComponentIn_eq hucomp']
          exact mem_compHull.mp hz
        exact ⟨p, hzp, esh_dSq_subset_compHull_of_mem_interior hucomp hu⟩
  -- the index bound for the box: any cell inside the hull is inside `ball 0 (R+1)`
  set B : ℤ := ⌈(R + 1) * 2 ^ n⌉ with hB
  have hBle : (R + 1) * 2 ^ n ≤ (B : ℝ) := by
    rw [hB]
    exact Int.le_ceil _
  refine ⟨((Finset.Icc (-B) B) ×ˢ (Finset.Icc (-B) B)).filter
      (fun p => dSq n p ⊆ compHull (dyadicPolyomino n S)), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨p, hzp, hcell⟩ := hsat z hz
    have hpbox : p ∈ (Finset.Icc (-B) B) ×ˢ (Finset.Icc (-B) B) := by
      obtain ⟨h1, h2⟩ := esh_abs_le_of_dSq_subset_ball (n := n) (p := p) (R := R + 1)
        (subset_trans (subset_trans hcell hbdd) (Metric.closedBall_subset_ball (by linarith)))
      have habs1 : |(p.1 : ℝ)| ≤ (B : ℝ) := le_trans h1 hBle
      have habs2 : |(p.2 : ℝ)| ≤ (B : ℝ) := le_trans h2 hBle
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact_mod_cast (abs_le.mp habs1).1
      · exact_mod_cast (abs_le.mp habs1).2
      · exact_mod_cast (abs_le.mp habs2).1
      · exact_mod_cast (abs_le.mp habs2).2
    exact mem_dyadicPolyomino.mpr ⟨p, Finset.mem_filter.mpr ⟨hpbox, hcell⟩, hzp⟩
  · intro hz
    obtain ⟨p, hp, hzp⟩ := mem_dyadicPolyomino.mp hz
    exact (Finset.mem_filter.mp hp).2 hzp

end Work.PlanarSC
