import Mathlib
import Submission.Work.PlanarSC.HullDefs

/-!
# The complement of the hull of a compact plane set is preconnected

`compHull A` (`Submission/Work/PlanarSC/HullDefs.lean`) is the set of points whose connected
component in `Aᶜ` is bounded — for `A` closed this is `A` together with the bounded components of
`Aᶜ`, the classical filling of the holes of `A`.

The main point of this file is that for **compact** `A ⊆ ℂ` the set of points whose component in
`Aᶜ` is *unbounded* is exactly one component of `Aᶜ`, namely the unbounded one, and is therefore
preconnected.  Compactness is used only to know that a compact set has **at most one** unbounded
complementary component (`Commons.Topology.Jordan.compl_compact_unique_unbounded`), together with
the elementary fact that the exterior of a large ball is a preconnected unbounded subset of `Aᶜ`.
(Without compactness the statement is false: for `A` the imaginary axis the two half planes are
unbounded components of `Aᶜ`.)  The requested lemma is the special case `A = dyadicPolyomino n S`,
a finite union of closed bounded squares.
-/

open Set

namespace Work.PlanarSC

/-- **The complement of the hull of a compact plane set is preconnected.**  It is precisely the
unique unbounded connected component of `Aᶜ`. -/
theorem isPreconnected_compl_compHull_of_isCompact {A : Set ℂ} (hA : IsCompact A) :
    IsPreconnected (compHull A)ᶜ := by
  -- `A` lies in a closed ball, so the exterior of that ball is a preconnected subset of `Aᶜ`.
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hA.isBounded
  have hEsub : {z : ℂ | R < ‖z‖} ⊆ Aᶜ := by
    intro z hz
    simp only [mem_compl_iff]
    intro hzA
    have h1 : ‖z‖ ≤ R := by
      have := hR hzA
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    exact absurd h1 (not_le.mpr hz)
  have hEpre : IsPreconnected {z : ℂ | R < ‖z‖} := by
    simpa using Commons.Topology.Connected.isPreconnected_compl_closedBall (0 : ℂ) R
  -- the exterior is unbounded
  have hEunb : ¬ Bornology.IsBounded {z : ℂ | R < ‖z‖} := by
    intro hb
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
    have hmem : (((max r R + 1 : ℝ)) : ℂ) ∈ {z : ℂ | R < ‖z‖} := by
      change R < ‖(((max r R + 1 : ℝ)) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : R < max r R + 1 := by
        have := le_max_right r R
        linarith
      exact lt_of_lt_of_le h1 (le_abs_self _)
    have hnorm : ‖(((max r R + 1 : ℝ)) : ℂ)‖ ≤ r := by
      have := hr hmem
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
    have h1 : r < max r R + 1 := by
      have := le_max_left r R
      linarith
    have h2 : max r R + 1 ≤ |max r R + 1| := le_abs_self _
    linarith
  -- the component of a point of the exterior contains the whole exterior, hence is unbounded
  have hz0E : (((R + 1 : ℝ)) : ℂ) ∈ {z : ℂ | R < ‖z‖} := by
    change R < ‖(((R + 1 : ℝ)) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  have hz0A : (((R + 1 : ℝ)) : ℂ) ∈ Aᶜ := hEsub hz0E
  have hCsub : {z : ℂ | R < ‖z‖} ⊆ connectedComponentIn Aᶜ (((R + 1 : ℝ)) : ℂ) :=
    hEpre.subset_connectedComponentIn hz0E hEsub
  have hCunb : ¬ Bornology.IsBounded (connectedComponentIn Aᶜ (((R + 1 : ℝ)) : ℂ)) :=
    fun hb => hEunb (hb.subset hCsub)
  -- the hull complement is that component
  have hEq : (compHull A)ᶜ = connectedComponentIn Aᶜ (((R + 1 : ℝ)) : ℂ) := by
    ext z
    constructor
    · intro hz
      have hzu : ¬ Bornology.IsBounded (connectedComponentIn Aᶜ z) := notMem_compHull.mp hz
      have hzA : z ∈ Aᶜ := by
        by_contra h
        exact hzu (by rw [connectedComponentIn_eq_empty h]; exact Bornology.isBounded_empty)
      rw [← Commons.Topology.Jordan.compl_compact_unique_unbounded hA hzA hz0A hzu hCunb]
      exact mem_connectedComponentIn hzA
    · intro hz
      refine notMem_compHull.mpr ?_
      rw [← connectedComponentIn_eq hz]
      exact hCunb
  rw [hEq]
  exact isPreconnected_connectedComponentIn

/-- The complement of the hull of a dyadic polyomino is preconnected: it is the unique unbounded
component of the complement of the (compact) polyomino. -/
theorem isPreconnected_compl_compHull (n : ℕ) (S : Finset (ℤ × ℤ)) :
    IsPreconnected (compHull (dyadicPolyomino n S))ᶜ := by
  refine isPreconnected_compl_compHull_of_isCompact ?_
  rw [dyadicPolyomino]
  refine (S.finite_toSet).isCompact_biUnion (fun p _ => ?_)
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · -- each closed dyadic cell is closed
    have h : Commons.Topology.Plane.dSq n p =
        {z : ℂ | (p.1 : ℝ) / 2 ^ n ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n} ∩
        {z : ℂ | (p.2 : ℝ) / 2 ^ n ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n} := by
      ext z
      simp only [Commons.Topology.Plane.dSq, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [h]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · -- and bounded
    refine (Metric.isBounded_closedBall (x := (0 : ℂ))
      (r := 2 * |(p.1 : ℝ)| + 2 * |(p.2 : ℝ)| + 4)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz' : (p.1 : ℝ) / 2 ^ n ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n ∧
        (p.2 : ℝ) / 2 ^ n ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n := hz
    obtain ⟨h1a, h1b, h2a, h2b⟩ := hz'
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

end Work.PlanarSC
