import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

set_option linter.unusedVariables false

/-! Round 8, strand A (the kinetic clause audit).

FS's sliding boxes are `B(u) = acube ℓ ∩ ((ℓd)•u + acube (ℓd))`; the corpus's `dlBox ℓ d u` is
the same intersection (`Submission/Work/DLInfra.lean`).  The `farSet` is the set of sliding
positions `u` for which some coordinate of `w = (ℓd)•u` exceeds the outer half-side
`½ℓ(1+d)` — exactly the positions at which FS *discard* the box.  Content: there the two cubes
do not meet, so `B(u) = ∅`.  (Same triangle-inequality computation as the corpus's
`Work.SmallBoxSliding.farSet_chiSmallB_zero`.) -/
theorem dlBox_eq_empty_of_mem_farSet {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ Work.SmallBoxSliding.farSet ℓ d μ) :
    Submission.BoseGases.dlBox ℓ d u = ∅ := by
  -- `farSet` membership: the coordinate `j` of `w = (ℓd)•u` exceeds the outer half-side.
  obtain ⟨j, hj⟩ := hu
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  -- `x ∈ B(u)` forces `|x_j| ≤ ℓ/2` and `|x_j − w_j| ≤ (ℓd)/2`.
  rw [Submission.BoseGases.mem_dlBox_iff] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : |x.ofLp j| ≤ ℓ / 2 := by
    have := hx1 j
    rw [Set.mem_Icc] at this
    rw [abs_le]
    exact ⟨by linarith [this.1], this.2⟩
  have h2 : |(x - (ℓ * d) • u).ofLp j| ≤ (ℓ * d) / 2 := by
    have := hx2 j
    rw [Set.mem_Icc] at this
    rw [abs_le]
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  -- triangle inequality: `|w_j| ≤ |x_j| + |x_j − w_j|`.
  have htri : |((ℓ * d) • u).ofLp j| ≤ |x.ofLp j| + |(x - (ℓ * d) • u).ofLp j| := by
    have key : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
    have hw : ((ℓ * d) • u).ofLp j = x.ofLp j - (x - (ℓ * d) • u).ofLp j := by simp
    rw [hw]
    exact key _ _
  -- hence `|w_j| ≤ ℓ/2 + (ℓd)/2 = ½ℓ(1+d)`, contradicting `farSet`.
  nlinarith [hj, h1, h2, htri]

end Work.UBBInputs8.A
