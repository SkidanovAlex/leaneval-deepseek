import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Defs
import Submission.Work.Peel.exists_gap_periodLattice_image

namespace Work.BoxShrink.PinchOff

open Set Metric

/-- The lattice contains `0`. -/
theorem periodLattice_zero : (0 : ℂ) ∈ periodLattice := ⟨(0, 0), periodPt_zero⟩

/-- The lattice is closed under subtraction. -/
theorem periodLattice_sub {ν μ : ℂ} (hν : ν ∈ periodLattice) (hμ : μ ∈ periodLattice) :
    ν - μ ∈ periodLattice := by
  rw [mem_periodLattice] at hν hμ ⊢
  obtain ⟨a, b, rfl⟩ := hν
  obtain ⟨c, d, rfl⟩ := hμ
  refine ⟨a - c, b - d, ?_⟩
  apply Complex.ext <;> simp [periodPt] <;> ring

/-- **A uniform positive gap between the lattice translates of a compact set.**

Let `V ⊆ ℂ` be bounded, and suppose that the lattice translates of `closure V` are pairwise
disjoint.  Then they are *uniformly* separated: there is `ρ > 0` such that points of distinct
translates are at distance `≥ 2ρ`.

(Only finitely many lattice vectors can bring `closure V` near itself: `closure V` is bounded, and
the lattice `2π(ℤ + iℤ)` is discrete, so all but finitely many translates are far away.  The
reviewers point out that this is a short reduction to the already-proved
`Work.Peel.exists_gap_of_isCompact` applied to `K = closure V`.) -/
theorem exists_uniform_gap {V : Set ℂ} (hVb : Bornology.IsBounded V)
    (hdisj : ∀ ν μ : ℂ, ν ∈ Work.BoxShrink.PinchOff.periodLattice →
      μ ∈ Work.BoxShrink.PinchOff.periodLattice → ν ≠ μ →
      Disjoint {z : ℂ | z - ν ∈ closure V} {z : ℂ | z - μ ∈ closure V}) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ν μ : ℂ, ν ∈ Work.BoxShrink.PinchOff.periodLattice →
      μ ∈ Work.BoxShrink.PinchOff.periodLattice → ν ≠ μ →
      ∀ x y : ℂ, x - ν ∈ closure V → y - μ ∈ closure V → 2 * ρ ≤ dist x y := by
  have hKc : IsCompact (closure V) := hVb.isCompact_closure
  -- no two points of `closure V` differ by a nonzero lattice vector
  have hsep : ∀ u ∈ closure V, ∀ v ∈ closure V, ∀ ν ∈ periodLattice, u - v = ν → ν = 0 := by
    intro u hu v hv ν hν huv
    by_contra hν0
    have hneg : -ν ∈ periodLattice := Work.Peel.periodLattice_neg hν
    have h0 : (0 : ℂ) ∈ periodLattice := periodLattice_zero
    have hne : (0 : ℂ) ≠ -ν := (neg_ne_zero.mpr hν0).symm
    have hdis := hdisj 0 (-ν) h0 hneg hne
    have hv0 : v ∈ {z : ℂ | z - (0 : ℂ) ∈ closure V} := by simpa using hv
    have hv1 : v ∈ {z : ℂ | z - (-ν) ∈ closure V} := by
      have hvu : v - (-ν) = u := by
        rw [sub_neg_eq_add, ← huv]
        ring
      show v - (-ν) ∈ closure V
      rw [hvu]
      exact hu
    exact (Set.disjoint_left.mp hdis hv0) hv1
  obtain ⟨η, hηpos, hη⟩ := Work.Peel.exists_gap_of_isCompact hKc hsep
  refine ⟨η / 2, by linarith, ?_⟩
  intro ν μ hν hμ hne x y hx hy
  have hνμ : ν - μ ∈ periodLattice := periodLattice_sub hν hμ
  have hνμ0 : ν - μ ≠ 0 := sub_ne_zero.mpr hne
  have h := hη (ν - μ) hνμ hνμ0 (x - ν) hx (y - μ) hy
  have hd : dist ((x - ν) + (ν - μ)) (y - μ) = dist x y := by
    have hxμ : (x - ν) + (ν - μ) = x - μ := by ring
    rw [hxμ, dist_sub_right]
  linarith

end Work.BoxShrink.PinchOff
