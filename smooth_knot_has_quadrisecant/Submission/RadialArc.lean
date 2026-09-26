import Mathlib
import ChallengeDeps
import Submission.BandArcCover
import Submission.TrisecantLocus

open LeanEval.KnotTheory.Quadrisecant
open AddSubgroup
open scoped Real Topology unitInterval

/-!
# The radial (cone) band arc — Kuperberg's trivial case

**Context.**  `BandArcCover.lean` shows that a *non-separating* band arc which
avoids the trisecant set `O` spans a disk whose boundary is the whole knot.
This module produces the basic instance: the **radial arc** through a knot
point `p = K(u)` whose chords are the segments `[p, q]`, `q ∈ K`.

* If no chord from `p` carries a strict middle point
  (`NoTrisecantThrough r u`), then the radial arc avoids `O` — the chords from
  `p` never meet `K` in a third point — and the chord-family disk is the
  **cone over the knot from `p`**, a disk whose boundary is the knot and whose
  interior avoids the knot.  This is Kuperberg's §1 illustration ("Suppose
  that there exists a point `p` in `K` such that no points `q` and `r` in `K`
  are collinear with `p`.  Then the union of the chords `p̄q̄` for all `q` in
  `K` is evidently a smooth embedded disk with boundary `K`, which renders `K`
  trivial.").
* The radial arc is **non-separating**: the fixed branch `a ≡ u` lifts
  constantly to `u₀` and the moving branch `s ↦ u₀ + s·period` gains exactly
  one period, so the two branches together sweep the whole knot.

Consequently `radialArc_spanningDisk` gives, for any knot point `u` carrying
no trisecant, the two knot paths bounding an interior-free disk that together
cover the knot — the input consumed by the Layer-B pin
`SpanningDisk_implies_IsUnknotted`.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-- **No trisecant through a knot point.**  `u` is a parameter whose knot
point `K(u)` lies on no trisecant of `r`: no chord with an endpoint at `u`
carries a knot point strictly inside it. -/
def NoTrisecantThrough (r : ℝ → Space) (u : AddCircle period) : Prop :=
  ∀ b z : AddCircle period, ¬ IsMiddleOnChord r u b z

/-- A fixed real representative of a parameter (chosen noncomputably). -/
noncomputable def radialLift (u : AddCircle period) : ℝ :=
  Classical.choose (QuotientAddGroup.mk_surjective (s := zmultiples period) u)

lemma radialLift_spec (u : AddCircle period) : (radialLift u : AddCircle period) = u :=
  Classical.choose_spec (QuotientAddGroup.mk_surjective (s := zmultiples period) u)

/-- The first branch of the radial arc: the constant parameter `u`. -/
def radialArcA (u : AddCircle period) : I → AddCircle period := fun _ => u

/-- The second branch of the radial arc: the parameter `u₀ + s·period`
(sweeping once around the circle as `s` runs over the interval). -/
def radialArcB (u : AddCircle period) : I → AddCircle period :=
  fun s => ((radialLift u + (s : ℝ) * period : ℝ) : AddCircle period)

lemma continuous_radialArcA (u : AddCircle period) : Continuous (radialArcA u) :=
  continuous_const

lemma continuous_radialArcB (u : AddCircle period) : Continuous (radialArcB u) := by
  unfold radialArcB
  exact continuous_quot_mk.comp
    (continuous_const.add (continuous_subtype_val.mul continuous_const))

/-- **The radial band arc at a knot point.**  Both branches collapse at the
two ends of the interval (to `u`), and the moving branch sweeps the circle
once; the two branches are distinct on the open interval. -/
noncomputable def radialArcData (u : AddCircle period) : BandArcData where
  a := radialArcA u
  b := radialArcB u
  cont_a := continuous_radialArcA u
  cont_b := continuous_radialArcB u
  collapse_left := by
    show radialArcA u 0 = radialArcB u 0
    simp only [radialArcA, radialArcB]
    norm_num
    exact (radialLift_spec u).symm
  collapse_right := by
    show radialArcA u 1 = radialArcB u 1
    simp only [radialArcA, radialArcB]
    have h1p : ((1 : I) : ℝ) * period = period := by norm_num
    rw [h1p, AddCircle.coe_add_period]
    exact (radialLift_spec u).symm
  offdiag := by
    intro s hs0 hs1 hEq
    simp only [radialArcA, radialArcB] at hEq
    have hsge : (0 : ℝ) ≤ s := s.2.1
    have hsle : (s : ℝ) ≤ 1 := s.2.2
    have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hsle hs1
    have hmem₁ : radialLift u + (s : ℝ) * period ∈ Set.Ico (radialLift u) (radialLift u + period) :=
      ⟨by nlinarith [period_pos, hsge], by nlinarith [period_pos, hslt]⟩
    have hmem₂ : radialLift u ∈ Set.Ico (radialLift u) (radialLift u + period) :=
      ⟨le_rfl, by nlinarith [period_pos]⟩
    have hEq' : ((radialLift u + (s : ℝ) * period : ℝ) : AddCircle period) =
        (radialLift u : AddCircle period) :=
      hEq.symm.trans (radialLift_spec u).symm
    have hsp : radialLift u + (s : ℝ) * period = radialLift u :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := period) (a := radialLift u) hmem₁ hmem₂).mp hEq'
    have hz : (s : ℝ) * period = 0 := by linarith
    have hs : (s : ℝ) = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd h period_ne_zero
    exact hs0 hs

/-- **The radial arc is non-separating.**  The fixed branch lifts to the
constant `u₀` and the moving branch to `s ↦ u₀ + s·period`, which gains
exactly one knot period over the traversal. -/
theorem radialArcData_nonSeparating (u : AddCircle period) :
    BandArcNonSeparating (radialArcData u) := by
  refine ⟨fun _ => radialLift u, fun s => radialLift u + (s : ℝ) * period,
    continuous_const, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.add (continuous_subtype_val.mul continuous_const)
  · intro s
    exact radialLift_spec u
  · intro s
    rfl
  · norm_num
  · show radialLift u + ((1 : I) : ℝ) * period = radialLift u + period
    norm_num

/-- **The radial arc avoids `O` when `u` carries no trisecant.**  For an
interior parameter the chord is `{u, u₀ + s·period}`; it lies in `O` exactly
when it carries a strict middle, i.e. exactly when some chord from `K(u)` is a
trisecant. -/
theorem radialArcData_avoids {r : ℝ → Space} {u : AddCircle period}
    (hu : NoTrisecantThrough r u) :
    ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨((radialArcData u).a s, (radialArcData u).b s),
        (radialArcData u).offdiag s hs0 hs1⟩ ∉ trisecantSet r := by
  intro s hs0 hs1 hmem
  have hiff := (HasMiddleOnClass_iff r
    ⟨((radialArcData u).a s, (radialArcData u).b s), (radialArcData u).offdiag s hs0 hs1⟩).mp hmem
  rcases hiff with ⟨m, hm⟩
  exact hu _ m (by simpa [radialArcData, radialArcA] using hm)

/-- **Kuperberg's trivial case: a knot point carrying no trisecant spans a
disk.**  If some knot point `K(u)` lies on no trisecant of `r`, then the two
branches of the radial arc at `u` are two knot paths based at `K(u)` which
bound a disk whose interior avoids the knot and which together cover the
whole knot — the spanning disk consumed by the Layer-B pin. -/
theorem radialArc_spanningDisk {r : ℝ → Space} (h : IsSmoothKnot r)
    (u : AddCircle period) (hu : NoTrisecantThrough r u) :
    ∃ γ δ : Path (knotMap r u) (knotMap r u),
      PathsBoundDiskInteriorFree (Set.range (knotMap r)) γ δ ∧
        Set.range γ ∪ Set.range δ = Set.range (knotMap r) := by
  have hspan := bandArc_spanningDisk h (radialArcData u)
    (radialArcData_nonSeparating u) (radialArcData_avoids (r := r) hu)
  exact ⟨bandArcPathA h (radialArcData u), bandArcPathB h (radialArcData u), hspan⟩

/-- **Kuperberg's §1 theorem modulo the Layer-B pin.**  Granting the pin
`SpanningDisk_implies_IsUnknotted` (a knot whose complementary arcs bound an
interior-free disk is unknotted), a smooth knot with a trisecant-free point
is unknotted: the radial arc at that point spans the disk.  This is exactly
the trivial case of the contrapositive of `smooth_knot_has_quadrisecant`. -/
theorem isUnknotted_of_noTrisecant {r : ℝ → Space}
    (hpin : SpanningDisk_implies_IsUnknotted) (h : IsSmoothKnot r)
    (u : AddCircle period) (hu : NoTrisecantThrough r u) : IsUnknotted r := by
  obtain ⟨γ, δ, hdisk, hcov⟩ := radialArc_spanningDisk h u hu
  exact hpin r h ⟨u, u, γ, δ, hdisk, hcov⟩

end LeanEval.KnotTheory.Quadrisecant
