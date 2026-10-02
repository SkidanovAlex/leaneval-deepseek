import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.notInArc_midNear
import Submission.Work.ELTop.seed_mem_polyRegion

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

/-!
# `Work.ELTop.nearArc_angle_data`

The reference angle `midNear ps` of an admissible ray polygon `ps` has a genuine *neighbourhood*
(on the line `ℝ`, not merely modulo `ℤ`) consisting of angles which avoid every arc of the
polygon: no angle `θ` near `midNear ps` lies in any open arc `(P.a, P.b)`, `P ∈ ps`, nor is it
congruent modulo `ℤ` to any of the `2m` angles of the polygon.

The content is purely angular.  Writing `InClosedArc θ a b` for the closed cyclic arc from `a`
to `b`, the set of angles avoiding the closed arc `[a, b]` is

`{θ | ¬ InClosedArc θ a b} = ⋃ k : ℤ, (a + k + arcLen a b, a + k + 1)`,

a union of open intervals (this is `notInClosedArc_eq_iUnion`), hence open.  Moreover avoiding
the *closed* arc is exactly the conjunction of avoiding the open arc and avoiding both
endpoints modulo `ℤ` (`not_InClosedArc_iff_not_InArc`).  Since the finitely many sets
`{θ | ¬ InClosedArc θ P.a P.b}`, `P ∈ ps`, are open, so is their intersection, and
`Work.ELTop.notInArc_midNear` together with `Work.ELTop.midNear_ne_angle_add_int` show that
`midNear ps` belongs to it.  A metric ball around `midNear ps` inside that open set is the
required neighbourhood.
-/

/-! ## The complement of a closed cyclic arc is a union of open intervals -/

/-- Avoiding the closed cyclic arc `[a, b]` means lying in one of the open intervals
`(a + k + arcLen a b, a + k + 1)`, `k ∈ ℤ`. -/
theorem notInClosedArc_eq_iUnion (a b : ℝ) :
    {θ : ℝ | ¬ Work.EL.InClosedArc θ a b}
      = ⋃ k : ℤ, Set.Ioo (a + k + Work.EL.arcLen a b) (a + k + 1) := by
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ioo]
  constructor
  · intro h
    have hf : Work.EL.arcLen a b < Int.fract (θ - a) := by
      by_contra hle
      push_neg at hle
      exact h ⟨Int.fract_nonneg (θ - a), hle⟩
    refine ⟨⌊θ - a⌋, ?_, ?_⟩
    · have hff := Int.floor_add_fract (θ - a); linarith
    · have hff := Int.floor_add_fract (θ - a)
      have hlt := Int.fract_lt_one (θ - a); linarith
  · rintro ⟨k, h1, h2⟩
    have hL0 : 0 ≤ Work.EL.arcLen a b := Work.EL.arcLen_nonneg a b
    have hy1 : 0 ≤ θ - a - k := by linarith
    have hy2 : θ - a - k < 1 := by linarith
    have hfrac : Int.fract (θ - a) = θ - a - k := by
      rw [← Int.fract_sub_intCast (θ - a) k]
      exact Int.fract_eq_self.mpr ⟨hy1, hy2⟩
    intro hIn
    have hle : Int.fract (θ - a) ≤ Work.EL.arcLen a b := hIn.2
    rw [hfrac] at hle
    linarith

/-- The set of angles avoiding a closed cyclic arc is open. -/
theorem isOpen_setOf_not_InClosedArc (a b : ℝ) :
    IsOpen {θ : ℝ | ¬ Work.EL.InClosedArc θ a b} := by
  rw [notInClosedArc_eq_iUnion a b]
  exact isOpen_iUnion (fun k => isOpen_Ioo)

/-! ## Avoiding the closed arc versus avoiding the open arc and the endpoints -/

/-- An angle avoids the closed cyclic arc `[a, b]` if and only if it avoids the open arc
`(a, b)` and is congruent modulo `ℤ` to neither endpoint. -/
theorem not_InClosedArc_iff_not_InArc (a b θ : ℝ) :
    ¬ Work.EL.InClosedArc θ a b ↔
      (¬ Work.EL.InArc θ a b ∧ (∀ k : ℤ, θ ≠ a + k) ∧ (∀ k : ℤ, θ ≠ b + k)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro hIn
      exact h ⟨le_of_lt hIn.1, le_of_lt hIn.2⟩
    · intro k hk
      apply h
      have h1 : θ - a = (k : ℝ) := by linarith
      unfold Work.EL.InClosedArc
      rw [h1, Int.fract_intCast]
      exact ⟨le_refl 0, Work.EL.arcLen_nonneg a b⟩
    · intro k hk
      apply h
      have h1 : θ - a = (b - a) - ((-k : ℤ) : ℝ) := by push_cast; linarith
      unfold Work.EL.InClosedArc
      rw [h1, Int.fract_sub_intCast]
      exact ⟨Int.fract_nonneg (b - a), le_refl _⟩
  · rintro ⟨hnArc, hna, hnb⟩ ⟨hf0, hfL⟩
    rcases lt_or_eq_of_le hf0 with hfpos | hfzero
    · rcases lt_or_eq_of_le hfL with hflt | hfeq
      · exact hnArc ⟨hfpos, hflt⟩
      · obtain ⟨z, hz⟩ :=
          (Int.fract_eq_fract (a := θ - a) (b := b - a)).mp hfeq
        exact hnb z (by linarith)
    · obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp hfzero.symm
      exact hna z (by linarith)

/-! ## Finitely many open conditions -/

/-- The set of angles avoiding every closed cyclic arc of the polygon is open: it is the finite
intersection of the open sets `{θ | ¬ InClosedArc θ P.a P.b}`, `P ∈ ps`. -/
theorem isOpen_setOf_forall_not_InClosedArc {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) :
    IsOpen {θ : ℝ | ∀ P ∈ ps, ¬ Work.EL.InClosedArc θ P.a P.b} := by
  induction ps with
  | nil =>
    convert isOpen_univ using 1
    ext θ; simp
  | cons P tl ih =>
    have hset : {θ : ℝ | ∀ Q ∈ P :: tl, ¬ Work.EL.InClosedArc θ Q.a Q.b}
        = {θ : ℝ | ¬ Work.EL.InClosedArc θ P.a P.b}
          ∩ {θ : ℝ | ∀ Q ∈ tl, ¬ Work.EL.InClosedArc θ Q.a Q.b} := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.mem_cons]
      constructor
      · intro h
        exact ⟨h P (Or.inl rfl), fun Q hQ => h Q (Or.inr hQ)⟩
      · rintro ⟨h1, h2⟩ Q (rfl | hQ)
        · exact h1
        · exact h2 Q hQ
    rw [hset]
    exact (isOpen_setOf_not_InClosedArc P.a P.b).inter ih

/-! ## The main statement -/

theorem nearArc_angle_data {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) :
    ∃ δ > 0, ∀ θ : ℝ, |θ - Work.EL.midNear ps| < δ →
      ((∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b) ∧
        ∀ P ∈ ps, (∀ k : ℤ, θ ≠ P.a + k) ∧ (∀ k : ℤ, θ ≠ P.b + k)) := by
  have hpoint : ∀ P ∈ ps, ¬ Work.EL.InClosedArc (Work.EL.midNear ps) P.a P.b := by
    intro P hP
    rw [not_InClosedArc_iff_not_InArc]
    refine ⟨notInArc_midNear ps hA P hP, ?_, ?_⟩
    · intro k
      exact midNear_ne_angle_add_int ps hA
        (List.mem_flatMap.mpr ⟨P, hP, by simp⟩) k
    · intro k
      exact midNear_ne_angle_add_int ps hA
        (List.mem_flatMap.mpr ⟨P, hP, by simp⟩) k
  obtain ⟨ε, hε, hball⟩ :=
    (Metric.isOpen_iff.mp (isOpen_setOf_forall_not_InClosedArc ps)) (Work.EL.midNear ps) hpoint
  refine ⟨ε, hε, fun θ hθ => ?_⟩
  have hθmem : θ ∈ Metric.ball (Work.EL.midNear ps) ε := by
    rw [Metric.mem_ball, Real.dist_eq]; exact hθ
  have hb : ∀ P ∈ ps, ¬ Work.EL.InClosedArc θ P.a P.b := hball hθmem
  exact ⟨fun P hP => ((not_InClosedArc_iff_not_InArc P.a P.b θ).mp (hb P hP)).1,
         fun P hP => ((not_InClosedArc_iff_not_InArc P.a P.b θ).mp (hb P hP)).2⟩

end Work.ELTop
