import Mathlib
import Submission.Work.PiS.Interfaces

set_option synthInstance.maxHeartbeats 400000

/-!
# pi_sphere_infinite_iff from the sphere-level areas (lead's glue; no sorry)

`Work.PiS.pi_sphere_of_areas` is the challenge statement from the seven sphere-level area `Prop`s of
`Interfaces.lean`. The engine areas feed `SphereFG`; the rational areas give `SphereTorsion` and
`HopfInfinite`.
-/

set_option autoImplicit false

namespace Work.PiS

theorem not_infinite_of_subsingleton {α : Type} (h : Subsingleton α) : ¬ Infinite α := by
  intro hi
  haveI := h
  exact not_finite α

theorem pi_sphere_of_areas (hB : BasepointHomog) (hL : LowDegree) (hC : CircleFacts)
    (hD : DegreeInfinite) (hH : HopfInfinite) (hF : SphereFG) (hT : SphereTorsion)
    (k n : ℕ) (hn : 1 ≤ n) (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Infinite (HomotopyGroup.Pi k (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) ↔
      k = n ∨ (Even n ∧ k + 1 = 2 * n) := by
  obtain ⟨e⟩ := hB n k x (pt n)
  change Infinite (HomotopyGroup.Pi k (Sph n) x) ↔ _
  rw [e.infinite_iff]
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- n = 1
    obtain rfl : n = 1 := by omega
    have hodd : ¬ Even 1 := by decide
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simp only [hodd, false_and, or_false]
        exact ⟨fun h => absurd h (not_infinite_of_subsingleton (hL.1 1 le_rfl)), fun h => by omega⟩
      · simp only [true_or, iff_true]
        exact hC.1
    · simp only [hodd, false_and, or_false]
      exact ⟨fun h => absurd h (not_infinite_of_subsingleton (hC.2 k hk)), fun h => by omega⟩
  · rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · refine ⟨fun h => absurd h (not_infinite_of_subsingleton (hL.1 n (by omega))), ?_⟩
        rintro (h | ⟨_, h⟩) <;> omega
      · refine ⟨fun h => absurd h (not_infinite_of_subsingleton (hL.2 n h2)), ?_⟩
        rintro (h | ⟨_, h⟩) <;> omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      by_cases hkn : j + 2 = n
      · subst hkn
        simp only [true_or, iff_true]
        exact hD (j + 2) h2
      by_cases hev : Even n ∧ j + 2 + 1 = 2 * n
      · simp only [hev, and_self, or_true, iff_true]
        exact hH n h2 hev.1 (j + 2) hev.2
      · simp only [hkn, hev, or_self, iff_false]
        intro hinf
        haveI : Group.FG (HomotopyGroup.Pi (j + 2) (Sph n) (pt n)) := hF n h2 j
        have htor : IsMulTorsion (HomotopyGroup.Pi (j + 2) (Sph n) (pt n)) := by
          intro a
          obtain ⟨m, hm, ha⟩ := hT n h2 j hkn (by simpa [show j + 3 = j + 2 + 1 by omega] using hev) a
          exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ha⟩
        haveI := CommGroup.finite_of_fg_isMulTorsion (HomotopyGroup.Pi (j + 2) (Sph n) (pt n)) htor
        exact not_finite (HomotopyGroup.Pi (j + 2) (Sph n) (pt n))

end Work.PiS
