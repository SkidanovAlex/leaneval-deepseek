/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — the finite certificate of the portrait argument

`NOTES_LEAD_mandelbar_seed.md` §4.2, item `C`: for every `j ∈ [0,1023)` outside the four angles
`{371, 372, 403, 404}`, the four angles `T^i{α₁, α₂, j/1023, g(j/1023)}` (`i < 5`) carry a
**linked** pair of two-subsets at two distinct levels.  Since all these angles land at the
points of the period-`5` cycle of `z₁`, and since rays landing at distinct points are unlinked
(the unlinked lemma `U`), such a `j` is impossible: this is the combinatorial half of the
rotation-number-zero argument `RN0`.

The certificate is a Boolean computation on `ℕ` (`List.range 1023`), closed by the kernel
`decide`; the bridge to the real angles `j/1023` is `Angle.lean`.

This reproduces block 1 of `Submission/Work/lead_seed/seed_portrait_search.py`.
-/
import Submission.Work.SeedSimple2.Angle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function
open scoped Topology

noncomputable section

namespace Work.SeedSimple2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The four angles at level `i` -/

/-- The four angles `T^i {α₁, α₂, j, g j}` of the portrait problem at level `i`, with
multiplicities. -/
def levelAngles (j i : ℕ) : List ℕ :=
  [(TN^[i]) α₁N, (TN^[i]) α₂N, (TN^[i]) j, (TN^[i]) (gN j)]

/-- The four angles of the portrait problem at level `i`, as a set (no multiplicities). -/
def levelSet (j i : ℕ) : List ℕ := (levelAngles j i).eraseDups

theorem mem_levelSet_of_mem_levelAngles {j i a : ℕ} (h : a ∈ levelAngles j i) :
    a ∈ levelSet j i := List.mem_eraseDups.mpr h

/-- **The combinatorial conclusion of the certificate**: at two distinct levels `i < k` there are
two-element subsets of the two level sets that are *linked* (the Boolean `unlinkedB` fails). -/
def linkedLevels (j i k : ℕ) : Prop :=
  ∃ a ∈ levelSet j i, ∃ b ∈ levelSet j i, a ≠ b ∧
    ∃ c ∈ levelSet j k, ∃ d ∈ levelSet j k, c ≠ d ∧ unlinkedB a b c d = false

/-- The Boolean checker of `linkedLevels`. -/
def linkedLevelsB (j i k : ℕ) : Bool :=
  (levelSet j i).any fun a => (levelSet j i).any fun b =>
    decide (a ≠ b) &&
      (levelSet j k).any fun c => (levelSet j k).any fun d =>
        decide (c ≠ d) && !(unlinkedB a b c d)

theorem linkedLevelsB_eq_true (j i k : ℕ) : (linkedLevelsB j i k = true) ↔ linkedLevels j i k := by
  have hany : ∀ (l : List ℕ) (p : ℕ → Bool), (l.any p = true) ↔ ∃ a ∈ l, p a = true :=
    fun l p => List.any_eq_true
  simp only [linkedLevelsB, linkedLevels]
  rw [hany]
  constructor
  · rintro ⟨a, ha, h2⟩
    rw [hany] at h2
    obtain ⟨b, hb, h2⟩ := h2
    rw [Bool.and_eq_true] at h2
    obtain ⟨hne, h2⟩ := h2
    rw [hany] at h2
    obtain ⟨c, hc, h2⟩ := h2
    rw [hany] at h2
    obtain ⟨d, hd, h2⟩ := h2
    rw [Bool.and_eq_true] at h2
    obtain ⟨hne2, h2⟩ := h2
    exact ⟨a, ha, b, hb, by simpa using hne, c, hc, d, hd, by simpa using hne2,
      by simpa using h2⟩
  · rintro ⟨a, ha, b, hb, hne, c, hc, d, hd, hne2, h5⟩
    refine ⟨a, ha, ?_⟩
    rw [hany]
    refine ⟨b, hb, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨by simpa using hne, ?_⟩
    rw [hany]
    refine ⟨c, hc, ?_⟩
    rw [hany]
    refine ⟨d, hd, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨by simpa using hne2, by simpa using h5⟩

/-! ## The certificate -/

/-- The Boolean certificate over `j < 1023`. -/
def certB (j : ℕ) : Bool :=
  (List.range 5).any fun i => (List.range 5).any fun k =>
    decide (i < k) && linkedLevelsB j i k

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The certificate**: every `j ∈ [0,1023)` outside the four survivor angles carries a linked
pair of two-subsets at two distinct levels.  Closed by the kernel `decide` on `ℕ` (no
`native_decide`). -/
theorem certificate :
    (List.range 1023).all (fun j => decide (j ∈ survivors) || certB j) = true := by
  decide

theorem certB_of_not_survivor (j : ℕ) (hj : j < 1023) (hjs : j ∉ survivors) :
    certB j = true := by
  have h := (List.all_eq_true.mp certificate) j (List.mem_range.mpr hj)
  simpa [hjs] using h

/-- The extraction of the linked pair from `linkedLevelsB`. -/
theorem linkedLevels_of_linkedLevelsB {j i k : ℕ} (h : linkedLevelsB j i k = true) :
    linkedLevels j i k := (linkedLevelsB_eq_true j i k).mp h

/-- The extraction of the two levels from `certB`. -/
theorem certB_imp (j : ℕ) (h : certB j = true) :
    ∃ i k : ℕ, i < 5 ∧ k < 5 ∧ i < k ∧ linkedLevelsB j i k = true := by
  rw [certB] at h
  rw [List.any_eq_true] at h
  obtain ⟨i, hi, h'⟩ := h
  rw [List.any_eq_true] at h'
  obtain ⟨k, hk, h''⟩ := h'
  rw [Bool.and_eq_true] at h''
  exact ⟨i, k, List.mem_range.mp hi, List.mem_range.mp hk, by simpa using h''.1, h''.2⟩

end Work.SeedSimple2

end
