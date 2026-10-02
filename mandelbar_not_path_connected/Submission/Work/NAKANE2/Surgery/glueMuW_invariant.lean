import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical

noncomputable section

namespace Work.NAKANE2.Surgery

/-! ## Auxiliary lemmas for the invariance of `glueMuW`

`glueMuW F W` is defined by pulling back `0` along the orbit of `F` until its first entrance
into the set `W`.  The two facts needed below are purely about the iterate bookkeeping:

* the first entrance time of `F z` into `W` is one less than that of `z`;
* if `z` never enters `W` then neither does `F z`.
-/

/-- Stepping the orbit forward shifts the hitting condition for `W` by one. -/
theorem hitW_shift {F : ℂ → ℂ} {W : Set ℂ} {z : ℂ} {n : ℕ} :
    (F^[n + 1]) z ∈ W ↔ (F^[n]) (F z) ∈ W := by
  rw [Function.iterate_succ_apply]

/-- If the first entrance time of `z` into `W` is `m + 1`, then the first entrance time of
`F z` into `W` is `m`. -/
theorem find_hitW_succ {F : ℂ → ℂ} {W : Set ℂ} {z : ℂ}
    (hz : ∃ n : ℕ, (F^[n]) z ∈ W) {m : ℕ} (hm : Nat.find hz = m + 1) :
    ∃ h : ∃ n : ℕ, (F^[n]) (F z) ∈ W, Nat.find h = m := by
  have hspec : (F^[m]) (F z) ∈ W := by
    have h := Nat.find_spec hz
    rw [hm, Function.iterate_succ_apply] at h
    exact h
  have hFz : ∃ n : ℕ, (F^[n]) (F z) ∈ W := ⟨m, hspec⟩
  have hfind : Nat.find hFz = m := by
    refine le_antisymm (Nat.find_min' hFz hspec) ?_
    have h1 : (F^[Nat.find hFz]) (F z) ∈ W := Nat.find_spec hFz
    have h2 : (F^[Nat.find hFz + 1]) z ∈ W := hitW_shift.mpr h1
    have h3 : Nat.find hz ≤ Nat.find hFz + 1 := Nat.find_min' hz h2
    omega
  exact ⟨hFz, hfind⟩

/-! ## The invariance of `glueMuW` -/

theorem glueMuW_invariant {F : ℂ → ℂ} {W : Set ℂ}
    (hWinv : ∀ z ∈ W, F z ∈ W)
    (hconf : ∀ z ∈ W, Work.MRMT.dz F z = 0)
    (hno : ∀ z, (∀ n, (F^[n]) z ∉ W) → Work.MRMT.dz F z = 0) :
    ∀ z : ℂ, Work.NAKANE2.glueMuW F W z
      = Work.MRMT.Found.pullRev (Work.NAKANE2.glueMuW F W) F z := by
  intro z
  by_cases hz : ∃ n : ℕ, (F^[n]) z ∈ W
  · rcases Nat.eq_zero_or_pos (Nat.find hz) with h0 | hpos
    · -- the first entrance time is `0`: `z` itself is already in `W`
      have hzW : z ∈ W := by
        have h := Nat.find_spec hz
        rw [h0, Function.iterate_zero] at h
        simpa using h
      have hFW : F z ∈ W := hWinv z hzW
      have hspec0 : (F^[0]) (F z) ∈ W := by
        rw [Function.iterate_zero]
        exact hFW
      have hFz : ∃ n : ℕ, (F^[n]) (F z) ∈ W := ⟨0, hspec0⟩
      have hfind0 : Nat.find hFz = 0 := Nat.le_zero.mp (Nat.find_min' hFz hspec0)
      have hglue_z : glueMuW F W z = 0 := by
        rw [glueMuW_of_hit hz, h0, Work.FBif.pullIter_zero]
      have hglue_Fz : glueMuW F W (F z) = 0 := by
        rw [glueMuW_of_hit hFz, hfind0, Work.FBif.pullIter_zero]
      have hdz : Work.MRMT.dz F z = 0 := hconf z hzW
      rw [hglue_z]
      unfold Work.MRMT.Found.pullRev
      rw [hglue_Fz, hdz]
      simp
    · -- the first entrance time is `m + 1`
      obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.find hz = m + 1 := ⟨Nat.find hz - 1, by omega⟩
      obtain ⟨hFz, hfind⟩ := find_hitW_succ hz hm
      have hglue_z : glueMuW F W z
          = Work.MRMT.Found.pullRev (Work.FBif.pullIter F m) F z := by
        rw [glueMuW_of_hit hz, hm, Work.FBif.pullIter_succ]
      have hglue_Fz : glueMuW F W (F z) = Work.FBif.pullIter F m (F z) := by
        rw [glueMuW_of_hit hFz, hfind]
      rw [hglue_z]
      exact Work.FBif.pullRev_congr hglue_Fz.symm
  · -- `z` never enters `W`
    have hznot : ∀ n : ℕ, (F^[n]) z ∉ W := fun n hn => hz ⟨n, hn⟩
    have hFznot : ∀ n : ℕ, (F^[n]) (F z) ∉ W :=
      fun n hn => hz ⟨n + 1, hitW_shift.mpr hn⟩
    have hglue_z : glueMuW F W z = 0 := glueMuW_of_not_hit hz
    have hglue_Fz : glueMuW F W (F z) = 0 :=
      glueMuW_of_not_hit (fun hcon => hcon.elim hFznot)
    have hdz : Work.MRMT.dz F z = 0 := hno z hznot
    rw [hglue_z]
    unfold Work.MRMT.Found.pullRev
    rw [hglue_Fz, hdz]
    simp

end Work.NAKANE2.Surgery

end
