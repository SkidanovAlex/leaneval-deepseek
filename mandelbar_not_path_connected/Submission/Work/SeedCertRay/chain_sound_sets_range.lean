import Mathlib
import Submission.Work.SeedCertRay.chain_sound_sets

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open Set
open LeanEval.ComplexAnalysis (Tantibar)

/-- **Soundness of the ray chain, up to a level bound.**  This is
`Work.SeedCertRay.chain_sound_sets` with the preimage condition `hD1` and the radial separation
condition `hD2` assumed only for indices `k ≤ M`; the conclusion then holds for all levels
`k ≤ M + 1`.  The point is that the induction step from level `k` to level `k + 1` uses `hD1`
and `hD2` at index `k` only, so the argument is unchanged and the bound is respected. -/
theorem chain_sound_sets_range {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℕ → ℝ) (hθ : ∀ j, θ (j + 1) = Work.EL.T (θ j)) (ρ : ℕ → ℝ) (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) (C : ℕ → ℕ → Set ℂ) (M : ℕ) (hD0 : ∀ j, Work.SeedCertRay.seg hN (θ j) (ρ 1) (ρ 0) ⊆ C 0 j) (hD1 : ∀ k, k ≤ M → ∀ j, ∀ u : ℂ, LeanEval.ComplexAnalysis.Tantibar c u ∈ C k (j + 1) → u ∈ C (k + 1) j ∨ -u ∈ C (k + 1) j) (hD2 : ∀ k, k ≤ M → ∀ j, IsClosed (C (k + 1) j) ∧ Disjoint (C (k + 1) j) (-C (k + 1) j) ∧ Disjoint (C k j) (-C (k + 1) j)) : ∀ k, k ≤ M + 1 → ∀ j, Work.SeedCertRay.seg hN (θ j) (ρ (k + 1)) (ρ k) ⊆ C k j := by
  intro k
  induction k with
  | zero => intro _ j; exact hD0 j
  | succ k ih =>
    intro hkM j
    -- The step from level `k` to level `k + 1` is available because `k ≤ M`.
    have hk : k ≤ M := Nat.succ_le_succ_iff.mp hkM
    have hkM1 : k ≤ M + 1 := le_trans hk (Nat.le_succ M)
    have hD2k := hD2 k hk
    -- The level sequence is decreasing: `ρ (k+2) ≤ ρ (k+1) ≤ ρ k`.
    have hk1 : ρ (k + 2) ≤ ρ (k + 1) := by
      have h1 := (hρ (k + 1)).1
      have h2 := (hρ (k + 1)).2
      nlinarith [sq_nonneg (ρ (k + 2) - 1)]
    have hk0 : ρ (k + 1) ≤ ρ k := by
      have h1 := (hρ k).1
      have h2 := (hρ k).2
      nlinarith [sq_nonneg (ρ (k + 1) - 1)]
    -- The piece `seg (θ j) (ρ (k+2)) (ρ (k+1))` is connected, and its `T_c`-image is the next
    -- piece `seg (θ (j+1)) (ρ (k+1)) (ρ k) ⊆ C k (j+1)`.  Splitting at the two closed disjoint
    -- sets `C (k+1) j` and `-C (k+1) j`, the witness point `rayPt (θ j) (ρ (k+1)) ∈ C k j`
    -- (from the induction hypothesis) forces the piece into `C (k+1) j`.
    refine subset_of_preconnected_of_sep
      (s := seg hN (θ j) (ρ (k + 2)) (ρ (k + 1)))
      (u := C (k + 1) j) (v := -C (k + 1) j) (w := C k j)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact isPreconnected_seg hN (θ j) (ρ (k + 2)) (ρ (k + 1)) (hρ (k + 1)).1
    · exact (hD2k j).1
    · exact (hD2k j).1.neg
    · exact (hD2k j).2.1
    · rintro z ⟨t, ht, rfl⟩
      have ht1 : 1 < t := lt_of_lt_of_le (hρ (k + 1)).1 ht.1
      have htpos : 0 < t := by linarith
      have hstep : Work.EL.rayPt hN (θ (j + 1)) (t ^ 2)
          = Tantibar c (Work.EL.rayPt hN (θ j) t) := by
        rw [hθ j]
        exact Work.ELTop.rayPt_T hN hφ ht1
      have hsq : t ^ 2 ∈ Set.Icc (ρ (k + 1)) (ρ k) := by
        refine ⟨?_, ?_⟩
        · rw [← (hρ (k + 1)).2]
          exact pow_le_pow_left₀ (by linarith [(hρ (k + 1)).1]) ht.1 2
        · rw [← (hρ k).2]
          exact pow_le_pow_left₀ (le_of_lt htpos) ht.2 2
      have hin : Work.EL.rayPt hN (θ (j + 1)) (t ^ 2) ∈ C k (j + 1) :=
        ih hkM1 (j + 1) ⟨t ^ 2, hsq, rfl⟩
      rw [hstep] at hin
      rcases hD1 k hk j (Work.EL.rayPt hN (θ j) t) hin with hmem | hmem
      · exact Or.inl hmem
      · exact Or.inr (by simpa using hmem)
    · exact (hD2k j).2.2
    · refine ⟨Work.EL.rayPt hN (θ j) (ρ (k + 1)), ?_, ?_⟩
      · exact ⟨ρ (k + 1), ⟨hk1, le_rfl⟩, rfl⟩
      · exact ih hkM1 j ⟨ρ (k + 1), ⟨le_rfl, hk0⟩, rfl⟩

end Work.SeedCertRay
