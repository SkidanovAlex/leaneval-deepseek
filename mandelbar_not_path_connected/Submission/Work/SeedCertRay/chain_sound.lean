import Mathlib
import Submission.Work.SeedCertRay.Basic
import Submission.Work.SeedCertRay.isPreconnected_seg
import Submission.Work.SeedCertRay.preconnected_subset_or_subset
import Submission.Work.SeedCertRay.subset_of_preconnected_of_sep
import Submission.Work.SeedCertRay.box_isClosed
import Submission.Work.SeedCertRay.sqrtCover_of_bounds
import Submission.Work.SeedCertRay.sepPair_of_halfplane
import Submission.Work.ELTop.landsN_map

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open Set
open LeanEval.ComplexAnalysis (Tantibar)

theorem chain_sound {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℕ → ℝ) (hθ : ∀ j, θ (j + 1) = Work.EL.T (θ j)) (ρ : ℕ → ℝ) (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) (X : Work.SeedCertRay.Box) (hcX : X.mem c) (B : ℕ → ℕ → Work.SeedCertRay.Box) (hD0 : ∀ j, Work.SeedCertRay.seg hN (θ j) (ρ 1) (ρ 0) ⊆ (B 0 j).toSet) (hD1 : ∀ k j, Work.SeedCertRay.SqrtCover (B k (j + 1)) X (B (k + 1) j)) (hD2 : ∀ k j, Work.SeedCertRay.SepSelf (B (k + 1) j) ∧ Work.SeedCertRay.SepPair (B k j) (B (k + 1) j)) : ∀ k j, Work.SeedCertRay.seg hN (θ j) (ρ (k + 1)) (ρ k) ⊆ (B k j).toSet := by
  intro k
  induction k with
  | zero => intro j; exact hD0 j
  | succ k ih =>
    intro j
    have hk1 : ρ (k + 2) ≤ ρ (k + 1) := by
      have h1 := (hρ (k + 1)).1
      have h2 := (hρ (k + 1)).2
      nlinarith [sq_nonneg (ρ (k + 2) - 1)]
    have hk : ρ (k + 1) ≤ ρ k := by
      have h1 := (hρ k).1
      have h2 := (hρ k).2
      nlinarith [sq_nonneg (ρ (k + 1) - 1)]
    refine subset_of_preconnected_of_sep
      (s := seg hN (θ j) (ρ (k + 2)) (ρ (k + 1)))
      (u := (B (k + 1) j).toSet) (v := (B (k + 1) j).neg.toSet) (w := (B k j).toSet)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact isPreconnected_seg hN (θ j) (ρ (k + 2)) (ρ (k + 1)) (hρ (k + 1)).1
    · exact box_isClosed _
    · exact box_isClosed _
    · rw [Box.neg_toSet]; exact (hD2 k j).1
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
      have hin : Work.EL.rayPt hN (θ (j + 1)) (t ^ 2) ∈ (B k (j + 1)).toSet :=
        ih (j + 1) ⟨t ^ 2, hsq, rfl⟩
      have hq : (B k (j + 1)).mem (Tantibar c (Work.EL.rayPt hN (θ j) t)) := by
        rw [← hstep]; exact Box.mem_toSet.mp hin
      rcases hD1 k j (Tantibar c (Work.EL.rayPt hN (θ j) t)) c
        (Work.EL.rayPt hN (θ j) t) hq hcX rfl with hmem | hmem
      · exact Or.inl (Box.mem_toSet.mpr hmem)
      · refine Or.inr ?_
        rw [Box.mem_toSet, Box.mem_neg]
        exact hmem
    · rw [Box.neg_toSet]; exact (hD2 k j).2
    · refine ⟨Work.EL.rayPt hN (θ j) (ρ (k + 1)), ?_, ?_⟩
      · exact ⟨ρ (k + 1), ⟨hk1, le_rfl⟩, rfl⟩
      · exact ih j ⟨ρ (k + 1), ⟨le_rfl, hk⟩, rfl⟩

end Work.SeedCertRay
