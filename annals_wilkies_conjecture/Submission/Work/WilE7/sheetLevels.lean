import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.sheetAssembly
import Submission.Work.WilE7.sheetComponent

namespace Work.WilE7

/-- A function on `Fin (m+1)` is reconstructed from its initial `m` coordinates and its value at
the last coordinate. -/
private theorem sheetLevels_snoc_init {m : ℕ} (v : Fin (m + 1) → ℝ) :
    Fin.snoc (Fin.init v) (v (Fin.last m)) = v :=
  Fin.snoc_init_self v

theorem sheetLevels {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (C : Set (Fin p → ℝ))
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) = WilkiesDesign.E.projSnd p (m + 1) z) :
    ∀ x ∈ C, ∀ t : ℝ,
      (∃ w : Fin m → ℝ, Fin.append x (Fin.snoc w t) ∈ S.X.set) ↔
        ∃ j : Fin k, (s j x) (Fin.last m) = t := by
  intro x hx t
  constructor
  · -- Every point of the stratum is on the graph of some `s j`, so its last coordinate is
    -- the last coordinate of that graph over the base point `x`.
    rintro ⟨w, hw⟩
    have hproj : WilkiesDesign.E.projFirst p (m + 1) (Fin.append x (Fin.snoc w t)) = x :=
      projFirst_append x (Fin.snoc w t)
    obtain ⟨j, hj⟩ := hcov _ hw (by rw [hproj]; exact hx)
    rw [hproj, projSnd_append] at hj
    exact ⟨j, by rw [hj, Fin.snoc_last]⟩
  · -- Conversely, a graph `s j` whose last coordinate at `x` is `t` gives a point of the
    -- stratum whose `Fin.snoc`-decomposition ends in `t`.
    rintro ⟨j, hj⟩
    refine ⟨Fin.init (s j x), ?_⟩
    have hsnoc : Fin.snoc (Fin.init (s j x)) t = s j x := by
      rw [← hj]
      exact sheetLevels_snoc_init (s j x)
    rw [hsnoc]
    exact hsub j x hx

end Work.WilE7
