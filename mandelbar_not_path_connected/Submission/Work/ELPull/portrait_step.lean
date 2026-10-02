import Mathlib
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELPull

theorem portrait_step {c : ℂ} {hN : DynB c}
    (himg : ∀ {θ' : ℝ} {y : ℂ}, LandsN hN θ' y →
      LandsN hN (T θ') (LeanEval.ComplexAnalysis.Tantibar c y))
    (hcount : PortraitCount hN)
    {y y' : ℂ} (hy : LeanEval.ComplexAnalysis.Tantibar c y' = y)
    {u v u' v' : ℝ}
    (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1) (huv : u ≠ v)
    (hport : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (LandsN hN θ y ↔ θ = u ∨ θ = v))
    (hu' : u' ∈ Set.Ico 0 1) (hv' : v' ∈ Set.Ico 0 1)
    (hTu : T u' = u) (hTv : T v' = v)
    (hlu : LandsN hN u' y') (hlv : LandsN hN v' y') :
    ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (LandsN hN θ y' ↔ θ = u' ∨ θ = v') := by
  intro θ hθ
  constructor
  · intro hland
    have hTθ : T θ ∈ Set.Ico 0 1 := by
      refine ⟨?_, ?_⟩
      · simpa only [T] using Int.fract_nonneg (-2 * θ)
      · simpa only [T] using Int.fract_lt_one (-2 * θ)
    have hlands : LandsN hN (T θ) y := by
      have h := himg hland
      rwa [hy] at h
    have hcount' := hcount y y' hy ⟨u, v, hu, hv, huv, hport⟩
    rcases (hport (T θ) hTθ).mp hlands with h | h
    · left
      exact hcount' θ u' hθ hu' hland hlu (by rw [h, hTu])
    · right
      exact hcount' θ v' hθ hv' hland hlv (by rw [h, hTv])
  · rintro (rfl | rfl)
    · exact hlu
    · exact hlv

end Work.ELPull
