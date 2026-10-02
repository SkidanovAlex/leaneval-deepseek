import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- If `F` solves the Beltrami equation `∂̄F = μ · ∂F` with `μ` compactly supported and
bounded, then `∂̄F` is continuous with compact support, hence square integrable. -/
theorem fw_memLp_dzbar {F μ : ℂ → ℂ} {k : ℝ}
    (hF : ContDiff ℝ 1 F) (hμs : HasCompactSupport μ) (hμb : ∀ z : ℂ, ‖μ z‖ ≤ k)
    (hbelt : ∀ z : ℂ, Work.MRMT.dzbar F z = μ z * Work.MRMT.dz F z) :
    MeasureTheory.MemLp (fun z => Work.MRMT.dzbar F z) 2
        (MeasureTheory.volume : MeasureTheory.Measure ℂ) ∧
      HasCompactSupport (fun z => Work.MRMT.dzbar F z) := by
  -- `ContDiff ℝ 1 F` makes the Fréchet derivative (hence `∂̄F`) continuous.
  have hcont : Continuous (fun z => Work.MRMT.dzbar F z) := by
    simp only [Work.MRMT.dzbar]
    fun_prop
  -- The Beltrami equation forces `∂̄F` to vanish wherever `μ` does, so its support is
  -- contained in that of `μ`.
  have hsupp : Function.support (fun z => Work.MRMT.dzbar F z) ⊆ Function.support μ := by
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro hμz
    rw [hbelt z, hμz, zero_mul] at hz
    exact hz rfl
  have hcs : HasCompactSupport (fun z => Work.MRMT.dzbar F z) :=
    IsCompact.of_isClosed_subset hμs isClosed_closure (closure_mono hsupp)
  -- A continuous compactly supported function lies in every `L^p`.
  exact ⟨hcont.memLp_of_hasCompactSupport hcs, hcs⟩

end Work.MRMT.Found
