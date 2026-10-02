import Mathlib
import Submission.Work.PARIMPL.Leak
import Submission.Work.Final.equatorLeak_shift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.PARIMPL.leak_shift_int` — the equator leak is invariant under integer shifts

The repelling coordinate `Ψ` of the parabolic flower satisfies the equivariance
`Ψ (w + 1) = F c₀ (Ψ w)`, where `F c₀ = (T_{c₀})^{10}` (`Work.EL.F_eq_tantibar`).  The filled
Julia set `K c₀ = Work.EL.K c₀` is totally invariant under `T_{c₀}`
(`Work.Final.mem_K_iff_Tantibar_mem_K`, iterated), so the property "`Ψ w` escapes" is invariant
under `w ↦ w + 1`.  Hence a real leaking point `x` (`Ψ x ∉ K c₀`) propagates to every integer
translate `Ψ (x + n) ∉ K c₀`.

This is what lets PARIMPL move the leak point an arbitrary integer amount towards the escaping
region (see `Submission/Work/PARIMPL/NOTES.md` §8).
-/

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar)

/-- The filled Julia set `Work.EL.K c` is totally invariant under the iterates of `T_c`:
an iterate of `z` lies in `K c` exactly when `z` does. -/
theorem mem_K_tantibar_iterate_iff (c z : ℂ) (m : ℕ) :
    (Tantibar c)^[m] z ∈ Work.EL.K c ↔ z ∈ Work.EL.K c := by
  induction m generalizing z with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih ((Tantibar c) z)).trans (Work.Final.mem_K_iff_Tantibar_mem_K c z).symm

/-- The shift relation `Ψ (w + 1) = F c₀ (Ψ w)` with `F c₀ = (T c₀)^{10}` makes the property
`Ψ w ∉ K c₀` invariant under `w ↦ w + 1`: the forward image stays outside the filled Julia set by
forward invariance of the escape set, and the backward image stays outside it by total invariance
of `K c₀`. -/
theorem notMem_K_shift_iff {c₀ : ℂ} {Ψ : ℂ → ℂ}
    (hΨ : ∀ w : ℂ, Ψ (w + 1) = Work.EL.F c₀ (Ψ w)) (w : ℂ) :
    Ψ (w + 1) ∉ Work.EL.K c₀ ↔ Ψ w ∉ Work.EL.K c₀ := by
  rw [hΨ w, Work.EL.F_eq_tantibar]
  constructor
  · intro hnm hmem
    exact hnm ((mem_K_tantibar_iterate_iff c₀ (Ψ w) 10).mpr hmem)
  · intro hnm hmem
    exact hnm ((mem_K_tantibar_iterate_iff c₀ (Ψ w) 10).mp hmem)

theorem leak_shift_int {c₀ : ℂ} {Ψ : ℂ → ℂ} (hΨ : ∀ w : ℂ, Ψ (w + 1) = Work.EL.F c₀ (Ψ w)) {x : ℝ} (h : Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c₀) (n : ℤ) : Ψ (((x + (n : ℝ)) : ℝ) : ℂ) ∉ Work.EL.K c₀ := by
  -- Rewrite the argument as `(x : ℂ) + (n : ℂ)`, then run the integer induction with the
  -- one-step symmetry `notMem_K_shift_iff`.
  have key : ∀ n : ℤ, Ψ ((x : ℂ) + (n : ℂ)) ∉ Work.EL.K c₀ := by
    intro n
    refine Int.induction_on n ?_ ?_ ?_
    · simpa using h
    · intro i hi
      have hw := (notMem_K_shift_iff hΨ ((x : ℂ) + (i : ℂ))).mpr hi
      have harg : ((x : ℂ) + (((i : ℤ) + 1 : ℤ) : ℂ)) = ((x : ℂ) + (i : ℂ)) + 1 := by
        push_cast; ring
      rw [harg]; exact hw
    · intro i hi
      have hw := (notMem_K_shift_iff hΨ ((x : ℂ) + ((-(i : ℤ) - 1 : ℤ) : ℂ))).mp
      refine hw ?_
      have harg : ((x : ℂ) + ((-(i : ℤ) - 1 : ℤ) : ℂ)) + 1
          = (x : ℂ) + ((-(i : ℤ) : ℤ) : ℂ) := by push_cast; ring
      rwa [harg]
  have hn : (((x + (n : ℝ)) : ℝ) : ℂ) = (x : ℂ) + (n : ℂ) := by push_cast; ring
  rw [hn]; exact key n

end Work.PARIMPL
