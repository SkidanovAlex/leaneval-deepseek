import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.EXL

/-- The orbit of the parabolic point `z₁` under `T_c` is periodic (of period dividing `5` by
`per_half`), hence bounded, i.e. `z₁` lies in the filled Julia set `K c`. -/
theorem z1_mem_K {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) : d.z₁ ∈ Work.EL.K c₀ := by
  show Work.ParamRays.BoundedOrbit c₀ d.z₁
  have hper : ∀ n : ℕ,
      (LeanEval.ComplexAnalysis.Tantibar c₀)^[n + 5] d.z₁
        = (LeanEval.ComplexAnalysis.Tantibar c₀)^[n] d.z₁ := by
    intro n
    rw [Function.iterate_add_apply, d.per_half]
  have hmod : ∀ n : ℕ,
      (LeanEval.ComplexAnalysis.Tantibar c₀)^[n] d.z₁
        = (LeanEval.ComplexAnalysis.Tantibar c₀)^[n % 5] d.z₁ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases lt_or_ge n 5 with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
      · have hn : n = (n - 5) + 5 := by omega
        rw [hn, hper (n - 5), ih (n - 5) (by omega)]
        congr 1
        omega
  exact ⟨∑ i ∈ Finset.range 5, ‖(LeanEval.ComplexAnalysis.Tantibar c₀)^[i] d.z₁‖, fun n => by
    rw [Work.ParamRays.orbit, hmod n]
    exact Finset.single_le_sum (s := Finset.range 5)
      (f := fun i => ‖(LeanEval.ComplexAnalysis.Tantibar c₀)^[i] d.z₁‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num : 0 < 5)))⟩

end Work.GATE2.EXL
