import Mathlib
import Submission.Work.FatouCoord.Flower
import Submission.Work.ELTop.Defs
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Filter

/-- **The general principle behind `critOrbit_not_mem_Pa`.**  Let `T` be a continuous self-map of
`ℂ` with `F = T^[10]`, let `z₁` be a limit point of the *`F`-orbit* of `c` (`hc`), and let `P` be any
set all of whose points have `F`-orbit converging to `z₁` (`hP` — in the application `P = fl.Pa`,
the attracting petal).  Then `T^[j] c ∉ P` for every `j` with `T^[j] z₁ ≠ z₁`.

Indeed, if `T^[j] c ∈ P`, then on the one hand `F^[n] (T^[j] c) → z₁` by `hP`, while on the other
hand `F^[n] (T^[j] c) = T^[j] (F^[n] c) → T^[j] z₁` by continuity of `T^[j]` and `hc`.  The two
limits of the same sequence agree, so `T^[j] z₁ = z₁`.

The hypothesis `hv` of `critOrbit_not_mem_Pa` is *not* needed: `d.crit` already provides the
convergence of the critical orbit of `F` to `z₁`. -/
theorem iterate_ten_not_mem_of_tendsto {T F : ℂ → ℂ} (hF : F = T^[10]) (hT : Continuous T)
    {z₁ c : ℂ} {j : ℕ} (hfix : T^[j] z₁ ≠ z₁) (P : Set ℂ)
    (hP : ∀ z ∈ P, Tendsto (fun n : ℕ => F^[n] z) atTop (nhds z₁))
    (hc : Tendsto (fun n : ℕ => F^[n] c) atTop (nhds z₁)) :
    T^[j] c ∉ P := by
  rw [hF] at hP hc
  intro hmem
  -- The two descriptions of the same sequence `n ↦ (T^[10])^[n] (T^[j] c)`.
  have h1 : Tendsto (fun n : ℕ => (T^[10])^[n] (T^[j] c)) atTop (nhds z₁) := hP _ hmem
  have h2 : Tendsto (fun n : ℕ => T^[j] ((T^[10])^[n] c)) atTop (nhds (T^[j] z₁)) :=
    ((hT.iterate j).tendsto z₁).comp hc
  have h3 : (fun n : ℕ => (T^[10])^[n] (T^[j] c)) =
      fun n : ℕ => T^[j] ((T^[10])^[n] c) := by
    funext n
    rw [← Function.iterate_mul, ← Function.iterate_add_apply, ← Function.iterate_add_apply]
    have h : 10 * n + j = j + 10 * n := Nat.add_comm _ _
    rw [h]
  rw [h3] at h1
  exact hfix (tendsto_nhds_unique h1 h2).symm

/-- The points `T^[j] c₀`, `1 ≤ j ≤ 4`, of the critical orbit of `T_{c₀}` do **not** lie in the
attracting petal `fl.Pa` of the parabolic flower of `F = (T_{c₀})^[10]` at its parabolic point
`d.z₁`, given that some point of the critical orbit of `F` does enter the petal. -/
theorem critOrbit_not_mem_Pa {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa)
    {j : ℕ} (hj : j ∈ Finset.Ioo 0 5) :
    (LeanEval.ComplexAnalysis.Tantibar c₀)^[j] c₀ ∉ fl.Pa := by
  -- `T_{c₀}` is continuous.
  have hT : Continuous (LeanEval.ComplexAnalysis.Tantibar c₀) := by
    rw [show LeanEval.ComplexAnalysis.Tantibar c₀ = fun z : ℂ => star z ^ 2 + c₀ from rfl]
    fun_prop
  -- The critical orbit of `F = (T_{c₀})^[10]` converges to `z₁` (`d.crit`), the petal converges to
  -- `z₁` along `F` (`fl.tendsto_Pa`), and `z₁` has exact period `5`, so `T^[j] z₁ ≠ z₁` for
  -- `1 ≤ j ≤ 4` (`d.ne_per`).
  exact iterate_ten_not_mem_of_tendsto (Work.EL.F_eq_tantibar c₀) hT (d.ne_per j hj) fl.Pa
    (fun z hz => fl.tendsto_Pa z hz) d.crit.1

end Work.GATE2.PL
