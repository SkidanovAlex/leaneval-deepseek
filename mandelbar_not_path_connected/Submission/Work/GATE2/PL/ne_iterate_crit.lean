import Mathlib
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.PL.critOrbit_not_mem_Pa

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Filter

/-- A `Good` function on `Dom v X k` (see `Submission/Work/GATE2/PL/Defs.lean`) never takes the
values `T^[j] c₀`, `1 ≤ j ≤ 4`. -/
theorem ne_iterate_crit {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (Work.GATE2.PL.G5 c₀) d.z₁}
    {FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (Work.GATE2.PL.G5 c₀) d.z₁ fl.Pa fl.φa}
    {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ} (hψ : Work.GATE2.PL.Good fl FF v X k ψ)
    {w : ℂ} (hw : w ∈ Work.GATE2.PL.Dom v X k) {j : ℕ} (hj : j ∈ Finset.Ioo 0 5) :
    ψ w ≠ (LeanEval.ComplexAnalysis.Tantibar c₀)^[j] c₀ := by
  -- `T_{c₀}` is continuous.
  have hT : Continuous (LeanEval.ComplexAnalysis.Tantibar c₀) := by
    rw [show LeanEval.ComplexAnalysis.Tantibar c₀ = fun z : ℂ => star z ^ 2 + c₀ from rfl]
    fun_prop
  -- The backwards basin of the attracting petal `fl.Pa`.
  let P : Set ℂ := {z : ℂ | ∃ n : ℕ, (Work.EL.F c₀)^[n] z ∈ fl.Pa}
  -- `ψ w` lies in it: some positive translate of `w` is far enough right.
  have hmemP : ψ w ∈ P := by
    obtain ⟨n, hn⟩ := exists_nat_gt (X - w.re)
    refine ⟨n, ?_⟩
    have hX : X < (w + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    have hfar : ψ (w + (n : ℂ)) ∈ FF.Pg := (hψ.far _ hX).1
    rw [Good.iterate_shift fl FF hψ hw n] at hfar
    exact FF.Pg_sub hfar
  -- Every point of `P` has its `F`-orbit converging to `z₁`.
  have hP : ∀ z ∈ P, Tendsto (fun n : ℕ => (Work.EL.F c₀)^[n] z) atTop (nhds d.z₁) := by
    intro z hz
    obtain ⟨n₀, hn₀⟩ := hz
    have h1 : Tendsto (fun n : ℕ => (Work.EL.F c₀)^[n] ((Work.EL.F c₀)^[n₀] z))
        atTop (nhds d.z₁) := fl.tendsto_Pa _ hn₀
    rw [show (fun n : ℕ => (Work.EL.F c₀)^[n] ((Work.EL.F c₀)^[n₀] z))
        = fun n : ℕ => (Work.EL.F c₀)^[n + n₀] z from by
      funext n; exact (Function.iterate_add_apply _ n n₀ z).symm] at h1
    exact (Filter.tendsto_add_atTop_iff_nat n₀).1 h1
  -- The critical orbit of `F` converges to `z₁` and `T^[j] z₁ ≠ z₁` for `1 ≤ j ≤ 4`.
  have hmain := iterate_ten_not_mem_of_tendsto (T := LeanEval.ComplexAnalysis.Tantibar c₀)
    (F := Work.EL.F c₀) (Work.EL.F_eq_tantibar c₀) hT (d.ne_per j hj) P hP d.crit.1
  intro hval
  exact hmain (hval ▸ hmemP)

end Work.GATE2.PL
