import Mathlib
import Submission.Work.DSM5c.Lp.ThetaCoord
import Submission.Work.DSM5c.Lp.ThetaBasicU

namespace Work.DSM5c.Lp

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false

-- `FormalCoproduct.power`'s indexing type `α → U.I` is definitionally the index type of the Čech
-- terms; the component formulas produce the latter in unfolded form, so the two must unify at the
-- `implicit` transparency level for the `erw` steps below to go through.
attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.power

attribute [local reducible] Work.DSM5c.chartTiltGen Work.DSM5c.tiltChart
  Work.DSM5c.Lp.chartLpRObj Work.DSM5c.Lp.chartLpROfHom
  DSMap.Mix2.perfChartRing DSMap.Mix2.perfChartPresheaf DSMap.Mix2.locPresheaf
  Work.DSM5c.Lp.chartLQObj Work.DSM5c.Lp.chartLQOfHom Work.DSM5c.Lp.chartLQEta
  Work.DSM5c.Lp.chartCmpLinear Work.DSM5c.Lp.chartDpTop

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

/-- **Naturality of the comparison along a restriction**, in the form needed for the differential
compatibility: `chartCmpMap` intertwines the functorial actions of the presheaves `chartLQ` (over
`W`) and `chartLpR` (over the tilt `W♭ = PreTilt W p`).  This is `chartCmpMap_mapU` with the
`map`-fields of the two presheaf literals unfolded. -/
theorem chartCmpMap_natU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]
    {ι : Type u} [Finite ι] [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : (Finset ι)ᵒᵖᵒᵖ} (f : S ⟶ T)
    (x : ↥(chartLQObj Q hθ t tr htr0 htr j₀ e S)) :
    chartCmpMap Q hθ t tr htr0 htr j₀ e T.unop.unop
        ((chartLQ Q hθ t tr htr0 htr j₀ e).map f x) =
      (chartLpR Q t tr htr0 htr j₀ e).map f
        (chartCmpMap Q hθ t tr htr0 htr j₀ e S.unop.unop x) := by
  rw [show (chartLQ Q hθ t tr htr0 htr j₀ e).map f
      = chartLQOfHom Q hθ t tr htr0 htr j₀ e f from rfl]
  rw [show (chartLpR Q t tr htr0 htr j₀ e).map f
      = chartLpROfHom Q t tr htr0 htr j₀ e f from rfl]
  exact chartCmpMap_mapU Q hθ t tr htr0 htr j₀ e f x

/-- **Differential compatibility of the transport `Θ`.**  `Θ_q` of
`Submission/Work/DSM5c/Lp/ThetaCoord.lean` (the componentwise mod-`p` comparison
`chartCmpMap : D_S ⧸ (p)·⊤ → R_S ⧸ (φ_S(ϖ♭)^p)` read through the product identifications of the
two Čech terms) commutes with the Čech differentials.  Blueprint:
`Submission/Work/DSM5c/Lp/probe/Stmts.lean` (`stmt_Theta_d`).  Ingredient: the naturality
`Work.DSM5c.Lp.chartCmpMap_mapU` (`Submission/Work/DSM5c/Lp/ThetaBasicU.lean`; the `Type 0`
original is `Work.DSM5c.Lp.chartCmpMap_map` in `Submission/Work/DSM5c/Lp/ThetaCmp.lean`, which
cannot be built because of its `maxHeartbeats`), plus the component formulas
`cechComplex_d_π_apply` and `Theta_π` of `ThetaCoord.lean`.

The proof is the componentwise computation: fix the tuple `y : Fin (q+2) → ι` and read both sides
in the `y`-component.  On the left, `Theta_π` gives the comparison of the `y`-component of `d z`,
which `cechComplex_d_π_apply` writes as the alternating sum of the coface components; `chartCmpMap`
is `W`-linear, so it distributes over the sum (`map_sum`, `map_zsmul`), and on each summand the
naturality `chartCmpMap_natU` converts the comparison of a coface into the coface of a comparison.
The right-hand side is, by `cechComplex_d_π_apply` for `chartLpR`, the same alternating sum whose
summands are the components of `Θ_q z` (`Theta_π`, read backwards), so the two agree term by term
(`Finset.sum_congr`). -/
theorem Theta_dU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι] [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (q : ℕ)
    (z : ↥(((cechComplexFunctor (chartIdx ι)).obj
      (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e)).X q)) :
    Work.DSM5c.Lp.Theta Q hθ t tr htr0 htr j₀ e (q + 1)
        ((((cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e)).d q (q + 1)).hom z) =
      ((((cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.Lp.chartLpR Q t tr htr0 htr j₀ e)).d q (q + 1)).hom
        (Work.DSM5c.Lp.Theta Q hθ t tr htr0 htr j₀ e q z)) := by
  refine (cech_pi_eq_iff).mpr (fun y => ?_)
  rw [Theta_π]
  rw [cechComplex_d_π_apply]
  rw [cechComplex_d_π_apply]
  simp only [Theta_π]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro x _
  erw [chartCmpMap_natU]
  rfl

end Work.DSM5c.Lp
