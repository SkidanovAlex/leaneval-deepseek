import Mathlib
import Submission.Work.DSM5c.Lp.ThetaCoord
import Submission.Work.DSM5c.Lp.ThetaBasicU

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false

-- As in `ThetaCoord.lean`/`ThetaBasicU.lean`: the *cheap* chart definitions must be locally
-- reducible, otherwise type class search does not see the (quotient) ring/module structures on the
-- carriers of the two Čech complexes — in particular not `Algebra (PreTilt W p) (L_S)`, which is
-- what makes the `W♭`-scalar action on `L_S` multiplication by the algebra map.
attribute [local reducible] Work.DSM5c.chartTiltGen Work.DSM5c.tiltChart
  Work.DSM5c.Lp.chartLpRObj Work.DSM5c.Lp.chartLpROfHom
  DSMap.Mix2.perfChartRing DSMap.Mix2.perfChartPresheaf DSMap.Mix2.locPresheaf
  Work.DSM5c.Lp.chartLQObj Work.DSM5c.Lp.chartLQOfHom Work.DSM5c.Lp.chartLQEta
  Work.DSM5c.Lp.chartCmpLinear Work.DSM5c.Lp.chartDpTop

namespace Work.DSM5c.Lp

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

universe u

/-- **The vector match for the transport `Θ`.**  The `W`-scalar action on `Č(chartLQ)` (i.e. on
`D_S ⧸ (p)·⊤`, induced by `chartDAlg`) corresponds, through `Θ`, to the `W♭ = PreTilt W p`-scalar
action on `Č(chartLpR)` (induced by `chartPhi`) along `ϖ_k ↦ (ϖ♭)^{1/p^k} = varpiTiltShift Q k`.
Blueprint: `Submission/Work/DSM5c/Lp/probe/Stmts.lean` (`stmt_Theta_smul`).  Ingredient: the
vector match at the chart level `Work.DSM5c.Lp.chartLRingHom_varpiU`
(`Submission/Work/DSM5c/Lp/ThetaBasicU.lean`; `Type 0` original `chartLRingHom_varpi` in
`ThetaCmp.lean`) together with the `W`-linearity of `chartCmpMap` (`chartCmpLinear`; note that
`chartLpR`'s scalar action is `algebraMap (PreTilt W p) _ = mk ∘ chartPhi`). -/
theorem Theta_smulU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι] [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (q k : ℕ)
    (z : ↥(((cechComplexFunctor (chartIdx ι)).obj
      (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e)).X q)) :
    Work.DSM5c.Lp.Theta Q hθ t tr htr0 htr j₀ e q (Q.ϖ k • z) =
      ((frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)) •
        (Work.DSM5c.Lp.Theta Q hθ t tr htr0 htr j₀ e q z) := by
  -- `Θ` is defined componentwise, so reduce to the components of the two Čech terms.
  refine (Work.DSM5c.Lp.cech_pi_eq_iff).mpr fun y => ?_
  -- Each projection is linear over the respective scalars, and `Theta_π` computes `Θ` on the
  -- `y`-component:
  --   LHS = `chartCmpMap S_y ((Q.ϖ k) • π_y z)`,  RHS = `(ϖ♭)^{1/p^k} • chartCmpMap S_y (π_y z)`.
  rw [map_smul, Work.DSM5c.Lp.Theta_π, map_smul, Work.DSM5c.Lp.Theta_π]
  -- `chartCmpMap` is `W`-linear for the `chartLAlg` structure on its target `L_S`, so the
  -- `W`-action of `Q.ϖ k` on the source is the multiplication by `algebraMap W _ (Q.ϖ k)`.
  letI := Work.DSM5c.chartLAlg Q t tr htr0 htr j₀ e
    (Opposite.unop (Opposite.unop (Work.DSM5c.Lp.cechIdx q y)))
  rw [map_smul, Algebra.smul_def]
  -- `algebraMap W L_S = chartLRingHom` by definition of `chartLAlg` (`Algebra.mk`).
  have hap : algebraMap W (↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e
        (Opposite.unop (Opposite.unop (Work.DSM5c.Lp.cechIdx q y)))) ⧸
        Work.DSM5c.chartLIdeal Q t tr htr0 htr j₀ e
          (Opposite.unop (Opposite.unop (Work.DSM5c.Lp.cechIdx q y))))
      (Q.ϖ k) =
      Work.DSM5c.chartLRingHom Q t tr htr0 htr j₀ e
        (Opposite.unop (Opposite.unop (Work.DSM5c.Lp.cechIdx q y))) (Q.ϖ k) := rfl
  -- The vector match at the chart level identifies the class of `ϖ_k` in `L_S` with the class of
  -- the tilt `(ϖ♭)^{1/p^k} = varpiTiltShift Q k`.
  rw [hap, Work.DSM5c.Lp.chartLRingHom_varpiU]
  -- On `L_S` (a quotient ring of the tilt) the `W♭`-scalar action is multiplication by the
  -- algebra map, which is `Algebra.smul_def` for `L_S` (the type ascription brings the quotient
  -- module structure of `chartLpR` into scope).
  exact (Algebra.smul_def ((frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q))
    (Work.DSM5c.Lp.chartCmpMap Q hθ t tr htr0 htr j₀ e
        (Opposite.unop (Opposite.unop (Work.DSM5c.Lp.cechIdx q y)))
        ((Pi.π (Work.DSM5c.Lp.cechFam (ι := ι)
          (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e) q) y).hom z) :
      ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e
          (Opposite.unop (Opposite.unop (Work.DSM5c.Lp.cechIdx q y)))) ⧸
        Work.DSM5c.chartLIdeal Q t tr htr0 htr j₀ e
          (Opposite.unop (Opposite.unop (Work.DSM5c.Lp.cechIdx q y))))).symm

end Work.DSM5c.Lp

end Work.DSM5c.Lp

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

universe u

/-- **Alias of `Work.DSM5c.Lp.Work.DSM5c.Lp.Theta_smulU` under the name announced for this file**
(the enclosing duplicate namespace of the statement block above is inherited from the generated
stub; this alias keeps the vector match available as `Work.DSM5c.Lp.Theta_smulU`). -/
theorem Theta_smulU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι] [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (q k : ℕ)
    (z : ↥(((cechComplexFunctor (chartIdx ι)).obj
      (Work.DSM5c.Lp.chartLQ Q hθ t tr htr0 htr j₀ e)).X q)) :
    Work.DSM5c.Lp.Theta Q hθ t tr htr0 htr j₀ e q (Q.ϖ k • z) =
      ((frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)) •
        (Work.DSM5c.Lp.Theta Q hθ t tr htr0 htr j₀ e q z) :=
  Work.DSM5c.Lp.Work.DSM5c.Lp.Theta_smulU Q hθ t tr htr0 htr j₀ e q k z

end Work.DSM5c.Lp
