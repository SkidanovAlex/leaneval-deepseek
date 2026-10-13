import Mathlib
import Submission.Work.DSM5c.Lp.ChartLpRQuot
import Submission.Work.DSM5c.Lp.almostAcyc_chartLpR
import Submission.Work.DSM5c.Lp.tiltGenU
import Submission.Work.DSM5c.Devissage.almostAcyc_surjective_desc

/-!
# DSM5c/Lp — the tilt-side mod-`p` chart complex at an arbitrary universe

Universe-polymorphic (`Type u`) restatement of `Work.DSM5c.Lp.almostAcyc_chartLpR` (and of the
auxiliary `Work.DSM5c.Lp.sat_of_ker`, which is pinned at `Type 0`): the characteristic-`p` input
modulo `((ϖ♭)^p)` on the Čech complex of the mod-`p` chart presheaf `chartLpR` over the tilt
`W♭ = PreTilt W p`, obtained from `Work.DSM5c.Lp.almostAcyc_tiltGenU` by the descent
`Work.DSM5c.Devissage.almostAcyc_surjective_desc` along the termwise quotient
`Work.DSM5c.Lp.perfChartToLpR`.  All the other ingredients
(`perfChartToLpR_cech_surjective`, `perfChartToLpR_cech_ker`, `ker_Pi_map_span`,
`surjective_Pi_map`) are already universe-polymorphic.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option allowUnsafeReducibility true

attribute [local reducible] Work.DSM5c.chartTiltGen Work.DSM5c.tiltChart
  Work.DSM5c.Lp.chartLpRObj Work.DSM5c.Lp.chartLpROfHom
  DSMap.Mix2.perfChartRing DSMap.Mix2.perfChartPresheaf DSMap.Mix2.locPresheaf

namespace Work.DSM5c.Lp

universe u

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

/-- **Saturation of a principal `I • ⊤` along a surjection with that kernel**
(universe-polymorphic copy of `Work.DSM5c.Lp.sat_of_ker`). -/
lemma sat_of_kerU {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (r : R) (hker : ∀ x : M, g x = 0 ↔ x ∈ Ideal.span {r} • (⊤ : Submodule R M))
    (x : M) (hx : g x ∈ Ideal.span {r} • (⊤ : Submodule R N)) :
    x ∈ Ideal.span {r} • (⊤ : Submodule R M) := by
  obtain ⟨v, hv⟩ := (Work.DSM5c.mem_span_singleton_smul_top (W := R) r (g x)).mp hx
  obtain ⟨v', hv'⟩ := hg v
  have hzero : g (x - r • v') = 0 := by
    rw [map_sub, map_smul, hv', hv, sub_self]
  have hmem : x - r • v' ∈ Ideal.span {r} • (⊤ : Submodule R M) := (hker _).mp hzero
  have hx' : x = (x - r • v') + r • v' := by abel
  rw [hx']
  exact Submodule.add_mem _ hmem
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top)

/-- **The characteristic-`p` input on the mod-`p` chart complex over the tilt**, modulo `((ϖ♭)^p)`,
at an arbitrary universe (universe-polymorphic copy of
`Work.DSM5c.Lp.almostAcyc_chartLpR`). -/
theorem almostAcyc_chartLpRU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι]
    [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hM5b : Work.DSM5c.M5bInput p (PreTilt W p)
      (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) (Work.DSM5c.tiltVarpi Q)) :
    DSMap.Mix2.AlmostAcyc (fun k => (frobeniusEquiv (PreTilt W p) p).symm^[k]
      (Work.DSM5c.tiltVarpi Q)) (Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p})
      ((CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj
        (Work.DSM5c.Lp.chartLpR Q t tr htr0 htr j₀ e))
      (Work.DSM5c.Lp.chartLpRCoaug Q t tr htr0 htr j₀ e) := by
  refine Work.DSM5c.Devissage.almostAcyc_surjective_desc
    (ϖ := fun k => (frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q))
    (I := Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p})
    (K := (CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj
      (DSMap.Mix2.perfChartPresheaf p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e)))
    (L := (CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj
      (Work.DSM5c.Lp.chartLpR Q t tr htr0 htr j₀ e))
    (f := (CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).map
      (Work.DSM5c.Lp.perfChartToLpR Q t tr htr0 htr j₀ e))
    (eK := DSMap.Mix2.perfChartCoaug p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e))
    (eL := Work.DSM5c.Lp.chartLpRCoaug Q t tr htr0 htr j₀ e)
    (he := fun _ => rfl)
    (hK := Work.DSM5c.Lp.almostAcyc_tiltGenU Q t tr htr0 htr j₀ e hM5b)
    ?_ ?_
  · intro q
    exact Work.DSM5c.Lp.perfChartToLpR_cech_surjective Q t tr htr0 htr j₀ e q
  · intro q x hx
    refine Work.DSM5c.Lp.sat_of_kerU (g := (((CategoryTheory.cechComplexFunctor
        (DSMap.Mix2.chartIdx ι)).map
        (Work.DSM5c.Lp.perfChartToLpR Q t tr htr0 htr j₀ e)).f q).hom)
      (Work.DSM5c.Lp.perfChartToLpR_cech_surjective Q t tr htr0 htr j₀ e q)
      ((Work.DSM5c.tiltVarpi Q) ^ p) ?_ x hx
    intro y
    rw [← LinearMap.mem_ker,
      Work.DSM5c.Lp.perfChartToLpR_cech_ker Q t tr htr0 htr j₀ e q]

end Work.DSM5c.Lp
