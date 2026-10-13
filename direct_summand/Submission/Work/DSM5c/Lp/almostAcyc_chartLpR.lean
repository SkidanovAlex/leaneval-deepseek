import Mathlib
import Submission.Work.DSM5c.Lp.ChartLpRQuot
import Submission.Work.DSM5c.Lp.almostAcyc_tiltGen
import Submission.Work.DSM5c.Lp.chartDToLp_exists
import Submission.Work.DSM5c.Devissage.almostAcyc_surjective_desc

/-!
# DSM5c/Lp — the characteristic-`p` input on the mod-`p` chart complex over the tilt

The characteristic-`p` input `Work.DSM5c.Lp.almostAcyc_tiltGen` (almost acyclicity of the Čech
complex of the perfected tilted charts modulo `((ϖ♭)^p)`, with the diagonal coaugmentation
`perfChartCoaug`) is pushed forward along the termwise quotient
`Work.DSM5c.Lp.perfChartToLpR : perfChartPresheaf ⟶ chartLpR` to the mod-`p` chart presheaf
`Work.DSM5c.Lp.chartLpR`.  This is the dévissage
`Work.DSM5c.Devissage.almostAcyc_surjective_desc`, whose three side conditions are supplied here:

* **termwise surjectivity** of the induced chain map of Čech complexes: its degree-`q` component is
  the product `Limits.Pi.map` of the components of `perfChartToLpR`
  (`cech_map_f_chartLpR`, a `rfl` lemma), each of which is surjective by
  `perfChartToLpR_app_surjective`; products of surjections are surjective
  (`Work.DSM5c.Lp.surjective_Pi_map`);
* **saturation of `((ϖ♭)^p) · ⊤`** along it: the kernel in degree `q` is again
  `((ϖ♭)^p) · ⊤`, because the kernel of a product of maps with kernel `(r) · ⊤` is `(r) · ⊤`
  (`Work.DSM5c.Lp.ker_Pi_map_span`, which applies to *principal* ideals and arbitrary index types;
  note that `ι` is not assumed finite here) applied to `perfChartToLpR_app_ker`; finally a
  principal multiple of the whole module is saturated along a surjection with that kernel
  (`Work.DSM5c.Lp.sat_of_ker`);
* the **coaugmentation compatibility**, which is `rfl` by definition of
  `Work.DSM5c.Lp.chartLpRCoaug`.

The degree-`q` term of `Č(P)` is the categorical product over `i : (Fin (q+1) → ι)` of the values
of the presheaf `P` on the intersections, so both `surjective_Pi_map` and `ker_Pi_map_span` apply
verbatim.
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

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]

/-! ## The degree-`q` component of the induced Čech chain map -/

/-- The component at degree `q` of the chain map induced by a natural transformation of presheaves
of `W`-modules is the product of the components of `η` at the chart intersections.  (A `rfl` lemma;
local copy of `Work.DSM5c.Lp.cech_map_f`, kept so that the assembly only needs the
`ChartLpRQuot` layer.) -/
theorem cech_map_f_chartLpR (F G : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} (PreTilt W p)) (η : F ⟶ G)
    (q : ℕ) :
    ((cechComplexFunctor (chartIdx ι)).map η).f q =
      CategoryTheory.Limits.Pi.map (fun i : (Fin (q + 1) → ι) =>
        η.app (op ((FormalCoproduct.power (FormalCoproduct.mk ι (chartIdx ι))
          (Fin (q + 1))).obj i))) :=
  rfl

/-- **The degree-`q` component of the Čech chain map `perfChartToLpR` is surjective.**  It is the
product of the termwise quotient maps `perfChartToLpR_app_surjective`. -/
theorem perfChartToLpR_cech_surjective (Q : DSMap.PerfectoidData p W) (t : ι → W)
    (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) (q : ℕ) :
    Function.Surjective (((cechComplexFunctor (chartIdx ι)).map
      (perfChartToLpR Q t tr htr0 htr j₀ e)).f q).hom := by
  rw [cech_map_f_chartLpR (perfChartPresheaf p (chartTiltGen Q t tr htr0 htr j₀ e))
    (chartLpR Q t tr htr0 htr j₀ e) (perfChartToLpR Q t tr htr0 htr j₀ e) q]
  exact surjective_Pi_map _ _ _
    (fun i => perfChartToLpR_app_surjective Q t tr htr0 htr j₀ e _)

/-- **The kernel of the degree-`q` component of the Čech chain map `perfChartToLpR`** is
`((ϖ♭)^p) · ⊤`: the kernel of a product of maps with kernel `(r) · ⊤` is `(r) · ⊤`
(`ker_Pi_map_span`, valid for principal ideals and arbitrary index types). -/
theorem perfChartToLpR_cech_ker (Q : DSMap.PerfectoidData p W) (t : ι → W)
    (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) (q : ℕ) :
    LinearMap.ker (((cechComplexFunctor (chartIdx ι)).map
      (perfChartToLpR Q t tr htr0 htr j₀ e)).f q).hom =
      Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p} • (⊤ : Submodule (PreTilt W p)
        (((cechComplexFunctor (chartIdx ι)).obj
          (perfChartPresheaf p (chartTiltGen Q t tr htr0 htr j₀ e))).X q)) := by
  rw [cech_map_f_chartLpR (perfChartPresheaf p (chartTiltGen Q t tr htr0 htr j₀ e))
    (chartLpR Q t tr htr0 htr j₀ e) (perfChartToLpR Q t tr htr0 htr j₀ e) q]
  exact ker_Pi_map_span _ _ _ _
    (fun i => perfChartToLpR_app_ker Q t tr htr0 htr j₀ e _)

/-! ## The target -/

/-- **The characteristic-`p` input on the mod-`p` chart complex over the tilt**, modulo `((ϖ♭)^p)`.  Obtained from `Work.DSM5c.Lp.almostAcyc_tiltGen` by the descent `Work.DSM5c.Devissage.almostAcyc_surjective_desc` along the termwise quotient `Work.DSM5c.Lp.perfChartToLpR` (whose Čech chain map has kernel `((ϖ♭)^p) · ⊤`), with the coaugmentation `Work.DSM5c.Lp.chartLpRCoaug`.

Elaboration hints: use `set_option allowUnsafeReducibility true` and
`attribute [local reducible] Work.DSM5c.chartTiltGen Work.DSM5c.tiltChart Work.DSM5c.Lp.chartLpRObj Work.DSM5c.Lp.chartLpROfHom DSMap.Mix2.perfChartRing DSMap.Mix2.perfChartPresheaf DSMap.Mix2.locPresheaf`
(so that type class search resolves the ring structure on the carriers of the presheaf values), and
write the index type of the degree-`q` product explicitly as the `.I` of the formal-coproduct power
when instantiating `Work.DSM5c.Lp.ker_Pi_map_span`.  An attempted proof is in the git history of
`Submission/Work/DSM5c/Lp/AlmostAcycChartLpR.lean`; the only obstruction was that instantiation. -/
theorem almostAcyc_chartLpR {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [Finite ι] [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (hM5b : Work.DSM5c.M5bInput p (PreTilt W p) (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e) (Work.DSM5c.tiltVarpi Q)) : DSMap.Mix2.AlmostAcyc (fun k => (frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)) (Ideal.span {(Work.DSM5c.tiltVarpi Q) ^ p}) ((CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj (Work.DSM5c.Lp.chartLpR Q t tr htr0 htr j₀ e)) (Work.DSM5c.Lp.chartLpRCoaug Q t tr htr0 htr j₀ e) := by
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
    (hK := Work.DSM5c.Lp.almostAcyc_tiltGen Q t tr htr0 htr j₀ e hM5b)
    ?_ ?_
  · intro q
    exact Work.DSM5c.Lp.perfChartToLpR_cech_surjective Q t tr htr0 htr j₀ e q
  · -- saturation of `((ϖ♭)^p) · ⊤` along the surjection with that kernel
    intro q x hx
    refine Work.DSM5c.Lp.sat_of_ker (g := (((CategoryTheory.cechComplexFunctor
        (DSMap.Mix2.chartIdx ι)).map
        (Work.DSM5c.Lp.perfChartToLpR Q t tr htr0 htr j₀ e)).f q).hom)
      (Work.DSM5c.Lp.perfChartToLpR_cech_surjective Q t tr htr0 htr j₀ e q)
      ((Work.DSM5c.tiltVarpi Q) ^ p) ?_ x hx
    intro y
    rw [← LinearMap.mem_ker,
      Work.DSM5c.Lp.perfChartToLpR_cech_ker Q t tr htr0 htr j₀ e q]

end Work.DSM5c.Lp
