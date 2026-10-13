import Submission.Work.DSM5c.Charts.UntiltMapAlgebra

/-!
# DSM5c — the chart layer as a presheaf: restriction maps between the perfected tilted charts

The frozen node `DSMap.Mix2.area_M5c` asks for a presheaf `Dp` of `W`-modules on the Čech index
category `(Finset ι)ᵒᵖᵒᵖ` with a chart map `η : chartPresheaf t ⟶ Dp`.  The intended
`Dp` is the untilted perfected tilted chart

  `D_S := untiltOf R_S φ_S`,   `R_S := perfChartRing p (chartTiltGen Q t tr … j₀ e) S`,
  `φ_S : PreTilt W p →+* R_S` the algebra structure,

functorial in `S` via `Work.DSM5c.untiltOf.map` (`Charts.lean`) applied to the restriction maps
`R_S → R_T` of the perfected charts.

This file supplies the restriction maps and their two structural properties:

* `Work.DSM5c.tiltChartRes` — the ring hom `R_S →+* R_T` for `S ⊆ T` (the localisation map
  `locRes`, restricted to the subalgebras);
* `Work.DSM5c.tiltChartRes_algebraMap` — it is compatible with the `PreTilt W p`-algebra
  structures, which is exactly the hypothesis of `untiltOf.map` (`untiltOf.mapData`) and hence what
  makes `S ↦ D_S` a functor;
* `Work.DSM5c.tiltChartRes_id` / `tiltChartRes_comp` — the functor laws.

Together with `untiltOf.map` and `untiltOf.map_algebraMap` these give the functor `Dp` into
`ModuleCat.{a} W`; see `NOTES.md` §§12–17 for the remaining items (`η`, the chart-level mod-`p`
comparison `D_S ⧸ p ≅ R_S ⧸ (ϖ♭)^p`, the M5b transport and the assembly).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section ChartRestriction

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
variable {ι : Type a} [DecidableEq ι]

/-- **The restriction map between the perfected tilted charts**: for `S ⊆ T`, the localisation map
`locRes` between the ambient localisations, restricted to the perfected tilted chart subalgebras
(`perfChartRing_map_le` is what makes the codomain restriction legitimate). -/
noncomputable def tiltChartRes (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) :
    tiltChart Q t tr htr0 htr j₀ e S →+* tiltChart Q t tr htr0 htr j₀ e T where
  toFun x := ⟨locRes (chartTiltGen Q t tr htr0 htr j₀ e) h x.1,
    perfChartRing_map_le p (chartTiltGen Q t tr htr0 htr j₀ e) h ⟨x.1, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

@[simp] theorem tiltChartRes_coe (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) (x : tiltChart Q t tr htr0 htr j₀ e S) :
    (tiltChartRes Q t tr htr0 htr j₀ e h x : Localization.Away
        (tS (chartTiltGen Q t tr htr0 htr j₀ e) T)) =
      locRes (chartTiltGen Q t tr htr0 htr j₀ e) h x.1 :=
  rfl

/-- **Compatibility of the restriction maps with the `PreTilt W p`-algebra structure**: this is the
hypothesis `h` of `Work.DSM5c.untiltOf.map`, so the untilts of the charts form a functor. -/
theorem tiltChartRes_algebraMap (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) (r : PreTilt W p) :
    tiltChartRes Q t tr htr0 htr j₀ e h (algebraMap (PreTilt W p) _ r) =
      algebraMap (PreTilt W p) _ r := by
  refine Subtype.ext ?_
  rw [tiltChartRes_coe]
  exact AlgHom.commutes (locRes (chartTiltGen Q t tr htr0 htr j₀ e) h) r

end ChartRestriction

end Work.DSM5c
