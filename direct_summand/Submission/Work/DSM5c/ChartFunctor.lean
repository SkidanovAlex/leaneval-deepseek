import Submission.Work.DSM5c.ChartDMap

/-!
# DSM5c — the presheaf `Dp` of chart untilts

`Work.DSM5c.chartDMap` (`ChartDMap.lean`) gives, for `S ⊆ T`, the `W`-linear map
`D_S →ₗ[W] D_T` between the chart untilts `D_S = untiltOf R_S φ_S`.  This file packages those into
the presheaf

  `Work.DSM5c.chartD Q hθ t tr htr0 htr j₀ e : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W`

of the frozen statement `DSMap.Mix2.area_M5c`, i.e. the `Dp` of the M5c design.  The functor laws
reduce to the functor laws of `untiltOf.map` (which is what `untiltOf.map_id`/`untiltOf.map_comp`
below supply; the corresponding `W`-linearity is `Charts/UntiltMapAlgebra.lean`).

## Contents

* `Work.DSM5c.untiltOf.map_id_apply`, `Work.DSM5c.untiltOf.map_id`;
* `Work.DSM5c.untiltOf.map_comp_apply`, `Work.DSM5c.untiltOf.map_comp`;
* `Work.DSM5c.chartD` — the presheaf of chart untilts.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W]

/-! ## The functor laws for `untiltOf.map` -/

theorem untiltOf.map_id_apply {R : Type a} [CommRing R] (φ : PreTilt W p →+* R)
    (y : untiltOf (p := p) (W := W) R φ) :
    untiltOf.map (p := p) (W := W) φ φ (RingHom.id R) (by rw [RingHom.id_comp]) y = y := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
  rw [← hx]
  change untiltOf.map (p := p) (W := W) φ φ (RingHom.id R) _
      (untiltOf.mk (p := p) (W := W) φ x) = untiltOf.mk (p := p) (W := W) φ x
  rw [untiltOf.map_apply, WittVector.map_id]
  rfl

theorem untiltOf.map_id {R : Type a} [CommRing R] (φ : PreTilt W p →+* R) :
    untiltOf.map (p := p) (W := W) φ φ (RingHom.id R) (by rw [RingHom.id_comp]) =
      RingHom.id (untiltOf (p := p) (W := W) R φ) :=
  RingHom.ext fun y => untiltOf.map_id_apply (p := p) (W := W) φ y

theorem untiltOf.map_comp_apply {R R' R'' : Type a} [CommRing R] [CommRing R'] [CommRing R'']
    (φ : PreTilt W p →+* R) (φ' : PreTilt W p →+* R') (φ'' : PreTilt W p →+* R'')
    (ψ : R →+* R') (ψ' : R' →+* R'') (h : ψ.comp φ = φ') (h' : ψ'.comp φ' = φ'')
    (y : untiltOf (p := p) (W := W) R φ) :
    untiltOf.map (p := p) (W := W) φ φ'' (ψ'.comp ψ) (by rw [RingHom.comp_assoc, h, h']) y =
      untiltOf.map (p := p) (W := W) φ' φ'' ψ' h'
        (untiltOf.map (p := p) (W := W) φ φ' ψ h y) := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
  rw [← hx]
  change untiltOf.map (p := p) (W := W) φ φ'' (ψ'.comp ψ) _
      (untiltOf.mk (p := p) (W := W) φ x) =
    untiltOf.map (p := p) (W := W) φ' φ'' ψ' h'
      (untiltOf.map (p := p) (W := W) φ φ' ψ h (untiltOf.mk (p := p) (W := W) φ x))
  rw [untiltOf.map_apply, untiltOf.map_apply, untiltOf.map_apply, ← wittVector_map_comp]
  rfl

theorem untiltOf.map_comp {R R' R'' : Type a} [CommRing R] [CommRing R'] [CommRing R'']
    (φ : PreTilt W p →+* R) (φ' : PreTilt W p →+* R') (φ'' : PreTilt W p →+* R'')
    (ψ : R →+* R') (ψ' : R' →+* R'') (h : ψ.comp φ = φ') (h' : ψ'.comp φ' = φ'') :
    untiltOf.map (p := p) (W := W) φ φ'' (ψ'.comp ψ) (by rw [RingHom.comp_assoc, h, h']) =
      (untiltOf.map (p := p) (W := W) φ' φ'' ψ' h').comp
        (untiltOf.map (p := p) (W := W) φ φ' ψ h) :=
  RingHom.ext fun y => untiltOf.map_comp_apply (p := p) (W := W) φ φ' φ'' ψ ψ' h h' y

/-! ## The presheaf of chart untilts — TODO (performance), with the exact obstruction

The presheaf of the frozen statement is

  `chartD Q hθ t tr htr0 htr j₀ e : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W`,
  `chartD.obj S = ModuleCat.of W (untiltOf R_S φ_S)` with the `W`-module structure `chartDAlg … S`,

with morphism data provided by `Work.DSM5c.chartDMap` (`ChartDMap.lean`) and functor laws from
`untiltOf.map_id` / `untiltOf.map_comp` above plus `Work.DSM5c.tiltChartRes_self` /
`tiltChartRes_comp`.

It is *not* written out here for a purely performance reason: elaborating the `Functor` structure
(the `by`-blocks for `obj`/`map`/`map_id`/`map_comp`) spends the entire `maxHeartbeats` budget
(1 600 000) in `isDefEq` / instance synthesis, because the `W`-module structures come from the
`letI := chartDAlg …` instances and `chartDAlg` unfolds `RingHom.toAlgebra`, so every `ModuleCat`
unification compares large structures.

The intended replacement (mechanical) is:

1. state the functor laws as *standalone closed lemmas* about `chartDMap`, e.g.
   `chartDMap_id : ∀ x, chartDMap … (subset_refl S) x = x` and
   `chartDMap_comp : ∀ x, chartDMap … (h₁.trans h₂) x = chartDMap … h₂ (chartDMap … h₁ x)`
   (both immediate from the definitions plus `tiltChartRes_self`/`tiltChartRes_comp` and
   `untiltOf.map_id_apply`/`untiltOf.map_comp_apply`, proved *outside* the structure);
2. then build the functor with `obj := chartDObj …`, `map := …`, and
   `map_id S := ModuleCat.ext (chartDMap_id …)`, `map_comp … := ModuleCat.ext (chartDMap_comp …)`
   — i.e. feed the structure closed terms instead of tactic blocks, which keeps `isDefEq` cheap.

(`chartDObj Q hθ t tr htr0 htr j₀ e S := by letI := chartDAlg … S.unop.unop; exact ModuleCat.of W …`
is the object helper; its type mentions no structure, so the `Functor` unification does not unfold a
`Functor.mk`.)

-/

/-! ## The presheaf of chart untilts -/

section ChartD

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W]
variable {ι : Type a} [DecidableEq ι]

/-- The `W`-module of the chart untilt `D_S = untiltOf R_S φ_S`, with the `W`-module structure
induced by `Work.DSM5c.chartDAlg`. -/
noncomputable def chartDObj (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : (Finset ι)ᵒᵖᵒᵖ) :
    ModuleCat.{a} W := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  exact ModuleCat.of W
    (untiltOf (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
      (chartPhi Q t tr htr0 htr j₀ e S.unop.unop))

/-- **The first functor law of `chartD`, in element form**: `chartDMap` along `S ⊆ S` is the
identity. -/
theorem chartDMap_self (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) (h : S ⊆ S)
    (x : untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S)) :
    chartDMap Q hθ t tr htr0 htr j₀ e h x = x := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show untiltOf.map (chartPhi Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S)
    (tiltChartRes Q t tr htr0 htr j₀ e h)
    (RingHom.ext fun r => tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h r)
    (untiltOf.mk (p := p) (W := W) (chartPhi Q t tr htr0 htr j₀ e S) a) =
      untiltOf.mk (p := p) (W := W) (chartPhi Q t tr htr0 htr j₀ e S) a
  rw [untiltOf.map_apply]
  have hh : h = subset_refl S := Subsingleton.elim _ _
  rw [hh, tiltChartRes_self Q t tr htr0 htr j₀ e, WittVector.map_id]
  rfl

/-- **The second functor law of `chartD`, in element form**: `chartDMap` along a composite is the
composite of the `chartDMap`s. -/
theorem chartDMap_trans (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) {S T V : Finset ι}
    (h₁ : S ⊆ T) (h₂ : T ⊆ V)
    (x : untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S)) :
    chartDMap Q hθ t tr htr0 htr j₀ e (h₁.trans h₂) x =
      chartDMap Q hθ t tr htr0 htr j₀ e h₂ (chartDMap Q hθ t tr htr0 htr j₀ e h₁ x) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e T
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e V
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show untiltOf.map (chartPhi Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e V)
      (tiltChartRes Q t tr htr0 htr j₀ e (h₁.trans h₂))
      (RingHom.ext fun r => tiltChartRes_algebraMap Q t tr htr0 htr j₀ e (h₁.trans h₂) r)
      (untiltOf.mk (p := p) (W := W) (chartPhi Q t tr htr0 htr j₀ e S) a) =
    untiltOf.map (chartPhi Q t tr htr0 htr j₀ e T) (chartPhi Q t tr htr0 htr j₀ e V)
      (tiltChartRes Q t tr htr0 htr j₀ e h₂)
      (RingHom.ext fun r => tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h₂ r)
      (untiltOf.map (chartPhi Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e T)
        (tiltChartRes Q t tr htr0 htr j₀ e h₁)
        (RingHom.ext fun r => tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h₁ r)
        (untiltOf.mk (p := p) (W := W) (chartPhi Q t tr htr0 htr j₀ e S) a))
  rw [untiltOf.map_apply, untiltOf.map_apply, untiltOf.map_apply]
  have hcomp : tiltChartRes Q t tr htr0 htr j₀ e (h₁.trans h₂) =
      (tiltChartRes Q t tr htr0 htr j₀ e h₂).comp (tiltChartRes Q t tr htr0 htr j₀ e h₁) :=
    (tiltChartRes_comp Q t tr htr0 htr j₀ e h₁ h₂).symm
  rw [hcomp, ← RingHom.comp_apply]
  have hmap : WittVector.map (p := p)
        ((tiltChartRes Q t tr htr0 htr j₀ e h₂).comp (tiltChartRes Q t tr htr0 htr j₀ e h₁)) =
      (WittVector.map (p := p) (tiltChartRes Q t tr htr0 htr j₀ e h₂)).comp
        (WittVector.map (p := p) (tiltChartRes Q t tr htr0 htr j₀ e h₁)) :=
    (wittVector_map_comp p (tiltChartRes Q t tr htr0 htr j₀ e h₁)
      (tiltChartRes Q t tr htr0 htr j₀ e h₂)).symm
  rw [hmap]
  rfl

/-- The morphism data of `chartD`: the bundled `W`-linear map `D_S → D_T` obtained from
`chartDMap`.  Stated as a separate definition so that the `W`-module instances (which come from
`chartDAlg` and are not global instances) are introduced by `letI` outside the `Functor` structure. -/
noncomputable def chartDOfHom (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : (Finset ι)ᵒᵖᵒᵖ} (f : S ⟶ T) :
    chartDObj (p := p) (W := W) Q hθ t tr htr0 htr j₀ e S ⟶
      chartDObj (p := p) (W := W) Q hθ t tr htr0 htr j₀ e T := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e T.unop.unop
  exact ModuleCat.ofHom (chartDMap Q hθ t tr htr0 htr j₀ e (leOfHom f.unop.unop))

/-- **The presheaf of chart untilts** `Dp`: the `Dp` of the frozen statement `DSMap.Mix2.area_M5c`,
with `Dp S = untiltOf R_S φ_S = 𝕎 R_S ⧸ 𝕎(φ_S)(ker θ_W)` the untilt of the perfected tilted chart
at `S`, and the structure maps `untiltOf.map` along the chart restrictions `tiltChartRes`. -/
noncomputable def chartD (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W where
  obj := chartDObj (p := p) (W := W) Q hθ t tr htr0 htr j₀ e
  map f := chartDOfHom (p := p) (W := W) Q hθ t tr htr0 htr j₀ e f
  map_id S := by
    ext x
    exact chartDMap_self Q hθ t tr htr0 htr j₀ e S.unop.unop (leOfHom (𝟙 S).unop.unop) x
  map_comp {S T V} f g := by
    ext x
    exact chartDMap_trans Q hθ t tr htr0 htr j₀ e (leOfHom f.unop.unop)
      (leOfHom g.unop.unop) x

end ChartD

end Work.DSM5c
