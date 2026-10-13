import Mathlib
import Submission.Work.DSM5c.Lp.chartDToLp_exists
import Submission.Work.DSM5c.Lp.chartLMap_algebraMap
import Submission.Work.DSM5c.Cech.chartCoaug_isCocycle

/-!
# DSM5c/Lp — the mod-`p` chart presheaf over the tilt `W♭`

`Work.DSM5c.chartLpObj` (`Submission/Work/DSM5c/ChartLpFunctor.lean`) is the mod-`p` chart
`L_S = R_S ⧸ (φ_S(ϖ♭)^p)` with the **`W`**-module structure `chartLAlg` (through PB2).  The
transport of the characteristic-`p` input needs the *same* presheaf with its natural
**`W♭ = PreTilt W p`**-module structure (the one induced by `chartPhi`), because that is the ring over
which the input `area_M5b` lives: on `L_S` the element `(ϖ♭)^p` acts by `0`, so `L_S` is a module over
`W♭ ⧸ (ϖ♭)^p`, the tilt-shadow of `W ⧸ (p)` (PB2).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.DSM5c.Lp

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]

/-! ## `chartLMap` is `W♭`-linear -/

/-- `chartLMap` fixes the constants, in the `W♭`-form. -/
theorem chartLMap_algebraMapR (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) (a : PreTilt W p) :
    chartLMap Q t tr htr0 htr j₀ e h (algebraMap (PreTilt W p)
        (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) a) =
      algebraMap (PreTilt W p)
        (tiltChart Q t tr htr0 htr j₀ e T ⧸ chartLIdeal Q t tr htr0 htr j₀ e T) a := by
  rw [IsScalarTower.algebraMap_apply (PreTilt W p) (↥(tiltChart Q t tr htr0 htr j₀ e S))
        (↥(tiltChart Q t tr htr0 htr j₀ e S) ⧸ chartLIdeal Q t tr htr0 htr j₀ e S),
      IsScalarTower.algebraMap_apply (PreTilt W p) (↥(tiltChart Q t tr htr0 htr j₀ e T))
        (↥(tiltChart Q t tr htr0 htr j₀ e T) ⧸ chartLIdeal Q t tr htr0 htr j₀ e T),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq]
  rw [chartLMap_mk, tiltChartRes_algebraMap]

/-- **`chartLMap` as a `W♭`-linear map.** -/
noncomputable def chartLMapLinear (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) :
    (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) →ₗ[PreTilt W p]
      (tiltChart Q t tr htr0 htr j₀ e T ⧸ chartLIdeal Q t tr htr0 htr j₀ e T) where
  toFun := chartLMap Q t tr htr0 htr j₀ e h
  map_add' := map_add _
  map_smul' := fun c x => by
    show chartLMap Q t tr htr0 htr j₀ e h (c • x) =
      c • chartLMap Q t tr htr0 htr j₀ e h x
    calc chartLMap Q t tr htr0 htr j₀ e h (c • x)
        = chartLMap Q t tr htr0 htr j₀ e h
            ((algebraMap (PreTilt W p) _ c) * x) :=
          congrArg _ (Algebra.smul_def c x)
      _ = chartLMap Q t tr htr0 htr j₀ e h (algebraMap (PreTilt W p) _ c) *
            chartLMap Q t tr htr0 htr j₀ e h x := RingHom.map_mul _ _ _
      _ = (algebraMap (PreTilt W p) _ c) * chartLMap Q t tr htr0 htr j₀ e h x := by
          rw [chartLMap_algebraMapR]
      _ = c • chartLMap Q t tr htr0 htr j₀ e h x := (Algebra.smul_def c _).symm

/-! ## The presheaf `Lp` over the tilt -/

/-- The object of `chartLpR` at `S`: the mod-`p` chart `L_S = R_S ⧸ (φ_S(ϖ♭)^p)`, as a
`W♭`-module through `chartPhi`. -/
noncomputable def chartLpRObj (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : (Finset ι)ᵒᵖᵒᵖ) : ModuleCat.{a} (PreTilt W p) :=
  ModuleCat.of (PreTilt W p)
    (↥((perfChartPresheaf p (chartTiltGen Q t tr htr0 htr j₀ e)).obj S) ⧸
      (chartLIdeal Q t tr htr0 htr j₀ e S.unop.unop).comap (RingHom.id _))

/-- The morphism data of `chartLpR`. -/
noncomputable def chartLpROfHom (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : (Finset ι)ᵒᵖᵒᵖ} (f : S ⟶ T) :
    chartLpRObj Q t tr htr0 htr j₀ e S ⟶ chartLpRObj Q t tr htr0 htr j₀ e T :=
  ModuleCat.ofHom (chartLMapLinear Q t tr htr0 htr j₀ e (leOfHom f.unop.unop))

/-- **The presheaf `Lp` of mod-`p` charts, over the tilt `W♭`.** -/
noncomputable def chartLpR (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} (PreTilt W p) where
  obj := chartLpRObj Q t tr htr0 htr j₀ e
  map f := chartLpROfHom Q t tr htr0 htr j₀ e f
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    show chartLMap Q t tr htr0 htr j₀ e (leOfHom (𝟙 S).unop.unop) (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ y
    rw [show leOfHom (𝟙 S).unop.unop = subset_refl S.unop.unop from Subsingleton.elim _ _,
      chartLMap_self_mk]
  map_comp {S T V} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    show chartLMap Q t tr htr0 htr j₀ e (leOfHom (f ≫ g).unop.unop) (Ideal.Quotient.mk _ y) =
      chartLMap Q t tr htr0 htr j₀ e (leOfHom g.unop.unop)
        (chartLMap Q t tr htr0 htr j₀ e (leOfHom f.unop.unop) (Ideal.Quotient.mk _ y))
    rw [show leOfHom (f ≫ g).unop.unop =
        (leOfHom f.unop.unop).trans (leOfHom g.unop.unop) from Subsingleton.elim _ _,
      chartLMap_comp_mk]

/-- On classes, `chartLpR.map f` is induced by the tilted chart restriction. -/
theorem chartLpR_map_mk (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : (Finset ι)ᵒᵖᵒᵖ} (f : S ⟶ T)
    (y : tiltChart Q t tr htr0 htr j₀ e S.unop.unop) :
    (chartLpR Q t tr htr0 htr j₀ e).map f (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _
        (tiltChartRes Q t tr htr0 htr j₀ e (leOfHom f.unop.unop) y) :=
  chartLMap_mk Q t tr htr0 htr j₀ e (leOfHom f.unop.unop) y

end Work.DSM5c.Lp
