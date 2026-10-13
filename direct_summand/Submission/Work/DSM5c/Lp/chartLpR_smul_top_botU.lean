import Mathlib
import Submission.Work.DSM5c.Lp.ChartLpRQuot
import Submission.Work.DSM5c.Lp.almostAcyc_chartLpR
import Submission.Work.DSM5c.Lp.PiHelpers

namespace Work.DSM5c.Lp

/-! ## Auxiliary lemmas

`((ϖ♭)^p) • ⊤ = ⊥` on the Čech complex of `chartLpR` is proved in two steps.

* Each *presheaf value* `chartLpRObj Q t tr htr0 htr j₀ e S` is a quotient `R_S ⧸ (φ_S(ϖ♭)^p)` of the
  perfected tilted chart, and `φ_S((ϖ♭)^p) = φ_S(ϖ♭)^p` lies in the defining ideal; since the
  `W♭ = PreTilt W p`-module structure of the quotient is the one induced by the `W♭`-algebra
  structure (`Algebra.smul_def`), the class `(ϖ♭)^p` acts by `0` on it
  (`chartLpRObj_smul_top_botU`, from the general `smul_top_bot_quot_algebraU`).
* The degree-`q` term of the Čech complex is the categorical product of the values of the presheaf
  at the chart intersections (`…).X q = ∏ᶜ Z` by `rfl`), and for a *principal* ideal
  `span {r} • ⊤` of a product is the product of the `span {r} • ⊤` of the factors, with no
  finiteness assumption on the index type (`smul_top_bot_piObjU`, from
  `span_singleton_smul_top_pi` and `ModuleCat.piIsoPi`). -/

set_option linter.unusedSectionVars false
set_option allowUnsafeReducibility true
set_option synthInstance.maxHeartbeats 800000

section Helpers

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

universe u

/-- A quotient of an `R`-algebra by an ideal containing `algebraMap r` is killed by `r`:
`span {r} • ⊤ = ⊥`.  On `A ⧸ J` the scalar action of `R` is `r • x = algebraMap r * x`, and
`algebraMap r = 0` in the quotient by `Ideal.Quotient.mk_eq_mk`. -/
lemma smul_top_bot_quot_algebraU {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (J : Ideal A) (r : R) (hr : algebraMap R A r ∈ J) :
    Ideal.span {r} • (⊤ : Submodule R (A ⧸ J)) = ⊥ := by
  have h0 : algebraMap R (A ⧸ J) r = 0 := by
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  apply le_antisymm _ bot_le
  rw [Submodule.smul_le]
  intro r' hr' z _
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr'
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Submodule.mem_bot, Algebra.smul_def, map_mul, h0, mul_zero, zero_mul]

/-- For a *principal* ideal, `span {r} • ⊤` of a categorical product of modules is `⊥` as soon as
each factor is killed by `r`.  No finiteness assumption on the index type is needed. -/
lemma smul_top_bot_piObjU {R : Type*} [CommRing R] {κ : Type*} (Z : κ → ModuleCat R) (r : R)
    (h : ∀ i, Ideal.span {r} • (⊤ : Submodule R (Z i)) = ⊥) :
    Ideal.span {r} • (⊤ : Submodule R ↥(∏ᶜ Z)) = ⊥ := by
  rw [← comap_smul_top_equiv_gen (CategoryTheory.Iso.toLinearEquiv (ModuleCat.piIsoPi Z))
    (Ideal.span {r})]
  have hprod : Ideal.span {r} • (⊤ : Submodule R ((i : κ) → ↥(Z i))) = ⊥ := by
    rw [span_singleton_smul_top_pi]
    simp only [h]
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_pi] at hx
    funext i
    exact hx i (Set.mem_univ i)
  rw [hprod, Submodule.comap_bot, LinearEquiv.ker]

variable {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [DecidableEq ι]

attribute [local reducible] Work.DSM5c.chartTiltGen Work.DSM5c.tiltChart
  Work.DSM5c.Lp.chartLpRObj Work.DSM5c.Lp.chartLpROfHom
  DSMap.Mix2.perfChartRing DSMap.Mix2.perfChartPresheaf DSMap.Mix2.locPresheaf

/-- **Each chart of the tilt-side mod-`p` chart presheaf is killed by `(ϖ♭)^p`.**  The value at `S`
is `R_S ⧸ (φ_S(ϖ♭)^p)`, and the class of `(ϖ♭)^p` is `φ_S((ϖ♭)^p) = φ_S(ϖ♭)^p ∈ (φ_S(ϖ♭)^p)`. -/
lemma chartLpRObj_smul_top_botU (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : (Finset ι)ᵒᵖᵒᵖ) :
    Ideal.span {Work.DSM5c.tiltVarpi Q ^ p} •
      (⊤ : Submodule (PreTilt W p) ↑(chartLpRObj Q t tr htr0 htr j₀ e S)) = ⊥ := by
  have hmem : algebraMap (PreTilt W p)
      ↥((perfChartPresheaf p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e)).obj S)
      (Work.DSM5c.tiltVarpi Q ^ p) ∈
      Work.DSM5c.chartLIdeal Q t tr htr0 htr j₀ e S.unop.unop := by
    rw [show algebraMap (PreTilt W p)
        ↥((perfChartPresheaf p (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e)).obj S)
        (Work.DSM5c.tiltVarpi Q ^ p) =
        Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S.unop.unop (Work.DSM5c.tiltVarpi Q) ^ p from by
      rw [Work.DSM5c.chartPhi, map_pow],
      Work.DSM5c.chartLIdeal_def]
    exact Ideal.mem_span_singleton_self _
  exact smul_top_bot_quot_algebraU _ _ hmem

/-- **The degree-`q` term of the Čech complex of a presheaf killed termwise by `r` is killed by
`r`.**  The term is the categorical product of the values of `P` at the chart intersections (this is
`rfl`, as in `Work.DSM5c.Lp.cech_map_f_chartLpR`), so `smul_top_bot_piObjU` applies. -/
lemma cech_smul_top_botU {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    (P : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) (r : R)
    (h : ∀ S, Ideal.span {r} • (⊤ : Submodule R (P.obj S)) = ⊥) (q : ℕ) :
    Ideal.span {r} • (⊤ : Submodule R
      ↥(((cechComplexFunctor (chartIdx ι)).obj P).X q)) = ⊥ :=
  smul_top_bot_piObjU
    (fun i : (Fin (q + 1) → ι) =>
      P.obj (Opposite.op ((FormalCoproduct.power (FormalCoproduct.mk ι (chartIdx ι))
        (Fin (q + 1))).obj i)))
    r (fun _ => h _)

end Helpers

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

universe u

/-- **The ideal `((ϖ♭)^p)` acts by `0` on the tilt-side mod-`p` chart Čech complex.**  Each term
`L_S = R_S ⧸ (φ_S(ϖ♭)^p)` of `Č(chartLpR)` is a module over `W♭ ⧸ ((ϖ♭)^p)` (its defining ideal was
quotiented out by construction), so `((ϖ♭)^p) • ⊤ = ⊥` termwise, hence also on the finite products
that are the terms of the Čech complex.  Blueprint: `Submission/Work/DSM5c/Lp/probe/Stmts.lean`
(`stmt_chartLpR_smul_top_bot`); this is what lets the tilt-side `AlmostAcyc` (which is modulo
`((ϖ♭)^p)`) be read as honest exactness statements.  Useful ingredients:
`Work.DSM5c.Lp.smul_top_eq_chartLIdeal`, `ChartLpR.chartLpRObj`, `ModuleCat.piIsoPi`,
`Work.DSM5c.Lp.mem_smul_top_pi_iff`. -/
theorem chartLpR_smul_top_botU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι]
    [DecidableEq ι] (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (q : ℕ) :
    Ideal.span {Work.DSM5c.tiltVarpi Q ^ p} • (⊤ : Submodule (PreTilt W p)
      (((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.Lp.chartLpR Q t tr htr0 htr j₀ e)).X q)) = ⊥ := by
  exact cech_smul_top_botU (Work.DSM5c.Lp.chartLpR Q t tr htr0 htr j₀ e)
    (Work.DSM5c.tiltVarpi Q ^ p)
    (fun S => chartLpRObj_smul_top_botU Q t tr htr0 htr j₀ e S) q

end Work.DSM5c.Lp
