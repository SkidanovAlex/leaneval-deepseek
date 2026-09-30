/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — the covering of `Pic⁰` by translates of the Brill–Noether chart

This file contains the second half of `NOTES_LEAD_jacobian_GC.md` §3.5: the covering `COV` of
the degree-zero Picard group by translates of the chart `V`, and its Galois-equivariant
refinement `COV′` over a finite Galois extension `k'/k`.

## The chart relation

`InChart d E c` (`E` a point of `Sym^g C`, `c : Pic⁰(C_F)`) says that `c` has a representative
`divOf y - divOf E` with `y` a point of the chart `V`.  Because the points of `V` have `ℓ = 1`,
they are the *unique* effective representatives of their classes (see
`BNData.eq_of_landsIn_of_linEquiv`), so `InChart d E c` *determines* the point `y`
(`InChart.unique` below): the charts are honest coordinate charts.

## Contents

* `chartClass` and its API (`chartClass_self`, `chartClass_add`, `chartClass_eq_iff`, …) — the
  class of the difference of two points of `Sym^g C`;
* `InChart`, with `InChart.unique`, `InChart.add_centre` (changing the centre translates the
  class — this is the transition map `σ_ij` of area `GC`) and `InChart.congr_divOf`;
* `Charts` — the covering data consumed by area `GC`: a finite family of centres whose chart
  translates cover every degree-zero class over every field extension;
* `GalCharts` — the Galois-equivariant refinement consumed by area `DS`: a finite Galois
  extension `k'/k`, a finite `Γ = Gal(k'/k)`-set of centres such that every class over every
  `k`-algebra receiving `k'` is covered by a whole `Γ`-orbit of centres;
* the named inputs `HasCharts` (COV), `HasGalCharts` (COV′) and `HasChartBaseChange` with the
  corresponding theorems `exists_charts`, `exists_galCharts`.

The named inputs are exactly the two sides of `COV`: existence of the covering is the
*dominance of the translations* `T_c` plus density of separable points and Noetherian
approximation (see `Submission/Work/Charts/Density.lean`), and the passage from `COV′` over
`k'` to a covering for the `k'`-curve `C_{k'}` is the base change of the symmetric power
(`Sym.baseChangeIso`) together with `V_baseChange`.
-/
import Submission.Work.Charts.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-! ### The class of a difference of two points of `Sym^g C` -/

/-- The class of `divOf p - divOf q` in `Pic⁰(C_F)`.  All the chart data of the Jacobian
construction is expressed through this class map. -/
abbrev chartClass {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {F : Type u} [Field F] [Algebra K F]
    (p q : FPt (Sym C R.g) F) : Pic0 C F :=
  Pic0.mk (divOf p - divOf q) (Ddeg_divOf_sub p q)

namespace chartClass

variable {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {F : Type u} [Field F] [Algebra K F]

/-- Equality of the classes of two differences is linear equivalence of the differences. -/
theorem eq_iff (p q p' q' : FPt (Sym C R.g) F) :
    chartClass p q = chartClass p' q' ↔
      LinEquiv C (divOf p - divOf q) (divOf p' - divOf q') :=
  Pic0.mk_eq_iff (Ddeg_divOf_sub p q) (Ddeg_divOf_sub p' q')

/-- A class of a difference is zero exactly when the two divisors are linearly equivalent. -/
theorem eq_zero_iff (p q : FPt (Sym C R.g) F) :
    chartClass p q = 0 ↔ LinEquiv C (divOf p) (divOf q) := by
  rw [show (0 : Pic0 C F) = Pic0.mk (0 : Dv C F) (by simp) from (Pic0.mk_zero).symm]
  refine (Pic0.mk_eq_iff (D := divOf p - divOf q) (D' := (0 : Dv C F))
    (Ddeg_divOf_sub p q) (by simp)).trans ?_
  exact Work.GCBasics.linEquiv_sub_zero_iff (divOf p) (divOf q)

/-- The class of the difference of a point with itself is zero. -/
theorem refl (p : FPt (Sym C R.g) F) : chartClass p p = 0 :=
  (eq_zero_iff p p).mpr (LinEquiv.refl (divOf p))

/-- **Additivity**: `[p - q] + [q - r] = [p - r]`. -/
theorem add (p q r : FPt (Sym C R.g) F) :
    chartClass p q + chartClass q r = chartClass p r := by
  change Pic0.mkHom C F ⟨divOf p - divOf q, Ddeg_divOf_sub p q⟩ +
      Pic0.mkHom C F ⟨divOf q - divOf r, Ddeg_divOf_sub q r⟩ =
    Pic0.mkHom C F ⟨divOf p - divOf r, Ddeg_divOf_sub p r⟩
  rw [← map_add]
  congr 1
  ext
  simp only [AddSubgroup.coe_add, Subtype.coe_mk]
  abel

/-- Reversing the order negates the class. -/
theorem neg (p q : FPt (Sym C R.g) F) : chartClass q p = -chartClass p q := by
  have h : chartClass p q + chartClass q p = 0 := by rw [add p q p, refl]
  exact eq_neg_of_add_eq_zero_right h

end chartClass

/-! ### The chart relation -/

/-- **`c` lies in the chart of `E`.**  `E` is a degree-`g` divisor (a point of `Sym^g C`) and
`c` a degree-zero class over `F`; `InChart d E c` says that `c` has a representative
`divOf y - divOf E` with `y` a point of the Brill–Noether chart `V ⊆ Sym^g C`.

This is the relation whose transitions along overlaps give the gluing of area `GC`; the finite
family of centres `E_i` of `Charts` below makes it a covering. -/
def InChart {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] (d : BNData C R)
    {F : Type u} [Field F] [Algebra K F] (E : FPt (Sym C R.g) F) (c : Pic0 C F) : Prop :=
  ∃ y : FPt (Sym C R.g) F, y.LandsIn d.V ∧ chartClass y E = c

namespace InChart

variable {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {d : BNData C R}
    {F : Type u} [Field F] [Algebra K F]

/-- **The chart of `E` is a coordinate chart**: the map `y ↦ [divOf y - divOf E]` is injective
on the points of `V`.  Two points of the chart with the same class are equal, because the points
of `V` are the unique effective degree-`g` representatives of their classes
(`BNData.eq_of_landsIn_of_linEquiv`). -/
theorem eq_of_chartClass_eq {E y y' : FPt (Sym C R.g) F} (hy : y.LandsIn d.V)
    (hy' : y'.LandsIn d.V) (h : chartClass y E = chartClass y' E) : y = y' :=
  d.eq_of_landsIn_of_linEquiv y y' hy
    ((LinEquiv.sub_iff (divOf y) (divOf y') (divOf E)).mp ((chartClass.eq_iff y E y' E).mp h))

/-- The chart of `E` is inhabited by the classes of the points of `V` relative to `E`. -/
theorem of_landsIn {E y : FPt (Sym C R.g) F} (hy : y.LandsIn d.V) :
    InChart d E (chartClass y E) :=
  ⟨y, hy, rfl⟩

/-- **Changing the centre translates the class** (the transition map `σ_ij` of area `GC`):
`c` is in the chart of `E` iff `c + [E - E']` is in the chart of `E'`. -/
theorem add_centre {E E' : FPt (Sym C R.g) F} {c : Pic0 C F} :
    InChart d E c ↔ InChart d E' (c + chartClass E E') := by
  constructor
  · rintro ⟨y, hy, hyc⟩
    exact ⟨y, hy, by rw [← chartClass.add y E E', hyc]⟩
  · rintro ⟨y, hy, hyc⟩
    refine ⟨y, hy, ?_⟩
    rw [← chartClass.add y E' E, hyc, chartClass.neg E E']
    abel

/-- The chart relation only depends on the divisor of the centre. -/
theorem congr_divOf {E E' : FPt (Sym C R.g) F} (h : divOf E = divOf E') {c : Pic0 C F} :
    InChart d E c ↔ InChart d E' c := by
  have hEE : E = E' := Work.SpecLin.SymGeom.divOf_injective E E' h
  rw [hEE]

/-- A point of the chart lies in its own chart, at the zero class. -/
theorem self_zero {E : FPt (Sym C R.g) F} (hE : E.LandsIn d.V) : InChart d E 0 :=
  ⟨E, hE, chartClass.refl E⟩

end InChart

/-! ### The covering (COV) -/

/-- **COV.**  A finite family of centres `E i ∈ Sym^g C(K)` whose chart translates cover every
degree-zero class of `C` over every field extension of `K`.

This is the covering data consumed by area `GC`: the charts of the Jacobian are the translates
of the single Brill–Noether chart `V`, and `cov` says that they cover `Pic⁰`. -/
structure Charts (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (P0 : 𝟙_ (Sch K) ⟶ C.toOver) where
  /-- the Brill–Noether chart -/
  d : BNData C R
  /-- the index set of centres -/
  ι : Type u
  [fintype : Fintype ι]
  /-- the centres -/
  E : ι → FPt (Sym C R.g) K
  /-- every degree-zero class over every field extension is in one of the charts -/
  cov : ∀ {F : Type u} [Field F] [Algebra K F] (c : Pic0 C F),
    ∃ i, InChart d (RPt.map (IsScalarTower.toAlgHom K K F) (E i)) c

namespace Charts

variable {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {P0 : 𝟙_ (Sch K) ⟶ C.toOver} (D : Charts C R P0)

/-- The chart condition of `Charts`, unwound: every class is represented in one of the charts
by a point of `V`. -/
theorem exists_landsIn {F : Type u} [Field F] [Algebra K F] (c : Pic0 C F) :
    ∃ i, ∃ y : FPt (Sym C R.g) F, y.LandsIn D.d.V ∧
      chartClass y (RPt.map (IsScalarTower.toAlgHom K K F) (D.E i)) = c :=
  D.cov c

/-- The same, stated as a *function* from classes to the covering index: this is the datum
area `GC` uses to define the chart maps. -/
theorem exists_chart_of (F : Type u) [Field F] [Algebra K F] (c : Pic0 C F) :
    ∃ i : D.ι, InChart D.d (RPt.map (IsScalarTower.toAlgHom K K F) (D.E i)) c :=
  D.cov c

end Charts

/-! ### The Galois-equivariant covering (COV′) -/

/-- **COV′.**  The Galois-equivariant refinement of the covering, over a finite Galois
extension `k'/k`.  It is the covering data consumed by area `DS`.

The centres `E i` are `k'`-points of `Sym^g_k`; the group `Γ = k' ≃ₐ[k] k'` permutes the index
set (`act`) consistently with its action on the centres (`E_act`), and every class over every
`k`-algebra `F` receiving a `k`-embedding of `k'` is covered by an *entire* `Γ`-orbit of
centres (`orbit_cov`).  The last condition makes the charts `Γ`-stable after descent, which is
what effective Galois descent (`DS`) needs. -/
structure GalCharts (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (P0 : 𝟙_ (Sch K) ⟶ C.toOver) where
  /-- the finite Galois extension over which the centres are defined -/
  k' : Type u
  [field' : Field k']
  [algebra' : Algebra K k']
  [galois : IsGalois K k']
  [finiteDimensional : FiniteDimensional K k']
  /-- the Brill–Noether chart (over the base field `K`) -/
  d : BNData C R
  /-- the index set of centres -/
  ι : Type u
  [fintype : Fintype ι]
  /-- the centres: `k'`-points of `Sym^g_K` -/
  E : ι → FPt (Sym C R.g) k'
  /-- the Galois action on the index set -/
  act : (k' ≃ₐ[K] k') →* Equiv.Perm ι
  /-- the action on the index set matches the action on the centres: the conjugate `σ • E i`
  of a centre is `Spec.map σ ≫ E i`.

  **Warning (convention).**  The lead's notes write `(E i).map σ.symm.toAlgHom` here.  That
  convention is *inconsistent* with `act` being a group homomorphism: the map
  `σ ↦ (E ↦ (E).map σ.symm)` is an **anti**-homomorphism of groups (`(σ₁σ₂).symm = σ₂.symm *
  σ₁.symm`), whereas `σ ↦ (E ↦ (E).map σ.toAlgHom)` is a homomorphism.  Hence, with the
  `σ.symm` convention, `E_act` would force `Φ(σ₁σ₂) = Φ(σ₂σ₁)` on the centres, i.e. it could
  hold only for abelian `k' ≃ₐ[K] k'`.  We use the correct convention `map σ.toAlgHom`; the
  *orbit* of a centre — which is all that area `DS` uses — is the same either way. -/
  E_act : ∀ σ i, E (act σ i) = RPt.map σ.toAlgHom (E i)
  /-- every class over a `K`-algebra receiving `k'` is covered by a full `Γ`-orbit -/
  orbit_cov : ∀ {F : Type u} [Field F] [Algebra K F] (ε : k' →ₐ[K] F) (c : Pic0 C F),
    ∃ i, ∀ σ, InChart d (RPt.map ε (E (act σ i))) c

namespace GalCharts

variable {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {P0 : 𝟙_ (Sch K) ⟶ C.toOver} (D : GalCharts C R P0)

/-- The instance fields of a `GalCharts` are available by typeclass search on `D.k'`. -/
instance (D : GalCharts C R P0) : Field D.k' := D.field'

instance (D : GalCharts C R P0) : Algebra K D.k' := D.algebra'

instance (D : GalCharts C R P0) : IsGalois K D.k' := D.galois

instance (D : GalCharts C R P0) : FiniteDimensional K D.k' := D.finiteDimensional

/-- COV′ gives, a fortiori, a covering by single centres: this is the form it takes over a
field of definition containing `k'`. -/
theorem exists_inChart {F : Type u} [Field F] [Algebra K F] (ε : D.k' →ₐ[K] F)
    (c : Pic0 C F) : ∃ i, InChart D.d (RPt.map ε (D.E i)) c := by
  obtain ⟨i, hi⟩ := D.orbit_cov ε c
  exact ⟨i, by simpa using hi 1⟩

/-- The orbit of a centre is `Γ`-stable, expressed on the level of points: this is the
`Γ`-stability of the charts used by area `DS` for the effective descent. -/
theorem orbit_stable (i : D.ι) :
    Set.range (fun σ : D.k' ≃ₐ[K] D.k' => D.E (D.act σ i)) =
      Set.range (fun σ : D.k' ≃ₐ[K] D.k' => RPt.map σ.toAlgHom (D.E i)) := by
  have hf : (fun σ : D.k' ≃ₐ[K] D.k' => D.E (D.act σ i)) =
      (fun σ : D.k' ≃ₐ[K] D.k' => RPt.map σ.toAlgHom (D.E i)) := by
    funext σ
    exact D.E_act σ i
  rw [hf]

end GalCharts

/-! ### Named inputs of the covering -/

/-- **Area `CH`, named input: COV.**  Every curve over a field carries a covering of `Pic⁰` by
finitely many translates of its Brill–Noether chart.

This is the content of steps 1–4 of §3.5: the translations `T_c` are dominant (RESID/DOM,
area `DM`), `k^s`-points are dense (`Density.lean`), and a Noetherian approximation moves the
chart data down to a finite extension. -/
class HasCharts (K : Type u) [Field K] : Prop where
  /-- COV -/
  exists_charts : ∀ (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (P0 : 𝟙_ (Sch K) ⟶ C.toOver), Nonempty (Charts C R P0)

/-- **Area `CH`, named input: COV′.**  Over a finite Galois extension the covering can be taken
`Γ`-stable, i.e. closed under the Galois action on the centres.

This is step 5 of §3.5: finitely many centres are defined over a finite extension, and their
conjugates can be met in a single `Γ`-orbit. -/
class HasGalCharts (K : Type u) [Field K] : Prop where
  /-- COV′ -/
  exists_galCharts : ∀ (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (P0 : 𝟙_ (Sch K) ⟶ C.toOver), Nonempty (GalCharts C R P0)

/-- **Area `CH`, named input: base change of the covering.**  The covering over `k'` of the
curve `C_{k'}`, obtained from a `GalCharts` by base changing the symmetric power
(`Sym.baseChangeIso`) and the chart `V` (`V_baseChange`).

This is what area `DS` consumes: it builds the Jacobian over `k'` and descends. -/
class HasChartBaseChange (K : Type u) [Field K] : Prop where
  /-- the base-changed covering -/
  charts_of_galCharts : ∀ {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {P0 : 𝟙_ (Sch K) ⟶ C.toOver} (D : GalCharts C R P0),
    ∃ (db : Work.SpecLin.DivBase (C.baseChange D.k')), letI := db
      ∃ (R' : RochData (C.baseChange D.k'))
        (h : Work.SpecLin.SymGeom (C.baseChange D.k') R'.g)
        (P0' : 𝟙_ (Sch D.k') ⟶ (C.baseChange D.k').toOver),
        Nonempty (@Charts D.k' _ (C.baseChange D.k') db R' h P0')

/-- **COV** as a theorem: the covering of `Pic⁰` by finitely many translates of the
Brill–Noether chart. -/
theorem exists_charts [HasCharts K] (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (P0 : 𝟙_ (Sch K) ⟶ C.toOver) :
    Nonempty (Charts C R P0) :=
  HasCharts.exists_charts C R P0

/-- **COV′** as a theorem: the Galois-stable covering over a finite Galois extension.

**RETIRED.**  The class `HasGalCharts` is a named input of the *old* design; COV′ is now proved
from the named inputs of areas `SY`/`DM`/`NM` by route B
(`Submission/Work/NOTES_LEAD_jacobian_charts3.md` §1–§4): see
`Work.Charts.exists_galCharts_of_inputs`.  This theorem is kept only for compatibility; its
hypothesis `HasGalCharts K` is not known to be satisfiable and nothing should consume it. -/
theorem exists_galCharts_of_hasGalCharts [HasGalCharts K] (C : Curve K)
    [Work.SpecLin.DivBase C] (R : RochData C) [Work.SpecLin.SymGeom C R.g]
    (P0 : 𝟙_ (Sch K) ⟶ C.toOver) : Nonempty (GalCharts C R P0) :=
  HasGalCharts.exists_galCharts C R P0

end

end Work.Charts
