/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — charts of the Jacobian drive: the Brill–Noether chart

This is the area `CH` of `NOTES_LEAD_jacobian_GC.md` §3.5.  It provides the *chart* of the
Jacobian construction of areas `GC` and `DS`: the open subscheme `V` of `Sym^g C` on which
the symmetric power is a torsor-like piece of `Pic⁰`, and the covering of `Pic⁰` by
translates of `V`.

## What is here

* `Sym C n` — the `n`-th symmetric power of `C`, i.e. area `SY`'s `SymGeom.S`;
* `divOf` — the divisor of a field point of `Sym^n C`;
* `pullK`, `iOf` — base change of a divisor along the structure map `K → F` and the index of
  speciality `i(D) = ℓ(W - D)` (RR5);
* `RochData` — the Riemann–Roch input of the area, in the form in which it is used (RR5 is
  built into `iOf`, so the input is the Riemann–Roch *equation* together with RR7);
* `BNData` — the Brill–Noether chart data: the canonical divisor `W`, the auxiliary place `Q`,
  the affine open `U ⊆ C`, a basis of `L(W)`, the affine chart `Sym^g(U)` of `Sym^g C` and
  the Brill–Noether determinant section `δ` on it;
* `BNData.V` — *the* chart `V = D(δ) ⊆ Sym^g C`, with `BNData.isAffineOpen_V` (`V` is affine),
  `BNData.ell_eq_one_of_landsIn` (points of `V` have `ℓ = 1`) and `BNData.i_eq_zero_iff`.

## The named inputs of this file

* `RochData C` — area `RR`: Riemann–Roch (with RR5 as the definition of `iOf`) and RR7;
* `SymProps C n` — area `SY`: `Sym^n C` is integral, geometrically irreducible, locally of
  finite type over `K` and quasi-compact;
* in `BNData`: the *construction* of the chart, i.e. the affine chart `Sym^g(U)` of `Sym^g C`
  together with the Brill–Noether section `δ = det(h_j(x_m))²` on it (area `SY`, §2 of the
  lead's notes, plus the evaluation-matrix computation of §3.5), the identification
  `D(δ) = {D : i(D) = 0}` (RR5 + that computation) and the non-emptiness of the chart (RR6/RR7).

Everything *derived* from these inputs is proved: see the end of this file.
-/
import Submission.Work.GCBasics.All
import Submission.Work.SpecLin.Interface
import Submission.Work.RiemannRoch.Linear.l_zero_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

open Work.CurveBasics

noncomputable section

variable {K : Type u} [Field K]

/-! ### Conventions -/

/-- The `n`-th symmetric power of a curve `C/K`: area `SY`'s `SymGeom.S`. -/
abbrev Sym (C : Curve K) [Work.SpecLin.DivBase C] (n : ℕ) [Work.SpecLin.SymGeom C n] :
    Work.GCBasics.Sch K :=
  Work.SpecLin.SymGeom.S (C := C) n

/-- The divisor of a field point of `Sym^n C` (area `SY`). -/
abbrev divOf {C : Curve K} [Work.SpecLin.DivBase C] {n : ℕ} [Work.SpecLin.SymGeom C n]
    {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt (Sym C n) F) :
    Work.GCBasics.Dv C F :=
  Work.SpecLin.SymGeom.divOf p

/-- Base change of a divisor along the structure map `K → F`. -/
def pullK (C : Curve K) [Work.SpecLin.DivBase C] (W : Work.GCBasics.Dv C K)
    {F : Type u} [Field F] [Algebra K F] : Work.GCBasics.Dv C F :=
  Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) W

/-- **The index of speciality**, in the form given by Riemann–Roch duality (RR5):
`i(D) = ℓ(W - D)` for a canonical divisor `W`. -/
def iOf (C : Curve K) [Work.SpecLin.DivBase C] (W : Work.GCBasics.Dv C K)
    {F : Type u} [Field F] [Algebra K F] (D : Work.GCBasics.Dv C F) : ℕ :=
  Work.GCBasics.ell C (pullK C W - D)

/-- `ℓ(0) = 1` (Riemann–Roch's normalisation, area `RR`'s `l 0 = 1`). -/
theorem ell_zero (C : Curve K) {F : Type u} [Field F] [Algebra K F] :
    Work.GCBasics.ell C (0 : Work.GCBasics.Dv C F) = 1 :=
  Work.RiemannRoch.Linear.l_zero_eq_one (C.baseChange F)

/-! ### The Riemann–Roch input (area RR) -/

/-- **The Riemann–Roch input of area `CH`** (area `RR`, named input).

It consists of a canonical divisor `W` (so that `i D = ℓ(W - D)` by definition, RR5), the
Riemann–Roch equation in the form
`ℓ(D) = deg D + 1 - g + i(D)`, and RR7 (`deg D ≥ g ⟹ ℓ(D) ≥ 1`). -/
structure RochData (C : Curve K) [Work.SpecLin.DivBase C] where
  /-- the genus of `C` -/
  g : ℕ
  /-- a canonical divisor -/
  W : Work.GCBasics.Dv C K
  /-- **Riemann–Roch**, with the index of speciality given by RR5 -/
  rr : ∀ {F : Type u} [Field F] [Algebra K F] (D : Work.GCBasics.Dv C F),
    (Work.GCBasics.ell C D : ℤ) =
      Work.GCBasics.Ddeg C F D + 1 - (g : ℤ) + (iOf C W D : ℤ)
  /-- **RR7**: a divisor of degree at least the genus has a nonzero section -/
  ell_pos_of_genus_le_deg : ∀ {F : Type u} [Field F] [Algebra K F]
    (D : Work.GCBasics.Dv C F), (g : ℤ) ≤ Work.GCBasics.Ddeg C F D → 1 ≤ Work.GCBasics.ell C D

namespace RochData

variable {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)

/-- `ℓ(W) = g`: the canonical divisor is maximally special (RR5 at `D = 0`, with RR). -/
theorem ell_canonical : ∀ {F : Type u} [Field F] [Algebra K F],
    Work.GCBasics.ell C (pullK C R.W : Work.GCBasics.Dv C F) = R.g := by
  intro F _ _
  have h := R.rr (0 : Work.GCBasics.Dv C F)
  rw [ell_zero C, map_zero] at h
  have h2 : (R.g : ℤ) = (iOf C R.W (0 : Work.GCBasics.Dv C F) : ℤ) := by omega
  have h3 : R.g = iOf C R.W (0 : Work.GCBasics.Dv C F) := by omega
  simpa [iOf, sub_zero] using h3.symm

/-- The Riemann–Roch equation, rearranged: `i(D) = ℓ(D) + g - 1 - deg D`. -/
theorem i_eq (F : Type u) [Field F] [Algebra K F] (D : Work.GCBasics.Dv C F) :
    (iOf C R.W D : ℤ) =
      (Work.GCBasics.ell C D : ℤ) + (R.g : ℤ) - 1 - Work.GCBasics.Ddeg C F D := by
  have h := R.rr D
  omega

/-- **RR7** in the vocabulary of this area. -/
theorem one_le_ell_of_genus_le_deg (F : Type u) [Field F] [Algebra K F]
    (D : Work.GCBasics.Dv C F) (h : (R.g : ℤ) ≤ Work.GCBasics.Ddeg C F D) :
    1 ≤ Work.GCBasics.ell C D :=
  R.ell_pos_of_genus_le_deg D h

/-- A degree-`g` divisor with `i(D) = 0` has `ℓ(D) = 1`: this is the numerical content of
"the points of the Brill–Noether chart are the non-special degree-`g` divisors". -/
theorem ell_eq_one_of_i_eq_zero {F : Type u} [Field F] [Algebra K F]
    {D : Work.GCBasics.Dv C F} (hdeg : Work.GCBasics.Ddeg C F D = (R.g : ℤ))
    (hi : iOf C R.W D = 0) : Work.GCBasics.ell C D = 1 := by
  have h := R.rr D
  rw [hdeg, hi] at h
  simp only [Nat.cast_zero, add_zero] at h
  omega

/-- For a degree-`g` divisor, `i(D) = 0` if and only if `ℓ(D) = 1`. -/
theorem i_eq_zero_iff_ell_eq_one {F : Type u} [Field F] [Algebra K F]
    {D : Work.GCBasics.Dv C F} (hdeg : Work.GCBasics.Ddeg C F D = (R.g : ℤ)) :
    iOf C R.W D = 0 ↔ Work.GCBasics.ell C D = 1 := by
  refine ⟨fun hi => R.ell_eq_one_of_i_eq_zero hdeg hi, fun hℓ => ?_⟩
  have h := R.rr D
  rw [hℓ, hdeg] at h
  omega

/-- A degree-`g` divisor with `ℓ(D) = 1` is the *unique* effective divisor of degree `g` in
its linear equivalence class (given `ℓ(0) = 1`). -/
theorem eq_of_ell_eq_one {F : Type u} [Field F] [Algebra K F]
    {D D' : Work.GCBasics.Dv C F} (hD : D.IsEffective) (hD' : D'.IsEffective)
    (_hdeg : Work.GCBasics.Ddeg C F D = (R.g : ℤ))
    (hℓ : Work.GCBasics.ell C D = 1) (he : Work.GCBasics.LinEquiv C D D') : D = D' :=
  (Work.GCBasics.ell_eq_one_iff hD (ell_zero C)).mp hℓ D' hD' he

end RochData

/-- The degree of the divisor of a point of `Sym^g C` is `g`.

This is `SymGeom.divOf_deg` restated for the abbreviation `Ddeg`; the restatement matters
because `Ddeg` is an abbreviation for `(C.baseChange F).degHom` while `SymGeom.divOf_deg` is
phrased with `(C.baseChange F).deg`, and the two are only *definitionally* equal (a plain `def`
is not unfolded by `rw`/`simp` matching). -/
theorem Ddeg_divOf {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {F : Type u} [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt (Sym C R.g) F) :
    Work.GCBasics.Ddeg C F (divOf p) = (R.g : ℤ) :=
  Work.SpecLin.SymGeom.divOf_deg p

/-- The degree is additive, restated for the abbreviation `Ddeg` (see `Ddeg_divOf`). -/
theorem Ddeg_add {C : Curve K} [Work.SpecLin.DivBase C] {F : Type u} [Field F] [Algebra K F]
    (D D' : Work.GCBasics.Dv C F) :
    Work.GCBasics.Ddeg C F (D + D') = Work.GCBasics.Ddeg C F D + Work.GCBasics.Ddeg C F D' :=
  map_add _ _ _

/-- The degree is additive in the negative direction, restated for `Ddeg`. -/
theorem Ddeg_sub {C : Curve K} [Work.SpecLin.DivBase C] {F : Type u} [Field F] [Algebra K F]
    (D D' : Work.GCBasics.Dv C F) :
    Work.GCBasics.Ddeg C F (D - D') = Work.GCBasics.Ddeg C F D - Work.GCBasics.Ddeg C F D' :=
  map_sub _ _ _

/-- The degree is homogeneous, restated for `Ddeg`. -/
theorem Ddeg_smul {C : Curve K} [Work.SpecLin.DivBase C] {F : Type u} [Field F] [Algebra K F]
    (n : ℤ) (D : Work.GCBasics.Dv C F) :
    Work.GCBasics.Ddeg C F (n • D) = n * Work.GCBasics.Ddeg C F D := by
  simpa [Work.GCBasics.Ddeg, zsmul_eq_mul] using map_zsmul (C.baseChange F).degHom n D

/-- The degree is invariant under base change of the field of definition, restated for `Ddeg`. -/
theorem Ddeg_bc {C : Curve K} [Work.SpecLin.DivBase C] {F F' : Type u} [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F') (D : Work.GCBasics.Dv C F) :
    Work.GCBasics.Ddeg C F' (Work.SpecLin.DivBase.bc e D) = Work.GCBasics.Ddeg C F D :=
  Work.SpecLin.DivBase.deg_bc e D

/-- The degree of `divOf p - divOf q` is zero: this is the reason the chart relation
`InChart` of area `CH` is about degree-zero classes. -/
theorem Ddeg_divOf_sub {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {F : Type u} [Field F] [Algebra K F]
    (p q : Work.GCBasics.FPt (Sym C R.g) F) :
    Work.GCBasics.Ddeg C F (divOf p - divOf q) = 0 := by
  rw [map_sub, Ddeg_divOf p, Ddeg_divOf q, sub_self]

/-! ### The scheme-theoretic properties of the symmetric power (area SY) -/

/-- **Area `SY`, named input**: the scheme-theoretic properties of the symmetric power
`Sym^n C` that area `CH` consumes, beyond `SymGeom`: integrality (used for the generic point),
geometric irreducibility (used by area `GC` for the Jacobian), local finiteness of type and
quasi-compactness. -/
class SymProps (C : Curve K) [Work.SpecLin.DivBase C] (n : ℕ)
    [Work.SpecLin.SymGeom C n] where
  isIntegral : IsIntegral (Sym C n).left
  geometricallyIrreducible : GeometricallyIrreducible (Sym C n).hom
  locallyOfFiniteType : LocallyOfFiniteType (Sym C n).hom
  quasiCompact : QuasiCompact (Sym C n).hom

instance instIsIntegralOfSymProps (C : Curve K) [Work.SpecLin.DivBase C] (n : ℕ)
    [Work.SpecLin.SymGeom C n] [SymProps C n] : IsIntegral (Sym C n).left :=
  SymProps.isIntegral

/-! ### Consequences of `SymProps` -/

section SymPropsInstances

variable (C : Curve K) [Work.SpecLin.DivBase C] (n : ℕ) [Work.SpecLin.SymGeom C n]

/-- `Sym^n C` is reduced, from area `SY`'s input that it is integral. -/
instance instIsReducedOfSymProps [h : SymProps C n] : IsReduced (Sym C n).left :=
  isReduced_of_isIntegral (X := (Sym C n).left)

/-- `Sym^n C` is irreducible, from area `SY`'s input that it is integral. -/
instance instIrreducibleSpaceOfSymProps [h : SymProps C n] : IrreducibleSpace (Sym C n).left :=
  irreducibleSpace_of_isIntegral (X := (Sym C n).left)

/-- `Sym^n C` is separated over `K`. -/
instance instIsSeparatedOfSymProps [SymProps C n] : IsSeparated (Sym C n).hom :=
  (Work.SpecLin.SymGeom.isProper (C := C) (n := n)).toIsSeparated

end SymPropsInstances

/-! ### The Brill–Noether chart -/

/-- **The Brill–Noether chart data** of a curve `C/K` (§3.5 of the lead's design).

Besides the book-keeping data (`Q`, `U`, the basis `h` of `L(W)`) it contains

* the affine chart `chart = Sym^g(U)` of `Sym^g C` and the *Brill–Noether section*
  `δ = det (h_j(x_m))²` on it, and
* the two facts about `δ` that make the chart work: a point lands in `D(δ)` exactly when the
  associated degree-`g` divisor is non-special (`i = 0`, i.e. `ℓ = 1`), and `D(δ)` is nonempty.

The first of these is the content of the evaluation-matrix computation: for `p` with
`divOf p = Σ_m [x_m]` over an algebraically closed extension, `δ(p) = det (h_j(x_m))²`
vanishes if and only if there is a nonzero `h ∈ L(W)` vanishing on all the `x_m`, i.e.
`L(W - divOf p) ≠ 0`; RR5 turns this into `i(divOf p) ≠ 0`. -/
structure BNData (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] where
  /-- an auxiliary place, used to make the chart affine (RR3/RR4, CB7) -/
  Q : C.Place
  /-- the affine open of `C` on which the chart is taken -/
  U : C.left.Opens
  hU : IsAffineOpen U
  /-- the basis of `L(W)` used to build the Brill–Noether determinant -/
  h : Fin R.g → (C.baseChange K).functionField
  /-- the `h j` lie in `L(W)` -/
  h_mem : ∀ j, 0 ≤ (C.baseChange K).div (h j) + R.W
  /-- the `h j` span `L(W)` -/
  h_span : (C.baseChange K).L R.W = Submodule.span K (Set.range h)
  /-- the affine chart `Sym^g(U)` of `Sym^g C` -/
  chart : (Sym C R.g).left.Opens
  hChart : IsAffineOpen chart
  /-- the Brill–Noether determinant section `det (h_j(x_m))²` on the chart -/
  δ : Γ((Sym C R.g).left, chart)
  /-- **The defining property of the Brill–Noether chart**, in the direction in which it is
  true and used: a point of `D(δ)` has `i (divOf p) = 0`, i.e. `ℓ (divOf p) = 1`.

  The *converse* is **false** in general: the chart `D(δ)` is contained in the affine chart
  `Sym^g(U)` with `U = C ∖ ({Q} ∪ supp W)`, while there are degree-`g` divisors of `ℓ = 1` whose
  support meets `supp W` (e.g. on a genus-`2` curve `C` with canonical divisor `W = [a] + [b]`,
  the divisor `[b] + [P]` with `P ∉ {a,b}` has `a i = ℓ(W - [b] - [P]) = ℓ([a] - [P]) = 0`, but
  it is not supported in `U`).  Consumers must therefore use `ℓ = 1` on the chart, and never
  the converse. -/
  i_eq_zero_of_landsIn : ∀ {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt (Sym C R.g) F),
    p.LandsIn ((Sym C R.g).left.basicOpen δ) → iOf C R.W (divOf p) = 0
  /-- the chart is nonempty (RR6/RR7: the generic point of `Sym^g C` lies in `V`) -/
  ne_bot : (Sym C R.g).left.basicOpen δ ≠ ⊥

namespace BNData

variable {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] (d : BNData C R)

/-- **The Brill–Noether chart** `V = D(δ) ⊆ Sym^g C`. -/
def V : (Sym C R.g).left.Opens := (Sym C R.g).left.basicOpen d.δ

/-- The chart is contained in the affine chart `Sym^g(U)` on which `δ` is defined. -/
theorem V_le_chart : d.V ≤ d.chart := Scheme.basicOpen_le _ _

/-- **The chart `V` is affine** (it is a basic open of the affine chart `Sym^g(U)`). -/
theorem isAffineOpen_V : IsAffineOpen d.V := d.hChart.basicOpen d.δ

/-- The chart is nonempty. -/
theorem V_ne_bot : d.V ≠ ⊥ := d.ne_bot

/-- **The points of the chart have `ℓ = 1`**: the key property of the Brill–Noether chart. -/
theorem ell_eq_one_of_landsIn {F : Type u} [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt (Sym C R.g) F) (hp : p.LandsIn d.V) :
    Work.GCBasics.ell C (divOf p) = 1 :=
  R.ell_eq_one_of_i_eq_zero (Work.SpecLin.SymGeom.divOf_deg p) (d.i_eq_zero_of_landsIn p hp)

/-- The chart is contained in the `i = 0` locus: a point of `Sym^g C` landing in `V` has
`i = 0`.  (The converse is false; see the field `BNData.i_eq_zero_of_landsIn`.) -/
theorem i_eq_zero_of_landsIn' {F : Type u} [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt (Sym C R.g) F) (hp : p.LandsIn d.V) :
    iOf C R.W (divOf p) = 0 := d.i_eq_zero_of_landsIn p hp

/-- A point of the chart is the *unique* effective divisor of degree `g` in its class: this is
what makes the chart inject into `Pic⁰` (area `GC`'s `cls`). -/
theorem eq_of_landsIn_of_linEquiv {F : Type u} [Field F] [Algebra K F]
    (p q : Work.GCBasics.FPt (Sym C R.g) F) (hp : p.LandsIn d.V)
    (h : Work.GCBasics.LinEquiv C (divOf p) (divOf q)) : p = q :=
  Work.SpecLin.SymGeom.divOf_injective p q
    (R.eq_of_ell_eq_one (Work.SpecLin.SymGeom.divOf_isEffective p)
      (Work.SpecLin.SymGeom.divOf_isEffective q) (Work.SpecLin.SymGeom.divOf_deg p)
      (d.ell_eq_one_of_landsIn p hp) h)

/-- The generic point of `Sym^g C` lies in the chart, as a point over the function field of
`Sym^g C`.  (RR6: `i(D_gen) = 0`.) -/
theorem genericFPt_landsIn_V [IsIntegral (Sym C R.g).left] :
    (Work.GCBasics.genericFPt (Sym C R.g)).LandsIn d.V := by
  refine (Work.GCBasics.genericFPt_landsIn_iff (Sym C R.g) d.V).mpr ?_
  have hne : (d.V : Set (Sym C R.g).left).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    exact d.V_ne_bot (TopologicalSpace.Opens.ext (by rw [hc]; rfl))
  obtain ⟨x, hx⟩ := hne
  exact (genericPoint_specializes x).mem_open d.V.2 hx

end BNData

end

end Work.Charts
