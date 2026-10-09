import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Lubin–Tate formal group law and its `𝒪`-module structure

This file fixes the vocabulary of the **Lubin–Tate formal group** over the ring of integers `R` of a
`p`-adic field, in Mathlib's language of formal group laws
(`Mathlib/RingTheory/FormalGroup/Basic.lean`: `FormalGroup R`, `FormalGroup.Point`, `𝔾ₐ`, `𝔾ₘ`,
`FormalGroup.map`).

For a complete discrete valuation ring `R` with uniformiser `π` and residue cardinality
`q = #(R/πR)`, the Lubin–Tate theorem (Serre, *Local Fields*, Ch. XV §3) provides a *commutative*
one-dimensional formal group law `F_π` over `R` with

* `F_π(X,Y) ≡ X + Y (mod deg 2)` — automatic for a formal group law,
* an endomorphism `[π]` with `[π](X) ≡ πX (mod deg 2)`, which is *unique* once the group law is
  fixed.

The theorem is usually stated as: *there exists a formal group law whose `π`-multiplication is
congruent to `πX` modulo degree two*; the formal group law is then unique
(Serre, *Local Fields*, Ch. XV §3, Thms. 3.1–3.3; Milne, *Class Field Theory*, §I.1).  The
`R`-module structure `R → End(F_π)`, `a ↦ [a]`, is the statement that the maximal ideal `𝔪_R`
becomes an `R`-module under the group law of `F_π` (the "Lubin–Tate module" of Milne, *op. cit.*).

## What is formalised here

* `NK.LocalReciprocityLubinTate.CongruentModDegTwo` — the congruence modulo total degree two,
  in which the Lubin–Tate conditions are expressed;
* `NK.LocalReciprocityLubinTate.LubinTateFormalGroupLaw R π q` — a commutative formal group law
  over `R` together with its `π`-multiplication series, subject to the Lubin–Tate conditions;
* `NK.LocalReciprocityLubinTate.LubinTateModule R π q` — a Lubin–Tate formal group law together
  with the ring homomorphism `R → End(F_π)` giving the `R`-module structure on the maximal ideal;
* `NK.LocalReciprocityLubinTate.LubinTateFormalGroupExists R π q` — the **existence theorem** of
  Lubin–Tate theory, as a named classical statement (`Prop`).

## What is *not* formalised here

The *torsion theory* of `F_π` — that the `π^n`-division points `F_π[π^n]`, realised in the maximal
ideal of the ring of integers of the algebraic closure of the fraction field of `R`, form a free
`R/π^n`-module of rank one, hence have cardinality `q^n` (Serre, *Local Fields*, Ch. XV §4, Thm. 4.1)
— requires Weierstrass preparation over the complete ring `R` and the evaluation of a formal power
series on an element of an infinite maximal ideal, neither of which is available in this workspace.
The *numerical* consequences of that torsion theory are, however, available through the Lubin–Tate
tower `NK.LocalReciprocityLubinTate.LubinTateTower`: the level `E_{0,n-1}` has degree
`(q-1)q^{n-1} = #F_π[π^n] - #F_π[π^{n-1}]` (`NK.LocalReciprocityLubinTate.finrank_level_of_tower_higherUnits`),
and with the norm residue symbol the level Galois group is `Fˣ ⧸ ⟨π⟩U^n`.
-/

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate

universe u

noncomputable section

/-- Two multivariable power series are **congruent modulo total degree two** if their coefficients in
total degree `< 2` agree — i.e. they have the same constant and the same linear terms.  This is the
"`≡` modulo `deg 2`" of the Lubin–Tate conditions: `F_π(X,Y) = X + Y + (deg ≥ 2 terms)` and
`[π](X) = πX + (deg ≥ 2 terms)`. -/
def CongruentModDegTwo {σ : Type*} {R : Type*} [CommSemiring R]
    (f g : MvPowerSeries σ R) : Prop :=
  ∀ s : σ →₀ ℕ, s.degree < 2 → MvPowerSeries.coeff s f = MvPowerSeries.coeff s g

theorem congruentModDegTwo_refl {σ : Type*} {R : Type*} [CommSemiring R] (f : MvPowerSeries σ R) :
    CongruentModDegTwo f f := fun _ _ => rfl

theorem congruentModDegTwo_symm {σ : Type*} {R : Type*} [CommSemiring R] {f g : MvPowerSeries σ R}
    (h : CongruentModDegTwo f g) : CongruentModDegTwo g f := fun s hs => (h s hs).symm

theorem congruentModDegTwo_trans {σ : Type*} {R : Type*} [CommSemiring R] {f g h : MvPowerSeries σ R}
    (hfg : CongruentModDegTwo f g) (hgh : CongruentModDegTwo g h) : CongruentModDegTwo f h :=
  fun s hs => (hfg s hs).trans (hgh s hs)

/-- **The Lubin–Tate formal group law** of a uniformiser `π` over a commutative ring `R`, with
residue cardinality `q`: a commutative formal group law together with its `π`-multiplication series
`[π]`, which is congruent to `πX` modulo degree two and is an endomorphism of the group law.

The existence of such a datum is the existence theorem of Lubin–Tate theory
(`LubinTateFormalGroupExists`); the *group law* is uniquely determined by it (Serre, *Local Fields*,
Ch. XV §3). -/
structure LubinTateFormalGroupLaw (R : Type u) [CommRing R] (π : R) (q : ℕ) where
  /-- the underlying one-dimensional formal group law over `R`. -/
  law : FormalGroup R
  /-- the formal group law is commutative (a Lubin–Tate group law always is). -/
  comm : law.IsComm
  /-- the `π`-multiplication series `[π](X)`, as a one-variable power series. -/
  piEndo : MvPowerSeries (Fin 1) R
  /-- `[π](0) = 0`. -/
  piEndo_zero : MvPowerSeries.constantCoeff piEndo = 0
  /-- the Lubin–Tate congruence `[π](X) ≡ πX (mod deg 2)`. -/
  piEndo_linear : CongruentModDegTwo piEndo (MvPowerSeries.C π * MvPowerSeries.X 0)
  /-- `[π]` is an endomorphism of the formal group law: `[π](F(X,Y)) = F([π](X),[π](Y))`. -/
  piEndo_endo : MvPowerSeries.subst ![(law : MvPowerSeries (Fin 2) R)] piEndo
      = MvPowerSeries.subst
          ![MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 2)] piEndo,
            MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 2)] piEndo]
          (law : MvPowerSeries (Fin 2) R)

/-- **The Lubin–Tate module structure**: a Lubin–Tate formal group law together with the ring
homomorphism `R → End(F_π)`, `a ↦ [a]` giving the classical `R`-module structure on the maximal
ideal `𝔪_R` (under the addition of `F_π`).

The classical statement is that such an `[a]` exists and is unique for every `a ∈ R`, that
`[ab] = [a]∘[b]`, `[a+b] = F_π([a],[b])`, and that `[a](X) ≡ aX (mod deg 2)` (Serre, *Local
Fields*, Ch. XV §3, Thms. 3.2–3.3; Milne, *Class Field Theory*, §I.1). -/
structure LubinTateModule (R : Type u) [CommRing R] (π : R) (q : ℕ) where
  /-- the underlying Lubin–Tate formal group law. -/
  toLaw : LubinTateFormalGroupLaw R π q
  /-- the `a`-multiplication series `[a](X)`, for `a ∈ R`. -/
  action : R → MvPowerSeries (Fin 1) R
  /-- `[1] = X`. -/
  action_one : action 1 = MvPowerSeries.X 0
  /-- `[a+b] = F_π([a],[b])`. -/
  action_add : ∀ a b : R, action (a + b)
      = MvPowerSeries.subst ![action a, action b] (toLaw.law : MvPowerSeries (Fin 2) R)
  /-- `[ab] = [a] ∘ [b]`. -/
  action_mul : ∀ a b : R, action (a * b) = MvPowerSeries.subst ![action b] (action a)
  /-- each `[a]` is an endomorphism of the formal group law. -/
  action_end : ∀ a : R,
    MvPowerSeries.subst ![(toLaw.law : MvPowerSeries (Fin 2) R)] (action a)
      = MvPowerSeries.subst
          ![MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 2)] (action a),
            MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 2)] (action a)]
          (toLaw.law : MvPowerSeries (Fin 2) R)
  /-- `[a](X) ≡ aX (mod deg 2)`. -/
  action_linear : ∀ a : R,
    CongruentModDegTwo (action a) (MvPowerSeries.C a * MvPowerSeries.X 0)
  /-- the `π`-multiplication of the group law is the `π`-th operation of the module structure. -/
  action_pi : action π = toLaw.piEndo

/-- **The existence theorem of Lubin–Tate theory** (Serre, *Local Fields*, Ch. XV §3, Thm. 3.1;
Milne, *Class Field Theory*, §I.1): for a complete discrete valuation ring `R` with uniformiser `π`
and finite residue field of cardinality `q`, there is a Lubin–Tate module over `R` for `π`.

This is a named classical statement of the chapter.  The *consequences* used by local class field
theory (the levels `F(π_n)`, their degrees and their norm groups) are packaged by
`NK.LocalReciprocityLubinTate.LubinTateTower`, and the reduction of the local reciprocity datum to
that tower is proved in this chapter — see `Submission/Work/LocalReciprocityLubinTate/README.md`. -/
def LubinTateFormalGroupExists (R : Type u) [CommRing R] (π : R) (q : ℕ) : Prop :=
  Nonempty (LubinTateModule R π q)

end

end NK.LocalReciprocityLubinTate
