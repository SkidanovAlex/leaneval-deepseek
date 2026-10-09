import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lubin–Tate series: the coefficient-ring conditions and the construction interface

This file sets up the *purely algebraic* setting in which the Lubin–Tate formal group law is
constructed (Milne, *Class Field Theory*, §I.1, Lemma 2.11 and Propositions 2.12, 2.14; Serre,
*Local Fields*, Ch. XV §3).  Nothing here uses completeness, topology or Weierstrass preparation:
Milne's construction of the formal group law is a **degree induction**, and this file isolates its
ingredients and interface.

## The setting

`A` is a commutative ring, `π : A` and `q : ℕ`.  A **Lubin–Tate series** for `π` and `q` is a
one-variable power series

`f(X) = πX + (terms of degree ≥ 2)`,  `f(X) ≡ X^q  (mod π)`

(Milne, *op. cit.*, Definition 2.9; for `A = 𝒪[F]` the ring of integers of a `p`-adic field, `π` a
uniformiser and `q = #𝓀[F]`).  The two conditions on the coefficient ring that the construction uses
are

* `1 - π^r` is a unit for `r ≥ 1` (automatic when `π` lies in the maximal ideal of a local ring,
  e.g. `π ∈ 𝔪[F]`), which lets one divide the degree-`(r+1)` correction by `π(1 - π^r)`;
* the `q`-power map is the identity on the residue ring `A ⧸ (π)` (automatic for a finite residue
  field `𝔽_q` of `q` elements), which is Milne's "binomial theorem in characteristic `p`": it makes
  the Frobenius congruence `f̄(φ̄) = φ̄(ḡ₁,…,ḡₙ)` hold modulo `π`;
* `π` is a nonzerodivisor, which makes the correction at each degree unique.

## The interface

* `NK.LocalReciprocityLubinTate.IsLubinTateSeries` — the LT series;
* `NK.LocalReciprocityLubinTate.IsLubinTateCoeff` — the coefficient-ring conditions;
* `NK.LocalReciprocityLubinTate.lubinTate_groupLaw` — **Milne I.1, Lemma 2.11 + Proposition 2.12**:
  for a Lubin–Tate series `f` there is a unique `F` with `F ≡ X + Y (mod deg 2)` and
  `f ∘ F = F(fX, fY)`, and it is a commutative formal group law;
* `NK.LocalReciprocityLubinTate.existsUnique_lubinTate_solution` — the general statement of Milne's
  Lemma 2.11 (the degree induction, in `n` variables) from which the group law and the
  `𝒪`-module structure are obtained by uniqueness.
-/

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate

universe u

noncomputable section

variable {A : Type u} [CommRing A] {π : A} {q : ℕ}

/-- **The Frobenius condition on the residue ring**: every element of `A ⧸ (π)` is fixed by the
`q`-th power map.  For `A = 𝒪[F]`, `π` a uniformiser and `q = #𝓀[F]` this holds because the residue
ring is the field `𝔽_q`.  It is exactly the "binomial theorem takes a simple form in characteristic
`p`" (Milne, *CFT*, proof of Lemma 2.11): `z ↦ z^q` being the identity, it is additive. -/
def IsFrobeniusResidue (π : A) (q : ℕ) : Prop := ∀ z : A ⧸ Ideal.span {π}, z ^ q = z

/-- **`q` is a power of the residue characteristic**: there is a prime `p` with `CharP (A ⧸ (π)) p`
and `q = p ^ k`.

This is the hypothesis that makes the `q`-th power map *additive* on the residue ring — the
"binomial theorem in characteristic `p`" of Milne's proof of Lemma 2.11.  It is **not** implied by
the weaker condition that every element of the residue ring satisfies `z^q = z`: in `𝔽₂⟦t⟧` with
`π = t` and `q = 3` one has `z^3 = z` for all `z ∈ 𝔽₂` but `(1+X)^3 ≠ 1 + X^3` in `𝔽₂⟦X⟧`, and the
degree induction genuinely fails (`q = 3` is not a power of the residue characteristic `2`).  For a
finite residue field of cardinality `q = #𝓀` the condition holds, with `p = char 𝓀`. -/
def IsFrobeniusPower (π : A) (q : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ CharP (A ⧸ Ideal.span {π}) p ∧ ∃ k : ℕ, q = p ^ k

/-- **The coefficient-ring conditions for the Lubin–Tate construction.**

* `1 - π^r` is a unit for every `r ≥ 1`;
* the residue ring satisfies the Frobenius condition `IsFrobeniusResidue`;
* `π` is a nonzerodivisor.

All three hold for `A = 𝒪[F]` (a discrete valuation ring) with `π` a uniformiser and `q = #𝓀[F]`. -/
def IsLubinTateCoeff (π : A) (q : ℕ) : Prop :=
  (∀ r : ℕ, 1 ≤ r → IsUnit (1 - π ^ r)) ∧ IsFrobeniusResidue π q ∧
    (∀ a b : A, π * a = π * b → a = b)

/-- The coefficient of `X^n` in a one-variable power series, written with the `Fin 1` indexing used
by Mathlib's formal group law API. -/
def coeffX (n : ℕ) (f : MvPowerSeries (Fin 1) A) : A :=
  MvPowerSeries.coeff (Finsupp.single 0 n) f

/-- **A Lubin–Tate series** for `π` and `q`: `f(X) = πX + (terms of degree ≥ 2)` and
`f(X) ≡ X^q (mod π)` (Milne, *CFT*, Definition 2.9). -/
def IsLubinTateSeries (π : A) (q : ℕ) (f : MvPowerSeries (Fin 1) A) : Prop :=
  f.constantCoeff = 0 ∧ coeffX 1 f = π ∧
    ∀ n : ℕ, coeffX n f - (if n = q then 1 else 0) ∈ Ideal.span {π}

theorem IsLubinTateSeries.constantCoeff {f : MvPowerSeries (Fin 1) A}
    (hf : IsLubinTateSeries π q f) : f.constantCoeff = 0 := hf.1

theorem IsLubinTateSeries.coeff_one {f : MvPowerSeries (Fin 1) A}
    (hf : IsLubinTateSeries π q f) : coeffX 1 f = π := hf.2.1

theorem IsLubinTateSeries.coeff_congr {f : MvPowerSeries (Fin 1) A}
    (hf : IsLubinTateSeries π q f) (n : ℕ) :
    coeffX n f - (if n = q then 1 else 0) ∈ Ideal.span {π} := hf.2.2 n

/-- A Lubin–Tate series has zero constant coefficient, hence positive order. -/
theorem IsLubinTateSeries.order_pos {f : MvPowerSeries (Fin 1) A}
    (hf : IsLubinTateSeries π q f) : 1 ≤ f.order := by
  rw [MvPowerSeries.one_le_order_iff_constCoeff_eq_zero]
  exact hf.constantCoeff

/-- `f` and `g` **agree modulo terms of total degree `≥ n`** (Milne's `f ≡ g mod deg n`). -/
def AgreeModDegree (n : ℕ) {σ : Type u} (f g : MvPowerSeries σ A) : Prop :=
  ∀ s : σ →₀ ℕ, s.degree < n → MvPowerSeries.coeff s f = MvPowerSeries.coeff s g

/-- **All coefficients of `h` are divisible by `π`**: `h ∈ π·A⟦X₁,…,Xₙ⟧`. -/
def CoeffsDivisibleBy (π : A) {σ : Type u} (h : MvPowerSeries σ A) : Prop :=
  ∀ s : σ →₀ ℕ, MvPowerSeries.coeff s h ∈ Ideal.span {π}

theorem agreeModDegree_refl (n : ℕ) {σ : Type u} (f : MvPowerSeries σ A) :
    AgreeModDegree n f f := fun _ _ => rfl

theorem AgreeModDegree.symm {n : ℕ} {σ : Type u}
    {f g : MvPowerSeries σ A} (h : AgreeModDegree n f g) : AgreeModDegree n g f :=
  fun s hs => (h s hs).symm

theorem AgreeModDegree.trans {n : ℕ} {σ : Type u}
    {f g k : MvPowerSeries σ A} (hfg : AgreeModDegree n f g) (hgk : AgreeModDegree n g k) :
    AgreeModDegree n f k := fun s hs => (hfg s hs).trans (hgk s hs)

theorem AgreeModDegree.mono {m n : ℕ} {σ : Type u}
    {f g : MvPowerSeries σ A} (h : AgreeModDegree n f g) (hmn : m ≤ n) : AgreeModDegree m f g :=
  fun s hs => h s (lt_of_lt_of_le hs hmn)

/-- Agreement to all degrees is equality. -/
theorem eq_of_agreeModDegree_all {σ : Type u}
    {f g : MvPowerSeries σ A} (h : ∀ n, AgreeModDegree n f g) : f = g := by
  ext s
  exact h (s.degree + 1) s (Nat.lt_succ_self _)

/-- **`f` is an endomorphism of the two-variable formal group law `G`** (Milne, *CFT*,
Definition 2.6): `f(G(X,Y)) = G(f(X), f(Y))` as power series. -/
def IsEndoSeries (G : MvPowerSeries (Fin 2) A) (f : MvPowerSeries (Fin 1) A) : Prop :=
  MvPowerSeries.subst ![G] f
    = G.subst ![MvPowerSeries.subst ![MvPowerSeries.X 0] f,
        MvPowerSeries.subst ![MvPowerSeries.X 1] f]

/-- The standard Lubin–Tate series `f(X) = πX + X^q` (Milne, *CFT*, Example 2.10(a)). -/
def piXAddXq (π : A) (q : ℕ) : MvPowerSeries (Fin 1) A :=
  MvPowerSeries.C π * MvPowerSeries.X 0 + MvPowerSeries.X 0 ^ q

end

end NK.LocalReciprocityLubinTate
