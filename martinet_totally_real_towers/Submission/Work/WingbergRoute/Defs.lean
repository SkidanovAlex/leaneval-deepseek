import Mathlib
import Submission.Work.ShafarevichKoch.All
import Submission.Work.ClassFieldTower.All
import Submission.Work.QuadraticFields.CertificateRealSummary
import Submission.Work.RelatorRank.All

/-!
# `Work.WingbergRoute.Defs` -- the vocabulary of the unramified (Wingberg) route

This module fixes the objects and the named arithmetic walls of the area
`Submission/Work/WingbergRoute/`, the *unramified* alternative route to Martinet's theorem
(`Submission.exists_totallyReal_discr_le`).  Everything here is a definition or a small
bookkeeping lemma; the mathematics is in the sibling modules of the area.

## The classical input, and why this shape

Let `K` be a number field with no real places and let `K_∅` be its maximal unramified pro-`2`
extension, `G_∅ = Gal(K_∅/K)`.  Write `d(G_∅) = dim_{𝔽₂} H¹(G_∅,𝔽₂)` for the generator rank and
`r(G_∅) = dim_{𝔽₂} H²(G_∅,𝔽₂)` for the relation rank, and `df(G_∅) = r - d` for the deficiency.
The classical theorem (Shafarevich 1963/64; Neukirch--Schmidt--Wingberg Ch. VIII §8 Thm. 8.8.1
with Lemma 8.8.4; Wingberg, *On the Fontaine--Mazur conjecture for CM-fields*, Compositio Math.
**131** (2002) 341--354; Hajir--Maire--Ramakrishna, arXiv:2103.09508, Thm. 1 and Cor.
`prop:r-d_wingberg`) is

```
r(G_∅) - d(G_∅) = df(G_∅) ≤ d₂(O_K^×) = r₁ + r₂ ,
```

the `S = ∅` case of Shafarevich's relation-rank bound `d₂(G_S) ≤ d₁(G_S) + (r₁+r₂-1) + θ` with
`θ = 1` (because `ζ₂ = -1 ∈ K`, `S = ∅`; see D. C. Mayer, *Recent progress in determining
`p`-class field towers*, arXiv:1605.09617, Thm. `thm:RelationRank`), the two shapes being the
same because `(r₁+r₂-1) + 1 = r₁+r₂ = d₂(O_K^×)`.  This identity is
`Work.WingbergRoute.unitTwoRank_eq_unitsRank_add_one` below.

`Work.WingbergRoute.ShafarevichBound F M` is that bound, stated for the concrete group
`galoisGroup M` in the form `dim H² ≤ dim H¹ + d₂(O_F^×)`, with the two dimensions presented as
the exponents of the cardinalities (`H¹`, `H²` are `𝔽₂`-vector spaces).  Stating it this way makes
it *non-vacuous* even in the presence of non-finiteness (`Nat.card` of an infinite type is `0`):
the proposition asserts the existence of the two exponents.

## The two instances

* `Work.WingbergRoute.KcWingbergWall` -- over the imaginary quadratic field
  `Kc = ℚ(√-30030)`, where `d₂(O_Kc^×) = 1` and `d(G_∅) = 5`, giving `r ≤ 6`; this is the wall of
  `Submission/Work/ShafarevichKoch/`.
* `Work.WingbergRoute.gsFWingbergWall` -- over the **totally real** field
  `F = gsF = ℚ(√2576450045)` of `Submission/Work/QuadraticFields/`, where `d₂(O_F^×) = 2` and
  `d(G_∅) ≥ 6`; the levels of the resulting tower are totally real, which is what makes this
  instance reach the benchmark itself.

## Main declarations

* `Work.WingbergRoute.genDim`, `...ShafarevichBound`;
* `Work.WingbergRoute.WingbergUnitInstance`, `...WingbergDualityFaithful` (the literature shape);
* `Work.WingbergRoute.KcWingbergWall`, `...KcH3Wall`, `...KcKochInjectionWall`;
* `Work.WingbergRoute.gsFWingbergWall`, `...gsFArithmeticInput`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField
open Work.ConCohomology

noncomputable section

namespace Work.WingbergRoute

/-- The imaginary quadratic field `Kc = ℚ(√-30030)` of the Shafarevich--Koch chapter. -/
abbrev Kc : Type := Work.ClassFieldTower.Kc

/-- The totally real quadratic field `F = ℚ(√2576450045)` of the multiquadratic certificate of
`Submission/Work/QuadraticFields/`. -/
abbrev gsF : Type := ↥Work.QuadraticFields.gsF

/-- **The `𝔽₂`-dimension of `H¹(Γ,𝔽₂)`**, presented as the logarithm of the cardinality.  When
`H¹(Γ,𝔽₂)` is infinite (`Nat.card = 0`) this is `0`, so it must only be used under the
hypothesis that the cardinality is a power of `2`; the walls below always carry that witness. -/
def genDim (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : ℕ :=
  Nat.log 2 (Nat.card (H1 Γ (ZMod 2)))

/-- **The `𝔽₂`-dimension of `H²_cont(Γ,𝔽₂)`**, presented as the logarithm of the cardinality. -/
def relDim (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : ℕ :=
  Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Γ))

/-- **Shafarevich's relation-rank bound in the unramified (`S = ∅`) case**, for a number field
`F` and a maximal unramified pro-`2` extension `M`:

```
dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ dim_{𝔽₂} H¹(G_∅,𝔽₂) + d₂(O_F^×) .
```

The two dimensions are recorded through the exponents `k` and `d` of the cardinalities (both
groups are `𝔽₂`-vector spaces), so the statement is non-vacuous: it *asserts* that
`#H²(G_∅,𝔽₂) = 2^k` and `#H¹(G_∅,𝔽₂) = 2^d` for some `k`, `d` with `k ≤ d + d₂(O_F^×)`.

Equivalently (Neukirch--Schmidt--Wingberg Ch. VIII §8 Thm. 8.8.1, see
`Work.WingbergRoute.unitTwoRank_eq_unitsRank_add_one`) this is the classical statement
`d₂(G_∅) ≤ d₁(G_∅) + r + θ` with `r = r₁ + r₂ - 1` the Dirichlet unit rank and `θ = 1`. -/
def ShafarevichBound (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP F 2) : Prop :=
  ∃ k d : ℕ,
    Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) = 2 ^ k ∧
    Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d ∧
    k ≤ d + Work.ClassFieldTower.unitTwoRank F

/-! ## The literature shape of Wingberg's duality -/

/-- **Wingberg's duality, `i = 0` instance** (Neukirch--Schmidt--Wingberg Ch. VIII §8 Thm. 8.8.1
with Lemma 8.8.4; Hajir--Maire--Ramakrishna arXiv:2103.09508, §1.2): the Pontryagin dual of
`H³(G_∅,ℤ)` is the group of *universal norms* of units
`Ĥ⁰(G_∅, O_{Kc_∅}^×) = lim_{L} (𝓞 Kc)ˣ / N_{L/Kc}(𝓞 L)ˣ`,

which is a quotient of `(𝓞 Kc)ˣ`.  This is the *entire* arithmetic content of the chapter's
`Work.ShafarevichKoch.WingbergDuality`: the `i = 1` conjunct is the H²-half, which is proved in
this workspace without class field theory. -/
def WingbergUnitInstance (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) : Prop :=
  Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
    ∃ N : Subgroup (Work.ShafarevichKoch.RingUnit Kc),
      Nonempty (Work.ShafarevichKoch.PDual (Work.ShafarevichKoch.H3
          (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+
        Additive (Work.ShafarevichKoch.RingUnit Kc ⧸ N))

/-- **Wingberg's duality in the shape consumed by this workspace**: the `i = 0` and `i = 1`
instances of `Ĥ^i(G_∅, O_{Kc_∅}^×) ≅ Ĥ^{3-i}(G_∅,ℤ)^∨` (Neukirch--Schmidt--Wingberg Ch. VIII §8
Thm. 8.8.1, in the case `S = T = ∅`, `A = ℤ`, `𝔠` the class of finite `2`-groups), together with
the finiteness of the two cohomology groups.

This is *verbatim* `Work.ShafarevichKoch.WingbergDuality`; `Work.WingbergRoute.Verification`
proves the equivalence and records the comparison with the literature. -/
def WingbergDualityFaithful (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) : Prop :=
  Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
    Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
    Nonempty (Work.ShafarevichKoch.PDual
        (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+
      Additive Work.ShafarevichKoch.Cl2Part) ∧
    (∃ N : Subgroup (Work.ShafarevichKoch.RingUnit Kc),
      Nonempty (Work.ShafarevichKoch.PDual (Work.ShafarevichKoch.H3
          (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+
        Additive (Work.ShafarevichKoch.RingUnit Kc ⧸ N)))

/-! ## The walls -/

/-- **THE `Kc` WALL.**  Shafarevich's relation-rank bound (`S = ∅`) for the maximal unramified
pro-`2` extension of `Kc = ℚ(√-30030)`.

Numerically (`d₂(O_Kc^×) = 1`, `d(G_∅) = 5`) this is `r(G_∅) ≤ 6 = d(G_∅) + 1`; it is the single
remaining arithmetic input of `Submission/Work/ShafarevichKoch/`
(`KcKochCohomologyBound` / `KcProTwoPresentationInput`). -/
def KcWingbergWall : Prop :=
  ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, ShafarevichBound Kc M

/-- **The `Kc` wall in the one-byte `H³`-torsion form**: `#H³(G_∅,ℤ)[2] ≤ 2`, together with the
finiteness of `H²` and `H³`.

**The finiteness conjuncts are essential and cannot be dropped** (a point recorded here because it
was checked while building this area): the dictionary
`#H²(G_∅,𝔽₂) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #H³(G_∅,ℤ)[2]` needs
`#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) = 2^5` *exactly*, and the general implication
`#A[2] ≤ #(A/2A)` for an abelian group `A` is **false** — for the Prüfer group
`A = ℚ₂/ℤ₂` one has `#A[2] = 2 > 1 = #(A/2A)`.  What the workspace proves unconditionally is only
`#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) ≤ 2^5`
(`Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc`), which is *vacuous* if the
quotient is infinite (`Nat.card` of an infinite type is `0`).  The finiteness of `H²(G_∅,ℤ)`
(equivalently: `G_∅^{ab} ≅ Cl(Kc) ⊗ ℤ₂` is finite, i.e. unramified class field theory) is
consequently part of the classical input, and it is stated here rather than derived. -/
def KcH3Wall : Prop :=
  ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
    Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
      Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
      Nat.card (Work.ShafarevichKoch.twoTorsionH3
        (Work.ClassFieldTower.galoisGroup M)) ≤ 2

/-- **The `Kc` wall in the Kummer-pairing (Koch) form**: the classical injection
`H²(G_∅,𝔽₂) ↪ (V_∅/Kc^{×2})^∨` of Koch, *Galois Theory of `p`-Extensions*, Ch. 11 Thm. 11.3
(the case `S = ∅` of the Shafarevich/Koch injection `Sha_S ↪ (V_S/K^{×p})^∨`). -/
def KcKochInjectionWall : Prop :=
  ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, Work.ShafarevichKoch.KochInjection M

/-- **THE TOTALLY REAL WALL.**  Shafarevich's relation-rank bound (`S = ∅`) for the maximal
unramified pro-`2` extension of the **totally real** field `gsF = ℚ(√2576450045)`.

Numerically (`d₂(O_F^×) = 2`, and `d(G_∅) ≥ 6` by the multiquadratic certificate
`gsM/gsF` unramified of degree `2^6`, `Submission/Work/QuadraticFields/`) this is
`r(G_∅) ≤ d(G_∅) + 2`, and `4(d+2) ≤ d²` for `d ≥ 6`: the Golod--Shafarevich criterion applies,
and because the base is totally real and the extension is unramified at the infinite places every
level is totally real.  This is the instance that reaches the benchmark. -/
def gsFWingbergWall : Prop :=
  ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2, ShafarevichBound gsF M

/-- **The arithmetic input of the totally real unramified route**, at the concrete field
`gsF = ℚ(√2576450045)`: a pro-`2` presentation datum for the maximal unramified (at the finite
*and* the infinite places) pro-`2` extension of `gsF`, with at least `6` generators and at most
`#α + d₂(O_gsF^×) = #α + 2` relators, all of whose finite `2`-quotients are realized by
unramified extensions.

This is `Submission.NumberField.GolodShafarevichArithmeticInput` with the base field pinned to
`gsF`; the `6` is the number of independent unramified quadratic extensions exhibited by the
multiquadratic certificate of `Submission/Work/QuadraticFields/`, and the `+2` is Shafarevich's
relation-rank bound (equivalently Wingberg's `df ≤ d₂(O_F^×) = r₁ + r₂ = 2`). -/
def gsFArithmeticInput : Prop :=
  ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
    6 ≤ Fintype.card α ∧
    rel.card ≤ Fintype.card α + Work.ClassFieldTower.unitTwoRank gsF ∧
    (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) ∧
    Group.ResiduallyFinite G ∧
    (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N)) ∧
    (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra gsF L)
        (_ : FiniteDimensional gsF L) (_ : IsGalois gsF L),
        differentIdeal (𝓞 gsF) (𝓞 L) = ⊤ ∧ IsUnramifiedAtInfinitePlaces gsF L ∧
        Nonempty ((L ≃ₐ[gsF] L) ≃* (G ⧸ N)))

end Work.WingbergRoute
