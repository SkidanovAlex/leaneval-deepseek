import Mathlib
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx
import Submission.Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset
import Submission.Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top
import Submission.Commons.FieldTheory.Galois.isGalois_iSup_of_charZero
import Submission.Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal
import Submission.Commons.FieldTheory.IntermediateField.exists_finset_of_le_iSup_of_finiteDimensional
import Submission.GroupTheory.GolodShafarevichFromCommons
import Submission.GroupTheory.GolodShafarevichCriterion
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.CMField

/-!
# `Work.ClassFieldTower.Defs` -- the objects and the invariants

This is the definition layer of the class-field-tower chapter
(`Submission/Work/ClassFieldTower/`), an area of the Martinet/GS route of the
`sum_product` project.

The deliverable of the chapter is: for an explicit imaginary quadratic field `F`,
the maximal unramified pro-`2` extension `F_∅` of `F` is **infinite** (an infinite
Hilbert `2`-class field tower), by Golod--Shafarevich, using the two arithmetic
invariants of `G_∅ = Gal(F_∅/F)`:

* `d(G_∅) = classGroupTwoRank F` -- the class-field-theoretic identification of the
  generator rank with `dim_{F_2} Cl(F)/Cl(F)^2` (the exponent-`2` unramified abelian
  extensions of `F` are the quadratic ones, classified by `Cl(F)/Cl(F)^2`);
* `r - d ≤ unitTwoRank F` -- the Shafarevich--Koch deficiency (relation count) bound,
  which for a number field `F` reads `0 ≤ df(G_∅) ≤ d_2(O_F^×)` with
  `d_2(O_F^×) = dim_{F_2}(O_F^×/(O_F^×)^2) = r_1 + r_2 - 1 + δ_2 = r_1 + r_2`
  (here `δ_2 = 1` because `-1` is a square root of unity in characteristic zero).
  For an imaginary quadratic field this is `1`.

Everything here is a definition; the theorems live in the sibling modules.

## Conventions

* `MaximalUnramifiedProP F p` is the object `F_∅`; its carrier is `M.K`, and
  `galoisGroup M` is `G_∅ = Gal(M.K / F)`.
* `classGroupTwoRank F` is `log_2 #(Cl(F)/Cl(F)^2)` -- for a number field this is
  the `F_2`-dimension of `Cl(F)/Cl(F)^2` (an elementary abelian `2`-group).
* `unitTwoRank F` is `r_1 + r_2`, the `F_2`-dimension of `O_F^×/(O_F^×)^2`.
* `HasMinimalPresentation G d r` says `G` has a presentation by `d` minimal generators
  and `r` relators.
* `ShafarevichKochBound F d r` is the deficiency bound `r ≤ d + unitTwoRank F`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-! ## 1. The object `F_∅` and its Galois group `G_∅` -/

/-- **The maximal unramified pro-`p` extension `F_∅` of a number field `F`.**

A number field `K` (carried as `M.K`) with:

* `M.universal`: the universal property -- every finite Galois extension `M/F` with pro-`p`
  Galois group and trivial relative different (i.e. unramified over `F`) embeds into `K`;
* `M.proP`: every finite dimensional Galois subextension of `K/F` has pro-`p` Galois group;
* `M.unramified`: every finite dimensional Galois subextension of `K/F` is unramified over `F`.

The three together say that `K` is *the* maximal unramified pro-`p` extension:
it is unramified pro-`p` over `F`, and it contains every unramified pro-`p` extension of `F`.
Existence is `Work.ClassFieldTower.exists_maximalUnramifiedProP`. -/
structure MaximalUnramifiedProP.{u} (F : Type*) [Field F] [NumberField F] (p : ℕ)
    [Fact p.Prime] where
  /-- the field `F_∅`. -/
  K : Type u
  [fieldK : Field K]
  [algebraK : Algebra F K]
  [galoisK : IsGalois F K]
  /-- Universal property: every finite unramified pro-`p` extension of `F` embeds in `K`. -/
  universal : ∀ (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M],
      IsPGroup p (M ≃ₐ[F] M) → differentIdeal (𝓞 F) (𝓞 M) = ⊤ → ∃ φ : M →ₐ[F] K, True
  /-- Every finite dimensional Galois subextension of `K/F` is pro-`p`. -/
  proP : ∀ L : IntermediateField F K, FiniteDimensional F L → IsGalois F L →
      IsPGroup p (L ≃ₐ[F] L)
  /-- Every finite dimensional Galois subextension of `K/F` is unramified over `F`. -/
  unramified : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤

attribute [instance] MaximalUnramifiedProP.fieldK MaximalUnramifiedProP.algebraK
  MaximalUnramifiedProP.galoisK

namespace MaximalUnramifiedProP

variable {F : Type*} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

/-- **`G_∅ = Gal(F_∅/F)`**, the Galois group of the maximal unramified pro-`p` extension. -/
abbrev galoisGroup (M : MaximalUnramifiedProP F p) : Type _ := M.K ≃ₐ[F] M.K

instance (M : MaximalUnramifiedProP F p) : Group (galoisGroup M) := inferInstance

end MaximalUnramifiedProP

/-- `G_∅ = Gal(F_∅/F)`, the Galois group of the maximal unramified pro-`p` extension. -/
abbrev galoisGroup {F : Type*} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    (M : MaximalUnramifiedProP F p) : Type _ := MaximalUnramifiedProP.galoisGroup M

/-! ## 2. The two arithmetic invariants -/

/-- **`d_2(O_F^×) = dim_{F_2}(O_F^×/(O_F^×)^2) = r_1 + r_2`.**

By Dirichlet's unit theorem `O_F^× ≅ μ_F × ℤ^{r_1+r_2-1}`; mod squares this is
`(ℤ/2)^{r_1+r_2-1} × μ_F/μ_F^2`, and `μ_F/μ_F^2 ≅ ℤ/2` in characteristic zero
(because `-1 ∈ μ_F` and `-1 ≠ 1`).  Hence the `F_2`-dimension is `r_1 + r_2`, i.e.
`NumberField.Units.rank F + 1`.  This is the quantity `d(O_F^×)` of the
Shafarevich--Koch deficiency bound.  The identification with the `2`-rank of `O_F^×` is proved
as `Work.ClassFieldTower.unitTwoRank_eq_finrank_units_modSquares`, and
`Work.ClassFieldTower.unitTwoRank_le_one_iff` shows that `unitTwoRank F ≤ 1` (the hypothesis of
the Golod--Shafarevich criterion for a quadratic field) holds exactly for `F = ℚ` and the
imaginary quadratic fields. -/
def unitTwoRank (F : Type*) [Field F] [NumberField F] : ℕ :=
  NumberField.Units.rank F + 1

/-- **`rank_2 Cl(F) = dim_{F_2}(Cl(F)/Cl(F)^2)`**, the `2`-rank of the ideal class group,
computed as the base-`2` logarithm of the cardinality of `Cl(F)/Cl(F)^2`.

(`Cl(F)/Cl(F)^2` is an elementary abelian `2`-group, so its cardinality is a power of `2`
and its `F_2`-dimension is exactly the base-`2` logarithm; this is
`Work.ClassFieldTower.classGroupTwoRank_eq_finrank_modN`.) -/
def classGroupTwoRank (F : Type*) [Field F] [NumberField F] : ℕ :=
  Nat.log 2 (Nat.card (ClassGroup (𝓞 F) ⧸
    Subgroup.closure (Set.range (fun x : ClassGroup (𝓞 F) => x ^ 2))))

/-! ## 3. Presentations, the Golod--Shafarevich inequality, deficiency -/

/-- **`G` has a minimal presentation with `d` generators and `r` relators.**

I.e. there are `α` with `Fintype.card α = d`, a relator set `rel : Finset (FreeGroup α)`
with `rel.card = r`, an isomorphism `G ≃* FreeGroup α ⧸ normalClosure rel`, and `α` is
*minimal*: no generating set of `G` is smaller than `d`.

This is the interface consumed by the Golod--Shafarevich criterion
`Work.ClassFieldTower.infinite_of_hasMinimalPresentation`. -/
def HasMinimalPresentation (G : Type*) [Group G] (d r : ℕ) : Prop :=
  ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    Fintype.card α = d ∧ rel.card = r ∧
    Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) ∧
    (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → d ≤ S.card)

/-- **The Golod--Shafarevich inequality `4r ≤ d^2`** for a presentation with `d` generators
and `r` relators: the presentation datum that makes the Golod--Shafarevich theorem apply. -/
def GolodShafarevichInequality (d r : ℕ) : Prop := 4 * r ≤ d * d

/-- **The Shafarevich--Koch deficiency bound (relation count) for `G_∅`.**

`0 ≤ df(G_∅) ≤ d_2(O_F^×)`, i.e. `r ≤ d + unitTwoRank F` for a minimal presentation of `G_∅`
by `d` generators and `r` relators.  For an imaginary quadratic field this reads
`r ≤ d + 1`. -/
def ShafarevichKochBound (F : Type*) [Field F] [NumberField F] (d r : ℕ) : Prop :=
  r ≤ d + unitTwoRank F

/-- The deficiency `df = r - d` of a presentation by `d` generators and `r` relators. -/
def deficiency (d r : ℕ) : ℕ := r - d

/-! ## 4. The arithmetic certificate -/

/-- **The Golod--Shafarevich certificate for the Hilbert `2`-class field tower of `F`.**

This is the single arithmetic input of the chapter.  It consists of the two classical
invariants of the maximal unramified pro-`2` group `G_∅ = Gal(F_∅/F)`:

* `gen_eq`: `d(G_∅) = rank_2 Cl(F)` -- class field theory (`G_∅/Φ(G_∅)` is the `2`-part of
  the class group), stated here as the generator-number part of a minimal presentation
  (`presentation` below carries the matching `d`);
* `deficiency`: the Shafarevich--Koch bound `r ≤ d + d_2(O_F^×)`;
* `unit_bound`: `d_2(O_F^×) ≤ 1`, i.e. `F` is (up to units) an imaginary quadratic field;
* `presentation`: `G_∅` has a minimal presentation by `d` generators and `r` relators;
* `rank_ge`: `5 ≤ d = rank_2 Cl(F)`, the numerical input supplied for a concrete field by
  `Submission.Work.QuadraticFields`.

Given this, `Work.ClassFieldTower.infinite_galoisGroup_of_certificate` produces
`Infinite G_∅`. -/
structure GolodShafarevichCertificate (F : Type*) [Field F] [NumberField F]
    (M : MaximalUnramifiedProP F 2) (d r : ℕ) : Prop where
  /-- `d(G_∅) = rank_2 Cl(F)`: the generator rank is the `2`-rank of the class group. -/
  gen_eq : d = classGroupTwoRank F
  /-- The Shafarevich--Koch deficiency bound `r ≤ d + d_2(O_F^×)`. -/
  deficiency : ShafarevichKochBound F d r
  /-- `d_2(O_F^×) ≤ 1`: the field is imaginary quadratic. -/
  unit_bound : unitTwoRank F ≤ 1
  /-- `G_∅` has a minimal presentation by `d` generators and `r` relators. -/
  presentation : HasMinimalPresentation (galoisGroup M) d r
  /-- The numerical certificate `rank_2 Cl(F) ≥ 5`. -/
  rank_ge : 5 ≤ d

/-- **The wall of the chapter, in named form.**  There is an imaginary quadratic field `F` whose
Hilbert `2`-class field tower is infinite, i.e. whose maximal unramified pro-`2` extension is
infinite.  This is the classical Golod--Shafarevich theorem for imaginary quadratic fields with
many ramified primes. -/
def InfiniteHilbertTwoClassFieldTower : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NumberField F) (M : MaximalUnramifiedProP.{0} F 2) (d r : ℕ),
    GolodShafarevichCertificate F M d r ∧ Infinite (galoisGroup M)

end Work.ClassFieldTower
