import Mathlib
import Submission.Work.WingbergRoute.All
import Submission.Work.WingbergH3.All
import Submission.Work.RelatorRank.All
import Submission.NumberField.MaximalProPOutsideS
import Submission.Work.QuadraticFields.CertificateRealSummary
import Submission.GroupTheory.GolodShafarevichFromCommons
import Submission.Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset
import Submission.Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_le_iSup_finset
import Submission.Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces

/-!
# `Work.WingbergEndgame` -- the unramified (Wingberg) route, and its endgame

**Namespace** `Work.WingbergEndgame`.

This area is the *unramified* route to Martinet's theorem, i.e. the route through

```
Work.WingbergRoute.exists_totallyReal_discr_le_of_gsFArithmeticInput :
  Work.WingbergRoute.gsFArithmeticInput -> Work.CMRealSubfield.Benchmark ,
```

at the **totally real** base field `gsF = ℚ(√(5·13·17·29·37·41·53))`.

## The mathematical content of the route

Let `F` be a totally real number field and `K/F` its **maximal pro-`2` extension unramified at
every place, finite and infinite** (`Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf`
with `S = ∅`; no class field theory is needed for the construction).  Write `Γ = Gal(K/F)`.  Then
every finite dimensional Galois subextension of `K/F` is a totally real number field with
`rootDiscr = rootDiscr F`, so *infinite* `Γ` gives Martinet's asymptotically good totally real
tower (`Submission.NumberField.exists_totallyReal_discr_le_of_infinite_unramified_protwo`).

By Golod--Shafarevich (`Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich`, with
the finite `p`-group inequality supplied by the library,
`Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons`), `Γ` is infinite as soon as it
has a presentation with `d` minimal generators and at most `d²/4` relators.  For `F = gsF` the
genus certificate `gsM/gsF` (`Work.QuadraticFields.gs_certificate`) gives `d ≥ 6`, so the
numerical content is

```
d₂(Γ) ≤ d₁(Γ) + d₂(O_gsF^×) = d₁(Γ) + unitTwoRank gsF = d₁(Γ) + 2 ,
```

i.e. `df(Γ) = d₂(Γ) - d₁(Γ) ≤ 2 = r₁ + r₂`: **Shafarevich's relation-rank bound for the
unramified case**, equivalently the `i = 0` instance of **Wingberg's duality**
`Ĥ⁰(Γ, O_K^×) ≅ H³(Γ,ℤ)^∨` (Wingberg, Compositio Math. **131** (2002); NSW VIII §8 Thm. 8.8.1,
`S = T = ∅`).

## The object, and why it is *not* the one the area recorded

`Work.WingbergRoute.gsFDeficiencyWall` (and `Work.WingbergH3.H3DeficiencyWall gsF`) state the
relation bound for `M : Work.ClassFieldTower.MaximalUnramifiedProP gsF 2`, the maximal pro-`2`
extension whose relative **different is trivial** -- i.e. unramified at the *finite* primes only.
That is the *narrow* (strict) object: its abelianisation is the narrow class group `Cl⁺(gsF) ⊗ ℤ₂`,
and its finite quotients need not be totally real.  The route to the benchmark needs the *wide*
object (`Cl(gsF) ⊗ ℤ₂`), i.e. unramifiedness at the infinite places *as well* -- exactly the
subtlety recorded in `Submission/Work/WingbergRoute/README.md` §6.2.  This area therefore

* defines the wide object (`UnramifiedProTwoExtension` below) and proves it exists;
* states the wall `h3DeficiencyWall` on it, in the form in which a pro-`2` presentation is
  actually produced (`HasProTwoPresentation`, a *genuine* pro-`2` presentation: the relators must
  present `Γ` itself, not merely a group with the same dense image);
* proves the whole endgame `h3DeficiencyWall → Work.CMRealSubfield.Benchmark` with no further
  input, including the reduction to `Work.WingbergRoute.gsFArithmeticInput`;
* records what the constructive alternative (Hajir--Maire--Ramakrishna / Shafarevich) amounts to
  here, as named `Prop`s.

## Main declarations

* `Work.WingbergEndgame.UnramifiedProTwoExtension` -- the wide maximal pro-`2` object;
* `Work.WingbergEndgame.exists_unramifiedProTwoExtension`;
* `Work.WingbergEndgame.HasProTwoPresentation` -- a genuine pro-`2` presentation;
* ★ `Work.WingbergEndgame.h3DeficiencyWall` -- **the wall**, the single named `Prop` of the area;
* `Work.WingbergEndgame.exists_totallyReal_discr_le_of_h3DeficiencyWall` -- the benchmark.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.WingbergEndgame

/-! ## 1. The base field -/

/-- The totally real quadratic field `gsF = ℚ(√(5·13·17·29·37·41·53))` of
`Submission/Work/QuadraticFields/`, the base of the only instance of the unramified route that
reaches the benchmark `Submission.exists_totallyReal_discr_le`. -/
abbrev gsF : Type := Work.WingbergRoute.gsF

/-- The totally real base has `d₂(O^×) = r₁ + r₂ = 2` (`Work.WingbergRoute.unitTwoRank_gsF`). -/
theorem unitTwoRank_gsF : Work.ClassFieldTower.unitTwoRank gsF = 2 :=
  Work.WingbergRoute.unitTwoRank_gsF

/-! ## 2. The wide maximal pro-`2` extension -/

/-- **The maximal pro-`2` extension of `F` unramified at every place, finite and infinite.**

A number field `K` (carried as `E.K`) with

* `universal`: every finite Galois pro-`2` extension `M/F` with trivial relative different *and*
  unramified at the infinite places embeds into `K`;
* `proP`: every finite dimensional Galois subextension of `K/F` has pro-`2` Galois group;
* `unramified`: every finite dimensional Galois subextension is unramified at the finite primes;
* `unramifiedInf`: ... and at the infinite places.

This is the object `F_∞` whose Galois group is the *wide* unramified pro-`2` group
(`Cl(F) ⊗ ℤ₂` abelianised), and it is the object the Martinet route needs: being unramified at the
infinite places is what makes all its levels totally real when `F` is
(`Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces`).

It differs from `Work.ClassFieldTower.MaximalUnramifiedProP F 2`, which records only
`differentIdeal = ⊤` (the *narrow* object).  Existence: `exists_unramifiedProTwoExtension`,
with no class field theory. -/
structure UnramifiedProTwoExtension (F : Type*) [Field F] [NumberField F] where
  /-- the field `F_∞` -/
  K : Type
  [fieldK : Field K]
  [algebraK : Algebra F K]
  [galoisK : IsGalois F K]
  /-- universal property: every finite everywhere-unramified pro-`2` extension of `F` embeds in `K` -/
  universal : ∀ (M : Type) [Field M] [NumberField M] [Algebra F M] [IsGalois F M],
      IsPGroup 2 (M ≃ₐ[F] M) → differentIdeal (𝓞 F) (𝓞 M) = ⊤ →
        IsUnramifiedAtInfinitePlaces F M → ∃ φ : M →ₐ[F] K, True
  /-- every finite dimensional Galois subextension of `K/F` is pro-`2` -/
  proP : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L → IsGalois F L →
      IsPGroup 2 (L ≃ₐ[F] L)
  /-- every finite dimensional Galois subextension of `K/F` is unramified at the finite primes -/
  unramified : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤
  /-- every finite dimensional Galois subextension of `K/F` is unramified at the infinite places -/
  unramifiedInf : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsUnramifiedAtInfinitePlaces F ↥L

attribute [instance] UnramifiedProTwoExtension.fieldK UnramifiedProTwoExtension.algebraK
  UnramifiedProTwoExtension.galoisK

namespace UnramifiedProTwoExtension

variable {F : Type*} [Field F] [NumberField F]

/-- **`Γ = Gal(F_∞/F)`**, the wide unramified pro-`2` group of `F`. -/
abbrev galoisGroup (E : UnramifiedProTwoExtension F) : Type := E.K ≃ₐ[F] E.K

instance (E : UnramifiedProTwoExtension F) : Group (galoisGroup E) := inferInstance

end UnramifiedProTwoExtension

/-- `Γ = Gal(F_∞/F)`, the wide unramified pro-`2` group. -/
abbrev galoisGroup {F : Type*} [Field F] [NumberField F]
    (E : UnramifiedProTwoExtension F) : Type := UnramifiedProTwoExtension.galoisGroup E

/-! ### Existence -/

/-- **A proper ideal is contained in a maximal ideal and is divisible by it.**  In the ring of
integers this is the Dedekind statement `I ∣ J ↔ J ≤ I`. -/
theorem dvd_of_le_of_ne_top {R : Type*} [CommRing R] [IsDedekindDomain R] {I P : Ideal R}
    (hP : P.IsMaximal) (h : I ≤ P) : P ∣ I :=
  Ideal.dvd_iff_le.mpr h

/-- **If no prime ideal divides the relative different, the extension is unramified at every
finite prime.**  This is the form of the `S = ∅` case of the support condition used by the
`∞`-conditioned maximal extension
`Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf`. -/
theorem differentIdeal_eq_top_of_forall_prime_not_dvd {F L : Type*} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L]
    (h : ∀ P : Ideal (𝓞 L), P.IsPrime → P ≠ ⊥ → ¬ (P ∣ differentIdeal (𝓞 F) (𝓞 L))) :
    differentIdeal (𝓞 F) (𝓞 L) = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hPprime : P.IsPrime := hPmax.isPrime
  have hPne : P ≠ ⊥ := by
    intro hbot
    exact differentIdeal_ne_bot (le_bot_iff.mp (hbot ▸ hle))
  exact h P hPprime hPne (dvd_of_le_of_ne_top hPmax hle)

/-- **The wide maximal pro-`2` extension exists, with no class field theory.**  It is the
`S = ∅` case of the `∞`-conditioned sup-construction
`Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf`. -/
theorem exists_unramifiedProTwoExtension (F : Type) [Field F] [NumberField F] :
    Nonempty (UnramifiedProTwoExtension F) := by
  classical
  obtain ⟨K, iK, iA, iG, huniv, hsub⟩ :=
    Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf F 2 (∅ : Finset ℕ)
  letI : Field K := iK
  letI : Algebra F K := iA
  letI : IsGalois F K := iG
  refine ⟨{ K := K, universal := ?_, proP := ?_, unramified := ?_, unramifiedInf := ?_ }⟩
  · intro M _ _ _ _ hpg hdiff hinf
    refine huniv M hpg ?_ hinf
    intro P hP hPne hdvd
    rw [hdiff] at hdvd
    exact (hP.ne_top (le_top.antisymm (Ideal.dvd_iff_le.mp hdvd))).elim
  · intro L _ hfd hgal
    exact (hsub L hfd hgal).1
  · intro L _ hfd hgal
    refine differentIdeal_eq_top_of_forall_prime_not_dvd ?_
    intro P hP hPne hdvd
    obtain ⟨q, hq, -⟩ := (hsub L hfd hgal).2.1 P hP hPne hdvd
    exact absurd hq (Finset.notMem_empty q)
  · intro L _ hfd hgal
    exact (hsub L hfd hgal).2.2

/-! ## 3. Genuine pro-`2` presentations -/

/-- **A *genuine* pro-`2` presentation of a topological group `Γ` on `d` generators with at most
`r` relators.**

This is the classical notion -- "`Γ` is presented by the relators `S` in the category of pro-`2`
groups" -- in a form that is self-contained and that the endgame can consume:

* `gen : Fin d → Γ` is a dense generating family;
* `S` is a relator set of size `≤ r`;
* the presentation is **faithful**: `ker (FreeGroup.lift gen) = ⟪S⟫`;
* the presentation is **complete** (this is the clause that distinguishes a genuine pro-`2`
  presentation from the discrete presentation `Work.RelatorRank.HasProP2Presentation`): every
  homomorphism `φ : FreeGroup (Fin d) →* P` into a *finite* `2`-group carrying the **discrete**
  topology (`⊥` in Lean, `DiscreteTopology.eq_bot`) which kills `S` **factors continuously through
  `Γ`**.

The last clause is exactly the statement that the abstract group `FreeGroup (Fin d) ⧸ ⟪S⟫`
presented by `S` has no more finite `2`-quotients than `Γ` -- equivalently that the pro-`2`
completion of that abstract group is `Γ` (`Work.ProPDict.relKernel_le_ker_of_le_sup_relFrattini`
is the analogous statement for a *spanning* relator set).  Without it, the discrete presentation
of `Work.RelatorRank.HasProP2Presentation` may have extraneous finite `2`-quotients, and the
quotients of the presented group need not be realisable by unramified extensions. -/
def HasProTwoPresentation (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (d r : ℕ) : Prop :=
  ∃ (gen : Fin d → Γ) (S : Finset (FreeGroup (Fin d))),
    S.card ≤ r ∧ Work.RelatorRank.DenseGenerating gen ∧
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (S : Set (FreeGroup (Fin d))) ∧
      ∀ (P : Type) [Group P] [Fintype P], IsPGroup 2 P → (φ : FreeGroup (Fin d) →* P) →
        (∀ s ∈ S, φ s = 1) → ∃ g : Γ →* P, @Continuous Γ P _ ⊥ g ∧
          g.comp (FreeGroup.lift gen) = φ

/-- The discrete (faithful) part of a genuine pro-`2` presentation: the abstract group presented
by the relators is a subgroup of `Γ` with dense image. -/
theorem HasProTwoPresentation.hasProP2Presentation {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {d r : ℕ} (h : HasProTwoPresentation Γ d r) :
    Work.RelatorRank.HasProP2Presentation Γ d r := by
  obtain ⟨gen, S, hcard, hdense, hker, -⟩ := h
  exact ⟨{ gen := gen, rel := S, dense := hdense, card_le := hcard, ker_eq := hker }⟩

/-! ## 4. The wall -/

/-- **THE WALL.**  *The* single named residual `Prop` of this area: Wingberg's duality / the
`H³`-half of Shafarevich's relation-rank bound, for the **wide** maximal pro-`2` extension of the
totally real base `gsF`.

Concretely: there is a wide maximal pro-`2` extension `E` of `gsF` whose Galois group
`Γ = Gal(gsF_∞/gsF)` admits a genuine pro-`2` presentation on `d₁(Γ) = GeneratorRank Γ`
generators and at most `d₁(Γ) + d₂(O_gsF^×) = d₁(Γ) + 2` relators:

```
d₂(Γ) ≤ d₁(Γ) + d₂(O_gsF^×) = d₁(Γ) + 2 ,   equivalently   df(Γ) ≤ 2 .
```

The generator count is the *minimal* one, so this is exactly the relation-rank bound, not a
statement about a redundant presentation.  A proof needs Wingberg's duality in degree `0`,
`H³(Γ,ℤ)^∨ ≅ Ĥ⁰(Γ, O_{gsF_∞}^×)` (NSW Ch. VIII §8 Thm. 8.8.1, `S = T = ∅`), i.e. the idèle class
group of the tower and its Tate/Artin duality.  The `H²`-half of the same duality is *proved* in
this workspace (`Work.WingbergRoute.natCard_H2Z_quot_two_le_card_H1_zmodTwo_gsF` and
`Work.ShafarevichKoch.natCard_H2_zmodTwo_eq`).

Everything downstream of this `Prop` is proved here: the Golod--Shafarevich step
(`infinite_of_h3DeficiencyWall`), the benchmark
(`exists_totallyReal_discr_le_of_h3DeficiencyWall`), and the reduction to the route's arithmetic
input `Work.WingbergRoute.gsFArithmeticInput` (`gsFArithmeticInput_of_h3DeficiencyWall`). -/
def h3DeficiencyWall : Prop :=
  ∃ E : UnramifiedProTwoExtension gsF,
    HasProTwoPresentation (galoisGroup E) (Work.RelatorRank.GeneratorRank (galoisGroup E))
      (Work.RelatorRank.GeneratorRank (galoisGroup E) + Work.ClassFieldTower.unitTwoRank gsF)

/-! ## 5. The recorded (narrow) forms, for comparison -/

/-- The **`H³`-half in the form recorded by the sibling area**
(`Work.WingbergH3.H3DeficiencyWall gsF`, which is *literally*
`Work.WingbergRoute.gsFDeficiencyWall`): the same relation bound, for the **narrow** object
`Work.ClassFieldTower.MaximalUnramifiedProP gsF 2` (trivial relative different only). -/
abbrev recordedDeficiencyWall : Prop := Work.WingbergRoute.gsFDeficiencyWall

/-- The recorded wall in its `H³`-torsion form (`Work.WingbergH3.H3DeficiencyWall`). -/
abbrev recordedH3DeficiencyWall : Prop := Work.WingbergH3.H3DeficiencyWall gsF

/-- The recorded wall in its classical "unit half of Wingberg's duality" form. -/
abbrev recordedUnitDualityWall : Prop := Work.WingbergH3.H3UnitDualityWall gsF

/-- The recorded wall in its sharp form (`df ≤ d₂(O^×) - 1 = 1`, Wingberg's actual theorem). -/
abbrev recordedSharpWall : Prop := Work.WingbergH3.SharpH3Wall gsF

/-- The recorded wall in the literature's deficient form `df ≤ d₂(O^×)`, at `gsF`. -/
abbrev recordedWingbergWall : Prop := Work.WingbergRoute.gsFWingbergWall

end Work.WingbergEndgame
