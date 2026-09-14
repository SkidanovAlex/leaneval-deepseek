import Submission.Vdw.FinalEndpoints
import Submission.Vdw.CaseIICountM
import Submission.Vdw.CaseIIIBound
import Submission.Vdw.PrimeDegreePrimitive
import Submission.Vdw.ImprimitiveInput
import Submission.Vdw.CubicFieldCount
import Submission.Vdw.PerFieldFibre
import Submission.Vdw.PerFieldFibreAll
import Submission.Vdw.SchmidtCount

open Polynomial Filter Asymptotics
open scoped BigOperators
open vanDerWaerdenConjecture

set_option autoImplicit false

/-!
# `theorem_1`: exact reduction status (canonical summary)

The challenge statement

    `theorem_1 (n) (3 ≤ n) : (fun H => (E n H : ℝ)) =O[atTop] (fun H => ((H:ℕ)^(n-1) : ℝ))`

(`E n H` = number of monic degree-`n` integer polynomials with `|coeff i| ≤ H`
for `i < n` and `|Gal| < n!`) is fully reduced, with every elementary
ingredient formalised.  `Submission.lean` still carries the `sorry`; the
endpoints below are machine-checked conditional proofs.

## The reduction chain (all theorems proved, axioms propext/choice/Quot.sound)

1. `Reducible.E_isBigO_of_irrBad` — `E ≤ #RedBox + #IrreducibleBad`, and
   `Reducible.redBox_isBigO` bounds the reducible part unconditionally
   (van der Waerden–Chela).  So `theorem_1` ⟸ `#IrreducibleBad n H = O(H^(n-1))`.
2. `PrimitiveCase.irrBad_eq_prim_union_imprim` — the primitive/imprimitive
   split of `IrreducibleBad`.
3. `PrimitiveCase.PrimBadCaseIII_isBigO` — the primitive `DD = 0` /
   Case-III-subcase-(ii) slice, **unconditional** (the geometric sieve, the
   double discriminant `DoubleDisc`, `CaseIIIHeight`, `CaseIIIAssembly`,
   `CaseIIIRegion`, `CaseIIIBound`).
4. `FinalAssembly`, `PrimitiveCaseM`, `FinalAssemblyM` — the subcase-(i)
   remainder `SubcaseIM n M H` (`M` a parameter, `SubcaseIM_P2` the
   `D_f ≤ H^(2+4/M)` slice) satisfies
   `#SubcaseIM ≤ #CaseIDirectM + #CaseIFullM + #SubcaseIM_P2 + #SubcaseI_P3M`
   (`ncard_SubcaseIM_le_M`), and each of the first three pieces is
   `O(H^(n-1))` from the §4 Fourier input at `δ = 2/M`
   (`CaseIDirectM_isBigO`, `CaseIFullM_isBigO`,
   `SubcaseI_P3M_isBigO_of_perIrrBoundTheta`).
5. **The §4 Fourier input is UNCONDITIONAL.**  The Weyl-bound chapter
   (`WeylBridge` → `WeylExpSum` → the θ-generic multi-prime sieve
   `MultiPrime*` → `PerIrrTheta` → `PerIrrWeyl`) gives
   `PerIrrBoundTheta n (weylδ n) c` for every `3 ≤ n`, from the completed
   Weyl bound `Commons.Analysis.ExponentialSums.complete_sum_weyl_bound`.
   With `M := weylM n = 4n·2^n` one has `2/M = weylδ n`
   (`FinalAssemblyM.two_div_weylM`), so all the region thresholds above are
   available unconditionally.
6. `FinalEndpoints.SubcaseIM_P2_isBigO_of_countBound` (in `CaseIICountM`) —
   the last piece, `#SubcaseIM_P2 n (weylM n) H = O(H^(n-1))`, from the
   **classical** Abel-refined field-counting input `CaseIICountBound n β`
   (Lemke Oliver–Thorne + field counts), with the exponent condition
   `1 + (2 + 4/weylM n)·(β − 1/(n(n−1))) < n − 1`.

## The inputs (per degree; all are true power-shaped literature statements)

* `CaseIIClasses.PerFieldFibreBound n` — Lemke Oliver–Thorne (per-field fibre
  bound).  **No longer an input in any degree**: `PerFieldFibre` proves it from
  the elementary Mahler-measure lattice-point count
  `Commons.NumberTheory.NumberField.ncard_polys_mahler_le` (itself built on
  `ncard_mahler_le`) together with the Ellenberg–Venkatesh height bound
  `|Disc K| ≤ (2·house α)^{n(n-1)}` for a generator `α`.  In prime degree
  every non-rational element generates (`perFieldFibreBound_prime`); in
  composite degree the region's members have *primitive* Galois group
  (`SubcaseI_P2 ⊆ SubcaseI ⊆ PrimitiveBad`) and primitivity forbids proper
  subextensions via the block-system argument
  (`PerFieldFibreAll.adjoin_eq_top_of_galPrimitive`), so the same proof applies
  (`PerFieldFibreAll.perFieldFibreBound_all`).
* `CaseIIClasses.FieldCountBound n β` — the number of degree-`n` number
  fields of discriminant `≤ Y` inside the region.
  **Schmidt's exponent `β = (n+2)/4` is now a THEOREM in every degree `n ≥ 3`**
  (`SchmidtCount.fieldCountBound_schmidt`): the region consists of polynomials
  with *primitive* Galois group, so every non-rational element of the field
  generates it; the minimal polynomial of the small trace-zero Minkowski element
  (`SchmidtCount.exists_trace_zero_house_le`) therefore determines the class, and
  bounding its coefficients by `≪ |Disc|^{i/(2(n-1))}` and counting gives
  `#classes of discriminant ≤ Y ≪ Y^((n+2)/4)`.
  The *sharper* exponents are the remaining deep inputs:
  * `β = 1/2` for `n = 3` (cyclic cubic fields; `|Disc K| = f²` with `f` the
    conductor),
  * `β = 1` for `n = 4, 5` (exact quartic/quintic counts).
* the imprimitive bound `#ImprimitiveBad n H = O(H^(n-1))` — vacuous in prime
  degree (`PrimeDegreePrimitive.ImprimitiveBad_isBigO_of_prime`), Widmer's
  `O(H^(n/2+2))` for `n ≥ 6`
  (`ImprimitiveInput.ImprimitiveBad_isBigO_of_widmer`), and an `O(H³)` input
  for `n = 4` (Widmer's `H⁴` does not suffice).  **This is now the only input
  left in composite degree `n ≥ 6`.**

## SESSION-166: `n = 4` and `n = 5` are now UNCONDITIONAL (the index refinement)

`Submission/Vdw/IndexCount.lean` + `Submission/Vdw/IndexCountMain.lean` (both
imported by `Helpers`) complete Bhargava's Theorem 1.2 route to the Case-II
field count:

* `IndexCount.goodVec_ncard_le` — the per-discriminant count
  `#GoodVec n D ≤ K·D^{(n+2)/4 + ε}/D_large` for squarefull `D` with
  `v_p(D) ≤ n−1` at every prime `p > n` (Proposition 4.x + Lemma 24 + the
  slicing moduli `D_j`; the real-arithmetic endgame is `IndexCountMain`).
* `IndexCountMain.squarefull_classDisc`, `discSmallPart_classDisc_le` — every
  class discriminant of the Case-II region is squarefull (Case-I
  squarefullness, since the region is primitive with `|Gal| < n!`) and its
  small-prime part is `≤ S₀(n) = primorial n ^ (n + n·log₂ n)`.
* `IndexCountMain.goodVec_ncard_le_classDisc` — the per-class bound
  `#GoodVec n (classDisc q) ≤ K·(classDisc q)^{(n+2)/4 − 1 + ε}`.
* **`IndexCountMain.fieldCountBound_index`** — `FieldCountBound n (n/4 + ε)`
  for every `n ≥ 3`, summing the per-`D` bound over the `≪ √Y` squarefull
  `D ≤ Y`.
* **`IndexCountMain.theorem_1_of_indexRefined_four_five`** — `theorem_1` in
  degrees **`n = 4` and `n = 5`, UNCONDITIONALLY**: neither
  Davenport–Heilbronn nor Bhargava (nor Cohn) is needed.  The imprimitive
  input is the machine-checked `ImprimitiveBad_four_isBigO` for `n = 4` and
  vacuous for the prime `n = 5`.
* `IndexCountMain.theorem_1_of_indexRefined_prime` — prime `n ≥ 5`;
  `IndexCountMain.theorem_1_of_indexRefined_widmer` — composite `n ≥ 6`
  from Widmer's bound.

So the challenge theorem is now proved unconditionally for `n = 4`, `n = 5`,
and every prime `n ≥ 7` (the latter already via `SchmidtCount.theorem_1_prime`).
**The only remaining cases are `n = 3` and the composite degrees `n ≥ 6`.**

## Unconditional pieces of the challenge theorem

`SchmidtCount.subcaseIM_P2_isBigO`: the Case-II slice is `O(H^(n-1))` in every
degree `n ≥ 6`, unconditionally (both Case-II inputs are now theorems).

`SchmidtCount.theorem_1_prime`: for every **prime** `n ≥ 7`,
`theorem_1` holds *unconditionally* — the imprimitive input is vacuous in prime
degree, the Lemke Oliver–Thorne per-field fibre bound is a theorem in every
degree, and Schmidt's field count is now a theorem too.  In composite degree
`n ≥ 6` the same reduction leaves only Widmer's bound
(`SchmidtCount.theorem_1_of_schmidt_and_widmer_all`).

## Endpoints

* `FinalAssemblyM.theorem_1_of_caseII_imprimitive` — the challenge statement
  from `#SubcaseI_P2 = O(H^(n-1))` and `#ImprimitiveBad = O(H^(n-1))`;
* `FinalEndpoints.theorem_1_of_field_inputs` — from
  `PerFieldFibreBound n`, `FieldCountBound n β` (plus the exponent condition)
  and the imprimitive bound;
* `FinalEndpoints.theorem_1_of_literature_{three,four,five,six}` and
  `theorem_1_of_literature_prime_degree` — the degree-wise specialisations
  (`β = 1/2`, `1`, `1`, `(n+2)/4`, `(n+2)/4`).
* `PerFieldFibre.theorem_1_of_fieldCountBound_of_prime` and its specialisations
  `theorem_1_of_cubic_fieldCount`, `theorem_1_of_quintic_fieldCount`,
  `theorem_1_of_schmidt_of_prime` — the same endpoints with the per-field fibre
  bound discharged in prime degree;
* `PerFieldFibreAll.theorem_1_of_fieldCountBound` — the same, in **every**
  degree: the Lemke Oliver–Thorne input is now discharged everywhere, so the
  only remaining inputs are `FieldCountBound` and (for composite `n ≥ 6`)
  Widmer's imprimitive bound.  Degree-wise:
  `theorem_1_of_cubic_fieldCount_all` (`n = 3`, `β = 1/2` only),
  `theorem_1_of_quartic_fieldCount_all` (`n = 4`, `β = 1` only, the
  imprimitive input being the machine-checked `ImprimitiveBad_four_isBigO`),
  `theorem_1_of_quintic_fieldCount_all` (`n = 5`, `β = 1` only) and
  `theorem_1_of_schmidt_and_widmer` (`n ≥ 6`).

Nothing else remains: every other lemma in the corpus is unconditional.

## The per-field fibre bound is now a THEOREM in every degree

`PerFieldFibreAll` closes the composite-degree gap: `SubcaseI_P2 n H` consists
of polynomials with *primitive* Galois group, and a primitive group has no
proper subextension, since a proper intermediate field `ℚ ⊆ F ⊊ K_f` produces a
nontrivial block system for the action of `Gal(f)` on the roots of `f`
(`Commons.NumberTheory.NumberField.exists_nontrivial_block_of_intermediate`),
contradicting `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`.  Hence
`adjoin_eq_top_of_galPrimitive` holds and with it
`perFieldFibreBound_all : PerFieldFibreBound n` for every `n ≥ 3`.

## The imprimitive slice is now a THEOREM in every degree

`QuarticSymmBound` proves `#symmBox H = O(H^3)` (hence
`ImprimitiveBad_four_isBigO : #ImprimitiveBad 4 H = O(H^3)`) by
splitting `symmBox` into the diagonal `xa = 2c` (where the symmetry equation
factors) and the off-diagonal, and counting the latter through
`rad(x² - 4d)`:

* diagonal: `x² = 4d` or `a² = 4e`, one variable determined ⟹ `O(H^3)` directly;
* off-diagonal: `A = x² - 4d ≠ 0` and `A ∣ (xa-2c)²`, so `rad A ∣ xa - 2c` and for
  each `(x,d)` the admissible `c` lie in a single residue class mod `rad A`; the key
  arithmetic input is `∑_{A ≤ N} 1/rad A ≪ √N` (and `∑ 1/(√A rad A) = O(1)`), giving
  `∑_{x,d} 4H/rad(x²-4d) = O(H)`.

With `ImprimitiveBad_isBigO_complete`, the imprimitive input `#ImprimitiveBad n H = O(H^(n-1))`
is now available for *every* `n ≥ 3`: vacuous in prime degree (`n = 3, 5`), the
Chow–Dietmann count above for `n = 4`, and Widmer's `O(H^(n/2+2))` for `n ≥ 6`
(`ImprimitiveInput.ImprimitiveBad_isBigO_of_widmer`).

## The sharp per-field fibre exponent (Session-164)

The Case-II estimate is `(per-field fibre count) × (field count)`, Abel-summed:
`#{f ∈ SubcaseI_P2 n H : |Disc| ≤ X} ≪ H(log H)^{n-1}·X^{β−α}`, where `α` is the
discriminant exponent of the per-field fibre bound and `β` that of the field
count.  The project (and the paper) use `α = 1/(n(n-1))` (Ellenberg–Venkatesh
separation `house ≥ |Disc|^{1/(n(n-1))}/2`).  The **sharp** exponent is
`α = 1/2`: the height-`≤ H` polynomials cutting out `K` are the lattice points
of `𝓞 K` in the region `{|a_i| ≤ H}` (volume `≍ H(log H)^{n-1}`, covolume
`√|Disc K|`), giving `H(log H)^{n-1}/√|Disc K|`.

`Submission/Vdw/SharpFibre.lean` parameterises the whole chain by `α`:

* `PerFieldFibreBoundExp n _ α`, `CaseIICountBoundExp n β α`,
  `caseIICountBoundExp_of_field_inputs` (any `α < β`),
  `SubcaseIM_P2_isBigO_of_countBoundExp`, `theorem_1_of_field_inputs_exp`,
  `FieldCountBound_mono`, and the exponent lemmas `exponent_schmidt_sharp`
  (`n ≥ 5`), `exponent_quartic_sharp`, `exponent_cubic_sharp`;
* endpoints: `theorem_1_of_schmidt_sharp` (`n ≥ 5`, only the imprimitive bound
  remains), **`theorem_1_of_schmidt_sharp_prime`** (prime `n ≥ 5`,
  unconditional apart from the sharp fibre bound — this removes the need for
  Bhargava's exact quintic count), `theorem_1_of_schmidt_widmer_sharp`
  (composite `n ≥ 6` from Widmer), `theorem_1_of_quartic_sharp'` (`n = 4, 5`),
  `theorem_1_of_quartic_sharp`, `theorem_1_of_cubic_sharp`.

With `α = 1/2` the exponent condition `β − 1/2 < (n−2)/(2 + 4/weylM n)` holds
for the **classical** field-count exponents: `β = 1/2` (`n = 3`, Cohn),
`β = 1` (`n = 4`, Davenport–Heilbronn) and `β = (n+2)/4` (`n ≥ 5`,
**Schmidt — already a theorem of the project**).  So the *only* remaining new
input for `n ≥ 5` is the sharp per-field fibre bound
(`Commons.NumberTheory.NumberField.ncard_polys_height_covolume`, requested from
the fleet), together with Widmer's imprimitive bound for composite `n ≥ 6`.

The index refinement (`FieldCountBound n β` with `β = n/4`, from the per-field
discriminant count `#{K : |Disc K| = D} ≪ D^{(n+2)/4−1+ε}`) would in addition
remove Cohn's and Davenport–Heilbronn's counts; its algebraic crux is with the
fleet as `Commons.FieldTheory.Polynomial.ncard_index_ge_fixed_coeffs_le`.

## The `+ 1` sharp fibre bound (Session-164)

The pure sharp fibre bound is FALSE in the boundary regime
`Y ≪ √|Disc K|` (fleet counterexamples: `K = ℚ(ζ_p)` with `Y = 1`;
`K = ℚ(∛m)` with `Y ≍ |Disc K|^{1/3}`).  The correct statement is

  `#{f : M(f) ≤ Y, K_f ≅ K} ≤ C^n (1 + Y(log Y)^{n-1}/√|Disc K|)`.

`Submission/Vdw/SharpFibre.lean` carries the whole case-II chain in this form:
`PerFieldFibreBoundPlus`, `CaseIICountBoundPlus`,
`caseIICountBoundPlus_of_field_inputs`, `SubcaseIM_P2_isBigO_of_countBoundPlus`
(with the two exponent conditions `(2+4/M)β < n−1` and
`1+(2+4/M)(β−α) < n−1`), and the endpoints
`theorem_1_of_schmidt_plus` (`n ≥ 5`),
**`theorem_1_of_schmidt_plus_prime`** (prime `n ≥ 5` — the exact quintic count
is no longer needed), `theorem_1_of_schmidt_widmer_plus` (composite `n ≥ 6`),
`theorem_1_of_quartic_plus` (`n = 4`), `theorem_1_of_cubic_plus` (`n = 3`).

With the `+ 1` bound and the **classical** field-count exponents —
Cohn `β = 1/2` (`n = 3`), Davenport–Heilbronn `β = 1` (`n = 4`), Schmidt
`β = (n+2)/4` (`n ≥ 5`, already a theorem) — every degree `n ≥ 3` closes.  The
remaining inputs are exactly: the `+ 1` fibre bound
(`Commons.NumberTheory.NumberField.ncard_polys_covolume_add_one`, requested), the
two small-degree field counts, and Widmer's imprimitive bound for composite
`n ≥ 6`.

## The fibre-exponent parameterisation and the index-refinement endpoint

`Submission/Vdw/SharpFibre.lean` parameterises the whole Case-II chain by the
per-field fibre exponent `α` and the field-count exponent `β`:

* `PerFieldFibreBoundExp n _ α`, `CaseIICountBoundExp n β α`,
  `caseIICountBoundExp_of_field_inputs`, `SubcaseIM_P2_isBigO_of_countBoundExp`,
  `theorem_1_of_field_inputs_exp` (condition `1 + (2+4/M)(β−α) < n−1`);
* the `+ 1` (lattice-point-with-boundary) variant `PerFieldFibreBoundPlus`,
  `CaseIICountBoundPlus`, `caseIICountBoundPlus_of_field_inputs`,
  `SubcaseIM_P2_isBigO_of_countBoundPlus` (conditions `(2+4/M)β < n−1` **and**
  `1 + (2+4/M)(β−α) < n−1`), `theorem_1_of_field_inputs_plus`;
* **`theorem_1_of_indexFieldCount (n ≥ 4) (FieldCountBound n (n/4))`**: with the
  *unconditional* fibre exponent `α = 1/(n(n−1))`
  (`PerFieldFibreAll.perFieldFibreBound_all`) and the index-refined field count
  `β = n/4`, the exponent condition holds for `n ≥ 4` (`exponent_index_refine`),
  so **Davenport–Heilbronn (`n = 4`) and Bhargava (`n = 5`) become unnecessary**
  once the index-refinement arithmetic is formalised; also
  `theorem_1_of_indexFieldCount_four_five`, `theorem_1_of_indexFieldCount_prime`,
  `theorem_1_of_indexFieldCount_widmer`;
* the sharp-exponent endpoints (`theorem_1_of_schmidt_plus_prime`, …), conditional
  on the sharp per-field fibre bound, which is **false in general** (four
  counterexample families found by the fleet: `ℚ(ζ_p)` with `Y = 1`; `ℚ(∛m)` with
  `Y ≍ |Disc|^{1/3}`; the same in the regimes `|Disc| ≤ Y^2, Y^3`; and — for the
  `+ 1` form — the subfield cosets of `ℚ(√a, √b)`).  The corrected statement
  (with primitivity *and* the region regime `|Disc K| ≤ Y^{2+1/n}`) is with the
  fleet as `Commons.NumberTheory.NumberField.ncard_polys_covolume_primitive_regime`.

Bhargava's Proposition 4.x is now a theorem of the commons:
`Commons.FieldTheory.Polynomial.ncard_index_ge_fixed_coeffs_le` — for a field `K`
with `char K ∤ n!`, prescribed coefficients in degrees `k, …, n−1` and index
`≥ k`, there are at most `(n+1)·n!·2^n` monic degree-`n` polynomials.

-/

/-!
# SESSION-167: degree 3 is UNCONDITIONAL — the elementary cyclic-cubic field count

`theorem_1` is now a theorem in degrees `3`, `4`, `5` and in every prime degree
`≥ 7`.  The remaining family is the **composite** degrees `n ≥ 6`, which need
Widmer's imprimitive bound (`ImprimitiveBad_isBigO_of_widmer`).

New modules:

* **`Submission/Vdw/CubicSign.lean`** (0 sorries) — the sign of the
  discriminant in degree three, obtained from the *infinite-place* argument
  instead of Galois theory of permutations:
  * `gal_card_eq_three_of_lt_six` — an irreducible cubic over `ℚ` whose Galois
    group has order `< 6` has order exactly `3` (transitivity +
    orbit–stabilizer);
  * `finrank_splittingField` — the splitting field has degree `3`;
  * `isTotallyReal_splittingField` — the splitting field is totally real
    (`InfinitePlace.even_finrank_of_not_isUnramified`: a ramified infinite
    place would force an even degree);
  * `discr_splittingField_pos`, and `discr_Kpoly_pos` — **the field of a cubic
    in the region has positive discriminant** (the root field `K_f` is a
    `ℚ`-subalgebra of the splitting field of the same dimension, hence equal to
    it; `Algebra.finrank_eq_one_iff_bijective_algebraMap` gives the algebra
    equivalence).

* **`Submission/Vdw/CubicFieldCount.lean`** (0 sorries) — the elementary count
  of cyclic cubic fields, replacing Cohn's theorem (and avoiding
  Kronecker–Weber entirely):
  * `eq_three_term`, `classPoly_eq_three_term` — the class polynomial is
    `X³ + bX + c`;
  * `exists_discr_classPoly_eq_classDisc_mul_sq` — Dedekind's index relation,
    read with the *positive* discriminant;
  * `discJ_dvd_classPoly_coeff` — the large-prime part `fl = discJ 3 D 1`
    divides both `b` and `c` (squarefullness + Lemma 24 + `polyIndex ≥ 2` ⟹
    the reduction is `X³`);
  * `exists_cubic_data` — decomposing positivity: `b < 0`, `b = -fl·B₁`,
    `c = fl·γ`, `D = d·fl²`, and the **definite binary quadratic equation**
    `27γ² + d·m² = 4·fl·B₁³`, with `B₁ ≤ cubicK0`, `d ≤ cubicS`;
  * `fieldCountBound_three_cyclic` — **`FieldCountBound 3 (1/2 + 1/20)`**:
    the class is determined by `(fl, B₁, γ)`, and
    `Commons.NumberTheory.Int.ncard_binary_quadratic_repr_le_bounded` bounds the
    number of `(γ, m)` for each `(fl, B₁, d)`, giving
    `≪ (√Y)·Y^{1/20} = Y^{1/2+1/20}`;
  * **`theorem_1_three`** — the challenge theorem in degree three,
    unconditionally.

Axioms of every new theorem: `propext`, `Classical.choice`, `Quot.sound`.

## Remaining for `theorem_1`

Only the composite degrees `n ≥ 6`: `#ImprimitiveBad n H = O(H^{n/2+2})`
(Widmer, "On number fields with nontrivial subfields"), consumed through
`ImprimitiveInput.ImprimitiveBad_isBigO_of_widmer` and
`theorem_1_of_indexRefined_widmer`.  (For prime `n` the imprimitive part is
empty; for `n = 4` it is the machine-checked `ImprimitiveBad_four_isBigO`.)
-/

namespace Submission.Vdw

/-- Sanity check: the endpoints are present and typecheck at the challenge
statement.  (This `example` is proof-irrelevant documentation.) -/
example (n : ℕ) (hn : 3 ≤ n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_caseII_imprimitive n hn h2 h4

/-- Sanity check: the challenge theorem in prime degree `≥ 7`, unconditionally. -/
example (n : ℕ) (hn : 7 ≤ n) (hp : Nat.Prime n) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_prime n hn hp

/-- Sanity check: the degree-three endpoint, with no per-field fibre input. -/
example (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_cubic_fieldCount_all hSC

/-- Sanity check: **degree three is unconditional** (SESSION-167). -/
example : (fun H : ℕ => (E 3 H : ℝ)) =O[atTop]
    (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) := theorem_1_three

/-- Sanity check: the elementary cyclic-cubic field count. -/
example : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2 + 1 / 20) :=
  fieldCountBound_three_cyclic

/-! ## SESSION-168 — the imprimitive slice sliced by the block system

`Submission/Vdw/ImprimitiveBlock.lean` (imported by `Helpers`) makes the last
missing input of `theorem_1` — Widmer's `#ImprimitiveBad n H = O(H^(n/2+2))`
for the composite degrees `n ≥ 6` — **per block system**:

* `imprimitiveBad_has_block`: `f ∈ ImprimitiveBad n H` admits a nontrivial
  block `B`; with `k = B.ncard` (block size) and `m` the number of blocks one
  has `2 ≤ k`, `2 ≤ m`, `k * m = n`.
* `ImprimitiveBlockBound`: the per-`(k,m)` count `#(k,m)-slice ≤ C·Y^(k+m)`
  (Widmer's `n + e` with `n = k`, `e = m`).
* `imprimitiveBad_isBigO_of_blockBound`, `theorem_1_of_blockBound`: the
  challenge theorem for composite `n ≥ 6` from that sliced input alone.

The blocking remark (see `Roadmap.lean` SESSION-168): the naive slicing by the
block size alone with exponent `k+1` is **false** — the family `f(X) = g(X²)`
has block size `2` and `≍ H^(n/2)` members. -/


/-!
## SESSION-174 (the imprimitive slice: the naive Galois action)

The blocker of SESSION-172/173 — the unprovable `hbridge` hypothesis
(`↑(galActionHom p p.SplittingField σ x) = σ ↑x`, false because Mathlib's
self-action is a *conjugation* by the splitting-field lift) — is REMOVED:

* `Submission/Vdw/BlockAction.lean` defines the naive action (`galRootPermN`,
  `galFinHomN`), proves the equivariance `σ (rootOf i) = rootOf (galFinHomN σ i)`
  unconditionally, shows the two `Fin`-indexed representations are conjugate
  (`galFinHom_conj`, `galFinHom_range_eq`), that blocks transfer under the
  conjugation (`isBlock_map_conj_iff`), and that the project's `HasBlockSize`
  agrees with the naive block condition (`hasBlockSize_iff`).
* `Submission/Vdw/BlockPolyAction.lean` transfers the block-polynomial
  dictionary (`blockPoly_map_galN`, `blockPoly_mapN_eq_iff`,
  `mem_blockField_fixingSubgroup_iffN`).
* `Submission/Vdw/BlockPolyL.lean` provides `blockPoly_coeff_mem`, `blockPolyL`
  (the block polynomial over its field of definition), `blockPolyL_coeff`,
  `blockPolyL_map_val` and `galFinHomN_pretransitive`.

All three modules are green with clean axioms; the counting architecture that
uses them is written up in `Submission/Vdw/Roadmap.lean` (SESSION-174).  The
remaining gap of `theorem_1` is unchanged: the imprimitive slice for composite
`n ≥ 6`.
-/

/-!
## SESSION-175: the structural dictionary complete, the Mahler bounds proved

New modules (green, clean axioms, **not yet imported by `Helpers.lean`**):

* `Submission/Vdw/BlockRank.lean` — `finrank_blockField_eq_card_orbit`
  (`[blockField p hsep B : ℚ] = #(translate orbit of B)`), via the block
  stabilizer/fixing-subgroup identification and orbit–stabiliser.  This is the
  `[L : ℚ] = m` input of the imprimitive count.
* `Submission/Vdw/BlockNorm.lean` — the set-indexed block dictionary
  (`setFin`, `orbitF`, `spoly`, `sfield`, `spolyL`, `spoly_factors`) and
  **`normIdentity`**:
  `∏_{ψ : L →ₐ[ℚ] ℂ} ψ(P_L) = p.map (algebraMap ℚ ℂ)`, i.e. the polynomial is
  recovered from the block polynomial over its field of definition.  Proved
  through the bijection `orbit ≃ (L →ₐ[ℚ] ℂ)` (`blkEmbedOrbit`).
* `Submission/Vdw/BlockMahler.lean` — `mahlerMeasure_mem_Box_le`
  (`M(f_ℂ) ≤ (n+1)(H+1)` for `f ∈ Box n H`),
  `mahlerK_spolyL_coeff_le` (`mahlerK L c_j ≤ 2^{|B|[L:ℚ]} M(p)`) and
  `mahlerK_spolyL_gamma_le` (same for the generator `Σ μ_j c_j`).
* `Submission/Vdw/SliceCount.lean` — **the imprimitive slice count**: the chosen
  block data of a slice polynomial (`sliceIrred`, `sliceSep`, `sliceBlock`,
  `sliceL`, `slicePL`, `slicePsi`), `slice_finrank`, `adjoin_coeff_eq_top_k`,
  `muGood_covers` and the covering `imprimSlice_subset_iUnion_muGood`; the
  isomorphism `sliceEquiv : ↥L ≃ₐ[ℚ] ↥ℚ(ψ(γ))` (`finrank_adjoin_sliceZ`), the
  transported block polynomial `sliceQB` with the **norm identity over `ℚ(b)`**
  (`slice_normIdentityB`), the Mahler bounds
  (`mahlerK_sliceQB_coeff_le`, `mahlerK_sliceGamma_le`), the coefficient-tuple
  injection `slice_tuple_inj`, the fibre count `slice_fiber_ncard_le`
  (`≪ H^{k-1}(log H)^{(m-1)(k-1)}`), the generator count
  `slice_image_ncard_le` (`≪ H^m`), the slice bound `imprimSlice_ncard_le`
  (`≪ H^{k+m}`), and
  **`imprimitiveSliceBoundExp : ImprimitiveSliceBoundExp n (fun k m => k + m)`
  for every `n ≥ 6`**.

## SESSION-176: `theorem_1` IS COMPLETE

`Submission/Vdw/SliceCount.lean` closes the last gap: the imprimitive slice for
composite `n ≥ 6` is `O(H^{k+m})` (hence `O(H^{n-1})` since `k*m = n ≥ 6` and
`k, m ≥ 2` force `(k-1)(m-1) ≥ 2`), and `Submission.lean` now dispatches

* `n = 3` → `Vdw.theorem_1_three` (Cohn, elementary replacement),
* `n = 4, 5` → `Vdw.theorem_1_of_indexRefined_four_five` (Bhargava's index
  refinement),
* prime `n ≥ 7` → `Vdw.theorem_1_prime` (Schmidt's field count),
* composite `n ≥ 6` → `Vdw.theorem_1_of_sliceExp` with
  `Vdw.imprimitiveSliceBoundExp`.

`#print axioms Submission.theorem_1` = `[propext, Classical.choice, Quot.sound]`.

The remaining files listed below are the earlier layers of the argument.
-/

end Submission.Vdw
