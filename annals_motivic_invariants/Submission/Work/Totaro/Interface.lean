import Submission.Work.Totaro.Paper
import Submission.Work.CY3.Main
import Submission.Work.K3.Main

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Totaro.Interface` — the two `TotaroInput`s and the consumers' distinguishings

This module is the **interface of the Totaro area**: everything a consumer needs, in one import.

## 1. The two chapters' `TotaroInput`s, from the cohomological input

`Work.CY3.TotaroInput` and `Work.K3.TotaroInput` are the named inputs of the two delivered L-link
chapters (`Submission/Work/CY3/Totaro.lean`, `Submission/Work/K3/HL.lean`).  Both are *produced*
here from the cohomological input `Work.Totaro.CohDistinguishing` at the chapters' own
Picard-rank-one predicates:

* `Work.Totaro.totaroInput_CY3 (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜)) :
  Work.CY3.TotaroInput 𝕜`
* `Work.Totaro.totaroInput_K3 (h : CohDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜)) :
  Work.K3.TotaroInput 𝕜`

The proof is the abstract implication layer of `Submission/Work/Totaro/Cohomology.lean`.

## 2. The `z₀`-residue-field distinguishing the `cInv` count needs

Both chapters compute the coefficient of their link at a base point whose residue field is
`κ(Z)(t)` — the *cylinder* function field of the first centre — and need the two exceptional
divisors of the link to be distinguished by their residue fields:

```lean
¬ ResEquiv 𝕜 y x      -- κ(y) ≇ κ(x), i.e. κ(Z)(t) ≇ κ(Z')(t)
```

This is the input `not_resEquiv_yx` of `Work.CY3.CY3Link` / `Work.K3.K3Link`.  It follows from
Totaro's input (`Work.CY3.CY3Data.not_resEquiv_yx_of_totaro`,
`Work.K3.K3Data.not_resEquiv_yx_of_totaro`) through the `ℙ¹`-bundle bridge of the link data
(`Work.Totaro.P1BundleBridge`).  The statements of this module are the same, with the cohomological
input in place of `TotaroInput`:

* `Work.Totaro.not_resEquiv_of_cohom` — the abstract form: a per-pair certificate plus a bridge;
* `Work.Totaro.CY3Data_not_resEquiv_yx`, `Work.Totaro.K3Data_not_resEquiv_yx` — on the two
  chapters' link data;
* `Work.Totaro.CY3Data_exists_cInv_ne_zero` — the `Cr 𝕜 5` existential of the CY3 chapter, with
  the cohomological input in place of `TotaroInput`.

## 3. End to end

The two challenge-level statements of the delivered chapters, with `TotaroInput` replaced by the
cohomological input:

* `Work.Totaro.not_gen_of_CY3_infiniteField_five` and `…_of_le` — Theorem 1.2 (3) of the challenge
  (`n ≥ 5` over an infinite field);
* `Work.Totaro.not_gen_of_K3_kSubC` and `…_of_le` — Theorem 1.2 (2) of the challenge
  (`n ≥ 4` over a subfield of `ℂ`).

Each is a one-line application of the corresponding chapter theorem, so a consumer may use either
route: the chapter's own `TotaroInput` hypothesis, or `CohDistinguishing`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. The two `TotaroInput`s from the cohomological input -/

/-- **Totaro's theorem for the CY3 chapter, from the cohomological input**: the named input
`Work.CY3.TotaroInput` (used by `Work.CY3.exists_cInv_ne_zero_infiniteField` and
`Work.CY3.not_gen_of_CY3_infiniteField`), produced from `CohDistinguishing` at the CY3
Picard-rank-one predicate. -/
theorem totaroInput_CY3 (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜)) :
    Work.CY3.TotaroInput 𝕜 :=
  ⟨fun X Y _ _ hX hY pX pY hne =>
    not_stablyBirat_of_not_iso_of_distinguishing h X Y hX hY pX pY hne⟩

/-- **Totaro's theorem for the K3 chapter, from the cohomological input**: the named input
`Work.K3.TotaroInput` (used by `Work.K3.exists_cInv_ne_zero_kSubC` and
`Work.K3.not_gen_of_K3_kSubC`), produced from `CohDistinguishing` at the K3 geometric
Picard-rank-one predicate. -/
theorem totaroInput_K3 (h : CohDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜)) :
    Work.K3.TotaroInput 𝕜 :=
  ⟨fun X Y _ _ hX hY pX pY hne =>
    not_stablyBirat_of_not_iso_of_distinguishing h X Y hX hY pX pY hne⟩

/-- **Totaro's theorem for the CY3 chapter, from the *per-pair* certificates**: the same as
`Work.Totaro.totaroInput_CY3`, but from the weakest form of the named input. -/
theorem totaroInput_CY3_of_separation
    (h : CohSeparationDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜)) :
    Work.CY3.TotaroInput 𝕜 :=
  ⟨fun X Y _ _ hX hY pX pY hne =>
    CohSeparation.not_stablyBirational (h X Y hX hY pX pY hne).some⟩

/-- **Totaro's theorem for the K3 chapter, from the *per-pair* certificates.** -/
theorem totaroInput_K3_of_separation
    (h : CohSeparationDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜)) :
    Work.K3.TotaroInput 𝕜 :=
  ⟨fun X Y _ _ hX hY pX pY hne =>
    CohSeparation.not_stablyBirational (h X Y hX hY pX pY hne).some⟩

/-- **Totaro's theorem for the CY3 chapter, from the paper's `cor-CYnSB`** (recorded in
`Submission/Work/Totaro/Paper.lean`, where it is derived from `thm:BurtCY` + `lem-stbirCY`). -/
theorem totaroInput_CY3_of_CorCYnSB (h : CorCYnSB 𝕜 (Work.CY3.PicardRankOne 𝕜)) :
    Work.CY3.TotaroInput 𝕜 :=
  ⟨CorCYnSB.not_stablyBirational_of_not_iso h⟩

/-- **Totaro's theorem for the K3 chapter, from the paper's `cor-CYnSB`.** -/
theorem totaroInput_K3_of_CorCYnSB (h : CorCYnSB 𝕜 (Work.K3.PicardRankOneGeom 𝕜)) :
    Work.K3.TotaroInput 𝕜 :=
  ⟨CorCYnSB.not_stablyBirational_of_not_iso h⟩

/-! ## 1b. The per-link (concrete pair) cohomological input

The named input `CohDistinguishing` of §1 quantifies over *all* pairs of non-isomorphic `K`-trivial
varieties of Picard rank one.  Mathematically, what the cohomology theory actually gives is the
certificate for the *two concrete centres* of a link — the Ito–Miura–Okawa–Ueda computation of
`H³(Z_𝕜)(1)` for the CY3 centres, and the `H²` (Hodge structure) of the K3 surfaces for the K3
centres.  These are recorded here as the per-link inputs `CY3CentreCohomology` /
`K3CentreCohomology`, so that a consumer may assume exactly the concrete computation rather than a
universal statement. -/

/-- **Named input: the cohomological certificate for the two centres of a CY3 datum**
(`H³(-)(1)` with the Tate twist; Ito–Miura–Okawa–Ueda). -/
def CY3CentreCohomology (𝕜 : Type) [Field 𝕜] (D : Work.CY3.CY3Data 𝕜) : Prop :=
  Nonempty (CohSeparation 𝕜 D.Z D.Z')

/-- **Named input: the cohomological certificate for the two centres of a K3 datum** (`H²` with its
Hodge structure; Hassett–Lai / Oguiso). -/
def K3CentreCohomology (𝕜 : Type) [Field 𝕜] (D : Work.K3.K3Data 𝕜) : Prop :=
  Nonempty (CohSeparation 𝕜 D.S D.S')

/-- The universal cohomological input gives the per-link certificate. -/
theorem CY3CentreCohomology.of_distinguishing (D : Work.CY3.CY3Data 𝕜)
    (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜)) (hne : ¬ IsoOver 𝕜 D.Z D.Z') :
    CY3CentreCohomology 𝕜 D :=
  (h D.Z D.Z' D.isKTrivial_Z D.isKTrivial_Z' D.picardOne_Z D.picardOne_Z' hne).map
    CohKunneth.toCohSeparation

/-- The universal cohomological input gives the per-link certificate (K3). -/
theorem K3CentreCohomology.of_distinguishing (D : Work.K3.K3Data 𝕜)
    (h : CohDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜)) (hne : ¬ IsoOver 𝕜 D.S D.S') :
    K3CentreCohomology 𝕜 D :=
  (h D.S D.S' D.kTrivial D.kTrivial' D.picardOne D.picardOne' hne).map
    CohKunneth.toCohSeparation

/-- **The CY3 link's non-triviality input from the per-link certificate**: `κ(y) ≇ κ(x)`.  Note
that the non-isomorphism of the two centres is *not* a separate hypothesis in this per-link form:
the certificate already forbids `Z` and `Z'` from being stably birational, hence (by
`Work.Totaro.StablyBirational_of_isoOver`) from being isomorphic. -/
theorem CY3Data_not_resEquiv_yx_of_centre (D : Work.CY3.CY3Data 𝕜)
    (h : CY3CentreCohomology 𝕜 D) :
    ¬ ResEquiv 𝕜 D.y D.x :=
  fun hres => h.some.not_stablyBirational (D.bridge hres)

/-- **The K3 link's non-triviality input from the per-link certificate** (again with no separate
non-isomorphism hypothesis). -/
theorem K3Data_not_resEquiv_yx_of_centre (D : Work.K3.K3Data 𝕜)
    (h : K3CentreCohomology 𝕜 D) :
    ¬ ResEquiv 𝕜 D.y D.x :=
  fun hres => h.some.not_stablyBirational (D.bridge hres)

/-- **The CY3 chapter's `Cr 𝕜 5` existential from the per-link certificate** (no universal
quantification over pairs). -/
theorem CY3Data_exists_cInv_ne_zero_of_centre (D : Work.CY3.CY3Data 𝕜)
    (h : CY3CentreCohomology 𝕜 D) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)) ≠ 0 :=
  (Work.CY3.CY3Link.exists_cInv_ne_zero
    { toCY3Data := D
      not_resEquiv_yx := CY3Data_not_resEquiv_yx_of_centre D h })

/-- **The K3 chapter's `Cr 𝕜 4` existential from the per-link certificate**. -/
theorem K3Data_exists_cInv_ne_zero_of_centre (D : Work.K3.K3Data 𝕜)
    (h : K3CentreCohomology 𝕜 D) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 4),
      cInv 𝕜 z₀ (φ : (Work.K3.Affine4 𝕜).BirationalMap (Work.K3.Affine4 𝕜)) ≠ 0 :=
  (Work.K3.K3Link.exists_cInv_ne_zero
    { toK3Data := D
      not_resEquiv_yx := K3Data_not_resEquiv_yx_of_centre D h })

/-! ## 2. The residue-field distinguishing -/

/-- **The abstract residue-field distinguishing.**  Let `y`, `x` be two points of a scheme `P`
(the two exceptional divisors of an L-link) whose residue fields are the cylinder function fields
`κ(Z)(t)` and `κ(Z')(t)` of two centres `Z`, `Z'` (this is the content of the bridge hypothesis,
which for the two links is a field of `Work.CY3.CY3Data` resp. `Work.K3.K3Data`).  If the pair
`(Z, Z')` is separated by the cohomological invariant, then `κ(y) ≇ κ(x)`.

This is the `¬ ResEquiv 𝕜 y x` input of the two L-links, and therefore the reason the
`[κ(Z)(t)]`-coefficient of the link is computable at the base point `z₀`. -/
theorem not_resEquiv_of_cohom {P Z Z' : Scheme.{0}} [P.Over (Spec (.of 𝕜))]
    [Variety 𝕜 Z] [Variety 𝕜 Z'] {y x : P}
    (C : CohSeparation 𝕜 Z Z') (bridge : P1BundleBridge 𝕜 (Z := Z) (Z' := Z') y x) :
    ¬ ResEquiv 𝕜 y x :=
  fun hres => C.not_stablyBirational (bridge hres)

/-- The same, from the universal cohomological input rather than a per-pair certificate. -/
theorem not_resEquiv_of_distinguishing {P Z Z' : Scheme.{0}} [P.Over (Spec (.of 𝕜))]
    [Variety 𝕜 Z] [Variety 𝕜 Z'] {y x : P}
    {Pic1 : Pic1Family 𝕜} (h : CohDistinguishing 𝕜 Pic1) (hZ : IsKTrivial 𝕜 Z)
    (hZ' : IsKTrivial 𝕜 Z') (pZ : Pic1 Z) (pZ' : Pic1 Z') (hne : ¬ IsoOver 𝕜 Z Z')
    (bridge : P1BundleBridge 𝕜 (Z := Z) (Z' := Z') y x) :
    ¬ ResEquiv 𝕜 y x :=
  fun hres => CohKunneth.not_stablyBirational (h Z Z' hZ hZ' pZ pZ' hne).some (bridge hres)

/-! ## 3. On the two chapters' link data -/

/-- **The CY3 link's non-triviality input, from the cohomological input.**
`Work.CY3.CY3Data.not_resEquiv_yx_of_totaro` with `Work.CY3.TotaroInput` replaced by
`CohDistinguishing`. -/
theorem CY3Data_not_resEquiv_yx (D : Work.CY3.CY3Data 𝕜)
    (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜)) (hne : ¬ IsoOver 𝕜 D.Z D.Z') :
    ¬ ResEquiv 𝕜 D.y D.x :=
  Work.CY3.CY3Data.not_resEquiv_yx_of_totaro D
    ((totaroInput_CY3 h).toInputAt 𝕜 D.isKTrivial_Z D.isKTrivial_Z' D.picardOne_Z
      D.picardOne_Z') hne

/-- **The K3 link's non-triviality input, from the cohomological input.**
`Work.K3.K3Data.not_resEquiv_yx_of_totaro` with `Work.K3.TotaroInput` replaced by
`CohDistinguishing`. -/
theorem K3Data_not_resEquiv_yx (D : Work.K3.K3Data 𝕜)
    (h : CohDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜)) (hne : ¬ IsoOver 𝕜 D.S D.S') :
    ¬ ResEquiv 𝕜 D.y D.x :=
  Work.K3.K3Data.not_resEquiv_yx_of_totaro D
    ((totaroInput_K3 h).toInputAt 𝕜 D.kTrivial D.kTrivial' D.picardOne D.picardOne') hne

/-- **The CY3 chapter's `Cr 𝕜 5` existential, from the cohomological input**: the exact
existential consumed by `Work.Motivic.not_gen_of_cInv_ne_zero` for `n = 5`. -/
theorem CY3Data_exists_cInv_ne_zero (D : Work.CY3.CY3Data 𝕜)
    (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜)) (hne : ¬ IsoOver 𝕜 D.Z D.Z') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)) ≠ 0 :=
  Work.CY3.CY3Data.exists_cInv_ne_zero D
    ((totaroInput_CY3 h).toInputAt 𝕜 D.isKTrivial_Z D.isKTrivial_Z' D.picardOne_Z
      D.picardOne_Z') hne

/-- **The K3 chapter's `Cr 𝕜 4` existential, from the cohomological input**. -/
theorem K3Data_exists_cInv_ne_zero (D : Work.K3.K3Data 𝕜)
    (h : CohDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜)) (hne : ¬ IsoOver 𝕜 D.S D.S') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 4),
      cInv 𝕜 z₀ (φ : (Work.K3.Affine4 𝕜).BirationalMap (Work.K3.Affine4 𝕜)) ≠ 0 :=
  Work.K3.K3Data.exists_cInv_ne_zero D
    ((totaroInput_K3 h).toInputAt 𝕜 D.kTrivial D.kTrivial' D.picardOne D.picardOne') hne

/-- **Theorem 1.2 (3) of the challenge at `n = 5`, from the per-link certificate only**: the
geometric input of `thm:CY3` (`Work.CY3.CY3Input`) and the cohomological certificate for the two
concrete centres — no universal quantification over pairs, and no separate non-isomorphism
hypothesis on the centres (it is a consequence of the certificate). -/
theorem not_gen_of_CY3_infiniteField_five_of_centre (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (I : Work.CY3.CY3Input 𝕜) (h : CY3CentreCohomology 𝕜 I.data) :
    ¬ GenByPseudoRegularizable 𝕜 5 :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 5 (CY3Data_exists_cInv_ne_zero_of_centre I.data h)

/-- **Theorem 1.2 (2) of the challenge at `n = 4`, from the per-link certificate only**: the
arithmetic and geometric inputs of `thm-HL` (`Work.K3.TerasomaInput`,
`Work.K3.HassettLaiTheorem`, whose descent produces the `𝕜`-model of the link) and the
cohomological certificate for the two concrete centres of that model. -/
theorem not_gen_of_K3_kSubC_of_centre (𝕜 : Subfield ℂ) (T : Work.K3.TerasomaInput)
    (h : Work.K3.HassettLaiTheorem T)
    (hd : K3CentreCohomology ↥𝕜 (Work.K3.toHLDescent h 𝕜).data) :
    ¬ GenByPseudoRegularizable ↥𝕜 4 :=
  Work.Motivic.not_gen_of_cInv_ne_zero ↥𝕜 4
    (K3Data_exists_cInv_ne_zero_of_centre (Work.K3.toHLDescent h 𝕜).data hd)

/-! ## 4. End to end: the two challenge statements -/

/-- **Theorem 1.2 (3) of the challenge at `n = 5`** (`Cr₅(𝕜)` is not generated by
pseudo-regularizable elements, over an infinite field), with `Work.CY3.TotaroInput` replaced by the
cohomological input. -/
theorem not_gen_of_CY3_infiniteField_five (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (I : Work.CY3.CY3Input 𝕜) (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜)) :
    ¬ GenByPseudoRegularizable 𝕜 5 :=
  Work.CY3.not_gen_of_CY3_infiniteField_five 𝕜 I
    ((totaroInput_CY3 h).toInputAt 𝕜 I.data.isKTrivial_Z I.data.isKTrivial_Z'
      I.data.picardOne_Z I.data.picardOne_Z')

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`**, with the cohomological input and the
named stabilisation step. -/
theorem not_gen_of_CY3_infiniteField_of_le {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    [Infinite 𝕜] (I : Work.CY3.CY3Input 𝕜) (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜))
    (S : Work.CY3.CY3Stabilisation 𝕜 n) : ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.CY3.not_gen_of_CY3_infiniteField hn 𝕜 I
    ((totaroInput_CY3 h).toInputAt 𝕜 I.data.isKTrivial_Z I.data.isKTrivial_Z'
      I.data.picardOne_Z I.data.picardOne_Z') S

/-- **Theorem 1.2 (2) of the challenge at `n = 4`** (`Cr₄(𝕜)` is not generated by
pseudo-regularizable elements, for every subfield `𝕜 ⊆ ℂ`), with `Work.K3.TotaroInput` replaced
by the cohomological input. -/
theorem not_gen_of_K3_kSubC (𝕜 : Subfield ℂ) (T : Work.K3.TerasomaInput)
    (h : Work.K3.HassettLaiTheorem T) (hd : CohDistinguishing ↥𝕜 (Work.K3.PicardRankOneGeom ↥𝕜)) :
    ¬ GenByPseudoRegularizable ↥𝕜 4 :=
  Work.K3.not_gen_of_K3_kSubC 𝕜 T h
    ((totaroInput_K3 hd).toInputAt ↥𝕜 (Work.K3.toHLDescent h 𝕜).data.kTrivial (Work.K3.toHLDescent h 𝕜).data.kTrivial'
      (Work.K3.toHLDescent h 𝕜).data.picardOne (Work.K3.toHLDescent h 𝕜).data.picardOne')

/-- **Theorem 1.2 (2) of the challenge for `n ≥ 4`**, with the cohomological input and the named
stabilisation step. -/
theorem not_gen_of_K3_kSubC_of_le {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ)
    (T : Work.K3.TerasomaInput) (h : Work.K3.HassettLaiTheorem T)
    (hd : CohDistinguishing ↥𝕜 (Work.K3.PicardRankOneGeom ↥𝕜)) (S : Work.K3.K3Stabilisation ↥𝕜 n) :
    ¬ GenByPseudoRegularizable ↥𝕜 n :=
  Work.K3.not_gen_of_K3_kSubC_of_le hn 𝕜 T h
    ((totaroInput_K3 hd).toInputAt ↥𝕜 (Work.K3.toHLDescent h 𝕜).data.kTrivial (Work.K3.toHLDescent h 𝕜).data.kTrivial'
      (Work.K3.toHLDescent h 𝕜).data.picardOne (Work.K3.toHLDescent h 𝕜).data.picardOne') S

end

end Work.Totaro
