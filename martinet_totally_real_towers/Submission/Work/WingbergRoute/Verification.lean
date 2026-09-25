import Mathlib
import Submission.Work.WingbergRoute.Defs
import Submission.Work.CruxOneByte.crux_iff_twoTorsionH3_le_two

/-!
# `Work.WingbergRoute.Verification` -- the literature comparison, machine-checked

This module records, with proofs, the relation between

* the statement of Wingberg's duality as it appears in the literature
  (Neukirch--Schmidt--Wingberg, *Cohomology of Number Fields*, Ch. VIII §8 Thm. 8.8.1 with
  Lemma 8.8.4, in the normalisation of Hajir--Maire--Ramakrishna, arXiv:2103.09508, Thm. 1.1 and
  Cor. `prop:r-d_wingberg`, i.e. `Ĥ^i(G_∅, O_{Kc_∅}^×) ≅ Ĥ^{3-i}(G_∅,ℤ)^∨` for `S = T = ∅`,
  `A = ℤ`, `𝔠` the class of finite `2`-groups),
* the statement `Work.ShafarevichKoch.WingbergDuality` formalised in this workspace,
* the statement of Shafarevich's relation-rank bound as quoted by D. C. Mayer,
  arXiv:1605.09617, Thm. `thm:RelationRank` (the `S = ∅` case with `θ = 1`), and
* the forms actually consumed downstream (`Work.ShafarevichKoch.KcProTwoPresentationInput`,
  `Work.ShafarevichKoch.KochInjection`, `Work.RelatorRank.ContH2DimLe`).

The conclusion of the comparison, in the vocabulary of the deliverable, is

* **the formal statement `Work.ShafarevichKoch.WingbergDuality` is sound and needs no correction
  for the consumer**: it is precisely the `i = 0` and `i = 1` instances of the literature's
  duality, with the `∃ N : Subgroup (RingUnit Kc)` slot correctly encoding the universal-norm
  quotient `Ĥ⁰(G_∅, O_{Kc_∅}^×) = (𝓞 Kc)ˣ / N_{Kc_∅/Kc}(O_{Kc_∅}^×)`, and the Pontryagin dual
  taken into `ℂˣ` instead of `ℚ/ℤ` (equivalent for a *finite* abelian group, and finiteness is
  asserted); no finiteness, generation or ramification hypothesis is missing because the base
  field is the fixed imaginary quadratic `Kc` (no real places, `ζ₂ = -1 ∈ Kc`);
* the two classical statements -- Shafarevich's `d₂ ≤ d₁ + r + θ` with `r = r₁+r₂-1`, `θ = 1`,
  and Wingberg's `df ≤ d₂(O_K^×) = r₁+r₂` -- are *the same inequality*, because
  `(r₁+r₂-1) + 1 = r₁+r₂`; this is `Work.WingbergRoute.unitTwoRank_eq_unitsRank_add_one`.

## Main declarations

* `Work.WingbergRoute.unitTwoRank_eq_unitsRank_add_one`;
* `Work.WingbergRoute.wingbergDualityFaithful_iff`,
  `Work.WingbergRoute.wingbergUnitInstance_of_wingbergDuality`;
* `Work.WingbergRoute.genDim_galoisGroup_Kc`, `Work.WingbergRoute.relDim_le_of_shafarevichBound`;
* `Work.WingbergRoute.shafarevichBound_iff_contH2DimLe_six`,
  `Work.WingbergRoute.kcWingbergWall_iff_kcKochCohomologyBound`,
  `Work.WingbergRoute.kcWingbergWall_of_kcH3Wall`,
  `Work.WingbergRoute.kcWingbergWall_of_kochInjectionWall`,
  `Work.WingbergRoute.kcWingbergWall_of_wingbergDuality`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField
open Work.ConCohomology

noncomputable section

namespace Work.WingbergRoute

/-! ## The two classical shapes are the same inequality -/

/-- **`d₂(O_F^×) = r + θ`.**  `unitTwoRank F` is by definition `NumberField.Units.rank F + 1`,
i.e. `(r₁ + r₂ - 1) + θ` with `θ = 1` for `p = 2` (because `ζ₂ = -1 ∈ F` for every number field
`F`).  Consequently Shafarevich's relation-rank bound `d₂(G_S) ≤ d₁(G_S) + r + θ` in the case
`S = ∅` is *literally* Wingberg's bound `df(G_∅) ≤ d₂(O_F^×)`. -/
theorem unitTwoRank_eq_unitsRank_add_one (F : Type*) [Field F] [NumberField F] :
    Work.ClassFieldTower.unitTwoRank F = NumberField.Units.rank F + 1 := rfl

/-- The same identity in the form `d₂(O_F^×) = r₁ + r₂`. -/
theorem unitTwoRank_eq_nrRealPlaces_add (F : Type*) [Field F] [NumberField F] :
    Work.ClassFieldTower.unitTwoRank F =
      NumberField.InfinitePlace.nrRealPlaces F +
        NumberField.InfinitePlace.nrComplexPlaces F :=
  Work.ClassFieldTower.unitTwoRank_eq_nrRealPlaces_add_nrComplexPlaces F

/-! ## The literature shape of the duality

`Work.WingbergRoute.WingbergDualityFaithful` is *verbatim* `Work.ShafarevichKoch.WingbergDuality`
(so nothing is lost in passing between the two vocabulary sets), and
`Work.WingbergRoute.WingbergUnitInstance` is the pair of `i = 0` conjuncts. -/

/-- **The workspace's `WingbergDuality` is exactly the literature's `i = 0,1` instances.**  The
two propositions are definitionally the same statement, spelled with the area's own names. -/
theorem wingbergDualityFaithful_iff
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) :
    WingbergDualityFaithful M ↔ Work.ShafarevichKoch.WingbergDuality M := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩

/-- The `i = 0` half of Wingberg's duality is the whole essential content: the `i = 1` half (the
`H²`-duality) is the H²-half of the relation count, which this workspace proves without class
field theory. -/
theorem wingbergUnitInstance_of_wingbergDuality
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (h : Work.ShafarevichKoch.WingbergDuality M) : WingbergUnitInstance M :=
  ⟨h.2.1, h.2.2.2⟩

/-! ## The numbers -/

/-- **`dim_{𝔽₂} H¹(G_∅,𝔽₂) = 5`**: the generator rank of the maximal unramified pro-`2` group of
`Kc` is `5 = rank₂ Cl(Kc)`.  This is item (1) of the Shafarevich--Koch chapter, proved there
without class field theory (`card_proTwoChar_Kc`). -/
theorem genDim_galoisGroup_Kc (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) :
    genDim (Work.ClassFieldTower.galoisGroup M) = 5 := by
  rw [genDim, Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc M, Nat.log_pow]
  norm_num

/-- **`d₂(O_Kc^×) = 1`**: the units of `Kc` are `{±1}`, so `rank₂ (𝓞 Kc)ˣ = 1`. -/
theorem unitTwoRank_Kc : Work.ClassFieldTower.unitTwoRank Kc = 1 :=
  Work.ClassFieldTower.unitTwoRank_witness_eq_one

/-- The same, in the form needed by the counting lemmas. -/
theorem unitTwoRank_Kc_le_one : Work.ClassFieldTower.unitTwoRank Kc ≤ 1 :=
  le_of_eq unitTwoRank_Kc

/-! ## The Shafarevich bound against the cohomological forms -/

/-- **The Shafarevich bound for `Kc` gives `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6`** -- with the generator rank
`5` and `d₂(O_Kc^×) ≤ 1` proved in the workspace. -/
theorem contH2DimLe_six_of_shafarevichBound
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (h : ShafarevichBound Kc M) :
    Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) 6 := by
  obtain ⟨k, d, hk, hd, hbd⟩ := h
  have hd5 : d = 5 := by
    have h5 := Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc M
    rw [h5] at hd
    exact (Nat.pow_right_injective (by norm_num : 1 < 2) hd.symm)
  have hu : Work.ClassFieldTower.unitTwoRank Kc = 1 := unitTwoRank_Kc
  have hk6 : k ≤ 6 := by omega
  exact ⟨k, hk6, hk⟩

/-- **Conversely**, the cohomological crux `dim H² ≤ 6` *is* the Shafarevich bound for `Kc`: the
generator rank is exactly `5` and `d₂(O_Kc^×) ≤ 1`, so `6 ≤ 5 + 1`. -/
theorem shafarevichBound_of_contH2DimLe_six
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (h : Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) 6) :
    ShafarevichBound Kc M := by
  obtain ⟨k, hk, hcard⟩ := h
  refine ⟨k, 5, hcard, Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc M, ?_⟩
  have := unitTwoRank_Kc
  omega

/-- **The two forms of the `Kc` wall are equivalent.** -/
theorem kcWingbergWall_iff_kcKochCohomologyBound :
    KcWingbergWall ↔ Work.ShafarevichKoch.KcKochCohomologyBound := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨M, contH2DimLe_six_of_shafarevichBound M h⟩
  · rintro ⟨M, h⟩
    exact ⟨M, shafarevichBound_of_contH2DimLe_six M h⟩

/-! ## The other normalisations of the wall -/

/-- **The `H³`-torsion form of the wall implies the Shafarevich form.**  This is the chapter's
`Work.CruxOneByte.crux_iff_twoTorsionH3_le_two` (the `⇐` direction) followed by the conversion
above. -/
theorem kcWingbergWall_of_kcH3Wall : KcH3Wall → KcWingbergWall := by
  rintro ⟨M, hfin2, hfin3, hB⟩
  exact ⟨M, shafarevichBound_of_contH2DimLe_six M
    (Work.ShafarevichKoch.contH2DimLe_six_of_twoTorsionH3_le_two M hfin2 hfin3 hB)⟩

/-- **The Kummer-pairing (Koch) form of the wall implies the Shafarevich form.**  The chapter's
`KochInjection` is the classical injection `H²(G_∅,𝔽₂) ↪ (V_∅/Kc^{×2})^∨` of Koch Ch. 11 Thm 11.3;
with `#(V_∅/Kc^{×2}) = 2^6` (proved in the chapter) it gives `dim H² ≤ 6`. -/
theorem kcWingbergWall_of_kochInjectionWall : KcKochInjectionWall → KcWingbergWall := by
  rintro ⟨M, hM⟩
  exact ⟨M, shafarevichBound_of_contH2DimLe_six M
    (Work.ShafarevichKoch.contH2DimLe_six_of_kochInjection M hM)⟩

/-- **Wingberg's duality implies the Shafarevich bound for `Kc`.**  This is the formal content of
"Wingberg's duality is a proof of Shafarevich's relation-rank bound in the case `S = ∅`". -/
theorem shafarevichBound_of_wingbergDuality
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (h : Work.ShafarevichKoch.WingbergDuality M) : ShafarevichBound Kc M :=
  shafarevichBound_of_contH2DimLe_six M
    (Work.ShafarevichKoch.contH2DimLe_six_of_wingbergDuality M h)

/-- **Wingberg's duality is an instance of the wall.** -/
theorem kcWingbergWall_of_wingbergDuality
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.ShafarevichKoch.WingbergDuality M) : KcWingbergWall := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, shafarevichBound_of_wingbergDuality M hM⟩

/-- **The `H³`-torsion bound gives the Shafarevich bound**, given the finiteness of `H²` and
`H³` of `G_∅` that the dictionary between the two normalisations of the count needs. -/
theorem shafarevichBound_of_twoTorsionH3_le_two
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hfin2 : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (hfin3 : Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (hB : Nat.card (Work.ShafarevichKoch.twoTorsionH3
      (Work.ClassFieldTower.galoisGroup M)) ≤ 2) :
    ShafarevichBound Kc M :=
  shafarevichBound_of_contH2DimLe_six M
    (Work.ShafarevichKoch.contH2DimLe_six_of_twoTorsionH3_le_two M hfin2 hfin3 hB)

/-- **Wingberg's `i = 0` instance (with the finiteness of `H²(G_∅,ℤ)`) gives the Shafarevich
bound.**  The `i = 1` conjunct of the full duality is not used beyond the finiteness of `H²`. -/
theorem shafarevichBound_of_wingbergUnitInstance
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hfin2 : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (h : WingbergUnitInstance M) : ShafarevichBound Kc M := by
  obtain ⟨hfin3, N, ⟨e⟩⟩ := h
  haveI : Fintype (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) :=
    Fintype.ofFinite _
  haveI : Finite (Work.ShafarevichKoch.RingUnit Kc) := Work.ShafarevichKoch.finite_RingUnit_Kc
  refine shafarevichBound_of_twoTorsionH3_le_two M hfin2 hfin3 ?_
  exact (Work.ShafarevichKoch.card_twoTorsion_of_dual_quotient_le
    (A := Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ)
    (B := Work.ShafarevichKoch.RingUnit Kc) N e).trans
      Work.ShafarevichKoch.card_RingUnit_Kc_le_two

/-- **Wingberg's `i = 0` instance alone suffices**, provided the finiteness of `H²(G_∅,ℤ)` is
supplied (it is the `i = 1` half of the duality, and the `H²`-half of the count). -/
theorem kcWingbergWall_of_wingbergUnitInstance
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
        WingbergUnitInstance M) : KcWingbergWall := by
  obtain ⟨M, hfin2, h⟩ := h
  exact ⟨M, shafarevichBound_of_wingbergUnitInstance M hfin2 h⟩

/-! ## The general shape of the bound

`ShafarevichBound F M` is equivalent to the "deficiency" form
`dim H² ≤ dim H¹ + d₂(O_F^×)` for an arbitrary number field `F`; the two forms are recorded for
`Kc` above and are used at `gsF` in `Work.WingbergRoute.TotallyReal`. -/

/-- **The general form of the Shafarevich bound at an arbitrary number field**: the relation
count `dim H² ≤ dim H¹ + d₂(O_F^×)`. -/
theorem shafarevichBound_iff (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP F 2) :
    ShafarevichBound F M ↔
      ∃ d : ℕ, Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d ∧
        Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M)
          (d + Work.ClassFieldTower.unitTwoRank F) := by
  constructor
  · rintro ⟨k, d, hk, hd, hbd⟩
    exact ⟨d, hd, ⟨k, hbd, hk⟩⟩
  · rintro ⟨d, hd, k, hk, hcont⟩
    exact ⟨k, d, hcont, hd, hk⟩

/-- `ShafarevichBound` is monotone in the unit rank: a bound with `d₂(O_F^×)` gives a bound with
any larger `u`. -/
theorem ShafarevichBound.mono_unitRank {F : Type*} [Field F] [NumberField F]
    {M : Work.ClassFieldTower.MaximalUnramifiedProP F 2} {u : ℕ}
    (h : ShafarevichBound F M) (hu : Work.ClassFieldTower.unitTwoRank F ≤ u) :
    ∃ k d : ℕ,
      Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) = 2 ^ k ∧
      Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d ∧ k ≤ d + u := by
  obtain ⟨k, d, hk, hd, hbd⟩ := h
  exact ⟨k, d, hk, hd, by omega⟩

/-! ## The presentation step

The wall and Gaschütz's value theorem give a *pro-`2` presentation* of `G_∅`: this is the shape in
which the Golod--Shafarevich criterion consumes the arithmetic. -/

/-- **The wall plus Gaschütz's value theorem give a pro-`2` presentation** of the maximal
unramified pro-`2` group: `d = d(G_∅)` generators and `d + d₂(O_F^×)` relators, where
`#H¹(G_∅,𝔽₂) = 2^d`. -/
theorem hasProP2Presentation_of_shafarevichBound (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP F 2)
    (hdict : Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : ShafarevichBound F M) :
    ∃ d : ℕ, Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d ∧
      Work.RelatorRank.HasProP2Presentation (Work.ClassFieldTower.galoisGroup M)
        (Work.RelatorRank.GeneratorRank (Work.ClassFieldTower.galoisGroup M))
        (d + Work.ClassFieldTower.unitTwoRank F) := by
  obtain ⟨d, hd, k, hk, hcont⟩ := (shafarevichBound_iff F M).mp h
  exact ⟨d, hd, (hdict _).mpr ⟨k, hk, hcont⟩⟩

/-- **The Kummer-pairing (Koch) form and the Shafarevich form of the wall are equivalent.**  The
forward direction is the Kummer-radical count `#(V_∅/Kc^{×2}) = 2^6`; the converse is the chapter's
`Work.ShafarevichKoch.kochInjection_of_contH2DimLe`, which turns the bound
`dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6` into Koch's injection. -/
theorem kcKochInjectionWall_iff_kcWingbergWall :
    KcKochInjectionWall ↔ KcWingbergWall := by
  constructor
  · exact kcWingbergWall_of_kochInjectionWall
  · rintro ⟨M, hM⟩
    exact ⟨M, Work.ShafarevichKoch.kochInjection_of_contH2DimLe M
      (contH2DimLe_six_of_shafarevichBound M hM)⟩

end Work.WingbergRoute
