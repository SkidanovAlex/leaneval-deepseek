import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.RestrictInfra
import Submission.NK.NUV2.ABHN.unitsLevelH2_card
import Submission.NK.NUV2.ABHN.unitsLevelMap_injective
import Submission.NK.NUV2.ABHN.kummerColim_injective_field
import Submission.NK.NUV2.ABHN.kummerColim_surjective_pTorsion_general
import Submission.NK.NUV2.ABHN.muColimCardFree
import Submission.NK.NUV2.LC.cardH2P_adicCompletion

namespace NK.NUV2.LC.RouteB

/-!
## Auxiliary lemmas: the restriction map without the `[NumberField K]` binder

The lemmas `NK.LocalDecomposition.H2Profinite.res_ofLevel` and
`NK.NUV2.LC.RouteB.Restrict.res_muToH2Sub` of the library both carry an unused
`[NumberField K]` binder, so they cannot be instantiated with `K := 𝔮.adicCompletion K` (the base
field of the present statement, which is a `p`-adic field, not a number field).  We restate and
reprove them here in the generality actually needed.
-/

/-- The computation rule for the restriction map on the finite levels, in the generality of an
arbitrary base field `F` (no `NumberField` hypothesis). -/
theorem res_ofLevel_gen {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F']
    (p : ℕ) {U V : Subgroup Gal(F'/F)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField F F') (a : NK.BrauerHasse.LevelH2 p U L) :
    NK.LocalDecomposition.H2Profinite.res p h (NK.BrauerHasse.H2Profinite.ofLevel L a) =
      NK.BrauerHasse.H2Profinite.ofLevel L
        ((NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom h L)) a) :=
  Classical.choose_spec (NK.BrauerHasse.exists_restriction_map p h) L a

/-- The comparison square `res ∘ muToH2Sub = muToH2Sub ∘ resMu` for an arbitrary base field `F`
(no `NumberField` hypothesis). -/
theorem res_muToH2Sub_gen {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F']
    (p : ℕ) [NeZero p] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {U V : Subgroup Gal(F'/F)} (h : V ≤ U)
    (x : NK.HassePrinciple.MuColim (K := F) (K' := F') p U) :
    NK.LocalDecomposition.H2Profinite.res p h
        (Restrict.muToH2Sub (K := F) (K' := F') p hζ U x) =
      Restrict.muToH2Sub (K := F) (K' := F') p hζ V
        (Restrict.resMu (K := F) (K' := F') p h x) := by
  obtain ⟨L, a, rfl⟩ := Restrict.MuColim_ofLevel_surjective (K := F) (K' := F') p U x
  rw [Restrict.muToH2Sub_ofLevel, res_ofLevel_gen, Restrict.resMu_ofLevel,
    Restrict.muToH2Sub_ofLevel, Restrict.levelCompare_muResLevel]

/-- **The restriction kills every class of the `μ_p`-colimit**, provided that the `p`-torsion of
the units colimit over the base field is already exhausted by the levels below `E`.

The proof is the `key` argument of `NK.NUV2.LC.RouteB.loc_eq_zero_of_localLevelGroup_subsingleton`,
specialised to `U = ⊤` and `V = E.fixingSubgroup`: the Kummer image of `x` lies in the
`p`-torsion of the units colimit, hence (by `hcolim`) in the image of the level `E`; the level group
of `E.fixingSubgroup` at the level `E` is trivial, so the restriction of that level class vanishes,
and the Kummer square together with the injectivity of the Kummer map on the colimits finishes. -/
theorem res_muToH2_eq_zero_of_colimPTors_eq {F F' : Type} [Field F] [CharZero F] [Field F']
    [Algebra F F'] [IsSepClosure F F'] (p : ℕ) (hp : p.Prime) [NeZero p] (ζ : F)
    (hζ : IsPrimitiveRoot ζ p) (E : FiniteGaloisIntermediateField F F')
    (hcolim : NK.NUV2.ABHN.colimPTors (K := F) (K' := F') p =
      NK.NUV2.ABHN.colimImagePTors (K := F) (K' := F') p E)
    (x : NK.HassePrinciple.MuColim (K := F) (K' := F') p ⊤) :
    NK.LocalDecomposition.H2Profinite.res p
        (le_top : E.fixingSubgroup ≤ (⊤ : Subgroup Gal(F'/F)))
        (NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ x) = 0 := by
  -- The Kummer image of `x` is `p`-torsion, hence comes from the level `E`.
  have hmem : NK.HassePrinciple.kummerColim (K := F) (K' := F') p ⊤ x ∈
      NK.NUV2.ABHN.colimImagePTors (K := F) (K' := F') p E := by
    rw [← hcolim]
    exact NK.NUV2.ABHN.kummerColim_mem_colimPTors (K := F) (K' := F') p x
  obtain ⟨cls, -, hcls⟩ :=
    (NK.NUV2.ABHN.mem_colimImagePTors (K := F) (K' := F') (p := p) (L := E)).mp hmem
  have hcls2 : NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F') ⊤ E cls =
      NK.HassePrinciple.kummerColim (K := F) (K' := F') p ⊤ x := by
    rw [← NK.NUV2.ABHN.ofLevelAddHom_apply (K := F) (K' := F') ⊤ E cls]
    exact hcls
  -- The level group of `E.fixingSubgroup` at the level `E` is trivial.
  haveI htriv : Subsingleton
      (NK.BrauerHasse.LevelGroup (K := F) (K' := F') E.fixingSubgroup E) := by
    show Subsingleton (↥(E.fixingSubgroup : Subgroup Gal(F'/F)) ⧸
      (E.fixingSubgroup.subgroupOf E.fixingSubgroup : Subgroup ↥(E.fixingSubgroup)))
    rw [Subgroup.subgroupOf_self]
    exact QuotientGroup.subsingleton_quotient_top
  haveI : Subsingleton
      (NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') E.fixingSubgroup E) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (isZero_groupCohomology_succ_of_subsingleton
        (NK.HassePrinciple.unitsLevelRep (K := F) (K' := F') E.fixingSubgroup E) 1)
  have hzero : Restrict.unitsResLevel (K := F) (K' := F')
      (le_top : E.fixingSubgroup ≤ (⊤ : Subgroup Gal(F'/F))) E cls = 0 := Subsingleton.elim _ _
  -- Hence the restriction of `x` dies in the units colimit.
  have hkc : NK.HassePrinciple.kummerColim (K := F) (K' := F') p E.fixingSubgroup
      (Restrict.resMu (K := F) (K' := F') p
        (le_top : E.fixingSubgroup ≤ (⊤ : Subgroup Gal(F'/F))) x) = 0 := by
    rw [Restrict.kummerColim_resMu, ← hcls2, Restrict.resUnits_ofLevel, hzero,
      Restrict.H2Units_ofLevel_zero']
  -- By injectivity of the Kummer map on the colimits the restricted class itself is zero.
  have hres0 : Restrict.resMu (K := F) (K' := F') p
      (le_top : E.fixingSubgroup ≤ (⊤ : Subgroup Gal(F'/F))) x = 0 := by
    refine NK.NUV2.ABHN.kummerColim_injective_field (K := F) (K' := F') p hp
      E.fixingSubgroup ?_
    rw [hkc, kummerColim_zero]
  calc NK.LocalDecomposition.H2Profinite.res p
        (le_top : E.fixingSubgroup ≤ (⊤ : Subgroup Gal(F'/F)))
        (NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ x)
      = NK.LocalDecomposition.H2Profinite.res p
          (le_top : E.fixingSubgroup ≤ (⊤ : Subgroup Gal(F'/F)))
          (Restrict.muToH2Sub (K := F) (K' := F') p hζ ⊤ x) := by
        rw [Restrict.muToH2Sub_top]
    _ = Restrict.muToH2Sub (K := F) (K' := F') p hζ E.fixingSubgroup
          (Restrict.resMu (K := F) (K' := F') p
            (le_top : E.fixingSubgroup ≤ (⊤ : Subgroup Gal(F'/F))) x) :=
        res_muToH2Sub_gen (F := F) (F' := F') p hζ le_top x
    _ = 0 := by rw [hres0, Restrict.muToH2Sub_zero]

/-- **The local Brauer computation in restriction form.**  Let `κ = 𝔮.adicCompletion K` be the
completion of a number field at a finite prime, containing a primitive `p`-th root of unity `ζ`.
Let `E/κ` be a finite Galois subextension of a separable closure `κ'` of `κ` of degree `p`.  Then
the restriction `H²(G_κ, Z/p) → H²(G_E, Z/p)` is zero: `H²(G_κ, Z/p) ≅ Br(κ)[p] ≅ Z/p` and the
base change map on the Brauer group multiplies invariants by `[E:κ] = p`, so it kills `Br(κ)[p]`.

Route (all inputs are on disk):
* it suffices to exhibit ONE non-zero class `x` killed by `res`, together with additivity of `res`,
  the `p`-torsion `H2Profinite.nsmul_p_eq_zero` and
  `Nat.card (H2Profinite p ⊤) = p` (`NK.NUV2.LC.card_h2P_top_adicCompletion`);
* take `x := NK.NUV2.ABHN.muToH2 p hζ (MuColim.ofLevel E a)`, where
  `a ∈ H²(Gal(E/κ), μ_p)` is non-zero.  Then `res x = 0`, because the level group
  `LevelGroup (E.fixingSubgroup) E` is trivial, so
  `H2.map (levelInclHom (E.fixingSubgroup ≤ ⊤) E) = 0`, and `res` is computed on levels by the
  computation rule for the restriction map;
* `x ≠ 0`: `muToH2` is a bijection (`NK.NUV2.ABHN.muColimEquiv`), `kummerColim` is injective
  (`NK.NUV2.ABHN.kummerColim_injective_field`), `H2Units.ofLevel` is injective
  (`NK.NUV2.ABHN.ofLevelAddHom_injective` in `Submission/Work/NUV2/ABHN/muColimCardFree.lean`,
  which rests on `NK.NUV2.ABHN.unitsLevelMap_injective`), and `kummerLevel a ≠ 0` because the
  target `H²(Gal(E/κ), Eˣ)` has cardinality `[E : κ] = p` (`NK.NUV2.ABHN.unitsLevelH2_card`)
  while the source has cardinality `p`; for this last step use
  `NK.HassePrinciple.kummerLevel`, `NK.HassePrinciple.MuLevelH2` and the fact that
  `H2.map` of a bijective group homomorphism is bijective.

NOTE (from the reviewers): the on-disk lemmas
`NK.LocalDecomposition.H2Profinite.res_ofLevel`, `NK.BrauerHasse.H2Profinite.res_add` and
`NK.BrauerHasse.H2Profinite.nsmul_p_eq_zero` carry an unused but unsynthesizable
`[NumberField K]` binder, so they cannot be applied with `K := 𝔮.adicCompletion K`.  Restate and
reprove them locally without that hypothesis (e.g. the level computation rule is
`Classical.choose_spec (NK.BrauerHasse.exists_restriction_map p h)`), or use
`NK.LocalDecomposition.H2Profinite.res` replaced by the `Classical.choose`d map. -/
theorem local_res_eq_zero_adicCompletion (p : ℕ) (hp : p.Prime) {K : Type} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ζ : IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮) (hζ : IsPrimitiveRoot ζ p)
    (E : FiniteGaloisIntermediateField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)))
    (hdeg : Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
      ↥E.toIntermediateField = p) :
    ∀ y : NK.BrauerHasse.H2Profinite (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p ⊤,
      NK.LocalDecomposition.H2Profinite.res p (U := ⊤) (V := E.fixingSubgroup) le_top y = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI hcz : CharZero (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔮
  -- The `p`-torsion of the units colimit over the local field is already the image of the level `E`.
  have hcolim : NK.NUV2.ABHN.colimPTors
        (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p =
      NK.NUV2.ABHN.colimImagePTors
        (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p E := by
    have hdvd : p ∣ Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        ↥E.toIntermediateField := hdeg ▸ dvd_refl p
    have h1 : Nat.card ↥(NK.NUV2.ABHN.colimImagePTors
        (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p E) = p :=
      (NK.NUV2.ABHN.natCard_colimImagePTors
        (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p E).trans
        (NK.NUV2.ABHN.natCard_levelPTors_eq K 𝔮 p hp E hdvd)
    have h2 : Nat.card ↥(NK.NUV2.ABHN.colimPTors
        (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p) = p :=
      NK.NUV2.ABHN.natCard_colimPTors_eq K 𝔮 p hp
    haveI : Finite ↥(NK.NUV2.ABHN.colimPTors
        (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p) :=
      (Nat.card_pos_iff.mp (by rw [h2]; exact hp.pos)).2
    exact (AddSubgroup.eq_of_le_of_card_ge
      (NK.NUV2.ABHN.colimImagePTors_le_colimPTors
        (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
        (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) (p := p)
        (L := E)) (by rw [h2, h1])).symm
  intro y
  rw [← NK.NUV2.ABHN.muToH2_right_inv
    (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
    (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p hζ y]
  exact res_muToH2_eq_zero_of_colimPTors_eq p hp ζ hζ E hcolim
    (NK.NUV2.ABHN.h2ToMu
      (K := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)
      (K' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) p hζ y)

end NK.NUV2.LC.RouteB
