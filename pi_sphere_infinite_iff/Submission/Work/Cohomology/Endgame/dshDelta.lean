import Submission.Work.Cohomology.Endgame.shiftCap

/-!
# Naturality of the reindexing isomorphisms of `dsh`, and the connecting-map comparison

`Work.Cohomology.dsh C` (`Submission/Work/Cohomology/Endgame/shiftCap.lean`) is the downward
reindexing `(dsh C).X n = C.X (4+n)` of a chain complex of `ℤ`-modules, realised as the
restriction of complexes along the embedding `shiftEmb : n ↦ 4+n`.  To compare invariants of `dsh C`
with invariants of `C` one needs the naturality of Mathlib's restriction isomorphisms
(`HomologicalComplex.restrictionCyclesIso`, `restrictionOpcyclesIso`, `restrictionHomologyIso`)
with respect to a morphism of complexes — Mathlib has the corresponding naturality lemmas for the
universal maps `iCycles`, `pOpcycles`, `homologyπ`, `homologyι`, but not for `cyclesMap`,
`opcyclesMap`, `homologyMap`, `toCycles` and `opcyclesToCycles`.

This file supplies them:

* `restrictionCyclesIso_natural`, `restrictionOpcyclesIso_natural`,
  `restrictionHomologyIso_natural` — naturality of the three restriction isomorphisms under a
  morphism of complexes `φ : K ⟶ L` (the morphism `restrictionMap φ e` is the restriction of `φ`);
* `dshToCycles_natural`, `dshOpcyclesToCycles_natural` — the corresponding statements for
  `toCycles` and `opcyclesToCycles` in the `dsh`-setting;
* `dshHomIso_natural`, `dshOpcyclesIso'_natural`, `dshCyclesIso'_natural` — the same statements
  phrased with the pinned isomorphisms `dshHomIsoH`, `dshOpcyclesIso'`, `dshCyclesIso'`
  (`(dsh K).cycles n ≅ K.cycles (4+n)` etc.), which are the form in which they are consumed by the
  comparison of the Mayer–Vietoris connecting maps
  (`Work.Cohomology.Endgame.dshShort_cruxShort_delta`).

Do **not** redeclare these under the `HomologicalComplex` namespace: they are deliberately in
`Work.Cohomology` so that they cannot clash with a colleague's copy.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

open HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C : Type*} [Category C] [HasZeroMorphisms C]
variable {K L : HomologicalComplex C c'} {e : c.Embedding c'} [e.IsRelIff]

theorem restrictionCyclesIso_natural (φ : K ⟶ L) (j k : ι) (hk : c.next j = k)
    {j' k' : ι'} (hj' : e.f j = j') (hk' : e.f k = k') (hk'' : c'.next j' = k')
    [K.HasHomology j'] [L.HasHomology j'] [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ cyclesMap φ j' =
      cyclesMap (restrictionMap φ e) j ≫ (L.restrictionCyclesIso e j k hk hj' hk' hk'').hom := by
  rw [← cancel_mono (L.iCycles j')]
  simp only [Category.assoc]
  have h1 : (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ cyclesMap φ j' ≫ L.iCycles j'
      = (K.restriction e).iCycles j ≫ (K.restrictionXIso e hj').hom ≫ φ.f j' := by
    rw [cyclesMap_i, ← Category.assoc, restrictionCyclesIso_hom_iCycles]
    simp only [Category.assoc]
  have h2 : cyclesMap (restrictionMap φ e) j
        ≫ (L.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ L.iCycles j'
      = (K.restriction e).iCycles j ≫ (restrictionMap φ e).f j
          ≫ (L.restrictionXIso e hj').hom := by
    rw [restrictionCyclesIso_hom_iCycles, ← Category.assoc, cyclesMap_i]
    simp only [Category.assoc]
  rw [h1, h2, restrictionMap_f' φ e hj']
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem restrictionOpcyclesIso_natural (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i)
    {i' j' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hi'' : c'.prev j' = i')
    [K.HasHomology j'] [L.HasHomology j'] [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom ≫ opcyclesMap φ j' =
      opcyclesMap (restrictionMap φ e) j ≫ (L.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom := by
  rw [← cancel_epi ((K.restriction e).pOpcycles j)]
  simp only [← Category.assoc]
  conv_lhs => rw [pOpcycles_restrictionOpcyclesIso_hom K e i j hi hi' hj' hi'', Category.assoc,
    p_opcyclesMap φ j']
  conv_rhs => rw [p_opcyclesMap (restrictionMap φ e) j, Category.assoc,
    pOpcycles_restrictionOpcyclesIso_hom L e i j hi hi' hj' hi'']
  rw [restrictionMap_f' φ e hj']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem restrictionHomologyIso_natural (φ : K ⟶ L) (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k)
    {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
    (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
    [K.HasHomology j'] [L.HasHomology j'] [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom ≫ homologyMap φ j' =
      homologyMap (restrictionMap φ e) j
        ≫ (L.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom := by
  rw [← cancel_epi ((K.restriction e).homologyπ j)]
  simp only [← Category.assoc]
  conv_lhs => rw [homologyπ_restrictionHomologyIso_hom K e i j k hi hk hi' hj' hk' hi'' hk'',
    Category.assoc, homologyπ_naturality φ j']
  conv_rhs => rw [homologyπ_naturality (restrictionMap φ e) j, Category.assoc,
    homologyπ_restrictionHomologyIso_hom L e i j k hi hk hi' hj' hk' hi'' hk'']
  conv_lhs => rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  rw [restrictionCyclesIso_natural φ j k hk hj' hk' hk'']

noncomputable section

lemma downPrev (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 :=
  (ComplexShape.down ℕ).prev_eq' (by simp only [ComplexShape.down_Rel])

lemma downNext (n : ℕ) (hn : 1 ≤ n) : (ComplexShape.down ℕ).next n = n - 1 :=
  (ComplexShape.down ℕ).next_eq' (by simp only [ComplexShape.down_Rel]; omega)

lemma downPrevS (n : ℕ) : (ComplexShape.down ℕ).prev (shiftEmb.f n) = shiftEmb.f (n + 1) := by
  rw [show shiftEmb.f n = 4 + n from rfl, show shiftEmb.f (n + 1) = 4 + (n + 1) from rfl]
  exact (ComplexShape.down ℕ).prev_eq' (by simp only [ComplexShape.down_Rel]; omega)

lemma downNextS (n : ℕ) (hn : 1 ≤ n) :
    (ComplexShape.down ℕ).next (shiftEmb.f n) = shiftEmb.f (n - 1) := by
  rw [show shiftEmb.f n = 4 + n from rfl, show shiftEmb.f (n - 1) = 4 + (n - 1) from rfl]
  exact (ComplexShape.down ℕ).next_eq' (by simp only [ComplexShape.down_Rel]; omega)

abbrev dshXIso' (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    (K.restriction shiftEmb).X i ≅ K.X (shiftEmb.f i) :=
  K.restrictionXIso shiftEmb rfl

abbrev dshCyclesIso' (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (K.restriction shiftEmb).cycles n ≅ K.cycles (shiftEmb.f n) :=
  K.restrictionCyclesIso shiftEmb n (n - 1) (downNext n hn) rfl rfl (downNextS n hn)

abbrev dshOpcyclesIso' (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (K.restriction shiftEmb).opcycles n ≅ K.opcycles (shiftEmb.f n) :=
  K.restrictionOpcyclesIso shiftEmb (n + 1) n (downPrev n) rfl rfl (downPrevS n)

theorem dshToCycles_natural (K : ChainComplex (ModuleCat ℤ) ℕ) (i j : ℕ) (hj : 1 ≤ j) :
    (dshXIso' K i).hom ≫ K.toCycles (shiftEmb.f i) (shiftEmb.f j)
      = (K.restriction shiftEmb).toCycles i j ≫ (dshCyclesIso' K j hj).hom := by
  rw [← cancel_mono (K.iCycles (shiftEmb.f j))]
  simp only [Category.assoc]
  have h1 : (dshXIso' K i).hom ≫ K.toCycles (shiftEmb.f i) (shiftEmb.f j)
        ≫ K.iCycles (shiftEmb.f j)
      = (dshXIso' K i).hom ≫ K.d (shiftEmb.f i) (shiftEmb.f j) := by
    rw [toCycles_i]
  have h2 : (K.restriction shiftEmb).toCycles i j ≫ (dshCyclesIso' K j hj).hom
        ≫ K.iCycles (shiftEmb.f j)
      = (dshXIso' K i).hom ≫ K.d (shiftEmb.f i) (shiftEmb.f j) := by
    rw [restrictionCyclesIso_hom_iCycles, ← Category.assoc, toCycles_i,
      restriction_d_eq K shiftEmb (rfl : shiftEmb.f i = shiftEmb.f i)
        (rfl : shiftEmb.f j = shiftEmb.f j)]
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h1, h2]

theorem dshOpcyclesToCycles_natural (K : ChainComplex (ModuleCat ℤ) ℕ) (p : ℕ) (hp : 1 ≤ p) :
    (dshOpcyclesIso' K (p + 1)).hom ≫ K.opcyclesToCycles (shiftEmb.f (p + 1)) (shiftEmb.f p)
      = (K.restriction shiftEmb).opcyclesToCycles (p + 1) p ≫ (dshCyclesIso' K p hp).hom := by
  rw [← cancel_epi ((K.restriction shiftEmb).pOpcycles (p + 1))]
  have h1 : (K.restriction shiftEmb).pOpcycles (p + 1)
        ≫ ((dshOpcyclesIso' K (p + 1)).hom
            ≫ K.opcyclesToCycles (shiftEmb.f (p + 1)) (shiftEmb.f p))
      = (dshXIso' K (p + 1)).hom ≫ K.toCycles (shiftEmb.f (p + 1)) (shiftEmb.f p) := by
    rw [← Category.assoc, pOpcycles_restrictionOpcyclesIso_hom, Category.assoc,
      pOpcycles_opcyclesToCycles]
  have h2 : (K.restriction shiftEmb).pOpcycles (p + 1)
        ≫ ((K.restriction shiftEmb).opcyclesToCycles (p + 1) p
            ≫ (dshCyclesIso' K p hp).hom)
      = (dshXIso' K (p + 1)).hom ≫ K.toCycles (shiftEmb.f (p + 1)) (shiftEmb.f p) := by
    rw [← Category.assoc, pOpcycles_opcyclesToCycles]
    exact (dshToCycles_natural K (p + 1) p hp).symm
  rw [h1, h2]


open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

#check @HomologicalComplex.HomologySequence.snakeInput



abbrev dshHomIsoH (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (K.restriction shiftEmb).homology n ≅ K.homology (shiftEmb.f n) :=
  K.restrictionHomologyIso shiftEmb (n + 1) n (n - 1) (downPrev n) (downNext n hn) rfl rfl rfl
    (downPrevS n) (downNextS n hn)

theorem dshHomIso_natural (K L : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ L)
    (n : ℕ) (hn : 1 ≤ n) :
    (dshHomIsoH K n hn).hom ≫ homologyMap φ (shiftEmb.f n)
      = homologyMap (HomologicalComplex.restrictionMap φ shiftEmb) n
        ≫ (dshHomIsoH L n hn).hom :=
  restrictionHomologyIso_natural (e := shiftEmb) φ (n + 1) n (n - 1)
    (downPrev n) (downNext n hn) rfl rfl rfl (downPrevS n) (downNextS n hn)

theorem dshOpcyclesIso'_natural (K L : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ L) (n : ℕ) :
    (dshOpcyclesIso' K n).hom ≫ opcyclesMap φ (shiftEmb.f n)
      = opcyclesMap (HomologicalComplex.restrictionMap φ shiftEmb) n
        ≫ (dshOpcyclesIso' L n).hom :=
  restrictionOpcyclesIso_natural (e := shiftEmb) φ (n + 1) n
    (downPrev n) rfl rfl (downPrevS n)

theorem dshCyclesIso'_natural (K L : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ L)
    (n : ℕ) (hn : 1 ≤ n) :
    (dshCyclesIso' K n hn).hom ≫ cyclesMap φ (shiftEmb.f n)
      = cyclesMap (HomologicalComplex.restrictionMap φ shiftEmb) n
        ≫ (dshCyclesIso' L n hn).hom :=
  restrictionCyclesIso_natural (e := shiftEmb) φ n (n - 1)
    (downNext n hn) rfl rfl (downNextS n hn)


/-- The `dshHomologyIso_mulFour` form of the naturality of the homology reindexing. -/
theorem dshHomologyIso_mulFour_natural (K L : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ L)
    (n : ℕ) (hn : 1 ≤ n) :
    (dshHomologyIso_mulFour K n hn).hom ≫ homologyMap φ (4 + n)
      = homologyMap (dshMap φ) n ≫ (dshHomologyIso_mulFour L n hn).hom := by
  have h1 : dshHomologyIso_mulFour K n hn = dshHomIsoH K n hn := rfl
  have h2 : dshHomologyIso_mulFour L n hn = dshHomIsoH L n hn := rfl
  rw [h1, h2]
  exact dshHomIso_natural K L φ n hn

theorem dshOpcyclesIso'_natural_dsh (K L : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ L) (n : ℕ) :
    (dshOpcyclesIso' K n).hom ≫ HomologicalComplex.opcyclesMap φ (4 + n)
      = HomologicalComplex.opcyclesMap (dshMap φ) n ≫ (dshOpcyclesIso' L n).hom :=
  dshOpcyclesIso'_natural K L φ n

theorem dshCyclesIso'_natural_dsh (K L : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ L)
    (n : ℕ) (hn : 1 ≤ n) :
    (dshCyclesIso' K n hn).hom ≫ HomologicalComplex.cyclesMap φ (4 + n)
      = HomologicalComplex.cyclesMap (dshMap φ) n ≫ (dshCyclesIso' L n hn).hom :=
  dshCyclesIso'_natural K L φ n hn

theorem dshHomology_ι (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (dshHomologyIso_mulFour K n hn).hom ≫ K.homologyι (4 + n)
      = (K.restriction shiftEmb).homologyι n ≫ (dshOpcyclesIso' K n).hom :=
  HomologicalComplex.restrictionHomologyIso_hom_homologyι (e := shiftEmb) K (n + 1) n (n - 1)
    (downPrev n) (downNext n hn) rfl rfl rfl (downPrevS n) (downNextS n hn)

theorem dshHomology_π (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (K.restriction shiftEmb).homologyπ n ≫ (dshHomologyIso_mulFour K n hn).hom
      = (dshCyclesIso' K n hn).hom ≫ K.homologyπ (4 + n) :=
  HomologicalComplex.homologyπ_restrictionHomologyIso_hom (e := shiftEmb) K (n + 1) n (n - 1)
    (downPrev n) (downNext n hn) rfl rfl rfl (downPrevS n) (downNextS n hn)


theorem dshShort_cruxShort_delta (X : TopCat) (A U V : Set X) (m : ℕ) (hm : 1 ≤ m) :
    (dshShort_cruxShort_shortExact A U V).δ (m + 1) m (by simp only [ComplexShape.down_Rel]) =
      CategoryTheory.CategoryStruct.comp
        (dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) (by omega)).hom
        (CategoryTheory.CategoryStruct.comp (cruxδ X A U V (4 + m))
          (dshHomologyIso_mulFour (relMVUV X A U V) m hm).inv) := by
  have hm1 : 1 ≤ m + 1 := by omega
  let f : CategoryTheory.ShortComplex.SnakeInput.Hom
      (HomologicalComplex.HomologySequence.snakeInput
        (dshShort_cruxShort_shortExact A U V) (m + 1) m (by simp only [ComplexShape.down_Rel]))
      (HomologicalComplex.HomologySequence.snakeInput
        (cruxShort_shortExact X A U V) (4 + m + 1) (4 + m) (by simp only [ComplexShape.down_Rel])) :=
    { f₀ := ShortComplex.homMk
        (dshHomologyIso_mulFour (relMVUV X A U V) (m + 1) hm1).hom
        (dshHomologyIso_mulFour (cruxMid X A U V) (m + 1) hm1).hom
        (dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) hm1).hom
        (by
          show (dshHomologyIso_mulFour (relMVUV X A U V) (m + 1) hm1).hom
                ≫ HomologicalComplex.homologyMap (cruxF X A U V) (4 + (m + 1))
              = HomologicalComplex.homologyMap (dshMap (cruxF X A U V)) (m + 1)
                ≫ (dshHomologyIso_mulFour (cruxMid X A U V) (m + 1) hm1).hom
          exact dshHomologyIso_mulFour_natural _ _ (cruxF X A U V) (m + 1) hm1)
        (by
          show (dshHomologyIso_mulFour (cruxMid X A U V) (m + 1) hm1).hom
                ≫ HomologicalComplex.homologyMap (cruxG X A U V) (4 + (m + 1))
              = HomologicalComplex.homologyMap (dshMap (cruxG X A U V)) (m + 1)
                ≫ (dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) hm1).hom
          exact dshHomologyIso_mulFour_natural _ _ (cruxG X A U V) (m + 1) hm1)
      f₁ := ShortComplex.homMk
        (dshOpcyclesIso' (relMVUV X A U V) (m + 1)).hom
        (dshOpcyclesIso' (cruxMid X A U V) (m + 1)).hom
        (dshOpcyclesIso' (relMVTopC X A U V) (m + 1)).hom
        (by
          show (dshOpcyclesIso' (relMVUV X A U V) (m + 1)).hom ≫ HomologicalComplex.opcyclesMap (cruxF X A U V) (4 + (m + 1))
              = HomologicalComplex.opcyclesMap (dshMap (cruxF X A U V)) (m + 1)
                ≫ (dshOpcyclesIso' (cruxMid X A U V) (m + 1)).hom
          exact dshOpcyclesIso'_natural_dsh _ _ (cruxF X A U V) (m + 1))
        (by
          show (dshOpcyclesIso' (cruxMid X A U V) (m + 1)).hom ≫ HomologicalComplex.opcyclesMap (cruxG X A U V) (4 + (m + 1))
              = HomologicalComplex.opcyclesMap (dshMap (cruxG X A U V)) (m + 1)
                ≫ (dshOpcyclesIso' (relMVTopC X A U V) (m + 1)).hom
          exact dshOpcyclesIso'_natural_dsh _ _ (cruxG X A U V) (m + 1))
      f₂ := ShortComplex.homMk
        (dshCyclesIso' (relMVUV X A U V) m hm).hom
        (dshCyclesIso' (cruxMid X A U V) m hm).hom
        (dshCyclesIso' (relMVTopC X A U V) m hm).hom
        (by
          show (dshCyclesIso' (relMVUV X A U V) (m) hm).hom ≫ HomologicalComplex.cyclesMap (cruxF X A U V) (4 + (m))
              = HomologicalComplex.cyclesMap (dshMap (cruxF X A U V)) (m)
                ≫ (dshCyclesIso' (cruxMid X A U V) (m) hm).hom
          exact dshCyclesIso'_natural_dsh _ _ (cruxF X A U V) (m) hm)
        (by
          show (dshCyclesIso' (cruxMid X A U V) (m) hm).hom ≫ HomologicalComplex.cyclesMap (cruxG X A U V) (4 + (m))
              = HomologicalComplex.cyclesMap (dshMap (cruxG X A U V)) (m)
                ≫ (dshCyclesIso' (relMVTopC X A U V) (m) hm).hom
          exact dshCyclesIso'_natural_dsh _ _ (cruxG X A U V) (m) hm)
      f₃ := ShortComplex.homMk
        (dshHomologyIso_mulFour (relMVUV X A U V) m hm).hom
        (dshHomologyIso_mulFour (cruxMid X A U V) m hm).hom
        (dshHomologyIso_mulFour (relMVTopC X A U V) m hm).hom
        (by
          show (dshHomologyIso_mulFour (relMVUV X A U V) (m) hm).hom
                ≫ HomologicalComplex.homologyMap (cruxF X A U V) (4 + (m))
              = HomologicalComplex.homologyMap (dshMap (cruxF X A U V)) (m)
                ≫ (dshHomologyIso_mulFour (cruxMid X A U V) (m) hm).hom
          exact dshHomologyIso_mulFour_natural _ _ (cruxF X A U V) (m) hm)
        (by
          show (dshHomologyIso_mulFour (cruxMid X A U V) (m) hm).hom
                ≫ HomologicalComplex.homologyMap (cruxG X A U V) (4 + (m))
              = HomologicalComplex.homologyMap (dshMap (cruxG X A U V)) (m)
                ≫ (dshHomologyIso_mulFour (relMVTopC X A U V) (m) hm).hom
          exact dshHomologyIso_mulFour_natural _ _ (cruxG X A U V) (m) hm)
      comm₀₁ := by
        apply ShortComplex.hom_ext
        · show (dshHomologyIso_mulFour (relMVUV X A U V) (m + 1) hm1).hom ≫ (relMVUV X A U V).homologyι (4 + (m + 1))
              = (dsh (relMVUV X A U V)).homologyι (m + 1) ≫ (dshOpcyclesIso' (relMVUV X A U V) (m + 1)).hom
          exact dshHomology_ι (relMVUV X A U V) (m + 1) hm1
        · show (dshHomologyIso_mulFour (cruxMid X A U V) (m + 1) hm1).hom ≫ (cruxMid X A U V).homologyι (4 + (m + 1))
              = (dsh (cruxMid X A U V)).homologyι (m + 1) ≫ (dshOpcyclesIso' (cruxMid X A U V) (m + 1)).hom
          exact dshHomology_ι (cruxMid X A U V) (m + 1) hm1
        · show (dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) hm1).hom ≫ (relMVTopC X A U V).homologyι (4 + (m + 1))
              = (dsh (relMVTopC X A U V)).homologyι (m + 1) ≫ (dshOpcyclesIso' (relMVTopC X A U V) (m + 1)).hom
          exact dshHomology_ι (relMVTopC X A U V) (m + 1) hm1
      comm₁₂ := by
        apply ShortComplex.hom_ext
        · show (dshOpcyclesIso' (relMVUV X A U V) (m + 1)).hom ≫ (relMVUV X A U V).opcyclesToCycles (4 + (m + 1)) (4 + (m))
              = (dsh (relMVUV X A U V)).opcyclesToCycles (m + 1) (m) ≫ (dshCyclesIso' (relMVUV X A U V) (m) hm).hom
          exact dshOpcyclesToCycles_natural (relMVUV X A U V) (m) hm
        · show (dshOpcyclesIso' (cruxMid X A U V) (m + 1)).hom ≫ (cruxMid X A U V).opcyclesToCycles (4 + (m + 1)) (4 + (m))
              = (dsh (cruxMid X A U V)).opcyclesToCycles (m + 1) (m) ≫ (dshCyclesIso' (cruxMid X A U V) (m) hm).hom
          exact dshOpcyclesToCycles_natural (cruxMid X A U V) (m) hm
        · show (dshOpcyclesIso' (relMVTopC X A U V) (m + 1)).hom ≫ (relMVTopC X A U V).opcyclesToCycles (4 + (m + 1)) (4 + (m))
              = (dsh (relMVTopC X A U V)).opcyclesToCycles (m + 1) (m) ≫ (dshCyclesIso' (relMVTopC X A U V) (m) hm).hom
          exact dshOpcyclesToCycles_natural (relMVTopC X A U V) (m) hm
      comm₂₃ := by
        apply ShortComplex.hom_ext
        · show (dshCyclesIso' (relMVUV X A U V) (m) hm).hom ≫ (relMVUV X A U V).homologyπ (4 + (m))
              = (dsh (relMVUV X A U V)).homologyπ (m) ≫ (dshHomologyIso_mulFour (relMVUV X A U V) (m) hm).hom
          exact (dshHomology_π (relMVUV X A U V) (m) hm).symm
        · show (dshCyclesIso' (cruxMid X A U V) (m) hm).hom ≫ (cruxMid X A U V).homologyπ (4 + (m))
              = (dsh (cruxMid X A U V)).homologyπ (m) ≫ (dshHomologyIso_mulFour (cruxMid X A U V) (m) hm).hom
          exact (dshHomology_π (cruxMid X A U V) (m) hm).symm
        · show (dshCyclesIso' (relMVTopC X A U V) (m) hm).hom ≫ (relMVTopC X A U V).homologyπ (4 + (m))
              = (dsh (relMVTopC X A U V)).homologyπ (m) ≫ (dshHomologyIso_mulFour (relMVTopC X A U V) (m) hm).hom
          exact (dshHomology_π (relMVTopC X A U V) (m) hm).symm }
  have key2 : (dshShort_cruxShort_shortExact A U V).δ (m + 1) m
        (by simp only [ComplexShape.down_Rel])
        ≫ (dshHomologyIso_mulFour (relMVUV X A U V) m hm).hom
      = (dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) hm1).hom
        ≫ cruxδ X A U V (4 + m) :=
    CategoryTheory.ShortComplex.SnakeInput.naturality_δ f
  calc (dshShort_cruxShort_shortExact A U V).δ (m + 1) m (by simp only [ComplexShape.down_Rel])
      = (dshShort_cruxShort_shortExact A U V).δ (m + 1) m (by simp only [ComplexShape.down_Rel])
          ≫ ((dshHomologyIso_mulFour (relMVUV X A U V) m hm).hom
            ≫ (dshHomologyIso_mulFour (relMVUV X A U V) m hm).inv) := by
        rw [Iso.hom_inv_id, Category.comp_id]
    _ = ((dshShort_cruxShort_shortExact A U V).δ (m + 1) m (by simp only [ComplexShape.down_Rel])
          ≫ (dshHomologyIso_mulFour (relMVUV X A U V) m hm).hom)
          ≫ (dshHomologyIso_mulFour (relMVUV X A U V) m hm).inv := by
        rw [Category.assoc]
    _ = ((dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) hm1).hom
          ≫ cruxδ X A U V (4 + m))
          ≫ (dshHomologyIso_mulFour (relMVUV X A U V) m hm).inv := by
        rw [key2]
    _ = (dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) hm1).hom
          ≫ cruxδ X A U V (4 + m) ≫ (dshHomologyIso_mulFour (relMVUV X A U V) m hm).inv := by
        rw [Category.assoc]

end

end Work.Cohomology
