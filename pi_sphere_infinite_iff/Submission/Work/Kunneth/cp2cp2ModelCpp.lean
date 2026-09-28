import Mathlib
import Submission.Work.Kunneth.cp2H_uCoh
import Submission.Work.Kunneth.ssetNaturality
import Submission.Work.Kunneth.TopCat
import Submission.Work.Cohomology.cupNaturalH

/-!
# The Künneth ring of the *space* `ℂP² × ℂP²`

`Work.Projective.CP2CP2Model X` is the Künneth-ring interface of `ℂP² × ℂP²` (the two classes
`a = π₁^*u`, `b = π₂^*u`, the fundamental class, the Pontryagin classes, `span{a², ab, b²} = ⊤`
and the nine intersection numbers).  `Work.Kunneth.cp2cp2Model` inhabits it for the *simplicial*
product `cpZ = ℂP² ⊗ ℂP²`; this module inhabits it for the space the consumers use,

`cppSSet = TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2))`,

which is the exact statement recorded as missing in `Submission/Work/Projective/README.md` §9 and
in `Submission/Work/Gen/`:

```lean
theorem cp2cp2Model_cpp :
    Nonempty (Work.Projective.CP2CP2Model
      (TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2))))
```

The two simplicial sets are identified by the Eilenberg–Zilber transport
`Work.Kunneth.singProdIso`, and every field is carried across it by
`Work.Kunneth.pullbackH_cupH` (multiplicativity), `Work.Kunneth.kronH_natural_sset`
(`⟨α, f_*c⟩ = ⟨f^*α, c⟩`) and `Work.Kunneth.pullbackH_comp` (functoriality).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- The singular simplicial set of the space `ℂP² × ℂP²` — the `SSet` the consumers use
(`Work.Gen.cppSSet`). -/
abbrev cppSSet : SSet := TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 2 × Work.Projective.CP 2))

/-- The first projection `ℂP² × ℂP² ⟶ ℂP²`, as a continuous map. -/
abbrev cpProj1 : C(Work.Projective.CP 2 × Work.Projective.CP 2, Work.Projective.CP 2) :=
  ContinuousMap.fst

/-- The second projection `ℂP² × ℂP² ⟶ ℂP²`, as a continuous map. -/
abbrev cpProj2 : C(Work.Projective.CP 2 × Work.Projective.CP 2, Work.Projective.CP 2) :=
  ContinuousMap.snd

/-- **The Eilenberg–Zilber identification** `ℂP² × ℂP² ≅ ℂP² ⊗ ℂP²` of the space with the
simplicial product. -/
abbrev cpE : cppSSet ≅ cpZ :=
  singProdIso (Work.Projective.CPSpace 2) (Work.Projective.CPSpace 2)

/-- `a = π₁^*u ∈ H²(ℂP² × ℂP²;ℤ)`, `u = c₁(O(1))` in the normalisation of `Work.Gen`. -/
abbrev cppA : ↥((cochainC ℤ cppSSet).homology 2) :=
  (Work.Thom.CohMap cpProj1 ℤ 2).hom (Work.Gen.uCoh 2)

/-- `b = π₂^*u ∈ H²(ℂP² × ℂP²;ℤ)`. -/
abbrev cppB : ↥((cochainC ℤ cppSSet).homology 2) :=
  (Work.Thom.CohMap cpProj2 ℤ 2).hom (Work.Gen.uCoh 2)

/-- **The fundamental class** `c = [ℂP²] × [ℂP²] ∈ H₈(ℂP² × ℂP²;ℤ)`, transported from the
simplicial product. -/
abbrev cppC : ↥((chainC ℤ cppSSet).homology 8) :=
  (HomologicalComplex.homologyMap (SSet.chainComplexMap cpE.inv zz) 8).hom cpFund

/-- The cup product is insensitive to a simultaneous sign. -/
lemma cupH'_neg_neg {n m : ℕ} (x : ↥((cochainC ℤ cppSSet).homology n))
    (y : ↥((cochainC ℤ cppSSet).homology m)) :
    cupH' ℤ cppSSet n m (-x) (-y) = cupH' ℤ cppSSet n m x y := by
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- `(CohMap π₁ ℤ n).hom y = (π₁^*y)` transported through the Eilenberg–Zilber identification. -/
lemma cohMap_proj1_eq (y : ↥((cochainC ℤ cpX).homology 2)) :
    (Work.Thom.CohMap cpProj1 ℤ 2).hom y
      = pullbackH cppSSet cpZ cpE.hom 2 (pullbackH cpZ cpX cpFst 2 y) := by
  rw [show (Work.Thom.CohMap cpProj1 ℤ 2).hom y
      = pullbackH cppSSet cpX
          (TopCat.toSSet.map (TopCat.ofHom cpProj1)) 2 y from rfl]
  rw [show TopCat.toSSet.map (TopCat.ofHom cpProj1) = cpE.hom ≫ cpFst from rfl]
  exact pullbackH_comp cppSSet cpZ cpX cpE.hom cpFst 2 y

/-- `(CohMap π₂ ℤ n).hom y = (π₂^*y)` transported through the Eilenberg–Zilber identification. -/
lemma cohMap_proj2_eq (y : ↥((cochainC ℤ cpX).homology 2)) :
    (Work.Thom.CohMap cpProj2 ℤ 2).hom y
      = pullbackH cppSSet cpZ cpE.hom 2 (pullbackH cpZ cpX cpSnd 2 y) := by
  rw [show (Work.Thom.CohMap cpProj2 ℤ 2).hom y
      = pullbackH cppSSet cpX
          (TopCat.toSSet.map (TopCat.ofHom cpProj2)) 2 y from rfl]
  rw [show TopCat.toSSet.map (TopCat.ofHom cpProj2) = cpE.hom ≫ cpSnd from rfl]
  exact pullbackH_comp cppSSet cpZ cpX cpE.hom cpSnd 2 y

/-- `a`, when the two normalisations of the hyperplane class agree. -/
lemma cppA_pos (h : Work.Gen.uCoh 2 = cpH) :
    cppA = pullbackH cppSSet cpZ cpE.hom 2 cpa :=
  (congrArg (fun x => (Work.Thom.CohMap cpProj1 ℤ 2).hom x) h).trans (cohMap_proj1_eq cpH)

/-- `a`, when the two normalisations differ by a sign. -/
lemma cppA_neg (h : Work.Gen.uCoh 2 = -cpH) :
    cppA = -(pullbackH cppSSet cpZ cpE.hom 2 cpa) :=
  ((congrArg (fun x => (Work.Thom.CohMap cpProj1 ℤ 2).hom x) h).trans
    (map_neg (Work.Thom.CohMap cpProj1 ℤ 2).hom cpH)).trans
    (congrArg Neg.neg (cohMap_proj1_eq cpH))

/-- `b`, when the two normalisations of the hyperplane class agree. -/
lemma cppB_pos (h : Work.Gen.uCoh 2 = cpH) :
    cppB = pullbackH cppSSet cpZ cpE.hom 2 cpb :=
  (congrArg (fun x => (Work.Thom.CohMap cpProj2 ℤ 2).hom x) h).trans (cohMap_proj2_eq cpH)

/-- `b`, when the two normalisations differ by a sign. -/
lemma cppB_neg (h : Work.Gen.uCoh 2 = -cpH) :
    cppB = -(pullbackH cppSSet cpZ cpE.hom 2 cpb) :=
  ((congrArg (fun x => (Work.Thom.CohMap cpProj2 ℤ 2).hom x) h).trans
    (map_neg (Work.Thom.CohMap cpProj2 ℤ 2).hom cpH)).trans
    (congrArg Neg.neg (cohMap_proj2_eq cpH))

/-- `a` is `±` the pullback of the hyperplane class. -/
lemma cppA_eq : cppA = pullbackH cppSSet cpZ cpE.hom 2 cpa
    ∨ cppA = -(pullbackH cppSSet cpZ cpE.hom 2 cpa) := by
  rcases uCoh_two_eq_pm_cp2H with h | h
  · exact Or.inl (cppA_pos h)
  · exact Or.inr (cppA_neg h)

/-- `b` is `±` the pullback of the hyperplane class. -/
lemma cppB_eq : cppB = pullbackH cppSSet cpZ cpE.hom 2 cpb
    ∨ cppB = -(pullbackH cppSSet cpZ cpE.hom 2 cpb) := by
  rcases uCoh_two_eq_pm_cp2H with h | h
  · exact Or.inl (cppB_pos h)
  · exact Or.inr (cppB_neg h)

/-- **`a²` is the transport of `a²`** of the simplicial product. -/
lemma cppA_sq : cupH' ℤ cppSSet 2 2 cppA cppA
    = pullbackH cppSSet cpZ cpE.hom 4 cpa2 := by
  rcases uCoh_two_eq_pm_cp2H with h | h
  · exact (congrArg₂ (fun x y => (cupH' ℤ cppSSet 2 2) x y) (cppA_pos h) (cppA_pos h)).trans
      (pullbackH_cupH cppSSet cpZ cpE.hom 2 2 cpa cpa).symm
  · exact ((congrArg₂ (fun x y => (cupH' ℤ cppSSet 2 2) x y) (cppA_neg h) (cppA_neg h)).trans
      (cupH'_neg_neg _ _)).trans
      (pullbackH_cupH cppSSet cpZ cpE.hom 2 2 cpa cpa).symm

/-- **`b²` is the transport of `b²`**. -/
lemma cppB_sq : cupH' ℤ cppSSet 2 2 cppB cppB
    = pullbackH cppSSet cpZ cpE.hom 4 cpb2 := by
  rcases uCoh_two_eq_pm_cp2H with h | h
  · exact (congrArg₂ (fun x y => (cupH' ℤ cppSSet 2 2) x y) (cppB_pos h) (cppB_pos h)).trans
      (pullbackH_cupH cppSSet cpZ cpE.hom 2 2 cpb cpb).symm
  · exact ((congrArg₂ (fun x y => (cupH' ℤ cppSSet 2 2) x y) (cppB_neg h) (cppB_neg h)).trans
      (cupH'_neg_neg _ _)).trans
      (pullbackH_cupH cppSSet cpZ cpE.hom 2 2 cpb cpb).symm

/-- **`ab` is the transport of `ab`**. -/
lemma cppAB : cupH' ℤ cppSSet 2 2 cppA cppB
    = pullbackH cppSSet cpZ cpE.hom 4 cpab := by
  rcases uCoh_two_eq_pm_cp2H with h | h
  · exact (congrArg₂ (fun x y => (cupH' ℤ cppSSet 2 2) x y) (cppA_pos h) (cppB_pos h)).trans
      (pullbackH_cupH cppSSet cpZ cpE.hom 2 2 cpa cpb).symm
  · exact ((congrArg₂ (fun x y => (cupH' ℤ cppSSet 2 2) x y) (cppA_neg h) (cppB_neg h)).trans
      (cupH'_neg_neg _ _)).trans
      (pullbackH_cupH cppSSet cpZ cpE.hom 2 2 cpa cpb).symm

/-- The fundamental class is carried by the pushforward of the Eilenberg–Zilber identification. -/
lemma cppC_push :
    (HomologicalComplex.homologyMap (SSet.chainComplexMap cpE.hom zz) 8).hom cppC = cpFund := by
  have hchain : SSet.chainComplexMap cpE.inv zz ≫ SSet.chainComplexMap cpE.hom zz
      = 𝟙 (sChain cpZ) := by
    rw [← chainComplexMap_comp, Iso.inv_hom_id, chainComplexMap_id]
  have key : (HomologicalComplex.homologyMap (SSet.chainComplexMap cpE.inv zz) 8 ≫
      HomologicalComplex.homologyMap (SSet.chainComplexMap cpE.hom zz) 8)
      = 𝟙 ((chainC ℤ cpZ).homology 8) := by
    rw [← HomologicalComplex.homologyMap_comp, hchain, HomologicalComplex.homologyMap_id]
  have h := congrArg (fun (g : (chainC ℤ cpZ).homology 8 ⟶ (chainC ℤ cpZ).homology 8) =>
    ModuleCat.Hom.hom g cpFund) key
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.id_apply] using h

/-- The Eilenberg–Zilber pullback is surjective (it is an isomorphism of cohomology). -/
lemma pullbackH_cpE_surjective (n : ℕ) :
    Function.Surjective (pullbackH cppSSet cpZ cpE.hom n) := by
  intro y
  refine ⟨pullbackH cpZ cppSSet cpE.inv n y, ?_⟩
  exact ((pullbackH_comp cppSSet cpZ cppSSet cpE.hom cpE.inv n y).symm).trans
    ((congrArg (fun (g : cppSSet ⟶ cppSSet) => pullbackH cppSSet cppSSet g n y)
      (Iso.hom_inv_id cpE)).trans (pullbackH_id cppSSet n y))

/-- **Transfer of the Kronecker pairing through the Eilenberg–Zilber identification.** -/
lemma kronH_transfer (S : ↥((cochainC ℤ cpZ).homology 8)) :
    kronH ℤ cppSSet 8 (pullbackH cppSSet cpZ cpE.hom 8 S) cppC
      = kronH ℤ cpZ 8 S cpFund :=
  (kronH_natural_sset cppSSet cpZ cpE.hom 8 S cppC).symm.trans
    (congrArg (fun w => kronH ℤ cpZ 8 S w) cppC_push)

/-- **Transfer of an intersection number through the Eilenberg–Zilber identification.** -/
lemma cppInt_eq (X Y : ↥((SSetCochainComplex ℤ cppSSet).homology 4))
    (X' Y' : ↥((SSetCochainComplex ℤ cpZ).homology 4))
    (hX : X = pullbackH cppSSet cpZ cpE.hom 4 X')
    (hY : Y = pullbackH cppSSet cpZ cpE.hom 4 Y') :
    Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC X Y
      = Work.SignatureBordism.interForm ℤ cpZ 4 4 cpFund X' Y' := by
  show kronH ℤ cppSSet 8 (cupH' ℤ cppSSet 4 4 X Y) cppC
      = kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 X' Y') cpFund
  exact (congrArg (fun z => kronH ℤ cppSSet 8 z cppC)
      ((congrArg₂ (fun x y => (cupH' ℤ cppSSet 4 4) x y) hX hY).trans
        (pullbackH_cupH cppSSet cpZ cpE.hom 4 4 X' Y').symm)).trans
    (kronH_transfer (cupH' ℤ cpZ 4 4 X' Y'))

/-- **The nine intersection numbers of `a², ab, b²` on the space `ℂP² × ℂP²`**, transported from the
simplicial product. -/
theorem cppInt_a2a2 : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kSq cppSSet cppA) (Work.Projective.kSq cppSSet cppA) = 0 :=
  (cppInt_eq _ _ cpa2 cpa2 cppA_sq cppA_sq).trans cpa2_cpa2_pairing

theorem cppInt_a2ab : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kSq cppSSet cppA) (Work.Projective.kMul cppSSet cppA cppB) = 0 :=
  (cppInt_eq _ _ cpa2 cpab cppA_sq cppAB).trans cpa2_cpab_pairing

theorem cppInt_a2b2 : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kSq cppSSet cppA) (Work.Projective.kSq cppSSet cppB) = 1 :=
  (cppInt_eq _ _ cpa2 cpb2 cppA_sq cppB_sq).trans cpa2_cpb2_pairing

theorem cppInt_aba2 : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kMul cppSSet cppA cppB) (Work.Projective.kSq cppSSet cppA) = 0 :=
  (cppInt_eq _ _ cpab cpa2 cppAB cppA_sq).trans cpab_cpa2_pairing

theorem cppInt_abab : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kMul cppSSet cppA cppB) (Work.Projective.kMul cppSSet cppA cppB) = 1 :=
  (cppInt_eq _ _ cpab cpab cppAB cppAB).trans cpab_cpab_pairing

theorem cppInt_abb2 : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kMul cppSSet cppA cppB) (Work.Projective.kSq cppSSet cppB) = 0 :=
  (cppInt_eq _ _ cpab cpb2 cppAB cppB_sq).trans cpab_cpb2_pairing

theorem cppInt_b2a2 : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kSq cppSSet cppB) (Work.Projective.kSq cppSSet cppA) = 1 :=
  (cppInt_eq _ _ cpb2 cpa2 cppB_sq cppA_sq).trans cpb2_cpa2_pairing

theorem cppInt_b2ab : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kSq cppSSet cppB) (Work.Projective.kMul cppSSet cppA cppB) = 0 :=
  (cppInt_eq _ _ cpb2 cpab cppB_sq cppAB).trans cpb2_cpab_pairing

theorem cppInt_b2b2 : Work.SignatureBordism.interForm ℤ cppSSet 4 4 cppC
    (Work.Projective.kSq cppSSet cppB) (Work.Projective.kSq cppSSet cppB) = 0 :=
  (cppInt_eq _ _ cpb2 cpb2 cppB_sq cppB_sq).trans cpb2_cpb2_pairing

/-- **`H⁴(ℂP² × ℂP²;ℤ) = ℤ⟨a², ab, b²⟩` on the space `ℂP² × ℂP²`. -/
theorem cpp_span_middle :
    Submodule.span ℤ ({Work.Projective.kSq cppSSet cppA, Work.Projective.kMul cppSSet cppA cppB,
      Work.Projective.kSq cppSSet cppB} : Set ↥((SSetCochainComplex ℤ cppSSet).homology 4)) = ⊤ := by
  have hle : Submodule.span ℤ ({cpa2, cpab, cpb2} : Set ↥((SSetCochainComplex ℤ cpZ).homology 4))
      ≤ Submodule.comap (pullbackH cppSSet cpZ cpE.hom 4)
          (Submodule.span ℤ ({Work.Projective.kSq cppSSet cppA,
            Work.Projective.kMul cppSSet cppA cppB,
            Work.Projective.kSq cppSSet cppB} :
              Set ↥((SSetCochainComplex ℤ cppSSet).homology 4))) := by
    refine Submodule.span_le.mpr ?_
    rintro y (rfl | rfl | rfl)
    · exact Submodule.subset_span (Or.inl cppA_sq.symm)
    · exact Submodule.subset_span (Or.inr (Or.inl cppAB.symm))
    · exact Submodule.subset_span (Or.inr (Or.inr cppB_sq.symm))
  refine Submodule.eq_top_iff'.mpr ?_
  intro z
  obtain ⟨w, hw⟩ := pullbackH_cpE_surjective 4 z
  have hw' : w ∈ Submodule.span ℤ ({cpa2, cpab, cpb2} :
      Set ↥((SSetCochainComplex ℤ cpZ).homology 4)) := by
    rw [cp2cp2_span_middle]; trivial
  exact hw ▸ hle hw'

/-- The first Chern-class form of `a²`: `π₁^*(u ⌣ u)`. -/
lemma cpp_kSq_fst : (Work.Thom.CohMap cpProj1 ℤ 4).hom (Work.Gen.uSq 2)
    = Work.Projective.kSq cppSSet cppA :=
  cupNaturalH ℤ (TopCat.ofHom cpProj1) 2 2 (Work.Gen.uCoh 2) (Work.Gen.uCoh 2)

/-- The first Chern-class form of `b²`: `π₂^*(u ⌣ u)`. -/
lemma cpp_kSq_snd : (Work.Thom.CohMap cpProj2 ℤ 4).hom (Work.Gen.uSq 2)
    = Work.Projective.kSq cppSSet cppB :=
  cupNaturalH ℤ (TopCat.ofHom cpProj2) 2 2 (Work.Gen.uCoh 2) (Work.Gen.uCoh 2)

/-- **The Künneth-ring model of the space `ℂP² × ℂP²`.**  The classes `a = π₁^*u`, `b = π₂^*u`
are the pullbacks of the hyperplane class (`u = c₁(O(1))` in the normalisation of `Work.Gen`),
`c = [ℂP²] × [ℂP²]`, `p₁ = 3(a² + b²)`, `p₂ = 9·a²b²`; `H⁴ = ℤ⟨a², ab, b²⟩` and the nine
intersection numbers are those of `Work.Kunneth.cppInt_*`. -/
noncomputable def cp2cp2ModelCpp : Work.Projective.CP2CP2Model cppSSet where
  a := cppA
  b := cppB
  c := cppC
  p₁ := (3 : ℤ) • ((Work.Thom.CohMap cpProj1 ℤ 4).hom (Work.Gen.uSq 2)
    + (Work.Thom.CohMap cpProj2 ℤ 4).hom (Work.Gen.uSq 2))
  p₂ := (9 : ℤ) • Work.Cohomology.cupH' ℤ cppSSet 4 4
    ((Work.Thom.CohMap cpProj1 ℤ 4).hom (Work.Gen.uSq 2))
    ((Work.Thom.CohMap cpProj2 ℤ 4).hom (Work.Gen.uSq 2))
  p₁_eq := show (3 : ℤ) • ((Work.Thom.CohMap cpProj1 ℤ 4).hom (Work.Gen.uSq 2)
      + (Work.Thom.CohMap cpProj2 ℤ 4).hom (Work.Gen.uSq 2))
      = (3 : ℤ) • (Work.Projective.kSq cppSSet cppA + Work.Projective.kSq cppSSet cppB) by
    rw [cpp_kSq_fst, cpp_kSq_snd]
    rfl
  p₂_eq := show (9 : ℤ) • Work.Cohomology.cupH' ℤ cppSSet 4 4
      ((Work.Thom.CohMap cpProj1 ℤ 4).hom (Work.Gen.uSq 2))
      ((Work.Thom.CohMap cpProj2 ℤ 4).hom (Work.Gen.uSq 2))
      = (9 : ℤ) • Work.Projective.kTop cppSSet
        (Work.Projective.kSq cppSSet cppA) (Work.Projective.kSq cppSSet cppB) by
    rw [cpp_kSq_fst, cpp_kSq_snd]
    rfl
  span_middle := cpp_span_middle
  int_a2a2 := cppInt_a2a2
  int_a2b2 := cppInt_a2b2
  int_b2a2 := cppInt_b2a2
  int_b2b2 := cppInt_b2b2
  int_abab := cppInt_abab
  int_a2ab := cppInt_a2ab
  int_aba2 := cppInt_aba2
  int_b2ab := cppInt_b2ab
  int_abb2 := cppInt_abb2

/-- **The GEN interface is inhabited for the space `ℂP² × ℂP²`.** -/
theorem cp2cp2Model_cpp :
    Nonempty (Work.Projective.CP2CP2Model
      (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 2 × Work.Projective.CP 2)))) :=
  ⟨cp2cp2ModelCpp⟩

end

end Work.Kunneth
