import Mathlib
import Submission.NK.NUV2.LC.RouteB.hasseSurjTopDefs
import Submission.NK.NUV2.LC.h2CardTransport
import Submission.NK.NUV2.LC.RouteB.inOrbit_iff_comap_fixedField
import Submission.NK.NUV2.LC.RouteB.isLive_of_isMuOpen
import Submission.NK.NUV2.LC.RouteB.step0_open_normal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped Pointwise

open NK.BrauerHasse

namespace NK.NUV2.LC.RouteB

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The fixed field of `U` (as an intermediate field), written as an abbreviation for readability. -/
abbrev fixedFieldOf (U : Subgroup Gal(K'/K)) : IntermediateField K K' :=
  IntermediateField.fixedField U

/-- `K'^U` is a finite extension of `K` when `U` is open. -/
theorem finiteDimensional_fixedField (U : Subgroup Gal(K'/K))
    (hUopen : IsOpen (U : Set Gal(K'/K))) :
    FiniteDimensional K ↥(IntermediateField.fixedField U) := by
  haveI : IsGalois K K' := IsSepClosure.isGalois
  have hUcl : IsClosed (U : Set Gal(K'/K)) := Subgroup.isClosed_of_isOpen U hUopen
  have hFix : (IntermediateField.fixedField U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUcl⟩
  rw [← InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField U), hFix]
  exact hUopen

/-- The fixed field of any subgroup is a separable extension. -/
theorem isSepClosure_fixedField (U : Subgroup Gal(K'/K)) :
    IsSepClosure ↥(IntermediateField.fixedField U) K' :=
  IsSepClosure.mk (IsSepClosure.sep_closed K)
    (Algebra.IsSeparable.of_integral ↥(IntermediateField.fixedField U) K')

/-- The Galois correspondence `↥U ≃ₜ* Gal(K'/↥F)` for `U` closed with `F = K'^U`. -/
noncomputable def fixedFieldCME (U : Subgroup Gal(K'/K)) (hUcl : IsClosed (U : Set Gal(K'/K)))
    (hUopen : IsOpen (U : Set Gal(K'/K))) :
    ↥U ≃ₜ* (K' ≃ₐ[↥(IntermediateField.fixedField U)] K') := by
  haveI : IsGalois K K' := IsSepClosure.isGalois
  haveI hfd : FiniteDimensional K ↥(IntermediateField.fixedField U) :=
    finiteDimensional_fixedField U hUopen
  have hFix : (IntermediateField.fixedField U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUcl⟩
  exact (subgroupCongrCME hFix.symm).trans
    (continuousMulEquivOfIsHomeomorph (IntermediateField.fixingSubgroupEquiv _)
      (NK.Reconstruct.isHomeomorph_fixingSubgroupEquiv (K := K) (Ω := K')
        (IntermediateField.fixedField U)))

/-- The canonical isomorphism preserves the underlying function. -/
theorem coe_fixedFieldCME (U : Subgroup Gal(K'/K)) (hUcl : IsClosed (U : Set Gal(K'/K)))
    (hUopen : IsOpen (U : Set Gal(K'/K))) (x : ↥U) :
    ⇑(fixedFieldCME U hUcl hUopen x) = ⇑((x : ↥U) : Gal(K'/K)) := rfl


/-! ## The transport data `HT.Tr` for the pair `(U, ⊤)` -/

/-- The transport data for the pair `(U ≤ Gal(K'/K), ⊤ ≤ Gal(K'/K'^U))`. -/
noncomputable abbrev trData (U : Subgroup Gal(K'/K)) (hUcl : IsClosed (U : Set Gal(K'/K)))
    (hUopen : IsOpen (U : Set Gal(K'/K)))
    (hsc : IsSepClosure ↥(fixedFieldOf U) K') :
    HT.Tr K K' ↥(fixedFieldOf U) K' :=
  letI : IsSepClosure ↥(fixedFieldOf U) K' := hsc
  { H := U
    e := (fixedFieldCME U hUcl hUopen).toMulEquiv
    hopen := fun M => HT.tsub_isOpen U (fixedFieldCME U hUcl hUopen) M
    hclosed := fun M => HT.tsub_isClosed U (fixedFieldCME U hUcl hUopen) M
    hpre := fun L => HT.tsub_pre U (fixedFieldCME U hUcl hUopen) L }

/-! ## The local group isomorphism -/

/-- **The decomposition group correspondence.**  The stabiliser of the place `A` in `U = Gal(K'/K'^U)`
is mapped by the Galois correspondence onto the stabiliser of `A` in `Gal(K'/K'^U)`. -/
theorem map_subgroupOf_inf_eq_stabilizer_fixedFieldCME (U : Subgroup Gal(K'/K))
    (hUcl : IsClosed (U : Set Gal(K'/K))) (hUopen : IsOpen (U : Set Gal(K'/K)))
    (A : ValuationSubring K') :
    (((U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A).subgroupOf U).map
        ((fixedFieldCME U hUcl hUopen) : ↥U →* (K' ≃ₐ[↥(fixedFieldOf U)] K')))
      = NK.BrauerHasse.stabSubgroup (K := ↥(fixedFieldOf U)) (K' := K') A := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    exact (smul_eq_of_coe_eq (fixedFieldOf U) A _ _ (coe_fixedFieldCME U hUcl hUopen x)).trans
      ((MulAction.mem_stabilizer_iff (G := Gal(K'/K)) (a := A)).mp hx.2)
  · intro hy
    have hyA : y • A = A :=
      (MulAction.mem_stabilizer_iff (G := K' ≃ₐ[↥(fixedFieldOf U)] K') (a := A)).mp hy
    refine ⟨(fixedFieldCME U hUcl hUopen).symm y, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨((fixedFieldCME U hUcl hUopen).symm y).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      have hcoe : ⇑(((fixedFieldCME U hUcl hUopen).symm y : ↥U) : Gal(K'/K)) = ⇑y := by
        rw [← coe_fixedFieldCME U hUcl hUopen ((fixedFieldCME U hUcl hUopen).symm y)]
        simp
      exact (smul_eq_of_coe_eq (fixedFieldOf U) A y
        ((fixedFieldCME U hUcl hUopen).symm y : ↥U) hcoe.symm).symm.trans hyA
    · exact MulEquiv.apply_symm_apply _ y

/-! ## The local group isomorphism at a place -/

/-- **The local group isomorphism.**  The decomposition group of `A` for the pair
`(K'/K, U)` is canonically isomorphic to the stabiliser of `A` inside `Gal(K'/K'^U)`, via the
Galois correspondence. -/
noncomputable def localGroupEquiv (U : Subgroup Gal(K'/K)) (hUcl : IsClosed (U : Set Gal(K'/K)))
    (hUopen : IsOpen (U : Set Gal(K'/K))) (A : ValuationSubring K') :
    ↥(U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A) ≃*
      ↥((⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) ⊓
        NK.BrauerHasse.stabSubgroup (K := ↥(fixedFieldOf U)) (K' := K') A) where
  toFun x :=
    ⟨fixedFieldCME U hUcl hUopen ⟨x.1, x.2.1⟩, by
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      refine ⟨trivial, ?_⟩
      have h1 := smul_eq_of_coe_eq (fixedFieldOf U) A
        (fixedFieldCME U hUcl hUopen ⟨x.1, x.2.1⟩) (x.1 : Gal(K'/K))
        (coe_fixedFieldCME U hUcl hUopen ⟨x.1, x.2.1⟩)
      have h2 : x.1 • A = A :=
        (MulAction.mem_stabilizer_iff (G := Gal(K'/K)) (a := A)).mp x.2.2
      rw [h2] at h1
      exact h1⟩
  invFun y :=
    ⟨(((fixedFieldCME U hUcl hUopen).symm y.1 : ↥U) : Gal(K'/K)), by
      rw [Subgroup.mem_inf]
      refine ⟨((fixedFieldCME U hUcl hUopen).symm y.1).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      have hcoe : ⇑(((fixedFieldCME U hUcl hUopen).symm y.1 : ↥U) : Gal(K'/K)) = ⇑y.1 := by
        rw [← coe_fixedFieldCME U hUcl hUopen ((fixedFieldCME U hUcl hUopen).symm y.1)]
        simp
      have h1 := smul_eq_of_coe_eq (fixedFieldOf U) A y.1
        ((fixedFieldCME U hUcl hUopen).symm y.1 : ↥U) hcoe.symm
      have h2 : y.1 • A = A :=
        (MulAction.mem_stabilizer_iff (G := K' ≃ₐ[↥(fixedFieldOf U)] K') (a := A)).mp y.2.2
      rw [h2] at h1
      exact h1.symm⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    show (fixedFieldCME U hUcl hUopen ⟨(x * y).1, (x * y).2.1⟩ :
        K' ≃ₐ[↥(fixedFieldOf U)] K') =
      (fixedFieldCME U hUcl hUopen ⟨x.1, x.2.1⟩) * (fixedFieldCME U hUcl hUopen ⟨y.1, y.2.1⟩)
    rw [show (⟨(x * y).1, (x * y).2.1⟩ : ↥U) = ⟨x.1, x.2.1⟩ * ⟨y.1, y.2.1⟩ from
      Subtype.ext rfl]
    exact map_mul _ _ _

/-- The underlying function of `localGroupEquiv` is the Galois correspondence. -/
theorem localGroupEquiv_val (U : Subgroup Gal(K'/K)) (hUcl : IsClosed (U : Set Gal(K'/K)))
    (hUopen : IsOpen (U : Set Gal(K'/K))) (A : ValuationSubring K')
    (x : ↥(U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A)) :
    ((localGroupEquiv U hUcl hUopen A x :
        ↥((⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) ⊓
          NK.BrauerHasse.stabSubgroup (K := ↥(fixedFieldOf U)) (K' := K') A)) :
        K' ≃ₐ[↥(fixedFieldOf U)] K') =
      fixedFieldCME U hUcl hUopen ⟨x.1, x.2.1⟩ := rfl


/-! ## The place of `K'^U` below a place over a finite prime of `K` -/

/-- A place of `K'` over a finite prime of `K` is also over a finite prime of `K'^U`. -/
theorem comap_fixedField_ne_top (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') ≠ ⊤) :
    A.comap (algebraMap ↥(fixedFieldOf U) K') ≠ ⊤ := by
  intro htop
  apply hA
  rw [IsScalarTower.algebraMap_eq K ↥(fixedFieldOf U) K', ← ValuationSubring.comap_comap, htop]
  ext x
  simp [ValuationSubring.mem_comap]


/-- `ζ` lies in the fixed field of every subgroup contained in `rootFix ζ`. -/
theorem mem_fixedField_of_le_rootFix (U : Subgroup Gal(K'/K)) (ζ : K')
    (hUζ : U ≤ rootFix (K := K) (K' := K') ζ) : ζ ∈ fixedFieldOf U := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact (IntermediateField.mem_fixingSubgroup_iff
    (IntermediateField.adjoin K ({ζ} : Set K')) σ).mp (hUζ hσ) ζ
    (IntermediateField.mem_adjoin_simple_self K ζ)

/-- Places in different `U`-orbits are in different orbits of the full group over `K'^U`. -/
theorem not_inOrbit_top_of_not_inOrbit (U : Subgroup Gal(K'/K)) (hUcl : IsClosed (U : Set Gal(K'/K)))
    {A B : ValuationSubring K'} (h : ¬ InOrbit (K := K) (K' := K') U A B) :
    ¬ InOrbit (K := ↥(fixedFieldOf U)) (K' := K')
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A B := by
  intro hAB
  obtain ⟨v, -, hv⟩ := hAB
  have hFix : (fixedFieldOf U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUcl⟩
  have hmem : AlgEquiv.restrictScalars K v ∈ (fixedFieldOf U).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    simpa using AlgEquiv.commutes v (⟨x, hx⟩ : ↥(fixedFieldOf U))
  refine h ⟨AlgEquiv.restrictScalars K v, ?_, ?_⟩
  · rwa [hFix] at hmem
  · exact (smul_eq_of_coe_eq (fixedFieldOf U) A v (AlgEquiv.restrictScalars K v) rfl).symm.trans hv


/-! ## Elementary compatibility lemmas for the local inflation maps (general form) -/

/-- Element-wise transitivity of the local inflations at a place. -/
lemma localLevelMap_trans_apply_gen (p : ℕ) {K' κ : Type} [Field K'] [Field κ]
    [Algebra κ K'] [IsSepClosure κ K']
    (V : Subgroup Gal(K'/κ)) (A : ValuationSubring K')
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField κ K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃)
    (x : NK.BrauerHasse.LocalLevelH2 (K := κ) (K' := K') p V A L₁) :
    (NK.BrauerHasse.localLevelMap (K := κ) (K' := K') p V A h₂)
        ((NK.BrauerHasse.localLevelMap (K := κ) (K' := K') p V A h₁) x) =
      (NK.BrauerHasse.localLevelMap (K := κ) (K' := K') p V A (h₁.trans h₂)) x := by
  have h := congrArg (fun f => f x)
    (NK.BrauerHasse.localLevelMap_comp (K := κ) (K' := K') p V A h₁ h₂)
  simpa [CategoryTheory.comp_apply] using h

/-- The local inflation does not depend on the proof of the level inclusion. -/
lemma localLevelMap_apply_proof_irrel_gen (p : ℕ) {K' κ : Type} [Field K'] [Field κ]
    [Algebra κ K'] [IsSepClosure κ K']
    (V : Subgroup Gal(K'/κ)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField κ K'} {h h' : L ≤ L'}
    (x : NK.BrauerHasse.LocalLevelH2 (K := κ) (K' := K') p V A L) :
    (NK.BrauerHasse.localLevelMap (K := κ) (K' := K') p V A h) x =
      (NK.BrauerHasse.localLevelMap (K := κ) (K' := K') p V A h') x := by
  rw [Subsingleton.elim h h']

/-! ## The level-aligned local transport (construction used by `localTransport`) -/

namespace HTO

variable (U : Subgroup Gal(K'/K)) (hUcl : IsClosed (U : Set Gal(K'/K)))
  (hUopen : IsOpen (U : Set Gal(K'/K))) [hsc : IsSepClosure ↥(fixedFieldOf U) K']

/-- The transport data, as an abbreviation. -/
noncomputable abbrev tdata : HT.Tr K K' ↥(fixedFieldOf U) K' := trData U hUcl hUopen hsc

/-- The `F`-level aligned with the `K`-level `L`. -/
noncomputable abbrev flev (L : FiniteGaloisIntermediateField K K') :
    FiniteGaloisIntermediateField ↥(fixedFieldOf U) K' :=
  HT.tlf (tdata U hUcl hUopen) L

/-- The stabiliser denominator in the target is the image of the source denominator. -/
theorem localIso_image (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    ((L.fixingSubgroup.subgroupOf (U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A)).map
        ((localGroupEquiv U hUcl hUopen A).toMonoidHom)) =
      (flev U hUcl hUopen L).fixingSubgroup.subgroupOf
        ((⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) ⊓
          NK.BrauerHasse.stabSubgroup (K := ↥(fixedFieldOf U)) (K' := K') A) := by
  classical
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, HT.tlf_fixingSubgroup, HT.tsub,
    Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, hxΦ⟩
    refine ⟨⟨x.1, x.2.1⟩, hx, ?_⟩
    rw [← hxΦ]
    exact (localGroupEquiv_val U hUcl hUopen A x).symm
  · rintro ⟨u, hu, heu⟩
    have hcoe : ⇑y.1 = ⇑(u.1 : Gal(K'/K)) := by
      rw [← heu]
      exact (coe_fixedFieldCME U hUcl hUopen u).symm
    have huD : u.1 ∈ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A := by
      rw [MulAction.mem_stabilizer_iff]
      exact (smul_eq_of_coe_eq (fixedFieldOf U) A y.1 (u.1 : Gal(K'/K)) hcoe).symm.trans
        ((MulAction.mem_stabilizer_iff
          (G := K' ≃ₐ[↥(fixedFieldOf U)] K') (a := A)).mp y.2.2)
    refine ⟨⟨u.1, u.2, huD⟩, hu, ?_⟩
    exact Subtype.ext ((localGroupEquiv_val U hUcl hUopen A ⟨u.1, u.2, huD⟩).trans heu)

/-- **The level-aligned local group isomorphism.** -/
noncomputable def localIso (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.LocalLevelGroup (K := K) (K' := K') U A L ≃*
      NK.BrauerHasse.LocalLevelGroup (K := ↥(fixedFieldOf U)) (K' := K')
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L) :=
  QuotientGroup.congr _ _ (localGroupEquiv U hUcl hUopen A)
    (localIso_image U hUcl hUopen A L)

@[simp]
lemma localIso_mk' (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (x : ↥(U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A)) :
    (localIso U hUcl hUopen A L).toMonoidHom
        (QuotientGroup.mk'
          (L.fixingSubgroup.subgroupOf (U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A))
          x) =
      QuotientGroup.mk'
        ((flev U hUcl hUopen L).fixingSubgroup.subgroupOf
          ((⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) ⊓
            NK.BrauerHasse.stabSubgroup (K := ↥(fixedFieldOf U)) (K' := K') A))
        (localGroupEquiv U hUcl hUopen A x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

/-- The computation rule for `localIso` on a representative. -/
lemma localIso_apply_coe (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (x : ↥(U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A)) :
    (localIso U hUcl hUopen A L).toMonoidHom ↑x =
      ↑((localGroupEquiv U hUcl hUopen A) x) :=
  QuotientGroup.congr_mk _ _ _ _ x

/-- **Naturality of the local level isomorphisms with the inflation maps.** -/
lemma localIso_natural (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    (NK.BrauerHasse.localLevelQuotHom (K := ↥(fixedFieldOf U)) (K' := K')
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A
        (HT.tlf_le (tdata U hUcl hUopen) h)).comp
        (localIso U hUcl hUopen A L').toMonoidHom =
      (localIso U hUcl hUopen A L).toMonoidHom.comp
        (NK.BrauerHasse.localLevelQuotHom (K := K) (K' := K') U A h) := by
  ext x
  simp only [MonoidHom.comp_apply]
  simp only [localIso_mk', localIso_apply_coe, NK.BrauerHasse.localLevelQuotHom,
    QuotientGroup.map_mk', MonoidHom.id_apply]

/-- **The local square**: the global level isomorphism and the local level isomorphism agree on the
localisation of a class. -/
lemma localIso_inclHom (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    (HT.tlfEquiv (tdata U hUcl hUopen) L).toMonoidHom.comp
        (NK.BrauerHasse.localInclHom (K := K) (K' := K') U A L) =
      (NK.BrauerHasse.localInclHom (K := ↥(fixedFieldOf U)) (K' := K')
          (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L)).comp
        (localIso U hUcl hUopen A L).toMonoidHom := by
  ext x
  simp only [MonoidHom.comp_apply, NK.BrauerHasse.localInclHom, QuotientGroup.map_mk',
    MulEquiv.coe_toMonoidHom, localIso_mk']
  rw [HT.tlfEquiv_coe]
  rfl

/-- The level transport, aligned at the `F`-level `HT.tlf` of the `K`-level. -/
noncomputable abbrev locFwd (p : ℕ) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K')
    (c : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A L) :
    NK.BrauerHasse.LocalH2 (K := ↥(fixedFieldOf U)) (K' := K') p ⊤ A :=
  NK.BrauerHasse.LocalH2.ofLevel (K := ↥(fixedFieldOf U)) (K' := K') p ⊤ A
    (flev U hUcl hUopen L)
    ((H2.map (p := p) (localIso U hUcl hUopen A L).symm.toMonoidHom).hom c)

/-- The level-wise transport, before passing to the colimit. -/
noncomputable abbrev locLevelFwd (p : ℕ) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K')
    (c : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A L) :
    NK.BrauerHasse.LocalLevelH2 (K := ↥(fixedFieldOf U)) (K' := K') p
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L) :=
  (H2.map (p := p) (localIso U hUcl hUopen A L).symm.toMonoidHom).hom c

/-- The level-wise inverse of `locLevelFwd`. -/
noncomputable abbrev locTheta (p : ℕ) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K')
    (d : NK.BrauerHasse.LocalLevelH2 (K := ↥(fixedFieldOf U)) (K' := K') p
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L)) :
    NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A L :=
  (H2.map (p := p) (localIso U hUcl hUopen A L).toMonoidHom).hom d

/-- `locTheta` is a left inverse of `locLevelFwd`. -/
lemma locTheta_locLevelFwd (p : ℕ) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K')
    (c : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A L) :
    locTheta U hUcl hUopen p A L (locLevelFwd U hUcl hUopen p A L c) = c := by
  have hcomp : ((localIso U hUcl hUopen A L).symm.toMonoidHom).comp
      ((localIso U hUcl hUopen A L).toMonoidHom) =
      MonoidHom.id (NK.BrauerHasse.LocalLevelGroup (K := K) (K' := K') U A L) := by
    ext x; simp
  rw [locTheta, locLevelFwd, ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
      (f := (localIso U hUcl hUopen A L).symm.toMonoidHom)
      (g := (localIso U hUcl hUopen A L).toMonoidHom) c,
    hcomp, H2.map_id]
  rfl

/-- **The level-wise form of the compatibility of `locLevelFwd` with inflation.** -/
lemma locLevelFwd_levelMap (p : ℕ) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (c : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A L) :
    locLevelFwd U hUcl hUopen p A L'
        ((NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A h) c) =
      (NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (HT.tlf_le (tdata U hUcl hUopen) h))
        (locLevelFwd U hUcl hUopen p A L c) := by
  have hinv : ((localIso U hUcl hUopen A L).symm.toMonoidHom).comp
        (NK.BrauerHasse.localLevelQuotHom (K := ↥(fixedFieldOf U)) (K' := K')
          (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A
          (HT.tlf_le (tdata U hUcl hUopen) h)) =
      (NK.BrauerHasse.localLevelQuotHom (K := K) (K' := K') U A h).comp
        ((localIso U hUcl hUopen A L').symm.toMonoidHom) := by
    ext z
    have hz := congrArg (fun f => (localIso U hUcl hUopen A L).symm
      (f ((localIso U hUcl hUopen A L').symm z)))
      (localIso_natural U hUcl hUopen A h)
    simpa [MonoidHom.comp_apply] using hz
  simp only [locLevelFwd, NK.BrauerHasse.localLevelMap]
  rw [← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := NK.BrauerHasse.localLevelQuotHom (K := K) (K' := K') U A h)
        (g := (localIso U hUcl hUopen A L').symm.toMonoidHom) c,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := (localIso U hUcl hUopen A L).symm.toMonoidHom)
        (g := NK.BrauerHasse.localLevelQuotHom (K := ↥(fixedFieldOf U)) (K' := K')
          (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A
          (HT.tlf_le (tdata U hUcl hUopen) h)) c,
      hinv]

/-- Compatibility of `locFwd` with inflation. -/
lemma locFwd_compat (p : ℕ) (A : ValuationSubring K') :
    ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L')
      (c : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A L),
      locFwd U hUcl hUopen p A L'
        ((NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A h) c) =
      locFwd U hUcl hUopen p A L c := by
  intro L L' h c
  change NK.BrauerHasse.LocalH2.ofLevel (K := ↥(fixedFieldOf U)) (K' := K') p
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L')
      (locLevelFwd U hUcl hUopen p A L'
        ((NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A h) c)) =
    NK.BrauerHasse.LocalH2.ofLevel (K := ↥(fixedFieldOf U)) (K' := K') p
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L)
      (locLevelFwd U hUcl hUopen p A L c)
  rw [locLevelFwd_levelMap,
    ← NK.BrauerHasse.LocalH2.ofLevel_levelMap (K := ↥(fixedFieldOf U)) (K' := K') p
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A
      (HT.tlf_le (tdata U hUcl hUopen) h)
      (a := locLevelFwd U hUcl hUopen p A L c)]

/-- **The local transport** from the local cohomology for `U` to the local cohomology for the full
group over the fixed field. -/
noncomputable def LocPhi (p : ℕ) (A : ValuationSubring K') :
    NK.BrauerHasse.LocalH2 (K := K) (K' := K') p U A →
      NK.BrauerHasse.LocalH2 (K := ↥(fixedFieldOf U)) (K' := K') p ⊤ A :=
  H2Profinite.lift (locFwd U hUcl hUopen p A) (locFwd_compat U hUcl hUopen p A)

@[simp]
lemma LocPhi_ofLevel (p : ℕ) (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (c : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A L) :
    LocPhi U hUcl hUopen p A
        (NK.BrauerHasse.LocalH2.ofLevel (K := K) (K' := K') p U A L c) =
      locFwd U hUcl hUopen p A L c :=
  H2Profinite.lift_ofLevel _ _ L c


@[simp]
lemma LocPhi_ofLevel' (p : ℕ) (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (c : NK.BrauerHasse.LocalLevelH2 (K := K) (K' := K') p U A L) :
    LocPhi U hUcl hUopen p A (H2Profinite.ofLevel (p := p) (U := U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A) L c) =
      locFwd U hUcl hUopen p A L c :=
  H2Profinite.lift_ofLevel _ _ L c

/-- **Injectivity of the local transport.** -/
theorem LocPhi_injective (p : ℕ) (A : ValuationSubring K') :
    Function.Injective (LocPhi U hUcl hUopen p A) := by
  intro x y hxy
  obtain ⟨M, a, rfl⟩ := H2Profinite.ofLevel_surjective (p := p)
    (U := U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A) x
  obtain ⟨M', a', rfl⟩ := H2Profinite.ofLevel_surjective (p := p)
    (U := U ⊓ NK.BrauerHasse.stabSubgroup (K := K) (K' := K') A) y
  have h1 : NK.BrauerHasse.LocalH2.ofLevel (K := ↥(fixedFieldOf U)) (K' := K') p
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen M)
        (locLevelFwd U hUcl hUopen p A M a) =
      NK.BrauerHasse.LocalH2.ofLevel (K := ↥(fixedFieldOf U)) (K' := K') p
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen M')
        (locLevelFwd U hUcl hUopen p A M' a') := by
    simpa only [LocPhi_ofLevel', locFwd] using hxy
  obtain ⟨L'', hLM'', hL'M'', heq⟩ :=
    (NK.BrauerHasse.local_ofLevel_eq_iff (p := p)
      (U := (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K'))) (A := A)
      (locLevelFwd U hUcl hUopen p A M a)
      (locLevelFwd U hUcl hUopen p A M' a')).mp h1
  obtain ⟨M'', hM''⟩ := HT.exists_le_tlf (tdata U hUcl hUopen) L''
  have hPM : M ≤ M ⊔ M' ⊔ M'' := le_trans le_sup_left le_sup_left
  have hPM' : M' ≤ M ⊔ M' ⊔ M'' := le_trans le_sup_right le_sup_left
  have hP3 : M'' ≤ M ⊔ M' ⊔ M'' := le_sup_right
  have hL''P : L'' ≤ flev U hUcl hUopen (M ⊔ M' ⊔ M'') :=
    le_trans hM'' (HT.tlf_le (tdata U hUcl hUopen) hP3)
  have hpsi : locLevelFwd U hUcl hUopen p A (M ⊔ M' ⊔ M'')
        ((NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A hPM) a) =
      locLevelFwd U hUcl hUopen p A (M ⊔ M' ⊔ M'')
        ((NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A hPM') a') := by
    rw [locLevelFwd_levelMap U hUcl hUopen p A hPM a,
      locLevelFwd_levelMap U hUcl hUopen p A hPM' a']
    calc (NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
            (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A
            (HT.tlf_le (tdata U hUcl hUopen) hPM))
          (locLevelFwd U hUcl hUopen p A M a)
        = (NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
            (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (hLM''.trans hL''P))
          (locLevelFwd U hUcl hUopen p A M a) :=
          localLevelMap_apply_proof_irrel_gen (p := p) (κ := ↥(fixedFieldOf U)) (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A _
      _ = (NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
            (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A hL''P)
          ((NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
            (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A hLM'')
            (locLevelFwd U hUcl hUopen p A M a)) :=
          (localLevelMap_trans_apply_gen (p := p) (κ := ↥(fixedFieldOf U)) (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A hLM'' hL''P _).symm
      _ = (NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
            (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A hL''P)
          ((NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
            (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A hL'M'')
            (locLevelFwd U hUcl hUopen p A M' a')) := by rw [heq]
      _ = (NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
            (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (hL'M''.trans hL''P))
          (locLevelFwd U hUcl hUopen p A M' a') :=
          localLevelMap_trans_apply_gen (p := p) (κ := ↥(fixedFieldOf U)) (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A hL'M'' hL''P _
      _ = (NK.BrauerHasse.localLevelMap (K := ↥(fixedFieldOf U)) (K' := K') p
            (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A
            (HT.tlf_le (tdata U hUcl hUopen) hPM'))
          (locLevelFwd U hUcl hUopen p A M' a') :=
          localLevelMap_apply_proof_irrel_gen (p := p) (κ := ↥(fixedFieldOf U)) (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A _
  have key : (NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A hPM) a =
      (NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A hPM') a' :=
    calc (NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A hPM) a
        = locTheta U hUcl hUopen p A (M ⊔ M' ⊔ M'')
            (locLevelFwd U hUcl hUopen p A (M ⊔ M' ⊔ M'')
              ((NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A hPM) a)) :=
          (locTheta_locLevelFwd U hUcl hUopen p A (M ⊔ M' ⊔ M'') _).symm
      _ = locTheta U hUcl hUopen p A (M ⊔ M' ⊔ M'')
            (locLevelFwd U hUcl hUopen p A (M ⊔ M' ⊔ M'')
              ((NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A hPM') a')) := by rw [hpsi]
      _ = (NK.BrauerHasse.localLevelMap (K := K) (K' := K') p U A hPM') a' :=
          locTheta_locLevelFwd U hUcl hUopen p A (M ⊔ M' ⊔ M'') _
  change NK.BrauerHasse.LocalH2.ofLevel (K := K) (K' := K') p U A M a =
    NK.BrauerHasse.LocalH2.ofLevel (K := K) (K' := K') p U A M' a'
  rw [← NK.BrauerHasse.LocalH2.ofLevel_levelMap (K := K) (K' := K') p U A hPM a,
    ← NK.BrauerHasse.LocalH2.ofLevel_levelMap (K := K) (K' := K') p U A hPM' a', key]

/-- **The level-wise compatibility of the local transport with the global transport.** -/
lemma locLevelFwd_locLevel (p : ℕ) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 (K := K) (K' := K') p U L) :
    locLevelFwd U hUcl hUopen p A L
        (locLevel (K := K) (K' := K') p U A L a) =
      locLevel (K := ↥(fixedFieldOf U)) (K' := K') p
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L)
        (HT.psi p (tdata U hUcl hUopen) L a) := by
  have hsq' : (NK.BrauerHasse.localInclHom (K := K) (K' := K') U A L).comp
        ((localIso U hUcl hUopen A L).symm.toMonoidHom) =
      ((HT.tlfEquiv (tdata U hUcl hUopen) L).symm.toMonoidHom).comp
        (NK.BrauerHasse.localInclHom (K := ↥(fixedFieldOf U)) (K' := K')
          (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L)) := by
    ext z
    have hz := congrArg (fun f => (HT.tlfEquiv (tdata U hUcl hUopen) L).symm
      (f ((localIso U hUcl hUopen A L).symm z))) (localIso_inclHom U hUcl hUopen A L)
    simpa [MonoidHom.comp_apply] using hz
  simp only [locLevelFwd, NK.BrauerHasse.locLevel, HT.psi, NK.BrauerHasse.localLevelMap]
  rw [← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := NK.BrauerHasse.localInclHom (K := K) (K' := K') U A L)
        (g := (localIso U hUcl hUopen A L).symm.toMonoidHom) a,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := (HT.tlfEquiv (tdata U hUcl hUopen) L).symm.toMonoidHom)
        (g := NK.BrauerHasse.localInclHom (K := ↥(fixedFieldOf U)) (K' := K')
          (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L)) a,
      hsq']

/-- **The compatibility of the local transport with the global transport** (naturality of
`LocPhi` with respect to the localisation maps). -/
theorem LocPhi_loc (p : ℕ) (A : ValuationSubring K') (hA : A.comap (algebraMap K K') ≠ ⊤)
    (x : H2Profinite (K := K) (K' := K') p U) :
    LocPhi U hUcl hUopen p A
        (H2Profinite.loc (K := K) (K' := K') p U x ⟨A, hA⟩) =
      H2Profinite.loc (K := ↥(fixedFieldOf U)) (K' := K') p
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K'))
        (HT.Phi p (tdata U hUcl hUopen) x) ⟨A, comap_fixedField_ne_top U A hA⟩ := by
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  rw [H2Profinite.loc_ofLevel_apply (K := K) (K' := K') p U L a ⟨A, hA⟩]
  simp only [HT.Phi, HT.fwd, H2Profinite.lift_ofLevel]
  rw [H2Profinite.loc_ofLevel_apply (K := ↥(fixedFieldOf U)) (K' := K') p
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) (flev U hUcl hUopen L)
      (HT.psi p (tdata U hUcl hUopen) L a) ⟨A, comap_fixedField_ne_top U A hA⟩]
  change NK.BrauerHasse.LocalH2.ofLevel (K := ↥(fixedFieldOf U)) (K' := K') p
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L)
      (locLevelFwd U hUcl hUopen p A L
        ((NK.BrauerHasse.locLevel (K := K) (K' := K') p U A L) a)) =
    NK.BrauerHasse.LocalH2.ofLevel (K := ↥(fixedFieldOf U)) (K' := K') p
      (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L)
      ((NK.BrauerHasse.locLevel (K := ↥(fixedFieldOf U)) (K' := K') p
        (⊤ : Subgroup (K' ≃ₐ[↥(fixedFieldOf U)] K')) A (flev U hUcl hUopen L))
        (HT.psi p (tdata U hUcl hUopen) L a))
  rw [locLevelFwd_locLevel]


end HTO

/-! ## The local transport (interface) -/

/-- **The local transport at a place.**  There is an injective map from the local cohomology of `U`
at the place `A` (for the pair `K'/K`) to the local cohomology of the full group over `K'^U` at the
same place, intertwining the localisation maps with the global transport `HT.Phi`.

This is the interface used by the assembly of `hasseSurj_of_top`: the only properties of the local
transport that the assembly needs are injectivity and the compatibility with the global transport. -/
theorem exists_localTransport (p : ℕ) (U : Subgroup Gal(K'/K))
    (hUcl : IsClosed (U : Set Gal(K'/K))) (hUopen : IsOpen (U : Set Gal(K'/K)))
    [hsc : IsSepClosure ↥(fixedFieldOf U) K']
    (A : ValuationSubring K') (hA : A.comap (algebraMap K K') ≠ ⊤) :
    ∃ Φ : NK.BrauerHasse.LocalH2 (K := K) (K' := K') p U A →
        NK.BrauerHasse.LocalH2 (K := ↥(fixedFieldOf U)) (K' := K') p ⊤ A,
      Function.Injective Φ ∧
        ∀ x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U,
          Φ (NK.BrauerHasse.H2Profinite.loc p U x ⟨A, hA⟩) =
            NK.BrauerHasse.H2Profinite.loc (K := ↥(fixedFieldOf U)) (K' := K') p ⊤
              (HT.Phi p (trData U hUcl hUopen hsc) x)
              ⟨A, comap_fixedField_ne_top U A hA⟩ :=
  ⟨HTO.LocPhi U hUcl hUopen p A, HTO.LocPhi_injective U hUcl hUopen p A,
    fun x => HTO.LocPhi_loc U hUcl hUopen p A hA x⟩


end NK.NUV2.LC.RouteB
