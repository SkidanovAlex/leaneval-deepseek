import Mathlib
import Submission.NK.LocalCFT.Brauer.Basic
import Submission.NK.LocalCFT.Brauer.localH2Nonvanishing_iff_surviving

/-!
# Transport of the level systems of `H²(·, ℤ/p)` along a group isomorphism

For a closed subgroup `H ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` (with every finite-index subgroup
of either group open), the defining level systems of the two profinite cohomologies
`NK.BrauerHasse.H2Profinite p H` and `NK.BrauerHasse.H2Profinite p ⊤` are matched by the
infinite Galois correspondence:

* the level subgroup of `M : FiniteGaloisIntermediateField K K'` is
  `N_M = H ∩ Gal(K'/M)`, and its image `e(N_M) ≤ Gal(κ'/κ)` is an open normal subgroup;
* by the fundamental theorem of infinite Galois theory
  (`InfiniteGalois.fixingSubgroup_fixedField`), `e(N_M)` is the fixing subgroup of its fixed field
  `L_M = (e(N_M))^{fix}` (`transportLevelField`), which is a finite Galois level of `κ'/κ`;
* `e` therefore induces an isomorphism of the finite quotients
  `LevelGroup H M ≃* LevelGroup ⊤ L_M` (`levelMulEquiv`), compatible with the inflation maps
  (`levelQuotHom_comp_levelMulEquiv`).

-/

open CategoryTheory
open scoped Pointwise
universe u

namespace NK.LocalCFT.Brauer

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {K K' κ κ' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
  [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

lemma fixingSubgroup_finiteIndex (L : FiniteGaloisIntermediateField K K') :
    L.fixingSubgroup.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff]
  show L.toIntermediateField.fixingSubgroup.index ≠ 0
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index (E' := K') L.toIntermediateField]
  exact (Module.finrank_pos (R := K) (M := ↥L.toIntermediateField)).ne'

/-- The image `e(N_M) ≤ Gal(κ'/κ)` of the level subgroup `N_M = H ∩ Gal(K'/M)` under `e`. -/
noncomputable def transportSubgroup (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (M : FiniteGaloisIntermediateField K K') : Subgroup Gal(κ'/κ) :=
  (M.fixingSubgroup.subgroupOf H).map (e : ↥H →* Gal(κ'/κ))

lemma transportSubgroup_normal (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (M : FiniteGaloisIntermediateField K K') : (transportSubgroup H e M).Normal :=
  Subgroup.Normal.map (Subgroup.normal_subgroupOf (N := M.fixingSubgroup) (H := H))
    (e : ↥H →* Gal(κ'/κ)) e.surjective

lemma transportSubgroup_finiteIndex (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (M : FiniteGaloisIntermediateField K K') : (transportSubgroup H e M).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  haveI h1 : M.fixingSubgroup.FiniteIndex := fixingSubgroup_finiteIndex M
  haveI h2 : (M.fixingSubgroup.subgroupOf H).FiniteIndex :=
    Subgroup.instFiniteIndex_subgroupOf M.fixingSubgroup H
  haveI h3 : (transportSubgroup H e M).Normal := transportSubgroup_normal H e M
  refine Finite.of_equiv (↥H ⧸ (M.fixingSubgroup.subgroupOf H))
    ((QuotientGroup.congr (M.fixingSubgroup.subgroupOf H) (transportSubgroup H e M) e ?_).toEquiv)
  rfl

lemma transportSubgroup_isOpen (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (M : FiniteGaloisIntermediateField K K') : IsOpen (transportSubgroup H e M : Set Gal(κ'/κ)) :=
  hopenκ _ (transportSubgroup_finiteIndex H e M)

lemma transportSubgroup_isClosed (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (M : FiniteGaloisIntermediateField K K') : IsClosed (transportSubgroup H e M : Set Gal(κ'/κ)) :=
  Subgroup.isClosed_of_isOpen _ (transportSubgroup_isOpen H e hopenκ M)

/-- The finite Galois level of `κ'/κ` attached to the level `M` of `K'/K`:
the fixed field of `e(N_M)`. -/
noncomputable def transportLevelField (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (M : FiniteGaloisIntermediateField K K') : FiniteGaloisIntermediateField κ κ' :=
  @FiniteGaloisIntermediateField.mk κ κ' _ _ _
    (IntermediateField.fixedField (transportSubgroup H e M)) (by
      rw [← InfiniteGalois.isOpen_iff_finite,
        InfiniteGalois.fixingSubgroup_fixedField
          ⟨transportSubgroup H e M, transportSubgroup_isClosed H e hopenκ M⟩]
      exact transportSubgroup_isOpen H e hopenκ M) (by
      rw [← InfiniteGalois.normal_iff_isGalois,
        InfiniteGalois.fixingSubgroup_fixedField
          ⟨transportSubgroup H e M, transportSubgroup_isClosed H e hopenκ M⟩]
      exact transportSubgroup_normal H e M)

lemma transportLevelField_fixingSubgroup (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (M : FiniteGaloisIntermediateField K K') :
    (transportLevelField H e hopenκ M).fixingSubgroup = transportSubgroup H e M :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨transportSubgroup H e M, transportSubgroup_isClosed H e hopenκ M⟩

lemma map_topEquiv_symm_eq_subgroupOf (G : Type u) [Group G] (K : Subgroup G) :
    Subgroup.map (Subgroup.topEquiv (G := G)).symm.toMonoidHom K
      = K.subgroupOf (⊤ : Subgroup G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Monotonicity: `M ≤ M'` gives `N_{M'} ≤ N_M`, hence `e(N_{M'}) ≤ e(N_M)`,
hence `L_M ≤ L_{M'}`. -/
lemma transportLevelField_le (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    {M M' : FiniteGaloisIntermediateField K K'} (h : M ≤ M') :
    transportLevelField H e hopenκ M ≤ transportLevelField H e hopenκ M' := by
  rw [FiniteGaloisIntermediateField.le_iff]
  show (IntermediateField.fixedField (transportSubgroup H e M))
      ≤ (IntermediateField.fixedField (transportSubgroup H e M'))
  refine IntermediateField.fixedField_le ?_
  rw [transportSubgroup, transportSubgroup]
  exact Subgroup.map_mono (NK.BrauerHasse.fixingSubgroup_subgroupOf_le h H)

/-- The level subgroup of the κ-side: `Gal(κ'/L_M)` inside `⊤`. -/
lemma levelGroupFixSub (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (M : FiniteGaloisIntermediateField K K') :
    (transportLevelField H e hopenκ M).fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(κ'/κ))
      = (M.fixingSubgroup.subgroupOf H).map
          ((e.trans (Subgroup.topEquiv (G := Gal(κ'/κ))).symm :
            ↥H ≃* ↥(⊤ : Subgroup Gal(κ'/κ))) : ↥H →* ↥(⊤ : Subgroup Gal(κ'/κ))) := by
  rw [transportLevelField_fixingSubgroup, transportSubgroup, MulEquiv.coe_monoidHom_trans,
    ← Subgroup.map_map]
  exact (map_topEquiv_symm_eq_subgroupOf (Gal(κ'/κ)) _).symm

/-- **The canonical isomorphism between the level `LevelGroup H M` of the subgroup `H ≤ G_K`
and the level `LevelGroup ⊤ L_M` of the local field, induced by `e`.** -/
noncomputable def levelMulEquiv (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (M : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.LevelGroup H M ≃*
      NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(κ'/κ)) (transportLevelField H e hopenκ M) :=
  QuotientGroup.congr _ _ (e.trans (Subgroup.topEquiv (G := Gal(κ'/κ))).symm)
    (levelGroupFixSub H e hopenκ M).symm

/-- **Cofinality of the level system.**  Every open subgroup `N` of `↥H` contains `N_M = H ∩ Gal(K'/M)`
for some finite Galois intermediate field `M`.  (No closedness of `H` is needed: this is the
statement that the sets `Gal(K'/M)` form a neighbourhood basis of `1` in the Krull topology.) -/
lemma exists_fixingSubgroup_subgroupOf_le_of_isOpen {H : Subgroup Gal(K'/K)} {N : Subgroup ↥H}
    (hN : IsOpen (N : Set ↥H)) :
    ∃ M : FiniteGaloisIntermediateField K K', M.fixingSubgroup.subgroupOf H ≤ N := by
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hN
  have ht1 : (1 : Gal(K'/K)) ∈ t := by
    have : (1 : ↥H) ∈ (N : Set ↥H) := N.one_mem
    rw [← hts] at this
    simpa using this
  have htmem : t ∈ nhds (1 : Gal(K'/K)) := IsOpen.mem_nhds ht ht1
  rw [krullTopology_mem_nhds_one_iff_of_normal] at htmem
  obtain ⟨E, hfd, hnorm, hsub⟩ := htmem
  refine ⟨@FiniteGaloisIntermediateField.mk K K' _ _ _ E hfd ?_, ?_⟩
  · haveI : Normal K ↥E := hnorm
    exact ⟨⟩
  · intro x hx
    rw [← SetLike.mem_coe, ← hts]
    exact hsub hx

/-- **Non-vanishing transfers across an isomorphism of finite groups.**  If `e : G ≃* H` and
`x ≠ 0` in `H²(H, ℤ/p)`, then the image of `x` under the isomorphism `H²(H, ℤ/p) ≃ H²(G, ℤ/p)`
induced by `e` (contravariantly) is again non-zero. -/
lemma H2_map_ne_zero_of_mulEquiv {p : ℕ} {G H : Type u} [Group G] [Group H] (e : G ≃* H)
    (x : NK.BrauerHasse.H2 p H) (hx : x ≠ 0) :
    (NK.BrauerHasse.H2.map (p := p) (e : G →* H)).hom x ≠ 0 := by
  intro h0
  have hid : ((e : G →* H).comp (e.symm : H →* G)) = MonoidHom.id H := by ext y; simp
  have h2 : ((NK.BrauerHasse.H2.map (p := p) (e : G →* H)) ≫
      (NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G))) = 𝟙 (NK.BrauerHasse.H2 p H) := by
    rw [← NK.BrauerHasse.H2.map_comp (f := (e : G →* H)) (g := (e.symm : H →* G)), hid,
      NK.BrauerHasse.H2.map_id]
  have key : (NK.BrauerHasse.H2.map (p := p) (e.symm : H →* G)).hom
      ((NK.BrauerHasse.H2.map (p := p) (e : G →* H)).hom x) = x := by
    have := congrArg (fun (f : NK.BrauerHasse.H2 p H ⟶ NK.BrauerHasse.H2 p H) => f.hom x) h2
    simpa using this
  exact hx (by rw [h0] at key; simpa using key.symm)


/-- **The level `L_M` dominates `L` as soon as `N_M ≤ e⁻¹(Gal(κ'/L))`.** -/
lemma le_transportLevelField (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    {L : FiniteGaloisIntermediateField κ κ'} {M : FiniteGaloisIntermediateField K K'}
    (h : M.fixingSubgroup.subgroupOf H ≤ L.fixingSubgroup.comap (e : ↥H →* Gal(κ'/κ))) :
    L ≤ transportLevelField H e hopenκ M := by
  rw [FiniteGaloisIntermediateField.le_iff]
  show L.toIntermediateField ≤ IntermediateField.fixedField (transportSubgroup H e M)
  rw [← InfiniteGalois.fixedField_fixingSubgroup (k := κ) (K := κ') L.toIntermediateField]
  apply IntermediateField.fixedField_le
  rw [transportSubgroup]
  exact Subgroup.map_le_iff_le_comap.mpr h

/-- Elementwise form of the functoriality `NK.BrauerHasse.H2.map_comp`. -/
lemma H2.map_comp_apply {p : ℕ} {G₁ G₂ G₃ : Type u} [Group G₁] [Group G₂] [Group G₃]
    (f : G₂ →* G₃) (g : G₁ →* G₂) (x : NK.BrauerHasse.H2 p G₃) :
    (NK.BrauerHasse.H2.map (p := p) (f.comp g)).hom x
      = (NK.BrauerHasse.H2.map (p := p) g).hom ((NK.BrauerHasse.H2.map (p := p) f).hom x) := by
  rw [NK.BrauerHasse.H2.map_comp]
  rfl

section Computation

/-- Computation of `levelMulEquiv` on the class of an element of `↥H`. -/
lemma levelMulEquiv_mk' (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (M : FiniteGaloisIntermediateField K K') (x : ↥H) :
    levelMulEquiv H e hopenκ M ((QuotientGroup.mk' (M.fixingSubgroup.subgroupOf H)) x)
      = (QuotientGroup.mk' ((transportLevelField H e hopenκ M).fixingSubgroup.subgroupOf
          (⊤ : Subgroup Gal(κ'/κ))))
          ((e.trans (Subgroup.topEquiv (G := Gal(κ'/κ))).symm) x) := by
  rw [levelMulEquiv, QuotientGroup.congr_mk']

/-- Computation of `levelMulEquiv` on a coerced element. -/
lemma levelMulEquiv_coe (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    (M : FiniteGaloisIntermediateField K K') (x : ↥H) :
    levelMulEquiv H e hopenκ M (x : ↥H ⧸ (M.fixingSubgroup.subgroupOf H))
      = ((e.trans (Subgroup.topEquiv (G := Gal(κ'/κ))).symm) x :
          ↥(⊤ : Subgroup Gal(κ'/κ)) ⧸
            ((transportLevelField H e hopenκ M).fixingSubgroup.subgroupOf
              (⊤ : Subgroup Gal(κ'/κ)))) := by
  rw [levelMulEquiv, QuotientGroup.congr_apply, QuotientGroup.mk'_apply]

/-- **Naturality of the level isomorphisms with the inflation maps.**  For `M ≤ M'` the square
```
  LevelGroup H M' --levelMulEquiv M'--> LevelGroup ⊤ L_M'
        |                                      |
  levelQuotHom                           levelQuotHom
        v                                      v
  LevelGroup H M  --levelMulEquiv M---> LevelGroup ⊤ L_M
```
commutes.  This is the only compatibility used in the transport of a surviving class. -/
lemma levelQuotHom_comp_levelMulEquiv (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    {M M' : FiniteGaloisIntermediateField K K'} (h : M ≤ M') :
    (NK.BrauerHasse.levelQuotHom (U := (⊤ : Subgroup Gal(κ'/κ)))
        (transportLevelField_le H e hopenκ h)).comp
      (levelMulEquiv H e hopenκ M').toMonoidHom
    = (levelMulEquiv H e hopenκ M).toMonoidHom.comp
        (NK.BrauerHasse.levelQuotHom (U := H) h) := by
  apply QuotientGroup.monoidHom_ext
  ext y
  simp only [MonoidHom.comp_apply, NK.BrauerHasse.levelQuotHom, MulEquiv.coe_toMonoidHom,
    levelMulEquiv_mk', levelMulEquiv_coe, QuotientGroup.map_mk', MonoidHom.id_apply]

/-- **The transport of a level class.**  Let `L` be a finite Galois level of `κ'/κ` with
`L ≤ L_M ∩ L_{M'}`, and `a` a class at the level `L`.  Then inflating the transported class at
level `M` up to the level `M'` gives the transported class at level `M'` of the inflation of `a`.

This is the elementwise form of the naturality square `levelQuotHom_comp_levelMulEquiv`, and it is
what makes a *surviving* class survive the transport. -/
lemma levelMap_levelMulEquiv {p : ℕ} (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (hopenκ : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsOpen (U : Set Gal(κ'/κ)))
    {L : FiniteGaloisIntermediateField κ κ'}
    {M M' : FiniteGaloisIntermediateField K K'} (h : M ≤ M')
    (hLM : L ≤ transportLevelField H e hopenκ M)
    (hLM' : L ≤ transportLevelField H e hopenκ M')
    (a : NK.BrauerHasse.LevelH2 p (⊤ : Subgroup Gal(κ'/κ)) L) :
    (NK.BrauerHasse.levelMap p (U := H) h)
        ((NK.BrauerHasse.H2.map (p := p) ((levelMulEquiv H e hopenκ M).toMonoidHom)).hom
          ((NK.BrauerHasse.levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) hLM) a))
      = (NK.BrauerHasse.H2.map (p := p) ((levelMulEquiv H e hopenκ M').toMonoidHom)).hom
          ((NK.BrauerHasse.levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) hLM') a) := by
  simp only [NK.BrauerHasse.levelMap]
  rw [← H2.map_comp_apply (p := p) (f := (levelMulEquiv H e hopenκ M).toMonoidHom)
    (g := NK.BrauerHasse.levelQuotHom (U := H) h)]
  rw [← levelQuotHom_comp_levelMulEquiv H e hopenκ h]
  rw [H2.map_comp_apply]
  rw [← H2.map_comp_apply (p := p)
    (f := NK.BrauerHasse.levelQuotHom (U := (⊤ : Subgroup Gal(κ'/κ))) hLM)
    (g := NK.BrauerHasse.levelQuotHom (U := (⊤ : Subgroup Gal(κ'/κ)))
      (transportLevelField_le H e hopenκ h))]
  rw [NK.BrauerHasse.levelQuotHom_comp hLM (transportLevelField_le H e hopenκ h)]

end Computation


end NK.LocalCFT.Brauer
