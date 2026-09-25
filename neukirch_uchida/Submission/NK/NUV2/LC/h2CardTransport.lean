/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cardinality transport of profinite `H²(·, Z/p)` along a topological group isomorphism

This file proves `NK.NUV2.LC.H2CardTransport`, the *cardinality* form of the transport of the
profinite cohomology `NK.BrauerHasse.H2Profinite p H` (the filtered colimit
`colim_M H²(H/(H ∩ Gal(K'/M)), Z/p)` over the finite Galois levels `M` of `K'/K`) along a
*topological* group isomorphism

  `e : ↥H ≃ₜ* Gal(κ'/κ)`   (`H ≤ Gal(K'/K)` a closed subgroup),

namely

  `Nat.card (H²(H, Z/p)) = Nat.card (H²(Gal(κ'/κ), Z/p))`.

## The mathematics of the transport

Both sides are filtered colimits of `H²(·, Z/p)` over the finite quotients of the respective
profinite group.  The two level systems are matched by the infinite Galois correspondence:

* a finite Galois level `M` of `K'/K` gives the open normal subgroup `N_M = M.fixingSubgroup ∩ H`
  of `↥H`, and `e(N_M)` is an open normal subgroup of `Gal(κ'/κ)`, whose fixed field is a finite
  Galois level `L_M` of `κ'/κ` (here the *homeomorphism* `e` supplies the openness of `e(N_M)`
  from the openness of `N_M`; the uniform hypothesis "every finite-index subgroup of `Gal(κ'/κ)`
  is open" of the earlier transport `NK.LocalCFT.Brauer.transportLevelField` is *not* available
  in this generality, and is not needed: only the images of the level subgroups occur);
* conversely, a finite Galois level `L` of `κ'/κ` has an open preimage in `↥H`, which contains
  some `N_M` by cofinality of the level subgroups, and then `L ≤ L_M`.

Hence the level isomorphisms `H/(H ∩ Gal(K'/M)) ≃* Gal(κ'/L_M)` assemble, compatibly with
inflation, into a bijection of the two colimits.

## Contents

* `HT.tsub`, `HT.Tr` — the transported level subgroup and the bundle of the transport data;
* `HT.tlf`, `HT.tlf_le`, `HT.tlfEquiv`, `HT.levelQuotHom_comp_tlfEquiv`, `HT.le_tlf`,
  `HT.exists_le_tlf` — the level dictionary;
* `HT.psi`, `HT.theta`, `HT.theta_psi`, `HT.psi_theta`, `HT.psi_levelMap` — the level transport on
  cohomology and its compatibility with inflation;
* `HT.fwd`, `HT.Phi`, `HT.Phi_surjective`, `HT.Phi_injective` — the map of colimits and its
  bijectivity;
* `h2CardTransport` — the requested lemma.
-/

import Mathlib
import Submission.NK.NUV2.LC.LeafInputs
import Submission.NK.LocalCFT.Brauer.Transport

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open NK.BrauerHasse

namespace NK.NUV2.LC

namespace HT

universe u

variable {K K' κ κ' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
  [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## §1. The transported level subgroup and the bundle of data -/

/-- The image of the level subgroup `M.fixingSubgroup ∩ H` under `e`. -/
def tsub (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (M : FiniteGaloisIntermediateField K K') : Subgroup Gal(κ'/κ) :=
  (M.fixingSubgroup.subgroupOf H).map (e : ↥H →* Gal(κ'/κ))

lemma tsub_normal (H : Subgroup Gal(K'/K)) (e : ↥H ≃* Gal(κ'/κ))
    (M : FiniteGaloisIntermediateField K K') : (tsub H e M).Normal :=
  Subgroup.Normal.map (Subgroup.normal_subgroupOf (N := M.fixingSubgroup) (H := H))
    (e : ↥H →* Gal(κ'/κ)) e.surjective

/-- The level subgroup of the finite Galois level `M` of `K'/K` is open in `↥H`. -/
lemma subFixOpen (H : Subgroup Gal(K'/K)) (M : FiniteGaloisIntermediateField K K') :
    IsOpen ((M.fixingSubgroup.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  rw [Subgroup.coe_subgroupOf]
  exact (IntermediateField.fixingSubgroup_isOpen M.toIntermediateField).preimage continuous_subtype_val

/-- The level subgroup of the finite Galois level `M` of `K'/K` is closed in `↥H`. -/
lemma subFixClosed (H : Subgroup Gal(K'/K)) (M : FiniteGaloisIntermediateField K K') :
    IsClosed ((M.fixingSubgroup.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  rw [Subgroup.coe_subgroupOf]
  exact (IntermediateField.fixingSubgroup_isClosed M.toIntermediateField).preimage continuous_subtype_val

/-- **The transport data.**  A closed subgroup `H ≤ Gal(K'/K)` together with a group isomorphism
`e : ↥H ≃* Gal(κ'/κ)` for which

* the images `e(N_M)` of the level subgroups are open and closed in `Gal(κ'/κ)`, and
* the preimages `e⁻¹(Gal(κ'/L))` of the level subgroups of `κ'/κ` are open in `↥H`.

For a *homeomorphism* `e` all three conditions are automatic (`tsub_isOpen`, `tsub_isClosed`,
`tsub_pre` below); they are exactly what the level dictionary uses. -/
structure Tr (K K' κ κ' : Type u) [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ'] where
  /-- the subgroup of `Gal(K'/K)` labelled by `Gal(κ'/κ)` -/
  H : Subgroup Gal(K'/K)
  /-- the labelling isomorphism -/
  e : ↥H ≃* Gal(κ'/κ)
  /-- the transported level subgroups are open -/
  hopen : ∀ M : FiniteGaloisIntermediateField K K',
    IsOpen ((tsub H e M : Subgroup Gal(κ'/κ)) : Set Gal(κ'/κ))
  /-- the transported level subgroups are closed -/
  hclosed : ∀ M : FiniteGaloisIntermediateField K K',
    IsClosed ((tsub H e M : Subgroup Gal(κ'/κ)) : Set Gal(κ'/κ))
  /-- the preimages of the level subgroups of `κ'/κ` are open in `↥H` -/
  hpre : ∀ L : FiniteGaloisIntermediateField κ κ',
    IsOpen ((L.fixingSubgroup.comap (e : ↥H →* Gal(κ'/κ)) : Subgroup ↥H) : Set ↥H)

variable (D : Tr K K' κ κ')

/-! ## §2. The level dictionary -/

/-- **The finite Galois level of `κ'/κ` attached to the level `M` of `K'/K`**: the fixed field of
the open normal subgroup `e(N_M)`. -/
noncomputable def tlf (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K') :
    FiniteGaloisIntermediateField κ κ' :=
  @FiniteGaloisIntermediateField.mk κ κ' _ _ _
    (IntermediateField.fixedField (tsub D.H D.e M)) (by
      rw [← InfiniteGalois.isOpen_iff_finite,
        InfiniteGalois.fixingSubgroup_fixedField
          ⟨tsub D.H D.e M, D.hclosed M⟩]
      exact D.hopen M) (by
      rw [← InfiniteGalois.normal_iff_isGalois,
        InfiniteGalois.fixingSubgroup_fixedField
          ⟨tsub D.H D.e M, D.hclosed M⟩]
      exact tsub_normal D.H D.e M)

lemma tlf_fixingSubgroup (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K') :
    (tlf D M).fixingSubgroup = tsub D.H D.e M :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨tsub D.H D.e M, D.hclosed M⟩

/-- Monotonicity of the level dictionary. -/
lemma tlf_le (D : Tr K K' κ κ') {M M' : FiniteGaloisIntermediateField K K'} (h : M ≤ M') :
    tlf D M ≤ tlf D M' := by
  rw [FiniteGaloisIntermediateField.le_iff]
  show (IntermediateField.fixedField (tsub D.H D.e M))
      ≤ (IntermediateField.fixedField (tsub D.H D.e M'))
  refine IntermediateField.fixedField_le ?_
  rw [tsub, tsub]
  exact Subgroup.map_mono (NK.BrauerHasse.fixingSubgroup_subgroupOf_le h D.H)

/-- Transport of the `topEquiv` along the isomorphism `A ↦ A.subgroupOf ⊤`. -/
lemma map_topEquiv_symm_eq_subgroupOf (G : Type u) [Group G] (A : Subgroup G) :
    Subgroup.map (Subgroup.topEquiv (G := G)).symm.toMonoidHom A
      = A.subgroupOf (⊤ : Subgroup G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The level subgroup of the κ-side, as the image of the level subgroup of the K-side. -/
lemma tlf_levelGroupFixSub (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K') :
    (tlf D M).fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(κ'/κ))
      = (M.fixingSubgroup.subgroupOf D.H).map
          ((D.e.trans (Subgroup.topEquiv (G := Gal(κ'/κ))).symm :
            ↥D.H ≃* ↥(⊤ : Subgroup Gal(κ'/κ))) : ↥D.H →* ↥(⊤ : Subgroup Gal(κ'/κ))) := by
  rw [tlf_fixingSubgroup, tsub, MulEquiv.coe_monoidHom_trans, ← Subgroup.map_map]
  exact (map_topEquiv_symm_eq_subgroupOf (Gal(κ'/κ)) _).symm

/-- **The isomorphism of the levels `H/(H ∩ Gal(K'/M)) ≃* Gal(κ'/L_M)`.** -/
noncomputable def tlfEquiv (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K') :
    LevelGroup D.H M ≃* LevelGroup (⊤ : Subgroup Gal(κ'/κ)) (tlf D M) :=
  QuotientGroup.congr _ _ (D.e.trans (Subgroup.topEquiv (G := Gal(κ'/κ))).symm)
    (tlf_levelGroupFixSub D M).symm

lemma tlfEquiv_mk' (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K') (x : ↥D.H) :
    tlfEquiv D M ((QuotientGroup.mk' (M.fixingSubgroup.subgroupOf D.H)) x)
      = (QuotientGroup.mk' ((tlf D M).fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(κ'/κ))))
          ((D.e.trans (Subgroup.topEquiv (G := Gal(κ'/κ))).symm) x) := by
  rw [tlfEquiv, QuotientGroup.congr_mk']

lemma tlfEquiv_coe (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K') (x : ↥D.H) :
    tlfEquiv D M (x : ↥D.H ⧸ (M.fixingSubgroup.subgroupOf D.H))
      = (((D.e.trans (Subgroup.topEquiv (G := Gal(κ'/κ))).symm) x :
          ↥(⊤ : Subgroup Gal(κ'/κ)) ⧸
            ((tlf D M).fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(κ'/κ))))) := by
  rw [tlfEquiv, QuotientGroup.congr_apply, QuotientGroup.mk'_apply]

/-- **Naturality of the level isomorphisms with the inflation maps.** -/
lemma levelQuotHom_comp_tlfEquiv (D : Tr K K' κ κ')
    {M M' : FiniteGaloisIntermediateField K K'} (h : M ≤ M') :
    (levelQuotHom (U := (⊤ : Subgroup Gal(κ'/κ))) (tlf_le D h)).comp (tlfEquiv D M').toMonoidHom
      = (tlfEquiv D M).toMonoidHom.comp (levelQuotHom (U := D.H) h) := by
  apply QuotientGroup.monoidHom_ext
  ext y
  simp only [MonoidHom.comp_apply, levelQuotHom, MulEquiv.coe_toMonoidHom, tlfEquiv_mk',
    tlfEquiv_coe, QuotientGroup.map_mk', MonoidHom.id_apply]

/-- **The level `L_M` dominates `L` as soon as `N_M ≤ e⁻¹(Gal(κ'/L))`.** -/
lemma le_tlf (D : Tr K K' κ κ') {L : FiniteGaloisIntermediateField κ κ'}
    {M : FiniteGaloisIntermediateField K K'}
    (h : M.fixingSubgroup.subgroupOf D.H ≤ L.fixingSubgroup.comap (D.e : ↥D.H →* Gal(κ'/κ))) :
    L ≤ tlf D M := by
  rw [FiniteGaloisIntermediateField.le_iff]
  show L.toIntermediateField ≤ IntermediateField.fixedField (tsub D.H D.e M)
  rw [← InfiniteGalois.fixedField_fixingSubgroup (k := κ) (K := κ') L.toIntermediateField]
  apply IntermediateField.fixedField_le
  rw [tsub]
  exact Subgroup.map_le_iff_le_comap.mpr h

/-- **Cofinality of the level dictionary**: every finite Galois level `L` of `κ'/κ` is contained in
some `L_M`. -/
lemma exists_le_tlf (D : Tr K K' κ κ') (L : FiniteGaloisIntermediateField κ κ') :
    ∃ M : FiniteGaloisIntermediateField K K', L ≤ tlf D M := by
  obtain ⟨M, hM⟩ := NK.LocalCFT.Brauer.exists_fixingSubgroup_subgroupOf_le_of_isOpen (D.hpre L)
  exact ⟨M, le_tlf D hM⟩

/-! ## §3. The transport on the level cohomologies -/

/-- The level transport `H²(H/N_M, Z/p) → H²(Gal(κ'/L_M), Z/p)`. -/
noncomputable def psi (p : ℕ) (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p D.H M) : LevelH2 p (⊤ : Subgroup Gal(κ'/κ)) (tlf D M) :=
  (H2.map (p := p) ((tlfEquiv D M).symm.toMonoidHom)).hom a

/-- The level transport `H²(Gal(κ'/L_M), Z/p) → H²(H/N_M, Z/p)`. -/
noncomputable def theta (p : ℕ) (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K')
    (b : LevelH2 p (⊤ : Subgroup Gal(κ'/κ)) (tlf D M)) : LevelH2 p D.H M :=
  (H2.map (p := p) ((tlfEquiv D M).toMonoidHom)).hom b

lemma theta_psi (p : ℕ) (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p D.H M) : theta p D M (psi p D M a) = a := by
  have hcomp : ((tlfEquiv D M).symm.toMonoidHom).comp ((tlfEquiv D M).toMonoidHom)
      = MonoidHom.id (LevelGroup D.H M) := by
    ext x; simp
  rw [theta, psi, ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
      (f := (tlfEquiv D M).symm.toMonoidHom) (g := (tlfEquiv D M).toMonoidHom) a,
    hcomp, H2.map_id]
  rfl

lemma psi_theta (p : ℕ) (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K')
    (b : LevelH2 p (⊤ : Subgroup Gal(κ'/κ)) (tlf D M)) : psi p D M (theta p D M b) = b := by
  have hcomp : ((tlfEquiv D M).toMonoidHom).comp ((tlfEquiv D M).symm.toMonoidHom)
      = MonoidHom.id (LevelGroup (⊤ : Subgroup Gal(κ'/κ)) (tlf D M)) := by
    ext x; simp
  rw [psi, theta, ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
      (f := (tlfEquiv D M).toMonoidHom) (g := (tlfEquiv D M).symm.toMonoidHom) b,
    hcomp, H2.map_id]
  rfl

/-- **`psi` is compatible with inflation.** -/
lemma psi_levelMap (p : ℕ) (D : Tr K K' κ κ') {M M' : FiniteGaloisIntermediateField K K'}
    (h : M ≤ M') (a : LevelH2 p D.H M) :
    psi p D M' ((levelMap p (U := D.H) h) a)
      = (levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) (tlf_le D h)) (psi p D M a) := by
  have hnat := levelQuotHom_comp_tlfEquiv D h
  have hhom : ((levelQuotHom (U := D.H) h)).comp ((tlfEquiv D M').symm.toMonoidHom)
      = ((tlfEquiv D M).symm.toMonoidHom).comp
          (levelQuotHom (U := (⊤ : Subgroup Gal(κ'/κ))) (tlf_le D h)) := by
    refine MonoidHom.ext fun y => ?_
    show (levelQuotHom (U := D.H) h) ((tlfEquiv D M').symm y)
      = (tlfEquiv D M).symm ((levelQuotHom (U := (⊤ : Subgroup Gal(κ'/κ))) (tlf_le D h)) y)
    apply (tlfEquiv D M).injective
    rw [MulEquiv.apply_symm_apply]
    have h2 := congrFun (congrArg DFunLike.coe hnat) ((tlfEquiv D M').symm y)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      using h2.symm
  simp only [psi, levelMap]
  rw [← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := levelQuotHom (U := D.H) h) (g := (tlfEquiv D M').symm.toMonoidHom) a,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := (tlfEquiv D M).symm.toMonoidHom)
        (g := levelQuotHom (U := (⊤ : Subgroup Gal(κ'/κ))) (tlf_le D h)) a,
      hhom]

/-! ## §4. The map of the colimits -/

/-- The forward level family: a class at the level `M` of `H` is sent to the corresponding class at
the level `L_M` of `Gal(κ'/κ)`. -/
noncomputable def fwd (p : ℕ) (D : Tr K K' κ κ') (M : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p D.H M) : H2Profinite p (⊤ : Subgroup Gal(κ'/κ)) :=
  H2Profinite.ofLevel (tlf D M) (psi p D M a)

lemma fwd_compat (p : ℕ) (D : Tr K K' κ κ') :
    ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p D.H L),
      fwd p D L' ((levelMap p (U := D.H) h) a) = fwd p D L a := by
  intro L L' h a
  rw [fwd, fwd, ← H2Profinite.ofLevel_levelMap (p := p) (U := (⊤ : Subgroup Gal(κ'/κ)))
    (h := tlf_le D h) (a := psi p D L a)]
  congr 1
  exact psi_levelMap p D h a

/-- **The transport map of the colimits** `H²(H, Z/p) → H²(Gal(κ'/κ), Z/p)`. -/
noncomputable def Phi (p : ℕ) (D : Tr K K' κ κ') :
    H2Profinite p D.H → H2Profinite p (⊤ : Subgroup Gal(κ'/κ)) :=
  H2Profinite.lift (fwd p D) (fwd_compat p D)

/-- **Surjectivity.**  Every class of `H²(Gal(κ'/κ), Z/p)` is represented at some level `L`; the
cofinality of the level dictionary (`exists_le_tlf`) inflates it to a level `L_M` in the image of
`Phi`. -/
theorem Phi_surjective (p : ℕ) (D : Tr K K' κ κ') : Function.Surjective (Phi p D) := by
  intro y
  obtain ⟨L, b, rfl⟩ := H2Profinite.ofLevel_surjective y
  obtain ⟨M, hM⟩ := exists_le_tlf D L
  refine ⟨H2Profinite.ofLevel M
    (theta p D M ((levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) hM) b)), ?_⟩
  rw [Phi, H2Profinite.lift_ofLevel, fwd, psi_theta]
  exact H2Profinite.ofLevel_levelMap hM b

/-- **Injectivity.**  Two classes with the same image agree on a common finite level: one passes to a
common upper bound of the two levels and of a level dominating the κ-level on which the equality is
seen, and uses the compatibility of `psi` with inflation. -/
theorem Phi_injective (p : ℕ) (D : Tr K K' κ κ') : Function.Injective (Phi p D) := by
  intro x y hxy
  obtain ⟨M, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  obtain ⟨M', a', rfl⟩ := H2Profinite.ofLevel_surjective y
  have h1 : H2Profinite.ofLevel (tlf D M) (psi p D M a)
      = H2Profinite.ofLevel (tlf D M') (psi p D M' a') := by
    simpa [Phi, fwd] using hxy
  obtain ⟨L'', hLM'', hL'M'', heq⟩ :=
    (NK.BrauerHasse.ofLevel_eq_iff (p := p) (U := (⊤ : Subgroup Gal(κ'/κ)))
      (psi p D M a) (psi p D M' a')).mp h1
  obtain ⟨M'', hM''⟩ := exists_le_tlf D L''
  have hPM : M ≤ M ⊔ M' ⊔ M'' := le_trans le_sup_left le_sup_left
  have hPM' : M' ≤ M ⊔ M' ⊔ M'' := le_trans le_sup_right le_sup_left
  have hP3 : M'' ≤ M ⊔ M' ⊔ M'' := le_sup_right
  have hL''P : L'' ≤ tlf D (M ⊔ M' ⊔ M'') := le_trans hM'' (tlf_le D hP3)
  have hpsi : psi p D (M ⊔ M' ⊔ M'') ((levelMap p (U := D.H) hPM) a)
      = psi p D (M ⊔ M' ⊔ M'') ((levelMap p (U := D.H) hPM') a') := by
    rw [psi_levelMap p D hPM a, psi_levelMap p D hPM' a']
    calc (levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) (tlf_le D hPM)) (psi p D M a)
        = (levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) (hLM''.trans hL''P))
            (psi p D M a) :=
          NK.BrauerHasse.levelMap_apply_proof_irrel _
      _ = (levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) hL''P)
            ((levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) hLM'') (psi p D M a)) :=
          (NK.BrauerHasse.levelMap_trans_apply hLM'' hL''P _).symm
      _ = (levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) hL''P)
            ((levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) hL'M'') (psi p D M' a')) := by rw [heq]
      _ = (levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) (hL'M''.trans hL''P))
            (psi p D M' a') :=
          NK.BrauerHasse.levelMap_trans_apply hL'M'' hL''P _
      _ = (levelMap p (U := (⊤ : Subgroup Gal(κ'/κ))) (tlf_le D hPM')) (psi p D M' a') :=
          NK.BrauerHasse.levelMap_apply_proof_irrel _
  have key : (levelMap p (U := D.H) hPM) a = (levelMap p (U := D.H) hPM') a' :=
    calc (levelMap p (U := D.H) hPM) a
        = theta p D (M ⊔ M' ⊔ M'')
            (psi p D (M ⊔ M' ⊔ M'') ((levelMap p (U := D.H) hPM) a)) :=
          (theta_psi p D (M ⊔ M' ⊔ M'') _).symm
      _ = theta p D (M ⊔ M' ⊔ M'')
            (psi p D (M ⊔ M' ⊔ M'') ((levelMap p (U := D.H) hPM') a')) := by rw [hpsi]
      _ = (levelMap p (U := D.H) hPM') a' := theta_psi p D (M ⊔ M' ⊔ M'') _
  rw [← H2Profinite.ofLevel_levelMap (p := p) (U := D.H) (h := hPM) (a := a),
    ← H2Profinite.ofLevel_levelMap (p := p) (U := D.H) (h := hPM') (a := a')]
  rw [key]

end HT

/-! ## §5. The homeomorphism supplies the transport data -/

namespace HT

universe u

variable {K K' κ κ' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
  [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The openness of the transported level subgroups** comes from the homeomorphism: it is the
image of the open level subgroup `M.fixingSubgroup ∩ H` under the open map `e`. -/
lemma tsub_isOpen (H : Subgroup Gal(K'/K)) (e : ↥H ≃ₜ* Gal(κ'/κ))
    (M : FiniteGaloisIntermediateField K K') :
    IsOpen ((tsub H (↑e) M : Subgroup Gal(κ'/κ)) : Set Gal(κ'/κ)) := by
  rw [tsub, Subgroup.coe_map]
  exact (Homeomorph.isOpenMap e.toHomeomorph) _ (subFixOpen H M)

/-- **The closedness of the transported level subgroups**: the image of the closed level subgroup
under the homeomorphism `e`. -/
lemma tsub_isClosed (H : Subgroup Gal(K'/K)) (e : ↥H ≃ₜ* Gal(κ'/κ))
    (M : FiniteGaloisIntermediateField K K') :
    IsClosed ((tsub H (↑e) M : Subgroup Gal(κ'/κ)) : Set Gal(κ'/κ)) := by
  rw [tsub, Subgroup.coe_map]
  exact (Homeomorph.isClosedMap e.toHomeomorph) _ (subFixClosed H M)

/-- **The openness of the preimages of the level subgroups of `κ'/κ`** comes from the continuity of
`e`. -/
lemma tsub_pre (H : Subgroup Gal(K'/K)) (e : ↥H ≃ₜ* Gal(κ'/κ))
    (L : FiniteGaloisIntermediateField κ κ') :
    IsOpen ((L.fixingSubgroup.comap (e : ↥H →* Gal(κ'/κ)) : Subgroup ↥H) : Set ↥H) := by
  rw [Subgroup.coe_comap]
  exact (IntermediateField.fixingSubgroup_isOpen L.toIntermediateField).preimage
    e.toHomeomorph.continuous

end HT

/-! ## §6. The requested lemma -/

/-- **The cardinality transport of profinite `H²(·, Z/p)` along a topological group
isomorphism.**  If `H ≤ Gal(K'/K)` is a closed subgroup and `e : ↥H ≃ₜ* Gal(κ'/κ)` is a topological
group isomorphism, then the profinite cohomology `H²(H, Z/p)` (the filtered colimit of the
`H²`'s of the finite quotients) has the same cardinality as `H²(Gal(κ'/κ), Z/p)`: the level
systems of the two colimits are matched by the infinite Galois correspondence along `e`, and the
resulting map of colimits is a bijection. -/
theorem h2CardTransport : NK.NUV2.LC.H2CardTransport := by
  intro p K K' κ κ' _ _ _ _ _ _ _ _ H _ e
  let D : HT.Tr K K' κ κ' :=
    { H := H
      e := (e : ↥H ≃* Gal(κ'/κ))
      hopen := fun M => HT.tsub_isOpen H e M
      hclosed := fun M => HT.tsub_isClosed H e M
      hpre := fun L => HT.tsub_pre H e L }
  have hbij : Function.Bijective (HT.Phi p D) :=
    ⟨HT.Phi_injective p D, HT.Phi_surjective p D⟩
  exact Nat.card_congr (Equiv.ofBijective (HT.Phi p D) hbij)

end NK.NUV2.LC
