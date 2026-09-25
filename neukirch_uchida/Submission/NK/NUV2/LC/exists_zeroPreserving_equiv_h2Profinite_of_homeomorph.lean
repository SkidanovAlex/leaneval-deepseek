import Mathlib
import Submission.NK.NUV2.LC.h2CardTransport
import Submission.NK.BrauerHasse.Profinite

/-!
# Transport of `H²(·, Z/p)` along a topological isomorphism of closed subgroups

If `H ≤ Gal(K'/K)` and `J ≤ Gal(κ'/κ)` are closed subgroups (with `K'/K`, `κ'/κ` separable
closures) and `e : ↥H ≃ₜ* ↥J` is a topological group isomorphism, then the profinite
cohomologies `H2Profinite p H` and `H2Profinite p J` are in bijection by a map sending `0` to `0`.

Both are filtered colimits of `H²(·, Z/p)` over the open normal subgroups of the respective
profinite group: the level subgroup of a finite Galois level `L` is `N_L = H ∩ Gal(K'/L)`, and
these run cofinally through the open normal subgroups of `↥H`.  A topological isomorphism matches
the two filtered systems (`N ↦ e(N)`) and the corresponding finite quotients
(`QuotientGroup.congr`), hence the two colimits.

## Contents

* `HTX.lsub`, `HTX.jsub`, `HTX.lsubJ` — the level subgroups and their images;
* `HTX.sigma`, `HTX.tau` — the level dictionaries, with the cofinality lemmas
  `exists_jsub_le_lsubJ` / `exists_lsub_le_comap`;
* `HTX.fwd`, `HTX.Phi`, `HTX.bwd`, `HTX.Psi` — the transport maps of the colimits;
* `HTX.Phi_psi`, `HTX.Psi_Phi` — the two round trips;
* `exists_zeroPreserving_equiv_h2Profinite_of_homeomorph` — the requested lemma.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NK.BrauerHasse

namespace NK.NUV2.LC

namespace HTX

universe u

variable {K K' κ κ' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
  [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
  (H : Subgroup Gal(K'/K)) (J : Subgroup Gal(κ'/κ))

/-! ## §1. The level subgroups -/

/-- The level subgroup `H ∩ Gal(K'/L)` of `↥H`. -/
noncomputable abbrev lsub (L : FiniteGaloisIntermediateField K K') : Subgroup ↥H :=
  L.fixingSubgroup.subgroupOf H

/-- The level subgroup `J ∩ Gal(κ'/M)` of `↥J`. -/
noncomputable abbrev jsub (M : FiniteGaloisIntermediateField κ κ') : Subgroup ↥J :=
  M.fixingSubgroup.subgroupOf J

/-- The image of the level subgroup `lsub H L` under an isomorphism `e`. -/
noncomputable def lsubJ (e : ↥H ≃* ↥J) (L : FiniteGaloisIntermediateField K K') : Subgroup ↥J :=
  (lsub H L).map (e : ↥H →* ↥J)

instance instNormalLsubJ (e : ↥H ≃* ↥J) (L : FiniteGaloisIntermediateField K K') :
    (lsubJ H J e L).Normal :=
  Subgroup.Normal.map (Subgroup.normal_subgroupOf (N := L.fixingSubgroup) (H := H))
    (e : ↥H →* ↥J) e.surjective

lemma isOpen_lsub (L : FiniteGaloisIntermediateField K K') :
    IsOpen ((lsub H L : Subgroup ↥H) : Set ↥H) := by
  rw [lsub, Subgroup.coe_subgroupOf]
  exact (IntermediateField.fixingSubgroup_isOpen L.toIntermediateField).preimage
    continuous_subtype_val

lemma isOpen_jsub (M : FiniteGaloisIntermediateField κ κ') :
    IsOpen ((jsub J M : Subgroup ↥J) : Set ↥J) := by
  rw [jsub, Subgroup.coe_subgroupOf]
  exact (IntermediateField.fixingSubgroup_isOpen M.toIntermediateField).preimage
    continuous_subtype_val

lemma isOpen_lsubJ (e : ↥H ≃ₜ* ↥J) (L : FiniteGaloisIntermediateField K K') :
    IsOpen ((lsubJ H J (e : ↥H ≃* ↥J) L : Subgroup ↥J) : Set ↥J) := by
  rw [lsubJ, Subgroup.coe_map]
  exact (Homeomorph.isOpenMap e.toHomeomorph) _ (isOpen_lsub H L)

lemma isOpen_comap_jsub (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ') :
    IsOpen (((jsub J M).comap (e : ↥H →* ↥J) : Subgroup ↥H) : Set ↥H) := by
  rw [Subgroup.coe_comap]
  exact (isOpen_jsub J M).preimage e.toHomeomorph.continuous

/-! ## §2. The level dictionaries -/

lemma exists_jsub_le_lsubJ (e : ↥H ≃ₜ* ↥J) (L : FiniteGaloisIntermediateField K K') :
    ∃ M : FiniteGaloisIntermediateField κ κ',
      jsub J M ≤ lsubJ H J (e : ↥H ≃* ↥J) L :=
  NK.LocalCFT.Brauer.exists_fixingSubgroup_subgroupOf_le_of_isOpen (H := J)
    (isOpen_lsubJ H J e L)

/-- The `J`-level attached to an `H`-level: a finite Galois level of `κ'/κ` whose level subgroup
is contained in the image of `lsub H L`. -/
noncomputable def sigma (e : ↥H ≃ₜ* ↥J) (L : FiniteGaloisIntermediateField K K') :
    FiniteGaloisIntermediateField κ κ' :=
  Classical.choose (exists_jsub_le_lsubJ H J e L)

lemma jsub_sigma_le (e : ↥H ≃ₜ* ↥J) (L : FiniteGaloisIntermediateField K K') :
    jsub J (sigma H J e L) ≤ lsubJ H J (e : ↥H ≃* ↥J) L :=
  Classical.choose_spec (exists_jsub_le_lsubJ H J e L)

lemma exists_lsub_le_comap (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ') :
    ∃ L : FiniteGaloisIntermediateField K K',
      lsub H L ≤ (jsub J M).comap (e : ↥H →* ↥J) :=
  NK.LocalCFT.Brauer.exists_fixingSubgroup_subgroupOf_le_of_isOpen (H := H)
    (isOpen_comap_jsub H J e M)

/-- The `H`-level attached to a `J`-level: a finite Galois level of `K'/K` whose level subgroup
maps into `jsub J M`. -/
noncomputable def tau (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ') :
    FiniteGaloisIntermediateField K K' :=
  Classical.choose (exists_lsub_le_comap H J e M)

lemma lsub_tau_le_comap (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ') :
    lsub H (tau H J e M) ≤ (jsub J M).comap (e : ↥H →* ↥J) :=
  Classical.choose_spec (exists_lsub_le_comap H J e M)

lemma lsubJ_tau_le (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ') :
    lsubJ H J (e : ↥H ≃* ↥J) (tau H J e M) ≤ jsub J M :=
  Subgroup.map_le_iff_le_comap.mpr (lsub_tau_le_comap H J e M)

/-! ## §3. The level-group morphisms -/

/-- The quotient projection `↥J ⧸ N →* ↥J ⧸ N'` for `N ≤ N'`. -/
noncomputable def proj {N N' : Subgroup ↥J} [N.Normal] [N'.Normal] (h : N ≤ N') :
    ↥J ⧸ N →* ↥J ⧸ N' :=
  QuotientGroup.map N N' (MonoidHom.id ↥J) (by simpa using h)

@[simp]
lemma proj_mk' {N N' : Subgroup ↥J} [N.Normal] [N'.Normal] (h : N ≤ N') (x : ↥J) :
    proj (J := J) h (QuotientGroup.mk' N x) = QuotientGroup.mk' N' x := by
  rw [proj, QuotientGroup.map_mk']
  rfl

/-- The isomorphism `LevelGroup H L ≃* ↥J ⧸ e(lsub H L)` induced by `e`. -/
noncomputable def iso (e : ↥H ≃* ↥J) (L : FiniteGaloisIntermediateField K K') :
    LevelGroup H L ≃* ↥J ⧸ lsubJ H J e L :=
  QuotientGroup.congr (lsub H L) (lsubJ H J e L) e (by rfl)

@[simp]
lemma iso_mk' (e : ↥H ≃* ↥J) (L : FiniteGaloisIntermediateField K K') (x : ↥H) :
    iso H J e L (QuotientGroup.mk' (lsub H L) x) = QuotientGroup.mk' (lsubJ H J e L) (e x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

@[simp]
lemma iso_symm_mk' (e : ↥H ≃* ↥J) (L : FiniteGaloisIntermediateField K K') (y : ↥J) :
    (iso H J e L).symm (QuotientGroup.mk' (lsubJ H J e L) y)
      = QuotientGroup.mk' (lsub H L) (e.symm y) := by
  have h : QuotientGroup.mk' (lsubJ H J e L) y
      = iso H J e L (QuotientGroup.mk' (lsub H L) (e.symm y)) := by
    rw [iso_mk']
    simp
  rw [h, MulEquiv.symm_apply_apply]

/-- The level morphism `↥J ⧸ jsub (σ L) →* ↥H ⧸ lsub L` transported by `e`. -/
noncomputable def alphaL (e : ↥H ≃ₜ* ↥J) (L : FiniteGaloisIntermediateField K K') :
    ↥J ⧸ jsub J (sigma H J e L) →* ↥H ⧸ lsub H L :=
  ((iso H J (e : ↥H ≃* ↥J) L).symm.toMonoidHom).comp
    (proj (J := J) (jsub_sigma_le H J e L))

@[simp]
lemma alphaL_mk' (e : ↥H ≃ₜ* ↥J) (L : FiniteGaloisIntermediateField K K') (y : ↥J) :
    alphaL H J e L (QuotientGroup.mk' (jsub J (sigma H J e L)) y)
      = QuotientGroup.mk' (lsub H L) ((e : ↥H ≃* ↥J).symm y) := by
  rw [alphaL, MonoidHom.comp_apply, proj_mk']
  exact iso_symm_mk' H J (e : ↥H ≃* ↥J) L y

/-- The level morphism `↥H ⧸ lsub (τ M) →* ↥J ⧸ jsub M` transported by `e`. -/
noncomputable def betaM (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ') :
    ↥H ⧸ lsub H (tau H J e M) →* ↥J ⧸ jsub J M :=
  (proj (J := J) (lsubJ_tau_le H J e M)).comp
    (iso H J (e : ↥H ≃* ↥J) (tau H J e M)).toMonoidHom

@[simp]
lemma betaM_mk' (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ') (x : ↥H) :
    betaM H J e M (QuotientGroup.mk' (lsub H (tau H J e M)) x)
      = QuotientGroup.mk' (jsub J M) ((e : ↥H ≃* ↥J) x) := by
  rw [betaM, MonoidHom.comp_apply]
  rw [show (iso H J (e : ↥H ≃* ↥J) (tau H J e M)).toMonoidHom
        (QuotientGroup.mk' (lsub H (tau H J e M)) x)
      = QuotientGroup.mk' (lsubJ H J (e : ↥H ≃* ↥J) (tau H J e M))
          ((e : ↥H ≃* ↥J) x) from
      iso_mk' H J (e : ↥H ≃* ↥J) (tau H J e M) x]
  rw [proj_mk']

/-! ## §4. The transport maps of the colimits -/

/-- The forward level transport: a class of the level `L` of `H` is sent to the level `σ L` of
`J`. -/
noncomputable def fwd (p : ℕ) (e : ↥H ≃ₜ* ↥J) (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p H L) : H2Profinite p J :=
  H2Profinite.ofLevel (U := J) (sigma H J e L) ((H2.map (alphaL H J e L)).hom a)

/-- The backward level transport: a class of the level `M` of `J` is sent to the level `τ M` of
`H`. -/
noncomputable def bwd (p : ℕ) (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ')
    (b : LevelH2 p J M) : H2Profinite p H :=
  H2Profinite.ofLevel (U := H) (tau H J e M) ((H2.map (betaM H J e M)).hom b)


/-! ## §5. Compatibility of the level transports with inflation -/

lemma levelQuotHom_mk' {U : Subgroup Gal(K'/K)} {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') (x : ↥U) :
    levelQuotHom (U := U) h (QuotientGroup.mk' (L'.fixingSubgroup.subgroupOf U) x)
      = QuotientGroup.mk' (L.fixingSubgroup.subgroupOf U) x := by
  rw [levelQuotHom, QuotientGroup.map_mk']
  rfl

/-- Compatibility of the forward level transport with inflation. -/
lemma fwd_compat (p : ℕ) (e : ↥H ≃ₜ* ↥J) :
    ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p H L),
      fwd H J p e L' ((levelMap p (U := H) h) a) = fwd H J p e L a := by
  intro L L' h a
  set P : FiniteGaloisIntermediateField κ κ' :=
    sigma H J e L ⊔ sigma H J e L' with hP
  have h1 : sigma H J e L ≤ P := le_sup_left
  have h2 : sigma H J e L' ≤ P := le_sup_right
  have hgrp : ((levelQuotHom (U := H) h).comp (alphaL H J e L')).comp
        (levelQuotHom (U := J) h2)
      = (alphaL H J e L).comp (levelQuotHom (U := J) h1) := by
    refine QuotientGroup.monoidHom_ext (jsub J P) ?_
    ext y
    simp only [MonoidHom.comp_apply, levelQuotHom_mk', alphaL_mk',
      MulEquiv.symm_apply_apply]
  rw [fwd, fwd]
  refine (NK.BrauerHasse.ofLevel_eq_iff (p := p) (U := J) _ _).mpr ⟨P, h2, h1, ?_⟩
  simp only [levelMap]
  rw [← NK.LocalCFT.Brauer.H2.map_comp_apply (f := levelQuotHom (U := H) h)
        (g := alphaL H J e L') a,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply
        (f := (levelQuotHom (U := H) h).comp (alphaL H J e L'))
        (g := levelQuotHom (U := J) h2) a,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply (f := alphaL H J e L)
        (g := levelQuotHom (U := J) h1) a]
  rw [hgrp]

/-- Compatibility of the backward level transport with inflation. -/
lemma bwd_compat (p : ℕ) (e : ↥H ≃ₜ* ↥J) :
    ∀ (M M' : FiniteGaloisIntermediateField κ κ') (h : M ≤ M') (b : LevelH2 p J M),
      bwd H J p e M' ((levelMap p (U := J) h) b) = bwd H J p e M b := by
  intro M M' h b
  set P : FiniteGaloisIntermediateField K K' := tau H J e M ⊔ tau H J e M' with hP
  have h1 : tau H J e M ≤ P := le_sup_left
  have h2 : tau H J e M' ≤ P := le_sup_right
  have hgrp : ((levelQuotHom (U := J) h).comp (betaM H J e M')).comp
        (levelQuotHom (U := H) h2)
      = (betaM H J e M).comp (levelQuotHom (U := H) h1) := by
    refine QuotientGroup.monoidHom_ext (lsub H P) ?_
    ext y
    simp only [MonoidHom.comp_apply, levelQuotHom_mk', betaM_mk',
      MulEquiv.apply_symm_apply]
  rw [bwd, bwd]
  refine (NK.BrauerHasse.ofLevel_eq_iff (p := p) (U := H) _ _).mpr ⟨P, h2, h1, ?_⟩
  simp only [levelMap]
  rw [← NK.LocalCFT.Brauer.H2.map_comp_apply (f := levelQuotHom (U := J) h)
        (g := betaM H J e M') b,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply
        (f := (levelQuotHom (U := J) h).comp (betaM H J e M'))
        (g := levelQuotHom (U := H) h2) b,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply (f := betaM H J e M)
        (g := levelQuotHom (U := H) h1) b]
  rw [hgrp]

/-! ## §6. The transport maps of the colimits and the round trips -/

/-- The transport map `H²(H, Z/p) → H²(J, Z/p)`. -/
noncomputable def Phi (p : ℕ) (e : ↥H ≃ₜ* ↥J) : H2Profinite p H → H2Profinite p J :=
  H2Profinite.lift (fwd H J p e) (fwd_compat H J p e)

/-- The transport map `H²(J, Z/p) → H²(H, Z/p)`. -/
noncomputable def Psi (p : ℕ) (e : ↥H ≃ₜ* ↥J) : H2Profinite p J → H2Profinite p H :=
  H2Profinite.lift (bwd H J p e) (bwd_compat H J p e)

lemma Phi_ofLevel (p : ℕ) (e : ↥H ≃ₜ* ↥J) (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p H L) :
    Phi H J p e (H2Profinite.ofLevel (U := H) L a) = fwd H J p e L a :=
  H2Profinite.lift_ofLevel _ _ L a

lemma Psi_ofLevel (p : ℕ) (e : ↥H ≃ₜ* ↥J) (M : FiniteGaloisIntermediateField κ κ')
    (b : LevelH2 p J M) :
    Psi H J p e (H2Profinite.ofLevel (U := J) M b) = bwd H J p e M b :=
  H2Profinite.lift_ofLevel _ _ M b

/-- The round trip `Ψ ∘ Φ = id`. -/
lemma Psi_Phi (p : ℕ) (e : ↥H ≃ₜ* ↥J) :
    ∀ x : H2Profinite p H, Psi H J p e (Phi H J p e x) = x := by
  intro x
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  rw [Phi_ofLevel, fwd, Psi_ofLevel, bwd]
  set P : FiniteGaloisIntermediateField K K' := L ⊔ tau H J e (sigma H J e L) with hP
  have h1 : tau H J e (sigma H J e L) ≤ P := le_sup_right
  have h2 : L ≤ P := le_sup_left
  have hgrp : ((alphaL H J e L).comp (betaM H J e (sigma H J e L))).comp
        (levelQuotHom (U := H) h1)
      = levelQuotHom (U := H) h2 := by
    refine QuotientGroup.monoidHom_ext (lsub H P) ?_
    ext y
    simp only [MonoidHom.comp_apply, levelQuotHom_mk', alphaL_mk', betaM_mk',
      MulEquiv.symm_apply_apply]
  refine (NK.BrauerHasse.ofLevel_eq_iff (p := p) (U := H) _ _).mpr ⟨P, h1, h2, ?_⟩
  simp only [levelMap]
  rw [← NK.LocalCFT.Brauer.H2.map_comp_apply
        (f := alphaL H J e L) (g := betaM H J e (sigma H J e L)) a,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply
        (f := (alphaL H J e L).comp (betaM H J e (sigma H J e L)))
        (g := levelQuotHom (U := H) h1) a]
  rw [hgrp]

/-- The round trip `Φ ∘ Ψ = id`. -/
lemma Phi_Psi (p : ℕ) (e : ↥H ≃ₜ* ↥J) :
    ∀ y : H2Profinite p J, Phi H J p e (Psi H J p e y) = y := by
  intro y
  obtain ⟨M, b, rfl⟩ := H2Profinite.ofLevel_surjective y
  rw [Psi_ofLevel, bwd, Phi_ofLevel, fwd]
  set P : FiniteGaloisIntermediateField κ κ' := M ⊔ sigma H J e (tau H J e M) with hP
  have h1 : sigma H J e (tau H J e M) ≤ P := le_sup_right
  have h2 : M ≤ P := le_sup_left
  have hgrp : ((betaM H J e M).comp (alphaL H J e (tau H J e M))).comp
        (levelQuotHom (U := J) h1)
      = levelQuotHom (U := J) h2 := by
    refine QuotientGroup.monoidHom_ext (jsub J P) ?_
    ext y
    simp only [MonoidHom.comp_apply, levelQuotHom_mk', alphaL_mk', betaM_mk',
      MulEquiv.apply_symm_apply]
  refine (NK.BrauerHasse.ofLevel_eq_iff (p := p) (U := J) _ _).mpr ⟨P, h1, h2, ?_⟩
  simp only [levelMap]
  rw [← NK.LocalCFT.Brauer.H2.map_comp_apply
        (f := betaM H J e M) (g := alphaL H J e (tau H J e M)) b,
      ← NK.LocalCFT.Brauer.H2.map_comp_apply
        (f := (betaM H J e M).comp (alphaL H J e (tau H J e M)))
        (g := levelQuotHom (U := J) h1) b]
  rw [hgrp]

end HTX

/-! ## §7. The requested lemma -/

/-- **The level system of `H²(·, Z/2)` is invariant under a topological isomorphism of closed
subgroups.**

If `H ≤ Gal(K'/K)` and `J ≤ Gal(κ'/κ)` are closed subgroups (`K'/K`, `κ'/κ` separable closures of
fields of characteristic zero) and `e : ↥H ≃ₜ* ↥J` is a topological group isomorphism, then
`H2Profinite 2 H` and `H2Profinite 2 J` are in bijection by a map sending `0` to `0`.

The two profinite cohomologies are filtered colimits of `H²(·, Z/2)` over the open normal
subgroups of `↥H` resp. `↥J`; a topological isomorphism matches the two filtered systems, and the
resulting map of colimits (`HTX.Phi`, with inverse `HTX.Psi`) is a bijection. -/
theorem exists_zeroPreserving_equiv_h2Profinite_of_homeomorph
    {K K' κ κ' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (J : Subgroup Gal(κ'/κ)) (hJ : IsClosed (J : Set Gal(κ'/κ)))
    (e : ↥H ≃ₜ* ↥J) :
    ∃ f : NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 H ≃
      NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') 2 J, f 0 = 0 := by
  refine ⟨{ toFun := HTX.Phi H J 2 e
            invFun := HTX.Psi H J 2 e
            left_inv := HTX.Psi_Phi H J 2 e
            right_inv := HTX.Phi_Psi H J 2 e }, ?_⟩
  show HTX.Phi H J 2 e
    (H2Profinite.ofLevel (p := 2) (U := H) ⊥ (0 : LevelH2 2 H ⊥)) = 0
  rw [HTX.Phi_ofLevel, HTX.fwd, map_zero]
  exact NK.BrauerHasse.ofLevel_zero _

end NK.NUV2.LC
