import Mathlib
import Submission.NK.NUV2.Transfer.verDefs
import Submission.NK.NUV2.Transfer.transfer_natural

namespace NK.NUV2.Transfer

open NK.Reconstruct

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

/-! ## Part 1: generic lemmas -/

section Generic

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

/-- **The transfer commutes with restriction**, in the form needed when the target subgroup is
given by an equation rather than as `H₂.map φ`. -/
theorem transfer_natural_congr [Fintype G₁] (φ : G₂ →* G₁) (hφ : Function.Surjective φ)
    (H₂ : Subgroup G₂) [H₂.Normal] [H₂.FiniteIndex] (H₁ : Subgroup G₁)
    (hH : H₂.map φ = H₁) (hker : φ.ker ≤ H₂) :
    ∀ (Φ : ↥H₂ →* ↥H₁), (∀ z : ↥H₂, ((Φ z : ↥H₁) : G₁) = φ z) →
      ∀ x : Abelianization G₂,
      Abelianization.map Φ (Abelianization.lift (MonoidHom.transfer (H := H₂)
        (Abelianization.of : ↥H₂ →* Abelianization ↥H₂)) x)
      = Abelianization.lift (MonoidHom.transfer (H := H₁)
        (Abelianization.of : ↥H₁ →* Abelianization ↥H₁)) (Abelianization.map φ x) := by
  let Φ₀ : ↥H₂ →* ↥(H₂.map φ) :=
    (φ.comp H₂.subtype).codRestrict (H₂.map φ) (fun h => ⟨h, h.2, rfl⟩)
  subst H₁
  intro Φ hΦ x
  have hΦeq : Φ = Φ₀ := by
    ext z
    rw [hΦ z]
    rfl
  rw [hΦeq]
  exact transfer_natural φ hφ H₂ hker x

end Generic


/-- The abelianisation of a composite is the composite of the abelianisations, on elements. -/
theorem Ab_map_comp_apply {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (f : G₂ →* G₃) (g : G₁ →* G₂) (x : Abelianization G₁) :
    Abelianization.map (f.comp g) x = Abelianization.map f (Abelianization.map g x) := by
  induction x using QuotientGroup.induction_on' with
  | _ h => rfl

section LevelRestrict

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K']

/-- **The restriction map `Gal(M/K) → Gal(L/K)` is surjective** for intermediate normal levels
`L ⊆ M`. -/
theorem levelRestrictHom_surjective (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    Function.Surjective (levelRestrictHom L M h) := by
  haveI := normal_levelTo L M h
  have key : levelRestrictHom L M h =
      (algEquivConjHom (levelToEquiv L M h)).comp
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) (levelTo L M h)) := rfl
  intro σ
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
    (K₁ := ↥(levelTo L M h)) (↥M.L) (algEquivConjHom (levelToEquiv L M h).symm σ)
  refine ⟨τ, ?_⟩
  rw [key, MonoidHom.comp_apply, hτ]
  ext x
  simp [algEquivConjHom, MulEquiv.trans_apply]

end LevelRestrict

/-! ## Part 2: the level-wise transfer -/

section Specific

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
  (M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
  [NumberField ↥M.L] [NumberField ↥L.L] [FiniteDimensional ℚ ↥M.L] [FiniteDimensional ℚ ↥L.L]
  [Normal ℚ ↥L.L] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω] (hML : M.L ≤ L.L)
  [Algebra ↥M.L ↥L.L] [IsScalarTower ↥M.L ↥L.L Ω]

/-- `L.L`, viewed as an element of the auxiliary level `auxA M L hML B`. -/
def lvIn (B : FrobLevel ↥L.L Ω) (x : ↥(LV M L hML)) : ↥(auxA M L hML B).L :=
  ⟨(x : Ω), LV_le_auxA M L hML B x.2⟩

/-- **The subgroup `HA` is exactly the group of `↥M.L`-automorphisms of the auxiliary level
which fix `L.L` pointwise.** -/
theorem mem_HA_iff (B : FrobLevel ↥L.L Ω) (σ : Gal(↥(auxA M L hML B).L/↥M.L)) :
    σ ∈ HA M L hML B ↔
      ∀ x : ↥(LV M L hML), σ (lvIn M L hML B x) = lvIn M L hML B x := by
  constructor
  · intro h x
    exact mem_HA_fixes M L hML B ⟨σ, h⟩ ((LAEquiv M L hML B).symm x)
  · intro h
    refine MonoidHom.mem_ker.mpr ?_
    have h1 : restrLA M L hML B σ = 1 := by
      ext y
      apply congrArg (fun t : ↥(auxA M L hML B).L => (t : Ω))
      change σ (y : ↥(auxA M L hML B).L) = (y : ↥(auxA M L hML B).L)
      have hxy : (y : ↥(auxA M L hML B).L) = lvIn M L hML B (LAEquiv M L hML B y) :=
        Subtype.ext rfl
      rw [hxy]
      exact h (LAEquiv M L hML B y)
    show resQ M L hML B σ = 1
    simp only [resQ, MonoidHom.comp_apply, h1, map_one]

/-- The kernel of the restriction `Gal(A_B/M.L) → Gal(A_B'/M.L)` fixes `L.L`, i.e. lies in `HA B'`. -/
theorem ker_levelRestrictHom_le_HA {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    (levelRestrictHom (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h)).ker
      ≤ HA M L hML B' := by
  intro σ hσ
  rw [mem_HA_iff]
  intro x
  have hσ1 : levelRestrictHom (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) σ = 1 :=
    MonoidHom.mem_ker.mp hσ
  have h1 : (levelRestrictHom (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) σ)
      (lvIn M L hML B x) = lvIn M L hML B x := by rw [hσ1]; rfl
  have h2 := congrArg (Subtype.val) h1
  rw [levelRestrictHom_apply_coe] at h2
  apply Subtype.ext
  exact h2

/-- **The image of `HA B'` under the restriction is `HA B`.** -/
theorem map_HA_eq {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    (HA M L hML B').map
        (levelRestrictHom (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h))
      = HA M L hML B := by
  ext σ
  constructor
  · intro hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
    rw [mem_HA_iff] at hτ ⊢
    intro x
    apply Subtype.ext
    rw [levelRestrictHom_apply_coe]
    exact congrArg (Subtype.val) (hτ x)
  · intro hσ
    obtain ⟨τ, hτ⟩ :=
      levelRestrictHom_surjective (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) σ
    refine Subgroup.mem_map.mpr ⟨τ, ?_, hτ⟩
    rw [mem_HA_iff]
    intro x
    have h1 : (levelRestrictHom (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) τ)
        (lvIn M L hML B x) = lvIn M L hML B x := by
      rw [hτ]
      exact (mem_HA_iff M L hML B σ).mp hσ x
    have h2 := congrArg (Subtype.val) h1
    rw [levelRestrictHom_apply_coe] at h2
    apply Subtype.ext
    exact h2

/-- The auxiliary level over `↥L.L` is monotone in the level over `↥M.L`. -/
theorem auxAL_mono {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    (auxAL M L hML B).L ≤ (auxAL M L hML B').L :=
  auxA_mono M L hML h

/-- The restriction of automorphisms of the auxiliary levels, in the `↥M.L`-world. -/
noncomputable def rhoA {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    Gal(↥(auxA M L hML B').L/↥M.L) →* Gal(↥(auxA M L hML B).L/↥M.L) :=
  levelRestrictHom (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h)

/-- The restriction of automorphisms of the auxiliary levels, in the `↥L.L`-world. -/
noncomputable def rhoL {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    Gal(↥(auxAL M L hML B').L/↥L.L) →* Gal(↥(auxAL M L hML B).L/↥L.L) :=
  levelRestrictHom (auxAL M L hML B) (auxAL M L hML B') (auxAL_mono M L hML h)

/-- `convH` read at an element of the auxiliary level viewed over `↥L.L`. -/
theorem convH_applyAL (B : FrobLevel ↥L.L Ω) (σ : ↥(HA M L hML B))
    (x : ↥(auxAL M L hML B).L) : convH M L hML B σ x = σ.1 x := rfl

/-- The value of `rhoA`. -/
theorem rhoA_apply_coe {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L)
    (σ : Gal(↥(auxA M L hML B').L/↥M.L)) (y : ↥(auxAL M L hML B).L) :
    (((rhoA M L hML h σ) y : Ω)) = ((σ ⟨(y : Ω), auxA_mono M L hML h y.2⟩ : Ω)) :=
  levelRestrictHom_apply_coe (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) σ y

/-- The value of `rhoL`. -/
theorem rhoL_apply_coe {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L)
    (σ : Gal(↥(auxAL M L hML B').L/↥L.L)) (y : ↥(auxAL M L hML B).L) :
    (((rhoL M L hML h σ) y : Ω)) = ((σ ⟨(y : Ω), auxAL_mono M L hML h y.2⟩ : Ω)) :=
  levelRestrictHom_apply_coe (auxAL M L hML B) (auxAL M L hML B') (auxAL_mono M L hML h) σ y

/-- The value of `restrB`. -/
theorem restrB_apply_coe (B : FrobLevel ↥L.L Ω) (σ : Gal(↥(auxAL M L hML B).L/↥L.L))
    (y : ↥B.L) :
    (((restrB M L hML B σ) y : Ω)) = ((σ ⟨(y : Ω), le_auxAL M L hML B y.2⟩ : Ω)) :=
  levelRestrictHom_apply_coe B (auxAL M L hML B) (le_auxAL M L hML B) σ y

/-- Restriction commutes with the identifications of the auxiliary levels. -/
theorem restrB_comp_levelRestrictHom {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    (restrB M L hML B).comp (rhoL M L hML h)
      = (levelRestrictHom B B' h).comp (restrB M L hML B') := by
  ext σ y
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  rw [restrB_apply_coe, rhoL_apply_coe]
  rw [levelRestrictHom_apply_coe, restrB_apply_coe]

/-- **The identifications `convH` are compatible with restriction.** -/
theorem convH_natural {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    ∀ (Φ : ↥(HA M L hML B') →* ↥(HA M L hML B)),
      (∀ z : ↥(HA M L hML B'),
        ((Φ z : ↥(HA M L hML B)) : Gal(↥(auxA M L hML B).L/↥M.L))
          = rhoA M L hML h z) →
      (convH M L hML B).comp Φ
        = (rhoL M L hML h).comp (convH M L hML B') := by
  intro Φ hΦ
  ext z x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, convH_applyAL, hΦ z, rhoA_apply_coe,
    rhoL_apply_coe, convH_applyAL]
  rfl

/-- The kernel of `rhoA` lies in `HA B'`. -/
theorem ker_rhoA_le_HA {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    (rhoA M L hML h).ker ≤ HA M L hML B' :=
  ker_levelRestrictHom_le_HA M L hML h

/-- `rhoA` is surjective. -/
theorem rhoA_surjective {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    Function.Surjective (rhoA M L hML h) :=
  levelRestrictHom_surjective (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h)

/-- The image of `HA B'` under `rhoA` is `HA B`. -/
theorem map_HA_eq_rhoA {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    (HA M L hML B').map (rhoA M L hML h) = HA M L hML B :=
  map_HA_eq M L hML h

/-- The raw level transfer `Γ_{A_B,2} → Γ_{B,2}`, before the ℓ-primary projection. -/
noncomputable def W (B : FrobLevel ↥L.L Ω) :
    LevelAbelianization (auxA M L hML B).L →* LevelAbelianization B.L :=
  (Abelianization.map (restrB M L hML B)).comp
    ((Abelianization.map (convH M L hML B)).comp (transferAb M L hML B))

/-- The defining formula of the level transfer. -/
theorem transferEll_apply (B : FrobLevel ↥L.L Ω) (x : LevelEllPart (auxA M L hML B).L 2) :
    transferEll M L hML B x
      = ellComp 2 (W M L hML B (x : LevelAbelianization (auxA M L hML B).L)) := rfl

/-- **Naturality of the raw level transfer `W` in the level.** -/
theorem W_natural {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L)
    (y : LevelAbelianization (auxA M L hML B').L) :
    levelRestrict B B' h (W M L hML B' y)
      = W M L hML B
          (levelRestrict (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) y) := by
  let Ψ : ↥(HA M L hML B') →* ↥((HA M L hML B').map (rhoA M L hML h)) :=
    ((rhoA M L hML h).comp (HA M L hML B').subtype).codRestrict
      ((HA M L hML B').map (rhoA M L hML h)) (fun z => ⟨z, z.2, rfl⟩)
  let e : ↥((HA M L hML B').map (rhoA M L hML h)) ≃* ↥(HA M L hML B) :=
    MulEquiv.subgroupCongr (map_HA_eq M L hML h)
  let Φ : ↥(HA M L hML B') →* ↥(HA M L hML B) := e.toMonoidHom.comp Ψ
  have hΦ : ∀ z : ↥(HA M L hML B'),
      ((Φ z : ↥(HA M L hML B)) : Gal(↥(auxA M L hML B).L/↥M.L)) = rhoA M L hML h z := by
    intro z
    show ((e (Ψ z) : ↥(HA M L hML B)) : Gal(↥(auxA M L hML B).L/↥M.L)) = rhoA M L hML h z
    simp only [e, MulEquiv.subgroupCongr_apply]
    rfl
  have ht : Abelianization.map Φ (transferAb M L hML B' y)
      = transferAb M L hML B (Abelianization.map (rhoA M L hML h) y) :=
    transfer_natural_congr (rhoA M L hML h) (rhoA_surjective M L hML h)
      (HA M L hML B') (HA M L hML B) (map_HA_eq M L hML h) (ker_rhoA_le_HA M L hML h) Φ hΦ y
  have hc := convH_natural M L hML h Φ hΦ
  have hstep : levelRestrict B B' h
        (Abelianization.map (restrB M L hML B')
          (Abelianization.map (convH M L hML B') (transferAb M L hML B' y)))
      = Abelianization.map (restrB M L hML B)
          (Abelianization.map (rhoL M L hML h)
            (Abelianization.map (convH M L hML B') (transferAb M L hML B' y))) := by
    rw [show levelRestrict B B' h = Abelianization.map (levelRestrictHom B B' h) from rfl]
    conv_lhs => rw [← Ab_map_comp_apply]
    rw [← restrB_comp_levelRestrictHom]
    conv_lhs => rw [Ab_map_comp_apply]
  have key : Abelianization.map (convH M L hML B)
        (transferAb M L hML B
          (levelRestrict (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) y))
      = Abelianization.map (rhoL M L hML h)
          (Abelianization.map (convH M L hML B') (transferAb M L hML B' y)) := by
    rw [show levelRestrict (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h)
        = Abelianization.map (rhoA M L hML h) from rfl]
    conv_lhs => rw [← ht]
    conv_lhs => rw [← Ab_map_comp_apply]
    conv_lhs => rw [hc]
    conv_lhs => rw [Ab_map_comp_apply]
  simp only [W, MonoidHom.comp_apply]
  rw [hstep, key]


/-- **Naturality of the level-wise transfer `transferEll`**: the transfer at the level `B'` followed
by the restriction to `B` is the transfer at `B` of the restriction of the argument from the
auxiliary level `auxA M L hML B'` to `auxA M L hML B`.

This is the compatibility of the level-wise transfer with the projective system
(`ellRestrict`) of Shimizu's §4, and is the input needed to make the level-wise transfers into a
map of `Γ_L` (the "norm–transfer identity" of `NK.NUV2.Transfer.transferNormIdentity`).

The proof reduces (via `ellRestrict_ellComp`, the compatibility of the ℓ-primary projection with the
transition maps) to the naturality of the raw transfer `W` (a map on the full abelianisations), which
is assembled from the functoriality of the transfer (`transfer_natural_congr`, itself a repackaging
of `NK.NUV2.Transfer.transfer_natural`), the compatibility of the restriction maps
(`restrB_comp_levelRestrictHom`) and the compatibility of the "same field, different base"
identifications (`convH_natural`). -/
theorem transferEll_natural {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (M : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
    [NumberField ↥M.L] [NumberField ↥L.L] [FiniteDimensional ℚ ↥M.L] [FiniteDimensional ℚ ↥L.L]
    [Normal ℚ ↥L.L] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω] (hML : M.L ≤ L.L)
    [Algebra ↥M.L ↥L.L] [IsScalarTower ↥M.L ↥L.L Ω]
    (B B' : NK.Reconstruct.FrobLevel ↥L.L Ω) (h : B.L ≤ B'.L)
    (y : NK.Reconstruct.LevelEllPart (NK.NUV2.Transfer.auxA M L hML B').L 2) :
    NK.Reconstruct.ellRestrict 2 B B' h (NK.NUV2.Transfer.transferEll M L hML B' y)
      = NK.NUV2.Transfer.transferEll M L hML B
          (NK.Reconstruct.ellRestrict 2 (NK.NUV2.Transfer.auxA M L hML B)
            (NK.NUV2.Transfer.auxA M L hML B') (NK.NUV2.Transfer.auxA_mono M L hML h) y) := by
  have hz : ((ellRestrict 2 (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) y :
      LevelEllPart (auxA M L hML B).L 2) : LevelAbelianization (auxA M L hML B).L)
      = levelRestrict (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h)
          (y : LevelAbelianization (auxA M L hML B').L) :=
    ellRestrict_coe 2 (auxA M L hML B) (auxA M L hML B') (auxA_mono M L hML h) y
  rw [transferEll_apply, transferEll_apply, hz, ellRestrict_ellComp,
    W_natural M L hML h (y : LevelAbelianization (auxA M L hML B').L)]


end Specific

end

end NK.NUV2.Transfer
