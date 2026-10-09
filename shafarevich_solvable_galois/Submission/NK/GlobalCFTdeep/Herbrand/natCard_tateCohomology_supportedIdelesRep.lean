import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
import Submission.NK.GlobalCFTdeep.Herbrand.SupportedIdelesInsert
import Submission.NK.RepresentationTheory.GroupCohomology.piCohomology_injective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.RepresentationTheory.GroupCohomology (piRep piRepIso piRep_ρ_apply)

attribute [local reducible] NK.RepresentationTheory.GroupCohomology.piRep
attribute [local reducible] NK.GlobalCFTdeep.fiberIdelesRep
attribute [local reducible] NK.GlobalCFTdeep.supportedIdelesRep
attribute [local reducible] Rep.ofMulDistribMulAction
attribute [local reducible] Representation.ofMulDistribMulAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Projection onto the fibre of a place -/

/-- The `w`-component of the idèle obtained from `x` by keeping the components at the places of
`L` above `v` and replacing all others by `1`. -/
noncomputable def fiberProjVal (x : Idele L) (v : Place K) (w : Place L) :
    (Place.localField L w)ˣ := by
  classical
  exact if Place.LiesOver w v then x w else 1

theorem fiberProjVal_of_liesOver {x : Idele L} {v : Place K} {w : Place L}
    (h : Place.LiesOver w v) : fiberProjVal x v w = x w := by
  classical
  rw [fiberProjVal]
  exact if_pos h

theorem fiberProjVal_of_not_liesOver {x : Idele L} {v : Place K} {w : Place L}
    (h : ¬ Place.LiesOver w v) : fiberProjVal x v w = 1 := by
  classical
  rw [fiberProjVal]
  exact if_neg h

/-- **The projection of an idèle to the idèles supported on the places above `v`.** -/
noncomputable def fiberProj (x : Idele L) (v : Place K) :
    ↥(fiberIdeles (K := K) (L := L) v) :=
  ⟨⟨fiberProjVal x v, by
      rw [Filter.eventually_cofinite]
      refine (Filter.eventually_cofinite.mp x.2).subset ?_
      intro w hw
      simp only [Set.mem_ofPred_eq] at hw ⊢
      by_cases h : Place.LiesOver w v
      · rwa [fiberProjVal_of_liesOver h] at hw
      · exact absurd (Subgroup.one_mem (Place.localUnits L w))
          (by rw [fiberProjVal_of_not_liesOver h] at hw; exact hw)⟩,
    fun _ hw => fiberProjVal_of_not_liesOver hw⟩

@[simp] theorem fiberProj_coe_apply (x : Idele L) (v : Place K) (w : Place L) :
    (((fiberProj x v : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L)) w =
      fiberProjVal x v w := rfl

theorem fiberProj_mul (x y : Idele L) (v : Place K) :
    fiberProj (x * y) v = fiberProj x v * fiberProj y v := by
  apply Subtype.ext
  apply Idele.ext
  intro w
  show fiberProjVal (x * y) v w = fiberProjVal x v w * fiberProjVal y v w
  by_cases h : Place.LiesOver w v
  · rw [fiberProjVal_of_liesOver h, fiberProjVal_of_liesOver h, fiberProjVal_of_liesOver h]
    rfl
  · rw [fiberProjVal_of_not_liesOver h, fiberProjVal_of_not_liesOver h,
      fiberProjVal_of_not_liesOver h, mul_one]

theorem fiberProj_one (v : Place K) : fiberProj (1 : Idele L) v = 1 := by
  apply Subtype.ext
  apply Idele.ext
  intro w
  show fiberProjVal (1 : Idele L) v w = 1
  by_cases h : Place.LiesOver w v
  · rw [fiberProjVal_of_liesOver h]
    rfl
  · rw [fiberProjVal_of_not_liesOver h]

theorem fiberProj_smul (σ : L ≃ₐ[K] L) (x : Idele L) (v : Place K) :
    fiberProj (σ • x) v = σ • fiberProj x v := by
  apply Subtype.ext
  apply Idele.ext
  intro w
  show fiberProjVal (σ • x) v w =
    (σ • ((fiberProj x v : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L)) w
  rw [Idele.smul_apply, fiberProj_coe_apply]
  by_cases h : Place.LiesOver w v
  · rw [fiberProjVal_of_liesOver h, Idele.smul_apply,
      fiberProjVal_of_liesOver ((Place.liesOver_smul_iff (σ := σ⁻¹)).mpr h)]
  · rw [fiberProjVal_of_not_liesOver h,
      fiberProjVal_of_not_liesOver (fun hh => h ((Place.liesOver_smul_iff (σ := σ⁻¹)).mp hh)),
      map_one]

/-- The projection of the idèles onto the family of fibres of the places of `S`, as a monoid
homomorphism. -/
noncomputable def fiberProjHom (S : Finset (Place K)) :
    Idele L →* (∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) where
  toFun x := fun v => fiberProj x (v : Place K)
  map_one' := by
    funext v
    exact fiberProj_one (v : Place K)
  map_mul' x y := by
    funext v
    exact fiberProj_mul x y (v : Place K)

theorem fiberProjHom_apply (S : Finset (Place K)) (x : Idele L) (v : S) :
    (fiberProjHom S) x v = fiberProj x (v : Place K) := rfl

theorem fiberProj_zpow (S : Finset (Place K)) (x : Idele L) (n : ℤ) (v : S) :
    fiberProj (x ^ n) (v : Place K) = (fiberProj x (v : Place K)) ^ n := by
  rw [← fiberProjHom_apply, map_zpow]
  rfl

theorem fiberProjHom_smul (S : Finset (Place K)) (σ : L ≃ₐ[K] L) (a : Idele L) :
    (fiberProjHom S) (σ • a) = σ • (fiberProjHom S) a := by
  funext v
  rw [show (σ • (fiberProjHom S) a) v = σ • (fiberProjHom S) a v from Pi.smul_apply σ _ v]
  exact fiberProj_smul σ a (v : Place K)

/-! ## Gluing a family of fibre-supported idèles -/

/-- The `w`-component of the gluing of a family of idèles supported on the fibres of the places
of `S`: the component at `w` of the member of the family indexed by the place below `w`. -/
noncomputable def glueVal {S : Finset (Place K)}
    (y : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) (w : Place L) :
    (Place.localField L w)ˣ := by
  classical
  exact if h : ∃ v ∈ S, Place.LiesOver w (v : Place K) then
    (((y ⟨h.choose, h.choose_spec.1⟩ :
        ↥(fiberIdeles (K := K) (L := L) h.choose)) : Idele L)) w
  else 1

theorem glueVal_of_liesOver {S : Finset (Place K)}
    (y : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K)))
    {w : Place L} {v : Place K} (hv : v ∈ S) (hw : Place.LiesOver w v) :
    glueVal y w = ((y ⟨v, hv⟩ : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L) w := by
  classical
  have h : ∃ u ∈ S, Place.LiesOver w (u : Place K) := ⟨v, hv, hw⟩
  rw [glueVal, dif_pos h]
  have hsub : (⟨h.choose, h.choose_spec.1⟩ : S) = ⟨v, hv⟩ :=
    Subtype.ext (Inclusion.globalCFT_liesOver_unique h.choose_spec.2 hw)
  rw [hsub]

theorem glueVal_eq_one_of_not_exists {S : Finset (Place K)}
    (y : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) {w : Place L}
    (h : ¬ ∃ v ∈ S, Place.LiesOver w (v : Place K)) : glueVal y w = 1 := by
  classical
  rw [glueVal]
  exact dif_neg h

theorem glueVal_eq_one_of_notMem {S : Finset (Place K)}
    (y : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) {T : Set (Place L)}
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) {w : Place L} (hw : w ∉ T) :
    glueVal y w = 1 :=
  glueVal_eq_one_of_not_exists y fun h => hw ((hTS w).mpr h)

theorem glueVal_one {S : Finset (Place K)} (w : Place L) :
    glueVal (1 : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) w = 1 := by
  classical
  by_cases h : ∃ v ∈ S, Place.LiesOver w (v : Place K)
  · obtain ⟨v, hv, hw⟩ := h
    rw [glueVal_of_liesOver (y := 1) hv hw]
    rfl
  · exact glueVal_eq_one_of_not_exists _ h

theorem glueVal_mul {S : Finset (Place K)}
    (y z : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) (w : Place L) :
    glueVal (y * z) w = glueVal y w * glueVal z w := by
  classical
  by_cases h : ∃ v ∈ S, Place.LiesOver w (v : Place K)
  · obtain ⟨v, hv, hw⟩ := h
    rw [glueVal_of_liesOver (y := y * z) hv hw, glueVal_of_liesOver (y := y) hv hw,
      glueVal_of_liesOver (y := z) hv hw]
    show (((y ⟨v, hv⟩ * z ⟨v, hv⟩ : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L)) w =
      ((y ⟨v, hv⟩ : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L) w *
        ((z ⟨v, hv⟩ : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L) w
    rw [Subgroup.coe_mul, Idele.mul_apply]
  · rw [glueVal_eq_one_of_not_exists (y := y * z) h, glueVal_eq_one_of_not_exists (y := y) h,
      glueVal_eq_one_of_not_exists (y := z) h, mul_one]

theorem glueVal_isIdele {S : Finset (Place K)}
    (y : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) :
    ∀ᶠ w in Filter.cofinite, glueVal y w ∈ Place.localUnits L w := by
  classical
  have h : ∀ᶠ w in Filter.cofinite, ∀ v : S,
      (((y v : ↥(fiberIdeles (K := K) (L := L) (v : Place K))) : Idele L) w ∈
        Place.localUnits L w) :=
    Filter.eventually_all.mpr (fun v => (y v : Idele L).2)
  filter_upwards [h] with w hw
  by_cases hmem : ∃ v ∈ S, Place.LiesOver w (v : Place K)
  · obtain ⟨v, hv, hwv⟩ := hmem
    rw [glueVal_of_liesOver y hv hwv]
    exact hw ⟨v, hv⟩
  · rw [glueVal_eq_one_of_not_exists y hmem]
    exact one_mem _

/-- **The gluing of a family of idèles supported on the fibres of the places of `S`**, as a monoid
homomorphism into the idèles supported on `T`. -/
noncomputable def glue (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    (∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) →*
      ↥(supportedIdeles (L := L) T) where
  toFun y := ⟨⟨fun w => glueVal y w, glueVal_isIdele y⟩,
    fun w hw => glueVal_eq_one_of_notMem y hTS hw⟩
  map_one' := by
    apply Subtype.ext
    apply Idele.ext
    intro w
    show glueVal (1 : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) w = 1
    exact glueVal_one w
  map_mul' y z := by
    apply Subtype.ext
    apply Idele.ext
    intro w
    show glueVal (y * z) w = glueVal y w * glueVal z w
    exact glueVal_mul y z w

@[simp] theorem glue_coe_apply (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (y : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) (w : Place L) :
    (((glue S T hTS) y : ↥(supportedIdeles (L := L) T)) : Idele L) w = glueVal y w := rfl

/-- The action of `Gal(L/K)` on the idèles supported on `T`, transported along the inclusion into
the idèles. -/
theorem supportedIdelesRep_ρ_coe (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (σ : L ≃ₐ[K] L)
    (x : (supportedIdelesRep (L := L) T hT).V) :
    ((Additive.toMul ((supportedIdelesRep (L := L) T hT).ρ σ x) :
        ↥(supportedIdeles (L := L) T)) : Idele L) =
      σ • ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L) := rfl

/-- The action of `Gal(L/K)` on the idèles supported on `T`, computed on a subgroup element. -/
theorem supportedIdelesRep_ρ_ofMul (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (σ : L ≃ₐ[K] L)
    (z : ↥(supportedIdeles (L := L) T)) :
    (supportedIdelesRep (L := L) T hT).ρ σ (Additive.ofMul z) =
      Additive.ofMul ⟨σ • (z : Idele L), smul_mem_supportedIdeles hT z.2⟩ := rfl

/-! ## The two maps are inverse to each other -/

theorem glue_fiberProj (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (x : ↥(supportedIdeles (L := L) T)) :
    (glue S T hTS) (fun v : S => fiberProj ((x : Idele L)) (v : Place K)) = x := by
  apply Subtype.ext
  apply Idele.ext
  intro w
  by_cases hw : w ∈ T
  · obtain ⟨v, hv, hwv⟩ := (hTS w).mp hw
    rw [glue_coe_apply, glueVal_of_liesOver _ hv hwv]
    show (((fiberProj ((x : Idele L)) v : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L)) w =
      (x : Idele L) w
    rw [fiberProj_coe_apply, fiberProjVal_of_liesOver hwv]
  · rw [glue_coe_apply, glueVal_eq_one_of_notMem _ hTS hw]
    exact (mem_supportedIdeles.mp x.2 w hw).symm

theorem fiberProj_glue (S : Finset (Place K)) (T : Set (Place L))
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (y : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) (v : S) :
    fiberProj (((glue S T hTS) y : ↥(supportedIdeles (L := L) T)) : Idele L) (v : Place K) =
      y v := by
  apply Subtype.ext
  apply Idele.ext
  intro w
  by_cases hwv : Place.LiesOver w (v : Place K)
  · show fiberProjVal (((glue S T hTS) y : ↥(supportedIdeles (L := L) T)) : Idele L)
        (v : Place K) w = _
    rw [fiberProjVal_of_liesOver hwv, glue_coe_apply, glueVal_of_liesOver _ v.2 hwv]
  · show fiberProjVal (((glue S T hTS) y : ↥(supportedIdeles (L := L) T)) : Idele L)
        (v : Place K) w = _
    rw [fiberProjVal_of_not_liesOver hwv]
    exact (mem_fiberIdeles.mp (y v).2 w hwv).symm

/-! ## Equivariance of the gluing -/

theorem glue_smul (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (σ : L ≃ₐ[K] L)
    (y : ∀ v : S, ↥(fiberIdeles (K := K) (L := L) (v : Place K))) :
    ((((glue S T hTS) (fun v : S => σ • y v) : ↥(supportedIdeles (L := L) T))) : Idele L) =
      σ • ((((glue S T hTS) y : ↥(supportedIdeles (L := L) T))) : Idele L) := by
  apply Idele.ext
  intro w
  rw [glue_coe_apply, Idele.smul_apply, glue_coe_apply]
  by_cases hw : w ∈ T
  · obtain ⟨v, hv, hwv⟩ := (hTS w).mp hw
    have hw' : Place.LiesOver (σ⁻¹ • w) v := (Place.liesOver_smul_iff (σ := σ⁻¹)).mpr hwv
    rw [glueVal_of_liesOver (y := fun v : S => σ • y v) hv hwv,
      glueVal_of_liesOver (y := y) hv hw']
    rw [show (((σ • y ⟨v, hv⟩ :
          ↥(fiberIdeles (K := K) (L := L) v)) : Idele L)) =
        σ • ((y ⟨v, hv⟩ : ↥(fiberIdeles (K := K) (L := L) v)) : Idele L) from rfl,
      Idele.smul_apply]
  · have hσw : σ⁻¹ • w ∉ T := fun hh => hw (by
      have h1 := hT σ hh
      rwa [smul_inv_smul] at h1)
    rw [glueVal_eq_one_of_notMem _ hTS hw, glueVal_eq_one_of_notMem _ hTS hσw, map_one]



/-! ## Reducible copies of the relevant representations

The three representations occurring below are definitionally equal to the originals but are
exposed as `abbrev`s, so that the underlying type `R.V` unfolds during elaboration and the
category-theoretic statements can be proved by rewriting group-level identities. -/

/-- The fibre representation `∏_{w | v} L_wˣ`. -/
abbrev hFiberRep (v : Place K) : Rep ℤ (L ≃ₐ[K] L) :=
  fiberIdelesRep (K := K) (L := L) v

/-- The representation of the idèles supported on `T`. -/
abbrev hSupportedRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) : Rep ℤ (L ≃ₐ[K] L) :=
  supportedIdelesRep (L := L) T hT

/-- The product representation `∏ᵢ Mᵢ` with the pointwise action. -/
abbrev hPiRep {ι : Type} (M : ι → Rep ℤ (L ≃ₐ[K] L)) : Rep ℤ (L ≃ₐ[K] L) :=
  piRep M

theorem hFiberRep_eq (v : Place K) :
    hFiberRep (K := K) (L := L) v = fiberIdelesRep (K := K) (L := L) v := rfl

theorem hSupportedRep_eq (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    hSupportedRep (L := L) T hT = supportedIdelesRep (L := L) T hT := rfl

theorem hPiRep_eq {ι : Type} (M : ι → Rep ℤ (L ≃ₐ[K] L)) :
    hPiRep (L := L) M = piRep M := rfl

/-- The action on the fibre, evaluated on a subgroup element. -/
theorem hFiberRep_ρ_apply (v : Place K) (γ : L ≃ₐ[K] L)
    (y : ↥(fiberIdeles (K := K) (L := L) v)) :
    (hFiberRep (K := K) (L := L) v).ρ γ (Additive.ofMul y) =
      Additive.ofMul (γ • y) := rfl

/-- The action on the fibre, in the `toMul` form. -/
theorem hFiberRep_ρ_apply' (v : Place K) (γ : L ≃ₐ[K] L) (x : (hFiberRep (K := K) (L := L) v).V) :
    (hFiberRep (K := K) (L := L) v).ρ γ x =
      Additive.ofMul (γ • (Additive.toMul x : ↥(fiberIdeles (K := K) (L := L) v))) := rfl

/-- The action on the product, evaluated on a component. -/
theorem hPiRep_ρ_apply {ι : Type} (M : ι → Rep ℤ (L ≃ₐ[K] L)) (g : L ≃ₐ[K] L)
    (x : (hPiRep (L := L) M).V) (i : ι) :
    (hPiRep (L := L) M).ρ g x i = (M i).ρ g (x i) := rfl

/-- The action on the idèles supported on `T`, evaluated on a subgroup element. -/
theorem hSupportedRep_ρ_ofMul (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (σ : L ≃ₐ[K] L)
    (z : ↥(supportedIdeles (L := L) T)) :
    (hSupportedRep (L := L) T hT).ρ σ (Additive.ofMul z) =
      Additive.ofMul ⟨σ • (z : Idele L), smul_mem_supportedIdeles hT z.2⟩ := rfl

/-- The multiplicative form of the addition on the product representation. -/
theorem hPiRep_toMul_add (S : Finset (Place K))
    (x y : (hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))).V) :
    ((fun v : S => Additive.toMul ((x + y) v)) : (v : S) → ↥(fiberIdeles (K := K) (L := L) (v : Place K)))
      = ((fun v : S => Additive.toMul (x v)) : (v : S) → ↥(fiberIdeles (K := K) (L := L) (v : Place K)))
        * ((fun v : S => Additive.toMul (y v)) : (v : S) → ↥(fiberIdeles (K := K) (L := L) (v : Place K))) := by
  funext v
  rw [show ((x + y) v) = x v + y v from Pi.add_apply x y v, toMul_add]
  rfl

/-- The multiplicative form of the integer action on the product representation. -/
theorem hPiRep_toMul_zsmul (S : Finset (Place K)) (n : ℤ)
    (x : (hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))).V) :
    ((fun v : S => Additive.toMul ((n • x) v)) :
        (v : S) → ↥(fiberIdeles (K := K) (L := L) (v : Place K)))
      = (((fun v : S => Additive.toMul (x v)) : (v : S) → ↥(fiberIdeles (K := K) (L := L) (v : Place K)))) ^ n := by
  funext v
  rw [show ((n • x) v) = n • (x v) from Pi.smul_apply n x v, toMul_zsmul]
  rfl

/-! ## The two morphisms of `ℤ[Gal(L/K)]`-modules -/

/-- **The projection `𝕀_{L,T} ⟶ ∏_{v ∈ S} (∏_{w | v} L_wˣ)`** of `ℤ[Gal(L/K)]`-modules. -/
noncomputable def hProjRep (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    hSupportedRep (L := L) T hT ⟶
      hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K)) :=
  Rep.ofHom
    { toFun := fun x => fun v =>
        Additive.ofMul (fiberProjHom S
          (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v)
      map_add' := fun x y => by
        funext v
        show Additive.ofMul (fiberProjHom S
              (((Additive.toMul (x + y) : ↥(supportedIdeles (L := L) T)) : Idele L)) v) =
          Additive.ofMul (fiberProjHom S
              (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v) +
            Additive.ofMul (fiberProjHom S
              (((Additive.toMul y : ↥(supportedIdeles (L := L) T)) : Idele L)) v)
        rw [show (((Additive.toMul (x + y) : ↥(supportedIdeles (L := L) T)) : Idele L)) =
            ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L) *
              ((Additive.toMul y : ↥(supportedIdeles (L := L) T)) : Idele L) from by
          rw [toMul_add]
          rfl]
        rw [show (fiberProjHom S) (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L) *
              ((Additive.toMul y : ↥(supportedIdeles (L := L) T)) : Idele L)) v =
            (fiberProjHom S) ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L) v *
              (fiberProjHom S) ((Additive.toMul y : ↥(supportedIdeles (L := L) T)) : Idele L) v from
          congrFun (map_mul (fiberProjHom S)
            ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)
            ((Additive.toMul y : ↥(supportedIdeles (L := L) T)) : Idele L)) v]
        rw [ofMul_mul]
      map_smul' := fun n x => by
        funext v
        show Additive.ofMul (fiberProjHom S
              (((Additive.toMul (n • x) : ↥(supportedIdeles (L := L) T)) : Idele L)) v) =
          n • Additive.ofMul (fiberProjHom S
              (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v)
        rw [show (((Additive.toMul (n • x) : ↥(supportedIdeles (L := L) T)) : Idele L)) =
            (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) ^ n from by
          rw [toMul_zsmul]
          rfl]
        rw [show (fiberProjHom S) ((((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) ^ n) v =
            ((fiberProjHom S) ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L) v) ^ n from
          congrFun (map_zpow (fiberProjHom S)
            ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L) n) v]
        rw [ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        funext v
        show Additive.ofMul (fiberProjHom S
              (((Additive.toMul ((hSupportedRep (L := L) T hT).ρ σ x) :
                ↥(supportedIdeles (L := L) T)) : Idele L)) v) =
          (hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))).ρ σ
            (fun v => Additive.ofMul (fiberProjHom S
              (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v)) v
        rw [show (hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))).ρ σ
              (fun v => Additive.ofMul (fiberProjHom S
                (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v)) v =
            (hFiberRep (K := K) (L := L) (v : Place K)).ρ σ
              (Additive.ofMul (fiberProjHom S
                (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v)) from
          hPiRep_ρ_apply _ _ _ _]
        rw [show (hFiberRep (K := K) (L := L) (v : Place K)).ρ σ
              (Additive.ofMul (fiberProjHom S
                (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v)) =
            Additive.ofMul (σ • (fiberProjHom S
                (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v)) from
          hFiberRep_ρ_apply (v := (v : Place K)) (γ := σ)
            (fiberProjHom S (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v)]
        rw [show (((Additive.toMul ((hSupportedRep (L := L) T hT).ρ σ x) :
                ↥(supportedIdeles (L := L) T)) : Idele L)) =
            σ • ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L) from
          rfl]
        rw [show (fiberProjHom S) (σ • ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v =
            σ • (fiberProjHom S) (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v from
          congrFun (fiberProjHom_smul S σ
            ((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) v] }

/-- **The gluing `∏_{v ∈ S} (∏_{w | v} L_wˣ) ⟶ 𝕀_{L,T}`** of `ℤ[Gal(L/K)]`-modules. -/
noncomputable def hGlueRep (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K)) ⟶
      hSupportedRep (L := L) T hT :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul
        ((glue S T hTS) (fun v : S => Additive.toMul (x v)))
      map_add' := fun x y => by
        show Additive.ofMul ((glue S T hTS) (fun v : S => Additive.toMul ((x + y) v))) =
          Additive.ofMul ((glue S T hTS) (fun v : S => Additive.toMul (x v))) +
            Additive.ofMul ((glue S T hTS) (fun v : S => Additive.toMul (y v)))
        rw [hPiRep_toMul_add, map_mul, ofMul_mul]
      map_smul' := fun n x => by
        show Additive.ofMul ((glue S T hTS) (fun v : S => Additive.toMul ((n • x) v))) =
          n • Additive.ofMul ((glue S T hTS) (fun v : S => Additive.toMul (x v)))
        rw [hPiRep_toMul_zsmul, map_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul ((glue S T hTS) (fun v : S => Additive.toMul
              ((hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))).ρ σ x v))) =
          (hSupportedRep (L := L) T hT).ρ σ (Additive.ofMul
            ((glue S T hTS) (fun v : S => Additive.toMul (x v))))
        have hρ : ((fun v : S => Additive.toMul
              ((hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))).ρ σ x v)) :
              (v : S) → ↥(fiberIdeles (K := K) (L := L) (v : Place K))) =
            (fun v : S => σ • Additive.toMul (x v)) := by
          funext v
          rw [show (hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))).ρ σ x v =
              (hFiberRep (K := K) (L := L) (v : Place K)).ρ σ (x v) from hPiRep_ρ_apply _ _ _ _]
          rw [show (hFiberRep (K := K) (L := L) (v : Place K)).ρ σ (x v) =
              Additive.ofMul (σ • (Additive.toMul (x v) :
                ↥(fiberIdeles (K := K) (L := L) (v : Place K)))) from
            hFiberRep_ρ_apply' (v := (v : Place K)) (γ := σ) (x v)]
          rw [show Additive.toMul (Additive.ofMul (σ • (Additive.toMul (x v) :
                ↥(fiberIdeles (K := K) (L := L) (v : Place K))))) =
              σ • (Additive.toMul (x v) :
                ↥(fiberIdeles (K := K) (L := L) (v : Place K))) from toMul_ofMul _]
          rfl
        rw [hρ]
        rw [show (hSupportedRep (L := L) T hT).ρ σ (Additive.ofMul
              ((glue S T hTS) (fun v : S => Additive.toMul (x v)))) =
            Additive.ofMul ⟨σ • ((((glue S T hTS) (fun v : S => Additive.toMul (x v))) :
                ↥(supportedIdeles (L := L) T)) : Idele L),
              smul_mem_supportedIdeles hT ((glue S T hTS)
                (fun v : S => Additive.toMul (x v))).2⟩ from
          hSupportedRep_ρ_ofMul T hT σ ((glue S T hTS) (fun v : S => Additive.toMul (x v)))]
        rw [show (glue S T hTS) (fun v : S => σ • Additive.toMul (x v)) =
            ⟨σ • ((((glue S T hTS) (fun v : S => Additive.toMul (x v))) :
                ↥(supportedIdeles (L := L) T)) : Idele L),
              smul_mem_supportedIdeles hT ((glue S T hTS)
                (fun v : S => Additive.toMul (x v))).2⟩ from
          Subtype.ext (glue_smul S T hT hTS σ (fun v : S => Additive.toMul (x v)))]
        rfl }

/-! ## The isomorphism -/

theorem hProjRep_toMul (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (x : (hSupportedRep (L := L) T hT).V) :
    ((fun v : S => Additive.toMul ((hProjRep S T hT hTS).hom x v)) :
        (v : S) → ↥(fiberIdeles (K := K) (L := L) (v : Place K)))
      = (fiberProjHom S) (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L)) := rfl

theorem hGlueRep_toMul (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (x : (hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))).V) :
    ((Additive.toMul ((hGlueRep S T hT hTS).hom x) : ↥(supportedIdeles (L := L) T)))
      = (glue S T hTS) (fun v : S => Additive.toMul (x v)) := rfl

theorem hProjRep_hGlueRep (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    hProjRep S T hT hTS ≫ hGlueRep S T hT hTS = 𝟙 (hSupportedRep (L := L) T hT) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show Additive.ofMul ((glue S T hTS) (fun v : S => Additive.toMul
      ((hProjRep S T hT hTS).hom x v))) = x
  rw [hProjRep_toMul]
  rw [show (glue S T hTS) ((fiberProjHom S)
        (((Additive.toMul x : ↥(supportedIdeles (L := L) T)) : Idele L))) =
      (Additive.toMul x : ↥(supportedIdeles (L := L) T)) from
    glue_fiberProj S T hTS (Additive.toMul x : ↥(supportedIdeles (L := L) T))]
  exact ofMul_toMul x

theorem hGlueRep_hProjRep (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    hGlueRep S T hT hTS ≫ hProjRep S T hT hTS =
      𝟙 (hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show (fun v : S => Additive.ofMul (fiberProjHom S
      ((Additive.toMul ((hGlueRep S T hT hTS).hom x) :
        ↥(supportedIdeles (L := L) T)) : Idele L) v)) = x
  rw [hGlueRep_toMul]
  rw [show (fun v : S => Additive.ofMul (fiberProjHom S ((((glue S T hTS)
        (fun u : S => Additive.toMul (x u)) : ↥(supportedIdeles (L := L) T))) : Idele L) v)) =
      (fun v : S => Additive.ofMul (fiberProj ((((glue S T hTS)
        (fun u : S => Additive.toMul (x u)) : ↥(supportedIdeles (L := L) T))) : Idele L) (v : Place K))) from by
    funext v
    rw [fiberProjHom_apply]]
  rw [show (fun v : S => Additive.ofMul (fiberProj ((((glue S T hTS)
        (fun u : S => Additive.toMul (x u)) : ↥(supportedIdeles (L := L) T))) : Idele L) (v : Place K))) =
      (fun v : S => Additive.ofMul (Additive.toMul (x v))) from by
    funext v
    rw [fiberProj_glue]
    rfl]
  exact funext (fun v => ofMul_toMul (x v))

/-- **The idèles supported on `T = ⋃_{v ∈ S} (places above `v`) decompose as the product of the
fibres**: an isomorphism of `ℤ[Gal(L/K)]`-modules
`𝕀_{L,T} ≅ ∏_{v ∈ S} (∏_{w | v} L_wˣ)`. -/
noncomputable def hSupportedRepIsoPi (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v) :
    hSupportedRep (L := L) T hT ≅
      hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K)) :=
  Iso.mk (hProjRep S T hT hTS) (hGlueRep S T hT hTS)
    (hProjRep_hGlueRep S T hT hTS) (hGlueRep_hProjRep S T hT hTS)

/-! ## Tate cohomology of a finite product of representations -/

/-- **The Tate cohomology of a finite product of representations is the product of the Tate
cohomologies.** -/
theorem natCard_tateCohomology_piRep {G : Type} [Group G] [Fintype G] {ι : Type} [Fintype ι]
    (M : ι → Rep ℤ G) (n : ℤ) :
    Nat.card (tateCohomology (piRep M) n) =
      Nat.card ((i : ι) → tateCohomology (M i) n) := by
  haveI hAdd : (tateCohomologyFunctor (R := ℤ) (G := G) n).Additive :=
    show Functor.Additive (tateComplexFunctor ℤ G ⋙
      HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℤ) n) from inferInstance
  haveI : PreservesFiniteProducts (tateCohomologyFunctor (R := ℤ) (G := G) n) := inferInstance
  haveI : PreservesLimitsOfShape (Discrete ι) (tateCohomologyFunctor (R := ℤ) (G := G) n) :=
    inferInstance
  have e1 : tateCohomology (piRep M) n ≅ tateCohomology (∏ᶜ M) n :=
    (tateCohomologyFunctor (R := ℤ) (G := G) n).mapIso (piRepIso M)
  have e2 : tateCohomology (∏ᶜ M) n ≅ ∏ᶜ fun i => tateCohomology (M i) n :=
    PreservesProduct.iso (tateCohomologyFunctor (R := ℤ) (G := G) n) M
  calc Nat.card (tateCohomology (piRep M) n)
      = Nat.card ↥(∏ᶜ fun i => tateCohomology (M i) n) := by
        rw [Nat.card_congr e1.toLinearEquiv.toEquiv,
          Nat.card_congr e2.toLinearEquiv.toEquiv]
    _ = Nat.card ↥(ModuleCat.of ℤ ((i : ι) → ↥(tateCohomology (M i) n))) :=
        Nat.card_congr (ModuleCat.piIsoPi _).toLinearEquiv.toEquiv
    _ = Nat.card ((i : ι) → tateCohomology (M i) n) := rfl

/-! ## The target -/

theorem natCard_tateCohomology_supportedIdelesRep {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (n : ℤ) :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.supportedIdelesRep (L := L) T hT) n) =
      Nat.card ((v : S) → tateCohomology
        (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (v : NK.GlobalCFT.Place K)) n) := by
  have e := hSupportedRepIsoPi S T hT hTS
  calc Nat.card (tateCohomology (supportedIdelesRep (L := L) T hT) n)
      = Nat.card (tateCohomology (hSupportedRep (L := L) T hT) n) := by
        rw [hSupportedRep_eq]
    _ = Nat.card (tateCohomology
          (hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K))) n) :=
        Nat.card_congr
          ((tateCohomologyFunctor (R := ℤ) (G := L ≃ₐ[K] L) n).mapIso e).toLinearEquiv.toEquiv
    _ = Nat.card (tateCohomology
          (piRep (fun v : S => fiberIdelesRep (K := K) (L := L) (v : Place K))) n) := by
        rw [show hPiRep (fun v : S => hFiberRep (K := K) (L := L) (v : Place K)) =
            piRep (fun v : S => fiberIdelesRep (K := K) (L := L) (v : Place K)) from by
          rw [hPiRep_eq]]
    _ = Nat.card ((v : S) → tateCohomology
          (fiberIdelesRep (K := K) (L := L) (v : Place K)) n) :=
        natCard_tateCohomology_piRep
          (fun v : S => fiberIdelesRep (K := K) (L := L) (v : Place K)) n

end NK.GlobalCFTdeep.Herbrand
