import Mathlib
import Submission.NK.GlobalCFTdeep.PlacePerm.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.PlacePerm

open NK.GlobalCFT
open NK.GlobalCFTdeep

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The Shapiro map on functions on a fibre

Let `v` be a place of `K`, `T` a `Gal(L/K)`-stable set of places of `L` and `w₀ ∈ T` a place above
`v`.  For `f : ↥(fibreSet T v) → ℤ` and `γ : Gal(L/K)` set `fibreToCoindFun f γ = f (γ⁻¹ • w₀)`,
the value at `γ` of the Shapiro map `ℤ[fibreSet T v] → Coind_{D_{w₀}}^G ℤ`.  Since the fibre is the
orbit of `w₀`, the assignment `γ ↦ γ⁻¹ • w₀` is a surjection `G → fibreSet T v` whose fibres are
the left cosets `g D_{w₀}`; thus `f ↦ (γ ↦ f (γ⁻¹ • w₀))` identifies `ℤ[fibreSet T v]` with the
`D_{w₀}`-invariant functions on `G`, which is the coinduced module. -/

variable (v : Place K) (T : Set (Place L))
  (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
  (w₀ : Place L) (hw₀ : w₀ ∈ fibreSet T v)

/-- The point `γ⁻¹ • w₀` of the fibre, as an element of `↥(fibreSet T v)`. -/
noncomputable def fibrePt (γ : L ≃ₐ[K] L) : ↥(fibreSet T v) :=
  ⟨γ⁻¹ • w₀, (smul_mem_fibreSet hT v hw₀ : γ⁻¹ • w₀ ∈ fibreSet T v)⟩

@[simp] theorem fibrePt_coe (γ : L ≃ₐ[K] L) :
    (fibrePt v T hT w₀ hw₀ γ : Place L) = γ⁻¹ • w₀ := rfl

/-- Two representatives of the same place of the fibre give the same point of the fibre. -/
theorem fibrePt_eq_of_smul_eq {σ : L ≃ₐ[K] L} {u : ↥(fibreSet T v)}
    (h : σ • w₀ = (u : Place L)) : fibrePt v T hT w₀ hw₀ σ⁻¹ = u := by
  apply Subtype.ext
  simpa using h

/-- The value at `γ` of the Shapiro map: `f ↦ (γ ↦ f (γ⁻¹ • w₀))`. -/
noncomputable def fibreToCoindFun (f : ↥(fibreSet T v) → ℤ) (γ : L ≃ₐ[K] L) : ℤ :=
  f (fibrePt v T hT w₀ hw₀ γ)

theorem fibreToCoindFun_apply (f : ↥(fibreSet T v) → ℤ) (γ : L ≃ₐ[K] L) :
    fibreToCoindFun v T hT w₀ hw₀ f γ = f (fibrePt v T hT w₀ hw₀ γ) := rfl

/-- `fibreToCoindFun f` is invariant under left multiplication by the decomposition group
`D_{w₀}`: the function `γ ↦ γ⁻¹ • w₀` is constant on the left cosets of `D_{w₀}`. -/
theorem fibreToCoindFun_invariant (f : ↥(fibreSet T v) → ℤ)
    (g : decompositionSubgroup (K := K) (L := L) w₀) (γ : L ≃ₐ[K] L) :
    fibreToCoindFun v T hT w₀ hw₀ f (g.1 * γ) = fibreToCoindFun v T hT w₀ hw₀ f γ := by
  have hg : g.1⁻¹ • w₀ = w₀ :=
    MulAction.mem_stabilizer_iff.mp
      (inv_mem g.2 : g.1⁻¹ ∈ decompositionSubgroup (K := K) (L := L) w₀)
  have hval : (g.1 * γ)⁻¹ • w₀ = γ⁻¹ • w₀ := by
    rw [mul_inv_rev, mul_smul, hg]
  simp only [fibreToCoindFun]
  exact congrArg f (Subtype.ext hval)

/-- **The Shapiro map** `ℤ[fibreSet T v] → Coind_{D_{w₀}}^G ℤ`, `f ↦ (γ ↦ f (γ⁻¹ • w₀))`,
as an element of the coinduced module. -/
noncomputable def fibreToCoind (f : ↥(fibreSet T v) → ℤ) :
    (Rep.coind (decompositionSubgroup (K := K) (L := L) w₀).subtype
      (Rep.trivial ℤ ↥(decompositionSubgroup (K := K) (L := L) w₀) ℤ)).V :=
  ⟨fibreToCoindFun v T hT w₀ hw₀ f, fun g h => by
    simpa only [Representation.trivial_apply, Subgroup.coe_subtype]
      using fibreToCoindFun_invariant v T hT w₀ hw₀ f g h⟩

/-- **The Shapiro map** as a `ℤ`-linear map. -/
noncomputable def fibreToCoindLin :
    (↥(fibreSet T v) → ℤ) →ₗ[ℤ]
      (Rep.coind (decompositionSubgroup (K := K) (L := L) w₀).subtype
        (Rep.trivial ℤ ↥(decompositionSubgroup (K := K) (L := L) w₀) ℤ)).V where
  toFun := fibreToCoind v T hT w₀ hw₀
  map_add' f g := by
    apply Subtype.ext
    funext γ
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext γ
    rfl

/-- The Shapiro map is `Gal(L/K)`-equivariant, on elements. -/
theorem fibreToCoind_smul_apply (f : ↥(fibreSet T v) → ℤ) (γ h : L ≃ₐ[K] L) :
    (fibreToCoind v T hT w₀ hw₀ ((fibreRep T hT v).ρ γ f) : (L ≃ₐ[K] L) → ℤ) h
      = ((Rep.coind (decompositionSubgroup (K := K) (L := L) w₀).subtype
          (Rep.trivial ℤ ↥(decompositionSubgroup (K := K) (L := L) w₀) ℤ)).ρ γ
            (fibreToCoind v T hT w₀ hw₀ f) : (L ≃ₐ[K] L) → ℤ) h := by
  change f ⟨γ⁻¹ • (h⁻¹ • w₀), (smul_mem_fibreSet hT v (smul_mem_fibreSet hT v hw₀) :
      γ⁻¹ • (h⁻¹ • w₀) ∈ fibreSet T v)⟩
    = f ⟨(h * γ)⁻¹ • w₀, (smul_mem_fibreSet hT v hw₀ : (h * γ)⁻¹ • w₀ ∈ fibreSet T v)⟩
  have hval : γ⁻¹ • (h⁻¹ • w₀) = (h * γ)⁻¹ • w₀ := by rw [mul_inv_rev, mul_smul]
  exact congrArg f (Subtype.ext hval)

/-- The Shapiro map is `Gal(L/K)`-equivariant. -/
theorem fibreToCoind_smul (f : ↥(fibreSet T v) → ℤ) (γ : L ≃ₐ[K] L) :
    fibreToCoind v T hT w₀ hw₀ ((fibreRep T hT v).ρ γ f)
      = (Rep.coind (decompositionSubgroup (K := K) (L := L) w₀).subtype
          (Rep.trivial ℤ ↥(decompositionSubgroup (K := K) (L := L) w₀) ℤ)).ρ γ
        (fibreToCoind v T hT w₀ hw₀ f) := by
  apply Subtype.ext
  funext h
  exact fibreToCoind_smul_apply v T hT w₀ hw₀ f γ h

/-- The Shapiro map is injective: an element of the fibre is `σ • w₀` for some `σ`, and
`f (σ⁻¹)` detects `f` at that place. -/
theorem fibreToCoindLin_injective : Function.Injective (fibreToCoindLin v T hT w₀ hw₀) := by
  intro f g hfg
  have hval : ∀ γ : L ≃ₐ[K] L,
      fibreToCoindFun v T hT w₀ hw₀ f γ = fibreToCoindFun v T hT w₀ hw₀ g γ := by
    intro γ
    exact congrFun (congrArg Subtype.val hfg) γ
  funext u
  obtain ⟨σ, hσ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hw₀.2 u.2.2
  have hu : fibrePt v T hT w₀ hw₀ σ⁻¹ = u := fibrePt_eq_of_smul_eq v T hT w₀ hw₀ hσ
  calc f u = f (fibrePt v T hT w₀ hw₀ σ⁻¹) := by rw [hu]
    _ = fibreToCoindFun v T hT w₀ hw₀ f σ⁻¹ := rfl
    _ = fibreToCoindFun v T hT w₀ hw₀ g σ⁻¹ := hval σ⁻¹
    _ = g (fibrePt v T hT w₀ hw₀ σ⁻¹) := rfl
    _ = g u := by rw [hu]

/-- **The Shapiro map is surjective**: a `D_{w₀}`-invariant function on `G` is determined by its
values at a set of representatives of the places of the fibre, and the choice
`u ↦ rep u` with `(rep u)⁻¹ • w₀ = u` makes this precise. -/
theorem fibreToCoindLin_surjective : Function.Surjective (fibreToCoindLin v T hT w₀ hw₀) := by
  intro F
  have hex : ∀ u : ↥(fibreSet T v), ∃ γ : L ≃ₐ[K] L, γ⁻¹ • w₀ = (u : Place L) := by
    intro u
    obtain ⟨σ, hσ⟩ :=
      NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hw₀.2 u.2.2
    exact ⟨σ⁻¹, by rw [inv_inv]; exact hσ⟩
  let rep : ↥(fibreSet T v) → L ≃ₐ[K] L := fun u => Classical.choose (hex u)
  have hrep : ∀ u : ↥(fibreSet T v), (rep u)⁻¹ • w₀ = (u : Place L) :=
    fun u => Classical.choose_spec (hex u)
  have hkey : ∀ {γ₁ γ₂ : L ≃ₐ[K] L}, γ₁⁻¹ • w₀ = γ₂⁻¹ • w₀ →
      (F : (L ≃ₐ[K] L) → ℤ) γ₁ = (F : (L ≃ₐ[K] L) → ℤ) γ₂ := by
    intro γ₁ γ₂ h
    have hmem : γ₂ * γ₁⁻¹ ∈ decompositionSubgroup (K := K) (L := L) w₀ := by
      rw [decompositionSubgroup_eq_stabilizer, MulAction.mem_stabilizer_iff]
      show (γ₂ * γ₁⁻¹) • w₀ = w₀
      rw [mul_smul, h, smul_inv_smul]
    have h2 := F.2 ⟨γ₂ * γ₁⁻¹, hmem⟩ γ₁
    simp only [Subgroup.coe_subtype, Representation.trivial_apply] at h2
    rw [mul_assoc, inv_mul_cancel, mul_one] at h2
    exact h2.symm
  refine ⟨fun u => (F : (L ≃ₐ[K] L) → ℤ) (rep u), ?_⟩
  apply Subtype.ext
  funext γ
  show (fun u => (F : (L ≃ₐ[K] L) → ℤ) (rep u)) (fibrePt v T hT w₀ hw₀ γ)
    = (F : (L ≃ₐ[K] L) → ℤ) γ
  refine hkey (γ₂ := γ) ?_
  rw [hrep]
  rfl

end

/-! ## Shapiro's lemma for a fibre -/

-- A single fibre `{w ∈ T | LiesOver w v}` of a `Gal(L/K)`-stable set `T` of places of `L` above a
-- place `v ∈ S` is a single `Gal(L/K)`-orbit (transitivity on the places above `v`), and hence its
-- permutation module `ℤ[fibre] = placeFunRep (fibreSet T v)` is the coinduced trivial module of
-- the decomposition group of any of its places (Shapiro's lemma).  Explicitly the isomorphism
-- sends `f` to `γ ↦ f (γ⁻¹ • (w v hv))`, onto the `D`-invariant functions `G → ℤ`.
theorem fibreRep_iso_coind {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (w : (v : NK.GlobalCFT.Place K) → v ∈ S → NK.GlobalCFT.Place L)
    (hw : ∀ (v : NK.GlobalCFT.Place K) (hv : v ∈ S),
      NK.GlobalCFT.Place.LiesOver (w v hv) v)
    (v : NK.GlobalCFT.Place K) (hv : v ∈ S) :
    Nonempty (NK.GlobalCFTdeep.PlacePerm.fibreRep (K := K) (L := L) T hT v ≅
      Rep.coind (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (w v hv)).subtype
        (Rep.trivial ℤ ↥(NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (w v hv))
          ℤ)) := by
  have hmem : w v hv ∈ fibreSet T v :=
    mem_fibreSet.mpr ⟨mem_T_of_liesOver hTS hv (hw v hv), hw v hv⟩
  refine ⟨Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.ofBijective (fibreToCoindLin v T hT (w v hv) hmem)
      ⟨fibreToCoindLin_injective v T hT (w v hv) hmem,
        fibreToCoindLin_surjective v T hT (w v hv) hmem⟩) ?_)⟩
  intro γ
  apply LinearMap.ext
  intro f
  exact fibreToCoind_smul v T hT (w v hv) hmem f γ

end NK.GlobalCFTdeep.PlacePerm
