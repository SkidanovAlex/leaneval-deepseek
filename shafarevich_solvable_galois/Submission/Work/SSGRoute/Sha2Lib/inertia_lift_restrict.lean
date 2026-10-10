import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.Work.SSGRoute.E9Nodes.e9_inertia_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lifting an inertia element along a finite Galois tower

Let `k ⊆ L ⊆ L'` be a tower of number fields with `L/k` and `L'/k` finite Galois, let `q` be a
nonzero prime of `𝒪 L`, `q'` a nonzero prime of `𝒪 L'` lying over `q`, and let `τ : L ≃ₐ[k] L` be
an element of the inertia group of `q` (`SSGRoute.PTExt.IsInertiaAt q τ`).

Then `τ` lifts to an element `γ : L' ≃ₐ[k] L'` of the inertia group of `q'` with the same
restriction to `L`: this is the surjectivity of the restriction map `I_{q'} ↠ I_q` on inertia
groups.

The proof follows the classical lines:

* **Decomposition correction.**  Lift `τ` arbitrarily to `σ₀ : Gal(L'/k)`.  Since `Gal(L'/L)` acts
  transitively on the primes of `𝒪 L'` above `q` (`Ideal.exists_comap_galRestrict_eq`), some
  `ρ : Gal(L'/L)` moves `σ₀ • q'` back to `q'`; then `ρ · σ₀` (viewed in `Gal(L'/k)`) has
  `(ρ · σ₀) • q' = q'` and still restricts to `τ`.
* **Inertia correction.**  With `σ₁` in the decomposition group of `q'` and `τ ∈ I_q`, the action
  `γbar` of `σ₁` on the residue ring `𝒪 L' ⧸ q'` is `κ(q)`-linear; since the stabiliser of `q'` in
  `Gal(L'/L)` surjects onto the automorphisms of `𝒪 L' ⧸ q'` over `κ(q)`
  (`Ideal.Quotient.stabilizerHom_surjective`, whose kernel is the ideal-theoretic inertia), some
  `h ∈ Gal(L'/L)` has residue action `γbar⁻¹`, and `h · σ₁` is the required inertia element.
-/

namespace Work.SSGRoute.Sha2Lib

open scoped Pointwise NumberField

attribute [local instance] Ideal.pointwiseMulSemiringAction

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {k L L' : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
  [Field L'] [NumberField L'] [Algebra k L'] [Algebra L L'] [IsScalarTower k L L']
  [FiniteDimensional k L] [FiniteDimensional L L'] [IsGalois k L] [IsGalois k L']

/-! ## The two actions on `𝒪 L'` and the valuation form of inertia -/

/-- `IsInertiaAt q' γ` is equivalent to `γ` acting trivially modulo `q'` on `𝒪 L'`. -/
lemma isInertiaAt_iff_smul_sub_mem (q' : IsDedekindDomain.HeightOneSpectrum (𝓞 L'))
    (γ : L' ≃ₐ[k] L') :
    SSGRoute.PTExt.IsInertiaAt q' γ ↔ ∀ x : 𝓞 L', γ • x - x ∈ q'.asIdeal := by
  unfold SSGRoute.PTExt.IsInertiaAt
  refine forall_congr' fun x => ?_
  have key : ((γ • x - x : 𝓞 L') : L') = γ (x : L') - (x : L') := by
    have h : algebraMap (𝓞 L') L' (γ • x - x) =
        algebraMap (𝓞 L') L' (γ • x) - algebraMap (𝓞 L') L' x := map_sub _ _ _
    rw [show ((γ • x - x : 𝓞 L') : L') = algebraMap (𝓞 L') L' (γ • x - x) from rfl, h,
      algebraMap.smul']
    rfl
  rw [← key]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L') q' _

/-- The `Gal(L'/k)`-action of `𝒪 L'` agrees with `galRestrict`. -/
lemma galRestrict_smul_apply (γ : L' ≃ₐ[k] L') (x : 𝓞 L') :
    galRestrict (𝓞 k) k L' (𝓞 L') γ x = γ • x := by
  apply NumberField.RingOfIntegers.ext
  change algebraMap (𝓞 L') L' (galRestrict (𝓞 k) k L' (𝓞 L') γ x) =
    algebraMap (𝓞 L') L' (γ • x)
  rw [algebraMap_galRestrict_apply, algebraMap.smul']
  rfl

/-- The `Gal(L'/L)`-action of `𝒪 L'` agrees with `galRestrict` and with the `Gal(L'/k)`-action. -/
lemma galRestrict_restrictScalars_smul_apply (ρ : L' ≃ₐ[L] L') (x : 𝓞 L') :
    galRestrict (𝓞 L) L L' (𝓞 L') ρ x = (AlgEquiv.restrictScalars k ρ) • x := by
  apply NumberField.RingOfIntegers.ext
  change algebraMap (𝓞 L') L' (galRestrict (𝓞 L) L L' (𝓞 L') ρ x) =
    algebraMap (𝓞 L') L' ((AlgEquiv.restrictScalars k ρ) • x)
  rw [algebraMap_galRestrict_apply, algebraMap.smul']
  rfl

/-- Instance of `galRestrict_smul_apply` at the base level `L' = L`. -/
lemma galRestrict_smul_apply_base (γ : L ≃ₐ[k] L) (y : 𝓞 L) :
    galRestrict (𝓞 k) k L (𝓞 L) γ y = γ • y :=
  galRestrict_smul_apply γ y

/-- `MulSemiringAction.toRingHom` of the `Gal(L'/k)`-action is `galRestrict`. -/
lemma toRingHom_galRestrict_k (γ : L' ≃ₐ[k] L') :
    (MulSemiringAction.toRingHom (L' ≃ₐ[k] L') (𝓞 L') γ : 𝓞 L' →+* 𝓞 L') =
      (galRestrict (𝓞 k) k L' (𝓞 L') γ : 𝓞 L' →+* 𝓞 L') := by
  ext x
  change algebraMap (𝓞 L') L' ((MulSemiringAction.toRingHom (L' ≃ₐ[k] L') (𝓞 L') γ) x) =
    algebraMap (𝓞 L') L' (galRestrict (𝓞 k) k L' (𝓞 L') γ x)
  rw [MulSemiringAction.toRingHom_apply, algebraMap.smul', algebraMap_galRestrict_apply]
  rfl

/-- `MulSemiringAction.toRingHom` of the `Gal(L'/L)`-action (viewed over `k`) is `galRestrict`. -/
lemma toRingHom_galRestrict_L (ρ : L' ≃ₐ[L] L') :
    (MulSemiringAction.toRingHom (L' ≃ₐ[k] L') (𝓞 L') (AlgEquiv.restrictScalars k ρ) :
        𝓞 L' →+* 𝓞 L') =
      (galRestrict (𝓞 L) L L' (𝓞 L') ρ : 𝓞 L' →+* 𝓞 L') := by
  ext x
  change algebraMap (𝓞 L') L'
      ((MulSemiringAction.toRingHom (L' ≃ₐ[k] L') (𝓞 L') (AlgEquiv.restrictScalars k ρ)) x) =
    algebraMap (𝓞 L') L' (galRestrict (𝓞 L) L L' (𝓞 L') ρ x)
  rw [MulSemiringAction.toRingHom_apply, algebraMap.smul', algebraMap_galRestrict_apply]
  rfl

lemma smul_ideal_map_galRestrict (γ : L' ≃ₐ[k] L') (I : Ideal (𝓞 L')) :
    γ • I = I.map (galRestrict (𝓞 k) k L' (𝓞 L') γ : 𝓞 L' →+* 𝓞 L') := by
  rw [Ideal.pointwise_smul_def, toRingHom_galRestrict_k]

lemma smul_ideal_map_galRestrict_restrictScalars (ρ : L' ≃ₐ[L] L') (I : Ideal (𝓞 L')) :
    (AlgEquiv.restrictScalars k ρ) • I =
      I.map (galRestrict (𝓞 L) L L' (𝓞 L') ρ : 𝓞 L' →+* 𝓞 L') := by
  rw [Ideal.pointwise_smul_def, toRingHom_galRestrict_L]

/-- The automorphism of `𝒪 L'` attached to `σ : Gal(L'/k)` by the place theory is `galRestrict`. -/
lemma ringOfIntegersEquiv_eq_galRestrict (σ : L' ≃ₐ[k] L') :
    (NK.GlobalCFT.Place.ringOfIntegersEquiv σ : 𝓞 L' →+* 𝓞 L') =
      (galRestrict (𝓞 k) k L' (𝓞 L') σ : 𝓞 L' →+* 𝓞 L') := by
  ext x
  change algebraMap (𝓞 L') L' (NK.GlobalCFT.Place.ringOfIntegersEquiv σ x) =
    algebraMap (𝓞 L') L' (galRestrict (𝓞 k) k L' (𝓞 L') σ x)
  rw [algebraMap_galRestrict_apply]
  rfl

/-- Congruence of `Ideal.map` in the map (a substitute for the missing Mathlib lemma). -/
lemma ideal_map_congr_apply {R S : Type*} [Semiring R] [Semiring S] {f g : R →+* S}
    (h : ∀ x, f x = g x) (I : Ideal R) : I.map f = I.map g := by
  rw [Ideal.map, Ideal.map]
  congr 1
  ext x
  exact ⟨fun ⟨y, hy, hyx⟩ => ⟨y, hy, by rw [← hyx, h y]⟩,
    fun ⟨y, hy, hyx⟩ => ⟨y, hy, by rw [← hyx, ← h y]⟩⟩

/-- The place-theoretic automorphism of `𝒪 L'` and `galRestrict` agree pointwise. -/
lemma ringOfIntegersEquiv_galRestrict_apply (σ : L' ≃ₐ[k] L') (x : 𝓞 L') :
    NK.GlobalCFT.Place.ringOfIntegersEquiv σ x = galRestrict (𝓞 k) k L' (𝓞 L') σ x := by
  apply NumberField.RingOfIntegers.ext
  change algebraMap (𝓞 L') L' (NK.GlobalCFT.Place.ringOfIntegersEquiv σ x) =
    algebraMap (𝓞 L') L' (galRestrict (𝓞 k) k L' (𝓞 L') σ x)
  rw [algebraMap_galRestrict_apply]
  rfl

/-- Compatibility of `galRestrict` with the inclusion `𝒪 L → 𝒪 L'` along `restrictNormalHom`. -/
lemma galRestrict_algebraMap (σ : L' ≃ₐ[k] L') (y : 𝓞 L) :
    galRestrict (𝓞 k) k L' (𝓞 L') σ (algebraMap (𝓞 L) (𝓞 L') y) =
      algebraMap (𝓞 L) (𝓞 L')
        (galRestrict (𝓞 k) k L (𝓞 L) (AlgEquiv.restrictNormalHom L σ) y) := by
  apply NumberField.RingOfIntegers.ext
  change algebraMap (𝓞 L') L'
      (galRestrict (𝓞 k) k L' (𝓞 L') σ (algebraMap (𝓞 L) (𝓞 L') y)) =
    algebraMap (𝓞 L') L'
      (algebraMap (𝓞 L) (𝓞 L')
        (galRestrict (𝓞 k) k L (𝓞 L) (AlgEquiv.restrictNormalHom L σ) y))
  simp only [algebraMap_galRestrict_apply, ← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 L') L',
    IsScalarTower.algebraMap_apply (𝓞 L) L L']
  exact (AlgEquiv.restrictNormal_commutes σ L (y : L)).symm

/-- `AlgEquiv.restrictScalars` lands in the kernel of the restriction map. -/
lemma galRes_restrictScalars (ρ : L' ≃ₐ[L] L') :
    SSGRoute.PTExt.galRes k L L' (AlgEquiv.restrictScalars k ρ) = 1 := by
  ext x
  show (AlgEquiv.restrictNormal (AlgEquiv.restrictScalars k ρ) L) x = x
  apply (algebraMap L L').injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply]
  exact ρ.commutes x

/-- The restriction of an inertia element of `q` lies in the stabiliser of `q`. -/
lemma galRes_mem_stabilizer_of_isInertiaAt (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (σ : L' ≃ₐ[k] L') (hτ : SSGRoute.PTExt.IsInertiaAt q (SSGRoute.PTExt.galRes k L L' σ)) :
    SSGRoute.PTExt.galRes k L L' σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) q.asIdeal :=
  Ideal.inertia_le_stabilizer q.asIdeal
    ((E9Nodes.isInertiaAt_iff_mem_inertia q (SSGRoute.PTExt.galRes k L L' σ)).mp hτ)

/-! ## The inertia correction at a fixed decomposition group -/

lemma exists_inertia_lift_of_stab
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (q' : IsDedekindDomain.HeightOneSpectrum (𝓞 L'))
    (hq : q'.asIdeal.LiesOver q.asIdeal)
    (σ : L' ≃ₐ[k] L') (hstab : σ ∈ MulAction.stabilizer (L' ≃ₐ[k] L') q'.asIdeal)
    (hres : SSGRoute.PTExt.IsInertiaAt q (SSGRoute.PTExt.galRes k L L' σ)) :
    ∃ h : L' ≃ₐ[L] L', SSGRoute.PTExt.IsInertiaAt q' (AlgEquiv.restrictScalars k h * σ) := by
  classical
  haveI hGal : IsGalois L L' := IsGalois.tower_top_of_isGalois k L L'
  haveI hlies : q'.asIdeal.LiesOver (q'.asIdeal.under (𝓞 k)) := Ideal.over_under q'.asIdeal
  -- the action of `σ` on the residue ring `𝒪 L' ⧸ q'` over `κ(q ∩ 𝒪 k)`
  let γbar := Ideal.Quotient.stabilizerHom q'.asIdeal (q'.asIdeal.under (𝓞 k))
    (L' ≃ₐ[k] L') ⟨σ, hstab⟩
  have hγbar_apply : ∀ z : 𝓞 L', γbar (Ideal.Quotient.mk q'.asIdeal z) =
      Ideal.Quotient.mk q'.asIdeal (galRestrict (𝓞 k) k L' (𝓞 L') σ z) := by
    intro z
    rw [Ideal.Quotient.stabilizerHom_apply]
    congr 1
    exact (galRestrict_smul_apply σ z).symm
  -- `γbar` is `κ(q)`-linear
  have hres' : ∀ y : 𝓞 L,
      galRestrict (𝓞 k) k L (𝓞 L) (SSGRoute.PTExt.galRes k L L' σ) y - y ∈ q.asIdeal := by
    intro y
    rw [galRestrict_smul_apply_base (SSGRoute.PTExt.galRes k L L' σ) y]
    exact (isInertiaAt_iff_smul_sub_mem q (SSGRoute.PTExt.galRes k L L' σ)).mp hres y
  have hfix : ∀ a : 𝓞 L ⧸ q.asIdeal,
      γbar (algebraMap (𝓞 L ⧸ q.asIdeal) (𝓞 L' ⧸ q'.asIdeal) a) =
        algebraMap (𝓞 L ⧸ q.asIdeal) (𝓞 L' ⧸ q'.asIdeal) a := by
    intro a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, hγbar_apply, galRestrict_algebraMap]
    rw [Ideal.Quotient.eq, ← map_sub]
    exact (Ideal.mem_of_liesOver q'.asIdeal q.asIdeal _).mp (hres' y)
  let γbarL : (𝓞 L' ⧸ q'.asIdeal) ≃ₐ[𝓞 L ⧸ q.asIdeal] (𝓞 L' ⧸ q'.asIdeal) :=
    { γbar with commutes' := hfix }
  -- the stabiliser of `q'` over `L` surjects onto the residue automorphisms over `κ(q)`
  letI actH : MulSemiringAction (L' ≃ₐ[L] L') (𝓞 L') :=
    IsIntegralClosure.MulSemiringAction (𝓞 L) L L' (𝓞 L')
  haveI scc : SMulCommClass (L' ≃ₐ[L] L') (𝓞 L) (𝓞 L') :=
    ⟨fun g a x => by
      show galRestrict (𝓞 L) L L' (𝓞 L') g (algebraMap (𝓞 L) (𝓞 L') a * x) =
        algebraMap (𝓞 L) (𝓞 L') a * galRestrict (𝓞 L) L L' (𝓞 L') g x
      rw [map_mul, AlgEquiv.commutes]⟩
  haveI inv : Algebra.IsInvariant (𝓞 L) (𝓞 L') (L' ≃ₐ[L] L') :=
    Algebra.isInvariant_of_isGalois (𝓞 L) L L' (𝓞 L')
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : MulAction.stabilizer (L' ≃ₐ[L] L') q'.asIdeal,
      Ideal.Quotient.stabilizerHom q'.asIdeal q.asIdeal (L' ≃ₐ[L] L') τ₀ = γbarL.symm :=
    Ideal.Quotient.stabilizerHom_surjective (L' ≃ₐ[L] L') q.asIdeal q'.asIdeal γbarL.symm
  refine ⟨(τ₀ : L' ≃ₐ[L] L'), ?_⟩
  -- the two `•`-actions of `Gal(L'/L)` on `𝒪 L'` agree
  have hsmul_ic : ∀ z : 𝓞 L', (AlgEquiv.restrictScalars k (τ₀ : L' ≃ₐ[L] L')) • z =
      (τ₀ : L' ≃ₐ[L] L') • z := by
    intro z
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 L') L' ((AlgEquiv.restrictScalars k (τ₀ : L' ≃ₐ[L] L')) • z) =
      algebraMap (𝓞 L') L' ((τ₀ : L' ≃ₐ[L] L') • z)
    conv_lhs => rw [algebraMap.smul']
    conv_rhs => rw [algebraMap.smul']
    rfl
  -- the final residue computation
  rw [isInertiaAt_iff_smul_sub_mem]
  intro x
  refine (Ideal.Quotient.eq).mp ?_
  have h1 : Ideal.Quotient.mk q'.asIdeal (σ • x) = γbar (Ideal.Quotient.mk q'.asIdeal x) := by
    rw [← galRestrict_smul_apply σ x]
    exact (hγbar_apply x).symm
  have h2 : Ideal.Quotient.mk q'.asIdeal
      (((AlgEquiv.restrictScalars k (τ₀ : L' ≃ₐ[L] L')) * σ) • x) =
      γbarL.symm (Ideal.Quotient.mk q'.asIdeal (σ • x)) := by
    rw [mul_smul, hsmul_ic]
    rw [show Ideal.Quotient.mk q'.asIdeal ((τ₀ : L' ≃ₐ[L] L') • (σ • x)) =
        (Ideal.Quotient.stabilizerHom q'.asIdeal q.asIdeal (L' ≃ₐ[L] L')) τ₀
          (Ideal.Quotient.mk q'.asIdeal (σ • x)) from by
      rw [Ideal.Quotient.stabilizerHom_apply]
      rfl]
    rw [hτ₀]
  calc Ideal.Quotient.mk q'.asIdeal (((AlgEquiv.restrictScalars k (τ₀ : L' ≃ₐ[L] L')) * σ) • x)
      = γbarL.symm (Ideal.Quotient.mk q'.asIdeal (σ • x)) := h2
    _ = γbarL.symm (γbar (Ideal.Quotient.mk q'.asIdeal x)) := by rw [h1]
    _ = Ideal.Quotient.mk q'.asIdeal x := by
        rw [show γbarL.symm (γbar (Ideal.Quotient.mk q'.asIdeal x)) =
            γbarL.symm (γbarL (Ideal.Quotient.mk q'.asIdeal x)) from rfl]
        exact AlgEquiv.symm_apply_apply γbarL _

/-! ## The decomposition correction -/

/-- For a lift `σ` of `τ` whose restriction is inertial at `q`, some `ρ ∈ Gal(L'/L)` makes
`ρ · σ` stabilise `q'`. -/
lemma exists_stab_correction
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (q' : IsDedekindDomain.HeightOneSpectrum (𝓞 L'))
    (hq : q'.asIdeal.LiesOver q.asIdeal)
    (σ : L' ≃ₐ[k] L') (hres : SSGRoute.PTExt.IsInertiaAt q (SSGRoute.PTExt.galRes k L L' σ)) :
    ∃ ρ : L' ≃ₐ[L] L',
      (AlgEquiv.restrictScalars k ρ * σ) ∈ MulAction.stabilizer (L' ≃ₐ[k] L') q'.asIdeal := by
  haveI hGal : IsGalois L L' := IsGalois.tower_top_of_isGalois k L L'
  have hgal : SSGRoute.PTExt.galRes k L L' σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) q.asIdeal :=
    galRes_mem_stabilizer_of_isInertiaAt q σ hres
  -- the moved prime `σ • q'` and its contraction
  have hP₀prime : (σ • q'.asIdeal).IsPrime := inferInstance
  have hP₀lies : (σ • q'.asIdeal).LiesOver q.asIdeal := by
    have hA : ∀ y : L, algebraMap L L' ((SSGRoute.PTExt.galRes k L L' σ) y) =
        σ (algebraMap L L' y) :=
      fun y => AlgEquiv.restrictNormal_commutes σ L y
    have h1 := NK.HassePrinciple.liesOver_map_ringOfIntegersEquiv σ
      (SSGRoute.PTExt.galRes k L L' σ) hA hq
    have h2 : Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv
        (SSGRoute.PTExt.galRes k L L' σ)) q.asIdeal = q.asIdeal := by
      rw [show Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv
              (SSGRoute.PTExt.galRes k L L' σ)) q.asIdeal
            = (SSGRoute.PTExt.galRes k L L' σ) • q.asIdeal from by
          rw [smul_ideal_map_galRestrict]
          exact ideal_map_congr_apply
            (fun x => ringOfIntegersEquiv_galRestrict_apply (SSGRoute.PTExt.galRes k L L' σ) x)
            q.asIdeal]
      exact MulAction.mem_stabilizer_iff.mp hgal
    rw [h2] at h1
    rw [show σ • q'.asIdeal = Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv σ) q'.asIdeal from by
      rw [smul_ideal_map_galRestrict]
      exact ideal_map_congr_apply
        (fun x => (ringOfIntegersEquiv_galRestrict_apply σ x).symm) q'.asIdeal]
    exact h1
  obtain ⟨ρ, hρ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 L) L L' (𝓞 L') (p := q.asIdeal)
    (P₁ := q'.asIdeal) (P₂ := σ • q'.asIdeal) ⟨q'.isPrime, hq⟩ ⟨hP₀prime, hP₀lies⟩
  refine ⟨ρ, ?_⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul, smul_ideal_map_galRestrict_restrictScalars,
    ← hρ]
  exact Ideal.map_comap_of_surjective _ (galRestrict (𝓞 L) L L' (𝓞 L') ρ).surjective q'.asIdeal

/-! ## The main theorem -/

theorem inertia_lift_restrict (k L L' : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [Field L'] [NumberField L'] [Algebra k L'] [Algebra L L']
    [IsScalarTower k L L'] [FiniteDimensional k L] [FiniteDimensional k L']
    [FiniteDimensional L L'] [IsGalois k L] [IsGalois k L']
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
    (hq : q'.asIdeal.LiesOver q.asIdeal)
    (τ : L ≃ₐ[k] L) (hτ : SSGRoute.PTExt.IsInertiaAt q τ) :
    ∃ γ : L' ≃ₐ[k] L', SSGRoute.PTExt.IsInertiaAt q' γ ∧
      ∀ x : L, γ (algebraMap L L' x) = algebraMap L L' (τ x) := by
  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := L) L' τ
  have hσ₀' : SSGRoute.PTExt.galRes k L L' σ₀ = τ := hσ₀
  have hres₀ : SSGRoute.PTExt.IsInertiaAt q (SSGRoute.PTExt.galRes k L L' σ₀) := by
    rw [hσ₀']; exact hτ
  obtain ⟨ρ, hρ⟩ := exists_stab_correction q q' hq σ₀ hres₀
  have hres₁ : SSGRoute.PTExt.IsInertiaAt q
      (SSGRoute.PTExt.galRes k L L' (AlgEquiv.restrictScalars k ρ * σ₀)) := by
    rw [map_mul, galRes_restrictScalars, one_mul, hσ₀']; exact hτ
  obtain ⟨h, hh⟩ := exists_inertia_lift_of_stab q q' hq (AlgEquiv.restrictScalars k ρ * σ₀) hρ hres₁
  refine ⟨AlgEquiv.restrictScalars k h * (AlgEquiv.restrictScalars k ρ * σ₀), hh, ?_⟩
  have hresγ : (AlgEquiv.restrictScalars k h * (AlgEquiv.restrictScalars k ρ * σ₀)).restrictNormal L
      = τ := by
    show SSGRoute.PTExt.galRes k L L' (AlgEquiv.restrictScalars k h * (AlgEquiv.restrictScalars k ρ * σ₀))
      = τ
    rw [map_mul, map_mul, galRes_restrictScalars, galRes_restrictScalars, one_mul, one_mul, hσ₀']
  intro x
  calc (AlgEquiv.restrictScalars k h * (AlgEquiv.restrictScalars k ρ * σ₀)) (algebraMap L L' x)
      = algebraMap L L'
          (((AlgEquiv.restrictScalars k h * (AlgEquiv.restrictScalars k ρ * σ₀)).restrictNormal L) x) :=
        (AlgEquiv.restrictNormal_commutes _ L x).symm
    _ = algebraMap L L' (τ x) := by rw [hresγ]

end Work.SSGRoute.Sha2Lib
