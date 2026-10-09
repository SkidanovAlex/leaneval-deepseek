import Mathlib
import Submission.Work.SSGRoute.E1aClean.decompDatum
import Submission.Work.SSGRoute.E1aClean.decompDatumFacts
import Submission.Work.SSGRoute.E1aClean.LocalExtensionAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois group of the henselisation over the decomposition field

For a finite place `A` of `Ω` over the prime `q` of `K`, the decomposition field `k^h = Ω^{D_A}`
and the henselisation `K^h = K·Ω^{D_A} = Ω^{D_A ⊓ Gal(Ω/K)}`, the restriction along `Ω` identifies
the decomposition group `D_q ≤ Gal(K/k)` with `Gal(K^h/k^h)`, compatibly with the restriction to
`K`: the automorphism `e τ` of `K^h/k^h` attached to `τ` acts on `K ⊆ K^h` as `τ` does.

This is the group identification used by the local dictionary of
`Work.SSGRoute.E1aClean.localDictionary_natural_family`: it is what makes `(K^h)ˣ` a
`D_q`-representation and what makes the coefficient change `Kˣ → (K^h)ˣ → K_qˣ` a morphism of
`D_q`-representations.

Route.  `restrictNormalHom : Gal(Ω/k^h) →* Gal(K^h/k^h)` is surjective with kernel `Gal(Ω/K^h)`;
its domain is `D_A = decomp k A` (`decompField_fixingSubgroup_via`).  The restriction `D_A → D_q`
is onto (`decomp_map_res_eq_decompK`), and the two maps have the same kernel
`D_A ⊓ Gal(Ω/K) = {σ ∈ D_A | σ|_K = 1}` (an element of `D_A` fixes `K^h` iff it fixes `K`).
Both are therefore `D_A ⧸ (D_A ⊓ Gal(Ω/K))`, and the witness `e` is assembled by `Classical.choose`
on the surjectivity of `D_A → D_q`, so that the defining property `e (res' σ) = ρ σ` is immediate.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped Pointwise

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- **The decomposition group of `A` is the Galois group of `K^h` over `k^h`.**

`e : D_q ≃* Gal(K^h/k^h)` is the restriction isomorphism, and `e τ` acts on `K ⊆ K^h` as `τ`. -/
theorem decompField_hensel_groupIso (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∃ e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A),
      ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
        ((e τ) ⟨(x : Ω), le_henselField k Ω K A x.2⟩ : Ω) = ((τ : K ≃ₐ[k] K) x : Ω) := by
  classical
  haveI : IsAlgClosure ↥(decompField k Ω A) Ω := (decompField_datum_facts k Ω K A).1
  haveI : FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_finiteDimensional k Ω K A
  haveI : IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_isGalois k Ω K A
  have hfix : (decompField k Ω A).fixingSubgroup = SSGRoute.decomp k A :=
    decompField_fixingSubgroup_via k Ω K A rfl
  -- ## the identification `D_A ≃* Gal(Ω/k^h)`
  let toGal : ↥(SSGRoute.decomp k A) ≃* (Ω ≃ₐ[↥(decompField k Ω A)] Ω) :=
    (MulEquiv.subgroupCongr hfix).symm.trans
      (IntermediateField.fixingSubgroupEquiv (decompField k Ω A))
  have toGal_apply : ∀ (σ : ↥(SSGRoute.decomp k A)),
      ((toGal σ : Ω ≃ₐ[↥(decompField k Ω A)] Ω) : Ω → Ω) = (σ : Ω ≃ₐ[k] Ω) := fun σ => rfl
  -- ## restriction to the henselisation
  let rn : (Ω ≃ₐ[↥(decompField k Ω A)] Ω) →*
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) :=
    AlgEquiv.restrictNormalHom (F := ↥(decompField k Ω A)) (K₁ := Ω) ↥(henselOverDecomp k Ω K A)
  let ρ : ↥(SSGRoute.decomp k A) →*
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) :=
    rn.comp toGal.toMonoidHom
  have rho_apply : ∀ (σ : ↥(SSGRoute.decomp k A)) (x : ↥(henselOverDecomp k Ω K A)),
      ((ρ σ) x : Ω) = ((σ : Ω ≃ₐ[k] Ω) x : Ω) := by
    intro σ x
    rw [show ((ρ σ) x : Ω) =
      (((rn (toGal σ)) x : Ω)) from rfl]
    rw [AlgEquiv.restrictNormalHom_apply]
    rfl
  -- ## restriction to `K`
  let res' : ↥(SSGRoute.decomp k A) →*
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
    { toFun := fun σ => ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω), by
        rw [← decomp_map_res_eq_decompK k Ω K A hA q hAq]
        exact Subgroup.mem_map_of_mem _ σ.2⟩
      map_one' := Subtype.ext (map_one (SSGRoute.res k K))
      map_mul' := fun σ τ => Subtype.ext (map_mul (SSGRoute.res k K) _ _) }
  have res'_apply : ∀ (σ : ↥(SSGRoute.decomp k A)),
      ((res' σ : K ≃ₐ[k] K)) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) := fun σ => rfl
  -- ## the two kernels agree
  have hker_iff : ∀ x : ↥(SSGRoute.decomp k A), (ρ x = 1) ↔ (res' x = 1) := by
    intro σ
    constructor
    · intro h
      -- `ρ σ = 1` means `σ` fixes `K^h`, hence `K`
      apply Subtype.ext
      apply AlgEquiv.ext
      intro y
      have h2 : ((ρ σ) ⟨(y : Ω), le_henselField k Ω K A y.2⟩ : Ω) = (y : Ω) := by
        rw [h]; simp
      have h3 : (σ : Ω ≃ₐ[k] Ω) (y : Ω) = (y : Ω) :=
        (rho_apply σ ⟨(y : Ω), le_henselField k Ω K A y.2⟩).symm.trans h2
      apply Subtype.ext
      show ((((res' σ) : K ≃ₐ[k] K) y : Ω)) = ((y : Ω))
      rw [res'_apply σ]
      exact (AlgEquiv.restrictNormalHom_apply K (σ : Ω ≃ₐ[k] Ω) y).trans h3
    · intro h
      -- `σ` fixes `K` and `σ ∈ D_A`, hence `σ ∈ D_A ⊓ Gal(Ω/K)` fixes `K^h`
      have hres : SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) = 1 := by
        have := congrArg (fun τ : ↥(SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite q)) => (τ : K ≃ₐ[k] K)) h
        rw [res'_apply] at this
        simpa using this
      have hK : (σ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := by
        rw [← IntermediateField.restrictNormalHom_ker K]
        exact MonoidHom.mem_ker.mpr hres
      apply AlgEquiv.ext
      intro x
      have hx : (x : Ω) ∈ henselField k Ω K A := x.2
      rw [henselField] at hx
      rw [IntermediateField.mem_fixedField_iff] at hx
      have hmem : (σ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker :=
        ⟨σ.2, MonoidHom.mem_ker.mpr hres⟩
      have hfixx : (σ : Ω ≃ₐ[k] Ω) (x : Ω) = (x : Ω) := hx (σ : Ω ≃ₐ[k] Ω) hmem
      exact Subtype.ext ((rho_apply σ x).trans hfixx)
  have hker : ρ.ker = res'.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact hker_iff x
  -- ## surjectivity of the two maps
  have hres'_surj : Function.Surjective res' := by
    intro τ
    have hmem : (τ : K ≃ₐ[k] K) ∈ (SSGRoute.decomp k A).map (SSGRoute.res k K) := by
      rw [decomp_map_res_eq_decompK k Ω K A hA q hAq]
      exact τ.2
    obtain ⟨σ, hσ, hres⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨σ, hσ⟩, Subtype.ext hres⟩
  have hρ_surj : Function.Surjective ρ := by
    intro γ
    obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥(decompField k Ω A))
      (K₁ := ↥(henselOverDecomp k Ω K A)) (E := Ω) γ
    refine ⟨toGal.symm g, ?_⟩
    show rn (toGal (toGal.symm g)) = γ
    rw [MulEquiv.apply_symm_apply]
    exact hg
  -- ## well-definedness and the assembled map
  have hwd : ∀ a b : ↥(SSGRoute.decomp k A), res' a = res' b → ρ a = ρ b := by
    intro a b hab
    have h1 : ρ (a⁻¹ * b) = 1 := by
      rw [hker_iff]
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    rw [map_mul, map_inv] at h1
    have h2 : ρ b = ρ a := by
      have h3 : ρ a * ((ρ a)⁻¹ * ρ b) = ρ a * 1 := by rw [h1]
      rwa [mul_inv_cancel_left, mul_one] at h3
    exact h2.symm
  let sec : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) →
      ↥(SSGRoute.decomp k A) := fun τ => Classical.choose (hres'_surj τ)
  have hsec : ∀ τ, res' (sec τ) = τ := fun τ => Classical.choose_spec (hres'_surj τ)
  let ψ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) →*
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) :=
    { toFun := fun τ => ρ (sec τ)
      map_one' := (hwd _ _ ((hsec 1).trans (map_one res').symm)).trans (map_one ρ)
      map_mul' := fun τ τ' => (hwd _ _ (by
        calc res' (sec (τ * τ')) = τ * τ' := hsec (τ * τ')
          _ = res' (sec τ) * res' (sec τ') := (congrArg₂ (· * ·) (hsec τ) (hsec τ')).symm
          _ = res' (sec τ * sec τ') := (map_mul res' (sec τ) (sec τ')).symm)).trans
        (map_mul ρ (sec τ) (sec τ')) }
  have hψ_res : ∀ σ : ↥(SSGRoute.decomp k A), ψ (res' σ) = ρ σ := fun σ =>
    hwd _ _ (hsec (res' σ))
  have hψ_inj : Function.Injective ψ := by
    intro τ τ' h
    have h1 : ρ (sec τ) = ρ (sec τ') := h
    have h2 : ρ ((sec τ)⁻¹ * (sec τ')) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    rw [hker_iff] at h2
    have h3 : res' (sec τ) = res' (sec τ') := by
      rw [map_mul, map_inv] at h2
      have h5 : res' (sec τ') = res' (sec τ) := by
        rw [← mul_inv_cancel_left (res' (sec τ)) (res' (sec τ')), h2, mul_one]
      exact h5.symm
    exact (hsec τ).symm.trans (h3.trans (hsec τ'))
  have hψ_surj : Function.Surjective ψ := by
    intro γ
    obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥(decompField k Ω A))
      (K₁ := ↥(henselOverDecomp k Ω K A)) (E := Ω) γ
    refine ⟨res' (toGal.symm g), ?_⟩
    rw [hψ_res]
    show rn (toGal (toGal.symm g)) = γ
    rw [MulEquiv.apply_symm_apply]
    exact hg
  refine ⟨MulEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩, ?_⟩
  intro τ x
  show ((ψ τ) ⟨(x : Ω), le_henselField k Ω K A x.2⟩ : Ω) = _
  show ((ρ (sec τ)) ⟨(x : Ω), le_henselField k Ω K A x.2⟩ : Ω) = _
  rw [rho_apply]
  have hspec' : ((sec τ : Ω ≃ₐ[k] Ω) (x : Ω) : Ω) = ((τ : K ≃ₐ[k] K) x : Ω) := by
    have h3 := AlgEquiv.restrictNormalHom_apply K (sec τ : Ω ≃ₐ[k] Ω) x
    have h4 : ((SSGRoute.res k K (sec τ : Ω ≃ₐ[k] Ω)) x : Ω) = ((τ : K ≃ₐ[k] K) x : Ω) :=
      congrArg (fun z : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) =>
        ((z : K ≃ₐ[k] K) x : Ω)) (hsec τ)
    rw [← h3]
    exact h4
  rw [hspec']

end

end Work.SSGRoute.E1aClean
