import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq
import Submission.NK.GlobalCFT.Place
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the inert cyclic level with a free Galois orbit

These are the field-theoretic pieces of
`Work.SSGRoute.E7cOmega.exists_inertCyclicLevel_freeOrbit`.  They are collected in this module so
that they can be proved without importing the (heavy) Grünwald descent machinery:

* `smul_comap_valuationSubringAtPrime` — the trace on `K` of `σ • A` is `σ|_K • (A ∩ K)`;
* `exists_algEquiv_restrict_eq` — every `ℚ`-automorphism of `K` lifts to a normal extension `Λ`;
* `mem_of_isGalois_restrictNormal` — a level which is Galois over `ℚ` is stable under `Gal(Λ/ℚ)`;
* `not_isGalois_of_algEquiv` — `IsGalois ℚ` transports along a `K`-algebra isomorphism;
* `conjK`, `conjK_smul_place` — the `K`-linear conjugate of a `K`-automorphism by a
  `ℚ`-automorphism restricting to `τ` on `K`, and its action on places;
* `not_isGalois_of_conjDecomp` — the free-orbit argument: a level whose decomposition-group
  character is trivial at `A₂` but not at `σ • A₂` cannot be Galois over `ℚ`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped NumberField Pointwise

namespace Work.SSGRoute.E7cOmega

/-! ## The Galois action on places -/

/-- **`Place.ringOfIntegersEquiv` is `galRestrict`**, as ring homomorphisms. -/
theorem ringOfIntegersEquiv_eq_galRestrict' {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    (NK.GlobalCFT.Place.ringOfIntegersEquiv σ : 𝓞 L →+* 𝓞 L) =
      (galRestrict (𝓞 k) k L (𝓞 L) σ : 𝓞 L →+* 𝓞 L) := by
  ext x
  change algebraMap (𝓞 L) L (NK.GlobalCFT.Place.ringOfIntegersEquiv σ x) =
    algebraMap (𝓞 L) L (galRestrict (𝓞 k) k L (𝓞 L) σ x)
  rw [algebraMap_galRestrict_apply]
  rfl

/-- **The Galois action on places, in valuation-ring form, over `K`.**  If `A` is a place of `Λ`
above the prime `𝔭` of `K` and `σ : Λ ≃ₐ[ℚ] Λ`, then `σ • A` lies above the conjugate prime
`(σ|_K) • 𝔭` of `K`. -/
theorem smul_comap_valuationSubringAtPrime (K Λ : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Field Λ] [Algebra K Λ] [Algebra ℚ Λ]
    [IsScalarTower ℚ K Λ] (A : ValuationSubring Λ) (σ : Λ ≃ₐ[ℚ] Λ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hA : A.comap (algebraMap K Λ) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭) :
    (σ • A).comap (algebraMap K Λ) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
        (NK.GlobalCFT.Place.smulHeightOneSpectrum (AlgEquiv.restrictNormalHom (K₁ := Λ) K σ) 𝔭) := by
  haveI : Normal ℚ K := inferInstance
  rw [NK.Reconstruct.comap_smul_eq_restrictNormalHom_smul' (F := ℚ) (E := K) (K := Λ) A σ, hA]
  exact Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict 𝔭
    (NK.GlobalCFT.Place.smulHeightOneSpectrum
      (AlgEquiv.restrictNormalHom (K₁ := Λ) K σ) 𝔭)
    (AlgEquiv.restrictNormalHom (K₁ := Λ) K σ)
    (by
      rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
      exact congrArg (fun f : 𝓞 K →+* 𝓞 K => Ideal.map f 𝔭.asIdeal)
        (ringOfIntegersEquiv_eq_galRestrict' (k := ℚ)
          (AlgEquiv.restrictNormalHom (K₁ := Λ) K σ)))

/-- **Every automorphism of `K` over `ℚ` lifts to a normal extension `Λ`.** -/
theorem exists_algEquiv_restrict_eq (K Λ : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Field Λ] [Algebra K Λ] [Algebra ℚ Λ]
    [IsScalarTower ℚ K Λ] [Normal ℚ Λ] (τ : K ≃ₐ[ℚ] K) :
    ∃ σ : Λ ≃ₐ[ℚ] Λ, ∀ x : K, σ (algebraMap K Λ x) = algebraMap K Λ (τ x) :=
  ⟨τ.liftNormal Λ, fun x => τ.liftNormal_commutes Λ x⟩

/-! ## Stability of a Galois level under the full Galois group -/

/-- **A level which is Galois over `ℚ` is stable under the full `ℚ`-Galois group.** -/
theorem mem_of_isGalois_restrictNormal (K Λ : Type) [Field K] [Algebra ℚ K] [Field Λ]
    [Algebra K Λ] [Algebra ℚ Λ] [IsScalarTower ℚ K Λ] (M : IntermediateField K Λ)
    (h : IsGalois ℚ ↥M) (σ : Λ ≃ₐ[ℚ] Λ) : ∀ x ∈ M, σ⁻¹ x ∈ M := by
  haveI : Normal ℚ ↥M := h.to_normal
  intro x hx
  have h2 : (algebraMap ↥M Λ ((σ⁻¹).restrictNormal ↥M (⟨x, hx⟩ : ↥M)) : Λ) = σ⁻¹ x :=
    AlgEquiv.restrictNormal_commutes (σ⁻¹) ↥M (⟨x, hx⟩ : ↥M)
  rw [← h2]
  exact ((σ⁻¹).restrictNormal ↥M (⟨x, hx⟩ : ↥M)).2

/-- **`IsGalois` over `ℚ` transports along a `K`-algebra isomorphism.** -/
theorem not_isGalois_of_algEquiv (K A B : Type) [Field K] [Algebra ℚ K] [Field A] [Field B]
    [Algebra K A] [Algebra K B] [Algebra ℚ A] [Algebra ℚ B]
    (hA : IsScalarTower ℚ K A) (hB : IsScalarTower ℚ K B)
    (e : A ≃ₐ[K] B) (h : ¬ IsGalois ℚ A) : ¬ IsGalois ℚ B := by
  haveI := hA
  haveI := hB
  intro hgal
  exact h ((AlgEquiv.restrictScalars (R := ℚ) (S := K) e).transfer_galois.mpr hgal)

/-! ## The `K`-linear conjugate `σ g σ⁻¹` -/

/-- **A `ℚ`-automorphism of `Λ` inverts its own action on places.** -/
theorem inv_smul_smul_place (Λ : Type) [Field Λ] [Algebra ℚ Λ] (σ : Λ ≃ₐ[ℚ] Λ)
    (B : ValuationSubring Λ) : σ⁻¹ • (σ • B) = B := by
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  show σ⁻¹ ((σ⁻¹)⁻¹ x) ∈ B ↔ x ∈ B
  rw [show (σ⁻¹ : Λ ≃ₐ[ℚ] Λ) ((σ⁻¹)⁻¹ x) = x from AlgEquiv.symm_apply_apply σ x]

/-- **The `K`-linear conjugate of a `K`-linear automorphism by a `ℚ`-linear one** which restricts
to `τ` on `K`: the automorphism with underlying map `σ g σ⁻¹`. -/
noncomputable def conjK (K Λ : Type) [Field K] [Algebra ℚ K] [Field Λ] [Algebra K Λ] [Algebra ℚ Λ]
    [IsScalarTower ℚ K Λ] (σ : Λ ≃ₐ[ℚ] Λ) (τ : K ≃ₐ[ℚ] K)
    (hσ : ∀ x : K, σ (algebraMap K Λ x) = algebraMap K Λ (τ x)) (g : Λ ≃ₐ[K] Λ) :
    Λ ≃ₐ[K] Λ :=
  { (σ * (AlgEquiv.restrictScalars (R := ℚ) (S := K) g) * σ⁻¹).toRingEquiv with
    commutes' := fun x => by
      have h1 : σ⁻¹ (algebraMap K Λ x) = algebraMap K Λ (τ⁻¹ x) := by
        refine σ.injective ?_
        rw [hσ (τ⁻¹ x), show τ (τ⁻¹ x) = x from AlgEquiv.apply_symm_apply τ x]
        exact AlgEquiv.apply_symm_apply σ (algebraMap K Λ x)
      have h2 : (σ * (AlgEquiv.restrictScalars (R := ℚ) (S := K) g) * σ⁻¹)
          (algebraMap K Λ x) = algebraMap K Λ x := by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.coe_restrictScalars, h1,
          g.commutes (τ⁻¹ x), hσ (τ⁻¹ x),
          show τ (τ⁻¹ x) = x from AlgEquiv.apply_symm_apply τ x]
      exact h2 }

/-- **The underlying map of `conjK`.** -/
theorem conjK_apply (K Λ : Type) [Field K] [Algebra ℚ K] [Field Λ] [Algebra K Λ] [Algebra ℚ Λ]
    [IsScalarTower ℚ K Λ] (σ : Λ ≃ₐ[ℚ] Λ) (τ : K ≃ₐ[ℚ] K)
    (hσ : ∀ x : K, σ (algebraMap K Λ x) = algebraMap K Λ (τ x)) (g : Λ ≃ₐ[K] Λ) (y : Λ) :
    conjK K Λ σ τ hσ g y = σ (g (σ⁻¹ y)) := by
  show (σ * (AlgEquiv.restrictScalars (R := ℚ) (S := K) g) * σ⁻¹) y = σ (g (σ⁻¹ y))
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.coe_restrictScalars]

/-- **The `K`-linear conjugate acts by conjugation on places.** -/
theorem conjK_smul_place (K Λ : Type) [Field K] [Algebra ℚ K] [Field Λ] [Algebra K Λ] [Algebra ℚ Λ]
    [IsScalarTower ℚ K Λ] (σ : Λ ≃ₐ[ℚ] Λ) (τ : K ≃ₐ[ℚ] K)
    (hσ : ∀ x : K, σ (algebraMap K Λ x) = algebraMap K Λ (τ x)) (g : Λ ≃ₐ[K] Λ)
    (B : ValuationSubring Λ) :
    conjK K Λ σ τ hσ g • B = σ • (g • (σ⁻¹ • B)) := by
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, hb, hbx⟩
    have hbx' : conjK K Λ σ τ hσ g b = x := hbx
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    refine ⟨g (σ⁻¹ b),
      ValuationSubring.smul_mem_pointwise_smul g (σ⁻¹ b) (σ⁻¹ • B)
        (ValuationSubring.smul_mem_pointwise_smul σ⁻¹ b B hb), ?_⟩
    rw [AlgEquiv.smul_def, ← hbx', conjK_apply]
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨t, ht, hgt⟩ :=
      (ValuationSubring.mem_smul_pointwise_iff_exists g s (σ⁻¹ • B)).mp hs
    obtain ⟨u, hu, hσu⟩ :=
      (ValuationSubring.mem_smul_pointwise_iff_exists σ⁻¹ t B).mp ht
    have hσu' : σ⁻¹ u = t := hσu
    have hgt' : g t = s := hgt
    have hsx' : σ s = x := hsx
    refine ⟨u, hu, ?_⟩
    rw [AlgEquiv.smul_def, conjK_apply, hσu', hgt', hsx']

/-! ## The free-orbit argument -/

/-- **A level which is inert at `σ • A₂` but splits at `A₂` is not Galois over `ℚ`.**

`η` is a character on `Gal(Λ/K)` whose zero set is `M.fixingSubgroup` (i.e. `M` is the fixed field
of `ker η`), which vanishes on the decomposition group of `A₂`, but does not vanish on some element
`h₀` of the decomposition group of `σ • A₂`, where `σ` is a `ℚ`-automorphism of `Λ` restricting to
`τ` on `K`.  Then `σ⁻¹ h₀ σ` is a `K`-automorphism of `Λ` lying in the decomposition group of
`A₂`, hence fixes `M`; if `M/ℚ` were Galois then `σ⁻¹ x ∈ M` for `x ∈ M`, so `h₀` would fix `M`
as well, contradicting `η h₀ ≠ 0`. -/
theorem not_isGalois_of_conjDecomp (K Λ : Type) [Field K] [Algebra ℚ K] [Field Λ] [Algebra K Λ]
    [Algebra ℚ Λ] [IsScalarTower ℚ K Λ] (R : Type) [Zero R]
    (M : IntermediateField K Λ) (η : (Λ ≃ₐ[K] Λ) → R)
    (hfix : ∀ σ : Λ ≃ₐ[K] Λ, σ ∈ M.fixingSubgroup ↔ η σ = 0)
    (A₂ : ValuationSubring Λ)
    (hsplit : ∀ σ : Λ ≃ₐ[K] Λ, σ ∈ MulAction.stabilizer (Λ ≃ₐ[K] Λ) A₂ → η σ = 0)
    (σ : Λ ≃ₐ[ℚ] Λ) (τ : K ≃ₐ[ℚ] K)
    (hσ : ∀ x : K, σ (algebraMap K Λ x) = algebraMap K Λ (τ x))
    (h₀ : Λ ≃ₐ[K] Λ) (hh₀ : h₀ ∈ MulAction.stabilizer (Λ ≃ₐ[K] Λ) (σ • A₂))
    (hne : η h₀ ≠ 0)
    (hstab : IsGalois ℚ ↥M → ∀ x ∈ M, σ⁻¹ x ∈ M) :
    ¬ IsGalois ℚ ↥M := by
  have hσinv : ∀ x : K, σ⁻¹ (algebraMap K Λ x) = algebraMap K Λ (τ⁻¹ x) := by
    intro x
    refine σ.injective ?_
    rw [hσ (τ⁻¹ x), show τ (τ⁻¹ x) = x from AlgEquiv.apply_symm_apply τ x]
    exact AlgEquiv.apply_symm_apply σ (algebraMap K Λ x)
  have hgmem : conjK K Λ σ⁻¹ τ⁻¹ hσinv h₀ ∈ MulAction.stabilizer (Λ ≃ₐ[K] Λ) A₂ := by
    rw [MulAction.mem_stabilizer_iff]
    rw [conjK_smul_place K Λ σ⁻¹ τ⁻¹ hσinv h₀ A₂,
      show ((σ⁻¹ : Λ ≃ₐ[ℚ] Λ))⁻¹ • A₂ = σ • A₂ from rfl,
      MulAction.mem_stabilizer_iff.mp hh₀]
    exact inv_smul_smul_place Λ σ A₂
  have hg0 : η (conjK K Λ σ⁻¹ τ⁻¹ hσinv h₀) = 0 := hsplit _ hgmem
  have hgfix : conjK K Λ σ⁻¹ τ⁻¹ hσinv h₀ ∈ M.fixingSubgroup := (hfix _).mpr hg0
  intro hMgalQ
  have hstab' := hstab hMgalQ
  have hh₀fix : h₀ ∈ M.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hgfix ⊢
    intro x hx
    have hx' : σ⁻¹ x ∈ M := hstab' x hx
    have hconjy : conjK K Λ σ⁻¹ τ⁻¹ hσinv h₀ (σ⁻¹ x) = σ⁻¹ (h₀ x) := by
      rw [conjK_apply,
        show ((σ⁻¹ : Λ ≃ₐ[ℚ] Λ))⁻¹ (σ⁻¹ x) = x from AlgEquiv.apply_symm_apply σ x]
    calc h₀ x = σ (σ⁻¹ (h₀ x)) := (AlgEquiv.apply_symm_apply σ (h₀ x)).symm
      _ = σ (conjK K Λ σ⁻¹ τ⁻¹ hσinv h₀ (σ⁻¹ x)) := by rw [hconjy]
      _ = σ (σ⁻¹ x) := by rw [hgfix (σ⁻¹ x) hx']
      _ = x := AlgEquiv.apply_symm_apply σ x
  exact hne ((hfix h₀).mp hh₀fix)

/-! ## End of file -/

end Work.SSGRoute.E7cOmega
