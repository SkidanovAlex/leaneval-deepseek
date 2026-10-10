import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSG8Escape.artin_reduces_to_local_product
import Submission.Work.SSGRoute.GrunwaldEscapeCore.mem_localNormSubgroup_algebra_norm
import Submission.Work.SSGRoute.N2v2.exists_artinMap_with_decompLift
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos
import Submission.Work.SSGRoute.ZDataTwo.RealPlaceInvolution
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the `p = 2` orthogonality `orthogonality_L2K_trichotomy_two`

The form in which the orthogonality consumes the decomposition clause of an idèlic Artin map: the
trichotomy `horth₁` is stated for elements of `decomp k A ⊓ K.fixingSubgroup` (a subgroup of
`Gal(Ω/k)`), whereas the proved `N2v2.decompLift_of_artinMap` / `N2v2.exists_artinMap_with_decompLift`
produce the lift in `decomp (k := ↥K) A` (the stabiliser inside `Gal(Ω/↥K)`).  The two are related
by `toGkHom K : Gal(Ω/↥K) →* Gal(Ω/k)` (`Work.SSGRoute.toGkHom_mem_decomp`,
`Work.SSGRoute.toGkHom_fixingSubgroupEquiv`); this file records the transfer.
-/

namespace Work.SSGRoute.ZDataTwo

open Work.SSG8Escape

open NumberField IsDedekindDomain

/-- **The decomposition clause, in `decomp k A ⊓ K.fixingSubgroup`.**  If an idèlic Artin map `Φ` of
the finite abelian extension `E/↥K` sends the one-place idèles into the decomposition groups of the
places of `Ω` (in the `Gal(Ω/↥K)`-form, as produced by
`Work.SSGRoute.N2v2.exists_artinMap_with_decompLift`), then every such local factor has a lift in the
subgroup `decomp k A ⊓ K.fixingSubgroup` of `Gal(Ω/k)` — the form consumed by the trichotomy. -/
theorem localFactor_lift_fixingSubgroup {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E))
    (hΦ : ∀ (A : ValuationSubring Ω) (_hA : SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ x : (↥K)ˣ,
        ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x)))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (hAcomap : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (x : (↥K)ˣ) :
    ∃ σ : Ω ≃ₐ[k] Ω, ∃ hσ : σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E
          (Work.SSGRoute.gesGalKOfFixing K σ (Subgroup.mem_inf.mp hσ).2) =
        Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) x)) := by
  classical
  obtain ⟨σ₀, hσ₀, hσ₀res⟩ := hΦ A hA 𝔭 hAcomap x
  have hmem1 : Work.SSGRoute.toGkHom K σ₀ ∈ SSGRoute.decomp k A :=
    (Work.SSGRoute.toGkHom_mem_decomp K A σ₀).mpr hσ₀
  have hmem2 : Work.SSGRoute.toGkHom K σ₀ ∈ K.fixingSubgroup := by
    intro y
    show (Work.SSGRoute.toGkHom K σ₀) (y : Ω) = (y : Ω)
    rw [Work.SSGRoute.toGkHom_apply]
    exact AlgEquiv.commutes σ₀ y
  refine ⟨Work.SSGRoute.toGkHom K σ₀, Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩, ?_⟩
  have hcoe : Work.SSGRoute.gesGalKOfFixing K (Work.SSGRoute.toGkHom K σ₀) hmem2 = σ₀ := by
    have h1 : (IntermediateField.fixingSubgroupEquiv K).symm σ₀ =
        (⟨Work.SSGRoute.toGkHom K σ₀, hmem2⟩ : ↥(K.fixingSubgroup)) := by
      refine Subtype.ext ?_
      have h2 := Work.SSGRoute.toGkHom_fixingSubgroupEquiv K
        ((IntermediateField.fixingSubgroupEquiv K).symm σ₀)
      rw [MulEquiv.apply_symm_apply] at h2
      exact h2.symm
    rw [Work.SSGRoute.gesGalKOfFixing, ← h1, MulEquiv.apply_symm_apply]
  rw [hcoe]
  exact hσ₀res


/-! ## The `p = 2` diagonal of the local Kummer pairing -/

/-- **The `p = 2` diagonal.**  For a quadratic Kummer extension `L = K(α)`, `α ^ 2 = x`, the norm of
the Kummer root is `-x` (the product of the two conjugates `α` and `-α`), so `-x` lies in the local
norm subgroup at every finite place.  This is the `p = 2` companion of
`GrunwaldEscapeCore.mem_localNormSubgroup_of_kummerRoot`. -/
theorem localImageAt_neg_mem_localNormSubgroup_two
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ) (α : L) (hα : α ^ 2 = algebraMap K L (x : K))
    (hgen : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (hdeg : Module.finrank K L = 2)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.CFTLib.IdeleHasse.localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite 𝔭) (-x) ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite 𝔭) := by
  classical
  have hx0 : (x : K) ≠ 0 := x.ne_zero
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hα
    exact ((map_ne_zero (algebraMap K L)).mpr hx0) hα.symm
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hdeg
  -- an automorphism fixing `α` is the identity
  have hfix_of_fixα : ∀ g : L ≃ₐ[K] L, g α = α → g = 1 := by
    intro g hg
    have hginv : g⁻¹ α = α := by
      have h1 : g⁻¹ (g α) = g⁻¹ α := congrArg (fun z => g⁻¹ z) hg
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h1
      exact h1.symm
    have hpow : ∀ n : ℤ, (g ^ n) α = α := by
      intro n
      induction n using Int.induction_on with
      | zero => simp
      | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hg, ih]
      | pred n ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hginv, ih]
    have hall : ∀ y : L, g y = y := by
      have hsub : IntermediateField.adjoin K ({α} : Set L) ≤
          IntermediateField.fixedField (Subgroup.zpowers g) := by
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        refine (IntermediateField.mem_fixedField_iff (Subgroup.zpowers g) α).mpr ?_
        intro f hf
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hf
        rw [← hn]
        exact hpow n
      intro y
      have hymem : y ∈ IntermediateField.adjoin K ({α} : Set L) := by
        rw [hgen]; exact IntermediateField.mem_top
      refine (IntermediateField.mem_fixedField_iff (Subgroup.zpowers g) y).mp (hsub hymem) g ?_
      exact Subgroup.mem_zpowers g
    exact AlgEquiv.ext hall
  -- every automorphism sends `α` to `α` or to `-α`
  have hpm : ∀ g : L ≃ₐ[K] L, g α = α ∨ g α = -α := by
    intro g
    have h2 : (g α) ^ 2 = α ^ 2 := by
      rw [← map_pow, hα]
      exact AlgEquiv.commutes g (x : K)
    have h4 : (g α - α) * (g α + α) = (g α) ^ 2 - α ^ 2 := by ring
    have h5 : (g α - α) * (g α + α) = 0 := by rw [h4, h2, sub_self]
    rcases mul_eq_zero.mp h5 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  -- the nontrivial automorphism
  have htwo : 1 < Fintype.card (L ≃ₐ[K] L) := by
    rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨σ, hσne⟩ := Fintype.exists_ne_of_one_lt_card htwo (1 : L ≃ₐ[K] L)
  have hσmul : σ α = -α := by
    rcases hpm σ with h | h
    · exact absurd (hfix_of_fixα σ h) hσne
    · exact h
  -- the group is `{1, σ}`, and the product of the conjugates of `α` is `α * (-α) = -x`
  have hsub2 : ({1, σ} : Finset (L ≃ₐ[K] L)) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun g => ?_
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hpm g with hg | hg
    · exact Or.inl (hfix_of_fixα g hg)
    · refine Or.inr ?_
      have hσinv : σ⁻¹ α = -α := by
        have h1 : σ (-α) = α := by rw [map_neg, hσmul, neg_neg]
        conv_lhs => rw [← h1]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      have hfix : (g * σ⁻¹) α = α := by
        rw [AlgEquiv.mul_apply, hσinv, map_neg, hg, neg_neg]
      exact mul_inv_eq_one.mp (hfix_of_fixα (g * σ⁻¹) hfix)
  have hnorm : Algebra.norm K α = -(x : K) := by
    apply (algebraMap K L).injective
    rw [Algebra.norm_eq_prod_automorphisms K α, ← hsub2,
      Finset.prod_insert (by simpa [eq_comm] using hσne), Finset.prod_singleton, hσmul, map_neg, mul_neg,
      AlgEquiv.one_apply, ← pow_two, hα]
  have hη : Units.map (Algebra.norm K) (Units.mk0 α hα0) = -x := Units.ext hnorm
  rw [← hη]
  exact Work.SSGRoute.GrunwaldEscapeCore.mem_localNormSubgroup_algebra_norm 𝔭 (Units.mk0 α hα0)

/-! ## The `p = 2` symmetry of the local Kummer pairing -/

/-- Additivity of the `ZMod 2`-valued Kummer character in the group variable, at the level of a
field `K` with algebraic closure `Ω` (a form of `ZConstruction.kummerCharZMod_apply_mul` that does
not require the ambient intermediate-field structure). -/
theorem kummerCharZMod_apply_mul_two {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (b : Kˣ) (σ τ : Ω ≃ₐ[K] Ω) :
    Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ b (σ * τ) =
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ b σ +
        Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ b τ := by
  rw [Work.SSGRoute.kummerCharZMod_apply, Work.SSGRoute.kummerCharZMod_apply,
    Work.SSGRoute.kummerCharZMod_apply,
    Work.SSGRoute.kummerIdx_mul_apply 2 hζ b (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) 2 b)
      (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) 2 b) σ τ]

/-- Additivity of the `ZMod 2`-valued Kummer character in the element. -/
theorem kummerCharZMod_add_two {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (β β' : Kˣ) (σ : Ω ≃ₐ[K] Ω) :
    Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ (β * β') σ =
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ β σ +
        Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ β' σ := by
  rw [Work.SSGRoute.kummerCharZMod_apply, Work.SSGRoute.kummerCharZMod_apply,
    Work.SSGRoute.kummerCharZMod_apply]
  have hcd : (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) 2 β *
      Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) 2 β') ^ 2 =
      Units.map (algebraMap K Ω) (β * β') := by
    rw [mul_pow, Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) 2 β,
      Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) 2 β', ← map_mul]
  rw [Work.SSGRoute.kummerIdx_congr 2 hζ (β * β')
      (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) 2 (β * β')) hcd σ,
    Work.SSGRoute.kummerIdx_mul 2 hζ β β' (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) 2 β)
      (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) 2 β')
      (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) 2 β)
      (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) 2 β') hcd σ]

/-- **The `p = 2` symmetry of the local Kummer pairing.**  At a level `E` (over `K`) containing the
Kummer fields of `x`, `y` and `x * y`, and for a homomorphism `θ : Kˣ →* Gal(E/K)`, the `p = 2`
diagonal `χ_c (θ (-c)) = 0` implies `χ_y (θ x) + χ_x (θ y) = 0` — for `p = 2` the local Kummer
pairing is *symmetric*, which is the form in which the datum `ha` of the orthogonality is consumed.
The shuffle is `0 = β(xy,xy) = β(x,x) + β(x,y) + β(y,x) + β(y,y)` with `β(z,z) = χ_z(θ(-1))` (the
diagonal).  This is the `p = 2` companion of `GrunwaldEscapeCore.kummerCharZMod_antisymm`, whose
diagonal `χ_c(θ c) = 0` is false at `p = 2`. -/
theorem kummerCharZMod_symm_two_aux
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] [Normal K E]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 2)
    (θ : Kˣ →* (↥E ≃ₐ[K] ↥E))
    (hdiag : ∀ c : Kˣ, NK.LocalAnabelian.kummerField (p := 2) (K' := Ω) c ≤ E →
      ∀ τ : Ω ≃ₐ[K] Ω,
        AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E τ = θ (-c) →
        Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ c τ = 0)
    (x y : Kˣ)
    (hx : NK.LocalAnabelian.kummerField (p := 2) (K' := Ω) x ≤ E)
    (hy : NK.LocalAnabelian.kummerField (p := 2) (K' := Ω) y ≤ E)
    (hxy : NK.LocalAnabelian.kummerField (p := 2) (K' := Ω) (x * y) ≤ E)
    (τ σ : Ω ≃ₐ[K] Ω)
    (hτ : AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E τ = θ x)
    (hσ : AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E σ = θ y) :
    Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ y τ +
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ x σ = 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) Ω (θ (-1))
  have hmulx : (-x : Kˣ) = (-1 : Kˣ) * x := by ext; simp
  have hmuly : (-y : Kˣ) = (-1 : Kˣ) * y := by ext; simp
  have hmulxy : (-(x * y) : Kˣ) = (-1 : Kˣ) * (x * y) := by ext; simp
  have h1 : Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ x (ρ * τ) = 0 := by
    refine hdiag x hx (ρ * τ) ?_
    rw [hmulx, map_mul, hρ, hτ]
    exact (map_mul θ (-1) x).symm
  have h2 : Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ y (ρ * σ) = 0 := by
    refine hdiag y hy (ρ * σ) ?_
    rw [hmuly, map_mul, hρ, hσ]
    exact (map_mul θ (-1) y).symm
  have h3 : Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ (x * y)
      (ρ * τ * σ) = 0 := by
    refine hdiag (x * y) hxy (ρ * τ * σ) ?_
    rw [hmulxy, map_mul, map_mul, hρ, hτ, hσ, map_mul, map_mul]
    exact mul_assoc _ _ _
  have h1' : Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ x ρ +
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ x τ = 0 := by
    rw [← kummerCharZMod_apply_mul_two (K := K) (Ω := Ω) ζ hζ x ρ τ]
    exact h1
  have h2' : Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ y ρ +
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ y σ = 0 := by
    rw [← kummerCharZMod_apply_mul_two (K := K) (Ω := Ω) ζ hζ y ρ σ]
    exact h2
  have h3u : Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ (x * y)
      ((ρ * τ) * σ) = 0 := h3
  have h3' : Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ x ρ +
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ y ρ +
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ x τ +
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ y τ +
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ x σ +
      Work.SSGRoute.kummerCharZMod (K := K) (Ω := Ω) 2 (ζ := ζ) hζ y σ = 0 := by
    have h4 := kummerCharZMod_apply_mul_two (K := K) (Ω := Ω) ζ hζ (x * y) (ρ * τ) σ
    have h5 := kummerCharZMod_apply_mul_two (K := K) (Ω := Ω) ζ hζ (x * y) ρ τ
    have h6 := kummerCharZMod_add_two (K := K) (Ω := Ω) ζ hζ x y ρ
    have h7 := kummerCharZMod_add_two (K := K) (Ω := Ω) ζ hζ x y τ
    have h8 := kummerCharZMod_add_two (K := K) (Ω := Ω) ζ hζ x y σ
    linear_combination h3u - h4 - h5 - h6 - h7 - h8
  linear_combination h3' - h1' - h2'

/-! ## The archimedean input from `hapos` -/

/-- **The archimedean components of `a` are local norms, from `hapos`.**  `hapos` says that the
Kummer character of `a` kills every involution of `K.fixingSubgroup`; by the Artin–Schreier
dictionary (`ZDataTwo.exists_conjInv_kummerChar_eq_zero_iff`) this says that `a` is *not negative*
at any real place of `↥K`, i.e. that `a` is totally positive; then
`ArtinReciprocity.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos` gives the claim. -/
theorem hapos_arch_localNorm_aux
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (a : (↥K)ˣ)
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F] [NumberField ↥F]
    (hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) :
    ∀ w : NumberField.InfinitePlace ↥K,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) a ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
          (NK.GlobalCFT.Place.ofInfinite w) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hACK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- `a` is not negative at any real place
  have hnotneg : ∀ (w : NumberField.InfinitePlace ↥K), ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a := by
    intro w
    by_cases hw : w.IsReal
    · obtain ⟨c, hc2, hc1, hcdict⟩ :=
        Work.SSGRoute.ZDataTwo.exists_conjInv_kummerChar_eq_zero_iff (k := ↥K) (Ω := Ω)
          ζ hζ w hw
      have hc'mem : Work.SSGRoute.toGkHom K c ∈ K.fixingSubgroup := by
        intro y
        show (Work.SSGRoute.toGkHom K c) (y : Ω) = (y : Ω)
        rw [Work.SSGRoute.toGkHom_apply]
        exact AlgEquiv.commutes c y
      have hc'2 : (Work.SSGRoute.toGkHom K c) ^ 2 = 1 := by
        rw [← map_pow, hc2, map_one]
      have hges : Work.SSGRoute.gesGalKOfFixing K (Work.SSGRoute.toGkHom K c) hc'mem = c := by
        have h1 : (IntermediateField.fixingSubgroupEquiv K).symm c =
            (⟨Work.SSGRoute.toGkHom K c, hc'mem⟩ : ↥(K.fixingSubgroup)) := by
          refine Subtype.ext ?_
          have h2 := Work.SSGRoute.toGkHom_fixingSubgroupEquiv K
            ((IntermediateField.fixingSubgroupEquiv K).symm c)
          rw [MulEquiv.apply_symm_apply] at h2
          exact h2.symm
        rw [Work.SSGRoute.gesGalKOfFixing, ← h1, MulEquiv.apply_symm_apply]
      have hzero := hapos (Work.SSGRoute.toGkHom K c) hc'mem hc'2
      rw [hges] at hzero
      have hchar : Work.SSGRoute.kummerChar (K := ↥K) (Ω := Ω) ζ hζ a c = 0 := by
        rw [← Work.SSGRoute.ZDataTwo.kummerCharZMod_two_eq_kummerChar k Ω K ζ hζ a c]
        exact hzero
      exact (hcdict a).mp hchar
    · exact fun hneg => hw hneg.isReal
  -- total positivity
  have hpos : ∀ (w : NumberField.InfinitePlace ↥K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (algebraMap ↥K w.Completion ((a : ↥K))) := by
    intro w hw
    have h1 : ¬ (NumberField.InfinitePlace.embedding_of_isReal hw ((a : ↥K)) < 0) :=
      fun hlt => hnotneg w ⟨hw, hlt⟩
    have h2 : NumberField.InfinitePlace.embedding_of_isReal hw ((a : ↥K)) ≠ 0 := by
      simpa using (map_ne_zero (NumberField.InfinitePlace.embedding_of_isReal hw)) a.ne_zero
    have h3 : 0 < NumberField.InfinitePlace.embedding_of_isReal hw ((a : ↥K)) :=
      lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    simpa [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply] using h3
  intro w
  exact Work.SSGRoute.ZDataMup.ArtinReciprocity.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos
    (K := ↥K) (L := ↥F) a w hpos

theorem artinFixes_localFactors_two_aux
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F] [NumberField ↥F]
    (c : (↥K)ˣ) (hc : NK.LocalAnabelian.kummerField (p := 2) (K' := Ω) c ≤ F)
    (χ : (↥F ≃ₐ[↥K] ↥F) →* Multiplicative (ZMod 2))
    (hχ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χ (AlgEquiv.restrictNormalHom F σ) =
        Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c σ))
    (a : (↥K)ˣ) (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hLT : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) 𝔮)
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥F ≃ₐ[↥K] ↥F))
    (hΦprin : ∀ x : (↥K)ˣ, Φ (NK.GlobalCFT.Idele.principalIdele ↥K x) = 1)
    (hΦnorm : ∀ y : NK.GlobalCFT.Idele ↥F, Φ (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥F y) = 1)
    (harch : ∀ w : NumberField.InfinitePlace ↥K,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) a ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
          (NK.GlobalCFT.Place.ofInfinite w))
    (hTfix : (∏ 𝔭 ∈ T', χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a)))) = 1) :
    χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 := by
  classical
  -- `Ψ := χ ∘ Φ`
  set Ψ : NK.GlobalCFT.Idele ↥K →* Multiplicative (ZMod 2) := χ.comp Φ with hΨ
  have hΨapply : ∀ x : NK.GlobalCFT.Idele ↥K, Ψ x = χ (Φ x) := fun x => by rw [hΨ]; rfl
  have hprinΨ : ∀ x : (↥K)ˣ, Ψ (NK.GlobalCFT.Idele.principalIdele ↥K x) = 1 := by
    intro x; rw [hΨapply, hΦprin x, map_one]
  have hnormΨ : ∀ y : NK.GlobalCFT.Idele ↥F,
      Ψ (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥F y) = 1 := by
    intro y; rw [hΨapply, hΦnorm y, map_one]
  -- the idèle `y = ρ(a) · 𝔡⁻¹`
  set y : NK.GlobalCFT.Idele ↥K := NK.GlobalCFT.Idele.principalIdele ↥K a *
    (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))⁻¹ with hy
  -- every place outside `T'` has `y`-component a local norm
  have hYnorm : ∀ v : NK.GlobalCFT.Place ↥K,
      v ∉ T'.image (NK.GlobalCFT.Place.ofFinite (K := ↥K)) →
      y v ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F) v := by
    intro v hv
    rcases v with w | 𝔮
    · -- archimedean place
      have hfrac : (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
          (NK.GlobalCFT.Place.ofInfinite w) = 1 := rfl
      have hyv : y (NK.GlobalCFT.Place.ofInfinite w)
          = NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) a := by
        rw [hy, NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hfrac, inv_one,
          mul_one, Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt]
      rw [hyv]
      exact harch w
    · -- finite place outside `T'`: unramified, and the component is a local unit
      have h𝔮T : 𝔮 ∉ T' := fun h => hv (Finset.mem_image.mpr ⟨𝔮, h, rfl⟩)
      have hmem : y (NK.GlobalCFT.Place.ofFinite 𝔮)
          ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔮) := by
        rw [NK.NUV2.RouteB.RayModulus.mem_localUnits_iff_exp_eq_zero]
        rw [hy, NK.GlobalCFT.Idele.exp_mul, NK.NUV2.RouteB.RayModulus.exp_inv,
          NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun,
          Work.SSGRoute.tFreePart_count_eq_exp (K := ↥K) T' a h𝔮T]
        ring
      exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := ↥K) (L := ↥F)
        𝔮 (hLT 𝔮 h𝔮T) hmem
  -- the product formula
  have hPF := productFormula_of_mem_localNormSubgroup (K := ↥K) (F := ↥F)
    (A := Multiplicative (ZMod 2)) Ψ hprinΨ hnormΨ y
    (T'.image (NK.GlobalCFT.Place.ofFinite (K := ↥K))) hYnorm
  -- collapse the `cprod` over the image of the finite places
  have hImage : NK.CFTLib.IdeleHasse.cprod (fun a b : Multiplicative (ZMod 2) => mul_comm a b)
        (T'.image (NK.GlobalCFT.Place.ofFinite (K := ↥K)))
        (fun v => Ψ (NK.HassePrinciple.onePlace v (y v)))
      = NK.CFTLib.IdeleHasse.cprod (fun a b : Multiplicative (ZMod 2) => mul_comm a b) T'
        (fun 𝔭 => Ψ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (y (NK.GlobalCFT.Place.ofFinite 𝔭)))) :=
    cprod_image_ofFinite_place (K := ↥K) (fun a b : Multiplicative (ZMod 2) => mul_comm a b) T'
      (fun v => Ψ (NK.HassePrinciple.onePlace v (y v)))
  -- `y` at a prime of `T'` is the local image of `a`
  have hyT : ∀ 𝔭 ∈ T', y (NK.GlobalCFT.Place.ofFinite 𝔭)
      = NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a := by
    intro 𝔭 h𝔭
    have hzero : (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
        (NK.GlobalCFT.Place.ofFinite 𝔭) = 1 := by
      rw [Work.SSGRoute.fracIdele_apply_ofFinite,
        Work.SSGRoute.tFreePart_count_eq_zero (K := ↥K) T' a h𝔭, zpow_zero]
    rw [hy, NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hzero, inv_one,
      mul_one, Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt]
  -- the local product is the hypothesis `hTfix`
  have hT'prod : NK.CFTLib.IdeleHasse.cprod (fun a b : Multiplicative (ZMod 2) => mul_comm a b) T'
        (fun 𝔭 => Ψ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (y (NK.GlobalCFT.Place.ofFinite 𝔭))))
      = ∏ 𝔭 ∈ T', χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))) := by
    rw [cprod_eq_finset_prod]
    exact Finset.prod_congr rfl (fun 𝔭 h𝔭 => by rw [hyT 𝔭 h𝔭, hΨapply])
  -- `Ψ y = (Ψ 𝔡)⁻¹`
  have hyval : Ψ y
      = (Ψ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)))⁻¹ := by
    rw [hy, map_mul, map_inv, hprinΨ a, one_mul]
  have hkey : (Ψ (NK.NUV2.RouteB.RayModulus.fracIdele
      (Work.SSGRoute.tFreePart (K := ↥K) T' a)))⁻¹ = 1 := by
    rw [← hyval, hPF, hImage, hT'prod, hTfix]
  have hPsi : Ψ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      = 1 := inv_eq_one.mp hkey
  rw [show χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)))
      = Ψ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      from (hΨapply _).symm, hPsi]


/-- **The involution condition implies total positivity.**  If a Kummer character (at `p = 2`)
vanishes at every involution of `K.fixingSubgroup`, then the corresponding element is not negative at
any real place of `↥K`.  This is the Archimedean–Schreier dictionary
(`ZDataTwo.exists_conjInv_kummerChar_eq_zero_iff` at the level `↥K`, transported along
`toGkHom K` and `kummerCharZMod_two_eq_kummerChar`). -/
theorem not_isNegAt_of_involution_condition
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ)
    (h : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) :
    ∀ w : NumberField.InfinitePlace ↥K, ¬ Work.SSGRoute.ZDataTwo.IsNegAt w b := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hACK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  intro w
  by_cases hw : w.IsReal
  · obtain ⟨c, hc2, hc1, hcdict⟩ :=
      Work.SSGRoute.ZDataTwo.exists_conjInv_kummerChar_eq_zero_iff (k := ↥K) (Ω := Ω)
        ζ hζ w hw
    have hc'mem : Work.SSGRoute.toGkHom K c ∈ K.fixingSubgroup := by
      intro y
      show (Work.SSGRoute.toGkHom K c) (y : Ω) = (y : Ω)
      rw [Work.SSGRoute.toGkHom_apply]
      exact AlgEquiv.commutes c y
    have hc'2 : (Work.SSGRoute.toGkHom K c) ^ 2 = 1 := by
      rw [← map_pow, hc2, map_one]
    have hges : Work.SSGRoute.gesGalKOfFixing K (Work.SSGRoute.toGkHom K c) hc'mem = c := by
      have h1 : (IntermediateField.fixingSubgroupEquiv K).symm c =
          (⟨Work.SSGRoute.toGkHom K c, hc'mem⟩ : ↥(K.fixingSubgroup)) := by
        refine Subtype.ext ?_
        have h2 := Work.SSGRoute.toGkHom_fixingSubgroupEquiv K
          ((IntermediateField.fixingSubgroupEquiv K).symm c)
        rw [MulEquiv.apply_symm_apply] at h2
        exact h2.symm
      rw [Work.SSGRoute.gesGalKOfFixing, ← h1, MulEquiv.apply_symm_apply]
    have hzero := h (Work.SSGRoute.toGkHom K c) hc'mem hc'2
    rw [hges] at hzero
    have hchar : Work.SSGRoute.kummerChar (K := ↥K) (Ω := Ω) ζ hζ b c = 0 := by
      rw [← Work.SSGRoute.ZDataTwo.kummerCharZMod_two_eq_kummerChar k Ω K ζ hζ b c]
      exact hzero
    exact (hcdict b).mp hchar
  · exact fun hneg => hw hneg.isReal

end Work.SSGRoute.ZDataTwo
