import Mathlib
import Submission.NK.Reconstruct.exists_tauStar
import Submission.NK.Reconstruct.tauStarDef
import Submission.NK.Reconstruct.exists_ringEquiv_extends

/-!
# The conjugation action of `Gal(L/ℚ)` on `Γ_L`

`NK.Reconstruct.tauStar L ℓ θ hθ` is Shimizu's outer action on the ℓ-adic abelianisation
`Γ_L = NK.Reconstruct.Gamma ↥L Ω ℓ` of a ring automorphism `θ` of the separable closure `Ω`
which preserves the finite level `L` setwise.  Arithmetically it depends only on `θ|_L`; the
purpose of this file is to make that precise and hence to produce the *group action*

  `Gal(L/ℚ) →* (Γ_L ≃* Γ_L)`,  `τ ↦ τ^*`,

which Shimizu (arXiv:2009.10431, §4, Proposition 4f.3) writes `τ^*`.

## Contents

* `galToGamma_conj_eq` — `galToGamma` is invariant under conjugation by `Gal(Ω/L)` (it is a
  homomorphism into the commutative group `Γ_L`);
* `ringConjHom_mul`, `ringConjHom_eq_conj_of_fixes` — functoriality of the conjugation;
* `tauStar_mul`, `tauStar_eq_one_of_fixes`, `tauStar_eq_of_agree` — `τ^*` is multiplicative in
  `θ`, trivial on automorphisms fixing `L` pointwise, and therefore depends only on `θ|_L`;
* `exists_tauStarAction` — the resulting action of `Gal(L/ℚ)` on `Γ_L`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.NUV2.Transfer

open NK.Reconstruct

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
  (L : IntermediateField ℚ Ω) [NumberField ↥L] [IsGalois ↥L Ω]

/-! ## Generalities -/

/-- A homomorphism into a commutative group is invariant under conjugation. -/
theorem map_conj_eq {G M : Type*} [Group G] [CommGroup M] (f : G →* M) (u v : G) :
    f (u * v * u⁻¹) = f v := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/-- **Conjugation by an element of `Gal(Ω/L)` is invisible to `galToGamma`.** -/
theorem galToGamma_conj_eq (ℓ : ℕ) (α g : Gal(Ω/↥L)) :
    galToGamma (K := ↥L) (K' := Ω) ℓ (α * g * α⁻¹)
      = galToGamma (K := ↥L) (K' := Ω) ℓ g :=
  map_conj_eq _ α g

/-! ## Automorphisms fixing `L` pointwise -/

/-- A ring automorphism of `Ω` fixing `L` pointwise, viewed as an element of `Gal(Ω/L)`. -/
noncomputable def algEquivOfFixes (θ : Ω ≃+* Ω) (hfix : ∀ x : Ω, x ∈ L → θ x = x) :
    Gal(Ω/↥L) where
  toRingEquiv := θ
  commutes' := fun c => hfix (c : Ω) c.2

@[simp] theorem algEquivOfFixes_apply (θ : Ω ≃+* Ω)
    (hfix : ∀ x : Ω, x ∈ L → θ x = x) (x : Ω) :
    algEquivOfFixes L θ hfix x = θ x := rfl

theorem algEquivOfFixes_inv_apply (θ : Ω ≃+* Ω)
    (hfix : ∀ x : Ω, x ∈ L → θ x = x) (x : Ω) :
    (algEquivOfFixes L θ hfix)⁻¹ x = θ.symm x := rfl

/-- Fixing `L` pointwise implies preserving it. -/
theorem preserves_of_fixes (θ : Ω ≃+* Ω) (hfix : ∀ x : Ω, x ∈ L → θ x = x) :
    ∀ x : Ω, x ∈ L ↔ θ x ∈ L := by
  intro x
  constructor
  · intro hx
    rw [hfix x hx]
    exact hx
  · intro hx
    have h : θ x = x := θ.injective (hfix (θ x) hx)
    rw [← h]
    exact hx

/-- Conjugation by a ring automorphism fixing `L` pointwise is the conjugation by the
corresponding element of `Gal(Ω/L)`. -/
theorem ringConjHom_eq_conj_of_fixes (θ : Ω ≃+* Ω)
    (hθ : ∀ x : Ω, x ∈ L ↔ θ x ∈ L) (hfix : ∀ x : Ω, x ∈ L → θ x = x)
    (g : Gal(Ω/↥L)) :
    ringConjHom L θ hθ g
      = algEquivOfFixes L θ hfix * g * (algEquivOfFixes L θ hfix)⁻¹ := by
  ext x
  rw [ringConjHom_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, algEquivOfFixes_apply,
    algEquivOfFixes_inv_apply]

/-! ## Functoriality of the conjugation -/

/-- The proof that `θ` preserves `L` is irrelevant. -/
theorem ringConjHom_hθ_irrel (θ : Ω ≃+* Ω)
    (h h' : ∀ x : Ω, x ∈ L ↔ θ x ∈ L) (g : Gal(Ω/↥L)) :
    ringConjHom L θ h g = ringConjHom L θ h' g := by
  ext x
  rw [ringConjHom_apply]

/-- The composition of two automorphisms preserving `L` preserves `L`. -/
theorem preserves_mul (θ₁ θ₂ : Ω ≃+* Ω)
    (h₁ : ∀ x : Ω, x ∈ L ↔ θ₁ x ∈ L) (h₂ : ∀ x : Ω, x ∈ L ↔ θ₂ x ∈ L) :
    ∀ x : Ω, x ∈ L ↔ (θ₁ * θ₂) x ∈ L :=
  fun x => (h₂ x).trans (h₁ (θ₂ x))

/-- **Conjugation is functorial**: `(θ₁θ₂) g (θ₁θ₂)⁻¹ = θ₁ (θ₂ g θ₂⁻¹) θ₁⁻¹`. -/
theorem ringConjHom_mul (θ₁ θ₂ : Ω ≃+* Ω)
    (h₁ : ∀ x : Ω, x ∈ L ↔ θ₁ x ∈ L) (h₂ : ∀ x : Ω, x ∈ L ↔ θ₂ x ∈ L)
    (h₁₂ : ∀ x : Ω, x ∈ L ↔ (θ₁ * θ₂) x ∈ L) (g : Gal(Ω/↥L)) :
    ringConjHom L (θ₁ * θ₂) h₁₂ g = ringConjHom L θ₁ h₁ (ringConjHom L θ₂ h₂ g) := by
  have hs : ∀ x : Ω, (θ₁ * θ₂).symm x = θ₂.symm (θ₁.symm x) := by
    intro x
    change (θ₂.trans θ₁).symm x = θ₂.symm (θ₁.symm x)
    rw [RingEquiv.symm_trans_apply]
  ext x
  rw [ringConjHom_apply, ringConjHom_apply, ringConjHom_apply, hs x]
  rfl

/-! ## Dependence of `τ^*` on `θ` -/

/-- The proof that `θ` preserves `L` is irrelevant for `τ^*` as well. -/
theorem tauStar_hθ_irrel (ℓ : ℕ) [Fact ℓ.Prime] (θ : Ω ≃+* Ω)
    (h h' : ∀ x : Ω, x ∈ L ↔ θ x ∈ L) :
    tauStar L ℓ θ h = tauStar L ℓ θ h' :=
  congrArg (fun p => tauStar L ℓ θ p) (Subsingleton.elim h h')

/-- `τ^*` is functorial in `θ`. -/
theorem tauStar_congr (ℓ : ℕ) [Fact ℓ.Prime] {θ₁ θ₂ : Ω ≃+* Ω}
    (h₁ : ∀ x : Ω, x ∈ L ↔ θ₁ x ∈ L) (h₂ : ∀ x : Ω, x ∈ L ↔ θ₂ x ∈ L)
    (heq : θ₁ = θ₂) : tauStar L ℓ θ₁ h₁ = tauStar L ℓ θ₂ h₂ := by
  subst heq
  exact tauStar_hθ_irrel L ℓ _ h₁ h₂

/-- **`τ^*` is multiplicative in `θ`.** -/
theorem tauStar_mul (ℓ : ℕ) [Fact ℓ.Prime] (θ₁ θ₂ : Ω ≃+* Ω)
    (h₁ : ∀ x : Ω, x ∈ L ↔ θ₁ x ∈ L) (h₂ : ∀ x : Ω, x ∈ L ↔ θ₂ x ∈ L)
    (h₁₂ : ∀ x : Ω, x ∈ L ↔ (θ₁ * θ₂) x ∈ L) :
    tauStar L ℓ (θ₁ * θ₂) h₁₂ = tauStar L ℓ θ₁ h₁ * tauStar L ℓ θ₂ h₂ := by
  refine MulEquiv.ext (fun x => ?_)
  obtain ⟨g, rfl⟩ := galToGamma_surjective (K := ↥L) (K' := Ω) ℓ x
  change tauStar L ℓ (θ₁ * θ₂) h₁₂ (galToGamma (K := ↥L) (K' := Ω) ℓ g)
      = tauStar L ℓ θ₁ h₁ (tauStar L ℓ θ₂ h₂ (galToGamma (K := ↥L) (K' := Ω) ℓ g))
  have e₀ : tauStar L ℓ (θ₁ * θ₂) h₁₂ (galToGamma (K := ↥L) (K' := Ω) ℓ g)
      = galToGamma (K := ↥L) (K' := Ω) ℓ (ringConjHom L (θ₁ * θ₂) h₁₂ g) :=
    tauStar_galToGamma L ℓ (θ₁ * θ₂) h₁₂ g
  have e₁ : tauStar L ℓ θ₂ h₂ (galToGamma (K := ↥L) (K' := Ω) ℓ g)
      = galToGamma (K := ↥L) (K' := Ω) ℓ (ringConjHom L θ₂ h₂ g) :=
    tauStar_galToGamma L ℓ θ₂ h₂ g
  have e₂ : tauStar L ℓ θ₁ h₁ (galToGamma (K := ↥L) (K' := Ω) ℓ (ringConjHom L θ₂ h₂ g))
      = galToGamma (K := ↥L) (K' := Ω) ℓ (ringConjHom L θ₁ h₁ (ringConjHom L θ₂ h₂ g)) :=
    tauStar_galToGamma L ℓ θ₁ h₁ (ringConjHom L θ₂ h₂ g)
  rw [e₀, e₁, e₂, ringConjHom_mul L θ₁ θ₂ h₁ h₂ h₁₂ g]

/-- **An automorphism fixing `L` pointwise acts trivially on `Γ_L`.** -/
theorem tauStar_eq_one_of_fixes (ℓ : ℕ) [Fact ℓ.Prime] (θ : Ω ≃+* Ω)
    (hθ : ∀ x : Ω, x ∈ L ↔ θ x ∈ L) (hfix : ∀ x : Ω, x ∈ L → θ x = x) :
    tauStar L ℓ θ hθ = 1 := by
  refine MulEquiv.ext (fun x => ?_)
  obtain ⟨g, rfl⟩ := galToGamma_surjective (K := ↥L) (K' := Ω) ℓ x
  have e₀ : tauStar L ℓ θ hθ (galToGamma (K := ↥L) (K' := Ω) ℓ g)
      = galToGamma (K := ↥L) (K' := Ω) ℓ (ringConjHom L θ hθ g) :=
    tauStar_galToGamma L ℓ θ hθ g
  have e₁ : (1 : Gamma ↥L Ω ℓ ≃* Gamma ↥L Ω ℓ) (galToGamma (K := ↥L) (K' := Ω) ℓ g)
      = galToGamma (K := ↥L) (K' := Ω) ℓ g := rfl
  rw [e₀, e₁, ringConjHom_eq_conj_of_fixes L θ hθ hfix g, galToGamma_conj_eq L ℓ _ g]

/-- **`τ^*` depends only on `θ|_L`.** -/
theorem tauStar_eq_of_agree (ℓ : ℕ) [Fact ℓ.Prime] (θ₁ θ₂ : Ω ≃+* Ω)
    (h₁ : ∀ x : Ω, x ∈ L ↔ θ₁ x ∈ L) (h₂ : ∀ x : Ω, x ∈ L ↔ θ₂ x ∈ L)
    (hagree : ∀ x : ↥L, θ₁ (x : Ω) = θ₂ (x : Ω)) :
    tauStar L ℓ θ₁ h₁ = tauStar L ℓ θ₂ h₂ := by
  have hγfix : ∀ x : Ω, x ∈ L → (θ₂.symm.trans θ₁) x = x := by
    intro x hx
    have hmem : θ₂.symm x ∈ L :=
      (h₂ (θ₂.symm x)).mpr (by rw [RingEquiv.apply_symm_apply]; exact hx)
    have h1 : θ₁ ((⟨θ₂.symm x, hmem⟩ : ↥L) : Ω) = θ₂ ((⟨θ₂.symm x, hmem⟩ : ↥L) : Ω) :=
      hagree ⟨θ₂.symm x, hmem⟩
    have h2 : θ₂ ((⟨θ₂.symm x, hmem⟩ : ↥L) : Ω) = x := RingEquiv.apply_symm_apply θ₂ x
    calc (θ₂.symm.trans θ₁) x = θ₁ (θ₂.symm x) := RingEquiv.trans_apply _ _ _
      _ = θ₁ ((⟨θ₂.symm x, hmem⟩ : ↥L) : Ω) := rfl
      _ = θ₂ ((⟨θ₂.symm x, hmem⟩ : ↥L) : Ω) := h1
      _ = x := h2
  have hγpres : ∀ x : Ω, x ∈ L ↔ (θ₂.symm.trans θ₁) x ∈ L :=
    preserves_of_fixes L _ hγfix
  have hγ1 : tauStar L ℓ (θ₂.symm.trans θ₁) hγpres = 1 :=
    tauStar_eq_one_of_fixes L ℓ _ hγpres hγfix
  have hpres : ∀ x : Ω, x ∈ L ↔ ((θ₂.symm.trans θ₁) * θ₂) x ∈ L :=
    preserves_mul L (θ₂.symm.trans θ₁) θ₂ hγpres h₂
  have hprod : θ₁ = (θ₂.symm.trans θ₁) * θ₂ := by
    ext x
    change θ₁ x = (θ₂.symm.trans θ₁) (θ₂ x)
    rw [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  calc tauStar L ℓ θ₁ h₁
      = tauStar L ℓ ((θ₂.symm.trans θ₁) * θ₂) hpres := tauStar_congr L ℓ h₁ hpres hprod
    _ = tauStar L ℓ (θ₂.symm.trans θ₁) hγpres * tauStar L ℓ θ₂ h₂ :=
        tauStar_mul L ℓ (θ₂.symm.trans θ₁) θ₂ hγpres h₂ hpres
    _ = tauStar L ℓ θ₂ h₂ := by rw [hγ1, one_mul]

/-! ## The action of `Gal(L/ℚ)` on `Γ_L` -/

/-- **Extension of an automorphism of a finite level to the separable closure.**  This is
`NK.Reconstruct.exists_ringEquiv_extends` without the (unused) normality hypothesis on the level,
which avoids an instance diamond between `L.algebra'` and `DivisionRing.toRatAlgebra`. -/
theorem exists_ringEquiv_extends_of_isSepClosure (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (L : IntermediateField ℚ Ω) (τ : Gal(↥L/ℚ)) :
    ∃ θ : Ω ≃+* Ω, (∀ x : Ω, x ∈ L ↔ θ x ∈ L) ∧
      ∀ x : ↥L, θ (x : Ω) = ((τ x : ↥L) : Ω) := by
  haveI : Normal ℚ Ω := inferInstance
  let σ : Gal(Ω/ℚ) := τ.liftNormal Ω
  have hpt : ∀ x : ↥L, σ (x : Ω) = ((τ x : ↥L) : Ω) := fun x => τ.liftNormal_commutes Ω x
  refine ⟨σ.toRingEquiv, ?_, fun x => hpt x⟩
  intro x
  constructor
  · intro hx
    change σ x ∈ L
    rw [hpt ⟨x, hx⟩]
    exact (τ ⟨x, hx⟩).2
  · intro hx
    let y : ↥L := τ.symm ⟨σ x, hx⟩
    have hy : σ (y : Ω) = σ x := by rw [hpt y]; simp [y]
    have hyx : (y : Ω) = x := σ.injective hy
    rw [← hyx]
    exact y.2

theorem exists_tauStarAction (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (L : NK.Reconstruct.FrobLevel ℚ Ω) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ ρ : Gal(↥L.L/ℚ) →* (NK.Reconstruct.Gamma ↥L.L Ω ℓ ≃* NK.Reconstruct.Gamma ↥L.L Ω ℓ),
      ∀ (τ : Gal(↥L.L/ℚ)) (θ : Ω ≃+* Ω) (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L)
        (hθτ : ∀ x : ↥L.L, θ (x : Ω) = ((τ x : ↥L.L) : Ω)),
        ρ τ = NK.Reconstruct.tauStar L.L ℓ θ hθ := by
  classical
  have hex : ∀ τ : Gal(↥L.L/ℚ), ∃ θ : Ω ≃+* Ω,
      (∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L) ∧ ∀ x : ↥L.L, θ (x : Ω) = ((τ x : ↥L.L) : Ω) :=
    fun τ => exists_ringEquiv_extends_of_isSepClosure Ω L.L τ
  choose θe hθe hτe using hex
  let ρ : Gal(↥L.L/ℚ) →* (NK.Reconstruct.Gamma ↥L.L Ω ℓ ≃* NK.Reconstruct.Gamma ↥L.L Ω ℓ) :=
    { toFun := fun τ => tauStar L.L ℓ (θe τ) (hθe τ)
      map_one' := by
        refine tauStar_eq_one_of_fixes L.L ℓ (θe 1) (hθe 1) (fun x hx => ?_)
        have h := hτe 1 ⟨x, hx⟩
        simpa using h
      map_mul' := by
        intro τ₁ τ₂
        have hpres : ∀ x : Ω, x ∈ L.L ↔ ((θe τ₁) * (θe τ₂)) x ∈ L.L :=
          preserves_mul L.L _ _ (hθe τ₁) (hθe τ₂)
        have hagree : ∀ x : ↥L.L,
            ((θe τ₁) * (θe τ₂)) (x : Ω) = (θe (τ₁ * τ₂)) (x : Ω) := by
          intro x
          show (θe τ₁) ((θe τ₂) (x : Ω)) = (θe (τ₁ * τ₂)) (x : Ω)
          rw [hτe τ₂ x, hτe τ₁ (τ₂ x), hτe (τ₁ * τ₂) x, AlgEquiv.mul_apply]
        show tauStar L.L ℓ (θe (τ₁ * τ₂)) (hθe (τ₁ * τ₂))
            = tauStar L.L ℓ (θe τ₁) (hθe τ₁) * tauStar L.L ℓ (θe τ₂) (hθe τ₂)
        rw [← tauStar_eq_of_agree L.L ℓ ((θe τ₁) * (θe τ₂)) (θe (τ₁ * τ₂)) hpres
          (hθe (τ₁ * τ₂)) hagree]
        exact tauStar_mul L.L ℓ (θe τ₁) (θe τ₂) (hθe τ₁) (hθe τ₂) hpres }
  refine ⟨ρ, ?_⟩
  intro τ θ hθ hθτ
  show tauStar L.L ℓ (θe τ) (hθe τ) = tauStar L.L ℓ θ hθ
  exact tauStar_eq_of_agree L.L ℓ (θe τ) θ (hθe τ) hθ
    (fun x => by rw [hτe τ x, hθτ x])

end NK.NUV2.Transfer
