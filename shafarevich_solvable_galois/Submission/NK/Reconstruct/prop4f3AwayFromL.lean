import Submission.NK.Reconstruct.exists_tau_gammaHausMk_eq_of_isFrobElementAt
import Submission.NK.Reconstruct.assemblyGen
import Submission.NK.ReconstructField.primeBelowNat_levelPrimeMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shimizu's Proposition 4f.3 with the Frobenius correspondence restricted to primes away from `ℓ`

`NK.Reconstruct.prop4f3` takes as a hypothesis the Frobenius correspondence

  `hb : IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ → σbar (galToGamma g₁) = galToGamma g₂`

*in the full ℓ-adic abelianisation* `Γ`, for **every** prime `𝔭`.  That statement is false as soon
as one admits primes above `ℓ` (there the ℓ-adic inertia is not torsion, so the Frobenius is not
well defined even modulo torsion), and it is also false for primes `𝔭 ∤ ℓ` in `Γ` itself (the ℓ-part
of the tame inertia is a nontrivial torsion subgroup of `Γ`).

The usable form — Shimizu's, who only ever applies the correspondence at **completely split primes
of residue characteristic `≠ ℓ`** — is the one used here: the correspondence is required

* only for primes `𝔭` that are completely split over `ℚ` (so that the residue degrees in the tower
  `ℚ ⊆ K_i ⊆ L` are `1`, which is what makes the restriction of a Frobenius element a Frobenius
  element at *every* level), and
* only modulo the torsion of `Γ`, i.e. after applying `gammaHausMk`.

With this hypothesis the whole proof of Proposition 4f.3 is unchanged; the only change is that the
escaping prime must be chosen with residue characteristic `≠ ℓ` (this is the content of the explicit
hypothesis `hescape` below).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped NumberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## The contraction of a completely split prime -/

section Under

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- **A prime completely split over `ℚ` has a completely split contraction.**  This is the tower
formula for the ramification index and the inertia degree. -/
theorem splitsCompletelyOverRat_under (𝔮 : NK.Chebotarev.PrimeIdeal L)
    (h : NK.Reconstruct.SplitsCompletelyOverRat 𝔮) :
    NK.Reconstruct.SplitsCompletelyOverRat
      (𝔮.under (NumberField.RingOfIntegers K)) := by
  haveI hl : 𝔮.asIdeal.LiesOver
      ((𝔮.under (NumberField.RingOfIntegers K)).asIdeal) := Ideal.over_under 𝔮.asIdeal
  refine ⟨?_, ?_⟩
  · have h1 := Ideal.inertiaDeg_tower (R := NumberField.RingOfIntegers ℚ)
      (S := NumberField.RingOfIntegers K) (T := NumberField.RingOfIntegers L)
      (𝔮.under (NumberField.RingOfIntegers K)).asIdeal 𝔮.asIdeal
    have h0 : 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) = 1 := h.1
    rw [h0] at h1
    exact (mul_eq_one.mp h1.symm).1
  · have h1 := Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers ℚ)
      (S := NumberField.RingOfIntegers K) (T := NumberField.RingOfIntegers L)
      (𝔮.under (NumberField.RingOfIntegers K)).asIdeal 𝔮.asIdeal
    have h0 : 𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1 := h.2
    rw [h0] at h1
    exact (mul_eq_one.mp h1.symm).1

/-- The rational prime below a contracted prime is the rational prime below the prime. -/
theorem primeBelowNat_under (𝔮 : NK.Chebotarev.PrimeIdeal L) :
    NK.LocalInputs.primeBelowNat K (𝔮.under (NumberField.RingOfIntegers K)) =
      NK.LocalInputs.primeBelowNat L 𝔮 := by
  simp only [NK.LocalInputs.primeBelowNat]
  rw [NK.ReconstructField.primeBelow_under_eq (K := K) (L := L) 𝔮]

/-- The residue characteristic of a prime and of its contraction agree. -/
theorem charP_under_eq (𝔮 : NK.Chebotarev.PrimeIdeal L) (p : ℕ)
    (hp : CharP (NumberField.RingOfIntegers L ⧸ 𝔮.asIdeal) p) :
    CharP (NumberField.RingOfIntegers K ⧸
      (𝔮.under (NumberField.RingOfIntegers K)).asIdeal) p := by
  have h1 : CharP (NumberField.RingOfIntegers K ⧸
      (𝔮.under (NumberField.RingOfIntegers K)).asIdeal)
      (NK.LocalInputs.primeBelowNat K (𝔮.under (NumberField.RingOfIntegers K))) :=
    NK.ReconstructField.charP_of_liesOver (𝔮.under (NumberField.RingOfIntegers K))
      (NK.LocalInputs.primeBelow K (𝔮.under (NumberField.RingOfIntegers K)))
      (NK.LocalInputs.primeBelow_liesOver K (𝔮.under (NumberField.RingOfIntegers K)))
  have h2 : CharP (NumberField.RingOfIntegers L ⧸ 𝔮.asIdeal)
      (NK.LocalInputs.primeBelowNat L 𝔮) :=
    NK.ReconstructField.charP_of_liesOver 𝔮 (NK.LocalInputs.primeBelow L 𝔮)
      (NK.LocalInputs.primeBelow_liesOver L 𝔮)
  have h3 : NK.LocalInputs.primeBelowNat K (𝔮.under (NumberField.RingOfIntegers K)) =
      NK.LocalInputs.primeBelowNat L 𝔮 := primeBelowNat_under 𝔮
  have hp' : NK.LocalInputs.primeBelowNat L 𝔮 = p := CharP.eq _ h2 hp
  rw [← hp', ← h3]
  exact h1

end Under

/-! ## The pinning step of Shimizu's Proposition 4f.3, with the corrected Frobenius
correspondence -/

section Pin

variable (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
  [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
  (ℓ : ℕ) [Fact ℓ.Prime]
  (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ)
  (primeMap : NK.Chebotarev.PrimeIdeal ↥K₁.L ≃ NK.Chebotarev.PrimeIdeal ↥K₂.L)

/-- **The pinning (`τ'`-step) of Shimizu's Proposition 4f.3, with the Frobenius correspondence
restricted to completely split primes of residue characteristic `≠ ℓ`.** -/
theorem exists_tau_gammaHausMk_eq_of_isFrobElementAt_split
    (hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L), SplitsCompletelyOverRat 𝔭 →
        ∀ (p : ℕ),
          CharP (NumberField.RingOfIntegers ↥K₁.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ →
        ∀ (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
          IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
          gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
              (σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁)) =
            gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
              (galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂))
    (hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃+* Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L)
    (hsplit : SplitsCompletelyOverRat 𝔭)
    (p : ℕ)
    (hres : CharP (NumberField.RingOfIntegers ↥L.L ⧸ 𝔭.asIdeal) p) (hne : p ≠ ℓ)
    (σ : Gal(Ω/↥L.L)) (hσ : IsFrobElementAt 𝔭 σ) :
    ∃ τ : Gal(↥L.L/ℚ),
      gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
          (σbar (ambientPi K₁ L h₁ ℓ (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
            (ambientPi K₂ L h₂ ℓ
              (tauStar L.L ℓ (Θ τ) (hΘmem τ) (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))) := by
  letI : Algebra ↥K₁.L ↥L.L := algOfLeEqTau K₁.L L.L h₁
  letI : Algebra ↥K₂.L ↥L.L := algOfLeEqTau K₂.L L.L h₂
  haveI : IsScalarTower ↥K₁.L ↥L.L Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower ↥K₂.L ↥L.L Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : FiniteDimensional ↥K₁.L ↥L.L := finiteDimensional_algOfLeEqTau K₁ L h₁ (fun x => rfl)
  haveI : FiniteDimensional ↥K₂.L ↥L.L := finiteDimensional_algOfLeEqTau K₂ L h₂ (fun x => rfl)
  have hdeg₁ : 𝔭.asIdeal.inertiaDeg (𝓞 ↥K₁.L) = 1 :=
    inertiaDeg_eq_one_of_splitsCompletelyOverRat (K := ↥K₁.L) 𝔭 hsplit
  have h1frob : IsFrobElementAt (𝔭.under (𝓞 ↥K₁.L)) (σ.restrictScalars ↥K₁.L) :=
    isFrobElementAt_restrictScalars_of_inertiaDeg_eq_one K₁ L h₁ 𝔭 hdeg₁ σ hσ
  obtain ⟨τ, hτ⟩ := exists_galois_primeTransport_under_eq K₁ K₂ L h₁ h₂ primeMap hchar 𝔭
  have hθ : thetaOnL L.L (Θ τ) (hΘmem τ) = (τ : ↥L.L ≃+* ↥L.L) := by
    ext x
    exact hΘres τ x
  have hconj : IsFrobElementAt (primeTransport (thetaOnL L.L (Θ τ) (hΘmem τ)) 𝔭)
      (ringConjHom L.L (Θ τ) (hΘmem τ) σ) :=
    isFrobElementAt_ringConjHom L.L (Θ τ) (hΘmem τ) 𝔭 σ hσ
  have hsplitθ : SplitsCompletelyOverRat (primeTransport (thetaOnL L.L (Θ τ) (hΘmem τ)) 𝔭) := by
    rw [hθ]
    exact splitsCompletelyOverRat_primeTransport L τ 𝔭 hsplit
  have hdeg₂ : (primeTransport (thetaOnL L.L (Θ τ) (hΘmem τ)) 𝔭).asIdeal.inertiaDeg (𝓞 ↥K₂.L)
      = 1 :=
    inertiaDeg_eq_one_of_splitsCompletelyOverRat (K := ↥K₂.L) _ hsplitθ
  have h2frob : IsFrobElementAt (primeMap (𝔭.under (𝓞 ↥K₁.L)))
      ((ringConjHom L.L (Θ τ) (hΘmem τ) σ).restrictScalars ↥K₂.L) := by
    have h := isFrobElementAt_restrictScalars_of_inertiaDeg_eq_one K₂ L h₂
      (primeTransport (thetaOnL L.L (Θ τ) (hΘmem τ)) 𝔭) hdeg₂
      (ringConjHom L.L (Θ τ) (hΘmem τ) σ) hconj
    rw [hθ, hτ] at h
    exact h
  -- the corrected Frobenius correspondence at the pair `(𝔭 ∩ K₁, primeMap (𝔭 ∩ K₁))`
  have hsplit_under : SplitsCompletelyOverRat (𝔭.under (𝓞 ↥K₁.L)) :=
    splitsCompletelyOverRat_under (K := ↥K₁.L) (L := ↥L.L) 𝔭 hsplit
  have hres_under : CharP (NumberField.RingOfIntegers ↥K₁.L ⧸
      (𝔭.under (𝓞 ↥K₁.L)).asIdeal) p :=
    charP_under_eq (K := ↥K₁.L) (L := ↥L.L) 𝔭 p hres
  have hbapp := hb (𝔭.under (𝓞 ↥K₁.L)) hsplit_under p hres_under hne
    (σ.restrictScalars ↥K₁.L)
    ((ringConjHom L.L (Θ τ) (hΘmem τ) σ).restrictScalars ↥K₂.L) h1frob h2frob
  refine ⟨τ, ?_⟩
  have h1 : ambientPi K₁ L h₁ ℓ (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)
      = galToGamma (K := ↥K₁.L) (K' := Ω) ℓ (σ.restrictScalars ↥K₁.L) :=
    gammaBaseChangeHom_galToGamma (K := ↥K₁.L) (K' := Ω) ℓ (levelExtendGen K₁ L h₁) σ
  have h2 : ambientPi K₂ L h₂ ℓ
        (galToGamma (K := ↥L.L) (K' := Ω) ℓ (ringConjHom L.L (Θ τ) (hΘmem τ) σ))
      = galToGamma (K := ↥K₂.L) (K' := Ω) ℓ
          ((ringConjHom L.L (Θ τ) (hΘmem τ) σ).restrictScalars ↥K₂.L) :=
    gammaBaseChangeHom_galToGamma (K := ↥K₂.L) (K' := Ω) ℓ (levelExtendGen K₂ L h₂)
      (ringConjHom L.L (Θ τ) (hΘmem τ) σ)
  rw [tauStar_galToGamma, h1, h2]
  exact hbapp

end Pin

/-! ## Shimizu's Proposition 4f.3 with the corrected Frobenius correspondence -/

section PropAway

/-- **Shimizu's Proposition 4f.3, with the Frobenius correspondence restricted to completely split
primes of residue characteristic `≠ ℓ`.** -/
theorem prop4f3_awayFromL
    (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (primeMap : NK.Chebotarev.PrimeIdeal ↥K₁.L ≃ NK.Chebotarev.PrimeIdeal ↥K₂.L)
    (hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L), SplitsCompletelyOverRat 𝔭 →
        ∀ (p : ℕ),
          CharP (NumberField.RingOfIntegers ↥K₁.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ →
        ∀ (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
          IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
          gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
              (σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁)) =
            gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
              (galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂))
    (hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃+* Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (hescape : ∀ (H : Gal(↥L.L/ℚ) → Subgroup (Gamma ↥L.L Ω ℓ)),
        (∀ i, IsClosed ((H i : Set (Gamma ↥L.L Ω ℓ)))) →
        (∀ i, ¬ IsOpen ((H i : Set (Gamma ↥L.L Ω ℓ)))) →
        ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (σ : Gal(Ω/↥L.L)),
          SplitsCompletelyOverRat 𝔭 ∧
          (∀ p : ℕ, CharP (NumberField.RingOfIntegers ↥L.L ⧸ 𝔭.asIdeal) p → p ≠ ℓ) ∧
          IsFrobElementAt 𝔭 σ ∧
          ∀ i, galToGamma (K := ↥L.L) (K' := Ω) ℓ σ ∉ H i) :
    ∃ τ : Gal(↥L.L/ℚ), ∀ γ : Gamma ↥L.L Ω ℓ,
      gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
          (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
            (ambientPi K₂ L h₂ ℓ
              (tauStar L.L ℓ (Θ τ) (hΘmem τ) γ)) := by
  classical
  by_contra hcon
  push_neg at hcon
  haveI : Finite (Gal(↥L.L/ℚ)) := inferInstance
  have hne : ∀ τ : Gal(↥L.L/ℚ),
      psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar (tauStar L.L ℓ (Θ τ) (hΘmem τ))
        (continuous_tauStar L.L ℓ (Θ τ) (hΘmem τ)) ≠ 1 := by
    intro τ h
    obtain ⟨γ, hγ⟩ := hcon τ
    refine hγ ((psiTau'_eq_one_iff K₁ K₂ L h₁ h₂ ℓ σbar hσbar
      (tauStar L.L ℓ (Θ τ) (hΘmem τ))
      (continuous_tauStar L.L ℓ (Θ τ) (hΘmem τ))).mp h γ)
  -- the escaping prime, completely split over `ℚ` and of residue characteristic `≠ ℓ`
  obtain ⟨𝔭, σ, hsplit, haway, hσ, hout⟩ := hescape
    (fun τ : Gal(↥L.L/ℚ) =>
      (psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar (tauStar L.L ℓ (Θ τ) (hΘmem τ))
        (continuous_tauStar L.L ℓ (Θ τ) (hΘmem τ))).ker)
    (fun τ => isClosed_ker_of_continuous _
      (psiTau'_continuous K₁ K₂ L h₁ h₂ ℓ σbar hσbar _ _))
    (fun τ => not_isOpen_ker_of_continuous_to_gammaHaus ℓ _
      (psiTau'_continuous K₁ K₂ L h₁ h₂ ℓ σbar hσbar _ _) (hne τ))
  -- the residue characteristic of the escaping prime
  have hres : CharP (NumberField.RingOfIntegers ↥L.L ⧸ 𝔭.asIdeal)
      (NK.LocalInputs.primeBelowNat ↥L.L 𝔭) :=
    NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow ↥L.L 𝔭)
      (NK.LocalInputs.primeBelow_liesOver (↥L.L) 𝔭)
  have hpne : NK.LocalInputs.primeBelowNat ↥L.L 𝔭 ≠ ℓ := haway _ hres
  obtain ⟨τ, hτ⟩ := exists_tau_gammaHausMk_eq_of_isFrobElementAt_split K₁ K₂ L h₁ h₂ ℓ
    σbar primeMap hb hchar Θ hΘmem hΘres 𝔭 hsplit _ hres hpne σ hσ
  refine hout τ ?_
  show psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar (tauStar L.L ℓ (Θ τ) (hΘmem τ))
      (continuous_tauStar L.L ℓ (Θ τ) (hΘmem τ)) (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ) = 1
  rw [psiTau'_apply]
  simp only [phiTau', MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply,
    map_mul, map_inv]
  change gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
      (σbar (ambientPi K₁ L h₁ ℓ (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)))
    * (gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
      (ambientPi K₂ L h₂ ℓ
        (tauStar L.L ℓ (Θ τ) (hΘmem τ) (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))))⁻¹ = 1
  rw [hτ, mul_inv_cancel]

end PropAway

/-! ## Shimizu's Theorem 4.0 (assembly), with the corrected Proposition 4f.3 -/

section Assembly

/-- **Shimizu's Theorem 4.0, with the corrected Proposition 4f.3.**  Its hypothesis `hprop` is the
conclusion of `NK.Reconstruct.prop4f3_awayFromL`. -/
theorem exists_theta_of_prop4f3_data_gen_awayFromL
    (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃ₐ[ℚ] Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (hprop : ∃ τ : Gal(↥L.L/ℚ), ∀ γ : Gamma ↥L.L Ω ℓ,
      gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
            (ambientPi K₂ L h₂ ℓ
              (tauStar L.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)))
    (hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v)
    (h45 : Fourf5InputGen Ω ℓ) :
    ∃ τ : Gal(↥L.L/ℚ), K₁.L = K₂.L.map (Θ τ).symm.toAlgHom := by
  classical
  -- Step 1: the element `τ ∈ Gal(L/ℚ)` produced by Shimizu's Proposition 4f.3.
  obtain ⟨τ, hτ⟩ := hprop
  refine ⟨τ, ?_⟩
  -- Step 2: the `θ⁻¹`-image `M` of `K₂`, and the transport isomorphism `Ψ : Γ_M ≅ Γ_{K₂}`.
  set M : NumFieldIn ℚ Ω := K₂.map (Θ τ) with hMdef
  have hM : M.L = K₂.L.map (Θ τ).symm.toAlgHom := NumFieldIn.map_L K₂ (Θ τ)
  haveI : IsSepClosure ↥M.L Ω := hM ▸ isSepClosure_level (K₂.L.map (Θ τ).symm.toAlgHom)
  have hθL : ∀ x : Ω, x ∈ L.L ↔ (Θ τ) x ∈ L.L := hΘmem τ
  have hML : M.L ≤ L.L := by
    rw [hM]
    exact le_trans (IntermediateField.map_mono (Θ τ).symm.toAlgHom h₂)
      (map_symm_le_self L.L (Θ τ) hθL)
  obtain ⟨Ψ, hΨcont, hΨeq⟩ := thetaGammaTransport_gen K₂ (Θ τ) ℓ M hM L h₂ hML hθL
  -- Step 3: `σbar' := Ψ⁻¹ ∘ σbar`, and the reformulation of step 1.
  have hΨsymm_cont : Continuous ⇑(Ψ.symm : Gamma ↥K₂.L Ω ℓ →* Gamma ↥M.L Ω ℓ) :=
    continuous_symm_of_mulEquiv Ψ hΨcont
  let σbar' : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥M.L Ω ℓ := σbar.trans Ψ.symm
  have hσbar'cont : Continuous ⇑σbar' := hΨsymm_cont.comp hσbar
  have heq : ∀ γ : Gamma ↥L.L Ω ℓ,
      gammaHausMk (K := ↥M.L) (K' := Ω) ℓ (σbar' (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥M.L) (K' := Ω) ℓ (ambientPi M L hML ℓ γ) := by
    intro γ
    have hτγ := hτ γ
    have hΨeqγ : (ambientPi K₂ L h₂ ℓ) (tauStar L.L ℓ (Θ τ) hθL γ)
        = Ψ (ambientPi M L hML ℓ γ) := by
      have h1 := DFunLike.congr_fun hΨeq γ
      rwa [MonoidHom.comp_apply] at h1
    have hstep : gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
        (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ (Ψ (ambientPi M L hML ℓ γ)) := by
      rw [hτγ, hΨeqγ]
    have h3 := congrArg
      (gammaHausLift ℓ (Ψ.symm : Gamma ↥K₂.L Ω ℓ →* Gamma ↥M.L Ω ℓ) hΨsymm_cont) hstep
    rw [gammaHausLift_comp, gammaHausLift_comp] at h3
    simpa [σbar', MulEquiv.trans_apply] using h3
  -- Step 4: Lemma 4f.4 for the pair `(K₁, M)`, then join with `L`.
  have h4f4 := lemma4f4_gen K₁ M L h₁ hML ℓ σbar' hσbar'cont heq
  have hsup : (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)
      = (L.L ⊔ levelInfinityOf M ℓ : IntermediateField ℚ Ω) := by
    calc (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)
        = (levelInfinityOf K₁ ℓ ⊔ M.L) ⊔ L.L := by rw [sup_assoc, sup_eq_right.mpr hML]
      _ = (K₁.L ⊔ levelInfinityOf M ℓ) ⊔ L.L := by rw [h4f4]
      _ = L.L ⊔ levelInfinityOf M ℓ := by
          rw [sup_assoc, sup_comm (levelInfinityOf M ℓ) L.L, ← sup_assoc,
            sup_eq_right.mpr h₁]
  -- Step 5: Proposition 4f.5 identifies `M` with `K₁`.
  have hKM : K₁.L = M.L := h45 K₁ M L h₁ hML hsup hcomplex
  exact hKM.trans hM


/-- **Shimizu's Theorem 4.0 (assembly), conclusion in the form of an isomorphism.** -/
theorem exists_isomorphism_of_prop4f3_data_gen_awayFromL
    (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃ₐ[ℚ] Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (hprop : ∃ τ : Gal(↥L.L/ℚ), ∀ γ : Gamma ↥L.L Ω ℓ,
      gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
            (ambientPi K₂ L h₂ ℓ
              (tauStar L.L ℓ ((Θ τ : Ω ≃+* Ω)) (hΘmem τ) γ)))
    (hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v)
    (h45 : Fourf5InputGen Ω ℓ) :
    ∃ τ : Gal(↥L.L/ℚ), Nonempty (↥K₁.L ≃+* ↥K₂.L) := by
  obtain ⟨τ, hf⟩ := exists_theta_of_prop4f3_data_gen_awayFromL K₁ K₂ L h₁ h₂ ℓ σbar hσbar
    Θ hΘmem hΘres hprop hcomplex h45
  refine ⟨τ, ?_⟩
  letI : Algebra ℚ ↥K₂.L := IntermediateField.algebra' K₂.L
  letI : Algebra ℚ ↥(K₂.L.map (Θ τ).symm.toAlgHom) :=
    IntermediateField.algebra' (K₂.L.map (Θ τ).symm.toAlgHom)
  rw [hf]
  exact ⟨(IntermediateField.equivMap K₂.L (Θ τ).symm.toAlgHom).symm.toRingEquiv⟩

end Assembly

end NK.Reconstruct
