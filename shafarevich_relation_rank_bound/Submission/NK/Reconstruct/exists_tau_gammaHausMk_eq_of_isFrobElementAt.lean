import Mathlib
import Submission.NK.Reconstruct.ambient4f3
import Submission.NK.Reconstruct.tauStarDef
import Submission.NK.Reconstruct.exists_algEquiv_primeTransport_eq
import Submission.NK.Reconstruct.splitFrobeniusBase
import Submission.NK.Chebotarev.IsFrobAtConj
import Submission.NK.Reconstruct.gammaBaseChangeHom_galToGamma
import Submission.NK.Reconstruct.isFrobElementAt_ringConjHom
import Submission.NK.Reconstruct.exists_galois_primeTransport_under_eq
import Submission.NK.Reconstruct.splitsCompletelyOverRat_primeTransport
import Submission.NK.Reconstruct.isFrobElementAt_restrictScalars_of_inertiaDeg_eq_one

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField


set_option maxHeartbeats 4000000

open scoped NumberField

/-- **The `↥L`-algebra structure on `↥M` given by the inclusion**, for `L ≤ M` two intermediate
fields of `K'/K` (a local copy of the helper of the same name). -/
noncomputable def algOfLeEqTau {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']
    (L M : IntermediateField K K') (h : L ≤ M) : Algebra ↥L ↥M :=
  RingHom.toAlgebra
    { toFun := fun x => ⟨x.1, h x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }


/-- **Finiteness of a level over a sublevel.**  For `K ⊆ L` finite Galois levels of `Ω/ℚ` the
level `↥L.L` is a finite extension of `↥K.L`, for the `↥K.L`-algebra structure given by the
inclusion.  (The `ℚ`-algebra structures are pinned inside the proof to the canonical ones of the
intermediate fields, so that the instance search does not have to choose between them and the
generic `Algebra ℚ _` structure of a field of characteristic zero.) -/
theorem finiteDimensional_algOfLeEqTau {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h : K.L ≤ L.L)
    [Algebra ↥K.L ↥L.L] [IsScalarTower ↥K.L ↥L.L Ω]
    (hcompat : ∀ x : ↥K.L, algebraMap ↥K.L ↥L.L x = (⟨x.1, h x.2⟩ : ↥L.L)) :
    FiniteDimensional ↥K.L ↥L.L := by
  letI algK : Algebra ℚ ↥K.L := IntermediateField.algebra' K.L
  letI algL : Algebra ℚ ↥L.L := IntermediateField.algebra' L.L
  letI : SMul ℚ ↥K.L := algK.toSMul
  letI : SMul ℚ ↥L.L := algL.toSMul
  haveI : IsScalarTower ℚ ↥K.L ↥L.L :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact Module.Finite.of_restrictScalars_finite ℚ ↥K.L ↥L.L

/-- **The pinning (the `τ'`-step) of Shimizu's Proposition 4f.3.**  Let `Ω/ℚ` be Galois and
separably closed, `K₁, K₂ ⊆ L` finite Galois levels of `Ω/ℚ`, `𝔭` a prime of `L` completely split
over `ℚ`, and `σ ∈ Gal(Ω/L)` a Frobenius element at `𝔭`.  Assume the Frobenius correspondence
`hb : IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ → σbar (galToGamma g₁) =
galToGamma g₂`, that `primeMap` preserves the rational prime (`hchar`), and that `Θ` is a section of
the restriction `Gal(L/ℚ) ← (Ω ≃+* Ω)` (i.e. `Θ τ` preserves `L` and restricts to `τ` on it).
Then there is `τ ∈ Gal(L/ℚ)` with

  `gammaHausMk (σbar (π_{L/K₁} (galToGamma σ))) = gammaHausMk (π_{L/K₂} (τ^*(Θ τ) (galToGamma σ)))`.

Plan (the proof route the reviewers recommend).  Write `w := ringConjHom L.L (Θ τ) (hΘmem τ) σ`,
i.e. `(Θ τ) σ (Θ τ)⁻¹`; it is a Frobenius element at `(Θ τ) · 𝔭`.  By
`gammaBaseChangeHom_galToGamma` and `tauStar_galToGamma`, the right-hand side is
`gammaHausMk (galToGamma (w|K₂))`, while the left-hand side is
`gammaHausMk (σbar (galToGamma (σ|K₁)))`.  So it suffices to have `IsFrobElementAt (𝔭 ∩ K₁) (σ|K₁)`
(by `isFrobElementAt_restrictScalars`, using `hsplit`) and
`IsFrobElementAt (primeMap (𝔭 ∩ K₁)) (w|K₂)`, and then to evaluate `hb` — the two `galToGamma`
arguments being literally the ones appearing in the goal, so no uniqueness statement is needed.

The second Frobenius condition is obtained by choosing `τ` with `(Θ τ) · 𝔭` lying over
`primeMap (𝔭 ∩ K₁)`.  Such `τ` exists: `hchar` makes `primeMap (𝔭 ∩ K₁)` lie over the same rational
prime as `𝔭 ∩ K₁`, and `Gal(L/ℚ)` acts transitively on the primes of `L` above a fixed rational
prime (`NK.Reconstruct.exists_algEquiv_primeTransport_eq`); `hΘres` converts `Θ τ` into
`τ|_L`.  Conjugating the Frobenius element `σ` at `𝔭` by the ring automorphism `Θ τ`
(which fixes `ℚ`, so preserves complete splitting) gives a Frobenius element at `(Θ τ) · 𝔭`
(`NK.Chebotarev.IsFrobAtConj` descent, level by level), and restricting to `K₂` at the completely
split prime gives the second condition (`isFrobElementAt_restrictScalars` again).

The prover needs one self-contained auxiliary statement: **conjugation of `IsFrobElementAt` along a
ring automorphism** `θ` of `Ω` preserving `L`: `IsFrobElementAt 𝔭 σ → IsFrobElementAt (θ · 𝔭)
(ringConjHom L θ h)`, where `θ · 𝔭 := primeTransport (θ|_{L}) 𝔭`
(`NK.Reconstruct.primeTransport`), plus the compatibility `(θ · 𝔭) ∩ K₂ = (θ · 𝔭).under (𝓞 ↥K₂.L)`
needed to feed the restriction statement. -/
theorem exists_tau_gammaHausMk_eq_of_isFrobElementAt
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K₁ K₂ : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : NK.Reconstruct.Gamma ↥K₁.L Ω ℓ ≃* NK.Reconstruct.Gamma ↥K₂.L Ω ℓ)
    (primeMap : NK.Chebotarev.PrimeIdeal ↥K₁.L ≃ NK.Chebotarev.PrimeIdeal ↥K₂.L)
    (hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L) (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
        NK.Reconstruct.IsFrobElementAt 𝔭 g₁ → NK.Reconstruct.IsFrobElementAt (primeMap 𝔭) g₂ →
        σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁) =
          galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂)
    (hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃+* Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L)
    (hsplit : NK.Reconstruct.SplitsCompletelyOverRat 𝔭)
    (σ : Gal(Ω/↥L.L)) (hσ : NK.Reconstruct.IsFrobElementAt 𝔭 σ) :
    ∃ τ : Gal(↥L.L/ℚ),
      NK.Reconstruct.gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
          (σbar (NK.Reconstruct.ambientPi K₁ L h₁ ℓ
            (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)))
        = NK.Reconstruct.gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
            (NK.Reconstruct.ambientPi K₂ L h₂ ℓ
              (NK.Reconstruct.tauStar L.L ℓ (Θ τ) (hΘmem τ)
                (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ))) := by
  -- The `↥K_i.L`-algebra structures on `↥L.L` and the associated instances.
  letI : Algebra ↥K₁.L ↥L.L := algOfLeEqTau K₁.L L.L h₁
  letI : Algebra ↥K₂.L ↥L.L := algOfLeEqTau K₂.L L.L h₂
  haveI : IsScalarTower ↥K₁.L ↥L.L Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower ↥K₂.L ↥L.L Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : FiniteDimensional ↥K₁.L ↥L.L := finiteDimensional_algOfLeEqTau K₁ L h₁ (fun x => rfl)
  haveI : FiniteDimensional ↥K₂.L ↥L.L := finiteDimensional_algOfLeEqTau K₂ L h₂ (fun x => rfl)
  -- the prime of `K₁.L` below `𝔭`
  have hdeg₁ : 𝔭.asIdeal.inertiaDeg (𝓞 ↥K₁.L) = 1 :=
    inertiaDeg_eq_one_of_splitsCompletelyOverRat (K := ↥K₁.L) 𝔭 hsplit
  -- `σ` restricted to `K₁.L` is a Frobenius element at the prime below `𝔭`
  have h1frob : IsFrobElementAt (𝔭.under (𝓞 ↥K₁.L)) (σ.restrictScalars ↥K₁.L) :=
    isFrobElementAt_restrictScalars_of_inertiaDeg_eq_one K₁ L h₁ 𝔭 hdeg₁ σ hσ
  -- choose `τ` so that `τ · 𝔭` contracts to `primeMap (𝔭 ∩ K₁)`
  obtain ⟨τ, hτ⟩ := exists_galois_primeTransport_under_eq K₁ K₂ L h₁ h₂ primeMap hchar 𝔭
  -- `Θ τ` restricts to `τ` on `L`
  have hθ : thetaOnL L.L (Θ τ) (hΘmem τ) = (τ : ↥L.L ≃+* ↥L.L) := by
    ext x
    exact hΘres τ x
  -- the conjugate of `σ` by `Θ τ` is a Frobenius element at `(Θ τ) · 𝔭`
  have hconj : IsFrobElementAt (primeTransport (thetaOnL L.L (Θ τ) (hΘmem τ)) 𝔭)
      (ringConjHom L.L (Θ τ) (hΘmem τ) σ) :=
    isFrobElementAt_ringConjHom L.L (Θ τ) (hΘmem τ) 𝔭 σ hσ
  -- `(Θ τ) · 𝔭` is completely split over `ℚ`
  have hsplitθ : SplitsCompletelyOverRat (primeTransport (thetaOnL L.L (Θ τ) (hΘmem τ)) 𝔭) := by
    rw [hθ]
    exact splitsCompletelyOverRat_primeTransport L τ 𝔭 hsplit
  have hdeg₂ : (primeTransport (thetaOnL L.L (Θ τ) (hΘmem τ)) 𝔭).asIdeal.inertiaDeg (𝓞 ↥K₂.L)
      = 1 :=
    inertiaDeg_eq_one_of_splitsCompletelyOverRat (K := ↥K₂.L) _ hsplitθ
  -- restricting to `K₂.L` gives the second Frobenius condition
  have h2frob : IsFrobElementAt (primeMap (𝔭.under (𝓞 ↥K₁.L)))
      ((ringConjHom L.L (Θ τ) (hΘmem τ) σ).restrictScalars ↥K₂.L) := by
    have h := isFrobElementAt_restrictScalars_of_inertiaDeg_eq_one K₂ L h₂
      (primeTransport (thetaOnL L.L (Θ τ) (hΘmem τ)) 𝔭) hdeg₂
      (ringConjHom L.L (Θ τ) (hΘmem τ) σ) hconj
    rw [hθ, hτ] at h
    exact h
  -- the Frobenius correspondence at the pair `(𝔭 ∩ K₁, primeMap (𝔭 ∩ K₁))`
  have hbapp := hb (𝔭.under (𝓞 ↥K₁.L)) (σ.restrictScalars ↥K₁.L)
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
  rw [tauStar_galToGamma, h1, h2, hbapp]

end NK.Reconstruct
