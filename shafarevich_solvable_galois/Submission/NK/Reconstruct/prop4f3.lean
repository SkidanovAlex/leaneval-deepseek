import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.Reconstruct.exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup
import Submission.NK.Reconstruct.exists_tau_gammaHausMk_eq_of_isFrobElementAt
import Submission.NK.Reconstruct.not_isOpen_ker_of_continuous_to_gammaHaus
import Submission.NK.Reconstruct.phiTauDef
import Submission.NK.Reconstruct.prop4f3_measureStep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shimizu's Proposition 4f.3 (corrected form)

Proposition 4f.3 of S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*
(arXiv:2009.10431, §4) — the step that produces, from the local correspondence and Čebotarev, a
`τ ∈ Gal(L/ℚ)` making the two base-change maps agree modulo the outer action of `τ`.

## The correction (README §19.8)

The naive statement of 4f.3 is **false**: its proof needs the pointwise step
`IsFrobElementAt 𝔭 g → IsFrobElementAt (𝔭|K) (g|K)`, which fails in general because the inclusion
`G_L ↪ G_K` carries `Frob_𝔭` to `Frob_{𝔭|K}^{f}` (`ℚ ⊆ ℚ(i)`, `𝔭 = (3)`).  Shimizu's own proof
selects the escaping prime `𝔭` among the primes *completely split over `ℚ`*, where every residue
degree in the tower is `1`, and the step becomes true
(`NK.Reconstruct.isFrobElementAt_restrictScalars`).  The Čebotarev input must therefore be the
split form `NK.Reconstruct.exists_split_frobAt` (obtained from `ChebotarevInput ℚ Ω`), and the
escape uses `NK.Reconstruct.exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup`.

The second correction is in the measure step: Shimizu argues that `ker φ_τ` has Haar measure `0`
because its `ℤ_ℓ`-rank is `< r_ℓ(L)`.  Here the same effect is obtained without any rank input: the
torsion-free quotient `Γ_L^{tf}` makes the kernel of a non-zero continuous homomorphism non-open
(`NK.Reconstruct.not_isOpen_ker_of_continuous_to_gammaHaus`), and the finitely many kernels cannot
cover `Γ_L` by the Baire argument.

## Statement

With `Ω/ℚ` Galois and separably closed, `K₁, K₂ ⊆ L` finite Galois levels of `Ω/ℚ`, a continuous
isomorphism `σbar : Γ_{K₁} ≅ Γ_{K₂}` whose Frobenius correspondence with respect to a prime
bijection `primeMap` is `hb`, a section `Θ` of the restriction `Gal(L/ℚ) ← (Ω ≃+* Ω)`, and the
Čebotarev input `hc`, there is `τ ∈ Gal(L/ℚ)` with

  `σbar (π_{L/K₁} γ) ≡ π_{L/K₂} (τ^*(Θ τ) γ)   (mod the invisible subgroup of Γ_{K₂})`

for all `γ ∈ Γ_L` — the form in which Lemma 4f.4 consumes it.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4;
J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. XII §12.2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField


open NK.Chebotarev
open scoped NumberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Shimizu's Proposition 4f.3, corrected form.** -/
theorem prop4f3
    (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (primeMap : PrimeIdeal ↥K₁.L ≃ PrimeIdeal ↥K₂.L)
    (hb : ∀ (𝔭 : PrimeIdeal ↥K₁.L) (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
        IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
        σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁) =
          galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂)
    (hchar : ∀ 𝔭 : PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃+* Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (hc : ChebotarevInput ℚ Ω) :
    ∃ τ : Gal(↥L.L/ℚ), ∀ γ : Gamma ↥L.L Ω ℓ,
      gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ (σbar (ambientPi K₁ L h₁ ℓ γ))
        = gammaHausMk (K := ↥K₂.L) (K' := Ω) ℓ
            (ambientPi K₂ L h₂ ℓ (tauStar L.L ℓ (Θ τ) (hΘmem τ) γ)) := by
  classical
  by_contra hcon
  push_neg at hcon
  -- The `τ`'s are the elements of the finite group `Gal(L/ℚ)`.
  haveI : Finite (Gal(↥L.L/ℚ)) := inferInstance
  -- The assumption says exactly that all the `Ψ_τ` are non-trivial.
  have hne : ∀ τ : Gal(↥L.L/ℚ),
      psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar (tauStar L.L ℓ (Θ τ) (hΘmem τ))
        (continuous_tauStar L.L ℓ (Θ τ) (hΘmem τ)) ≠ 1 := by
    intro τ h
    obtain ⟨γ, hγ⟩ := hcon τ
    refine hγ ((psiTau'_eq_one_iff K₁ K₂ L h₁ h₂ ℓ σbar hσbar
      (tauStar L.L ℓ (Θ τ) (hΘmem τ))
      (continuous_tauStar L.L ℓ (Θ τ) (hΘmem τ))).mp h γ)
  -- The escaping prime, completely split over `ℚ`.
  obtain ⟨𝔭, σ, hσ, hsplit, hout⟩ :=
    exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup (Ω := Ω) hc L ℓ
      (fun τ : Gal(↥L.L/ℚ) =>
        (psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar (tauStar L.L ℓ (Θ τ) (hΘmem τ))
          (continuous_tauStar L.L ℓ (Θ τ) (hΘmem τ))).ker)
      (fun τ => isClosed_ker_of_continuous _
        (psiTau'_continuous K₁ K₂ L h₁ h₂ ℓ σbar hσbar _ _))
      (fun τ => not_isOpen_ker_of_continuous_to_gammaHaus ℓ _
        (psiTau'_continuous K₁ K₂ L h₁ h₂ ℓ σbar hσbar _ _) (hne τ))
  -- The pinning step at that prime.
  obtain ⟨τ, hτ⟩ := exists_tau_gammaHausMk_eq_of_isFrobElementAt K₁ K₂ L h₁ h₂ ℓ σbar
    primeMap hb hchar Θ hΘmem hΘres 𝔭 hsplit σ hσ
  -- Contradiction: `galToGamma σ` lies in `ker Ψ_τ`.
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

end NK.Reconstruct
