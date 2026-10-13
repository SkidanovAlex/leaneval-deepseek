import Mathlib
import Submission.Work.DSG4b.Defs
import Submission.Work.DSG4b.RootLift
import Submission.Work.DSG4b.rootLocal_flat
import Submission.Work.DSG4b.rootLocal_residueField_equiv
import Submission.Work.DSG4b.GonfDefs
import Submission.Work.DSG4b.uRingKey.uRing_ker_exists_mul_mem
import Submission.Work.DSG4b.gonfPerfect.exists_flat_local_perfect_residue
import Submission.Work.DSG4b.gonfPerfect.exists_flat_local_perfect_residue
import Submission.Work.DSG4b.uRingKey.uRing_ker_exists_mul_mem
import Submission.Work.DSG4b.gonfPerfect.exists_flat_local_perfect_residue

/-!
# G4b residue enlargement

Design (full account in `GONF_ENLARGEMENT_DESIGN.md` in this directory):

* `B := (A : Localization.AtPrime 𝔫)`, where `A` is a quotient of a polynomial ring over `R` by
  *monic* relations (so that `A` is flat over `R` by `Work.DSG4b.RFAux.flat_quotient_monic`) and `𝔫`
  is the kernel of a surjection `A ↠ K = AlgebraicClosure (ResidueField R)`.  Then `B` is flat and
  local, its residue field is `A ⧸ 𝔫 ≅ K`, and `𝔪_R B = 𝔪_B` holds once `A ⧸ 𝔪_R A` localised at
  `𝔫` is a field.
* `A = S[U_α : α ∈ K] ⧸ (F_α(U_α))`, where `S` is the "`p`-root tower" attached to a `p`-basis
  `Λ ⊆ k = ResidueField R` of `k` over `k^p` (char `k = p`; `Λ = ∅` when char `k = 0`), whose
  residue field is `k^{perf}`, and `F_α ∈ S[U]` is a monic lift of `minpoly_{k^{perf}}(α)` which
  moreover vanishes at `α`.
-/

namespace Work.DSG4b

universe a

open _root_.MvPolynomial Polynomial

section Basic

variable (R : Type a) [CommRing R] [IsLocalRing R]

/-- The residue field of `R`. -/
abbrev resField : Type a := IsLocalRing.ResidueField R

/-- An algebraic closure of the residue field of `R`; the target residue field of the enlargement. -/
abbrev resAlgClosure : Type a := AlgebraicClosure (IsLocalRing.ResidueField R)

end Basic

variable (R : Type a) [CommRing R] [IsLocalRing R]

/-- A `p`-basis datum for the residue field of `R` in residual characteristic `p`: a subset `Λ` of
`k = ResidueField R` whose monomials form a basis of `k` over `k^p`.  (For `char k = 0` one uses
`Λ = ∅`, so the tower below is trivial; this structure is only used in residual characteristic
`p`.) -/
structure PBData (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p] where
  /-- the `p`-basis. -/
  Λ : Set (IsLocalRing.ResidueField R)
  /-- the monomial basis of `k` over `k^p` attached to `Λ`. -/
  basis : Module.Basis {e : Λ →₀ ℕ // ∀ a : Λ, e a < p}
    ((frobenius (IsLocalRing.ResidueField R) p).fieldRange) (IsLocalRing.ResidueField R)
  /-- the basis vectors are the monomials in `Λ`. -/
  basis_apply : ∀ e, (basis e : IsLocalRing.ResidueField R) =
    (e.1).prod (fun a k => ((a : IsLocalRing.ResidueField R) ^ k))

/-- The `T`-tower relation indexed by `x = (λ, n)`: `(T^{(n+1)}_λ)^p − T^{(n)}_λ`, where
`T^{(0)}_λ := λ̃ ∈ R` is a chosen lift of `λ` (`Work.DSG4b.coeffLift`).  The relation is monic in the
variable `(λ, n+1)`. -/
noncomputable def towerRel (p : ℕ) (Λ : Set (IsLocalRing.ResidueField R)) (x : Λ × ℕ) :
    MvPolynomial (Λ × ℕ) R :=
  (MvPolynomial.X (x.1, x.2 + 1)) ^ p -
    (if x.2 = 0 then MvPolynomial.C (coeffLift x.1) else MvPolynomial.X (x.1, x.2))

/-- The ideal of `T`-tower relations. -/
noncomputable def towerIdeal (p : ℕ) (Λ : Set (IsLocalRing.ResidueField R)) :
    Ideal (MvPolynomial (Λ × ℕ) R) :=
  Ideal.span (Set.range (towerRel R p Λ))

/-- The `T`-tower ring attached to a `p`-basis `Λ ⊆ k`: a flat `R`-algebra whose residue field is
the perfect closure `k^{perf}` of `k`. -/
noncomputable abbrev towerRing (p : ℕ) (Λ : Set (IsLocalRing.ResidueField R)) : Type a :=
  MvPolynomial (Λ × ℕ) R ⧸ towerIdeal R p Λ

section UPart

variable (R : Type a) [CommRing R] [IsLocalRing R]

/-- **The `U`-part (separable closure over a perfectified ring).**  Let `S` be a local `R`-algebra
with `𝔪_R S = 𝔪_S` and perfect residue field `L`, and let `K = AlgebraicClosure L`.  Then there is a
flat local `R`-algebra `B` with `𝔪_R B = 𝔪_B` and algebraically closed residue field `K`.

The input `hkey` is the key fibre fact `Work.DSG4b.uRing_ker_exists_mul_mem`: every element of
`ker (uEv S)` is annihilated modulo `𝔪_R A` by an element outside `ker (uEv S)` (where `A = uRing S`
and `uEv S` is the evaluation `X_α ↦ α`). -/
theorem gonf_of_perfect_aux (S : Type a) [CommRing S] [IsLocalRing S] (φ : R →+* S)
    (hφ : φ.Flat) (hmax : (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal S)
    [PerfectField (IsLocalRing.ResidueField S)]
    (hkey : ∀ a ∈ RingHom.ker (uEv S), ∃ s, s ∉ RingHom.ker (uEv S) ∧
      s * a ∈ (IsLocalRing.maximalIdeal R).map ((uRingAlg S).comp φ))
    [(RingHom.ker (uEv S)).IsPrime]
    (ψB : R →+* Localization.AtPrime (RingHom.ker (uEv S)))
    (hψB : ∀ x : R, ψB x = algebraMap (uRing S) (Localization.AtPrime (RingHom.ker (uEv S)))
      ((uRingAlg S) (φ x)))
    (hψBflat : RingHom.Flat (R := R) (S := Localization.AtPrime (RingHom.ker (uEv S))) ψB) :
    ∃ (B : Type a) (_ : CommRing B) (_ : IsLocalRing B) (ψ : R →+* B),
      ψ.Flat ∧ (IsLocalRing.maximalIdeal R).map ψ = IsLocalRing.maximalIdeal B ∧
        IsAlgClosed (IsLocalRing.ResidueField B) := by
  classical
  let A := uRing S
  let ψA : R →+* A := (uRingAlg S).comp φ
  let 𝔫 : Ideal A := RingHom.ker (uEv S)
  have h𝔫max : 𝔫.IsMaximal := RingHom.ker_isMaximal_of_surjective (uEv S) (uEv_surjective S)
  haveI : 𝔫.IsMaximal := h𝔫max
  haveI : 𝔫.IsPrime := h𝔫max.isPrime
  let B := Localization.AtPrime 𝔫
  -- the maximal ideal of `R` dies in `K`
  have h𝔪Aker : ∀ x ∈ IsLocalRing.maximalIdeal R, uEv S (ψA x) = 0 := by
    intro x hx
    have hx' : φ x ∈ IsLocalRing.maximalIdeal S := by
      rw [← hmax]
      exact Ideal.mem_map_of_mem _ hx
    show uEv S ((uRingAlg S) (φ x)) = 0
    exact uEv_eq_zero_of_mem_maximalIdeal S hx'
  have h𝔪Ale : (IsLocalRing.maximalIdeal R).map ψA ≤ 𝔫 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    exact RingHom.mem_ker.mpr (h𝔪Aker x hx)
  have hψBeq : ψB = (algebraMap A B).comp ψA := RingHom.ext fun x => hψB x
  -- the key step: `𝔫 · B ≤ 𝔪_R B`
  have h𝔫le : 𝔫 ≤ Ideal.comap (algebraMap A B) ((IsLocalRing.maximalIdeal R).map ψB) := by
    intro a ha
    obtain ⟨s, hs, hsa⟩ := hkey a ha
    rw [Ideal.mem_comap]
    obtain ⟨u, hu⟩ := IsLocalization.map_units B (⟨s, fun h => hs h⟩ : ↥𝔫.primeCompl)
    have hsaeq : algebraMap A B a = (↑u⁻¹ : B) * algebraMap A B (s * a) := by
      rw [map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hsaeq]
    refine Ideal.mul_mem_left _ _ ?_
    rw [hψBeq, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hsa
  -- the maximal ideal of `B`
  have hmaxB : (IsLocalRing.maximalIdeal R).map ψB = IsLocalRing.maximalIdeal B := by
    have h1 : IsLocalRing.maximalIdeal B = Ideal.map (algebraMap A B) 𝔫 :=
      (IsLocalization.AtPrime.map_eq_maximalIdeal 𝔫 B).symm
    rw [h1]
    refine le_antisymm ?_ ?_
    · have hsplit : (IsLocalRing.maximalIdeal R).map ψB
          = Ideal.map (algebraMap A B) (Ideal.map ψA (IsLocalRing.maximalIdeal R)) :=
        by
          rw [hψBeq]
          exact (Ideal.map_map ψA (algebraMap A B)).symm
      rw [hsplit]
      exact Ideal.map_mono h𝔪Ale
    · exact Ideal.map_le_iff_le_comap.mpr h𝔫le
  -- the residue field of `B` is `K`, which is algebraically closed
  have hres : IsAlgClosed (IsLocalRing.ResidueField B) := by
    obtain ⟨e1⟩ := residueField_localizationAtPrime_equiv A 𝔫
    have e2 : (A ⧸ 𝔫) ≃+* AlgebraicClosure (IsLocalRing.ResidueField S) :=
      RingHom.quotientKerEquivOfSurjective (uEv_surjective S)
    exact IsAlgClosed.of_ringEquiv _ _ (e1.trans e2).symm
  exact ⟨B, inferInstance, inferInstance, ψB, hψBflat, hmaxB, hres⟩

/-- **The `U`-part (separable closure over a perfectified ring)**, with the key fibre fact taken
from `Work.DSG4b.uRingKey.uRing_ker_exists_mul_mem` and the flatness of the localisation from the
explicit `RingHom.Flat` instances. -/
theorem gonf_of_perfect (S : Type a) [CommRing S] [IsLocalRing S] (φ : R →+* S)
    (hφ : φ.Flat) (hmax : (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal S)
    [PerfectField (IsLocalRing.ResidueField S)] :
    ∃ (B : Type a) (_ : CommRing B) (_ : IsLocalRing B) (ψ : R →+* B),
      ψ.Flat ∧ (IsLocalRing.maximalIdeal R).map ψ = IsLocalRing.maximalIdeal B ∧
        IsAlgClosed (IsLocalRing.ResidueField B) := by
  classical
  haveI : (RingHom.ker (uEv S)).IsPrime :=
    (RingHom.ker_isMaximal_of_surjective (uEv S) (uEv_surjective S)).isPrime
  let A := uRing S
  let ψA : R →+* A := (uRingAlg S).comp φ
  let B := Localization.AtPrime (RingHom.ker (uEv S))
  let ψB := (algebraMap A B).comp ψA
  have hAflat : (uRingAlg S).Flat := by
    rw [uRingAlg_eq_algebraMap]
    exact RingHom.flat_algebraMap_iff.mpr (uRing_flat S)
  have hABflat : RingHom.Flat (R := A) (S := B) (algebraMap A B) :=
    (RingHom.flat_algebraMap_iff (R := A) (S := B)).mpr
      (IsLocalization.flat B (RingHom.ker (uEv S)).primeCompl)
  have hψAflat : RingHom.Flat (R := R) (S := A) ψA :=
    RingHom.Flat.comp (f := φ) (g := uRingAlg S) hφ hAflat
  have hψBflat : RingHom.Flat (R := R) (S := B) ((algebraMap A B).comp ψA) :=
    RingHom.Flat.comp (R := R) (S := A) (T := B) (f := ψA) (g := algebraMap A B)
      hψAflat hABflat
  exact gonf_of_perfect_aux R S φ hφ hmax (uRingKey.uRing_ker_exists_mul_mem R S φ hmax) ψB
    (fun x => rfl) hψBflat

end UPart

/-- **G4b residue enlargement** (Cohen-free, and with no Noetherian hypothesis on `B`), matching the
lead's frozen node `DSMap.Gaps.gonf_residue`: a Noetherian local ring `R` admits a flat local
`R`-algebra `B` (not required Noetherian) with algebraically closed residue field.

Construction (lead's design, `sources/dsmap/direct_summand_gaps_1013.md` section 2.3):

* (a) if `char (ResidueField R) = p`, choose a `p`-basis `Λ` of `k = ResidueField R` (Zorn); the
  ℕ-indexed tower `R[T_b]/(T_b^{p^n} - b̃)` (`b ∈ Λ`, `b̃` a lift) is free over `R`, hence flat, its
  `m`-fibre is the field `k^{1/p^n}` (a `p`-basis is a `p^n`-basis), so the colimit `R₁` is flat
  local over `R` with `(maximalIdeal R).map = maximalIdeal R₁` and residue field `k^perf`;
* (b) one localisation for the separable closure `L` of `k^perf`: `R₂ = (R₁[T_α : α ∈ L]/(F_α))_n`
  with `F_α` a monic lift of the separable minimal polynomial of `α` over `k^perf` and
  `n = ker(T_α ↦ α)`, whose fibre is a localisation of an ind-finite-étale algebra, hence a field;
  so the residue field is `L`, which is algebraically closed as `k^perf` is perfect.

No well-orders and no Cohen structure theory.  Useful Mathlib facts: `Ring.DirectLimit`
(`Mathlib/Algebra/Colimit/Ring.lean`), `AdicCompletion.flat_of_isNoetherian`,
`IsAdicComplete.henselianRing`, `AlgebraicClosure` (`k̄ : Type u`). -/
theorem gonf_residue_enlargement (R : Type a) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ (B : Type a) (_ : CommRing B) (_ : IsLocalRing B) (ψ : R →+* B),
      ψ.Flat ∧ (IsLocalRing.maximalIdeal R).map ψ = IsLocalRing.maximalIdeal B ∧
        IsAlgClosed (IsLocalRing.ResidueField B) := by
  obtain ⟨S, hSc, hSl, φ, hφ, hmax, hperf⟩ := gonfPerfect.exists_flat_local_perfect_residue R
  exact gonf_of_perfect R S φ hφ hmax

end Work.DSG4b
