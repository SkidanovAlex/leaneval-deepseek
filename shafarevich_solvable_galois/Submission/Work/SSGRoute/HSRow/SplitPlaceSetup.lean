import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.UchidaKummer.Embedding.KummerSup
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer level of a split place: setup

Vocabulary for the construction of the regular-module Kummer level at a place `q` of `K` which
splits completely in `K/k` (`decompK w = ⊥`).

Fix a prime `p`, number fields `k ⊆ K` with `K/k` finite Galois, an ambient field `Ω` with
`K → Ω`, a prime `q` of `𝓞 K`, and `α ∈ Kˣ`.

* `conjUnit τ α` is the conjugate `τ α ∈ Kˣ`;
* `orbitFinset q` is the finite set of primes `τ • q` (`τ : Gal(K/k)`);
* `kummerLevel p q α` is the compositum `K((τ α)^{1/p} : τ)` of the Kummer fields — realised as
  `NK.UchidaKummer.Embedding.kummerSup p (orbitFinset q) (conjUnitAt q α)` so that the degree
  statement `NK.UchidaKummer.Embedding.finrank_kummerSup` applies directly;
* `kummerLevel_eq_sup` identifies it with the sup over `τ` of `kummerField p (τ α)`, under the
  hypothesis that the orbit map `τ ↦ τ • q` is injective (which holds when `decompK w = ⊥`).
-/

open scoped Classical
open IntermediateField

namespace Work.SSGRoute.HSRow

noncomputable section

/-- The conjugate of a global unit `α` under `τ : Gal(K/k)`. -/
def conjUnit {k K : Type*} [Field k] [Field K] [Algebra k K] (τ : K ≃ₐ[k] K) (α : Kˣ) : Kˣ :=
  Units.map (AlgEquiv.toRingEquiv τ).toMonoidHom α

@[simp]
theorem conjUnit_coe {k K : Type*} [Field k] [Field K] [Algebra k K] (τ : K ≃ₐ[k] K) (α : Kˣ) :
    ((conjUnit τ α : Kˣ) : K) = τ ((α : Kˣ) : K) := rfl

@[simp]
theorem conjUnit_one {k K : Type*} [Field k] [Field K] [Algebra k K] :
    conjUnit (1 : K ≃ₐ[k] K) = MonoidHom.id Kˣ := rfl

theorem conjUnit_mul {k K : Type*} [Field k] [Field K] [Algebra k K] (τ τ' : K ≃ₐ[k] K)
    (α : Kˣ) : conjUnit (τ * τ') α = conjUnit τ (conjUnit τ' α) := rfl

variable {k K Ω : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-- The finite set of primes of `K` above `q ∩ k`, i.e. the orbit of `q` under `Gal(K/k)`. -/
def orbitFinset (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  classical
  exact Finset.univ.image (fun τ : K ≃ₐ[k] K => NK.GlobalCFT.Place.smulHeightOneSpectrum τ q)

/-- The family `𝔮 ↦ τ α` for `𝔮 = τ • q` (and `1` away from the orbit). -/
def conjUnitAt (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (α : Kˣ) : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Kˣ :=
  fun 𝔮 => by
    classical
    exact if h : ∃ τ : K ≃ₐ[k] K, NK.GlobalCFT.Place.smulHeightOneSpectrum τ q = 𝔮
      then conjUnit (Classical.choose h) α else 1

/-- The Kummer level of `α`: the compositum over the primes `𝔮 = τ • q` of the Kummer fields
`K((τ α)^{1/p})`, realised through `kummerSup` so that the degree formula applies. -/
def kummerLevel (p : ℕ) (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (α : Kˣ) : IntermediateField K Ω :=
  NK.UchidaKummer.Embedding.kummerSup p (orbitFinset (k := k) (K := K) q)
    (conjUnitAt (k := k) (K := K) q α)

theorem kummerLevel_def (p : ℕ)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (α : Kˣ) :
    kummerLevel (k := k) (K := K) (Ω := Ω) p q α =
      (orbitFinset (k := k) (K := K) q).sup
        (fun 𝔮 => NK.LocalAnabelian.kummerField (K' := Ω) p
          (conjUnitAt (k := k) (K := K) q α 𝔮)) :=
  rfl

/-- The orbit is a genuine orbit: `τ • q ∈ orbitFinset q`. -/
theorem smulHeightOneSpectrum_mem_orbitFinset
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (τ : K ≃ₐ[k] K) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum τ q ∈ orbitFinset (k := k) (K := K) q := by
  classical
  rw [orbitFinset]
  exact Finset.mem_image.mpr ⟨τ, Finset.mem_univ τ, rfl⟩

/-- The family `conjUnitAt q α` takes the value `τ α` at `τ • q`. -/
theorem conjUnitAt_smul (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (α : Kˣ) (τ : K ≃ₐ[k] K)
    (hstab : ∀ τ τ' : K ≃ₐ[k] K,
      NK.GlobalCFT.Place.smulHeightOneSpectrum τ q =
        NK.GlobalCFT.Place.smulHeightOneSpectrum τ' q → τ = τ') :
    conjUnitAt (k := k) (K := K) q α (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q) =
      conjUnit τ α := by
  classical
  have h : ∃ τ' : K ≃ₐ[k] K,
      NK.GlobalCFT.Place.smulHeightOneSpectrum τ' q =
        NK.GlobalCFT.Place.smulHeightOneSpectrum τ q := ⟨τ, rfl⟩
  rw [conjUnitAt, dif_pos h]
  exact congrArg (fun σ => conjUnit σ α)
    (hstab (Classical.choose h) τ (Classical.choose_spec h))

/-- The level is the sup of the Kummer fields of the conjugates of `α`. -/
theorem kummerLevel_eq_sup (p : ℕ)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (α : Kˣ)
    (hstab : ∀ τ τ' : K ≃ₐ[k] K,
      NK.GlobalCFT.Place.smulHeightOneSpectrum τ q =
        NK.GlobalCFT.Place.smulHeightOneSpectrum τ' q → τ = τ') :
    kummerLevel (k := k) (K := K) (Ω := Ω) p q α =
      ⨆ τ : K ≃ₐ[k] K, NK.LocalAnabelian.kummerField (K' := Ω) p (conjUnit τ α) := by
  classical
  rw [kummerLevel_def, Finset.sup_eq_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun 𝔮 => iSup_le fun h𝔮 => ?_
    rw [orbitFinset, Finset.mem_image] at h𝔮
    obtain ⟨σ, -, hσ⟩ := h𝔮
    subst hσ
    rw [conjUnitAt_smul (k := k) (K := K) q α σ hstab]
    exact le_iSup (fun τ : K ≃ₐ[k] K =>
      NK.LocalAnabelian.kummerField (K' := Ω) p (conjUnit τ α)) σ
  · refine iSup_le fun τ => ?_
    refine le_iSup_of_le (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q) ?_
    refine le_iSup_of_le (smulHeightOneSpectrum_mem_orbitFinset (k := k) (K := K) q τ) ?_
    rw [conjUnitAt_smul (k := k) (K := K) q α τ hstab]

theorem kummerField_le_kummerLevel (p : ℕ)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (α : Kˣ)
    (hstab : ∀ τ τ' : K ≃ₐ[k] K,
      NK.GlobalCFT.Place.smulHeightOneSpectrum τ q =
        NK.GlobalCFT.Place.smulHeightOneSpectrum τ' q → τ = τ')
    (τ : K ≃ₐ[k] K) :
    NK.LocalAnabelian.kummerField (K' := Ω) p (conjUnit τ α) ≤
      kummerLevel (k := k) (K := K) (Ω := Ω) p q α := by
  rw [kummerLevel_eq_sup (k := k) (K := K) (Ω := Ω) p q α hstab]
  exact le_iSup (fun τ : K ≃ₐ[k] K =>
    NK.LocalAnabelian.kummerField (K' := Ω) p (conjUnit τ α)) τ

end

end Work.SSGRoute.HSRow
