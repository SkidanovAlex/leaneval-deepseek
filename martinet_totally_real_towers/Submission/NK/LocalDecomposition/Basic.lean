/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Group theory of decomposition groups: disjointness, normalizers, cores

This file contains the *proved* group-theoretic part of the reduction of Neukirch's
decomposition-group criterion:

* `NK.LocalDecomposition.stabSubgroup_inf_eq_bot_of_ne` — **the decomposition groups of distinct
  places of `K'` over finite primes of `K` intersect trivially** (CoNF XII (12.1.3)).  This is the
  sharp form of "distinct places have disjoint decomposition groups"; it is proved in the commons
  (`Submission/Commons/NumberTheory/NumberField/Valuation/`).

* `NK.LocalDecomposition.normalizer_le_of_ne_bot` — the **normalizer property** (A. Ivanov,
  arXiv:1309.2801, Corollary `FKSnormalizerproperty`(i), in the sharp form available in the
  number-field case): the normalizer of a *non-trivial* subgroup of a decomposition group is again
  contained in that decomposition group.

* `NK.LocalDecomposition.coreIn` and its API — the largest subgroup of `H₀` normalised by `H`
  (the `H`-core of `H₀`).

* `NK.LocalDecomposition.le_stabSubgroup_of_openSubgroup_le` — **Ivanov's `lm:finindexlm`**
  (Neukirch's argument, cf. CoNF (12.1.10)): if an open subgroup `H₀` of `H` is contained in the
  decomposition group `D_A` of a place over a finite prime, then already `H ≤ D_A`.  This is the
  passage from the *open subgroup* produced by the localisation argument
  (`NK.LocalDecomposition.IndecomposedPrime`) to a containment of the whole group `H`.
-/
import Submission.NK.LocalDecomposition.Defs
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
import Submission.Commons.NumberTheory.NumberField.Valuation.normalizer_stabilizer_valuationSubring_sepClosure
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false


open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.LocalDecomposition

noncomputable section

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **Disjointness of the decomposition groups of distinct places** (CoNF XII (12.1.3)): two
distinct places of `K'` over finite primes of `K` have trivial decomposition groups in common. -/
theorem stabSubgroup_inf_eq_bot_of_ne {A A' : ValuationSubring K'} (hne : A ≠ A')
    (hA : A.comap (algebraMap K K') ≠ ⊤) (hA' : A'.comap (algebraMap K K') ≠ ⊤) :
    MulAction.stabilizer Gal(K'/K) A ⊓ MulAction.stabilizer Gal(K'/K) A' = ⊥ :=
  Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne hne hA hA'

/-- A place and its image under `x ∈ Gal(K'/K)` have the same restriction to the base field. -/
theorem comap_smul (A : ValuationSubring K') (x : Gal(K'/K)) :
    (x • A).comap (algebraMap K K') = A.comap (algebraMap K K') :=
  Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A x

/-- The stabiliser of a place and of its image under a Galois automorphism are conjugate. -/
theorem stabSubgroup_smul (A : ValuationSubring K') (x : Gal(K'/K)) :
    MulAction.stabilizer Gal(K'/K) (x • A) = (MulAction.stabilizer Gal(K'/K) A).map (MulAut.conj x).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj x A

/-- **The decomposition group of a place is closed** in the Krull topology. -/
theorem isClosed_stabSubgroup (A : ValuationSubring K') :
    IsClosed ((MulAction.stabilizer Gal(K'/K) A : Set Gal(K'/K))) :=
  Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A

/-- **The normalizer of a non-trivial subgroup of a decomposition group stays inside it.**

Let `A` be a place of `K'` over a finite prime of `K` and let `H ≤ D_A` be non-trivial.  Then
`N(H) ≤ D_A`: for `x ∈ N(H)` one has `H = xHx⁻¹ = x D_A x⁻¹ = D_{xA}` as well as `H ≤ D_A`, so
`H ≤ D_A ∩ D_{xA} = ⊥` whenever `xA ≠ A`, contradicting `H ≠ ⊥`. -/
theorem normalizer_le_of_ne_bot (A : ValuationSubring K') (hA : A.comap (algebraMap K K') ≠ ⊤)
    (H : Subgroup Gal(K'/K)) (hHne : H ≠ ⊥) (hHle : H ≤ MulAction.stabilizer Gal(K'/K) A) :
    Subgroup.normalizer H ≤ MulAction.stabilizer Gal(K'/K) A := by
  intro x hx
  have hxmap : H.map (MulAut.conj x).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hHx : H ≤ MulAction.stabilizer Gal(K'/K) (x • A) := by
    rw [stabSubgroup_smul, ← hxmap]
    exact Subgroup.map_mono hHle
  by_cases hxA : x • A = A
  · rw [MulAction.mem_stabilizer_iff]; exact hxA
  · exfalso
    have hbot : MulAction.stabilizer Gal(K'/K) A ⊓ MulAction.stabilizer Gal(K'/K) (x • A) = ⊥ :=
      stabSubgroup_inf_eq_bot_of_ne (Ne.symm hxA) hA (by rw [comap_smul]; exact hA)
    exact hHne (eq_bot_iff.mpr (hbot ▸ le_inf hHle hHx))

/-- **A decomposition group is self-normalising** (CoNF XII (12.1.4), normaliser form; the "only
if" half of the characterisation (12.1.9) of decomposition groups): an element of `Gal(K'/K)`
normalising the decomposition group of a place over a finite prime already lies in it. -/
theorem normalizer_stabSubgroup_eq (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') ≠ ⊤) :
    Subgroup.normalizer (MulAction.stabilizer Gal(K'/K) A) =
      MulAction.stabilizer Gal(K'/K) A := by
  obtain ⟨𝔭, h𝔭⟩ := exists_heightOneSpectrum_eq_comap A hA
  have htop : A.comap (algebraMap K K') ≠ ⊤ := by
    rw [h𝔭]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔭
  refine le_antisymm ?_ Subgroup.le_normalizer
  intro σ hσ
  have hconj : ∀ τ ∈ MulAction.stabilizer Gal(K'/K) A,
      σ * τ * σ⁻¹ ∈ MulAction.stabilizer Gal(K'/K) A := fun τ hτ =>
    ((Subgroup.mem_normalizer_iff (H := MulAction.stabilizer Gal(K'/K) A) (g := σ)).mp
      hσ τ).mp hτ
  refine (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer
    (K := K) (K' := K') A σ).mp ?_
  exact Commons.NumberTheory.NumberField.Valuation.normalizer_stabilizer_valuationSubring_sepClosure
    𝔭 A h𝔭 σ fun τ hτ =>
      (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer
        (K := K) (K' := K') A (σ * τ * σ⁻¹)).mpr
        (hconj τ ((Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer
          (K := K) (K' := K') A τ).mp hτ))

/-- **The `H`-core of `H₀`**: the largest subgroup of `H₀` normalised by `H`, i.e. the intersection
of the `H`-conjugates of `H₀`.  It is the subgroup used in Ivanov's argument to pass from an open
subgroup `H₀ ≤ H` to a subgroup normal in `H`. -/
def coreIn (H H₀ : Subgroup Gal(K'/K)) : Subgroup Gal(K'/K) where
  carrier := {x | x ∈ H ∧ ∀ h ∈ H, h * x * h⁻¹ ∈ H₀}
  one_mem' := ⟨H.one_mem, fun h _ => by rw [mul_one, mul_inv_cancel]; exact H₀.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨H.mul_mem hx.1 hy.1, fun h hh => ?_⟩
    have hconj : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [hconj]
    exact H₀.mul_mem (hx.2 h hh) (hy.2 h hh)
  inv_mem' := by
    intro x hx
    refine ⟨H.inv_mem hx.1, fun h hh => ?_⟩
    have hconj : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [hconj]
    exact H₀.inv_mem (hx.2 h hh)

theorem coreIn_le_right (H H₀ : Subgroup Gal(K'/K)) : coreIn H H₀ ≤ H₀ :=
  fun _ hx => by simpa using hx.2 1 H.one_mem

theorem coreIn_le_left (H H₀ : Subgroup Gal(K'/K)) : coreIn H H₀ ≤ H := fun _ hx => hx.1

/-- The `H`-core of `H₀` is normal in `H`. -/
theorem le_normalizer_coreIn (H H₀ : Subgroup Gal(K'/K)) :
    H ≤ Subgroup.normalizer (coreIn H H₀) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    refine ⟨H.mul_mem (H.mul_mem hx hy.1) (H.inv_mem hx), fun h hh => ?_⟩
    have h1 : h * (x * y * x⁻¹) * h⁻¹ = (h * x) * y * (h * x)⁻¹ := by group
    rw [h1]
    exact hy.2 (h * x) (H.mul_mem hh hx)
  · intro hy
    refine ⟨?_, fun h hh => ?_⟩
    · have h2 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [h2]
      exact H.mul_mem (H.mul_mem (H.inv_mem hx) hy.1) hx
    · have h3 : h * y * h⁻¹ = (h * x⁻¹) * (x * y * x⁻¹) * (h * x⁻¹)⁻¹ := by group
      rw [h3]
      exact hy.2 (h * x⁻¹) (H.mul_mem hh (H.inv_mem hx))

/-- The `H`-core of `H₀` agrees with the normal core of `H₀` inside the group `H`. -/
theorem coreIn_eq_normalCore_map (H H₀ : Subgroup Gal(K'/K)) :
    coreIn H H₀ = (Subgroup.normalCore (H₀.subgroupOf H)).map H.subtype := by
  ext x
  constructor
  · rintro ⟨hx, hprop⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    intro b
    exact hprop (b : Gal(K'/K)) b.2
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun h hh => hy ⟨h, hh⟩⟩

/-- The `H`-core of a finite-index subgroup of `H` has finite index in `H`. -/
theorem coreIn_relIndex_pos (H H₀ : Subgroup Gal(K'/K)) (h : 0 < H₀.relIndex H) :
    0 < (coreIn H H₀).relIndex H := by
  have hfin : (H₀.subgroupOf H).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    exact ne_of_gt h
  haveI := hfin
  haveI : (Subgroup.normalCore (H₀.subgroupOf H)).FiniteIndex := inferInstance
  have hpos : 0 < (Subgroup.normalCore (H₀.subgroupOf H)).index :=
    Nat.pos_of_ne_zero (Subgroup.finiteIndex_iff.mp (inferInstance : (Subgroup.normalCore (H₀.subgroupOf H)).FiniteIndex))
  have hrel : (coreIn H H₀).relIndex H =
      (Subgroup.normalCore (H₀.subgroupOf H)).index := by
    rw [coreIn_eq_normalCore_map H H₀, Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [hrel]; exact hpos

/-- **Ivanov's `lm:finindexlm`** (Neukirch's argument, cf. CoNF (12.1.10)): if an open subgroup `H₀`
of `H` is contained in the decomposition group of a place `A` over a finite prime of `K`, and `H` is
infinite, then `H ≤ D_A`.

Proof.  Replace `H₀` by its `H`-core `C` (normal in `H`, of finite index in `H`, still contained in
`H₀ ⊆ D_A`).  Since `H` is infinite and `[H : C]` is finite, `C ≠ ⊥`; hence by
`normalizer_le_of_ne_bot` the normalizer of `C` lies in `D_A`, and `H ≤ N(C)`. -/
theorem le_stabSubgroup_of_openSubgroup_le (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') ≠ ⊤) (H H₀ : Subgroup Gal(K'/K)) (hH₀le : H₀ ≤ H)
    (hfin : 0 < H₀.relIndex H) (hinf : Nat.card ↥H = 0) (hH₀ : H₀ ≤ MulAction.stabilizer Gal(K'/K) A) :
    H ≤ MulAction.stabilizer Gal(K'/K) A := by
  have hcorele : coreIn H H₀ ≤ MulAction.stabilizer Gal(K'/K) A :=
    le_trans (coreIn_le_right H H₀) hH₀
  have hrel : 0 < (coreIn H H₀).relIndex H := coreIn_relIndex_pos H H₀ hfin
  have hne : coreIn H H₀ ≠ ⊥ := by
    intro hbot
    have hcard : (coreIn H H₀).relIndex H = Nat.card ↥H := by
      rw [hbot, Subgroup.relIndex, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    rw [hcard, hinf] at hrel
    exact absurd hrel (lt_irrefl 0)
  exact le_trans (le_normalizer_coreIn H H₀)
    (normalizer_le_of_ne_bot A hA (coreIn H H₀) hne hcorele)

end

end NK.LocalDecomposition
