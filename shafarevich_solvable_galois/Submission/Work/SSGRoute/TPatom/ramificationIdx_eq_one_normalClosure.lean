import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.Sha2Lib.inertia_map_galRes_eq
import Submission.Work.SSGRoute.TPatom.inertia_le_fixingSubgroup_of_ramificationIdx_eq_one
import Submission.Work.SSGRoute.Sha2Lib.smulHeightOneSpectrum_inv_liesOver
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open scoped NumberField

set_option linter.style.haveILetI false

namespace Work.SSGRoute.TPatom

/-! ## Two elementary helpers

The proof below is organised around the inertias `Ideal.inertia Gal(M/k) P`, an element of which is
carried by conjugation to the inertial elements of the conjugate prime (helper
`mem_inertia_mul_conj`), and around the description of the normal closure as the supremum of the
conjugates of `E` (helper `le_fixingSubgroup_iSup`). -/

section Helpers

variable {k M : Type*} [Field k] [Field M] [Algebra k M]

/-- **The fixing subgroup of a supremum.**  If a subgroup fixes pointwise each member of a family
of intermediate fields, it fixes pointwise their supremum as well. -/
lemma le_fixingSubgroup_iSup {ι : Type*} (f : ι → IntermediateField k M)
    (H : Subgroup (M ≃ₐ[k] M)) (h : ∀ i, H ≤ (f i).fixingSubgroup) :
    H ≤ (⨆ i, f i).fixingSubgroup := by
  rw [← IntermediateField.le_iff_le H (⨆ i, f i)]
  exact iSup_le fun i => (IntermediateField.le_iff_le H (f i)).mpr (h i)

end Helpers

section Conjugation

variable {G R : Type*} [Ring R] [Group G] [MulSemiringAction G R]

/-- **Conjugation of the inertia subgroup.**  If `γ` is inertial at the prime `P`, then its
conjugate `τ * γ * τ⁻¹` is inertial at the translate `τ • P`. -/
lemma mem_inertia_mul_conj (P : Ideal R) (τ : G) {γ : G} (hγ : γ ∈ Ideal.inertia G P) :
    τ * γ * τ⁻¹ ∈ Ideal.inertia G (τ • P) := by
  show ∀ x, (τ * γ * τ⁻¹) • x - x ∈ τ • P
  intro x
  have hmem : γ • (τ⁻¹ • x) - τ⁻¹ • x ∈ P := hγ (τ⁻¹ • x)
  have h := Ideal.smul_mem_pointwise_smul τ (γ • (τ⁻¹ • x) - τ⁻¹ • x) P hmem
  simpa only [smul_sub, mul_smul, smul_inv_smul] using h

end Conjugation

section Actions

variable {k M : Type*} [Field k] [NumberField k] [Field M] [NumberField M] [Algebra k M]

/-- **The two Galois actions on the primes of `𝓞 M` agree**: the pointwise (`Pointwise` locale)
action of `Gal(M/k)` on ideals agrees with the action used for the places of `M`. -/
lemma pointwise_smul_asIdeal (τ : M ≃ₐ[k] M)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M)) :
    (τ • P.asIdeal : Ideal (NumberField.RingOfIntegers M)) =
      (NK.GlobalCFT.Place.smulHeightOneSpectrum τ P).asIdeal := by
  rw [Ideal.pointwise_smul_def, NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
  congr 1

end Actions

/-- **The normal closure of an extension unramified at all primes over `p` is unramified at all
primes over `p`.**

Let `k ⊆ M` be a finite Galois extension of number fields, `E` an intermediate field, and `p` a
nonzero prime of `𝓞 k`.  If every prime `q` of `𝓞 E` over `p` has ramification index `1` over `p`,
then the same holds for every prime of the normal closure `F := IntermediateField.normalClosure k E M`
over `p`.

Proof sketch: `F = ⨆_{τ ∈ Gal(F/k)} τ(E)` (the conjugates of `E` generate the normal closure, since
their supremum is stable under `Gal(F/k)`, hence Galois over `k`, and contains `E`).  For each `τ`,
`e(Q | Q ∩ 𝓞(τE)) = 1` because `Q ∩ 𝓞(τE)` is the `τ`-image of a prime of `E` over `p`
(automorphisms fixing `k` preserve the contraction to `k`, and `ramificationIdx` is invariant under
`τ`).  With `G = Gal(F/k)`, `H_τ := (τE).fixingSubgroup`, the tower formula
`Ideal.ramificationIdx_tower` gives `e(Q|p) = e(Q | Q ∩ 𝓞(τE))`,
`Ideal.card_inertia_eq_ramificationIdxIn` (applied to `F/k` and to `F/τE`, the latter after
transporting along `IntermediateField.fixingSubgroupEquiv` with `Ideal.inertiaEquiv`) identifies
`|Ideal.inertia G Q| = e(Q|p)` and `|Ideal.inertia G Q ⊓ H_τ| = e(Q | Q ∩ 𝓞(τE))`, hence
`Ideal.inertia G Q ≤ H_τ`; intersecting over all `τ` (using
`IntermediateField.fixingSubgroup_sup`) gives `Ideal.inertia G Q ≤ (⊤).fixingSubgroup = ⊥`, so
`e(Q|p) = |Ideal.inertia G Q| = 1`. -/
theorem ramificationIdx_eq_one_normalClosure {k M : Type} [Field k] [NumberField k] [Field M]
    [NumberField M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
    (E : IntermediateField k M) [FiniteDimensional k E]
    [FiniteDimensional k ↥(IntermediateField.normalClosure k E M)]
    [NumberField ↥(IntermediateField.normalClosure k E M)]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hE : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
      q.asIdeal.LiesOver p.asIdeal → q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    ∀ Q : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(IntermediateField.normalClosure k E M)),
      Q.asIdeal.LiesOver p.asIdeal →
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
  intro Q hQ
  -- ## A prime of `𝓞 M` above `Q`
  obtain ⟨P₀, hP₀max, hP₀comap⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := NumberField.RingOfIntegers
        ↥(IntermediateField.normalClosure k E M)) (S := NumberField.RingOfIntegers M) Q.asIdeal
  haveI hP₀lies : P₀.LiesOver Q.asIdeal := hP₀comap
  have hP₀prime : P₀.IsPrime := hP₀max.isPrime
  have hP₀ne : P₀ ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot Q.ne_bot P₀
  let P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M) :=
    ⟨P₀, hP₀prime, hP₀ne⟩
  have hPQ : P.asIdeal.LiesOver Q.asIdeal := hP₀lies
  have hPp : P.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    rw [hQ.over, hPQ.over, Ideal.under_under]
  -- ## The inertia of `P` in `Gal(M/k)` fixes the normal closure pointwise
  have hfix : ∀ σ : M ≃ₐ[k] M, Ideal.inertia (M ≃ₐ[k] M) P.asIdeal
      ≤ (E.map (σ : M →ₐ[k] M)).fixingSubgroup := by
    intro σ
    -- the conjugate prime `σ⁻¹ • P`
    set P' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M) :=
      NK.GlobalCFT.Place.smulHeightOneSpectrum σ⁻¹ P with hP'def
    have hP'eq : (σ⁻¹ • P.asIdeal : Ideal (NumberField.RingOfIntegers M)) = P'.asIdeal :=
      pointwise_smul_asIdeal σ⁻¹ P
    have hP'p : P'.asIdeal.LiesOver p.asIdeal := by
      refine ⟨?_⟩
      rw [hP'def, Work.SSGRoute.Sha2Lib.under_smulHeightOneSpectrum σ⁻¹ P, hPp.over]
    -- the prime of `𝓞 E` below `P'`
    have hunder : (Ideal.under (NumberField.RingOfIntegers ↥E) P'.asIdeal).LiesOver
        p.asIdeal := by
      refine ⟨?_⟩
      rw [Ideal.under_under, hP'p.over]
    haveI hunderI : (Ideal.under (NumberField.RingOfIntegers ↥E) P'.asIdeal).LiesOver
        p.asIdeal := hunder
    have hqne : Ideal.under (NumberField.RingOfIntegers ↥E) P'.asIdeal ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _
    have hram : (Ideal.under (NumberField.RingOfIntegers ↥E) P'.asIdeal).ramificationIdx
        (NumberField.RingOfIntegers k) = 1 :=
      hE ⟨Ideal.under (NumberField.RingOfIntegers ↥E) P'.asIdeal,
        Ideal.IsPrime.under _ P'.asIdeal, hqne⟩ hunder
    have hle : Ideal.inertia (M ≃ₐ[k] M) P'.asIdeal ≤ E.fixingSubgroup :=
      inertia_le_fixingSubgroup_of_ramificationIdx_eq_one E P' hram
    intro γ hγ
    have h1 : σ⁻¹ * γ * σ ∈ Ideal.inertia (M ≃ₐ[k] M) (σ⁻¹ • P.asIdeal) :=
      mem_inertia_mul_conj P.asIdeal σ⁻¹ hγ
    rw [hP'eq] at h1
    have h2 : σ⁻¹ * γ * σ ∈ E.fixingSubgroup := hle h1
    rw [IntermediateField.mem_fixingSubgroup_iff] at h2 ⊢
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (IntermediateField.mem_map E).mp hy
    have h3 : (σ⁻¹ * γ * σ) x = x := h2 x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h3
    have h4 : σ (σ⁻¹ (γ (σ x))) = σ x := by rw [h3]
    simpa using h4
  have key : Ideal.inertia (M ≃ₐ[k] M) P.asIdeal
      ≤ (IntermediateField.normalClosure k E M).fixingSubgroup := by
    rw [IntermediateField.normalClosure_def'' E]
    exact le_fixingSubgroup_iSup (fun σ : M ≃ₐ[k] M => E.map (σ : M →ₐ[k] M))
      (Ideal.inertia (M ≃ₐ[k] M) P.asIdeal) hfix
  -- ## The inertia of `Q` in `Gal(F/k)` is trivial
  have hbot : Ideal.inertia (↥(IntermediateField.normalClosure k E M) ≃ₐ[k]
      ↥(IntermediateField.normalClosure k E M)) Q.asIdeal = ⊥ := by
    rw [← Work.Sha2Lib.inertia_map_galRes_eq (k := k)
      (K := ↥(IntermediateField.normalClosure k E M)) (L := M) Q P hPQ]
    exact (Subgroup.map_eq_bot_iff _).mpr (by
      rw [IntermediateField.restrictNormalHom_ker]
      exact key)
  exact (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
    (F := k) (K := ↥(IntermediateField.normalClosure k E M)) p.asIdeal Q.asIdeal).mp hbot

end Work.SSGRoute.TPatom
