/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The compositum of Kummer fields splits completely at a prime where the radicals are local
`ℓ`-th powers

For a number field `L`, a prime `ℓ`, a finite set `T` of finite primes of `L`, a family of units
`b : PrimeIdeal L → Lˣ` and a fixed finite prime `𝔮` of `L`, the compositum
`kummerSup ℓ T b` of the Kummer fields `L(b_P^{1/ℓ})`, `P ∈ T`, splits completely at `𝔮` whenever
each `b_P` is an `ℓ`-th power in the completion `L_𝔮`.

This is the "easy" direction of the local Kummer dichotomy, applied to a whole compositum: the
local degree `[M_𝔓 : L_𝔮] = e · f` is `1` because the completion `M_𝔓` is generated over `L_𝔮` by
the chosen `ℓ`-th roots `α_P` of the `b_P`, and each `α_P` is already in the image of `L_𝔮` (its
quotient by a local `ℓ`-th root of `b_P` is an `ℓ`-th root of unity, and the `ℓ`-th roots of unity
of `M_𝔓` are the images of those of `L`, which lie in the image of `L_𝔮`).
-/
import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Embedding.KummerSup
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.API.localDeg_tower
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.Embedding

open scoped Classical

/-- **The general form.**  Let `M = L(α_i : i ∈ ι)` be generated over the number field `L` by a
family of elements `α_i` which are `ℓ`-th roots of units `b i` that are local `ℓ`-th powers at the
prime `𝔮` of `L`.  Then `M` splits completely at `𝔮`: every prime of `M` above `𝔮` has local
degree `1`.

The proof is the local computation described in the file header; `M` enters only through the
generation hypothesis `hM`. -/
private theorem localDeg_eq_one_of_adjoin_range {L K' : Type*} [Field L] [NumberField L]
    [Field K'] [Algebra L K'] (ℓ : ℕ) (hℓ : ℓ.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ ℓ)
    {ι : Type*} (b : ι → Lˣ) (α : ι → K')
    (hα : ∀ i, α i ^ ℓ = algebraMap L K' (b i : L))
    (𝔮 : NK.Chebotarev.PrimeIdeal L)
    (hloc : ∀ i, ∃ c : (𝔮.adicCompletion L)ˣ,
      algebraMap L (𝔮.adicCompletion L) (b i : L) = (c : 𝔮.adicCompletion L) ^ ℓ)
    (M : IntermediateField L K') (hM : M = IntermediateField.adjoin L (Set.range α))
    [FiniteDimensional L M] [NumberField ↥M]
    (P : NK.Chebotarev.PrimeIdeal ↥M) (hP : P.asIdeal.LiesOver 𝔮.asIdeal) :
    NK.UchidaKummer.localDeg P 𝔮 = 1 := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  letI : Algebra (𝔮.adicCompletion L) (P.adicCompletion ↥M) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔮 P hP)
  haveI hST : IsScalarTower L (𝔮.adicCompletion L) (P.adicCompletion ↥M) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion 𝔮 P hP
  -- The range of the base change `L_𝔮 → M_P` is a subfield of the target.
  let Tgt : Set (P.adicCompletion ↥M) :=
    Set.range (algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M))
  have hadd : ∀ y ∈ Tgt, ∀ y' ∈ Tgt, y + y' ∈ Tgt := by
    rintro y ⟨u, rfl⟩ y' ⟨u', rfl⟩
    exact ⟨u + u', by rw [map_add]⟩
  have hmul : ∀ y ∈ Tgt, ∀ y' ∈ Tgt, y * y' ∈ Tgt := by
    rintro y ⟨u, rfl⟩ y' ⟨u', rfl⟩
    exact ⟨u * u', by rw [map_mul]⟩
  have hinv : ∀ y ∈ Tgt, y⁻¹ ∈ Tgt := by
    rintro y ⟨u, rfl⟩
    exact ⟨u⁻¹, by rw [map_inv₀]⟩
  -- Every element of `M` maps into `Tgt`.
  have key : ∀ (x : K') (hxM : x ∈ M),
      algebraMap ↥M (P.adicCompletion ↥M) ⟨x, hxM⟩ ∈ Tgt := by
    intro x hxM
    have hxA : x ∈ IntermediateField.adjoin L (Set.range α) := hM ▸ hxM
    have hall : ∀ (y : K') (hy : y ∈ IntermediateField.adjoin L (Set.range α))
        (hyM : y ∈ M), algebraMap ↥M (P.adicCompletion ↥M) ⟨y, hyM⟩ ∈ Tgt := by
      intro y hy
      induction hy using IntermediateField.adjoin_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        intro hzM
        obtain ⟨c, hc⟩ := hloc i
        -- the local `ℓ`-th root of `b i`, transported into the target
        have hc0 : (c : 𝔮.adicCompletion L) ≠ 0 := Units.ne_zero c
        have hcF0 : (algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M)
            (c : 𝔮.adicCompletion L)) ≠ 0 := by
          intro h
          exact hc0 ((map_eq_zero_iff _ (RingHom.injective (algebraMap (𝔮.adicCompletion L)
            (P.adicCompletion ↥M)))).mp h)
        -- `α i` is an `ℓ`-th root of `algebraMap L M (b i)` in `M`
        have hpow_elt : (⟨α i, hzM⟩ : ↥M) ^ ℓ = algebraMap L ↥M (b i : L) := by
          apply Subtype.ext
          push_cast
          exact hα i
        -- `(α i)^ℓ = (local root)^ℓ` in the target
        have hL : (algebraMap ↥M (P.adicCompletion ↥M) ⟨α i, hzM⟩) ^ ℓ
            = algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M)
                ((c : 𝔮.adicCompletion L) ^ ℓ) := by
          rw [← map_pow, hpow_elt,
            ← IsScalarTower.algebraMap_apply L ↥M (P.adicCompletion ↥M) (b i : L),
            IsScalarTower.algebraMap_apply L (𝔮.adicCompletion L) (P.adicCompletion ↥M)
              (b i : L),
            hc]
        have h1 : (algebraMap ↥M (P.adicCompletion ↥M) ⟨α i, hzM⟩) ^ ℓ
            = (algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M)
                (c : 𝔮.adicCompletion L)) ^ ℓ :=
          hL.trans (by rw [map_pow])
        have hone : (algebraMap ↥M (P.adicCompletion ↥M) ⟨α i, hzM⟩
            / (algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M)
                (c : 𝔮.adicCompletion L))) ^ ℓ = 1 := by
          rw [div_pow, h1, div_self (pow_ne_zero ℓ hcF0)]
        -- the quotient is an `ℓ`-th root of unity, hence of the form `ζ^j`
        have hζF : IsPrimitiveRoot (algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M)
            (algebraMap L (𝔮.adicCompletion L) ζ)) ℓ :=
          (hζ.map_of_injective (RingHom.injective (algebraMap L (𝔮.adicCompletion L)))).map_of_injective
            (RingHom.injective (algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M)))
        obtain ⟨j, -, hj⟩ := hζF.eq_pow_of_pow_eq_one hone
        refine ⟨(algebraMap L (𝔮.adicCompletion L) ζ) ^ j * (c : 𝔮.adicCompletion L), ?_⟩
        rw [map_mul, map_pow, hj]
        exact div_mul_cancel₀ _ hcF0
      | algebraMap r =>
        intro hrM
        refine ⟨algebraMap L (𝔮.adicCompletion L) r, ?_⟩
        rw [show (⟨algebraMap L K' r, hrM⟩ : ↥M) = algebraMap L ↥M r from Subtype.ext rfl,
          ← IsScalarTower.algebraMap_apply L ↥M (P.adicCompletion ↥M) r,
          IsScalarTower.algebraMap_apply L (𝔮.adicCompletion L) (P.adicCompletion ↥M) r]
      | add z w hz hw ihz ihw =>
        intro hzwM
        have h1 : algebraMap ↥M (P.adicCompletion ↥M) ⟨z + w, hzwM⟩
            = algebraMap ↥M (P.adicCompletion ↥M) ⟨z, hM.symm ▸ hz⟩
              + algebraMap ↥M (P.adicCompletion ↥M) ⟨w, hM.symm ▸ hw⟩ := by
          have hXY : (⟨z + w, hzwM⟩ : ↥M)
              = ⟨z, hM.symm ▸ hz⟩ + ⟨w, hM.symm ▸ hw⟩ := Subtype.ext rfl
          exact hXY ▸ map_add (algebraMap ↥M (P.adicCompletion ↥M)) _ _
        rw [h1]
        exact hadd _ (ihz (hM.symm ▸ hz)) _ (ihw (hM.symm ▸ hw))
      | inv z hz ih =>
        intro hzM
        have h1 : algebraMap ↥M (P.adicCompletion ↥M) ⟨z⁻¹, hzM⟩
            = (algebraMap ↥M (P.adicCompletion ↥M) ⟨z, hM.symm ▸ hz⟩)⁻¹ := by
          have hXY : (⟨z⁻¹, hzM⟩ : ↥M) = (⟨z, hM.symm ▸ hz⟩ : ↥M)⁻¹ := Subtype.ext rfl
          exact hXY ▸ map_inv₀ (algebraMap ↥M (P.adicCompletion ↥M)) _
        rw [h1]
        exact hinv _ (ih (hM.symm ▸ hz))
      | mul z w hz hw ihz ihw =>
        intro hzwM
        have h1 : algebraMap ↥M (P.adicCompletion ↥M) ⟨z * w, hzwM⟩
            = algebraMap ↥M (P.adicCompletion ↥M) ⟨z, hM.symm ▸ hz⟩
              * algebraMap ↥M (P.adicCompletion ↥M) ⟨w, hM.symm ▸ hw⟩ := by
          have hXY : (⟨z * w, hzwM⟩ : ↥M)
              = ⟨z, hM.symm ▸ hz⟩ * ⟨w, hM.symm ▸ hw⟩ := Subtype.ext rfl
          exact hXY ▸ map_mul (algebraMap ↥M (P.adicCompletion ↥M)) _ _
        rw [h1]
        exact hmul _ (ihz (hM.symm ▸ hz)) _ (ihw (hM.symm ▸ hw))
    exact hall x hxA hxM
  -- Hence the base change `L_𝔮 → M_P` is surjective.
  have hsub : Set.range (algebraMap ↥M (P.adicCompletion ↥M)) ⊆ Tgt := by
    rintro y ⟨w, rfl⟩
    exact key w.1 w.2
  have htop : LinearMap.range (Algebra.linearMap (𝔮.adicCompletion L)
      (P.adicCompletion ↥M)) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← NK.UchidaKummer.Kummer.span_range_algebraMap_adicCompletion_eq_top
      (K := L) (L := ↥M) 𝔮 P hP]
    refine le_trans (Submodule.span_mono hsub) ?_
    refine Submodule.span_le.mpr ?_
    rintro y ⟨u, rfl⟩
    exact ⟨u, by rw [Algebra.linearMap_apply]⟩
  have hsurj : Function.Surjective
      (algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M)) := by
    intro y
    have hy : y ∈ LinearMap.range (Algebra.linearMap (𝔮.adicCompletion L)
        (P.adicCompletion ↥M)) := htop ▸ Submodule.mem_top
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hy
    exact ⟨u, by rw [← Algebra.linearMap_apply]; exact hu⟩
  have hinj : Function.Injective
      (algebraMap (𝔮.adicCompletion L) (P.adicCompletion ↥M)) := RingHom.injective _
  have hfr : Module.finrank (𝔮.adicCompletion L) (P.adicCompletion ↥M) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr ⟨hinj, hsurj⟩
  rw [NK.UchidaKummer.localDeg,
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := L) (L := ↥M) 𝔮 P hP]
  exact hfr

/-- **The compositum `kummerSup ℓ T b` splits completely at `𝔮`** when the prescribed local
`ℓ`-power classes of the `b P` at `𝔮` are trivial: if for every `P ∈ T` the unit `b P` is an
`ℓ`-th power in the completion `L_𝔮`, then every prime of the compositum of the Kummer fields
`L((b P)^{1/ℓ})` lying over `𝔮` has local degree `1`. -/
theorem localDeg_eq_one_of_kummerSup {L K' : Type*} [Field L] [NumberField L] [Field K']
    [Algebra L K'] [IsSepClosure L K'] (ℓ : ℕ) (hℓ : ℓ.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ ℓ)
    (T : Finset (NK.Chebotarev.PrimeIdeal L)) (b : NK.Chebotarev.PrimeIdeal L → Lˣ)
    (𝔮 : NK.Chebotarev.PrimeIdeal L)
    (hpow : ∀ P ∈ T, ∃ c : (𝔮.adicCompletion L)ˣ,
      algebraMap L (𝔮.adicCompletion L) ((b P : L)) = (c : 𝔮.adicCompletion L) ^ ℓ)
    [FiniteDimensional L ↥(NK.UchidaKummer.Embedding.kummerSup (K' := K') ℓ T b)]
    [NumberField ↥(NK.UchidaKummer.Embedding.kummerSup (K' := K') ℓ T b)]
    (P : NK.Chebotarev.PrimeIdeal ↥(NK.UchidaKummer.Embedding.kummerSup (K' := K') ℓ T b))
    (hP : P.asIdeal.LiesOver 𝔮.asIdeal) :
    NK.UchidaKummer.localDeg P 𝔮 = 1 := by
  classical
  -- Choose, for each `P ∈ T`, a root in `K'` of `X ^ ℓ - b P`.
  have hroot : ∀ t : ↥T, ∃ α : K', α ^ ℓ = algebraMap L K' ((b t.1 : Lˣ) : L) := fun t =>
    NK.UchidaKummer.Kummer.exists_pow_eq_algebraMap_of_isSepClosure (k := L) (K' := K')
      ℓ hℓ hζ (b t.1)
  choose α hα using hroot
  -- The compositum is generated by these roots.
  have hM : kummerSup (K' := K') ℓ T b = IntermediateField.adjoin L (Set.range α) := by
    rw [kummerSup]
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le_iff.mpr ?_
      intro Q hQ
      rw [NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple ℓ hℓ hζ (b Q) (hα ⟨Q, hQ⟩)]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact IntermediateField.subset_adjoin L (Set.range α) ⟨⟨Q, hQ⟩, rfl⟩
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x ⟨t, rfl⟩
      refine Finset.le_sup (f := fun Q : NK.Chebotarev.PrimeIdeal L =>
        NK.LocalAnabelian.kummerField (K' := K') ℓ (b Q)) t.2 ?_
      rw [NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple ℓ hℓ hζ (b t.1) (hα t)]
      exact IntermediateField.mem_adjoin_simple_self L (α t)
  exact localDeg_eq_one_of_adjoin_range (K' := K') ℓ hℓ hζ (fun t : ↥T => b t.1) α hα 𝔮
    (fun t => hpow t.1 t.2) (kummerSup (K' := K') ℓ T b) hM P hP

end NK.UchidaKummer.Embedding
