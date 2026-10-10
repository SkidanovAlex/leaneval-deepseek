import Mathlib.Tactic.Have
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.AdjustId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.spanUnit_mem_principalRayId_of_mem_congruenceSubgroupId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NK.GlobalCFT NK.CFTLib.ArtinReciprocityIdeal

/-- **Dictionary lemma: the ℕ-norm group `𝔑(M)` of a small principal modulus is contained in the
ideal-modulus norm ray `𝔑(𝔪)`.**  This is the "easy" direction of the dictionary between
`NK.CFTLib.ARL.normIdeals K L M` and `normRayId 𝔪` for `(M) ⊆ 𝔪`: a generator of the former is
the norm of an ideal coprime to `(M)𝓞 L`, and since `(M)𝓞 L ⊆ 𝔪𝓞 L` such an ideal is also coprime
to `𝔪𝓞 L`, hence a generator of the latter. -/
theorem normIdeals_le_normRayId_of_span_le_aux
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (M : ℕ) (hM : 0 < M)
    (hle : Ideal.span {(M : NumberField.RingOfIntegers K)} ≤ 𝔪) :
    NK.CFTLib.ARL.normIdeals K L M ≤
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  classical
  rw [NK.CFTLib.ARL.normIdeals, Subgroup.closure_le]
  rintro A ⟨𝔅, rfl⟩
  refine Subgroup.subset_closure ⟨𝔅.1, 𝔅.2.1, ?_, ?_⟩
  · -- the ideal `𝔅.1` is coprime to `𝔪𝓞 L`
    intro 𝔓 h𝔓
    have hMmem : (M : 𝓞 L) ∈ 𝔓.asIdeal := by
      have h1 : (M : 𝓞 K) ∈ 𝔪 := hle (Ideal.subset_span (Set.mem_singleton _))
      have h2 : algebraMap (𝓞 K) (𝓞 L) (M : 𝓞 K) ∈ 𝔓.asIdeal :=
        h𝔓 (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h1)
      rwa [map_natCast] at h2
    have hndvd : ¬ 𝔓.asIdeal ∣ 𝔅.1 := 𝔅.2.2 𝔓 hMmem
    have h1 : ¬ (1 ≤ FractionalIdeal.count L 𝔓 (𝔅.1 : FractionalIdeal (𝓞 L)⁰ L)) :=
      fun h => hndvd
        ((dvdPrime_iff_dvd' (𝔪 := 𝔅.1) (𝔭 := 𝔓)).mp
          ((dvdPrime_iff_one_le_count 𝔅.2.1 𝔓).mpr h))
    have h2 : 0 ≤ FractionalIdeal.count L 𝔓 (𝔅.1 : FractionalIdeal (𝓞 L)⁰ L) :=
      FractionalIdeal.count_coe_nonneg L 𝔓 𝔅.1
    show FractionalIdeal.count L 𝔓
      ((idealUnit 𝔅.1 𝔅.2.1 : Frac L) : FractionalIdeal (𝓞 L)⁰ L) = 0
    rw [show ((idealUnit 𝔅.1 𝔅.2.1 : Frac L) : FractionalIdeal (𝓞 L)⁰ L)
        = (𝔅.1 : FractionalIdeal (𝓞 L)⁰ L) from rfl]
    omega
  · -- the two `Units` have the same underlying fractional ideal
    apply Units.ext
    rfl

/-- **The ideal of an idèle whose norm is congruent to `1` modulo `𝔪` lies in the norm ray
`𝔑(𝔪)`.**  Here `y ∈ U(M)` for a natural modulus `M` with `(M) ⊆ 𝔪`, so that `idealOf y` is
coprime to `𝔪𝓞 L`; hence `relNormUnit (idealOf y) ∈ normIdeals K L M ≤ normRayId 𝔪`
(`NK.CFTLib.ARL.relNormUnit_mem_normIdeals` and `normIdeals_le_normRayId_of_span_le_aux`), and
`idealOf (N y) = relNormFI (idealOf y)` (`NK.CFTLib.ARL.idealOf_normIdeleHom`). -/
theorem idealOfUnitHom_normIdeleHom_mem_normRayId_aux
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (M : ℕ) (hM : 0 < M)
    (hle : Ideal.span {(M : NumberField.RingOfIntegers K)} ≤ 𝔪)
    {y : NK.GlobalCFT.Idele L}
    (hy : y ∈ NK.CFTLib.Arl.congruenceSubgroup L M) :
    NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K (NK.GlobalCFT.Idele.normIdeleHom K L y) ∈
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  classical
  have hA : ∀ 𝔓 : HeightOneSpectrum (𝓞 L), (M : 𝓞 L) ∈ 𝔓.asIdeal →
      FractionalIdeal.count L 𝔓 (Units.mk0 (NK.GlobalCFT.Idele.idealOf y)
        (NK.GlobalCFT.Idele.idealOf_ne_zero y) : FractionalIdeal (𝓞 L)⁰ L) = 0 := by
    intro 𝔓 h𝔓
    rw [Units.val_mk0]
    exact NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence hy 𝔓 h𝔓
  have hmemN := NK.CFTLib.ARL.relNormUnit_mem_normIdeals (K := K) (L := L) M
    (A := Units.mk0 (NK.GlobalCFT.Idele.idealOf y)
      (NK.GlobalCFT.Idele.idealOf_ne_zero y)) hA
  have hmemR := normIdeals_le_normRayId_of_span_le_aux 𝔪 M hM hle hmemN
  convert hmemR using 1
  apply Units.ext
  simp only [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, NK.CFTLib.ARL.relNormUnit]
  exact NK.CFTLib.ARL.idealOf_normIdeleHom y

theorem idealOf_mem_principalRayId_sup_normRayId
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    {y : NK.GlobalCFT.Idele L} {β : Kˣ} {z : NK.GlobalCFT.Idele K}
    (hz : z ∈ NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪)
    (hzy : z = NK.GlobalCFT.Idele.normIdeleHom K L y *
      NK.GlobalCFT.Idele.principalIdele K β) :
    NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K z ∈
      NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  classical
  -- The natural modulus `M = absNorm 𝔪` satisfies `(M) ⊆ 𝔪`, hence `U(M) ≤ U(𝔪)`.
  have hMpos : 0 < Ideal.absNorm 𝔪 :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨𝔪, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using h𝔪)⟩
  have hle : Ideal.span {(Ideal.absNorm 𝔪 : 𝓞 K)} ≤ 𝔪 :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.absNorm_mem 𝔪))
  -- Step 1: adjust `y` in `L` so that `y' = y · (d) ∈ U(M)`.
  obtain ⟨d, hd⟩ := NK.CFTLib.ARL.exists_adjust_congruenceSubgroup L (Ideal.absNorm 𝔪) hMpos y
  set y' : NK.GlobalCFT.Idele L := y * NK.GlobalCFT.Idele.principalIdele L d with hy'def
  have hd' : y' ∈ NK.CFTLib.Arl.congruenceSubgroup L (Ideal.absNorm 𝔪) := hd
  -- Step 2: `N y' ∈ U(M) ⊆ U(𝔪)`.
  have hNyM : NK.GlobalCFT.Idele.normIdeleHom K L y' ∈
      NK.CFTLib.Arl.congruenceSubgroup K (Ideal.absNorm 𝔪) :=
    NK.CFTLib.Arl.normIdeleHom_mem_congruenceSubgroup (K := K) (L := L) (Ideal.absNorm 𝔪) hMpos hd'
  have hNy'mem : NK.GlobalCFT.Idele.normIdeleHom K L y' ∈
      NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪 := by
    have h1 : NK.GlobalCFT.Idele.normIdeleHom K L y' ∈
        NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K
          (Ideal.span {(Ideal.absNorm 𝔪 : 𝓞 K)}) := by
      rwa [← NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroup_eq_congruenceSubgroupId
        (K := K) hMpos]
    exact NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId_mono
      (NK.CFTLib.ArtinReciprocityIdeal.span_nat_ne_bot hMpos) hle h1
  -- Step 3: the leftover principal idèle `β / N(d)` is congruent to `1` modulo `𝔪`.
  have hNy'_eq : NK.GlobalCFT.Idele.normIdeleHom K L y' =
      NK.GlobalCFT.Idele.normIdeleHom K L y *
        NK.GlobalCFT.Idele.principalIdele K (Units.map (Algebra.norm K) d) := by
    rw [hy'def, map_mul, NK.GlobalCFT.Idele.normIdeleHom_principalIdele]
  have hprinc : NK.GlobalCFT.Idele.principalIdele K (β / Units.map (Algebra.norm K) d) =
      z * (NK.GlobalCFT.Idele.normIdeleHom K L y')⁻¹ := by
    rw [hzy, hNy'_eq, map_div]
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hprinc_mem : NK.GlobalCFT.Idele.principalIdele K (β / Units.map (Algebra.norm K) d) ∈
      NK.CFTLib.ArtinReciprocityIdeal.congruenceSubgroupId K 𝔪 := by
    rw [hprinc]
    exact Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hNy'mem)
  have hray : NK.CFTLib.ArtinReciprocityIdeal.spanUnit (K := K)
      (β / Units.map (Algebra.norm K) d) ∈
      NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 :=
    spanUnit_mem_principalRayId_of_mem_congruenceSubgroupId 𝔪 h𝔪 _ hprinc_mem
  -- Step 4: `idealOf (N y') ∈ 𝔑(𝔪)`.
  have hnorm : NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K
      (NK.GlobalCFT.Idele.normIdeleHom K L y') ∈
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 :=
    idealOfUnitHom_normIdeleHom_mem_normRayId_aux 𝔪 (Ideal.absNorm 𝔪) hMpos hle hd'
  -- Step 5: assemble `z = N y' · (β / N d)`.
  have hz_split : z = NK.GlobalCFT.Idele.normIdeleHom K L y' *
      NK.GlobalCFT.Idele.principalIdele K (β / Units.map (Algebra.norm K) d) := by
    rw [hprinc]
    simp
  have hkey : NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K z =
      NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K (NK.GlobalCFT.Idele.normIdeleHom K L y') *
        NK.CFTLib.ArtinReciprocityIdeal.spanUnit (K := K) (β / Units.map (Algebra.norm K) d) := by
    rw [hz_split, map_mul, NK.CFTLib.ArtinReciprocityIdeal.idealOfUnitHom_principalIdele']
    rfl
  rw [hkey]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hnorm) (Subgroup.mem_sup_left hray)

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
