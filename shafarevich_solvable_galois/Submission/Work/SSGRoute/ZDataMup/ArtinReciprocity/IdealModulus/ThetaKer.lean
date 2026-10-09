import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.ThetaRange
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_normImage_of_congruence_mul_normId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.normIdeleHom_mem_congruenceSubgroupId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel of `θ` for an ideal modulus

The two inclusions computing the kernel of `θ : 𝕀 K →* (fractional ideals) ⧸ P(𝔪)·𝔑(𝔪)`:

* `principalSubgroup_sup_normImage_le_ker_thetaId` (in `ThetaRange.lean`) — the easy inclusion;
* `thetaId_ker_le` — the hard inclusion `ker θ ⊆ Kˣ · N_{L/K} 𝕀 L`, for an *admissible* modulus `𝔪`
  containing all the ramified primes.  This is the local–global argument: if `x ∈ ker θ` and `b`
  is the adjustment with `x·(b) ∈ U(𝔪)`, the ideal of `x·(b)` is a product `𝔭·𝔫` with
  `𝔭 ∈ P(𝔪)`, `𝔫 ∈ 𝔑(𝔪)`; writing `𝔭 = (a)` and `𝔫 = N_{L/K}(A)` for a suitable idèle `y` of `L`
  with `idealOf y = A`, the idèle
  `z := x·(b)·(a)⁻¹·N_{L/K}(y)⁻¹`
  is integral, congruent to `1` modulo `𝔪` against `N(y)` and positive at the real places, hence —
  by `mem_normImage_of_congruence_mul_normId` (admissibility plus Hasse's norm theorem) — an idèlic
  norm.  Hence `x ∈ Kˣ · N_{L/K} 𝕀 L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **Every element of `𝔑(𝔪)` is the ideal of the norm of an idèle of `U(𝔪 · 𝓞 L)`.** -/
lemma exists_normIdele_of_mem_normRayId {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) {𝔫 : Frac K}
    (h𝔫 : 𝔫 ∈ normRayId (K := K) (L := L) 𝔪) :
    ∃ y : Idele L, y ∈ congruenceSubgroupId L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪) ∧
      IdeleClassGroup.idealOfUnitHom K (Idele.normIdeleHom K L y) = 𝔫 := by
  classical
  have hmap : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪 ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot h𝔪
  have hle : normRayId (K := K) (L := L) 𝔪 ≤
      (congruenceSubgroupId L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪)).map
        ((IdeleClassGroup.idealOfUnitHom K).comp (Idele.normIdeleHom K L)) := by
    rw [normRayId]
    refine (Subgroup.closure_le _).mpr ?_
    rintro A ⟨I, hI, hcop, rfl⟩
    obtain ⟨y, hyC, hyA⟩ :=
      Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.exists_idealOf_eq_of_mem_idealCoprimeGroupId
        (K := L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪) hmap (idealUnit I hI) hcop
    refine Subgroup.mem_map.mpr ⟨y, hyC, ?_⟩
    refine Units.ext ?_
    rw [MonoidHom.comp_apply, IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0,
      NK.CFTLib.ARL.idealOf_normIdeleHom]
    have hyA' : (Idele.idealOf y) = ((I : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) := by
      have h := congrArg (fun u : Frac L => (u : FractionalIdeal (𝓞 L)⁰ L)) hyA
      rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0] at h
      exact h
    rw [hyA', NK.CFTLib.ARL.relNormFI_coeIdeal I hI]
    rfl
  obtain ⟨y, hyC, hyN⟩ := Subgroup.mem_map.mp (hle h𝔫)
  exact ⟨y, hyC, hyN⟩

/-- **The kernel of `θ` is contained in `Kˣ · N_{L/K} 𝕀 L`** (the hard inclusion, using the
admissibility of `𝔪` and the ramification hypothesis). -/
theorem thetaId_ker_le [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥)
    (hram : ContainsRamified (K := K) (L := L) 𝔪)
    (hadm : IsAdmissibleId (K := K) (L := L) 𝔪) :
    (thetaId K L 𝔪 h𝔪).ker ≤ Idele.principalSubgroup K ⊔ Idele.normImage K L := by
  classical
  intro x hx
  rw [MonoidHom.mem_ker, thetaId_apply] at hx
  set xb : Idele K := x * Idele.principalIdele K (adjIdMod 𝔪 h𝔪 x) with hxbdef
  have hxb : xb ∈ congruenceSubgroupId K 𝔪 := adjIdMod_spec h𝔪 x
  have hxb' := (mem_congruenceSubgroupId_iff h𝔪).mp hxb
  have hmem : IdeleClassGroup.idealOfUnitHom K xb ∈ rayNormClId K L 𝔪 := by
    have h := hx
    rw [show thetaIdFun 𝔪 h𝔪 x = QuotientGroup.mk' (rayNormClId K L 𝔪)
        (IdeleClassGroup.idealOfUnitHom K xb) from rfl] at h
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨𝔭, h𝔭P, 𝔫, h𝔫N, hprod⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨a, haU, haEq⟩ := Subgroup.mem_map.mp h𝔭P
  have haC : Idele.principalIdele K a ∈ congruenceSubgroupId K 𝔪 := haU
  have haC' := (mem_congruenceSubgroupId_iff h𝔪).mp haC
  obtain ⟨y, hyC, hyN⟩ := exists_normIdele_of_mem_normRayId (K := K) (L := L) h𝔪 h𝔫N
  -- the integral idèle `z`
  set z : Idele K := xb * (Idele.principalIdele K a)⁻¹ * (Idele.normIdeleHom K L y)⁻¹ with hzdef
  have hzU : IdeleClassGroup.idealOfUnitHom K z = 1 := by
    rw [hzdef, map_mul, map_mul, map_inv, map_inv, idealOfUnitHom_principalIdele', haEq,
      ← hprod, hyN]
    rw [mul_assoc 𝔭 𝔫 𝔭⁻¹, mul_comm 𝔫 𝔭⁻¹, ← mul_assoc 𝔭 𝔭⁻¹ 𝔫, mul_inv_cancel, one_mul,
      mul_inv_cancel]
  have hz : z.idealOf = 1 := by
    have h := congrArg (fun u : Frac K => (u : FractionalIdeal (𝓞 K)⁰ K)) hzU
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, Units.val_one] at h
    exact h
  have hzw : ∀ v : Place K, z v * Idele.normIdeleFun K L y v
      = (xb * (Idele.principalIdele K a)⁻¹) v := by
    intro v
    rw [hzdef]
    simp only [Idele.mul_apply, Idele.inv_apply, Idele.normIdeleHom_apply]
    group
  have hcong : ∀ 𝔭' : HeightOneSpectrum (𝓞 K), DvdPrime 𝔪 𝔭' →
      CongrAtId 𝔭' 𝔪
        (z (Place.ofFinite 𝔭') * Idele.normIdeleFun K L y (Place.ofFinite 𝔭')) := by
    intro 𝔭' h𝔭'
    rw [hzw (Place.ofFinite 𝔭')]
    have h1 : CongrAtId 𝔭' 𝔪 ((xb * (Idele.principalIdele K a)⁻¹) (Place.ofFinite 𝔭')) := by
      rw [Idele.mul_apply, Idele.inv_apply]
      exact congrAtId_mul 𝔭' 𝔪 ((dvdPrime_iff_one_le_count h𝔪 𝔭').mp h𝔭') (hxb'.1 𝔭' h𝔭')
        (congrAtId_inv 𝔭' 𝔪 ((dvdPrime_iff_one_le_count h𝔪 𝔭').mp h𝔭') (haC'.1 𝔭' h𝔭'))
    exact h1
  have hpos : ∀ w : InfinitePlace K, NK.CFTLib.Arl.PosAtReal w
      (z (Place.ofInfinite w) * Idele.normIdeleFun K L y (Place.ofInfinite w)) := by
    intro w
    rw [hzw (Place.ofInfinite w)]
    rw [Idele.mul_apply, Idele.inv_apply]
    exact NK.CFTLib.Arl.posAtReal_mul (hxb'.2 w) (NK.CFTLib.Arl.posAtReal_inv (haC'.2 w))
  have hznorm : z ∈ Idele.normImage K L :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_normImage_of_congruence_mul_normId
      (K := K) (L := L) 𝔪 h𝔪 hram hadm z y hz hcong hpos
  -- assembly
  have hxb_decomp : xb = z * Idele.normIdeleHom K L y * Idele.principalIdele K a := by
    rw [hzdef]; group
  have hxb_mem : xb ∈ Idele.principalSubgroup K ⊔ Idele.normImage K L := by
    rw [hxb_decomp]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hznorm) ?_)
      (Subgroup.mem_sup_left (Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩))
    refine Subgroup.mem_sup_right ?_
    rw [Idele.normImage_eq_range]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have hx_eq : x = xb * (Idele.principalIdele K (adjIdMod 𝔪 h𝔪 x))⁻¹ := by
    rw [hxbdef]; group
  rw [hx_eq]
  exact Subgroup.mul_mem _ hxb_mem
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Idele.mem_principalSubgroup.mpr ⟨_, rfl⟩)))

end NK.CFTLib.ArtinReciprocityIdeal
