import Mathlib
import Submission.NK.CFTLib.pClassField_exists
import Submission.Work.SSGRoute.ZDataMup.nonempty_artinReciprocity_of_abelian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

namespace Work.SSGRoute.E9Nodes

/-- **The norm-kernel principle, without cyclicity.**  If `L / K` is a finite Galois extension of
number fields which is unramified at every finite place (`differentIdeal = ⊤`) and at every
infinite place, and if the primes of a finite set `S` split completely in `L / K` while the classes
of the primes of `S` generate the ideal class group `Cl(K)`, then the norm class subgroup
`N_{L/K} C_L` is all of the idèle class group `C_K`.

This is `NK.CFTLib.normClassSubgroup_eq_top_of_unramified_of_generating_splits` with the hypothesis
`[IsCyclic (L ≃ₐ[K] L)]` dropped: that proof never uses cyclicity.  Its two arithmetic inputs are
`NK.CFTLib.integralIdelesLeNormImage` (an extension unramified everywhere has the modulus-one ray
group in its norm group, so the kernel of the ideal class map is a norm group) and
`NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_mem_normImage_of_splitsCompletely` (a completely
split prime has its prime idèle in the norm group), and the closing argument is pure group theory. -/
theorem e9_normClassSubgroup_eq_top_of_unramified_of_generating_splits
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hfin : differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces K L)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (hgen : Subgroup.closure {d : ClassGroup (NumberField.RingOfIntegers K) |
      ∃ 𝔮 ∈ S, d = ClassGroup.mk0 ⟨𝔮.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔮.ne_bot⟩} = ⊤)
    (hsplit : ∀ 𝔮 ∈ S,
      (𝔮.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L) :
    NK.GlobalCFT.Idele.normClassSubgroup K L = ⊤ := by
  classical
  have hker : (NK.GlobalCFT.IdeleClassGroup.idealClassHom K).ker ≤
      NK.GlobalCFT.Idele.normClassSubgroup K L := by
    rw [NK.GlobalCFT.IdeleClassGroup.ker_idealClassHom K]
    exact Subgroup.map_mono (NK.CFTLib.integralIdelesLeNormImage (K := K) (L := L) hfin hinf)
  have hS : ∀ d ∈ ({d : ClassGroup (NumberField.RingOfIntegers K) |
      ∃ 𝔮 ∈ S, d = ClassGroup.mk0 ⟨𝔮.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔮.ne_bot⟩} : Set _),
      d ∈ (NK.GlobalCFT.Idele.normClassSubgroup K L).map
        (NK.GlobalCFT.IdeleClassGroup.idealClassHom K) := by
    rintro d ⟨𝔮, h𝔮, rfl⟩
    have hmem : NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮) ∈
        NK.GlobalCFT.Idele.normClassSubgroup K L :=
      Subgroup.mem_map_of_mem (NK.GlobalCFT.IdeleClassGroup.mk K)
        (NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_mem_normImage_of_splitsCompletely
          (K := K) (L := L) 𝔮 (hsplit 𝔮 h𝔮))
    have h2 := Subgroup.mem_map_of_mem (NK.GlobalCFT.IdeleClassGroup.idealClassHom K) hmem
    rwa [NK.CFTLib.idealClassHom_mk_ideleOfPrime K 𝔮] at h2
  have himg : (NK.GlobalCFT.IdeleClassGroup.idealClassHom K).range ≤
      (NK.GlobalCFT.Idele.normClassSubgroup K L).map
        (NK.GlobalCFT.IdeleClassGroup.idealClassHom K) := by
    rw [MonoidHom.range_eq_top.mpr (NK.GlobalCFT.IdeleClassGroup.idealClassHom_surjective K),
      ← hgen]
    exact (Subgroup.closure_le _).mpr hS
  rw [eq_top_iff]
  intro x _
  have hx : NK.GlobalCFT.IdeleClassGroup.idealClassHom K x ∈
      (NK.GlobalCFT.IdeleClassGroup.idealClassHom K).range := ⟨x, rfl⟩
  obtain ⟨n, hn, hnx⟩ := himg hx
  have hmem : x * n⁻¹ ∈ (NK.GlobalCFT.IdeleClassGroup.idealClassHom K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnx.symm, mul_inv_cancel]
  have hx' : x = (x * n⁻¹) * n := by group
  rw [hx']
  exact Subgroup.mul_mem _ (hker hmem) hn

/-- **The abelian "wide witness".**  Let `F / K` be a finite **abelian** Galois extension of number
fields which is unramified at every finite place (`differentIdeal = ⊤`) and at every infinite place,
and suppose that every prime `𝔮` of a finite set `S` **splits completely** in `F / K` while the
classes of the primes of `S` **generate the ideal class group** `Cl(K)`.  Then `F = K`, i.e.
`[F : K] = 1`.

This is the class-field-theoretic core of the E9 "descent" node: an everywhere unramified abelian
extension in which a class-group generating set splits completely is trivial.  It is the abelian
version of `NK.CFTLib.finrank_eq_one_of_unramified_of_generating_splits` (which assumes
`IsCyclic` in addition); the proof is that of
`NK.CFTLib.normClassSubgroup_eq_top_of_unramified_of_generating_splits` (whose argument never uses
cyclicity: the kernel of the ideal class map is contained in the norm subgroup because the integral
idèles are norms, and the classes of `S` lie in the image of the norm subgroup), followed by the
Artin reciprocity isomorphism `C_K ⧸ N_{F/K} C_F ≃* Gal(F/K)` for abelian `F/K`, which is available
as `Work.SSGRoute.ZDataMup.nonempty_artinReciprocity_of_abelian` (proved, sorry-free), whose
`ArtinReciprocity.iso` gives `Gal(F/K) ≃* C_K ⧸ N`; with `N = ⊤` the Galois group is a subsingleton
and `IsGalois.card_aut_eq_finrank` gives `finrank = 1`.

Useful imports: `Submission.NK.CFTLib.pClassField_exists`,
`Submission.Work.SSGRoute.ZDataMup.nonempty_artinReciprocity_of_abelian`. -/
theorem e9_abelian_wide_witness (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] [FiniteDimensional K F] [IsGalois K F] [IsMulCommutative (F ≃ₐ[K] F)]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hgen : Subgroup.closure {d : ClassGroup (NumberField.RingOfIntegers K) |
      ∃ 𝔮 ∈ S, d = ClassGroup.mk0 ⟨𝔮.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔮.ne_bot⟩} = ⊤)
    (hfin : differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers F) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces K F)
    (hsplit : ∀ 𝔮 ∈ S,
      (𝔮.asIdeal.primesOver (NumberField.RingOfIntegers F)).ncard = Module.finrank K F) :
    Module.finrank K F = 1 := by
  -- the norm class subgroup is everything
  have hN : NK.GlobalCFT.Idele.normClassSubgroup K F = ⊤ :=
    e9_normClassSubgroup_eq_top_of_unramified_of_generating_splits (K := K) (L := F)
      (S := S) hfin hinf hgen hsplit
  -- Artin reciprocity for the abelian extension `F / K`
  have hcomm : ∀ a b : F ≃ₐ[K] F, a * b = b * a := fun a b => mul_comm' a b
  obtain ⟨hAR⟩ := Work.SSGRoute.ZDataMup.nonempty_artinReciprocity_of_abelian K F hcomm
  have hcard : Nat.card (NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K F) = 1 := by
    rw [hN]
    exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
  rw [← IsGalois.card_aut_eq_finrank K F, ← Nat.card_congr hAR.iso.toEquiv]
  exact hcard

end Work.SSGRoute.E9Nodes
