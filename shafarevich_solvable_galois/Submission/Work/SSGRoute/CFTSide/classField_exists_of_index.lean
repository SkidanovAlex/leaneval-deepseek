import Mathlib
import Submission.Work.SSGRoute.NKExistenceImport
import Submission.Work.SSGRoute.classField_exists_ramified
import Submission.Work.SSGRoute.CFTSide.exists_intermediateField_normClassSubgroup_eq_of_index
import Submission.Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le
import Submission.Work.SSGRoute.exists_level_normGroup_not_mem_of_not_pthPower
import Submission.NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
import Submission.NK.GlobalCFTdeep.Audit.index_normClassSubgroup_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The existence theorem of global class field theory at arbitrary index

For a number field `K` and an open subgroup `V ≤ C_K` of finite index `n`, there is a finite Galois
extension `L / K` with `N_{L/K} C_L = V` and `[L : K] = n`.

The proof is Milne's (`CFT` V.9.5), in the "finite" form that avoids infinite Galois theory:

* if `V = C_K` take `L = K`;
* otherwise choose a prime `p ∣ n` and an index-`p` subgroup `W ≥ V`.  By the existence theorem at
  **prime** index (`Work.SSGRoute.classField_exists_ramified`, unconditional in this workspace) there
  is `K' / K` Galois with `N_{K'/K}C_{K'} = W` and `[K' : K] = p`;
* the pullback `U' = Nm_{K'/K}^{-1} V ≤ C_{K'}` has index `[W : V] < n`, so by induction there is
  `M / K'` with `N_{M/K'}C_M = U'`;
* transitivity of the norm gives `N_{M/K}C_M = Nm_{K'/K}(U') = V`;
* passing to the Galois closure `Ω` of `M / K` we get `N_{Ω/K} ≤ V`, and inside `Ω` the maximal
  abelian subextension `A` still has `N_{A/K} ≤ V`
  (`Work.SSGRoute.CFTSide.exists_abelian_subextension_normClassSubgroup_le`, the norm limitation
  theorem in index form);
* finally the norm-group correspondence for the abelian extension `A / K`
  (`Work.SSGRoute.CFTSide.exists_intermediateField_normClassSubgroup_eq_of_index`) produces `E ≤ A`
  with `N_{E/K} = V` and `[E : K] = [C_K : V] = n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

namespace Work.SSGRoute.CFTSide

open NK.GlobalCFT

noncomputable section

/-! ## Group-theoretic preliminaries -/

/-- In a finite commutative group whose order is divisible by the prime `p`, some element is not a
`p`-th power.  Otherwise the `p`-th power map would be injective, so no element of order `p` would
exist, contradicting Cauchy's theorem. -/
private theorem exists_not_pow_of_dvd_natCard (A : Type*) [CommGroup A] [Finite A] (p : ℕ)
    [Fact p.Prime] (hp : p ∣ Nat.card A) : ∃ a : A, ∀ b : A, b ^ p ≠ a := by
  by_contra h
  push_neg at h
  have hsurj : Function.Surjective (fun b : A => b ^ p) := fun a => h a
  have hinj : Function.Injective (fun b : A => b ^ p) :=
    (Finite.injective_iff_surjective (f := fun b : A => b ^ p)).mpr hsurj
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact (Fact.out : p.Prime).ne_one hx.symm
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  exact hx1 (hinj (by simpa [hxp]))

/-- A finite commutative group whose order is divisible by `p` has a subgroup of index `p`. -/
private theorem exists_subgroup_index_prime_of_dvd_card (A : Type*) [CommGroup A] [Finite A]
    (p : ℕ) [Fact p.Prime] (hp : p ∣ Nat.card A) : ∃ K : Subgroup A, K.index = p := by
  obtain ⟨a, ha⟩ := exists_not_pow_of_dvd_natCard A p hp
  obtain ⟨U, hU, -⟩ := exists_subgroup_index_prime_notMem_of_not_pow_eq p a ha
  exact ⟨U, hU⟩

/-- In a commutative group, an index-`p` subgroup can be found above any finite-index subgroup
whose index is divisible by `p`. -/
private theorem exists_subgroup_index_prime_of_dvd_index {G : Type*} [CommGroup G]
    (V : Subgroup G) (hV : V.FiniteIndex) (p : ℕ) [Fact p.Prime] (hp : p ∣ V.index) :
    ∃ W : Subgroup G, V ≤ W ∧ W.index = p := by
  haveI hVfi : V.FiniteIndex := hV
  obtain ⟨K, hK⟩ := exists_subgroup_index_prime_of_dvd_card (G ⧸ V) p
    (by rw [← Subgroup.index_eq_card]; exact hp)
  refine ⟨K.comap (QuotientGroup.mk' V), ?_, ?_⟩
  · intro x hx
    have h1 : (QuotientGroup.mk' V) x = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hx
    rw [Subgroup.mem_comap, h1]
    exact K.one_mem
  · rw [Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective V)]
    exact hK

/-! ## The existence theorem, by strong induction on the index -/

private theorem exists_classField_of_index_aux :
    ∀ (n : ℕ) {K : Type} [Field K] [NumberField K] (V : Subgroup (IdeleClassGroup K)),
      V.FiniteIndex → IsOpen (V : Set (IdeleClassGroup K)) → V.index = n →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
        IsGalois K L ∧ Idele.normClassSubgroup K L = V ∧ Module.finrank K L = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro K _instK _instNK V hVfin hopen hidx
    rcases Nat.lt_or_ge n 2 with hnlt | hnge
    · -- `n = 0` (impossible) or `n = 1`
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · exact absurd hidx (Subgroup.finiteIndex_iff.mp hVfin)
      · -- `V = ⊤`: the trivial extension `K / K` works
        have hVtop : V = ⊤ := Subgroup.index_eq_one.mp hidx
        have htop : Idele.normClassSubgroup K K = ⊤ :=
          Subgroup.index_eq_one.mp (NK.GlobalCFTdeep.Audit.index_normClassSubgroup_self (K := K))
        refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
          ?_, ?_⟩
        · rw [htop, hVtop]
        · rw [Module.finrank_self]
    · -- `2 ≤ n`
      obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
      haveI : Fact p.Prime := ⟨hpprime⟩
      -- an index-`p` subgroup `W ≥ V`
      obtain ⟨W, hVW, hWidx⟩ :=
        exists_subgroup_index_prime_of_dvd_index V hVfin p (by rw [hidx]; exact hpdvd)
      have hWfin : W.FiniteIndex :=
        Subgroup.finiteIndex_iff.mpr (by rw [hWidx]; exact hpprime.ne_zero)
      have hWopen : IsOpen (W : Set (IdeleClassGroup K)) := Subgroup.isOpen_mono hVW hopen
      -- the class field of `W`: a Galois extension of degree `p`
      obtain ⟨K', hFK', hNK', hAK', hfdK', hGalK', hNormK', _hdegK'⟩ :=
        classField_exists_ramified NK.CFTLib.artinReciprocityIdeal_proved
          NK.CFTLib.fundamentalClassElement (K := K) p W hWfin hWopen hWidx
      letI : Field K' := hFK'
      letI : NumberField K' := hNK'
      letI : Algebra K K' := hAK'
      letI : FiniteDimensional K K' := hfdK'
      -- the pullback of `V` to `C_{K'}`
      let U' : Subgroup (IdeleClassGroup K') := V.comap (IdeleClassGroup.normClassHom K K')
      have hrange : (IdeleClassGroup.normClassHom K K').range = W := by
        rw [← Idele.normClassSubgroup_eq_range (K := K) (L := K'), hNormK']
      have hU'idx : U'.index = V.relIndex W := by
        dsimp only [U']
        rw [Subgroup.index_comap, hrange]
      have hmul : U'.index * p = n := by
        rw [hU'idx, ← hWidx, ← hidx]
        exact Subgroup.relIndex_mul_index hVW
      have hU'ne : U'.index ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hmul
        omega
      have hU'fin : U'.FiniteIndex := Subgroup.finiteIndex_iff.mpr hU'ne
      have hU'pos : 0 < U'.index := Nat.pos_of_ne_zero hU'ne
      have hU'lt : U'.index < n := by
        rw [← hmul]
        simpa using Nat.mul_lt_mul_of_pos_left hpprime.one_lt hU'pos
      have hU'open : IsOpen (U' : Set (IdeleClassGroup K')) :=
        NK.NUV2.ArtinBridge.isOpen_comap_normClassHom K K' V hopen
      -- the induction hypothesis over `K'`
      obtain ⟨M, hFM, hNM, hAM, hfdM, hGalM, hNormM, _⟩ :=
        ih U'.index hU'lt (K := K') U' hU'fin hU'open rfl
      letI : Field M := hFM
      letI : NumberField M := hNM
      letI : Algebra K' M := hAM
      letI : FiniteDimensional K' M := hfdM
      -- the `K`-algebra structure on `M` through `K'`
      letI : Algebra K M := ((algebraMap K' M).comp (algebraMap K K')).toAlgebra
      haveI hSTM : IsScalarTower K K' M := IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI hFDM : FiniteDimensional K M := FiniteDimensional.trans K K' M
      -- transitivity of the norm: `N_{M/K}C_M = Nm_{K'/K}(U') = V`
      have hcomp : IdeleClassGroup.normClassHom K M =
          (IdeleClassGroup.normClassHom K K').comp (IdeleClassGroup.normClassHom K' M) :=
        MonoidHom.ext fun q => (NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans q).symm
      have hNMK : Idele.normClassSubgroup K M = V := by
        have h1 : Idele.normClassSubgroup K M =
            Subgroup.map (IdeleClassGroup.normClassHom K K') (Idele.normClassSubgroup K' M) := by
          rw [Idele.normClassSubgroup_eq_range (K := K) (L := M), hcomp, MonoidHom.range_comp,
            ← Idele.normClassSubgroup_eq_range (K := K') (L := M)]
        rw [h1, hNormM]
        change Subgroup.map (IdeleClassGroup.normClassHom K K')
          (V.comap (IdeleClassGroup.normClassHom K K')) = V
        rw [Subgroup.map_comap_eq, hrange]
        exact inf_eq_right.mpr hVW
      -- the Galois closure `Ω` of `M / K`, and the maximal abelian subextension `A`
      haveI huniq : FiniteDimensional K (NK.GlobalCFTdeep.galoisClosure K M) :=
        normalClosure.is_finiteDimensional K M (AlgebraicClosure M)
      haveI hNFuniq : NumberField (NK.GlobalCFTdeep.galoisClosure K M) :=
        NumberField.of_module_finite K (NK.GlobalCFTdeep.galoisClosure K M)
      haveI hGaluniq : IsGalois K (NK.GlobalCFTdeep.galoisClosure K M) :=
        Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
      have hΩV : Idele.normClassSubgroup K (NK.GlobalCFTdeep.galoisClosure K M) ≤ V := by
        have h := Idele.normClassSubgroup_le_of_tower (K := K) (L := M)
          (M := NK.GlobalCFTdeep.galoisClosure K M)
        rwa [hNMK] at h
      obtain ⟨A, hAgal, hAcomm, hAle⟩ :=
        exists_abelian_subextension_normClassSubgroup_le
          NK.CFTLib.fundamentalClassElement (K := K) (L := NK.GlobalCFTdeep.galoisClosure K M)
          V hΩV
      haveI : IsGalois K ↥A := hAgal
      haveI : IsMulCommutative (↥A ≃ₐ[K] ↥A) := hAcomm
      -- the norm-group correspondence for the abelian extension `A / K`
      obtain ⟨E, hEgal, hEnorm, hEdeg⟩ :=
        NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index
          NK.CFTLib.artinReciprocityIdeal_proved NK.CFTLib.fundamentalClassElement
          (K := K) (L := ↥A) V hAle
      refine ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance, hEgal, hEnorm, ?_⟩
      rw [hEdeg, hidx]

end

end Work.SSGRoute.CFTSide

namespace Work.SSGRoute.CFTSide

open NK.GlobalCFT

/-- **The existence theorem of global class field theory at arbitrary index.** -/
theorem classField_exists_of_index :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (hn : 0 < n)
      (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)), V.FiniteIndex →
      IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)) → V.index = n →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
        IsGalois K L ∧ NK.GlobalCFT.Idele.normClassSubgroup K L = V ∧ Module.finrank K L = n := by
  intro K _instK _instNK n _hn V hVfin hopen hidx
  exact exists_classField_of_index_aux n V hVfin hopen hidx

end Work.SSGRoute.CFTSide
