import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.Existence.artinKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.Existence

/-! **The norm-group / Galois correspondence (Milne, *CFT*, 9.1) at prime index.**

For `L / K` a finite abelian extension of number fields, the map `M ↦ N_{M/K}C_M` from intermediate
fields to subgroups of `C_K` containing `N_{L/K}C_L` is a bijection (Neukirch *ANT* V.5.5 / Milne
Ch. V Corollary 3.7).  This is the statement at *arbitrary* index `V.index`, obtained from the index-`p` version
by observing that the proof never uses primality: the index hypothesis enters only in the
final computation of `Module.finrank K ↥E`.

The proof uses the idèlic Artin map at the two levels `L/K` and `E/K`: the Artin isomorphism
`e : C_K ⧸ N_{L/K}C_L ≃* Gal(L/K)` identifies `V ⧸ N_{L/K}C_L` with a subgroup `J` of index `p`,
and `E := L^J` is the candidate.  The two Artin maps `g` (for `E/K`) and `res ∘ f` (for `L/K`
restricted to `E`) kill `N_{L/K}C_L`, hence factor through `C_K ⧸ N_{L/K}C_L`; they agree on the
classes of the idèles of the primes `𝔭 ∤ m_L m_E` (both are the Frobenius at `𝔭` there, using the
consistency of Frobenius under restriction), and those classes generate `C_K ⧸ N_{L/K}C_L` because
the Frobenius elements generate `Gal(L/K)`.  Hence `g = res ∘ f`, and therefore
`N_{E/K}C_E = ker g = f⁻¹(Gal(L/E)) = f⁻¹(J) = V`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct IsMulCommutative
open NK.GlobalCFT
open NK.Chebotarev

theorem exists_intermediateField_normClassSubgroup_eq_of_index
    (hARL : NK.CFTLib.ArtinReciprocityIdeal) (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K))
    (hle : NK.GlobalCFT.Idele.normClassSubgroup K L ≤ V) :
    ∃ E : IntermediateField K L, IsGalois K ↥E ∧
      NK.GlobalCFT.Idele.normClassSubgroup K ↥E = V ∧ Module.finrank K ↥E = V.index := by
  classical
  have hcommL : ∀ a b : Gal(L/K), a * b = b * a := fun a b => mul_comm' a b
  -- ## The idèlic Artin map of `L/K` and the induced isomorphism `C_K ⧸ N ≃* Gal(L/K)`
  obtain ⟨mL, hmL, artL, hramL, hprincL, hnormL, hfrobL, hsurjL⟩ :=
    exists_ideleArtinMap_of_arl hARL (K := K) (L := L)
  have hkerL : Idele.principalSubgroup K ≤ artL.ker := by
    rintro x ⟨k, rfl⟩
    exact MonoidHom.mem_ker.mpr (hprincL k)
  set f : IdeleClassGroup K →* Gal(L/K) := artinMapCK artL hkerL with hf
  have hkerf : f.ker = Idele.normClassSubgroup K L :=
    ker_artinMapCK_eq_normClassSubgroup hFC artL hkerL hnormL hsurjL
  obtain ⟨e, he⟩ := exists_artinIso_of_ideleArtin hFC artL hkerL hnormL hsurjL
  -- ## The subgroup `J = e(V ⧸ N) ≤ Gal(L/K)` of index `p`, and `E = L^J`
  let A : Subgroup (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) :=
    V.map (QuotientGroup.mk' (Idele.normClassSubgroup K L))
  let J : Subgroup Gal(L/K) :=
    A.map (e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K))
  have hidxJ : J.index = V.index := by
    have h1 : J.index = A.index := Subgroup.index_map_equiv A e
    have h2 : A.index = V.index :=
      Subgroup.index_map_eq V (QuotientGroup.mk'_surjective (Idele.normClassSubgroup K L))
        (by rw [QuotientGroup.ker_mk']; exact hle)
    rw [h1, h2]
  haveI hJnorm : J.Normal := inferInstance
  let E : IntermediateField K L := IntermediateField.fixedField J
  haveI hEgal : IsGalois K ↥E := IsGalois.of_fixedField_normal_subgroup J
  have hfixJ : E.fixingSubgroup = J := IntermediateField.fixingSubgroup_fixedField J
  have hfinE : Module.finrank K ↥E = V.index := by
    have h1 : Module.finrank ↥E L = Nat.card ↥J :=
      IntermediateField.finrank_fixedField_eq_card J
    have h2 : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
    have h4 : Module.finrank K ↥E * Nat.card ↥J = Module.finrank K L := by
      rw [← h1]; exact Module.finrank_mul_finrank K ↥E L
    have h5 : Module.finrank K L = Nat.card ↥J * J.index := by
      rw [← h2, ← Subgroup.card_mul_index J]
    have h6 : Module.finrank K ↥E * Nat.card ↥J = Nat.card ↥J * V.index := by
      rw [h4, h5, hidxJ]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos
      (by rw [mul_comm (Nat.card ↥J) (Module.finrank K ↥E)]; exact h6)
  -- ## `Gal(E/K)` is commutative: it is a quotient of the commutative group `Gal(L/K)`
  haveI hcommE : IsMulCommutative (↥E ≃ₐ[K] ↥E) :=
    IsMulCommutative.of_comm (fun a b => by
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) L a
      obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) L b
      rw [← map_mul, ← map_mul, mul_comm' σ τ])
  have hcommE' : ∀ a b : Gal(↥E/K), a * b = b * a := fun a b => mul_comm' a b
  set res : Gal(L/K) →* Gal(↥E/K) := AlgEquiv.restrictNormalHom (F := K) (K₁ := L) ↥E with hres
  -- ## The idèlic Artin map of `E/K`
  obtain ⟨mE, hmE, artE, hramE, hprincE, hnormE, hfrobE, hsurjE⟩ :=
    exists_ideleArtinMap_of_arl hARL (K := K) (L := ↥E)
  have hkerE : Idele.principalSubgroup K ≤ artE.ker := by
    rintro x ⟨k, rfl⟩
    exact MonoidHom.mem_ker.mpr (hprincE k)
  set g : IdeleClassGroup K →* Gal(↥E/K) := artinMapCK artE hkerE with hg
  have hkerg : g.ker = Idele.normClassSubgroup K ↥E :=
    ker_artinMapCK_eq_normClassSubgroup hFC artE hkerE hnormE hsurjE
  -- ## The finite set of primes to avoid
  set T : Finset (PrimeIdeal K) :=
    NK.CFTLib.Arl.primesDividing mL hmL ∪ NK.CFTLib.Arl.primesDividing mE hmE with hT
  have hTl : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ T → (mL : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    refine h𝔭 ?_
    rw [hT]
    exact Finset.mem_union.mpr (Or.inl ((NK.CFTLib.Arl.mem_primesDividing mL hmL 𝔭).mpr hmem))
  have hTe : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ T → (mE : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    refine h𝔭 ?_
    rw [hT]
    exact Finset.mem_union.mpr (Or.inr ((NK.CFTLib.Arl.mem_primesDividing mE hmE 𝔭).mpr hmem))
  have hunrL : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ T → ∀ Q : PrimeIdeal L,
      Q.asIdeal.LiesOver 𝔭.asIdeal → Q.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    fun 𝔭 h𝔭 => hramL 𝔭 (hTl 𝔭 h𝔭)
  have hunrE : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ T → ∀ Q : PrimeIdeal ↥E,
      Q.asIdeal.LiesOver 𝔭.asIdeal → Q.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    fun 𝔭 h𝔭 => hramE 𝔭 (hTe 𝔭 h𝔭)
  -- ## The value of `e` on the class of a prime idèle
  have heval : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ T →
      (e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K))
          (QuotientGroup.mk' (Idele.normClassSubgroup K L)
            (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔭)))
        = frobAtPrime (K := K) (L := L) 𝔭 := by
    intro 𝔭 h𝔭
    exact (he (NK.HeckeL.ideleOfPrime K 𝔭)).trans (hfrobL 𝔭 (hTl 𝔭 h𝔭))
  -- ## The two Artin maps agree on the classes of the good primes
  have hval : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ T →
      g (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔭))
        = res (f (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔭))) := by
    intro 𝔭 h𝔭
    have h1 : g (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔭))
        = frobAtPrime (K := K) (L := ↥E) 𝔭 :=
      (artinMapCK_mk artE hkerE (NK.HeckeL.ideleOfPrime K 𝔭)).trans (hfrobE 𝔭 (hTe 𝔭 h𝔭))
    have h2 : f (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔭))
        = frobAtPrime (K := K) (L := L) 𝔭 :=
      (artinMapCK_mk artL hkerL (NK.HeckeL.ideleOfPrime K 𝔭)).trans (hfrobL 𝔭 (hTl 𝔭 h𝔭))
    have h3 : res (frobAtPrime (K := K) (L := L) 𝔭)
        = frobAtPrime (K := K) (L := ↥E) 𝔭 :=
      ((isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := ↥E) hcommE' 𝔭 (hunrE 𝔭 h𝔭) _).mp
        (NK.CFTLib.exists_isFrobAtPrime_restrict (K := K) (L := L) E
          (isFrobAtPrime_frobAtPrime (K := K) (L := L) hcommL 𝔭 (hunrL 𝔭 h𝔭)))).symm
    rw [h1, h2, h3]
  -- ## The classes of the good primes generate `C_K ⧸ N`
  set S : Set (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) :=
    {z | ∃ 𝔭 : PrimeIdeal K, 𝔭 ∉ T ∧ z = QuotientGroup.mk' (Idele.normClassSubgroup K L)
      (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔭))} with hS
  have hStop : Subgroup.closure S = ⊤ := by
    have hsub : {σ : Gal(L/K) | ∃ q : PrimeIdeal K, q ∉ T ∧
          IsFrobAtPrime (K := K) (L := L) q σ} ⊆
        ((e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K)) '' S) := by
      rintro σ ⟨𝔭, h𝔭, hfrob⟩
      exact ⟨QuotientGroup.mk' (Idele.normClassSubgroup K L)
          (IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔭)), ⟨𝔭, h𝔭, rfl⟩,
        (heval 𝔭 h𝔭).trans
          ((isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcommL 𝔭 (hunrL 𝔭 h𝔭) σ).mp hfrob)⟩
    have himg : (Subgroup.closure S).map
          (e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K)) = ⊤ := by
      rw [MonoidHom.map_closure]
      have h2 : Subgroup.closure {σ : Gal(L/K) | ∃ q : PrimeIdeal K, q ∉ T ∧
            IsFrobAtPrime (K := K) (L := L) q σ} ≤
          Subgroup.closure ((e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →*
            Gal(L/K)) '' S) := Subgroup.closure_mono hsub
      rw [NK.CFTLib.Arl.closure_isFrobAtPrime_of_notMem_eq_top (K := K) (L := L) T] at h2
      exact top_le_iff.mp h2
    have hmem : ∀ z, z ∈ Subgroup.closure S := by
      intro z
      have hz : (e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K)) z ∈
          (Subgroup.closure S).map
            (e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K)) := by
        rw [himg]; exact Subgroup.mem_top z
      rw [Subgroup.mem_map] at hz
      obtain ⟨w, hw, hwe⟩ := hz
      rwa [MulEquiv.injective e hwe] at hw
    exact eq_top_iff.mpr fun z _ => hmem z
  -- ## Hence the two Artin maps on `C_K` coincide
  have hcomp : g = res.comp f := by
    have hNLmem : Idele.normClassSubgroup K L ≤ (g * (res.comp f)⁻¹).ker := by
      intro z hz
      have hfz : f z = 1 := by
        rw [← MonoidHom.mem_ker, hkerf]
        exact hz
      have hgz : g z = 1 := by
        rw [← MonoidHom.mem_ker, hkerg]
        exact Idele.normClassSubgroup_le_of_tower (K := K) (L := ↥E) (M := L) hz
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
        hfz, map_one, hgz, one_mul, inv_one]
    have hprime : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ T →
        IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔭) ∈ (g * (res.comp f)⁻¹).ker := by
      intro 𝔭 h𝔭
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
        hval 𝔭 h𝔭, mul_inv_cancel]
    have hmap : (g * (res.comp f)⁻¹).ker.map
        (QuotientGroup.mk' (Idele.normClassSubgroup K L)) = ⊤ := by
      have hle : Subgroup.closure S ≤ (g * (res.comp f)⁻¹).ker.map
          (QuotientGroup.mk' (Idele.normClassSubgroup K L)) := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro z ⟨𝔭, h𝔭, hz⟩
        rw [hz]
        exact Subgroup.mem_map.mpr ⟨_, hprime 𝔭 h𝔭, rfl⟩
      exact top_le_iff.mp (hStop ▸ hle)
    have hkertop : (g * (res.comp f)⁻¹).ker = ⊤ := by
      have h := Subgroup.comap_map_eq (QuotientGroup.mk' (Idele.normClassSubgroup K L))
        ((g * (res.comp f)⁻¹).ker)
      rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hNLmem] at h
      exact h.symm
    have hρ : g * (res.comp f)⁻¹ = 1 := MonoidHom.ker_eq_top_iff.mp hkertop
    refine MonoidHom.ext fun z => ?_
    have hz := congrArg (fun u : IdeleClassGroup K →* Gal(↥E/K) => u z) hρ
    simp only [MonoidHom.one_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
      MonoidHom.comp_apply] at hz
    exact mul_inv_eq_one.mp hz
  -- ## Conclusion: `N_{E/K}C_E = ker g = f⁻¹(J) = V`
  have hfe : f = (e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K)).comp
      (QuotientGroup.mk' (Idele.normClassSubgroup K L)) := by
    refine MonoidHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K z
    show f (IdeleClassGroup.mk K x) = e (QuotientGroup.mk' (Idele.normClassSubgroup K L)
      (IdeleClassGroup.mk K x))
    rw [artinMapCK_mk]
    exact (he x).symm
  have hfV : V.map f = J := by
    rw [hfe]
    exact (Subgroup.map_map V
      (e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K))
      (QuotientGroup.mk' (Idele.normClassSubgroup K L))).symm
  have hkerres : res.ker = J := by
    rw [hres, IntermediateField.restrictNormalHom_ker, hfixJ]
  have hfinal : (res.comp f).ker = V := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hkerres]
    constructor
    · intro hz
      have hz' : f z ∈ V.map f := by rw [hfV]; exact hz
      rw [Subgroup.mem_map] at hz'
      obtain ⟨v, hv, hfv⟩ := hz'
      have hmem : z * v⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hfv]
        exact mul_inv_cancel (f z)
      rw [hkerf] at hmem
      have hzv : z = (z * v⁻¹) * v := by group
      rw [hzv]
      exact V.mul_mem (hle hmem) hv
    · intro hz
      exact (by rw [← hfV]; exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩ : f z ∈ J)
  refine ⟨E, hEgal, ?_, hfinE⟩
  rw [← hkerg, hcomp]
  exact hfinal

end NK.CFTLib.Existence
