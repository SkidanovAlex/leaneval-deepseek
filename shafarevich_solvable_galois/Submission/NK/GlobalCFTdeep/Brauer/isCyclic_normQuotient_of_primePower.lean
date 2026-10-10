import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Basic
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.GlobalCFTdeep.hasseNorm_index_eq_universe
import Submission.NK.GroupTheory.Cyclic.isCyclic_of_cyclic_subgroup_cyclic_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cyclicity of the norm-class quotient for a cyclic extension, from the prime-power case

For a finite cyclic extension `L / K` of number fields, the quotient `C_K ⧸ N_{L/K} C_L` of the
idèle class group by the norm class subgroup is cyclic (it is isomorphic to `Gal(L/K)` by
Artin's reciprocity law).  This file proves the reduction that is *independent* of reciprocity:

> if `C_E ⧸ N_{F/E} C_F` is cyclic for every cyclic extension `E ⊆ F` whose degree is a prime
> power, then `C_K ⧸ N_{L/K} C_L` is cyclic for every cyclic extension `L / K` whatsoever.

The argument is the classical one.  For a cyclic `L/K` of degree `n` and a prime `p ∣ n`, write
`n = p^e · m` with `p ∤ m`, let `H ≤ Gal(L/K)` be the unique subgroup of order `p^e` and
`M = L^H` the corresponding fixed field.  Then `[L : M] = p^e` and `[M : K] = m`, and one has the
exact sequence

`1 → C_M ⧸ N_{L/M} C_L → C_K ⧸ N_{L/K} C_L → C_K ⧸ N_{M/K} C_M → 1`

of abelian groups, in which the kernel is cyclic of order `p^e` (it is a quotient of
`C_M ⧸ N_{L/M} C_L`, which is cyclic of order `p^e` by the prime-power hypothesis) and the
quotient is cyclic of order `m` (by induction on `n`, since `m < n`).  An extension of a cyclic
group of order `m` by a cyclic group of order `p^e` with `gcd(p^e, m) = 1` is cyclic, i.e.
isomorphic to `ℤ/n`, which is the content of
`NK.GroupTheory.Cyclic.isCyclic_of_cyclic_subgroup_cyclic_quotient`.

The only two ingredients from class field theory that are used are unconditional here:

* Hasse's index theorem `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`, which identifies
  `[C_K : N_{L/K} C_L] = [L : K]` for cyclic `L/K` and is what makes the orders of the pieces of
  the exact sequence the ones computed above;
* the transitivity and monotonicity of the norm class subgroups along a tower
  (`NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans`,
  `NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower`).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.GlobalCFTdeep.Brauer

open NK.GlobalCFT

/-! ## Arithmetic lemmas on the `p`-part of a natural number -/

/-- The `p`-part `p ^ n.factorization p` of `n` divides `n`. -/
private lemma pow_factorization_dvd {n p : ℕ} (hp : p.Prime) : p ^ n.factorization p ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hn, Nat.factorization_pow,
      hp.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_le_iff]

/-- The `p`-part of `n` is coprime to the complementary factor `n / p ^ n.factorization p`. -/
private lemma coprime_pow_factorization_div {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (p ^ n.factorization p).Coprime (n / p ^ n.factorization p) :=
  (Nat.coprime_ordCompl hp hn).pow_left _

/-! ## The range of a lifted homomorphism -/

/-- Lifting a homomorphism `f` which kills `N` to the quotient `G ⧸ N` does not change its
range. -/
private lemma range_lift_eq {G M : Type*} [Group G] [Group M] (N : Subgroup G) [N.Normal]
    (f : G →* M) (hf : N ≤ f.ker) :
    (QuotientGroup.lift N f hf).range = f.range := by
  ext y
  rw [MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact ⟨x, (QuotientGroup.lift_mk' N hf x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨QuotientGroup.mk' N x, QuotientGroup.lift_mk' N hf x⟩

/-! ## The induction over the degree -/

/-- **Strong induction over the degree**: the norm class quotient of a cyclic extension of number
fields is cyclic, assuming this in every prime-power degree. -/
private theorem isCyclic_normClassQuotient_aux
    (h : ∀ {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
      [FiniteDimensional E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)],
      (∃ p k : ℕ, p.Prime ∧ 0 < k ∧ Nat.card (F ≃ₐ[E] F) = p ^ k) →
      IsCyclic (IdeleClassGroup E ⧸ Idele.normClassSubgroup E F)) :
    ∀ n, ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
      Nat.card (L ≃ₐ[K] L) = n →
      IsCyclic (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K L _ _ _ _ _ _ _ _ hcard
    by_cases hn1 : n = 1
    · -- ### the trivial extension: the quotient is trivial
      have hdeg : Module.finrank K L = 1 := by
        rw [← IsGalois.card_aut_eq_finrank K L, hcard, hn1]
      have hidx : (Idele.normClassSubgroup K L).index = 1 := by
        rw [index_eq_finrank_of_isCyclic, hdeg]
      have htop : Idele.normClassSubgroup K L = ⊤ := Subgroup.index_eq_one.mp hidx
      rw [htop]
      haveI : Subsingleton (IdeleClassGroup K ⧸ (⊤ : Subgroup (IdeleClassGroup K))) :=
        QuotientGroup.subsingleton_quotient_top
      exact isCyclic_of_subsingleton
    · -- ### the general case
      have hnpos : 0 < n := by
        rw [← hcard]
        exact Nat.card_pos
      obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
      let e : ℕ := n.factorization p
      let P : ℕ := p ^ e
      have hPdvd : P ∣ n := pow_factorization_dvd (p := p) hpprime
      have hepos : 0 < e := hpprime.factorization_pos_of_dvd hnpos.ne' hpdvd
      have hPpos : 0 < P := pow_pos hpprime.pos e
      have hPone : 1 < P := Nat.one_lt_pow hepos.ne' hpprime.one_lt
      let m : ℕ := n / P
      have hmP : m * P = n := Nat.div_mul_cancel hPdvd
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | hmm
        · rw [h0, zero_mul] at hmP
          exact absurd hmP.symm hnpos.ne'
        · exact hmm
      by_cases hm1 : m = 1
      · -- #### `n = p ^ e` is a prime power: apply the hypothesis
        have hnP : n = P := by rw [← hmP, hm1, one_mul]
        refine h (E := K) (F := L) ⟨p, e, hpprime, hepos, ?_⟩
        rw [hcard]
        exact hnP
      · -- #### `m > 1`: pass to the fixed field of the Sylow `p`-subgroup
        have hm_lt : m < n := by
          calc m < m * P := lt_mul_of_one_lt_right hmpos hPone
            _ = n := hmP
        obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
        have hgord : orderOf g = n := by
          rw [orderOf_eq_card_of_forall_mem_zpowers hgen, ← hcard]
        have hm_dvd : m ∣ n := ⟨P, hmP.symm⟩
        have hgpow : orderOf (g ^ m) = P := by
          rw [orderOf_pow, hgord, Nat.gcd_eq_right hm_dvd, ← hmP]
          exact Nat.mul_div_right P hmpos
        let H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers (g ^ m)
        have hHcard : Nat.card ↥H = P := by
          show Nat.card ↥(Subgroup.zpowers (g ^ m)) = P
          rw [Nat.card_zpowers, hgpow]
        haveI hHnormal : H.Normal := Subgroup.normal_of_isMulCommutative H
        let M : IntermediateField K L := IntermediateField.fixedField H
        haveI : FiniteDimensional K ↥M := inferInstance
        haveI : NumberField ↥M := NumberField.of_module_finite K ↥M
        haveI : IsGalois K ↥M := IsGalois.of_fixedField_normal_subgroup H
        haveI : FiniteDimensional ↥M L := inferInstance
        haveI : IsGalois ↥M L := inferInstance
        have hML : Module.finrank ↥M L = P := by
          show Module.finrank ↥(IntermediateField.fixedField H) L = P
          rw [IntermediateField.finrank_fixedField_eq_card H, hHcard]
        have hKL : Module.finrank K L = n := (IsGalois.card_aut_eq_finrank K L).symm.trans hcard
        have hKM : Module.finrank K ↥M = m := by
          have hmul := Module.finrank_mul_finrank K ↥M L
          rw [hML, hKL] at hmul
          exact Nat.eq_div_of_mul_eq_left hPpos.ne' hmul
        have hMcard : Nat.card (↥M ≃ₐ[K] ↥M) = m := by
          rw [IsGalois.card_aut_eq_finrank K ↥M, hKM]
        have hLMcard : Nat.card (L ≃ₐ[↥M] L) = P := by
          rw [IsGalois.card_aut_eq_finrank ↥M L, hML]
        haveI hcycM : IsCyclic (↥M ≃ₐ[K] ↥M) :=
          (IsGalois.normalAutEquivQuotient (K := K) (L := L) H).isCyclic.mp
            (isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H))
        haveI hcycLM : IsCyclic (L ≃ₐ[↥M] L) :=
          (IntermediateField.subgroupEquivAlgEquiv (F := K) (E := L) H).isCyclic.mp
            (Subgroup.isCyclic_zpowers (g ^ m))
        -- the two inputs of the assembly
        haveI hIH : IsCyclic (IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥M) :=
          ih m hm_lt hMcard
        haveI hh : IsCyclic (IdeleClassGroup ↥M ⧸ Idele.normClassSubgroup ↥M L) :=
          h (E := ↥M) (F := L) ⟨p, e, hpprime, hepos, hLMcard⟩
        -- the norm class subgroups of the tower
        let NL : Subgroup (IdeleClassGroup K) := Idele.normClassSubgroup K L
        let NM : Subgroup (IdeleClassGroup K) := Idele.normClassSubgroup K ↥M
        let NLM : Subgroup (IdeleClassGroup ↥M) := Idele.normClassSubgroup ↥M L
        have hle : NL ≤ NM := Idele.normClassSubgroup_le_of_tower
        haveI hfinL : NL.FiniteIndex :=
          Subgroup.finiteIndex_iff.mpr (by
            show (Idele.normClassSubgroup K L).index ≠ 0
            rw [index_eq_finrank_of_isCyclic, hKL]
            exact hnpos.ne')
        have hAcard : Nat.card (IdeleClassGroup K ⧸ NL) = n := by
          rw [(Subgroup.index_eq_card NL).symm,
            (show NL.index = Module.finrank K L from index_eq_finrank_of_isCyclic), hKL]
        have hQcard : Nat.card ((IdeleClassGroup K ⧸ NL) ⧸
            NM.map (QuotientGroup.mk' NL)) = m := by
          have hiso := QuotientGroup.quotientQuotientEquivQuotient (N := NL) (M := NM) hle
          rw [Nat.card_congr hiso.toEquiv, (Subgroup.index_eq_card NM).symm,
            (show NM.index = Module.finrank K ↥M from index_eq_finrank_of_isCyclic), hKM]
        -- the subgroup `S = N_M ⧸ N_L` of `A = C_K ⧸ N_L`
        let S : Subgroup (IdeleClassGroup K ⧸ NL) := NM.map (QuotientGroup.mk' NL)
        have hScard : Nat.card ↥S = P := by
          have h1 := Subgroup.card_mul_index S
          have h2 : S.index = m := (Subgroup.index_eq_card S).trans hQcard
          rw [hAcard, h2, ← hmP, mul_comm m P] at h1
          exact Nat.mul_right_cancel hmpos h1
        have hScop : (Nat.card ↥S).Coprime (Nat.card ((IdeleClassGroup K ⧸ NL) ⧸ S)) := by
          rw [hScard, show Nat.card ((IdeleClassGroup K ⧸ NL) ⧸ S) = m from hQcard]
          exact (Nat.coprime_ordCompl hpprime hnpos.ne').pow_left e
        -- `S` is cyclic: it is a quotient of `C_M ⧸ N_{L/M} C_L`
        let f : IdeleClassGroup ↥M →* (IdeleClassGroup K ⧸ NL) :=
          (QuotientGroup.mk' NL).comp (IdeleClassGroup.normClassHom K ↥M)
        have hfker : NLM ≤ f.ker := by
          intro x hx
          rw [MonoidHom.mem_ker]
          obtain ⟨y, rfl⟩ := Idele.mem_normClassSubgroup.mp hx
          show QuotientGroup.mk' NL ((IdeleClassGroup.normClassHom K ↥M)
            ((IdeleClassGroup.normClassHom ↥M L) y)) = 1
          rw [NormGroup.globalCFT_normClassHom_trans y]
          exact (QuotientGroup.eq_one_iff _).mpr (Idele.mem_normClassSubgroup.mpr ⟨y, rfl⟩)
        let φ : (IdeleClassGroup ↥M ⧸ NLM) →* (IdeleClassGroup K ⧸ NL) :=
          QuotientGroup.lift NLM f hfker
        have hfrange : f.range = S := by
          show ((QuotientGroup.mk' NL).comp (IdeleClassGroup.normClassHom K ↥M)).range =
            NM.map (QuotientGroup.mk' NL)
          rw [MonoidHom.range_comp, ← Idele.normClassSubgroup_eq_range]
        have hφrange : φ.range = S := by
          show (QuotientGroup.lift NLM f hfker).range = S
          rw [range_lift_eq NLM f hfker, hfrange]
        have hScyc : IsCyclic ↥S := by
          rw [← hφrange]
          exact isCyclic_of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
        -- `A ⧸ S ≅ C_K ⧸ N_M` is cyclic: the induction hypothesis
        have hQcyc : IsCyclic ((IdeleClassGroup K ⧸ NL) ⧸ S) := by
          have hiso := QuotientGroup.quotientQuotientEquivQuotient (N := NL) (M := NM) hle
          exact hiso.isCyclic.mpr hIH
        exact NK.GroupTheory.Cyclic.isCyclic_of_cyclic_subgroup_cyclic_quotient
          S hScyc hQcyc hScop

/-- **The norm class quotient of a cyclic extension of number fields is cyclic**, assuming this in
every prime-power degree.  Reduction of the general case to the prime-power case (see the module
docstring for the proof). -/
theorem isCyclic_normQuotient_of_primePower
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (h : ∀ {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
      [FiniteDimensional E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)],
      (∃ p k : ℕ, p.Prime ∧ 0 < k ∧ Nat.card (F ≃ₐ[E] F) = p ^ k) →
      IsCyclic (NK.GlobalCFT.IdeleClassGroup E ⧸
        NK.GlobalCFT.Idele.normClassSubgroup E F)) :
    IsCyclic (NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K L) :=
  isCyclic_normClassQuotient_aux h _ rfl

end NK.GlobalCFTdeep.Brauer
