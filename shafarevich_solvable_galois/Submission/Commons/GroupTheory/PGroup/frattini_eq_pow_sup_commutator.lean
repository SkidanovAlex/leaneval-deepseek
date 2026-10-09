import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.GroupTheory.Frattini
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped IsMulCommutative

namespace Commons.GroupTheory.PGroup

open Subgroup

/-- The radical of the lattice of submodules of a module over a field is trivial:
every nonzero element of the module is outside some maximal submodule. -/
theorem Submodule.radical_eq_bot {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    Order.radical (Submodule K V) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  by_contra hx0
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hx0
  have hsurj : Function.Surjective (f : V → K) := by
    rw [← LinearMap.range_eq_top]
    rw [Submodule.eq_top_iff']
    intro y
    have : y = f (y • x) := by rw [map_smul, hf, smul_eq_mul, mul_one]
    rw [this]
    exact LinearMap.mem_range_self f (y • x)
  have hcoatom : IsCoatom f.ker := by
    rw [LinearMap.ker]
    rw [Submodule.isCoatom_comap_iff (f := f) hsurj (p := ⊥)]
    exact isCoatom_bot
  have hle : Order.radical (Submodule K V) ≤ f.ker := Order.radical_le_coatom hcoatom
  have hxker : x ∈ f.ker := hle hx
  rw [LinearMap.mem_ker] at hxker
  exact one_ne_zero (hf.symm.trans hxker)

/-- The radical of the lattice of additive subgroups of an elementary abelian `p`-group is
trivial. -/
theorem AddSubgroup.radical_eq_bot {p : ℕ} [Fact p.Prime] {A : Type*} [AddCommGroup A]
    [Module (ZMod p) A] : Order.radical (AddSubgroup A) = ⊥ := by
  let e2 : AddSubgroup A ≃o Submodule (ZMod p) A := AddSubgroup.toZModSubmodule p
  have h : e2 (Order.radical (AddSubgroup A)) = ⊥ := by
    rw [OrderIso.map_radical e2, Submodule.radical_eq_bot]
  have hsymm := congrArg e2.symm h
  rw [OrderIso.symm_apply_apply, OrderIso.map_bot e2.symm] at hsymm
  exact hsymm

/-- The Frattini subgroup of a finite elementary abelian `p`-group is trivial. -/
theorem frattini_eq_bot_of_elementary_abelian {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    [IsMulCommutative H] (hexp : ∀ x : H, x ^ p = 1) : frattini H = ⊥ := by
  have hmod : ∀ x : Additive H, p • x = 0 := by
    intro x
    induction x using Additive.rec with
    | ofMul y => rw [← ofMul_pow, hexp y]; rfl
  letI : Module (ZMod p) (Additive H) := AddCommGroup.zmodModule hmod
  have hA : Order.radical (AddSubgroup (Additive H)) = ⊥ :=
    @AddSubgroup.radical_eq_bot p _ (Additive H) _ _
  have hH : Order.radical (Subgroup H) = ⊥ := by
    let e1 : Subgroup H ≃o AddSubgroup (Additive H) := Subgroup.toAddSubgroup
    have h : e1 (Order.radical (Subgroup H)) = ⊥ := by
      rw [OrderIso.map_radical e1, hA]
    have hsymm := congrArg e1.symm h
    rw [OrderIso.symm_apply_apply, OrderIso.map_bot e1.symm] at hsymm
    exact hsymm
  rw [frattini]
  exact hH

/-- If a subgroup is the preimage of a coatom under a surjective homomorphism, then the
coatom is a coatom. -/
theorem isCoatom_of_isCoatom_comap_of_surjective
    {G H : Type*} [Group G] [Group H] {φ : G →* H} (hφ : Function.Surjective φ)
    {P : Subgroup H} (hP : IsCoatom (P.comap φ)) : IsCoatom P := by
  constructor
  · intro hPt
    exact hP.1 (by rw [hPt, Subgroup.comap_top])
  · intro Q hQ
    have hQ' : P.comap φ < Q.comap φ := (Subgroup.comap_lt_comap_of_surjective hφ).mpr hQ
    have hQtop : Q.comap φ = ⊤ := hP.2 _ hQ'
    calc Q = (Q.comap φ).map φ := (Subgroup.map_comap_eq_self_of_surjective hφ Q).symm
      _ = ⊤ := by rw [hQtop, Subgroup.map_top_of_surjective φ hφ]

/-- The quotient of a finite `p`-group by a maximal subgroup has order `p`. -/
theorem natCard_quotient_coatom_eq_prime {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) :
    Nat.card (G ⧸ M) = p := by
  haveI hNil : Group.IsNilpotent G := hG.isNilpotent
  haveI hMnorm : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M (Group.normalizerCondition_of_isNilpotent) hM
  have hbot : IsCoatom (⊥ : Subgroup (G ⧸ M)) := by
    refine isCoatom_of_isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective M) ?_
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact hM
  haveI : IsSimpleOrder (Subgroup (G ⧸ M)) := isSimpleOrder_iff_isCoatom_bot.mpr hbot
  have hq : IsPGroup p (G ⧸ M) := hG.to_quotient M
  have hnt : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM.ne_top
  obtain ⟨n, hnpos, hn⟩ := hq.nontrivial_iff_card.mp hnt
  have hn1 : n = 1 := by
    by_contra hne
    have h2 : 2 ≤ n := by omega
    have hle : p ^ 1 ≤ Nat.card (G ⧸ M) := by
      rw [hn]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).one_le (by omega : 1 ≤ n)
    obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (Fact.out : p.Prime) hq hle
    rcases IsSimpleOrder.eq_bot_or_eq_top H with hHbot | hHtop
    · rw [hHbot, Subgroup.card_bot, pow_one] at hHcard
      exact (Fact.out : p.Prime).ne_one hHcard.symm
    · rw [hHtop, Subgroup.card_top, hn] at hHcard
      have : n = 1 := Nat.pow_right_injective (Fact.out : p.Prime).one_lt hHcard
      omega
  rw [hn, hn1, pow_one]

/-- The subgroup generated by `p`-th powers is normal. -/
theorem closure_range_pow_normal {p : ℕ} {G : Type*} [Group G] :
    (Subgroup.closure (Set.range (fun x : G => x ^ p))).Normal := by
  have hconj : ∀ h x : G, h * x ^ p * h⁻¹ = (h * x * h⁻¹) ^ p := by
    intro h x
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  rw [← Subgroup.normalizer_eq_top_iff]
  have hnorm : Subgroup.normalizer (Set.range (fun x : G => x ^ p)) = ⊤ := by
    rw [eq_top_iff, Subgroup.le_set_normalizer_iff]
    intro h hh g hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨h * x * h⁻¹, (hconj h x).symm⟩
  apply top_le_iff.mp
  rw [← hnorm]
  exact Subgroup.normalizer_le_normalizer_closure _

theorem frattini_eq_pow_sup_commutator {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) :
    frattini G = Subgroup.closure (Set.range (fun x : G => x ^ p)) ⊔ commutator G := by
  set P := Subgroup.closure (Set.range (fun x : G => x ^ p)) with hPdef
  set C := commutator G with hCdef
  haveI hPnorm : P.Normal := closure_range_pow_normal
  haveI hN : (P ⊔ C).Normal := inferInstance
  apply le_antisymm
  · -- frattini G ≤ P ⊔ C
    have hcomm : IsMulCommutative (G ⧸ (P ⊔ C)) := by
      rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
      exact le_sup_right
    have hexp : ∀ x : G ⧸ (P ⊔ C), x ^ p = 1 := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (P ⊔ C) x
      rw [← map_pow, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (g ^ p)).mpr
        (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨g, rfl⟩))
    have hfrattini : frattini (G ⧸ (P ⊔ C)) = ⊥ := frattini_eq_bot_of_elementary_abelian hexp
    have hle := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective (P ⊔ C))
    rw [hfrattini, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hle
    exact hle
  · -- P ⊔ C ≤ frattini G
    apply sup_le
    · rw [frattini, Order.radical]
      apply le_iInf; intro M
      apply le_iInf; intro hM
      rw [Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      haveI : Group.IsNilpotent G := hG.isNilpotent
      haveI hMnorm : M.Normal :=
        Subgroup.NormalizerCondition.normal_of_coatom M (Group.normalizerCondition_of_isNilpotent) hM
      have hcard : Nat.card (G ⧸ M) = p := natCard_quotient_coatom_eq_prime hG hM
      have hx1 : (QuotientGroup.mk' M x : G ⧸ M) ^ p = 1 := by
        have := pow_card_eq_one' (G := G ⧸ M) (x := (QuotientGroup.mk' M x : G ⧸ M))
        rwa [hcard] at this
      rw [← map_pow, QuotientGroup.mk'_apply] at hx1
      exact (QuotientGroup.eq_one_iff (x ^ p)).mp hx1
    · rw [frattini, Order.radical]
      apply le_iInf; intro M
      apply le_iInf; intro hM
      have hcard : Nat.card (G ⧸ M) = p := natCard_quotient_coatom_eq_prime hG hM
      haveI : Group.IsNilpotent G := hG.isNilpotent
      haveI hMnorm : M.Normal :=
        Subgroup.NormalizerCondition.normal_of_coatom M (Group.normalizerCondition_of_isNilpotent) hM
      haveI : IsCyclic (G ⧸ M) := isCyclic_of_prime_card hcard
      haveI : IsMulCommutative (G ⧸ M) := IsCyclic.isMulCommutative
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp ‹IsMulCommutative (G ⧸ M)›

end Commons.GroupTheory.PGroup