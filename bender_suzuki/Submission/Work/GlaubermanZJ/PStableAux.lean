import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.PStable.pstable_representation
import Submission.Work.PStable.conjData
import Submission.Work.PStable.conjRep_eq_one_iff
import Submission.Work.PGroup.All
import Submission.Work.Fitting.Main
import Submission.Work.HallHigman.isPSolvable_quotient_prime
import Submission.Work.HallHigman.exists_ne_zero_fixed_of_isPGroup
import Submission.Work.LocalPrelim.conjRep_sub_one_pow_four_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end


/-!
# Auxiliary material of the area `GlaubermanZJ` (namespaced copy)

This module holds the §6 material of the area (`pstable_of_abelianSylowTwo` and its support
lemmas) in the namespace `Work.GlaubermanZJ.PStableAux`.  The canonical import path for the
same material is `Submission.Work.GlaubermanZJ.pstable_of_abelianSylowTwo`; this module exists
so that `theoremA` and `GlaubermanZJ_reduced` have a stable import path.
-/
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 6000000

open scoped commutatorElement IsMulCommutative

namespace Work.GlaubermanZJ.PStableAux

universe u

/-! ## 1. Elementary bridges

`HasAbelianSylowTwo` is expressed with `Submission.Blueprint.IsAbelianSubgroup`; the
representation-theoretic and `2`-group lemmas of the workspace use `IsMulCommutative` on the
subtype, and "every `2`-subgroup is abelian".  We record the translations, and the fact that
"all `2`-subgroups are abelian" passes to quotients (needed for the induction). -/

lemma isAbelianSubgroup_iff_isMulCommutative_crux {G : Type*} [Group G] (A : Subgroup G) :
    Submission.Blueprint.IsAbelianSubgroup A ↔ IsMulCommutative ↥A := by
  constructor
  · intro h
    exact ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩
  · intro h a ha b hb
    simpa using h.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩

lemma hasAbelianSylowTwo_iff_commutative (G : Type*) [Group G] :
    HasAbelianSylowTwo G ↔ ∀ Q : Sylow 2 G, IsMulCommutative ↥(Q : Subgroup G) := by
  constructor
  · intro h Q
    exact (isAbelianSubgroup_iff_isMulCommutative_crux (Q : Subgroup G)).mp (h Q)
  · intro h Q
    exact (isAbelianSubgroup_iff_isMulCommutative_crux (Q : Subgroup G)).mpr (h Q)

lemma allTwoSubgroups_commutative_of_sylow {G : Type*} [Group G] [Finite G]
    (h : ∀ Q : Sylow 2 G, IsMulCommutative ↥(Q : Subgroup G)) :
    ∀ S : Subgroup G, IsPGroup 2 ↥S → IsMulCommutative ↥S :=
  fun S hS => Work.PStable.Quad.isMulCommutative_of_isPGroup_two_of_sylow h hS

lemma allTwoSubgroups_commutative_of_hasAbelianSylowTwo {G : Type*} [Group G] [Finite G]
    (h : HasAbelianSylowTwo G) :
    ∀ S : Subgroup G, IsPGroup 2 ↥S → IsMulCommutative ↥S :=
  allTwoSubgroups_commutative_of_sylow ((hasAbelianSylowTwo_iff_commutative G).mp h)

lemma allTwoSubgroups_commutative_quotient {G : Type*} [Group G] [Finite G]
    (h : ∀ S : Subgroup G, IsPGroup 2 ↥S → IsMulCommutative ↥S) (N : Subgroup G) [N.Normal] :
    ∀ S : Subgroup (G ⧸ N), IsPGroup 2 ↥S → IsMulCommutative ↥S := fun S hS =>
  Work.PStable.Quad.isMulCommutative_of_isPGroup_two_of_surjective
    (ψ := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) h hS

lemma sylow_commutative_quotient {G : Type*} [Group G] [Finite G]
    (h : ∀ S : Subgroup G, IsPGroup 2 ↥S → IsMulCommutative ↥S) (N : Subgroup G) [N.Normal] :
    ∀ Q : Sylow 2 (G ⧸ N), IsMulCommutative ↥(Q : Subgroup (G ⧸ N)) := fun Q =>
  allTwoSubgroups_commutative_quotient h N (Q : Subgroup (G ⧸ N)) Q.isPGroup'

/-! ## 2. The failure of `p`-stability, in element form

A failure of `IsPStable p G` is the existence of a normal `p`-subgroup `P`, a `p`-subgroup `A`
with `[[P,A],A] = 1` and an element `x ∈ A` whose coset modulo `C_G(P)` is not in `O_p`. -/

/-- `IsBad p G P` says that `p`-stability of `G` fails at the normal `p`-subgroup `P`. -/
def IsBad (p : ℕ) (G : Type*) [Group G] (P : Subgroup G) [P.Normal] : Prop :=
  IsPGroup p P ∧ ∃ (A : Subgroup G) (x : G), IsPGroup p A ∧ x ∈ A ∧ ⁅⁅P, A⁆, A⁆ = ⊥ ∧
    (QuotientGroup.mk' (Subgroup.centralizer (P : Set G))) x ∉
      Work.HallHigman.pCore p (G ⧸ Subgroup.centralizer (P : Set G))

theorem not_isPStable_of_isBad {p : ℕ} (G : Type*) [Group G] {P : Subgroup G} [P.Normal]
    (h : IsBad p G P) : ¬ IsPStable p G := by
  intro hstable
  obtain ⟨hPp, A, x, hAp, hxA, hcomm, hbad⟩ := h
  exact hbad (hstable P hPp A hAp hcomm (Subgroup.mem_map_of_mem _ hxA))

theorem exists_isBad_of_not_isPStable {p : ℕ} (G : Type*) [Group G] (h : ¬ IsPStable p G) :
    ∃ (P : Subgroup G) (hPn : P.Normal), @IsBad p G _ P hPn := by
  simp only [IsPStable] at h
  push Not at h
  obtain ⟨P, hPn, hPp, A, hAp, hcomm, hbad⟩ := h
  obtain ⟨x, hxA, hxbad⟩ : ∃ x ∈ A,
      (QuotientGroup.mk' (Subgroup.centralizer (P : Set G))) x ∉
        Work.HallHigman.pCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
    by_contra hcon
    push Not at hcon
    exact hbad fun y hy => by
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      exact hcon a ha
  exact ⟨P, hPn, hPp, A, x, hAp, hxA, hcomm, hxbad⟩

/-! ## 3. Minimal normal `p`-subgroups are elementary abelian

We need: a minimal normal subgroup which is a `p`-group has exponent `p` (commutativity is
`Work.Fitting.isMinimalNormal_isPGroup_commutative`).  The subgroup of elements of order
dividing `p` is characteristic in `H`, hence normal in the ambient group, and non-trivial by
the existence of an element of order `p`; minimality forces it to be all of `H`. -/

/-- A non-trivial finite `p`-group has a non-identity element of order dividing `p`. -/
lemma exists_ne_one_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) (hne : Nontrivial G) : ∃ y : G, y ≠ 1 ∧ y ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  obtain ⟨m, hm⟩ := hG.dvd_orderOf hg
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, mul_zero] at hm
      exact absurd hm (orderOf_pos g).ne'
    · exact hpos
  refine ⟨g ^ m, ?_, ?_⟩
  · intro h
    have hdvd : orderOf g ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h
    have hle : p * m ≤ m := Nat.le_of_dvd hmpos (hm ▸ hdvd)
    have := hp.two_le
    nlinarith
  · rw [← pow_mul, mul_comm m p, ← hm, pow_orderOf_eq_one]

/-- A minimal normal subgroup which is a `p`-group has exponent `p`. -/
lemma isMinimalNormal_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hH : Work.Fitting.IsMinimalNormal H) (hHp : IsPGroup p ↥H) :
    ∀ y : ↥H, y ^ p = 1 := by
  classical
  obtain ⟨hHn, hHne, hHmin⟩ := hH
  haveI : H.Normal := hHn
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative ↥H :=
    Work.Fitting.isMinimalNormal_isPGroup_commutative p G hp ⟨hHn, hHne, hHmin⟩ hHp
  letI : CommMonoid ↥H := { (inferInstance : Monoid ↥H) with
    mul_comm := fun a b => hcomm.is_comm.comm a b }
  -- the subgroup of elements of order dividing `p`
  let S : Subgroup ↥H :=
    { carrier := {y : ↥H | y ^ p = 1}
      one_mem' := by rw [Set.mem_setOf_eq]; exact one_pow p
      mul_mem' := fun ha hb => by rw [Set.mem_setOf_eq, mul_pow, ha, hb, one_mul]
      inv_mem' := fun ha => by rw [Set.mem_setOf_eq, inv_pow, ha, inv_one] }
  have hchar : S.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show (φ z) ^ p = 1
      rw [← map_pow, hz, map_one]
    · intro hy
      refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
      show (φ.symm y) ^ p = 1
      rw [← map_pow, show y ^ p = 1 from hy, map_one]
  haveI : S.Characteristic := hchar
  have hSne : S.map H.subtype ≠ ⊥ := by
    obtain ⟨y, hy1, hyp⟩ :=
      exists_ne_one_pow_eq_one hp hHp ((Subgroup.nontrivial_iff_ne_bot H).mpr hHne)
    intro hbot
    have hmem : (y : G) ∈ S.map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype (show y ∈ S from hyp)
    rw [hbot] at hmem
    exact hy1 (Subtype.ext (by simpa using hmem))
  have hSeq : S.map H.subtype = H :=
    hHmin (S.map H.subtype) ConjAct.normal_of_characteristic_of_normal
      (Subgroup.map_subtype_le _) hSne
  intro y
  have hmem : (y : G) ∈ S.map H.subtype := by rw [hSeq]; exact y.2
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
  have hzy' : z = y := Subtype.ext hzy
  rw [← hzy']
  exact hz

variable {X : Type*} [Group X]

/-! ## 4. The conjugation representation of `X/C_X(M)` on an elementary abelian normal subgroup -/

/-- Conjugation gives a representation of `X / C_X(M)` on an elementary abelian normal subgroup
`M` of exponent `p`. -/
noncomputable def conjRepQuotient (M : Subgroup X) [M.Normal] [IsMulCommutative ↥M]
    {p : ℕ} [Fact (∀ y : ↥M, y ^ p = 1)] :
    X ⧸ Subgroup.centralizer (M : Set X) →* Module.End (ZMod p) (Additive ↥M) :=
  QuotientGroup.lift (Subgroup.centralizer (M : Set X)) (Work.PStable.conjRep (p := p) M)
    (fun g hg => by
      rw [MonoidHom.mem_ker]
      exact (Work.PStable.conjRep_eq_one_iff (p := p) M g).mpr hg)

@[simp] lemma conjRepQuotient_mk (M : Subgroup X) [M.Normal] [IsMulCommutative ↥M]
    {p : ℕ} [Fact (∀ y : ↥M, y ^ p = 1)] (g : X) :
    conjRepQuotient (p := p) M (QuotientGroup.mk' (Subgroup.centralizer (M : Set X)) g)
      = Work.PStable.conjRep (p := p) M g :=
  QuotientGroup.lift_mk' _ _ _

lemma conjRepQuotient_injective (M : Subgroup X) [M.Normal] [IsMulCommutative ↥M]
    {p : ℕ} [Fact (∀ y : ↥M, y ^ p = 1)] :
    Function.Injective (conjRepQuotient (p := p) M) := by
  rw [conjRepQuotient, QuotientGroup.injective_lift_iff]
  ext g
  rw [MonoidHom.mem_ker]
  exact (Work.PStable.conjRep_eq_one_iff (p := p) M g).symm

/-! ## 5. The final contradiction: a quadratic `p`-element on a minimal normal `p`-subgroup -/

theorem false_of_isMinimalNormal_quadratic {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hpne : p ≠ 2)
    {H : Subgroup X} [H.Normal] (hH : Work.Fitting.IsMinimalNormal H) (hHp : IsPGroup p ↥H)
    (hpsQ : Work.HallHigman.IsPSolvable p (X ⧸ Subgroup.centralizer (H : Set X)))
    (h2Q : 5 ≤ p ∨ ∀ Q : Sylow 2 (X ⧸ Subgroup.centralizer (H : Set X)),
      IsMulCommutative ↥(Q : Subgroup (X ⧸ Subgroup.centralizer (H : Set X))))
    (hOp : Work.HallHigman.pCore p (X ⧸ Subgroup.centralizer (H : Set X)) = ⊥)
    {x : X} (hxp : IsPGroup p ↥(Subgroup.closure {x}))
    (hquad : ⁅⁅H, Subgroup.closure {x}⁆, Subgroup.closure {x}⁆ = ⊥)
    (hbad : x ∉ ((Work.HallHigman.pCore p (X ⧸ Subgroup.centralizer (H : Set X))).comap
        (QuotientGroup.mk' (Subgroup.centralizer (H : Set X))))) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hHn, hHne, hHmin⟩ := hH
  haveI : H.Normal := hHn
  have hHcomm : IsMulCommutative ↥H :=
    Work.Fitting.isMinimalNormal_isPGroup_commutative p X hp ⟨hHn, hHne, hHmin⟩ hHp
  have hHexp : ∀ y : ↥H, y ^ p = 1 := isMinimalNormal_pow_eq_one hp ⟨hHn, hHne, hHmin⟩ hHp
  haveI : Fact (∀ y : ↥H, y ^ p = 1) := ⟨hHexp⟩
  let C : Subgroup X := Subgroup.centralizer (H : Set X)
  let A : Subgroup (X ⧸ C) := (Subgroup.closure {x}).map (QuotientGroup.mk' C)
  have hAp : IsPGroup p ↥A := hxp.map (QuotientGroup.mk' C)
  have hcommChain : Work.LocalPrelim.commChain H (Subgroup.closure {x}) 2 = ⊥ := hquad
  have hquadA : ∀ a ∈ A, (conjRepQuotient (p := p) H a - 1) ^ 2 = 0 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    rw [conjRepQuotient_mk]
    apply LinearMap.ext
    intro v
    obtain ⟨m, rfl⟩ := Additive.ofMul.surjective v
    rw [Work.LocalPrelim.conjRep_sub_one_pow_apply (M := H) (p := p) y 2 m]
    have hm := Work.LocalPrelim.iterate_conjMinusOne_mem H (Subgroup.closure {x}) y hy m 2
    rw [hcommChain, Subgroup.mem_bot] at hm
    have hz : ((Work.LocalPrelim.conjMinusOne H y)^[2]) m = 1 := Subtype.ext (by simpa using hm)
    rw [hz]
    rfl
  have hAbot : A = ⊥ :=
    Work.PStable.pstable_representation hp (hp.odd_of_ne_two hpne) hpsQ h2Q
      (conjRepQuotient (p := p) H) (conjRepQuotient_injective H) hOp A hAp hquadA
  have hmem : (QuotientGroup.mk' C) x ∈ A :=
    Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
  rw [hAbot] at hmem
  have hx1 : (QuotientGroup.mk' C) x = 1 := Subgroup.mem_bot.mp hmem
  refine hbad ?_
  rw [Subgroup.mem_comap, hx1, hOp]
  exact Subgroup.mem_bot.mpr rfl

/-! ## 6. Glauberman's Lemma 3.4: `O_p(X/C_X(K)) = 1` for a minimal normal `p`-subgroup -/

theorem pCore_quotient_centralizer_eq_bot_of_isMinimalNormal {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {K : Subgroup X} [K.Normal] (hK : Work.Fitting.IsMinimalNormal K)
    (hKp : IsPGroup p ↥K) :
    Work.HallHigman.pCore p (X ⧸ Subgroup.centralizer (K : Set X)) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKn, hKne, hKmin⟩ := hK
  haveI : K.Normal := hKn
  have hKcomm : IsMulCommutative ↥K :=
    Work.Fitting.isMinimalNormal_isPGroup_commutative p X hp ⟨hKn, hKne, hKmin⟩ hKp
  have hKexp : ∀ y : ↥K, y ^ p = 1 := isMinimalNormal_pow_eq_one hp ⟨hKn, hKne, hKmin⟩ hKp
  haveI : Fact (∀ y : ↥K, y ^ p = 1) := ⟨hKexp⟩
  by_contra hQne
  let C : Subgroup X := Subgroup.centralizer (K : Set X)
  let Q : Subgroup (X ⧸ C) := Work.HallHigman.pCore p (X ⧸ C)
  have hQp : IsPGroup p ↥Q := Work.HallHigman.isPGroup_pCore
  let Q' : Subgroup X := Q.comap (QuotientGroup.mk' C)
  have hQ'def : Q' = Q.comap (QuotientGroup.mk' C) := rfl
  haveI : Q'.Normal := Subgroup.normal_comap _
  have hCQ' : C ≤ Q' := by
    intro g hg
    rw [Subgroup.mem_comap]
    have : (QuotientGroup.mk' C) g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    rw [this]
    exact Subgroup.one_mem _
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  obtain ⟨v, hv0, hvfix⟩ :=
    Work.HallHigman.exists_ne_zero_fixed_of_isPGroup (conjRepQuotient (p := p) K) hQp
      (inferInstance : Nontrivial (Additive ↥K))
  obtain ⟨k, rfl⟩ := Additive.ofMul.surjective v
  have hk1 : k ≠ 1 := fun h => hv0 (by rw [h]; rfl)
  have hkfix : ∀ g ∈ Q', g * (k : X) * g⁻¹ = (k : X) := by
    intro g hg
    have hgQ : (QuotientGroup.mk' C) g ∈ Q := hg
    have h1 := hvfix ((QuotientGroup.mk' C) g) hgQ
    rw [conjRepQuotient_mk] at h1
    rw [Work.PStable.conjRep_apply] at h1
    have h2 : MulAut.conjNormal g k = k := Additive.ofMul.injective h1
    have h3 := congrArg (fun z : ↥K => (z : X)) h2
    simpa [MulAut.conjNormal_apply] using h3
  let F : Subgroup X := K ⊓ Subgroup.centralizer (Q' : Set X)
  have hFle : F ≤ K := inf_le_left
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hkK : (k : X) ∈ K := k.2
    have hkC : (k : X) ∈ Subgroup.centralizer (Q' : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h := hkfix g hg
      rwa [mul_inv_eq_iff_eq_mul] at h
    have : (k : X) ∈ F := ⟨hkK, hkC⟩
    rw [hbot] at this
    exact hk1 (Subtype.ext (Subgroup.mem_bot.mp this))
  have hFnorm : F.Normal := inferInstance
  have hFK : F = K := hKmin F hFnorm hFle hFne
  have hle : K ≤ Subgroup.centralizer (Q' : Set X) := hFK ▸ inf_le_right
  have hcomm1 : ⁅K, Q'⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  have hcomm2 : ⁅Q', K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm1
  have hQ'le : Q' ≤ C := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm2
  have hQeq : Q = ⊥ := by
    have hmap : Q'.map (QuotientGroup.mk' C) = Q := by
      have h := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) Q
      simpa [Q'] using h
    rw [← hmap]
    refine le_bot_iff.mp ?_
    calc Q'.map (QuotientGroup.mk' C) ≤ C.map (QuotientGroup.mk' C) := Subgroup.map_mono hQ'le
      _ = ⊥ := by
          rw [Subgroup.map_eq_bot_iff]
          rw [QuotientGroup.ker_mk']
  exact hQne hQeq


/-! ## 7. Two group-theoretic ingredients for the reduction steps

* a `p`-subgroup and a subgroup of `p'`-order intersect trivially;
* Glauberman's Lemma 5.3: an automorphism of a `p`-group `H` trivialising both `K ⊴ H` and
  `H/K` has order dividing `|K|` (so elements of `C_X(K) ∩ C_X(H/K)` have `p`-power order
  modulo `C_X(H)`). -/

lemma inf_eq_bot_of_isPGroup_of_isPiNat {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {P M : Subgroup X} (hP : IsPGroup p ↥P)
    (hM : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥M)) : P ⊓ M = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨hyP, hyM⟩ := hy
  have hdvdP : orderOf y ∣ Nat.card ↥P := Subgroup.orderOf_dvd_natCard P hyP
  have hdvdM : orderOf y ∣ Nat.card ↥M := Subgroup.orderOf_dvd_natCard M hyM
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hpk : orderOf y ∣ p ^ k := hk ▸ hdvdP
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hpk
  have hj0 : j = 0 := by
    by_contra hjne
    have hdvd : p ∣ orderOf y := by rw [hj]; exact dvd_pow_self p hjne
    exact (hM p hp (hdvd.trans hdvdM)) rfl
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

lemma conjNormal_pow_card_eq_one {X : Type*} [Group X] {p : ℕ} {K H : Subgroup X}
    [K.Normal] [H.Normal] (hKH : K ≤ H) (hHp : IsPGroup p ↥H) {y : X}
    (hyK : y ∈ Subgroup.centralizer (K : Set X))
    (hyHK : y ∈ Work.Fitting.sectionCentralizer K H) :
    (MulAut.conjNormal y : MulAut ↥H) ^ Nat.card ↥K = 1 := by
  classical
  set φ : MulAut ↥H := MulAut.conjNormal y with hφ
  have hcoey : ∀ z : ↥H, ((φ z : ↥H) : X) = y * (z : X) * y⁻¹ := by
    intro z
    rw [hφ]
    simp [MulAut.conjNormal_apply]
  have hfix : ∀ z : ↥H, (z : X) ∈ K → φ z = z := by
    intro z hz
    refine Subtype.ext ?_
    rw [hcoey z]
    have hcomm : (z : X) * y = y * (z : X) :=
      Subgroup.mem_centralizer_iff.mp hyK (z : X) hz
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have htriv : ∀ z : ↥H, ((φ z * z⁻¹ : ↥H) : X) ∈ K := by
    intro z
    have hmem := Work.Fitting.mem_sectionCentralizer_iff.mp hyHK
    have hc := Subgroup.mem_centralizer_iff.mp hmem ((QuotientGroup.mk' K) z)
      (Subgroup.mem_map_of_mem _ z.2)
    have hq : (QuotientGroup.mk' K) (y * (z : X) * y⁻¹ * (z : X)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [show (QuotientGroup.mk' K) y * (QuotientGroup.mk' K) z
          = (QuotientGroup.mk' K) z * (QuotientGroup.mk' K) y from hc.symm]
      group
    have h2 : y * (z : X) * y⁻¹ * (z : X)⁻¹ ∈ K := (QuotientGroup.eq_one_iff _).mp hq
    have hcoe : ((φ z * z⁻¹ : ↥H) : X) = y * (z : X) * y⁻¹ * (z : X)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoey z]
    rw [hcoe]
    exact h2
  have key : ∀ (m : ℕ) (z : ↥H), (φ ^ m) z = (φ z * z⁻¹) ^ m * z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      have hc : φ (φ z * z⁻¹) = φ z * z⁻¹ := hfix _ (htriv z)
      calc (φ ^ (m + 1)) z = φ ((φ ^ m) z) := by rw [pow_succ', MulAut.mul_apply]
        _ = φ ((φ z * z⁻¹) ^ m * z) := by rw [ih]
        _ = φ ((φ z * z⁻¹) ^ m) * φ z := by rw [map_mul]
        _ = (φ (φ z * z⁻¹)) ^ m * φ z := by rw [map_pow]
        _ = (φ z * z⁻¹) ^ m * φ z := by rw [hc]
        _ = (φ z * z⁻¹) ^ (m + 1) * z := by rw [pow_succ]; group
  ext z
  rw [key (Nat.card ↥K) z]
  have hc : ((φ z * z⁻¹ : ↥H) : X) ∈ K := htriv z
  let c : ↥K := ⟨((φ z * z⁻¹ : ↥H) : X), hc⟩
  have hcK : c ^ Nat.card ↥K = 1 := pow_card_eq_one'
  have h5 : ((c : X)) ^ Nat.card ↥K = 1 := by
    rw [← Subgroup.coe_pow, hcK]; rfl
  have h6 : ((c : X)) = ((φ z * z⁻¹ : ↥H) : X) := rfl
  have h3 : ((φ z * z⁻¹) ^ Nat.card ↥K : ↥H) = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, ← h6]
    exact h5
  rw [h3, one_mul]
  simp

lemma pow_card_mem_centralizer_of_mem_inf {X : Type*} [Group X] {p : ℕ} {K H : Subgroup X}
    [K.Normal] [H.Normal] (hKH : K ≤ H) (hHp : IsPGroup p ↥H) {y : X}
    (hyK : y ∈ Subgroup.centralizer (K : Set X))
    (hyHK : y ∈ Work.Fitting.sectionCentralizer K H) :
    y ^ Nat.card ↥K ∈ Subgroup.centralizer (H : Set X) := by
  have h := conjNormal_pow_card_eq_one hKH hHp hyK hyHK
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hiter : ∀ n : ℕ,
      (((MulAut.conjNormal y : MulAut ↥H) ^ n) ⟨w, hw⟩ : X) = y ^ n * w * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply]
      rw [show ((MulAut.conjNormal y (((MulAut.conjNormal y) ^ n) ⟨w, hw⟩)) : X)
          = y * ((((MulAut.conjNormal y) ^ n) ⟨w, hw⟩) : X) * y⁻¹ from by
        simp [MulAut.conjNormal_apply], ih, pow_succ]
      group
  have h3 : y ^ Nat.card ↥K * w * (y ^ Nat.card ↥K)⁻¹ = w := by
    have h2 : ((MulAut.conjNormal y : MulAut ↥H) ^ Nat.card ↥K) ⟨w, hw⟩ = ⟨w, hw⟩ := by
      rw [h]; rfl
    have h4 := congrArg (fun z : ↥H => (z : X)) h2
    rw [hiter (Nat.card ↥K)] at h4
    simpa using h4
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

/-! ## 8. The reduction step: descent of a failure of `p`-stability to `X/K` -/

lemma hasAbelianSylowTwo_quotient {G : Type*} [Group G] [Finite G] (h : HasAbelianSylowTwo G)
    (N : Subgroup G) [N.Normal] : HasAbelianSylowTwo (G ⧸ N) := by
  rw [hasAbelianSylowTwo_iff_commutative]
  intro Q
  exact allTwoSubgroups_commutative_quotient (allTwoSubgroups_commutative_of_hasAbelianSylowTwo h)
    N (Q : Subgroup (G ⧸ N)) Q.isPGroup'

/-- The failure of `p`-stability at a normal `p`-subgroup `H` descends to `X/K` when the
witness centralises `K ≤ H`. -/
theorem not_isPStable_quotient_of_bad_of_mem_centralizer {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {H K A : Subgroup X} [K.Normal] [H.Normal] (hKH : K ≤ H)
    (hHp : IsPGroup p ↥H) (hAp : IsPGroup p ↥A) (hcomm : ⁅⁅H, A⁆, A⁆ = ⊥)
    {x : X} (hxA : x ∈ A) (hxK : x ∈ Subgroup.centralizer (K : Set X))
    (hbad : x ∉ ((Work.HallHigman.pCore p (X ⧸ Subgroup.centralizer (H : Set X))).comap
        (QuotientGroup.mk' (Subgroup.centralizer (H : Set X))))) :
    ¬ Work.GlaubermanZJ.IsPStable p (X ⧸ K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup X := Subgroup.centralizer (H : Set X) with hC
  set D : Subgroup X := Work.Fitting.sectionCentralizer K H with hD
  haveI : D.Normal := by rw [hD]; exact Work.Fitting.sectionCentralizer_normal (H := K) (K := H)
  have hKD : K ≤ D := by
    intro k hk
    rw [hD, Work.Fitting.mem_sectionCentralizer_iff, Subgroup.mem_centralizer_iff]
    intro z hz
    have hk1 : (QuotientGroup.mk' K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [hk1]
    simp
  -- Step 1: the witness descends to `X/D`, `D = C_X(H/K)`
  have hxD : x ∉ ((Work.HallHigman.pCore p (X ⧸ D)).comap (QuotientGroup.mk' D)) := by
    intro hxM
    set N : Subgroup X := (Work.HallHigman.pCore p (X ⧸ D)).comap (QuotientGroup.mk' D)
      ⊓ Subgroup.centralizer (K : Set X) with hN
    haveI : N.Normal := inferInstance
    have hxN : x ∈ N := ⟨hxM, hxK⟩
    have hpcore : N.map (QuotientGroup.mk' C) ≤ Work.HallHigman.pCore p (X ⧸ C) := by
      refine Work.HallHigman.le_pCore (inferInstance : (N.map (QuotientGroup.mk' C)).Normal) ?_
      refine (Work.Fitting.isPiNat_prime_iff_isPGroup hp (N.map (QuotientGroup.mk' C))).mpr ?_
      rw [isPGroup_iff_pow_pow_eq_one]
      intro z
      obtain ⟨g, hg, hgz⟩ := Subgroup.mem_map.mp z.2
      have hgoal : z = (⟨(QuotientGroup.mk' C) g, Subgroup.mem_map_of_mem _ hg⟩ :
          ↥(N.map (QuotientGroup.mk' C))) := Subtype.ext hgz.symm
      rw [hgoal]
      have hgM : (QuotientGroup.mk' D) g ∈ Work.HallHigman.pCore p (X ⧸ D) := hg.1
      have hgK : g ∈ Subgroup.centralizer (K : Set X) := hg.2
      obtain ⟨Q, hQmem, hgQ⟩ := Work.Fitting.mem_piCore_iff.mp hgM
      obtain ⟨k, hk⟩ := (Work.Fitting.isPiNat_prime_iff hp).mp
        (Work.Fitting.mem_piCoreSet.mp hQmem).2
      have hQpQ : IsPGroup p ↥Q := IsPGroup.of_card hk
      obtain ⟨i, hi⟩ := isPGroup_iff_pow_pow_eq_one.mp hQpQ ⟨(QuotientGroup.mk' D) g, hgQ⟩
      have hgi : ((QuotientGroup.mk' D) g) ^ p ^ i = 1 := by simpa using hi
      rw [← map_pow] at hgi
      have hgiD : g ^ p ^ i ∈ D := (QuotientGroup.eq_one_iff _).mp hgi
      have hgiK : g ^ p ^ i ∈ Subgroup.centralizer (K : Set X) := Subgroup.pow_mem _ hgK _
      have hKp : IsPGroup p ↥K := hHp.to_le hKH
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hKp
      have h2 : (g ^ p ^ i) ^ Nat.card ↥K ∈ C := by
        rw [hC]
        exact pow_card_mem_centralizer_of_mem_inf hKH hHp hgiK (by rw [← hD]; exact hgiD)
      have hkey : ((QuotientGroup.mk' C) g) ^ p ^ (i + n) = 1 := by
        rw [show p ^ (i + n) = p ^ i * p ^ n from pow_add p i n, pow_mul, ← map_pow,
          ← map_pow, ← hn]
        exact (QuotientGroup.eq_one_iff _).mpr h2
      refine ⟨i + n, ?_⟩
      apply Subtype.ext
      show (((⟨(QuotientGroup.mk' C) g, Subgroup.mem_map_of_mem _ hg⟩ :
        ↥(N.map (QuotientGroup.mk' C))) : X ⧸ C)) ^ p ^ (i + n) = 1
      exact hkey
    have : (QuotientGroup.mk' C) x ∈ Work.HallHigman.pCore p (X ⧸ C) :=
      hpcore (Subgroup.mem_map_of_mem _ hxN)
    exact hbad (by rwa [Subgroup.mem_comap])
  -- Step 2: the failure in `X/K`
  have hCbar : Subgroup.centralizer ((H.map (QuotientGroup.mk' K)) : Set (X ⧸ K))
      = D.map (QuotientGroup.mk' K) := by
    ext z
    constructor
    · intro hz
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K z
      exact Subgroup.mem_map_of_mem _ (Work.Fitting.mem_sectionCentralizer_iff.mpr hz)
    · rintro ⟨g, hg, rfl⟩
      exact Work.Fitting.mem_sectionCentralizer_iff.mp hg
  have hKker : K ≤ (QuotientGroup.mk' D).ker := by
    rw [QuotientGroup.ker_mk']; exact hKD
  let ψ : X ⧸ K →* X ⧸ D := QuotientGroup.lift K (QuotientGroup.mk' D) hKker
  have hCbar_le : Subgroup.centralizer ((H.map (QuotientGroup.mk' K)) : Set (X ⧸ K)) ≤ ψ.ker := by
    intro z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K z
    rw [MonoidHom.mem_ker, show ψ (QuotientGroup.mk' K g) = (QuotientGroup.mk' D) g from
      QuotientGroup.lift_mk' _ _ _]
    exact (QuotientGroup.eq_one_iff g).mpr (Work.Fitting.mem_sectionCentralizer_iff.mpr hz)
  let φ : (X ⧸ K) ⧸ Subgroup.centralizer ((H.map (QuotientGroup.mk' K)) : Set (X ⧸ K)) →* X ⧸ D :=
    QuotientGroup.lift _ ψ hCbar_le
  have hφsurj : Function.Surjective φ := by
    intro w
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D w
    exact ⟨(QuotientGroup.mk' _) (QuotientGroup.mk' K g), by
      rw [show φ ((QuotientGroup.mk' _) (QuotientGroup.mk' K g)) = ψ (QuotientGroup.mk' K g) from
        QuotientGroup.lift_mk' _ _ _, show ψ (QuotientGroup.mk' K g) = (QuotientGroup.mk' D) g from
        QuotientGroup.lift_mk' _ _ _]⟩
  have hφx : φ ((QuotientGroup.mk' _) ((QuotientGroup.mk' K) x)) = (QuotientGroup.mk' D) x := by
    rw [show φ ((QuotientGroup.mk' _) ((QuotientGroup.mk' K) x)) = ψ (QuotientGroup.mk' K x) from
      QuotientGroup.lift_mk' _ _ _, show ψ (QuotientGroup.mk' K x) = (QuotientGroup.mk' D) x from
      QuotientGroup.lift_mk' _ _ _]
  have hbadbar : (QuotientGroup.mk' (Subgroup.centralizer
        ((H.map (QuotientGroup.mk' K)) : Set (X ⧸ K))))
      (QuotientGroup.mk' K x) ∉ Work.HallHigman.pCore p
        ((X ⧸ K) ⧸ Subgroup.centralizer ((H.map (QuotientGroup.mk' K)) : Set (X ⧸ K))) := by
    intro hcon
    obtain ⟨Q, hQmem, hxQ⟩ := Work.Fitting.mem_piCore_iff.mp hcon
    obtain ⟨e, he⟩ := (Work.Fitting.isPiNat_prime_iff hp).mp
      (Work.Fitting.mem_piCoreSet.mp hQmem).2
    haveI : IsPGroup p ↥Q := IsPGroup.of_card he
    have hφQp : IsPGroup p ↥(Q.map φ) := IsPGroup.of_card_dvd_pow (he ▸ Subgroup.card_map_dvd Q φ)
    have hφQcore : Q.map φ ≤ Work.HallHigman.pCore p (X ⧸ D) :=
      Work.HallHigman.le_pCore (Subgroup.Normal.map hQmem.1 φ hφsurj)
        ((Work.Fitting.isPiNat_prime_iff_isPGroup hp (Q.map φ)).mpr hφQp)
    have hx1 : (QuotientGroup.mk' D) x ∈ Q.map φ := by
      rw [← hφx]
      exact Subgroup.mem_map_of_mem φ hxQ
    exact hxD (by rw [Subgroup.mem_comap]; exact hφQcore hx1)
  -- conclude
  haveI : (H.map (QuotientGroup.mk' K)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective K)
  refine not_isPStable_of_isBad (G := X ⧸ K) (P := H.map (QuotientGroup.mk' K)) ?_
  refine ⟨hHp.map (QuotientGroup.mk' K), A.map (QuotientGroup.mk' K), QuotientGroup.mk' K x,
    hAp.map _, Subgroup.mem_map_of_mem _ hxA, ?_, hbadbar⟩
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hcomm, Subgroup.map_bot]

/-- An element whose coset modulo `C_Y(K)` lies in `O_p` lies in `C_Y(K)` itself, when `K` is a
minimal normal `p`-subgroup. -/
lemma mem_centralizer_of_mem_pCore_quotient {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {K : Subgroup Y} [K.Normal] (hK : Work.Fitting.IsMinimalNormal K)
    (hKp : IsPGroup p ↥K) {x : Y}
    (hcon : (QuotientGroup.mk' (Subgroup.centralizer (K : Set Y))) x ∈
      Work.HallHigman.pCore p (Y ⧸ Subgroup.centralizer (K : Set Y))) :
    x ∈ Subgroup.centralizer (K : Set Y) := by
  have hbot : Work.HallHigman.pCore p (Y ⧸ Subgroup.centralizer (K : Set Y)) = ⊥ :=
    pCore_quotient_centralizer_eq_bot_of_isMinimalNormal hp hK hKp
  rw [hbot] at hcon
  exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hcon)

/-- If `K ≤ H` and every element of `⁅H, A⁆` commutes with `A`, then `K` acts quadratically. -/
lemma comm_of_le_of_comm {Y : Type*} [Group Y] {H K A : Subgroup Y} [K.Normal] (hKH : K ≤ H)
    (hcomm : ⁅⁅H, A⁆, A⁆ = ⊥) : ⁅⁅K, A⁆, A⁆ = ⊥ := by
  rw [← le_bot_iff, Subgroup.commutator_le]
  intro u hu v hv
  have hu' : u ∈ ⁅H, A⁆ := Subgroup.commutator_mono_left hKH hu
  have h1 : ⁅u, v⁆ ∈ ⁅⁅H, A⁆, A⁆ := Subgroup.commutator_mem_commutator hu' hv
  rw [hcomm] at h1
  exact h1

/-! ## 9. The main theorem

`p`-solvable finite groups with abelian Sylow `2`-subgroups (or `p ≥ 5`) are `p`-stable; the
proof is the minimal-counterexample reduction of Glauberman §6, with the final step replaced by
`Work.PStable.pstable_representation`. -/

theorem isPStable_of_isPSolvable_of_abelianSylowTwo (p : ℕ) (hp : p.Prime) (hpne : p ≠ 2) :
    ∀ n : ℕ, ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y ≤ n →
      Work.HallHigman.IsPSolvable p Y → (5 ≤ p ∨ HasAbelianSylowTwo Y) →
      IsPStable p Y := by
  classical
  intro n
  induction n with
  | zero =>
    intro Y _ _ hcard _ _
    haveI : Nonempty Y := ⟨1⟩
    exact absurd hcard (Nat.not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro Y _ _ hcard hps h2
    by_cases hsmall : Nat.card Y ≤ n
    · exact ih Y hsmall hps h2
    · have hYcard : Nat.card Y = n + 1 := by omega
      by_contra hnot
      obtain ⟨P₀, hP₀n, hP₀p, A₀, x₀, hA₀p, hx₀A₀, hcomm₀, hbad₀⟩ :=
        exists_isBad_of_not_isPStable Y hnot
      -- choose a bad normal `p`-subgroup of minimal order
      haveI : Finite (Subgroup Y) :=
        Finite.of_injective (fun N : Subgroup Y => (N : Set Y))
          (fun a b h => SetLike.ext (Set.ext_iff.mp h))
      haveI : Fintype (Subgroup Y) := Fintype.ofFinite _
      have hne : ((Finset.univ.filter (fun N : Subgroup Y => ∃ hNn : N.Normal,
          @IsBad p Y _ N hNn)) : Finset (Subgroup Y)).Nonempty :=
        ⟨P₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨hP₀n, ⟨hP₀p, A₀, x₀, hA₀p, hx₀A₀, hcomm₀, hbad₀⟩⟩⟩⟩
      obtain ⟨H, hHmem, hHmin'⟩ := Finset.exists_min_image
        (Finset.univ.filter (fun N : Subgroup Y => ∃ hNn : N.Normal, @IsBad p Y _ N hNn))
        (fun N => Nat.card N) hne
      obtain ⟨hHn, hHbad⟩ := (Finset.mem_filter.mp hHmem).2
      have hHmin : ∀ (M : Subgroup Y) (hMn : M.Normal), @IsBad p Y _ M hMn →
          Nat.card H ≤ Nat.card M := by
        intro M hMn hMbad
        exact hHmin' M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hMn, hMbad⟩⟩)
      obtain ⟨hHp, A, x, hAp, hxA, hcomm, hbad⟩ := hHbad
      haveI : H.Normal := hHn
      -- `H ≠ ⊥`
      have hHne : H ≠ ⊥ := by
        intro hbot
        refine hbad ?_
        have h1 : (QuotientGroup.mk' (Subgroup.centralizer (H : Set Y))) x = 1 :=
          (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_centralizer_iff.mpr (fun z hz => by
            rw [hbot] at hz
            rw [Subgroup.mem_bot.mp hz]
            simp))
        rw [h1]
        exact Subgroup.one_mem _
      -- a minimal normal subgroup inside `H`
      obtain ⟨K, hKmin, hKH⟩ := Work.Fitting.exists_isMinimalNormal_le Y hHn hHne
      have hKn : K.Normal := hKmin.1
      haveI : K.Normal := hKn
      have hKne : K ≠ ⊥ := hKmin.2.1
      have hKp : IsPGroup p ↥K := hHp.to_le hKH
      -- a strictly smaller bad subgroup would contradict minimality of `H`
      have hlt : K ≠ H → Nat.card K < Nat.card H := by
        intro hne
        refine lt_of_le_of_ne (Subgroup.card_le_of_le hKH) ?_
        intro hc
        exact hne (Subgroup.eq_of_le_of_card_ge hKH (le_of_eq hc.symm))
      -- `K` acts quadratically as well
      have hcommK : ⁅⁅K, A⁆, A⁆ = ⊥ := comm_of_le_of_comm hKH hcomm
      by_cases hxK : x ∈ Subgroup.centralizer (K : Set Y)
      · -- `x` centralises `K`
        by_cases hKH' : K = H
        · -- `K = H`: then `x ∈ C_Y(H)`, contradicting the badness of `H`
          subst hKH'
          refine hbad ?_
          have h1 : (QuotientGroup.mk' (Subgroup.centralizer (K : Set Y))) x = 1 :=
            (QuotientGroup.eq_one_iff x).mpr hxK
          rw [h1]
          exact Subgroup.one_mem _
        · -- `K < H`: the failure descends to `Y/K`, contradicting the induction hypothesis
          have hbadbar := not_isPStable_quotient_of_bad_of_mem_centralizer hp hKH hHp hAp hcomm
            hxA hxK hbad
          have hcard' : Nat.card (Y ⧸ K) ≤ n := by
            have h2 : Nat.card Y = Nat.card (Y ⧸ K) * Nat.card ↥K :=
              Subgroup.card_eq_card_quotient_mul_card_subgroup K
            haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
            have h3 : 1 < Nat.card ↥K := (Subgroup.one_lt_card_iff_ne_bot (H := K)).mpr hKne
            haveI : Nonempty (Y ⧸ K) := ⟨1⟩
            have h4 : 0 < Nat.card (Y ⧸ K) := Nat.card_pos
            have h5 : Nat.card (Y ⧸ K) < Nat.card Y := by
              rw [h2]
              simpa using Nat.mul_lt_mul_of_pos_left h3 h4
            omega
          have hps' : Work.HallHigman.IsPSolvable p (Y ⧸ K) :=
            Work.HallHigman.isPSolvable_quotient_prime hp K hps
          have h2' : 5 ≤ p ∨ HasAbelianSylowTwo (Y ⧸ K) := by
            rcases h2 with h5 | hab
            · exact Or.inl h5
            · exact Or.inr (hasAbelianSylowTwo_quotient hab K)
          exact hbadbar (ih (Y ⧸ K) hcard' hps' h2')
      · -- `x ∉ C_Y(K)`
        by_cases hKH' : K = H
        · -- `K = H`: the representation-theoretic contradiction
          subst hKH'
          have hle : Subgroup.closure {x} ≤ A :=
            (Subgroup.closure_le A).mpr (by rintro y rfl; exact hxA)
          have hclp : IsPGroup p ↥(Subgroup.closure {x}) := hAp.to_le hle
          have hquad : ⁅⁅K, Subgroup.closure {x}⁆, Subgroup.closure {x}⁆ = ⊥ := by
            rw [← le_bot_iff, Subgroup.commutator_le]
            intro u hu v hv
            have hu' : u ∈ ⁅K, A⁆ := Subgroup.commutator_mono_right hle hu
            have h1 : ⁅u, v⁆ ∈ ⁅⁅K, A⁆, A⁆ := Subgroup.commutator_mem_commutator hu' (hle hv)
            rw [hcommK] at h1
            exact h1
          have hOp : Work.HallHigman.pCore p (Y ⧸ Subgroup.centralizer (K : Set Y)) = ⊥ :=
            pCore_quotient_centralizer_eq_bot_of_isMinimalNormal hp hKmin hKp
          have hpsQ : Work.HallHigman.IsPSolvable p (Y ⧸ Subgroup.centralizer (K : Set Y)) :=
            Work.HallHigman.isPSolvable_quotient_prime hp _ hps
          have h2Q : 5 ≤ p ∨ ∀ Q : Sylow 2 (Y ⧸ Subgroup.centralizer (K : Set Y)),
              IsMulCommutative ↥(Q : Subgroup (Y ⧸ Subgroup.centralizer (K : Set Y))) := by
            rcases h2 with h5 | hab
            · exact Or.inl h5
            · exact Or.inr (sylow_commutative_quotient
                (allTwoSubgroups_commutative_of_hasAbelianSylowTwo hab) _)
          exact false_of_isMinimalNormal_quadratic hp hpne hKmin hKp hpsQ h2Q hOp hclp hquad hbad
        · -- `K < H`: `K` is bad, contradicting the minimality of `H`
          have hbadK : x ∉ (Work.HallHigman.pCore p (Y ⧸ Subgroup.centralizer (K : Set Y))).comap
              (QuotientGroup.mk' (Subgroup.centralizer (K : Set Y))) :=
            fun hcon => hxK (mem_centralizer_of_mem_pCore_quotient hp hKmin hKp hcon)
          clear hcomm hKmin hbad
          have hKbad : IsBad p Y K := ⟨hKp, A, x, hAp, hxA, hcommK, hbadK⟩
          exact absurd (hHmin K hKn hKbad) (not_le.mpr (hlt hKH'))

-- Glauberman 1968, Lemma 6.3 (direction (a) => (b)), restricted to `O_{p'}(X) = 1`:
-- a finite p-solvable group with abelian Sylow 2-subgroups (or `5 ≤ p`) is `p`-stable.
-- Route: Glauberman §6 (the elementary part of the proof of Lemma 6.3) reduces a failure of
-- `p`-stability to a subquotient `G/C` acting faithfully and irreducibly on an elementary
-- abelian `p`-group `H`, with a `p`-element `x ≠ 1` acting quadratically on `H` and `O_p(G/C)=1`.
-- Glauberman then quotes Dickson (Lemma 6.2); here that step is replaced by the delivered
-- `Work.PStable.pstable_representation` (quadratic Hall–Higman with abelian Sylow 2), which
-- directly contradicts the existence of the quadratic `p`-subgroup `⟨x⟩`.
theorem pstable_of_abelianSylowTwo {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hpne : p ≠ 2) (hps : Work.HallHigman.IsPSolvable p X)
    (h2 : 5 ≤ p ∨ Work.GlaubermanZJ.HasAbelianSylowTwo X)
    (hcore : Work.Fitting.pPrimeCore p X = ⊥) :
    Work.GlaubermanZJ.IsPStable p X :=
  isPStable_of_isPSolvable_of_abelianSylowTwo p hp hpne (Nat.card X) X le_rfl hps h2



end Work.GlaubermanZJ.PStableAux
