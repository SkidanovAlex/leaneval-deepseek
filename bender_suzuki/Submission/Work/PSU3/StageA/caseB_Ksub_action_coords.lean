import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.PSU3.StageA.caseC_W_semireg
import Submission.Work.PSU3.StageA.cyclic_fpf_action_field
import Submission.Work.Higman.BS.mem_center_of_mul_mem_center_of_coprime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# Case b): the coordinates of the `K`-action on `Q`

In case b) of the Proposition of Peterfalvi II, Ch. VI §1 (`Q` non-abelian of order `q²`,
`q = |Q₀| = |Q0sub H|`, `orderOf (s * t) = 5`, `W H t = ⊥`, `K = Ksub H t = Kset H t` cyclic),
the quotient `Q/Q₀` carries a field structure `F` of order `q`, `K` is isomorphic to `Fˣ`, and
`K` acts on `Q/Q₀` by multiplication.

The route followed here is the Singer-cycle description of the Suzuki 2-group `Q`:

* `Q` is a Suzuki 2-group, so `HigmanProp` applies: `Z(↥Q) = Ω₁(↥Q) = (Q0sub H).subgroupOf Q`
  and every square of `Q` is central; hence `V = ↥Q ⧸ Z(↥Q)` is an elementary abelian group of
  order `q`;
* `K` acts on `V` by conjugation and this action is fixed-point-free on `V ∖ {1}`
  (`Work.ThmF.ChV12.prop1a`: a non-trivial element of `Kset` centralises no non-trivial element
  of `Q`, and Higman's lemma `mem_center_of_mul_mem_center_of_coprime` upgrades this to `V`);
* `Work.PSU3.StageA.cyclic_fpf_action_field` then produces the field `F` of order `q`, the
  additive bijection `V ≃ F` and the character `ρ : K →* Fˣ` through which `K` acts on `V` by
  multiplication.

Composing with the projection `Q → Q/Z(Q) = Q/Q₀` gives the coordinates of the statement.
-/

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

section Helpers

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## §1. Elementary cardinalities in case b) -/

/-- `|K| = |Q₀| - 1` in case b) (`K = Kset` and `|Kset| = |Inv H|`). -/
private lemma caseB_card_Ksub (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
  have h1 : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Ksub H t : Set G).ncard :=
    Nat.card_coe_set_eq _
  have h2 : (Work.ThmF.Kset H t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hS.split.stronglyEmbedded hS.split.invol hS.split.not_mem
  rw [h1, hKsub, h2, card_Q0sub_eq hS hC4]
  omega

private lemma caseB_abelianSubgroup_of_card_one {Q : Subgroup G}
    (h : Nat.card ↥Q = 1) : Submission.Blueprint.IsAbelianSubgroup Q := by
  haveI : Subsingleton ↥Q := (Nat.card_eq_one_iff_unique.mp h).1
  intro x hx y hy
  have hxy : x = y := Subtype.ext_iff.mp (Subsingleton.elim (⟨x, hx⟩ : ↥Q) ⟨y, hy⟩)
  rw [hxy]

private lemma caseB_abelianSubgroup_of_card_four {Q : Subgroup G}
    (h : Nat.card ↥Q = 2 ^ 2) : Submission.Blueprint.IsAbelianSubgroup Q := by
  have hcomm : ∀ a b : ↥Q, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := ↥Q) (p := 2) h).is_comm.comm
  intro x hx y hy
  have h1 := congrArg (fun z : ↥Q => (z : G)) (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  simpa using h1

/-- In case b) one has `4 ≤ |Q₀|`: a `2`-group of order `≤ 4` is abelian. -/
private lemma caseB_four_le_card_Q0sub (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2) :
    4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
  obtain ⟨n, hn⟩ := exists_card_Q0sub_eq_two_pow hS hC4
  by_contra h4
  push_neg at h4
  have hn1 : n ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at hn
    have hcard1 : Nat.card ↥Q = 1 := by rw [hcard, hn]; norm_num
    exact hnab (caseB_abelianSubgroup_of_card_one hcard1)
  · have h1 : n = 1 := by omega
    rw [h1] at hn
    have hcard4 : Nat.card ↥Q = 2 ^ 2 := by rw [hcard, hn]; norm_num
    exact hnab (caseB_abelianSubgroup_of_card_four hcard4)

/-! ## §2. The Suzuki structure of `Q` in case b) -/

/-- The elements of `Q` of order dividing two are exactly the elements of `Q₀`. -/
private lemma caseB_mem_Q0sub_iff_sq_eq_one (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 := by
  intro x
  constructor
  · intro hx
    exact Subtype.ext ((Q0sub_structure hS hC4).1 (x : G) hx)
  · intro hx
    have hx1 : (x : G) * (x : G) = 1 := congrArg Subtype.val hx
    rcases eq_or_ne (x : G) 1 with h1 | h1
    · rw [h1]; exact (Work.ThmF.Q0sub H).one_mem
    · have hdvd : orderOf (x : G) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hx1
      have hxord : orderOf (x : G) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) h1
        · exact h
      exact Work.ThmF.Q0_le_Q0sub H
        (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hS.split.le x.2, hxord⟩))

/-- `Q` has two distinct involutions in case b) (`4 ≤ |Q₀|` and `Q₀ = {1} ∪ Inv(Q)`). -/
private lemma caseB_manyInvol (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2) :
    ∃ x y : ↥Q, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y := by
  have h4 : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) :=
    caseB_four_le_card_Q0sub hS hC4 hnab hcard
  have hsetcard : ((Work.ThmF.Q0sub H : Set G)).ncard = Nat.card ↥(Work.ThmF.Q0sub H) :=
    (Nat.card_coe_set_eq (Work.ThmF.Q0sub H : Set G)).symm
  have hmem1 : (1 : G) ∈ (Work.ThmF.Q0sub H : Set G) := (Work.ThmF.Q0sub H).one_mem
  have hlt : 1 < ((Work.ThmF.Q0sub H : Set G) \ {1}).ncard := by
    rw [Set.ncard_diff_singleton_of_mem hmem1, hsetcard]
    omega
  obtain ⟨z1, hz1, _hz1ne⟩ := Set.exists_ne_of_one_lt_ncard hlt (1 : G)
  obtain ⟨z2, hz2, hz2ne⟩ := Set.exists_ne_of_one_lt_ncard hlt z1
  have hz1Q0 : z1 ∈ Work.ThmF.Q0sub H := (Set.mem_sdiff z1).mp hz1 |>.1
  have hz2Q0 : z2 ∈ Work.ThmF.Q0sub H := (Set.mem_sdiff z2).mp hz2 |>.1
  have hz11 : z1 ≠ 1 := (Set.mem_sdiff z1).mp hz1 |>.2
  have hz21 : z2 ≠ 1 := (Set.mem_sdiff z2).mp hz2 |>.2
  have hsq1 : z1 * z1 = 1 := (Q0sub_structure hS hC4).1 z1 hz1Q0
  have hsq2 : z2 * z2 = 1 := (Q0sub_structure hS hC4).1 z2 hz2Q0
  refine ⟨⟨z1, Q0sub_le_Q hS.split hz1Q0⟩, ⟨z2, Q0sub_le_Q hS.split hz2Q0⟩, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq1)
      (fun h => hz11 (Subtype.ext_iff.mp h))
  · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq2)
      (fun h => hz21 (Subtype.ext_iff.mp h))
  · intro h
    exact hz2ne (Subtype.ext_iff.mp h).symm

/-- An element of `Q` different from `1`. -/
private lemma caseB_exists_ne_one_Q (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2) :
    ∃ z : ↥Q, z ≠ 1 := by
  obtain ⟨x1, x2, -, -, hne⟩ := caseB_manyInvol hS hC4 hnab hcard
  rcases eq_or_ne x1 1 with h | h
  · exact ⟨x2, fun h2 => hne (by rw [h, h2])⟩
  · exact ⟨x1, h⟩

/-- A generator of the cyclic group `Ksub H t`. -/
private lemma caseB_exists_generator (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t)) :
    ∃ k : G, k ∈ Work.ThmF.Ksub H t ∧ Subgroup.zpowers k = Work.ThmF.Ksub H t := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Work.ThmF.Ksub H t))
  refine ⟨(g : G), g.2, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn]
    exact (Work.ThmF.Ksub H t).zpow_mem g.2 n
  · intro hx
    have h1 : (⟨x, hx⟩ : ↥(Work.ThmF.Ksub H t)) ∈ Subgroup.zpowers g := hg ⟨x, hx⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩

/-- Conjugation by a generator of `K` is transitive on the involutions of `Q`. -/
private lemma caseB_conj_trans_invol (hS : Work.PSU3.PSU3Hyp H Q t)
    {k : G} (hkK : k ∈ Work.ThmF.Ksub H t)
    (hkgen : Subgroup.zpowers k = Work.ThmF.Ksub H t) :
    ∀ x y : ↥Q, orderOf x = 2 → orderOf y = 2 →
      ∃ n : ℕ, ((cwConj Q k (Ksub_le_normalizer hS hkK)) ^ n) x = y := by
  intro x y hx hy
  have hxH : (x : G) ∈ involutions (H : Set G) :=
    ⟨hS.split.le x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hyH : (y : G) ∈ involutions (H : Set G) :=
    ⟨hS.split.le y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  obtain ⟨j, hjk, hjy⟩ := Kset_transitive_involutions hS.split.stronglyEmbedded
    hS.split.invol hS.split.not_mem (x : G) hxH (y : G) hyH
  have hjK : j ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hjk
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (by rw [hkgen]; exact hjK)
  obtain ⟨r, hr⟩ := Work.ThmF.ChV12.exists_nat_pow_eq_of_zpow_eq hn
  refine ⟨r, ?_⟩
  apply Subtype.ext
  rw [cwConj_pow_apply, hr, hjy]

/-- **`Q` is a Suzuki 2-group in case b).** -/
private noncomputable def caseB_isSuzuki2Grp (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t)) : Work.Higman.IsSuzuki2Grp ↥Q := by
  classical
  set k : G := (caseB_exists_generator hKcyc).choose with hk
  have hkK : k ∈ Work.ThmF.Ksub H t := (caseB_exists_generator hKcyc).choose_spec.1
  have hkgen : Subgroup.zpowers k = Work.ThmF.Ksub H t :=
    (caseB_exists_generator hKcyc).choose_spec.2
  have hnc : ∃ x y : ↥Q, x * y ≠ y * x := by
    by_contra h
    push_neg at h
    exact hnab (fun x hx y hy => congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  have htr : ∀ x y : ↥Q, orderOf x = 2 → orderOf y = 2 →
      ∃ n : ℕ, ((cwConj Q k (Ksub_le_normalizer hS hkK)) ^ n) x = y :=
    fun x y hx hy => caseB_conj_trans_invol hS hkK hkgen x y hx hy
  exact
    { isPGroup := hS.two
      noncomm := hnc
      manyInvol := caseB_manyInvol hS hC4 hnab hcard
      xi := cwConj Q k (Ksub_le_normalizer hS hkK)
      trans := htr }

/-! ## §3. `Z(Q) = Q₀` and the quotient `V = Q/Z(Q)` -/

/-- `Z(↥Q) = Q₀` (Higman: the centre of a Suzuki 2-group is `Ω₁`). -/
private lemma caseB_center_eq_Q0sub (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t)) :
    Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q := by
  have hSuz : Work.Higman.IsSuzuki2Grp ↥Q :=
    caseB_isSuzuki2Grp hS hC4 hnab hcard hKsub hKcyc
  have htwo : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  have hZsq : ∀ z : ↥Q, z ∈ Subgroup.center ↥Q → z * z = 1 := by
    intro z hz
    have h1 : z ^ 2 = 1 := (hHig ↥Q htwo).1 z |>.mp hz
    rwa [pow_two] at h1
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact (caseB_mem_Q0sub_iff_sq_eq_one hS hC4 x).mpr (hZsq x hx)
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := (Work.ThmF.mem_centerOf (Q := Q)).mp (Q0sub_le_centerOf hS hC4 hx)
    exact Subtype.ext (h1.2 (y : G) y.2).symm

/-- `|Z(↥Q)| = |Q₀|`. -/
private lemma caseB_card_center (hS : Work.PSU3.PSU3Hyp H Q t)
    (hcenter : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q) :
    Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
  rw [hcenter]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q0sub_le_Q hS.split)).toEquiv

/-- `|Q/Z(Q)| = |Q₀|`. -/
private lemma caseB_card_quot_center (hS : Work.PSU3.PSU3Hyp H Q t)
    (hcenter : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2) :
    Nat.card (↥Q ⧸ Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
  have h1 : Nat.card (↥Q ⧸ Subgroup.center ↥Q) * Nat.card ↥(Subgroup.center ↥Q)
      = Nat.card ↥Q := by
    rw [← Subgroup.card_mul_index (H := Subgroup.center ↥Q), Subgroup.index_eq_card]
    exact mul_comm _ _
  rw [caseB_card_center hS hcenter, hcard, pow_two] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

/-- `V = Q/Z(Q)` has exponent two (Higman: every square of a Suzuki 2-group is central). -/
private lemma caseB_quot_sq_one (hHig : Submission.Blueprint.HigmanProp)
    (hSuz : Work.Higman.IsSuzuki2Grp ↥Q) :
    ∀ v : ↥Q ⧸ Subgroup.center ↥Q, v * v = 1 := by
  have htwo : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  have hsq : ∀ x : ↥Q, x ^ 2 ∈ Subgroup.center ↥Q := (hHig ↥Q htwo).2.1
  intro v
  refine QuotientGroup.induction_on v (fun x => ?_)
  rw [← QuotientGroup.mk_mul]
  exact (QuotientGroup.eq_one_iff (x * x)).mpr (by simpa [pow_two] using hsq x)

/-! ## §4. The conjugation action of `K` on `Q` and on `V = Q/Z(Q)` -/

/-- Conjugation by `k ∈ Ksub H t` as an automorphism of `Q`. -/
private noncomputable def caseB_actQ (hS : Work.PSU3.PSU3Hyp H Q t) :
    ↥(Work.ThmF.Ksub H t) →* MulAut ↥Q where
  toFun k := cwConj Q (k : G) (Ksub_le_normalizer hS k.2)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [cwConj_apply, Subgroup.coe_one, one_mul, inv_one, mul_one, MulAut.one_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [cwConj_apply, Subgroup.coe_mul, MulAut.mul_apply]
    group

@[simp] private lemma caseB_actQ_apply (hS : Work.PSU3.PSU3Hyp H Q t)
    (k : ↥(Work.ThmF.Ksub H t)) (x : ↥Q) :
    caseB_actQ hS k x = cwConj Q (k : G) (Ksub_le_normalizer hS k.2) x := rfl

/-- The centre of `Q` is invariant under the conjugation action of `K`. -/
private lemma caseB_center_map_eq (hS : Work.PSU3.PSU3Hyp H Q t)
    (k : ↥(Work.ThmF.Ksub H t)) :
    (Subgroup.center ↥Q).map (↑(caseB_actQ hS k)) = Subgroup.center ↥Q :=
  Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center ↥Q).Characteristic)
    (caseB_actQ hS k)

/-- The conjugation action of `K` on `V = Q/Z(Q)`. -/
private noncomputable def caseB_actV (hS : Work.PSU3.PSU3Hyp H Q t) :
    ↥(Work.ThmF.Ksub H t) →* MulAut (↥Q ⧸ Subgroup.center ↥Q) where
  toFun k := QuotientGroup.congr (Subgroup.center ↥Q) (Subgroup.center ↥Q) (caseB_actQ hS k)
    (caseB_center_map_eq hS k)
  map_one' := by
    apply MulEquiv.ext
    intro v
    refine QuotientGroup.induction_on v (fun x => ?_)
    show (((caseB_actQ hS (1 : ↥(Work.ThmF.Ksub H t))) x : ↥Q) : ↥Q ⧸ Subgroup.center ↥Q)
      = (x : ↥Q ⧸ Subgroup.center ↥Q)
    rw [map_one, MulAut.one_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro v
    refine QuotientGroup.induction_on v (fun x => ?_)
    show (((caseB_actQ hS (a * b)) x : ↥Q) : ↥Q ⧸ Subgroup.center ↥Q)
      = (((caseB_actQ hS a) ((caseB_actQ hS b) x) : ↥Q) : ↥Q ⧸ Subgroup.center ↥Q)
    rw [map_mul, MulAut.mul_apply]

private lemma caseB_actV_mk (hS : Work.PSU3.PSU3Hyp H Q t)
    (k : ↥(Work.ThmF.Ksub H t)) (x : ↥Q) :
    caseB_actV hS k (x : ↥Q ⧸ Subgroup.center ↥Q)
      = ((caseB_actQ hS k x : ↥Q) : ↥Q ⧸ Subgroup.center ↥Q) :=
  QuotientGroup.congr_mk (Subgroup.center ↥Q) (Subgroup.center ↥Q) (caseB_actQ hS k)
    (caseB_center_map_eq hS k) x

/-- **The action of `K` on `V = Q/Z(Q)` is fixed-point-free.**

`Work.ThmF.ChV12.prop1a` gives `C_Q(k) = 1` for `1 ≠ k ∈ Kset H t`; Higman's
`mem_center_of_mul_mem_center_of_coprime` upgrades this to the quotient `V = Q/Z(Q)`. -/
private lemma caseB_actV_fpf (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t)) :
    ∀ k : ↥(Work.ThmF.Ksub H t), k ≠ 1 →
      ∀ v : ↥Q ⧸ Subgroup.center ↥Q, caseB_actV hS k v = v → v = 1 := by
  have hSuz : Work.Higman.IsSuzuki2Grp ↥Q :=
    caseB_isSuzuki2Grp hS hC4 hnab hcard hKsub hKcyc
  have hcenter : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    caseB_center_eq_Q0sub hS hC4 hHig hnab hcard hKsub hKcyc
  have hcenter_card : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) :=
    caseB_card_center hS hcenter
  -- the coprime input `(q - 1).Coprime q`, `q = 2 ^ n`
  obtain ⟨n, hn⟩ := exists_card_Q0sub_eq_two_pow hS hC4
  have h4 : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := caseB_four_le_card_Q0sub hS hC4 hnab hcard
  have hn1 : 1 ≤ n := by
    by_contra h
    push_neg at h
    have h0 : n = 0 := by omega
    rw [hn] at h4
    rw [h0] at h4
    norm_num at h4
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn1
    rw [hm, pow_add, pow_one]
    refine ⟨2 ^ m - 1, ?_⟩
    have hle : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  have hcopq : (2 ^ n - 1).Coprime (2 ^ n) := (Nat.coprime_two_right.mpr hodd).pow_right n
  have hKsub_card : Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 :=
    caseB_card_Ksub hS hC4 hKsub
  intro k hk1 v hv
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  -- `ξ = conj_k` is a non-trivial automorphism of `Q`
  have hξ_ne : cwConj Q (k : G) (Ksub_le_normalizer hS k.2) ≠ 1 := by
    intro hcon
    apply hk1
    apply Subtype.ext
    by_contra hkne
    obtain ⟨z, hzne⟩ := caseB_exists_ne_one_Q hS hC4 hnab hcard
    have hkKset : (k : G) ∈ Work.ThmF.Kset H t := by rw [← hKsub]; exact k.2
    have h1 : (cwConj Q (k : G) (Ksub_le_normalizer hS k.2)) z = z := by rw [hcon]; rfl
    have h2 := congrArg (fun u : ↥Q => (u : G)) h1
    rw [cwConj_apply] at h2
    have hcomm : z * (k : G) = (k : G) * z := by
      have h3 : (k : G) * z * (k : G)⁻¹ = z := h2
      calc z * (k : G) = ((k : G) * z * (k : G)⁻¹) * (k : G) := by rw [h3]
        _ = (k : G) * z := by group
    exact hzne (Subtype.ext (Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split (k : G)
      hkKset hkne z z.2 hcomm))
  -- every non-trivial power of `ξ` is fixed-point-free on `Q`
  have hfpf : ∀ j : ℕ, (cwConj Q (k : G) (Ksub_le_normalizer hS k.2)) ^ j ≠ 1 →
      ∀ y : ↥Q, ((cwConj Q (k : G) (Ksub_le_normalizer hS k.2)) ^ j) y = y → y = 1 := by
    intro j hj y hy
    have hkjKset : (k : G) ^ j ∈ Work.ThmF.Kset H t := by
      rw [← hKsub]; exact (Work.ThmF.Ksub H t).pow_mem k.2 j
    have hkjne : (k : G) ^ j ≠ 1 := by
      intro h0
      apply hj
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      rw [cwConj_pow_apply, h0]
      simp
    have hcomm : (y : G) * (k : G) ^ j = (k : G) ^ j * (y : G) := by
      have h1 : (y : G) = (k : G) ^ j * (y : G) * ((k : G) ^ j)⁻¹ := by
        have h2 := congrArg (fun u : ↥Q => (u : G)) hy
        rw [cwConj_pow_apply] at h2
        exact h2.symm
      have h3 : (y : G) * (k : G) ^ j
          = ((k : G) ^ j * (y : G) * ((k : G) ^ j)⁻¹) * (k : G) ^ j := by
        conv_lhs => rw [h1]
      rw [h3]
      group
    exact Subtype.ext (Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split ((k : G) ^ j)
      hkjKset hkjne (y : G) y.2 hcomm)
  -- the coprimality hypothesis of Higman's lemma
  have hdvd : orderOf (cwConj Q (k : G) (Ksub_le_normalizer hS k.2))
      ∣ Nat.card ↥(Work.ThmF.Ksub H t) := by
    refine dvd_trans ?_ (orderOf_dvd_natCard k)
    rw [orderOf_dvd_iff_pow_eq_one]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have hkpow : (k : G) ^ orderOf k = 1 := by
      rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [cwConj_pow_apply, hkpow]
    simp
  have hcop : (orderOf (cwConj Q (k : G) (Ksub_le_normalizer hS k.2))).Coprime
      (Nat.card ↥(Subgroup.center ↥Q)) := by
    rw [hcenter_card, hn]
    refine hcopq.coprime_dvd_left ?_
    rw [← hn, ← hKsub_card]
    exact hdvd
  -- the coset condition
  have hx : x⁻¹ * (cwConj Q (k : G) (Ksub_le_normalizer hS k.2)) x
      ∈ Subgroup.center ↥Q := by
    have hv' : caseB_actV hS k (x : ↥Q ⧸ Subgroup.center ↥Q)
        = (x : ↥Q ⧸ Subgroup.center ↥Q) := hv
    rw [caseB_actV_mk hS k x, caseB_actQ_apply hS k x] at hv'
    have h2 : ((cwConj Q (k : G) (Ksub_le_normalizer hS k.2)) x)⁻¹ * x
        ∈ Subgroup.center ↥Q := QuotientGroup.eq.mp hv'
    have h3 : x⁻¹ * (cwConj Q (k : G) (Ksub_le_normalizer hS k.2)) x
        = (((cwConj Q (k : G) (Ksub_le_normalizer hS k.2)) x)⁻¹ * x)⁻¹ := by group
    rw [h3]
    exact (Subgroup.center ↥Q).inv_mem h2
  have hxZ : x ∈ Subgroup.center ↥Q :=
    Work.Higman.BS.mem_center_of_mul_mem_center_of_coprime hSuz hcop hfpf
      (k := 1) (by simpa using hξ_ne) (by simpa using hx)
  exact (QuotientGroup.eq_one_iff x).mpr hxZ

end Helpers

theorem caseB_Ksub_action_coords {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5) (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥Q → F) (κ : ↥(Work.ThmF.Ksub H t) ≃* Fˣ),
      Nat.card F = Nat.card (Work.ThmF.Q0sub H) ∧ Function.Surjective α ∧
      (∀ x y : ↥Q, α (x * y) = α x + α y) ∧
      (∀ x : ↥Q, α x = 0 ↔ (x : G) ∈ Work.ThmF.Q0sub H) ∧
      (∀ (k : ↥(Work.ThmF.Ksub H t)) (x y : ↥Q), (y : G) = (k : G)⁻¹ * (x : G) * (k : G) →
        α y = (κ k : F) * α x) := by
  classical
  haveI : Fintype (↥Q ⧸ Subgroup.center ↥Q) := Fintype.ofFinite _
  haveI : Fintype ↥(Work.ThmF.Ksub H t) := Fintype.ofFinite _
  have hSuz : Work.Higman.IsSuzuki2Grp ↥Q := caseB_isSuzuki2Grp hS hC4 hnab hcard hKsub hKcyc
  have hcenter : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    caseB_center_eq_Q0sub hS hC4 hHig hnab hcard hKsub hKcyc
  have hsqone : ∀ v : ↥Q ⧸ Subgroup.center ↥Q, v * v = 1 := caseB_quot_sq_one hHig hSuz
  have hcardV : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) :=
    caseB_card_quot_center hS hcenter hcard
  have hcardK : Nat.card ↥(Work.ThmF.Ksub H t)
      = Nat.card (↥Q ⧸ Subgroup.center ↥Q) - 1 := by
    rw [hcardV, caseB_card_Ksub hS hC4 hKsub]
  have hfpf : ∀ k : ↥(Work.ThmF.Ksub H t), k ≠ 1 →
      ∀ v : ↥Q ⧸ Subgroup.center ↥Q, caseB_actV hS k v = v → v = 1 :=
    caseB_actV_fpf hS hC4 hHig hnab hcard hKsub hKcyc
  obtain ⟨k₀, hk₀⟩ := IsCyclic.exists_generator (α := ↥(Work.ThmF.Ksub H t))
  have hgen : Subgroup.zpowers k₀ = ⊤ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hk₀ x)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, hn⟩
  obtain ⟨F, hF, hFint, φ, ρ, hcardF, hadd, heq, hρinj⟩ :=
    cyclic_fpf_action_field (V := ↥Q ⧸ Subgroup.center ↥Q) (K := ↥(Work.ThmF.Ksub H t))
      hsqone (caseB_actV hS) k₀ hgen hcardK hfpf
  -- the character `κ = ρ⁻¹` of `K`
  let κhom : ↥(Work.ThmF.Ksub H t) →* Fˣ :=
    MonoidHom.mk' (fun k => (ρ k)⁻¹) (fun a b => by rw [map_mul, mul_inv_rev, mul_comm])
  have hκinj : Function.Injective κhom := by
    intro a b hab
    have h : ρ a = ρ b := by
      have h1 := congrArg (fun u : Fˣ => u⁻¹) hab
      simpa [κhom] using h1
    exact hρinj h
  have hcardUnits : Nat.card Fˣ = Nat.card ↥(Work.ThmF.Ksub H t) := by
    rw [Nat.card_units, hcardF, hcardV, hcardK, hcardV]
  have hκsurj : Function.Surjective κhom := by
    have h1 : (Set.range κhom).ncard = (Set.univ : Set Fˣ).ncard := by
      rw [Set.ncard_range_of_injective hκinj, ← hcardUnits, Set.ncard_univ]
    have h2 : Set.range κhom = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (le_of_eq h1.symm)
    intro y
    have hy : y ∈ Set.range κhom := by rw [h2]; trivial
    exact hy
  let κ : ↥(Work.ThmF.Ksub H t) ≃* Fˣ := MulEquiv.ofBijective κhom ⟨hκinj, hκsurj⟩
  let α : ↥Q → F := fun x => φ (x : ↥Q ⧸ Subgroup.center ↥Q)
  have hφone : φ (1 : ↥Q ⧸ Subgroup.center ↥Q) = 0 := by
    have h1 : φ 1 = φ 1 + φ 1 := by
      have h := hadd 1 1
      rwa [mul_one] at h
    have h2 : φ 1 + 0 = φ 1 + φ 1 := by rw [add_zero]; exact h1
    exact (add_left_cancel h2).symm
  refine ⟨F, hF, hFint, α, κ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcardF, hcardV]
  · intro y
    obtain ⟨v, hv⟩ := φ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    exact ⟨x, hv⟩
  · intro x y
    show φ ((x * y : ↥Q) : ↥Q ⧸ Subgroup.center ↥Q)
      = φ (x : ↥Q ⧸ Subgroup.center ↥Q) + φ (y : ↥Q ⧸ Subgroup.center ↥Q)
    rw [QuotientGroup.mk_mul]
    exact hadd _ _
  · intro x
    show φ (x : ↥Q ⧸ Subgroup.center ↥Q) = 0 ↔ (x : G) ∈ Work.ThmF.Q0sub H
    constructor
    · intro hx
      have hx1 : (x : ↥Q ⧸ Subgroup.center ↥Q) = 1 := by
        have h2 : φ (x : ↥Q ⧸ Subgroup.center ↥Q) = φ (1 : ↥Q ⧸ Subgroup.center ↥Q) := by
          rw [hx, hφone]
        exact φ.injective h2
      have h3 : x ∈ (Work.ThmF.Q0sub H).subgroupOf Q := by
        rw [← hcenter]
        exact (QuotientGroup.eq_one_iff x).mp hx1
      exact Subgroup.mem_subgroupOf.mp h3
    · intro hx
      have h4 : x ∈ Subgroup.center ↥Q := by
        rw [hcenter]
        exact Subgroup.mem_subgroupOf.mpr hx
      have h5 : (x : ↥Q ⧸ Subgroup.center ↥Q) = 1 := (QuotientGroup.eq_one_iff x).mpr h4
      rw [h5, hφone]
  · intro k x y hy
    have h1 : (y : ↥Q ⧸ Subgroup.center ↥Q)
        = caseB_actV hS k⁻¹ (x : ↥Q ⧸ Subgroup.center ↥Q) := by
      rw [caseB_actV_mk hS k⁻¹ x, caseB_actQ_apply hS k⁻¹ x]
      refine congrArg (fun z : ↥Q => (z : ↥Q ⧸ Subgroup.center ↥Q)) ?_
      apply Subtype.ext
      rw [cwConj_apply, Subgroup.coe_inv, inv_inv]
      exact hy
    calc α y = φ (y : ↥Q ⧸ Subgroup.center ↥Q) := rfl
      _ = φ (caseB_actV hS k⁻¹ (x : ↥Q ⧸ Subgroup.center ↥Q)) := by rw [h1]
      _ = (ρ (k⁻¹) : F) * φ (x : ↥Q ⧸ Subgroup.center ↥Q) :=
            heq k⁻¹ (x : ↥Q ⧸ Subgroup.center ↥Q)
      _ = (κ k : F) * α x := by
        have h2 : (κhom k : Fˣ) = (ρ k)⁻¹ := rfl
        have h3 : (ρ (k⁻¹) : Fˣ) = (ρ k)⁻¹ := by rw [map_inv]
        have h4 : (ρ (k⁻¹) : F) = (κ k : F) := by
          rw [show (κ k : Fˣ) = κhom k from rfl, h2]
          exact congrArg (fun u : Fˣ => (u : F)) h3
        rw [h4]

end Work.PSU3.StageA
