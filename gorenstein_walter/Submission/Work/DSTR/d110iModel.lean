import Mathlib
import Submission.Work.DSTR.D110iDefs
import Submission.Work.DSTR.Defs
import Submission.Work.L2F.Defs
import Submission.Work.ASM.oddCore_odd
import Submission.Work.DSTR.FourGroupCentInvariant
import Submission.Work.DSTR.A7CentInvariantHa7
import Submission.Work.DSTR.L2CentInvariant

namespace Work.DSTR

open Subgroup

open scoped MatrixGroups

/-!
# `DS9a`: Bender 1.10(i) in the reduced shapes

This file proves `Work.GW2.D110iModelProp` (Bender 1981, 1.10(i), for the shapes of `DShape`).

`CentInvariant Q` is the conclusion of 1.10(i) for a single group `Q`
(`Submission/Work/DSTR/D110iDefs.lean`).  The argument has three ingredients.

* `centInvariant_of_isPGroup_two`: if `Q` is a `2`-group then every odd `p`-subgroup is trivial.
* `le_centralizer_of_inf_le` and `centInvariant_of_normal`: the elementary reduction to a normal
  subgroup.  If `M ⊴ Q` contains every involution of `Q`, `P ≤ Q` is odd and `C_Q(t)`-invariant,
  and `P ∩ M ≤ C_M(t)`, then already `P ≤ C_Q(t)`.  This handles the `DShape` clauses whose
  normal `L₂(q)`/`PGL₂(q)` has *odd* index.
* the three model shapes, proved in separate modules:
  `Work.DSTR.FourGroupCentInvariant` (clause 2 of `DShape`), `Work.DSTR.A7CentInvariant`
  (clause 3) and `Work.DSTR.L2CentInvariant` (clause 4, from the given `hl2` for `L₂(q)`).
-/

/-- A finite `p`-group with `p` odd has odd order.  (`private`: the same helper is defined in
`Submission/Work/DSTR/d110iOdd.lean`; do not re-export it from this module.) -/
private theorem odd_card_of_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hP : IsPGroup p P) : Odd (Nat.card P) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  exact Odd.pow (n := n) ((Fact.out : p.Prime).odd_of_ne_two hp)

/-- Every normal subgroup of odd order is contained in `O(G)`. -/
theorem le_oddCore_of_normal_of_odd {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (hodd : Odd (Nat.card N)) : N ≤ Work.GW2.oddCore Q := by
  show N ≤ (sSup {N : Subgroup Q | N.Normal ∧ Odd (Nat.card N)}).normalCore
  refine (Subgroup.normal_le_normalCore).mpr ?_
  exact le_sSup ⟨inferInstance, hodd⟩

/-- A normal subgroup of odd order of a group with `O(Q) = ⊥` is trivial. -/
theorem eq_bot_of_normal_of_odd_of_oddCore_eq_bot {Q : Type*} [Group Q]
    (hO : Work.GW2.oddCore Q = ⊥) (N : Subgroup Q) [N.Normal] (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  have h := le_oddCore_of_normal_of_odd N hodd
  rw [hO] at h
  exact le_bot_iff.mp h

/-- `O(Q) = ⊥` is equivalent to "no nontrivial normal odd subgroup". -/
theorem oddCore_eq_bot_iff {Q : Type*} [Group Q] [Finite Q] :
    Work.GW2.oddCore Q = ⊥ ↔ ∀ N : Subgroup Q, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  constructor
  · intro hO N hN hodd
    exact eq_bot_of_normal_of_odd_of_oddCore_eq_bot hO N hodd
  · intro h
    by_contra hne
    have hodd : Odd (Nat.card (Work.GW2.oddCore Q)) := Work.ASM.oddCore_odd Q
    exact hne (h _ (inferInstance) hodd)

/-! ### Case 1: `Q` is a `2`-group -/

/-- **Case 1 of `DShape`.**  If `Q` is a `2`-group, every odd `p`-subgroup of `Q` is trivial. -/
theorem centInvariant_of_isPGroup_two {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hO : Work.GW2.oddCore Q = ⊥) : CentInvariant Q := by
  intro t ht p hp hp2 P hP hC
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hdvd : p ^ m ∣ 2 ^ n := by
    rw [← hm, ← hn]
    exact Subgroup.card_subgroup_dvd_card P
  have hm0 : m = 0 := by
    by_contra h
    have hmpos : 0 < m := Nat.pos_of_ne_zero h
    have hp1 : p ∣ p ^ m := dvd_pow_self p (Nat.pos_iff_ne_zero.mp hmpos)
    have hp2' : p ∣ 2 ^ n := hp1.trans hdvd
    have hp_dvd_two : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow hp2'
    have hp_eq : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp_dvd_two
    exact hp2 hp_eq
  have hcard : Nat.card P = 1 := by rw [hm, hm0, pow_zero]
  have hbot : P = ⊥ := Subgroup.card_eq_one.mp hcard
  rw [hbot]
  exact bot_le

/-! ### The elementary reduction to a normal subgroup -/

/-- **Key elementary step.**  Let `M ⊴ Q`, let `t ∈ M` be an involution and let `P ≤ Q` be an
odd subgroup normalised by `C_Q(t)`.  If `P ∩ M ≤ C_Q(t)`, then `P ≤ C_Q(t)`.

Indeed, for `x ∈ P` the element `d = x⁻¹ (t x t⁻¹)` lies in `P` and — because `t ∈ M` and
`M ⊴ Q`, so that `t x t⁻¹ ≡ x` modulo `M` — also in `M`, hence in `P ∩ M ≤ C_Q(t)`.  On the
other hand `d^t = d⁻¹` (using `t² = 1`); combining, `d = d⁻¹`, so `d² = 1`, and since `d` lies in
the odd group `P` we get `d = 1`, i.e. `t x t⁻¹ = x`. -/
theorem le_centralizer_of_inf_le {Q : Type*} [Group Q] {M : Subgroup Q} (hMn : M.Normal)
    {t : Q} (ht2 : t * t = 1) (htM : t ∈ M) {P : Subgroup Q} (hPodd : Odd (Nat.card P))
    (hC : Subgroup.centralizer ({t} : Set Q) ≤ Subgroup.normalizer (P : Set Q))
    (hinf : P ⊓ M ≤ Subgroup.centralizer ({t} : Set Q)) :
    P ≤ Subgroup.centralizer ({t} : Set Q) := by
  have htinv : t⁻¹ * t⁻¹ = 1 := by rw [inv_eq_of_mul_eq_one_left ht2, ht2]
  have htC : t ∈ Subgroup.centralizer ({t} : Set Q) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have htN : t ∈ Subgroup.normalizer (P : Set Q) := hC htC
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have htx : t * x * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp htN x).mp hx
  set d : Q := x⁻¹ * (t * x * t⁻¹) with hd
  have hdP : d ∈ P := mul_mem (inv_mem hx) htx
  have hdM : d ∈ M := by
    have h1 : (QuotientGroup.mk' M) d = 1 := by
      rw [hd, map_mul, map_inv, map_mul, map_mul, map_inv]
      have ht1 : (QuotientGroup.mk' M) t = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff (N := M) t).mpr htM
      rw [ht1]
      group
    exact (QuotientGroup.eq_one_iff (N := M) d).mp h1
  have hdC : d ∈ Subgroup.centralizer ({t} : Set Q) := hinf (Subgroup.mem_inf.mpr ⟨hdP, hdM⟩)
  have hdt : t * d * t⁻¹ = d := by
    have hcomm : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
    rw [← hcomm]; group
  have hconj : t * (t * x * t⁻¹) * t⁻¹ = x := by
    have h1 : t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    rw [h1, ht2, htinv]; simp
  have hdinv : t * d * t⁻¹ = d⁻¹ := by
    rw [hd]
    have h1 : t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹ =
        (t * x⁻¹ * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
    have h2 : (x⁻¹ * (t * x * t⁻¹))⁻¹ = (t * x⁻¹ * t⁻¹) * x := by group
    rw [h1, hconj, h2]
  have hd1 : d = 1 := by
    have hdeq : d = d⁻¹ := hdt.symm.trans hdinv
    have hd2 : d ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 2 [hdeq]; exact mul_inv_cancel d
    have hodd : Odd (orderOf d) := Odd.of_dvd_nat hPodd (Subgroup.orderOf_dvd_natCard P hdP)
    have h2 : orderOf d ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hd2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h2 | h2
    · exact orderOf_eq_one_iff.mp h2
    · exact absurd (h2 ▸ hodd) (by decide)
  have h4 : x⁻¹ * (t * x * t⁻¹) = 1 := by rw [← hd]; exact hd1
  have h5 : t * x * t⁻¹ = x := by
    have := congrArg (fun w => x * w) h4
    simp only [mul_one] at this
    rwa [mul_inv_cancel_left] at this
  calc x * t = (t * x * t⁻¹) * t := by rw [h5]
    _ = t * x := by group

/-! ### The odd-index reduction -/

/-- **Reduction to a normal subgroup.**  If `M ⊴ Q` contains every involution of `Q` and the
claim holds in `M`, then it holds in `Q`.

`P ∩ M` is a `p`-subgroup of `M` normalised by `C_M(t)`, so the claim in `M` gives
`P ∩ M ≤ C_M(t) ≤ C_Q(t)`, and `le_centralizer_of_inf_le` finishes. -/
theorem centInvariant_of_normal {Q : Type*} [Group Q] [Finite Q] {M : Subgroup Q}
    (hMn : M.Normal) (hM : CentInvariant M) (hinv : ∀ t : Q, orderOf t = 2 → t ∈ M) :
    CentInvariant Q := by
  intro t ht p hp hp2 P hP hC
  have htM : t ∈ M := hinv t ht
  have ht2 : t * t = 1 := by
    have h2 : t ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [ht])
    rwa [pow_two] at h2
  let tm : M := ⟨t, htM⟩
  have htm : orderOf tm = 2 := by
    show orderOf (⟨t, htM⟩ : M) = 2
    rw [← Subgroup.orderOf_coe]; exact ht
  let R : Subgroup M := (P ⊓ M).subgroupOf M
  have hRp : IsPGroup p ↥R :=
    (hP.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hCR : Subgroup.centralizer ({tm} : Set M) ≤ Subgroup.normalizer (R : Set M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hxQ : (x : Q) ∈ Subgroup.centralizer ({t} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun w : M => (w : Q)) hx
    have hxN : (x : Q) ∈ Subgroup.normalizer (P : Set Q) := hC hxQ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxN (y : Q)).mp hy.1,
        M.mul_mem (M.mul_mem x.2 y.2) (M.inv_mem x.2)⟩
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      have hxN' : (x : Q)⁻¹ ∈ Subgroup.normalizer (P : Set Q) := Subgroup.inv_mem _ hxN
      have hmem : (x : Q)⁻¹ * ((x : Q) * (y : Q) * (x : Q)⁻¹) * (x : Q) ∈ P := by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hxN' ((x : Q) * (y : Q) * (x : Q)⁻¹)).mp hy.1
      have heq : (x : Q)⁻¹ * ((x : Q) * (y : Q) * (x : Q)⁻¹) * (x : Q) = (y : Q) := by group
      rw [Subgroup.mem_subgroupOf]
      exact ⟨by rw [heq] at hmem; exact hmem, y.2⟩
  have hres := hM tm htm p hp2 R hRp hCR
  have hinf : P ⊓ M ≤ Subgroup.centralizer ({t} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyR : (⟨y, hy.2⟩ : M) ∈ R := (Subgroup.mem_subgroupOf).mpr hy
    have hmem := hres hyR
    rw [Subgroup.mem_centralizer_singleton_iff] at hmem
    exact congrArg (fun w : M => (w : Q)) hmem
  exact le_centralizer_of_inf_le hMn ht2 htM (odd_card_of_isPGroup hp2 hP) hC hinf

/-! ### Assembly: the deliverable -/

/-- **DS9a** (`Work.GW2.D110iModelProp`, Bender 1981 1.10(i) in the reduced shapes). -/
theorem d110iModel (ha7 : Work.GW2.A7ModelProp) (hsub : Work.GW2.DihedralSubgroupProp)
    (h1 : Work.GW2.DihOrCycHeredProp) (h2 : Work.GW2.OddCoreQuotProp)
    (hautL2 : Work.GW2.AutL2Prop) (hl2 : Work.L2F.L2CentInvariantProp) :
    Work.GW2.D110iModelProp := by
  intro Q _ _ hSyl hO hD
  rcases hD with h2g | ⟨V, hVn, hV4, hVc⟩ | hA7 | ⟨L, hLn, hLodd, q, k, hq, hqodd, h5, hLiso⟩
  · exact centInvariant_of_isPGroup_two h2g hO
  · exact FourGroupCentInvariant Q V hVn hV4.1 hV4.2 hVc (oddCore_eq_bot_iff.mp hO)
  · obtain ⟨e⟩ := hA7
    exact A7CentInvariantHa7 ha7 Q e
  · -- clause 4: `L ⊴ Q` of odd index, `L` isomorphic to `L₂(q)` or `PGL₂(q)`
    haveI : Fact q.Prime := hq
    refine centInvariant_of_normal hLn ?_ ?_
    · exact L2CentInvariant hl2 L q k hqodd h5 hLiso
    · -- every involution of `Q` lies in `L` (the index is odd)
      intro t ht
      by_contra htL
      have hne : QuotientGroup.mk' L t ≠ 1 := fun h1 =>
        htL ((QuotientGroup.eq_one_iff (N := L) t).mp h1)
      have ht2 : t * t = 1 := by
        have h2 : t ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [ht])
        rwa [pow_two] at h2
      have hpow : (QuotientGroup.mk' L t) ^ 2 = 1 := by
        rw [← map_pow, pow_two, ht2, map_one]
      have hdvd : orderOf (QuotientGroup.mk' L t) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hodd : Odd L.index := hLodd
      rw [Subgroup.index_eq_card] at hodd
      have hdvd2 : orderOf (QuotientGroup.mk' L t) ∣ Nat.card (Q ⧸ L) :=
        orderOf_dvd_natCard _
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact hne (orderOf_eq_one_iff.mp h1)
      · rw [h1] at hdvd2
        exact hodd.not_two_dvd_nat hdvd2

end Work.DSTR
