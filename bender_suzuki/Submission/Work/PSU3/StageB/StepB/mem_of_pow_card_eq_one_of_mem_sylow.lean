import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.StepB.mem_of_pow_card_eq_one_of_mem_sylow`

Bender–Suzuki (GLS, Number 2, §2): in a finite **Z-group** `K` (one all of whose Sylow subgroups
are cyclic), if `P` is a Sylow `p`-subgroup and `y ∈ P` satisfies `y ^ |N| = 1` for a normal
subgroup `N ≤ K`, then `y ∈ N`.

The proof has two ingredients.

* `P ⊓ N` is a Sylow `p`-subgroup of `N`, i.e. `|P ⊓ N| = p ^ (|N|).factorization p` is exactly
  the `p`-part of `|N|` (`card_inf_normal_sylow_pow` below).  The key point is that
  `[N : P ⊓ N] = [P ⊔ N : P]` divides `[K : P]`, which is prime to `p`; this is bookkept with
  `Subgroup.relIndex` (no normality of `P` is available, so no quotient by `P` can be formed
  directly).
* `y ∈ P` and `y ^ |N| = 1` force `orderOf y` to be a `p`-power dividing `|N|`, hence dividing
  `|P ⊓ N|`.  Since `↥P` is cyclic, `IsCyclic.subgroup_le_iff_card_dvd` turns the order
  divisibility `orderOf y ∣ |P ⊓ N|` into the subgroup inclusion `⟨y⟩ ≤ P ⊓ N`.
-/

set_option linter.style.haveILetI false

namespace Work.PSU3.StageB.StepB

/-- For a Sylow `p`-subgroup `P` of a finite group `K` and a normal subgroup `N`, the intersection
`P ⊓ N` is a Sylow `p`-subgroup of `N`: it has order the `p`-part of `|N|`. -/
theorem card_inf_normal_sylow_pow {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (P : Sylow p K) (N : Subgroup K) [N.Normal] :
    Nat.card ↥((P : Subgroup K) ⊓ N) = p ^ (Nat.card ↥N).factorization p := by
  classical
  have hinf : IsPGroup p ↥((P : Subgroup K) ⊓ N) := IsPGroup.to_inf_left P.isPGroup'
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hinf
  -- `[N : P ⊓ N] = [P ⊔ N : P]` divides `[K : P]`, which is prime to `p`
  have hdvd : ((P : Subgroup K) ⊓ N).relIndex N ∣ (P : Subgroup K).index := by
    set A : Subgroup K := (P : Subgroup K) ⊓ N with hA
    have h1 : A.relIndex (P : Subgroup K) * (P : Subgroup K).relIndex ((P : Subgroup K) ⊔ N)
        = A.relIndex ((P : Subgroup K) ⊔ N) :=
      Subgroup.relIndex_mul_relIndex A _ _ inf_le_left le_sup_left
    have h2 : A.relIndex N * N.relIndex ((P : Subgroup K) ⊔ N)
        = A.relIndex ((P : Subgroup K) ⊔ N) :=
      Subgroup.relIndex_mul_relIndex A _ _ inf_le_right le_sup_right
    have h3 : N.relIndex ((P : Subgroup K) ⊔ N) = N.relIndex (P : Subgroup K) :=
      Subgroup.relIndex_sup_right (P : Subgroup K) N
    have h4 : N.relIndex (P : Subgroup K) = A.relIndex (P : Subgroup K) := by
      rw [← Subgroup.inf_relIndex_right N (P : Subgroup K)]
      congr 1
      rw [hA, inf_comm]
    have hne : A.relIndex (P : Subgroup K) ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    have heq : A.relIndex (P : Subgroup K) * (P : Subgroup K).relIndex ((P : Subgroup K) ⊔ N)
        = A.relIndex (P : Subgroup K) * A.relIndex N := by
      calc A.relIndex (P : Subgroup K) * (P : Subgroup K).relIndex ((P : Subgroup K) ⊔ N)
          = A.relIndex ((P : Subgroup K) ⊔ N) := h1
        _ = A.relIndex N * N.relIndex ((P : Subgroup K) ⊔ N) := h2.symm
        _ = A.relIndex N * N.relIndex (P : Subgroup K) := by rw [h3]
        _ = A.relIndex N * A.relIndex (P : Subgroup K) := by rw [h4]
        _ = A.relIndex (P : Subgroup K) * A.relIndex N := Nat.mul_comm _ _
    have h5 : (P : Subgroup K).relIndex ((P : Subgroup K) ⊔ N) = A.relIndex N :=
      Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) heq
    rw [← h5]
    exact Subgroup.relIndex_dvd_index_of_le le_sup_left
  have hnotdvd : ¬ p ∣ ((P : Subgroup K) ⊓ N).relIndex N :=
    fun h => Sylow.not_dvd_index P (h.trans hdvd)
  have hANne : ((P : Subgroup K) ⊓ N).relIndex N ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  -- the `p`-part of `|N|` is the `p`-part of `|P ⊓ N|`, namely `b`
  have hfac : (Nat.card ↥N).factorization p = b := by
    have hAN : Nat.card ↥(((P : Subgroup K) ⊓ N).subgroupOf N)
        = Nat.card ↥((P : Subgroup K) ⊓ N) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h1 : Nat.card ↥N = p ^ b * ((P : Subgroup K) ⊓ N).relIndex N := by
      rw [← Subgroup.card_mul_index (((P : Subgroup K) ⊓ N).subgroupOf N), hAN, hb]
      rfl
    rw [h1, Nat.factorization_mul (a := p ^ b)
      (b := ((P : Subgroup K) ⊓ N).relIndex N)
      (pow_ne_zero b (Nat.Prime.ne_zero Fact.out)) hANne]
    simp [Finsupp.add_apply, Nat.Prime.factorization_pow Fact.out,
      Nat.factorization_eq_zero_of_not_dvd hnotdvd]
  rw [hb, hfac]

/-- **Bender–Suzuki, GLS Number 2, §2.**  In a finite group `K` all of whose Sylow subgroups are
cyclic (`IsZGroup K`), an element `y` of a Sylow `p`-subgroup `P` with `y ^ |N| = 1` lies in every
normal subgroup `N` of `K`. -/
theorem mem_of_pow_card_eq_one_of_mem_sylow {K : Type*} [Group K] [Finite K] [IsZGroup K]
    {N : Subgroup K} [N.Normal] {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    {y : K} (hy : y ∈ P) (hyN : y ^ Nat.card ↥N = 1) : y ∈ N := by
  classical
  -- `↥P` is cyclic
  haveI hcyc : IsCyclic ↥(P : Subgroup K) := IsPGroup.isCyclic_of_isZGroup P.isPGroup'
  -- `orderOf y` is a `p`-power
  have horder : orderOf (⟨y, hy⟩ : ↥P) = orderOf y := Subgroup.orderOf_mk y hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') (⟨y, hy⟩ : ↥P)
  rw [horder] at hk
  -- `orderOf y ∣ |N|`, hence `orderOf y ∣ p ^ (|N|).factorization p`
  have hdvdN : orderOf y ∣ Nat.card ↥N := orderOf_dvd_iff_pow_eq_one.mpr hyN
  have hNne : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  have hk_le : k ≤ (Nat.card ↥N).factorization p := by
    rw [hk] at hdvdN
    exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out hNne).mp hdvdN
  have hcardS' : Nat.card ↥(((P : Subgroup K) ⊓ N).subgroupOf (P : Subgroup K)) =
      Nat.card ↥((P : Subgroup K) ⊓ N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show (P : Subgroup K) ⊓ N ≤ (P : Subgroup K) from inf_le_left)).toEquiv
  have hordS : orderOf y ∣
      Nat.card ↥(((P : Subgroup K) ⊓ N).subgroupOf (P : Subgroup K)) := by
    rw [hcardS', card_inf_normal_sylow_pow P N, hk]
    exact Nat.pow_dvd_pow p hk_le
  -- in the cyclic group `↥P`, an element of order dividing `|P ⊓ N|` lies in `P ⊓ N`
  have hle : Subgroup.zpowers (⟨y, hy⟩ : ↥P) ≤
      ((P : Subgroup K) ⊓ N).subgroupOf (P : Subgroup K) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd]
    rwa [Nat.card_zpowers, horder]
  have hzS : (⟨y, hy⟩ : ↥P) ∈ ((P : Subgroup K) ⊓ N).subgroupOf (P : Subgroup K) :=
    hle (Subgroup.mem_zpowers _)
  exact (Subgroup.mem_subgroupOf.mp hzS).2

end Work.PSU3.StageB.StepB
