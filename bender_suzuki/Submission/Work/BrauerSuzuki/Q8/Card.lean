import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.isTISet_cstar_diff
import Submission.Work.BrauerSuzuki.Q8.oddCore_centralizer_map_normalized

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Cardinalities of `C*`, `N*`, `A*` in Glauberman's `Q₈` argument

With `S : Sylow 2 G`, `d : GenQuaternionData ↥S`, `d.n = 2`, `x` of order `4` in `S`
(`Work.BrauerSuzuki.Q8.Ctx x S`), so that `X = ⟨x⟩`, `T = ⟨x²⟩`, `C* = C_G(X)`,
`N* = N_G(X)`, `H* = O_{2'}(C*)`:

* `|C*| = 4 |H*|`, `|N*| = 8 |H*|`, `|A*| = 2 |H*|`, where `A* = C* \ (T · H*)`.

The proofs use the product formula `|H ∨ K| |H ∧ K| = |H| |K|` for
`K ≤ N_G(H)` (`Work.PGroup.card_sup_mul_card_inf_of_le_normalizer`) and the fact that `S`
normalizes `H*` (`oddCore_centralizer_map_normalized`, via `S ≤ N*`), so that `S H* = S ⊔ H*`
is a subgroup.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G] [Finite G]

namespace Ctx

variable {x : G} {S : Sylow 2 G}

theorem S_inf_Hstar (h : Ctx G x S) : (S : Subgroup G) ⊓ Hstar x = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyS, hyH⟩ := hy
  have hdiv : orderOf y ∣ 8 := by
    have h1 := orderOf_dvd_natCard_of_mem (H := (S : Subgroup G)) hyS
    rwa [h.card_S] at h1
  have hodd : Odd (orderOf y) := odd_orderOf_of_mem h.odd_H hyH
  have hcop : Nat.Coprime (orderOf y) 8 := by
    have h1 : (orderOf y).Coprime 2 := hodd.coprime_two_right
    have h2 := Nat.Coprime.pow_right 3 h1
    norm_num at h2
    exact h2
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdiv)

theorem S_le_normalizer_Hstar (h : Ctx G x S) :
    (S : Subgroup G) ≤ Subgroup.normalizer ↑(Hstar x) := by
  rw [Subgroup.le_normalizer_iff]
  intro n hn m hm
  exact oddCore_centralizer_map_normalized (X x) n (h.le_N hn) m hm

theorem Hstar_normal_Nstar' (h : Ctx G x S) {n m : G} (hn : n ∈ Nstar x) (hm : m ∈ Hstar x) :
    n * m * n⁻¹ ∈ Hstar x :=
  oddCore_centralizer_map_normalized (X x) n hn m hm

theorem card_Cstar (h : Ctx G x S) : Nat.card ↥(Cstar x) = 4 * Nat.card ↥(Hstar x) := by
  have hcomp := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := X x) (K := Hstar x)
    (le_trans h.Hstar_le_Cstar (Subgroup.centralizer_le_normalizer (X x : Set G)))
  rw [h.supC, h.infC, Subgroup.card_bot, h.X_card, mul_one] at hcomp
  exact hcomp

theorem T_inf_Hstar (h : Ctx G x S) : T x ⊓ Hstar x = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_inf] at hy
  have hy' : y ∈ X x ⊓ Hstar x := ⟨h.T_le_X hy.1, hy.2⟩
  rw [h.infC] at hy'
  simpa using hy'

theorem Hstar_le_centralizer_T (h : Ctx G x S) :
    Hstar x ≤ Subgroup.centralizer (T x : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact h.comm a (h.T_le_X ha) b hb

theorem card_T_sup_Hstar (h : Ctx G x S) :
    Nat.card ↥(T x ⊔ Hstar x) = 2 * Nat.card ↥(Hstar x) := by
  have hcomp := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := T x) (K := Hstar x)
    (le_trans h.Hstar_le_centralizer_T (Subgroup.centralizer_le_normalizer (T x : Set G)))
  rw [h.T_inf_Hstar, Subgroup.card_bot, h.T_card, mul_one] at hcomp
  exact hcomp

theorem card_Nstar (h : Ctx G x S) : Nat.card ↥(Nstar x) = 8 * Nat.card ↥(Hstar x) := by
  have hcomp := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
    (H := Hstar x) (K := (S : Subgroup G)) h.S_le_normalizer_Hstar
  have hinf : Hstar x ⊓ (S : Subgroup G) = ⊥ := by rw [inf_comm]; exact h.S_inf_Hstar
  rw [hinf, Subgroup.card_bot, h.card_S, mul_one, sup_comm, h.supN] at hcomp
  rw [mul_comm]
  exact hcomp

/-- The set product `T · H*` is the subgroup `T ⊔ H*`. -/
theorem coe_T_mul_Hstar (h : Ctx G x S) :
    (T x : Set G) * (Hstar x : Set G) = ((T x ⊔ Hstar x : Subgroup G) : Set G) :=
  (Subgroup.coe_mul_of_right_le_normalizer_left (T x) (Hstar x)
    (le_trans h.Hstar_le_centralizer_T
      (Subgroup.centralizer_le_normalizer (T x : Set G)))).symm

theorem card_THstar (h : Ctx G x S) :
    Nat.card ↥((T x : Set G) * (Hstar x : Set G)) = 2 * Nat.card ↥(Hstar x) := by
  rw [h.coe_T_mul_Hstar]
  exact h.card_T_sup_Hstar

/-- `T · H*` is contained in `C*`. -/
theorem mul_T_Hstar_subset_Cstar (h : Ctx G x S) :
    ((T x : Set G) * (Hstar x : Set G)) ⊆ (Cstar x : Set G) := by
  intro y hy
  rw [Set.mem_mul] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  exact (Cstar x).mul_mem (h.T_le_Cstar ha) (h.Hstar_le_Cstar hb)

/-- `C*` is the disjoint union of the subgroup `T · H*` and Glauberman's `A*`. -/
theorem card_Cstar_eq_add (h : Ctx G x S) :
    Nat.card ↥(Cstar x) = Nat.card ↥((T x : Set G) * (Hstar x : Set G)) +
      Nat.card ↥(Astar x) := by
  let P : Set G := (T x : Set G) * (Hstar x : Set G)
  have hsub := h.mul_T_Hstar_subset_Cstar
  have e : ↥(Cstar x) ≃ ↥P ⊕ ↥(Astar x) :=
    { toFun := fun y =>
        if hy : (y : G) ∈ P then Sum.inl ⟨(y : G), hy⟩
        else Sum.inr ⟨(y : G), y.2, hy⟩
      invFun := fun z => match z with
        | Sum.inl w => ⟨(w : G), hsub w.2⟩
        | Sum.inr v => ⟨(v : G), v.2.1⟩
      left_inv := by
        intro y
        by_cases hy : (y : G) ∈ P <;> simp [hy]
      right_inv := by
        intro z
        rcases z with w | v
        · simp only
          rw [dif_pos w.2]
        · simp only
          rw [dif_neg v.2.2] }
  have h1 := Nat.card_congr e
  rw [Nat.card_sum] at h1
  exact h1

theorem card_Astar (h : Ctx G x S) : Nat.card ↥(Astar x) = 2 * Nat.card ↥(Hstar x) := by
  have h1 := h.card_Cstar_eq_add
  have h2 := h.card_Cstar
  have h3 := h.card_THstar
  omega

end Ctx

end Work.BrauerSuzuki.Q8
