/-
Area `A7REC` (recognition of `A₇`), file `Basic/exists_involution_inverting.lean`.

# An involution inverting a nontrivial element of `U`

Let `G` be a finite group satisfying the `A₇` hypotheses (`A7RecCtx G`): the Sylow
`2`-subgroup `S` is isomorphic to the dihedral group `D₈` of order `8` with central involution
`z`, `C_G(z) = U ⊔ S` with `|U| = 3` and `U ⊴ C_G(z)`, `V = O₂(C_G(z))` a four-group with
`N_G(U) = N_G(V)` of order `72`, and the involution centralizer has order `24`.

We prove that every nontrivial `σ ∈ U` is inverted by some involution:

`∃ τ', orderOf τ' = 2 ∧ τ' * σ * τ'⁻¹ = σ⁻¹`.

This is the group-theoretic input behind Suzuki's configuration `(S', τ')` of Suzuki 1959 §8:
it produces the involution `τ'` normalizing `U` with `U^τ' = U` which, together with the
one-class hypothesis, yields the `A₇` configuration used in `Char/a7Config.lean`.

## The proof

`U` has prime order `3`, so `σ` has order `3` and generates `U` (`zpowers σ = U`).

* `V ≤ C_G(U)`: `⁅U, V⁆ = ⊥` (`commute_U_V`), so `V` centralizes `U`.
* `S ⊓ C_G(U) = V`: it contains `V` and has order dividing `8`; order `8` would mean `S ≤ C_G(U)`
  and hence `8 ∣ 36 = |C_G(U)|` (`card_centralizer_U`), so the order is `4 = |V|`.
* `involutionNotMemFour` (applied to `S ≃* DihedralGroup 4` and the four-group `V ≤ S`)
  produces `t ∈ S ∖ V` with `t * t = 1`; thus `t` is an involution of `S` lying outside
  `S ⊓ C_G(U)`, so `t` does **not** centralize `σ`.
* `S ≤ N_G(U)` (`S_le_normalizer_U`), so `t σ t⁻¹ ∈ U`; its order is `3`, hence it is `σ` or
  `σ⁻¹` (`eq_or_eq_inv_of_mem_zpowers_of_orderOf_three`); as it is not `σ`, it is `σ⁻¹`, and
  `τ' = t` works.
-/
import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.Basic.local
import Submission.Work.A7REC.Basic.exists_tau_order_four
import Submission.Work.A7REC.Basic.V_le_S
import Submission.Work.A7REC.Char.involutionNotMemFour

namespace Work.A7REC.Basic

open Subgroup

/-- In a cyclic group `⟨σ⟩` of order `3`, an element of order `3` is `σ` or `σ⁻¹`. -/
lemma zpowers_order_three_eq_or_inv {G : Type*} [Group G] [Finite G] {σ x : G}
    (hσ : orderOf σ = 3) (hx : x ∈ Subgroup.zpowers σ) (hx3 : orderOf x = 3) :
    x = σ ∨ x = σ⁻¹ := by
  classical
  have h3 : σ ^ (3 : ℕ) = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσ2 : σ ^ (2 : ℕ) = σ⁻¹ := by
    have h4 : σ ^ 2 * σ = 1 := by rw [← pow_succ]; simpa using h3
    exact eq_inv_of_mul_eq_one_left h4
  obtain ⟨i, hi, hix⟩ :=
    Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := σ)).mp hx)
  have hi3 : i < 3 := by rw [hσ] at hi; simpa using hi
  interval_cases i
  · exfalso
    rw [pow_zero] at hix
    rw [← hix] at hx3
    simp at hx3
  · left; rw [pow_one] at hix; exact hix.symm
  · right; rw [hσ2] at hix; exact hix.symm

theorem exists_involution_inverting {G : Type} [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G)
    {σ : G} (hσU : σ ∈ ctx.U) (hσ1 : σ ≠ 1) :
    ∃ τ' : G, orderOf τ' = 2 ∧ τ' * σ * τ'⁻¹ = σ⁻¹ := by
  classical
  -- ### Step 0: `σ` has order `3` and generates `U`
  have hσ3 : orderOf σ = 3 := by
    have hdvd : orderOf σ ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard ctx.U hσU
      rwa [ctx.hUcard] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hσ1
    · exact h3
  have hUgen : ctx.U = Subgroup.zpowers σ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hσU) ?_).symm
    rw [Nat.card_zpowers, hσ3, ctx.hUcard]
  -- ### Step 1: `V ≤ C_G(U)` and `S ⊓ C_G(U) = V`
  have hV_le_CU : ctx.V ≤ Subgroup.centralizer (ctx.U : Set G) := by
    have h := commute_U_V G ctx
    rw [Subgroup.commutator_comm] at h
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ctx.V) (H₂ := ctx.U)).mp h
  have hSinfCU : (ctx.S : Subgroup G) ⊓ Subgroup.centralizer (ctx.U : Set G) = ctx.V := by
    have hle : ctx.V ≤ (ctx.S : Subgroup G) ⊓ Subgroup.centralizer (ctx.U : Set G) :=
      le_inf (V_le_S G ctx) hV_le_CU
    have hdvd : Nat.card ↥((ctx.S : Subgroup G) ⊓
        Subgroup.centralizer (ctx.U : Set G)) ∣ 8 := by
      have h := Subgroup.card_dvd_of_le (α := G)
        (inf_le_left : (ctx.S : Subgroup G) ⊓ Subgroup.centralizer (ctx.U : Set G) ≤
          (ctx.S : Subgroup G))
      rwa [card_S G ctx] at h
    have hne8 : Nat.card ↥((ctx.S : Subgroup G) ⊓
        Subgroup.centralizer (ctx.U : Set G)) ≠ 8 := by
      intro h8
      have hEq : (ctx.S : Subgroup G) ⊓ Subgroup.centralizer (ctx.U : Set G) =
          (ctx.S : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, card_S G ctx])
      have hS_le : (ctx.S : Subgroup G) ≤ Subgroup.centralizer (ctx.U : Set G) :=
        hEq ▸ inf_le_right
      have hdvd8 : (8 : ℕ) ∣ 36 := by
        have h := Subgroup.card_dvd_of_le (α := G) hS_le
        rwa [card_S G ctx, card_centralizer_U G ctx] at h
      norm_num at hdvd8
    have hge : 4 ≤ Nat.card ↥((ctx.S : Subgroup G) ⊓
        Subgroup.centralizer (ctx.U : Set G)) := by
      have h := Subgroup.card_le_of_le hle
      rwa [ctx.hV4.1] at h
    have hcard4 : Nat.card ↥((ctx.S : Subgroup G) ⊓
        Subgroup.centralizer (ctx.U : Set G)) = 4 := by
      rcases hdvd with ⟨k, hk⟩
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk; omega
        · exact h
      have hkle : k ≤ 2 := by
        have h : 4 * k ≤ Nat.card ↥((ctx.S : Subgroup G) ⊓
            Subgroup.centralizer (ctx.U : Set G)) * k := Nat.mul_le_mul_right k hge
        rw [← hk] at h
        omega
      interval_cases k
      · omega
      · omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard4, ctx.hV4.1])).symm
  -- ### Step 2: an involution `t ∈ S ∖ V`
  obtain ⟨eS⟩ := ctx.hSdih
  obtain ⟨t, ht2, htW⟩ :=
    Work.A7REC.Char.involutionNotMemFour eS (ctx.V.subgroupOf (ctx.S : Subgroup G))
      (fun w hw => Subtype.ext (by
        have hw' : (w : G) ∈ ctx.V := Subgroup.mem_subgroupOf.mp hw
        simpa [pow_two] using ctx.hV4.2 (w : G) hw'))
  have htS : (t : G) ∈ (ctx.S : Subgroup G) := t.2
  have htV : (t : G) ∉ ctx.V := fun h => htW (Subgroup.mem_subgroupOf.mpr h)
  have htsq : (t : G) * (t : G) = 1 := by
    have := congrArg (fun x : ↥(ctx.S : Subgroup G) => (x : G)) ht2
    simpa using this
  have htne : (t : G) ≠ 1 := by
    intro h
    have h1 : t = 1 := Subtype.ext (by simpa using h)
    exact htW (by rw [h1]; exact Subgroup.one_mem _)
  have ht2ord : orderOf (t : G) = 2 :=
    orderOf_eq_prime (p := 2) (by simpa [pow_two] using htsq) htne
  -- ### Step 3: `t ∈ N_G(U) ∖ C_G(U)`, hence `t` inverts `σ`
  have htN : (t : G) ∈ Subgroup.normalizer (ctx.U : Set G) := S_le_normalizer_U G ctx htS
  have htC : (t : G) ∉ Subgroup.centralizer (ctx.U : Set G) := by
    intro h
    exact htV (by rw [← hSinfCU]; exact ⟨htS, h⟩)
  have hmem_iff : (t : G) ∈ Subgroup.centralizer (ctx.U : Set G) ↔
      (t : G) * σ * (t : G)⁻¹ = σ := by
    rw [hUgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1; rw [h1]; group
    · intro h1
      rw [show (t : G) * σ = ((t : G) * σ * (t : G)⁻¹) * (t : G) from by group, h1]
  have hconj_ne : (t : G) * σ * (t : G)⁻¹ ≠ σ := fun h => htC (hmem_iff.mpr h)
  have hconj_mem : (t : G) * σ * (t : G)⁻¹ ∈ ctx.U :=
    (Subgroup.mem_normalizer_iff.mp htN σ).mp hσU
  have hconj_ord : orderOf ((t : G) * σ * (t : G)⁻¹) = 3 := by
    rw [← MulAut.conj_apply (t : G) σ, MulEquiv.orderOf_eq, hσ3]
  have hkey := zpowers_order_three_eq_or_inv (σ := σ)
    (x := (t : G) * σ * (t : G)⁻¹) hσ3 (hUgen ▸ hconj_mem) hconj_ord
  rcases hkey with h | h
  · exact absurd h hconj_ne
  · exact ⟨(t : G), ht2ord, h⟩

end Work.A7REC.Basic
