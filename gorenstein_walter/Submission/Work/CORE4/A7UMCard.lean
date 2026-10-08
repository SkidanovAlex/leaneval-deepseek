import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2KB0
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The two eigenvalue facts of `s` on `U ⊓ M`, at the level of `Case2Data`

`K = I_{U∩M}(s)` is the `(-1)`-eigenspace of the involution `s` acting on the odd-order group
`U ⊓ M`, and `B₀ = C_{U∩M}(s)` is the `(+1)`-eigenspace.  The two facts recorded here are exactly
§4 (5) of Bender's paper.  They are the same arguments as `Case2KB0_b0_le_normalizer` and
`Case2KB0_inf` of `Submission/Work/CORE4/Case2KB0.lean`, but stated for an arbitrary
`Case2Data B` (those versions ask for a full `Case2Ctx B`, which carries §4 (6), (9) and the
exclusion of `A₇` — data not available here). -/

/-- **`B₀` normalises `K`.**  If `b ∈ B₀ = C_{U∩M}(s)` and `x ∈ K = I_{U∩M}(s)`, then
`b x b⁻¹ ∈ U ∩ M` and `s (b x b⁻¹) s⁻¹ = b x⁻¹ b⁻¹ = (b x b⁻¹)⁻¹`, because `s` commutes with
`b`. -/
theorem A7UMCard_b0_le_normalizer (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) :
    D.B0 ≤ Subgroup.normalizer (D.K : Set G) := by
  have hKdef : ∀ y : G, y ∈ D.K ↔ y ∈ Work.GW2.invSet (B.U ⊓ D.M) D.s :=
    fun y => Set.ext_iff.mp D.K_def y
  rw [Subgroup.le_normalizer_iff]
  intro b hb x hx
  obtain ⟨hxA, hxinv⟩ := (hKdef x).mp hx
  have hb' : b ∈ (B.U ⊓ D.M) ⊓ Subgroup.centralizer ({D.s} : Set G) := by
    rw [← D.B0_def]; exact hb
  obtain ⟨hbA, hbC⟩ := Subgroup.mem_inf.mp hb'
  have hbs : D.s * b = b * D.s :=
    (Subgroup.mem_centralizer_iff.mp hbC) D.s (Set.mem_singleton D.s)
  have hbs_inv : b⁻¹ * D.s⁻¹ = D.s⁻¹ * b⁻¹ := by
    rw [← mul_inv_rev, hbs, mul_inv_rev]
  refine (hKdef (b * x * b⁻¹)).mpr ⟨?_, ?_⟩
  · exact (B.U ⊓ D.M).mul_mem ((B.U ⊓ D.M).mul_mem hbA hxA) ((B.U ⊓ D.M).inv_mem hbA)
  · calc D.s * (b * x * b⁻¹) * D.s⁻¹
        = (D.s * b) * x * (b⁻¹ * D.s⁻¹) := by group
      _ = (b * D.s) * x * (D.s⁻¹ * b⁻¹) := by rw [hbs, hbs_inv]
      _ = b * (D.s * x * D.s⁻¹) * b⁻¹ := by group
      _ = b * x⁻¹ * b⁻¹ := by rw [hxinv]
      _ = (b * x * b⁻¹)⁻¹ := by group

/-- **`K ⊓ B₀ = ⊥`**: if `x` lies in both then `s` inverts it and fixes it, so `x = x⁻¹`,
i.e. `orderOf x ∣ 2`; but `x ∈ K ≤ U` and `U = O(H)` has odd order, so `x = 1`. -/
theorem A7UMCard_inf (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) :
    D.K ⊓ D.B0 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxK, hxB0⟩ := Subgroup.mem_inf.mp hx
  have hinv : D.s * x * D.s⁻¹ = x⁻¹ := D.K_inv B x hxK
  have hxcen : x ∈ Subgroup.centralizer ({D.s} : Set G) := by
    rw [D.B0_def] at hxB0
    exact (Subgroup.mem_inf.mp hxB0).2
  have hce : D.s * x = x * D.s :=
    (Subgroup.mem_centralizer_iff.mp hxcen) D.s (Set.mem_singleton D.s)
  have hconj : D.s * x * D.s⁻¹ = x := by
    rw [hce, mul_assoc, mul_inv_cancel, mul_one]
  have hxinv : x = x⁻¹ := by rw [← hinv, hconj]
  have hxx : x * x = 1 := by
    have h2 : x * x = x * x⁻¹ := congrArg (fun y => x * y) hxinv
    rwa [mul_inv_cancel] at h2
  have hdvd2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hxx
  have hdvdU : orderOf x ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U (D.K_le_U B hxK)
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat (Work.GW2.BenderSetup.U_odd B) hdvdU
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

/-- `|F ⊔ K| = |F| · |K|` when `F` plays the role of `B₀` (`B₀ = F`): `B₀ ≤ N_G(K)`, so
`K ⊴ K ⊔ B₀`, and `K ⊓ B₀ = ⊥`; the multiplication map `K × B₀ → K ⊔ B₀` is then a bijection. -/
theorem A7UMCard_card (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hB0F : D.B0 = D.F) :
    Nat.card ↥(D.F ⊔ D.K) = Nat.card ↥D.F * Nat.card ↥D.K := by
  have hmain := Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
    (H := D.K) (K := D.B0) (A7UMCard_b0_le_normalizer B D) (A7UMCard_inf B D)
  -- `hmain : Nat.card ↥(D.K ⊔ D.B0) = Nat.card ↥D.K * Nat.card ↥D.B0`
  have hcomm : Nat.card ↥D.K * Nat.card ↥D.F = Nat.card ↥D.F * Nat.card ↥D.K :=
    mul_comm _ _
  rw [hB0F, hcomm] at hmain
  have hsup : D.F ⊔ D.K = D.K ⊔ D.F := sup_comm D.F D.K
  rw [hsup]
  exact hmain

/-- In the `A₇` case `B₀ = F` is a subgroup of order `3` while `|K| = 3`; the two eigenspaces of
`s` on `U ∩ M` then generate a group of order `9`. -/
theorem A7UMCard {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} {C : Work.GW2.Case2Ctx6 B}
    (hB0F : C.D.B0 = C.D.F) (hK : Nat.card C.D.K = 3) (hF : Nat.card C.D.F = 3) :
    Nat.card ↥(C.D.F ⊔ C.D.K) = 9 := by
  have h1 : Nat.card ↥C.D.F * Nat.card ↥C.D.K = 9 := by rw [hF, hK]
  rw [A7UMCard_card B C.D hB0F]
  exact h1

end Work.CORE4
