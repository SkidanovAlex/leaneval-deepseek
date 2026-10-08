import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

namespace Work.CORE4

open Subgroup

/-! ## The two eigenspaces of `s` on `U ∩ M`

Throughout this file `B` is a Bender setup, `h : Case2Ctx B` is the §4 configuration, and
`D = h.D` carries the §4 objects `M, X, s, K, B₀, F`.  By definition

* `K = I_{U∩M}(s)` is the set of elements of `U ∩ M` *inverted* by `s` (`D.K_def`), and
* `B₀ = C_{U∩M}(s)` is the set of elements of `U ∩ M` *fixed* by `s` (`D.B0_def`),

so `K` and `B₀` are the `(-1)`- and `(+1)`-eigenspaces of the involution `s` acting on the
odd-order group `U ∩ M`.  The three facts recorded here are exactly §4 (2) and (5) of Bender's
paper: `K ⊓ B₀ = ⊥`, `|U ∩ M| = |K|·|B₀|` and `|K| · |U : U ∩ M| = |U : C_U(s)|`. -/

variable {G : Type} [Group G] [Finite G]

/-- **`B₀` normalises `K`.**  If `b ∈ B₀ = C_{U∩M}(s)` and `x ∈ K = I_{U∩M}(s)`, then
`b x b⁻¹ ∈ U ∩ M` and `s (b x b⁻¹) s⁻¹ = b x⁻¹ b⁻¹ = (b x b⁻¹)⁻¹`, because `s` commutes with
`b`.  Hence `U ∩ M = K ⊔ B₀ ≤ N_G(K)` — i.e. `K ⊴ U ∩ M`. -/
theorem Case2KB0_b0_le_normalizer (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    h.D.B0 ≤ Subgroup.normalizer (h.D.K : Set G) := by
  -- `D.K_def` is an equality of *sets*, so we convert it to a membership test first.
  have hKdef : ∀ y : G, y ∈ h.D.K ↔ y ∈ Work.GW2.invSet (B.U ⊓ h.D.M) h.D.s :=
    fun y => Set.ext_iff.mp h.D.K_def y
  rw [Subgroup.le_normalizer_iff]
  intro b hb x hx
  obtain ⟨hxA, hxinv⟩ := (hKdef x).mp hx
  have hb' : b ∈ (B.U ⊓ h.D.M) ⊓ Subgroup.centralizer ({h.D.s} : Set G) := by
    rw [← h.D.B0_def]; exact hb
  obtain ⟨hbA, hbC⟩ := Subgroup.mem_inf.mp hb'
  have hbs : h.D.s * b = b * h.D.s :=
    (Subgroup.mem_centralizer_iff.mp hbC) h.D.s (Set.mem_singleton h.D.s)
  have hbs_inv : b⁻¹ * h.D.s⁻¹ = h.D.s⁻¹ * b⁻¹ := by
    rw [← mul_inv_rev, hbs, mul_inv_rev]
  refine (hKdef (b * x * b⁻¹)).mpr ⟨?_, ?_⟩
  · exact (B.U ⊓ h.D.M).mul_mem ((B.U ⊓ h.D.M).mul_mem hbA hxA) ((B.U ⊓ h.D.M).inv_mem hbA)
  · calc h.D.s * (b * x * b⁻¹) * h.D.s⁻¹
        = (h.D.s * b) * x * (b⁻¹ * h.D.s⁻¹) := by group
      _ = (b * h.D.s) * x * (h.D.s⁻¹ * b⁻¹) := by rw [hbs, hbs_inv]
      _ = b * (h.D.s * x * h.D.s⁻¹) * b⁻¹ := by group
      _ = b * x⁻¹ * b⁻¹ := by rw [hxinv]
      _ = (b * x * b⁻¹)⁻¹ := by group

/-- **§4 (2), first half**: the `(-1)`- and `(+1)`-eigenspaces of `s` on `U ∩ M` meet trivially.
Indeed if `x ∈ K ⊓ B₀` then `s x s⁻¹ = x⁻¹` and `s x s⁻¹ = x`, so `x = x⁻¹`, i.e.
`orderOf x ∣ 2`; but `x ∈ U` and `U = O(H)` has odd order, so `x = 1`. -/
theorem Case2KB0_inf (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    h.D.K ⊓ h.D.B0 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxK, hxB0⟩ := Subgroup.mem_inf.mp hx
  have hinv : h.D.s * x * h.D.s⁻¹ = x⁻¹ := h.D.K_inv B x hxK
  have hxcen : x ∈ Subgroup.centralizer ({h.D.s} : Set G) := by
    rw [h.D.B0_def] at hxB0
    exact (Subgroup.mem_inf.mp hxB0).2
  have hce : h.D.s * x = x * h.D.s :=
    (Subgroup.mem_centralizer_iff.mp hxcen) h.D.s (Set.mem_singleton h.D.s)
  have hconj : h.D.s * x * h.D.s⁻¹ = x := by
    rw [hce, mul_assoc, mul_inv_cancel, mul_one]
  have hxinv : x = x⁻¹ := by rw [← hinv, hconj]
  have hxx : x * x = 1 := by
    have h2 : x * x = x * x⁻¹ := congrArg (fun y => x * y) hxinv
    rwa [mul_inv_cancel] at h2
  have hdvd2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hxx
  have hdvdU : orderOf x ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U (h.D.K_le_U B hxK)
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat B.U_odd hdvdU
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

/-- **§4 (2), second half**: `|U ∩ M| = |K| · |B₀|`.  Since `U ∩ M = K ⊔ B₀` (§4 (5)) and
`B₀ ≤ N_G(K)` (so that `K ⊴ U ∩ M`), the multiplication map `K × B₀ → U ∩ M` is a bijection
with trivial `K ⊓ B₀`. -/
theorem Case2KB0_card (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    Nat.card ↥(B.U ⊓ h.D.M) = Nat.card ↥h.D.K * Nat.card ↥h.D.B0 := by
  have hmain := Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
    (H := h.D.K) (K := h.D.B0) (Case2KB0_b0_le_normalizer B h) (Case2KB0_inf B h)
  rw [h.pre.U_eq]
  exact hmain

/-- **§4 (5)**: `|K| · |U : U ∩ M| = |U : C_U(s)|`.  Combine `|U ∩ M| = |K|·|B₀|` with the two
index formulae `|U| = |U : U ∩ M| · |U ∩ M|` and `|U| = |U : C_U(s)| · |C_U(s)|`, using
`B₀ = C_U(s) = U ⊓ C_G(s)` (`Case2Pre.B0_eq`). -/
theorem Case2KB0_relIndex (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    Nat.card ↥h.D.K * (B.U ⊓ h.D.M).relIndex B.U =
      (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U := by
  rw [← h.pre.B0_eq]
  have hA_le : B.U ⊓ h.D.M ≤ B.U := inf_le_left
  have hB0_le : h.D.B0 ≤ B.U := le_trans (h.D.B0_le B) inf_le_left
  have h1 : (B.U ⊓ h.D.M).relIndex B.U * Nat.card ↥(B.U ⊓ h.D.M) = Nat.card ↥B.U := by
    have hh := Subgroup.relIndex_mul_card (B.U ⊓ h.D.M) B.U
    rwa [inf_eq_left.mpr hA_le] at hh
  have h2 : h.D.B0.relIndex B.U * Nat.card ↥h.D.B0 = Nat.card ↥B.U := by
    have hh := Subgroup.relIndex_mul_card h.D.B0 B.U
    rwa [inf_eq_left.mpr hB0_le] at hh
  have hc : 0 < Nat.card ↥h.D.B0 := Nat.card_pos
  have hkey : ((B.U ⊓ h.D.M).relIndex B.U * Nat.card ↥h.D.K) * Nat.card ↥h.D.B0 =
      h.D.B0.relIndex B.U * Nat.card ↥h.D.B0 := by
    rw [mul_assoc, ← Case2KB0_card B h]
    rw [h1, h2]
  have hfin := Nat.eq_of_mul_eq_mul_right hc hkey
  rw [mul_comm (Nat.card ↥h.D.K) ((B.U ⊓ h.D.M).relIndex B.U)]
  exact hfin

/-- §4 (2): `K = I_{U∩M}(s)` and `B₀ = C_{U∩M}(s)` are the `-1`- and `+1`-eigenspaces of `s`
on `U ∩ M`, hence `K ⊓ B₀ = ⊥` and `|U ∩ M| = |K| · |B₀|`. Moreover `B₀ = C_U(s)` (§4 (5)), so
`|K| · |U : U ∩ M| = |U : C_U(s)|`. -/
theorem Case2KB0 :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
      h.D.K ⊓ h.D.B0 = ⊥ ∧
      Nat.card ↥(B.U ⊓ h.D.M) = Nat.card ↥h.D.K * Nat.card ↥h.D.B0 ∧
      Nat.card ↥h.D.K * (B.U ⊓ h.D.M).relIndex B.U =
        (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U := by
  intro G _ _ B h
  exact ⟨Case2KB0_inf B h, Case2KB0_card B h, Case2KB0_relIndex B h⟩

end Work.CORE4
