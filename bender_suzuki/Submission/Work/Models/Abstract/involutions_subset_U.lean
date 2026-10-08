import Mathlib
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.Abstract.involutions_subset_U`

Every involution of the Borel subgroup `B = U ⋊ T` of a Bender pair lies in the unipotent
radical `U`.

`T` normalizes `U` and `B = U ⊔ T = U · T`, so `U ⊴ B` (with quotient of order `|T|`, odd).
Hence the quotient `B ⧸ U` has odd order; an element of order dividing `2` maps to the identity
there, i.e. lies in `U`.

The intermediate facts used are assembled in the helper lemmas below:
`BenderPair.le_normalizer_U` (`B ≤ N_G(U)`), `BenderPair.index_quotient_subgroupOf_U`
(`[B : U] = |T|`, hence odd) and `BenderPair.odd_card_quotient_subgroupOf_U`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Submission.BenderPair

variable {G : Type*} [Group G] [Finite G]

/-- `U ⊴ B`: the Borel subgroup normalizes its unipotent radical. -/
theorem le_normalizer_U (P : BenderPair G) : P.B ≤ Subgroup.normalizer (P.U : Set G) := by
  rw [P.hB]
  exact sup_le Subgroup.le_normalizer P.hTnU

/-- `|B| = |U| · |T|`: `B` is the semidirect product `U ⋊ T`. -/
theorem card_eq_card_U_mul_card_T (P : BenderPair G) :
    Nat.card ↥P.B = Nat.card ↥P.U * Nat.card ↥P.T := by
  rw [P.hB]
  exact Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer
    P.U P.T P.hTnU P.hUT

/-- `[B : U] = |T|` (the quotient `B ⧸ U` is the odd-order torus `T`). -/
theorem index_subgroupOf_U (P : BenderPair G) :
    (P.U.subgroupOf P.B).index = Nat.card ↥P.T := by
  have hcardN : Nat.card ↥(P.U.subgroupOf P.B) = Nat.card ↥P.U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe P.U_le_B).toEquiv
  have hUp : 0 < Nat.card ↥P.U := by
    haveI : Nonempty ↥P.U := ⟨1⟩
    exact Nat.card_pos
  refine Nat.mul_right_cancel hUp ?_
  calc (P.U.subgroupOf P.B).index * Nat.card ↥P.U
      = (P.U.subgroupOf P.B).index * Nat.card ↥(P.U.subgroupOf P.B) := by rw [hcardN]
    _ = Nat.card ↥P.B := Subgroup.index_mul_card _
    _ = Nat.card ↥P.U * Nat.card ↥P.T := P.card_eq_card_U_mul_card_T
    _ = Nat.card ↥P.T * Nat.card ↥P.U := Nat.mul_comm _ _

/-- The quotient `B ⧸ U` has odd order `|T|`. -/
theorem odd_card_quotient_subgroupOf_U (P : BenderPair G) :
    Odd (Nat.card (↥P.B ⧸ P.U.subgroupOf P.B)) := by
  rw [← Subgroup.index_eq_card, P.index_subgroupOf_U]
  exact P.hoddT

end Submission.BenderPair

namespace Work.Models.Abstract

/-- **Every involution of `B` lies in `U`**: `B ⧸ U` has odd order (`= |T|`), while an element
of order `2` maps to an element of order dividing `2`. -/
theorem involutions_subset_U {G : Type*} [Group G] [Finite G] (P : Submission.BenderPair G) :
    Submission.Blueprint.involutions (P.B : Set G) ⊆ (P.U : Set G) := by
  intro x hx
  obtain ⟨hxB, hx2⟩ := hx
  have hUB : P.U ≤ P.B := P.U_le_B
  -- `U` is normal in `B`, so we may form the quotient of `B` by `U`.
  have hNnorm : (P.U.subgroupOf P.B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mpr P.le_normalizer_U
  haveI := hNnorm
  -- The image of the involution `x` in `B ⧸ U` has order dividing `2`.
  have hx2pow : (⟨x, hxB⟩ : ↥P.B) ^ 2 = 1 := by
    apply Subtype.ext
    change x ^ 2 = (1 : G)
    rw [← hx2]
    exact pow_orderOf_eq_one x
  have hy2 : orderOf (QuotientGroup.mk' (P.U.subgroupOf P.B) ⟨x, hxB⟩) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hx2pow, map_one]
  -- ... but that order also divides the odd number `|B ⧸ U|`, so it is `1`.
  have hy1 : QuotientGroup.mk' (P.U.subgroupOf P.B) ⟨x, hxB⟩ = 1 := by
    have hydvd : orderOf (QuotientGroup.mk' (P.U.subgroupOf P.B) ⟨x, hxB⟩) ∣
        Nat.card (↥P.B ⧸ P.U.subgroupOf P.B) := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hy2 with h1 | h1
    · rwa [orderOf_eq_one_iff] at h1
    · exfalso
      rw [h1] at hydvd
      obtain ⟨k, hk⟩ := P.odd_card_quotient_subgroupOf_U
      obtain ⟨m, hm⟩ := hydvd
      omega
  -- Hence `x ∈ U`.
  have hmemN : (⟨x, hxB⟩ : ↥P.B) ∈ P.U.subgroupOf P.B := by
    have : (⟨x, hxB⟩ : ↥P.B) ∈ (QuotientGroup.mk' (P.U.subgroupOf P.B)).ker := by
      rw [MonoidHom.mem_ker]; exact hy1
    rwa [QuotientGroup.ker_mk'] at this
  exact (Subgroup.mem_subgroupOf).mp hmemN

end Work.Models.Abstract
