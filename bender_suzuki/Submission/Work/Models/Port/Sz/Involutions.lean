/-
**The involutions of `Sz(2^(2n+1))`.**

The Sylow `2`-subgroup `U` of `Sz(2^(2n+1))` is the Suzuki `2`-group; its elements of order
`≤ 2` are exactly the elements `u(0,b)`, so `U` has `q - 1` involutions where `q = 2^(2n+1)`.
Every involution of the Borel subgroup `B = U ⋊ T` already lies in `U` (because `B/U ≅ T` has
odd order), and the abstract Bender counting theorem
`Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul` gives

  `#{involutions of Sz(q)} = [Sz : B] · #{involutions of B} = (q² + 1)(q - 1)`.

This is one of the basic numerical invariants used in the analysis of groups with a strongly
embedded subgroup.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_of_sq_eq_one_of_odd_index
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul
import Submission.Work.Models.Port.Commons.GroupTheory.OrderOfElement.card_orderOf_eq_two_eq_card_sq_eq_one_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-! ## Elements of order `≤ 2` in the Suzuki `2`-group -/

/-- `u(a,b)² = 1` iff `a = 0`: the involutions of the Suzuki `2`-group are the elements
`u(0,b)`, indexed by the additive group of the field. -/
lemma szUg_sq_eq_one_iff (n : ℕ) (a b : SzField n) :
    (szUg n a b) ^ 2 = 1 ↔ a = 0 := by
  rw [szUg_sq]
  constructor
  · intro h
    have h1 : ((0 : SzField n), a ^ (1 + 2 ^ (n + 1))) = ((0 : SzField n), (0 : SzField n)) :=
      szUg_injective n (h.trans (szUg_zero n).symm)
    have h0 : a ^ (1 + 2 ^ (n + 1)) = 0 := (Prod.ext_iff.mp h1).2
    by_contra ha
    exact pow_ne_zero _ ha h0
  · rintro rfl
    rw [zero_pow (show 1 + 2 ^ (n + 1) ≠ 0 by positivity), szUg_zero]

lemma szUg_zero_mem (n : ℕ) (b : SzField n) : szUg n 0 b ∈ szTwoGroup n := ⟨0, b, rfl⟩

lemma szUg_zero_sq (n : ℕ) (b : SzField n) :
    (⟨szUg n 0 b, szUg_zero_mem n b⟩ : ↥(szTwoGroup n)) ^ 2 = 1 := by
  refine Subtype.ext ?_
  show ((szUg n 0 b) ^ 2 : GL (Fin 4) (SzField n)) = 1
  rw [szUg_sq, zero_pow (show 1 + 2 ^ (n + 1) ≠ 0 by positivity), szUg_zero]

/-- The elements of the Suzuki `2`-group squaring to `1` number `q = 2^(2n+1)`. -/
lemma card_sq_eq_one_szTwoGroup (n : ℕ) :
    Nat.card {x : ↥(szTwoGroup n) // x ^ 2 = 1} = Nat.card (SzField n) := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun b : SzField n =>
      (⟨⟨szUg n 0 b, szUg_zero_mem n b⟩, szUg_zero_sq n b⟩ :
        {x : ↥(szTwoGroup n) // x ^ 2 = 1}))
    ⟨?_, ?_⟩)).symm.trans ?_
  · intro b₁ b₂ h
    have h2 : (⟨szUg n 0 b₁, szUg_zero_mem n b₁⟩ : ↥(szTwoGroup n)) =
        (⟨szUg n 0 b₂, szUg_zero_mem n b₂⟩ : ↥(szTwoGroup n)) := Subtype.ext_iff.mp h
    have h3 : (szUg n 0 b₁ : GL (Fin 4) (SzField n)) = szUg n 0 b₂ := by
      have h4 := congrArg Subtype.val h2
      simpa using h4
    have h5 : ((0, b₁) : SzField n × SzField n) = (0, b₂) :=
      szUg_injective n (show (fun p : SzField n × SzField n => szUg n p.1 p.2) (0, b₁) =
        (fun p : SzField n × SzField n => szUg n p.1 p.2) (0, b₂) from h3)
    exact (Prod.ext_iff.mp h5).2
  · rintro ⟨y, hy⟩
    obtain ⟨a, b, hyab⟩ := y.2
    have h1 : (szUg n a b) ^ 2 = 1 := by
      have h2 : (y : GL (Fin 4) (SzField n)) ^ 2 = 1 := by
        have h3 := Subtype.ext_iff.mp hy
        simpa using h3
      rwa [hyab] at h2
    have ha : a = 0 := (szUg_sq_eq_one_iff n a b).mp h1
    refine ⟨b, Subtype.ext (Subtype.ext ?_)⟩
    show (szUg n 0 b : GL (Fin 4) (SzField n)) = (y : GL (Fin 4) (SzField n))
    rw [hyab, ha]
  · rfl

/-- The elements of the Suzuki `2`-group inside `SzModel n` squaring to `1` number `q`. -/
lemma card_sq_eq_one_szTwoGroupS (n : ℕ) :
    Nat.card {x : ↥(szTwoGroupS n) // x ^ 2 = 1} = Nat.card (SzField n) := by
  have e := Subgroup.subgroupOfEquivOfLe (szTwoGroup_le_szModel n)
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => ?_))).trans
    (card_sq_eq_one_szTwoGroup n)
  have h1 : (e.toEquiv x) ^ 2 = e (x ^ 2) := by
    change (e x) ^ 2 = e (x ^ 2)
    exact (map_pow e x 2).symm
  rw [h1]
  exact (map_eq_one_iff e e.injective).symm

/-- The number of involutions of the Suzuki `2`-group is `q - 1`. -/
lemma card_orderOf_eq_two_szTwoGroupS (n : ℕ) :
    Nat.card {t : ↥(szTwoGroupS n) // orderOf t = 2} = Nat.card (SzField n) - 1 := by
  rw [Commons.GroupTheory.OrderOfElement.card_orderOf_eq_two_eq_card_sq_eq_one_sub_one
      (G := ↥(szTwoGroupS n)),
    card_sq_eq_one_szTwoGroupS n]

/-! ## Involutions of the Borel subgroup -/

lemma szBorelS_le_normalizer_szTwoGroupS (n : ℕ) :
    szBorelS n ≤ Subgroup.normalizer (szTwoGroupS n : Set (SzModel n)) :=
  (normalizer_szTwoGroupS n).ge

lemma szTwoGroupS_subgroupOf_normal (n : ℕ) :
    ((szTwoGroupS n).subgroupOf (szBorelS n)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (szTwoGroupS_le_szBorelS n)).mpr
    (szBorelS_le_normalizer_szTwoGroupS n)

lemma card_szBorelS (n : ℕ) :
    Nat.card ↥(szBorelS n) = 2 ^ (4 * n + 2) * (2 ^ (2 * n + 1) - 1) := by
  rw [szBorelS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szBorel_le_szModel n)).toEquiv,
    card_szBorel_eq]

/-- The index of `U` in the Borel subgroup is `q - 1`. -/
lemma szTwoGroupS_subgroupOf_index (n : ℕ) :
    ((szTwoGroupS n).subgroupOf (szBorelS n)).index = 2 ^ (2 * n + 1) - 1 := by
  have hcard : Nat.card ↥((szTwoGroupS n).subgroupOf (szBorelS n)) = 2 ^ (4 * n + 2) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (szTwoGroupS_le_szBorelS n)).toEquiv,
      card_szTwoGroupS]
  have hprod := Subgroup.index_mul_card ((szTwoGroupS n).subgroupOf (szBorelS n))
  rw [hcard, card_szBorelS n] at hprod
  exact Nat.mul_right_cancel (pow_pos (by norm_num : (0 : ℕ) < 2) _)
    (by rw [hprod, mul_comm])

/-- An element of the Borel subgroup of `Sz(2^(2n+1))` with `x² = 1` already lies in the
Suzuki `2`-group: the quotient `B/U ≅ T` has odd order. -/
lemma mem_szTwoGroupS_of_sq_eq_one (n : ℕ) {x : SzModel n} (hxB : x ∈ szBorelS n)
    (hx : x * x = 1) : x ∈ szTwoGroupS n := by
  haveI := szTwoGroupS_subgroupOf_normal n
  have hx' : (⟨x, hxB⟩ : ↥(szBorelS n)) * (⟨x, hxB⟩ : ↥(szBorelS n)) = 1 := Subtype.ext hx
  exact Commons.GroupTheory.Subgroup.mem_of_sq_eq_one_of_odd_index
    ((szTwoGroupS n).subgroupOf (szBorelS n))
    (by rw [szTwoGroupS_subgroupOf_index n]
        exact odd_two_pow_sub_one (2 * n + 1) (by omega)) hx'

lemma mem_szTwoGroupS_of_orderOf_coe_eq_two (n : ℕ) {x : SzModel n} (hxB : x ∈ szBorelS n)
    (hx : orderOf (⟨x, hxB⟩ : ↥(szBorelS n)) = 2) : x ∈ szTwoGroupS n := by
  have h2 : orderOf x = 2 := (Subgroup.orderOf_coe (⟨x, hxB⟩ : ↥(szBorelS n))).trans hx
  have h3 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  rw [h2] at h3
  refine mem_szTwoGroupS_of_sq_eq_one n hxB ?_
  rw [← pow_two]
  exact h3

/-- The number of involutions of the Borel subgroup is `q - 1`. -/
lemma card_orderOf_eq_two_szBorelS (n : ℕ) :
    Nat.card {t : ↥(szBorelS n) // orderOf t = 2} = Nat.card (SzField n) - 1 := by
  have hkey : Nat.card {t : ↥(szBorelS n) // orderOf t = 2} =
      Nat.card {t : ↥(szTwoGroupS n) // orderOf t = 2} := by
    refine le_antisymm ?_ ?_
    · let f : {t : ↥(szBorelS n) // orderOf t = 2} → {t : ↥(szTwoGroupS n) // orderOf t = 2} :=
        fun t => ⟨⟨t.1.1, mem_szTwoGroupS_of_orderOf_coe_eq_two n t.1.2 t.2⟩,
          ((Subgroup.orderOf_coe (⟨t.1.1, mem_szTwoGroupS_of_orderOf_coe_eq_two n t.1.2 t.2⟩ :
              ↥(szTwoGroupS n))).symm.trans ((Subgroup.orderOf_coe t.1).trans t.2))⟩
      refine Nat.card_le_card_of_injective f ?_
      intro a b hab
      have h1 : a.1.1 = b.1.1 := by
        have h2 : ((f a).1 : SzModel n) = ((f b).1 : SzModel n) :=
          congrArg (fun z : {t : ↥(szTwoGroupS n) // orderOf t = 2} => (z.1 : SzModel n)) hab
        simpa [f] using h2
      exact Subtype.ext (Subtype.ext h1)
    · let g : {t : ↥(szTwoGroupS n) // orderOf t = 2} → {t : ↥(szBorelS n) // orderOf t = 2} :=
        fun u => ⟨⟨u.1.1, szTwoGroupS_le_szBorelS n u.1.2⟩,
          ((Subgroup.orderOf_coe (⟨u.1.1, szTwoGroupS_le_szBorelS n u.1.2⟩ :
              ↥(szBorelS n))).symm.trans ((Subgroup.orderOf_coe u.1).trans u.2))⟩
      refine Nat.card_le_card_of_injective g ?_
      intro a b hab
      have h1 : a.1.1 = b.1.1 := by
        have h2 : ((g a).1 : SzModel n) = ((g b).1 : SzModel n) :=
          congrArg (fun z : {t : ↥(szBorelS n) // orderOf t = 2} => (z.1 : SzModel n)) hab
        simpa [g] using h2
      exact Subtype.ext (Subtype.ext h1)
  rw [hkey, card_orderOf_eq_two_szTwoGroupS n, card_szField n]

/-- **The number of involutions of `Sz(2^(2n+1))` is `(q² + 1)(q - 1)`** with `q = 2^(2n+1)`,
i.e. `(2^(4n+2) + 1)(2^(2n+1) - 1)`. -/
theorem card_involutions_SzModel (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {t : SzModel n // orderOf t = 2} =
      (2 ^ (4 * n + 2) + 1) * (2 ^ (2 * n + 1) - 1) := by
  obtain ⟨hM, hEven, hOdd⟩ := szBorel_stronglyEmbedded n hn
  rw [Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul (szBorelS n) hM hEven hOdd,
    card_szBorelS_index n, card_orderOf_eq_two_szBorelS n, card_szField n, ← pow_mul,
    show (2 * n + 1) * 2 = 4 * n + 2 from by ring]

end Submission.Sz
