import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.RED.no_elementary_abelian_eight

/-!
# RED: the centralizer of a normal subgroup with a four-subgroup and trivial centre is odd

Source: Gorenstein–Walter (1965), non-simple step (`NOTES_RED.md`, blueprint §4).

Let `G` be a finite group, `N ⊴ G` with `Z(N) = 1` and `V ≤ N` a Klein four-subgroup, and
suppose a Sylow 2-subgroup `P` of `G` is dihedral (`P ≃* DihedralGroup n`).  Then `C_G(N)`
has odd order.

The mathematics: if `t ∈ C_G(N)` were an involution then `t` centralises `V ≤ N`; as `t ∉ V`
(else `t ∈ N ∩ C_G(N) = Z(N) = 1`), the group `W = V · ⟨t⟩` is elementary abelian of order
`8 = |V| · |⟨t⟩|`.  Being a 2-group it lies in a Sylow 2-subgroup of `G`, which is conjugate
to `P`, hence `W` would give an elementary abelian subgroup of order `8` of `DihedralGroup n`,
contradicting the rank bound `hdi.elementary_abelian_card_le_four`.  Cauchy's theorem turns
"`2 ∣ |C_G(N)|`" into such an involution.
-/

namespace Work.RED

open Subgroup
open scoped Pointwise

/-- Cardinality of the join of two elementwise commuting subgroups with trivial intersection:
the multiplication map `↥H × ↥K → ↥(H ⊔ K)` is a bijection (`MonoidHom.noncommCoprod`). -/
theorem card_sup_commute_disj {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, Commute x y) (hdisj : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  classical
  have hc : ∀ (a : ↥H) (b : ↥K), Commute (H.subtype a) (K.subtype b) :=
    fun a b => hcomm (a : G) a.2 (b : G) b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hc) :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr
      ⟨H.subtype_injective, K.subtype_injective, by
        rw [H.range_subtype, K.range_subtype]; exact disjoint_iff.mpr hdisj⟩
  have hrange : (MonoidHom.noncommCoprod H.subtype K.subtype hc).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, H.range_subtype, K.range_subtype]
  rw [← Nat.card_congr
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).toEquiv, Nat.card_prod]

/-- If `N` is a subgroup with `Z(N) = 1` containing a four-group `V`, and `z ∈ C_G(N)` is an
involution, then `V · ⟨z⟩` is an elementary abelian subgroup of order `8`. -/
theorem exists_elementary_abelian_eight_of_involution
    {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (hZ : Subgroup.center ↥N = ⊥)
    {V : Subgroup G} (hVle : V ≤ N) (hV : Work.RED.GW2.IsFourGroup V)
    {z : G} (hzC : z ∈ Subgroup.centralizer (N : Set G)) (hz2 : orderOf z = 2) :
    ∃ W : Subgroup G, Nat.card W = 8 ∧ ∀ x ∈ W, x ^ 2 = 1 := by
  have hzV : z ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le hVle hzC
  have hzNormV : z ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer (V : Set G) hzV
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr hzNormV
  -- `V` and `⟨z⟩` commute elementwise
  have hcomm : ∀ v ∈ V, ∀ b ∈ Subgroup.zpowers z, Commute v b := by
    intro v hv b hb
    have hvz : Commute v z := (Subgroup.mem_centralizer_iff.mp hzV) v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact hvz.zpow_right k
  -- `N ⊓ C_G(N) = Z(N) = ⊥`
  have hinf : N ⊓ Subgroup.centralizer (N : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
    have hy : (⟨x, hxN⟩ : ↥N) ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_iff.mp hxC) (g : G) g.2
    rw [hZ, Subgroup.mem_bot] at hy
    simpa using congrArg Subtype.val hy
  -- `V ⊓ ⟨z⟩ = ⊥` because `⟨z⟩ ≤ C_G(N)` and `V ≤ N`
  have hdisj : V ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxV, hxz⟩ := Subgroup.mem_inf.mp hx
    have hx2 : x ∈ N ⊓ Subgroup.centralizer (N : Set G) :=
      Subgroup.mem_inf.mpr ⟨hVle hxV, (Subgroup.zpowers_le.mpr hzC) hxz⟩
    rw [hinf, Subgroup.mem_bot] at hx2
    exact hx2
  refine ⟨V ⊔ Subgroup.zpowers z, ?_, ?_⟩
  · rw [card_sup_commute_disj hcomm hdisj, hV.1, Nat.card_zpowers, hz2]
  · intro x hx
    have hx' : x ∈ (V : Set G) * (Subgroup.zpowers z : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left V (Subgroup.zpowers z) hnorm]
      exact hx
    rw [Set.mem_mul] at hx'
    obtain ⟨v, hv, b, hb, rfl⟩ := hx'
    have hvb : Commute v b := hcomm v hv b hb
    have hv2 : v ^ 2 = 1 := hV.2 v hv
    have hb2 : b ^ 2 = 1 := by
      have h1 : orderOf b ∣ orderOf z := orderOf_dvd_of_mem_zpowers hb
      rw [hz2] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    rw [pow_two] at hv2 hb2
    rw [pow_two, Commute.mul_mul_mul_comm hvb.symm v b, hv2, hb2]
    simp

set_option linter.unusedVariables false in
theorem odd_card_centralizer_of_four_subgroup
    (hdi : Work.RED.GW2.DihedralFactsProp)
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) (hNn : N.Normal)
    (hZ : Subgroup.center ↥N = ⊥)
    {n : ℕ} [NeZero n] {P : Sylow 2 G} (e : ↥(P : Subgroup G) ≃* DihedralGroup n) (hn : 2 ≤ n)
    (hV : ∃ V : Subgroup G, V ≤ N ∧ Work.RED.GW2.IsFourGroup V) :
    Odd (Nat.card (Subgroup.centralizer (N : Set G))) := by
  obtain ⟨V, hVle, hV⟩ := hV
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  -- `2 ∣ |C_G(N)|` gives an involution `z ∈ C_G(N)` (Cauchy)
  obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  have hz2' : orderOf (z : G) = 2 := by rw [orderOf_coe, hz2]
  obtain ⟨W, hWcard, hW2⟩ :=
    exists_elementary_abelian_eight_of_involution N hZ hVle hV z.2 hz2'
  exact no_elementary_abelian_eight hdi e ⟨W, hWcard, hW2⟩

end Work.RED
