import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.BrauerSuzuki.Q8.Vocab
import Submission.Work.BrauerSuzuki.Q8.LamEta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Elementary properties of Glauberman's set `B`

`Work.BrauerSuzuki.Q8.Bset x` is the set of `G`-conjugates of the elements of
`A* = C* \ (T · H*)`, where `C* = C_G(⟨x⟩)`, `T = ⟨x²⟩` and `H* = O_{2'}(C*)`.

The structural hypotheses `Ctx G x S` give `C* = X · H*` with `X = ⟨x⟩` and with `X` and `H*`
commuting elementwise and intersecting trivially.  Consequently an element `a = v · w`
(`v ∈ X`, `w ∈ H*`) of `A*` satisfies `v ∉ T`, whence `orderOf v = 4`, and then
`a ^ (orderOf w) = v ^ (orderOf w)` has order `4` (because `orderOf w` is odd).  As the order of a
power divides the order of the element, `4 ∣ orderOf a`; conjugation preserves the order, so every
element of `B` has order divisible by `4`.  In particular `1` and `x ^ 2` (of order `2`) do not
lie in `B`.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

/-- **The product decomposition of a supremum of commuting subgroups.**

If the subgroups `H` and `K` of a group commute elementwise, then every element of `H ⊔ K` is a
product `a * b` with `a ∈ H` and `b ∈ K`.  (The point is that products of elements of `H` and `K`
can be rearranged, so the set of such products is a subgroup.) -/
theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, a * b = g := by
  rw [Subgroup.sup_eq_closure] at hg
  have key : ∀ g ∈ Subgroup.closure ((H : Set G) ∪ (K : Set G)),
      ∃ a ∈ H, ∃ b ∈ K, a * b = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, K.one_mem, mul_one x⟩
      · exact ⟨1, H.one_mem, x, hx, one_mul x⟩
    | one => exact ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨a1, ha1, b1, hb1, rfl⟩ := ihx
      obtain ⟨a2, ha2, b2, hb2, rfl⟩ := ihy
      refine ⟨a1 * a2, H.mul_mem ha1 ha2, b1 * b2, K.mul_mem hb1 hb2, ?_⟩
      calc a1 * a2 * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
        _ = a1 * (b1 * a2) * b2 := by rw [hcomm a2 ha2 b1 hb1]
        _ = a1 * b1 * (a2 * b2) := by group
    | inv x hx ihx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihx
      refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, ?_⟩
      have h := congrArg Inv.inv (hcomm a ha b hb)
      simp only [mul_inv_rev] at h
      rw [mul_inv_rev, h]
  exact key g hg

/-- If `orderOf x = 4`, then `v ∈ ⟨x⟩ \ ⟨x²⟩` has order `4`.

Writing `v = x ^ n` and noting that `n` cannot be even (otherwise `v ∈ ⟨x²⟩`), we get
`orderOf v = orderOf x / gcd (orderOf x) n = 4 / gcd 4 n = 4` because `n` is odd. -/
theorem orderOf_eq_four_of_mem_zpowers_notMem_sq {G : Type*} [Group G] [Finite G] {x v : G}
    (hx4 : orderOf x = 4) (hv : v ∈ Subgroup.zpowers x)
    (hvT : v ∉ Subgroup.zpowers (x ^ 2)) : orderOf v = 4 := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff v x).mp
    ((isOfFinOrder_of_finite x).mem_powers_iff_mem_zpowers.mpr hv)
  have hodd : Odd n := by
    rw [← Nat.not_even_iff_odd]
    intro hn
    apply hvT
    obtain ⟨m, hm⟩ := (even_iff_two_dvd.mp hn)
    rw [hm, pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m
  rw [orderOf_pow, hx4]
  have hcop : Nat.Coprime (2 ^ 2) n := (Nat.coprime_two_left.mpr hodd).pow_left 2
  have hgcd : Nat.gcd 4 n = 1 := hcop
  rw [hgcd]

open Classical in
theorem Bset_facts {G : Type*} [Group G] [Finite G] {x : G} {S : Sylow 2 G}
    (h : Work.BrauerSuzuki.Q8.Ctx G x S) :
    (1 : G) ∉ Work.BrauerSuzuki.Q8.Bset x ∧
      x ^ 2 ∉ Work.BrauerSuzuki.Q8.Bset x ∧
      (∀ y : G, y ∈ Work.BrauerSuzuki.Q8.Bset x → 4 ∣ orderOf y) ∧
      (∀ a : G, a ∈ Work.BrauerSuzuki.Q8.Astar x → 4 ∣ orderOf a) := by
  -- Every element of `A*` has order divisible by `4`.
  have hA : ∀ a : G, a ∈ Astar x → 4 ∣ orderOf a := by
    intro a ha
    obtain ⟨haC, haT⟩ := ha
    -- `C* = X · H*`: decompose `a` accordingly
    have hmemsup : a ∈ X x ⊔ Hstar x := by rw [h.supC]; exact haC
    obtain ⟨v, hv, w, hw, hvw⟩ := exists_mul_of_mem_sup_of_commute h.comm hmemsup
    -- the `X`-component of `a` is not in `T`
    have hvT : v ∉ T x := by
      intro hvT'
      exact haT (Set.mem_mul.mpr ⟨v, hvT', w, hw, hvw⟩)
    have hov : orderOf v = 4 := orderOf_eq_four_of_mem_zpowers_notMem_sq h.hx4 hv hvT
    -- the `H*`-component has odd order
    have hoddw : Odd (orderOf w) := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      have h2 : 2 ∣ Nat.card ↥(Hstar x) :=
        (even_iff_two_dvd.mp hev).trans (Subgroup.orderOf_dvd_natCard _ hw)
      obtain ⟨j, hj⟩ := h2
      obtain ⟨k, hk⟩ := h.odd_H
      omega
    have hcop : Nat.gcd 4 (orderOf w) = 1 := (Nat.coprime_two_left.mpr hoddw).pow_left 2
    -- `a ^ orderOf w = v ^ orderOf w` has order `4`
    have hcommvw : Commute v w := h.comm v hv w hw
    have haK : a ^ orderOf w = v ^ orderOf w := by
      rw [← hvw, hcommvw.mul_pow, pow_orderOf_eq_one, mul_one]
    have hovk : orderOf (v ^ orderOf w) = 4 := by
      rw [orderOf_pow, hov, hcop]
    have hdvd : orderOf (a ^ orderOf w) ∣ orderOf a := orderOf_pow_dvd _
    rw [haK, hovk] at hdvd
    exact hdvd
  -- Conjugation preserves the order, so the same holds on `B`.
  have hB : ∀ y : G, y ∈ Bset x → 4 ∣ orderOf y := by
    rintro y ⟨a, ha, hconj⟩
    obtain ⟨c, hc⟩ := hconj
    rw [hc.orderOf_eq]
    exact hA a ha
  have hx2 : orderOf (x ^ 2) = 2 := by rw [orderOf_pow, h.hx4]; norm_num
  refine ⟨?_, ?_, hB, hA⟩
  · intro hmem
    exact absurd (hB 1 hmem) (by rw [orderOf_one]; norm_num)
  · intro hmem
    exact absurd (hB (x ^ 2) hmem) (by rw [hx2]; norm_num)

end Work.BrauerSuzuki.Q8
