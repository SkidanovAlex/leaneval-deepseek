import Mathlib
import Submission.Work.Frobenius.Complement.exists_elementaryAbelian_card_prime_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An element of order `p` outside a central subgroup of order `p`

This file proves `Work.Frobenius.Complement.exists_orderOf_ne_of_quotient`: if `G` is a finite
`p`-group with `p ≠ 2`, `N ≤ Z(G)` has order `p`, and the quotient `G ⧸ N` has two distinct
subgroups of order `p`, then `G` has an element of order `p` not lying in `N`.

The heart of the argument is the following.  Let `Q ≤ G ⧸ N` be an elementary abelian subgroup of
order `p²` (which exists by `exists_elementaryAbelian_card_prime_sq`, since `G ⧸ N` is a `p`-group
with two distinct subgroups of order `p`), and let `M ≤ G` be its preimage.  Then `M ⧸ N` is
elementary abelian, so the derived subgroup of `M` lies in `N` and the `p`-th power of every
element of `M` lies in `N`.  In particular `M` has nilpotency class at most two, and since `p` is
odd the map `x ↦ x ^ p` is a homomorphism `M →* M` (`pow_mul_eq_of_commutator_mem_center`), with
image contained in `N` and kernel equal to `N` (as soon as there are no elements of order `p`
outside `N`).  Noether's first isomorphism theorem then forces `|M : N| ≤ p`, contradicting
`|M : N| = p²`.
-/

namespace Work.Frobenius.Complement

open scoped commutatorElement

/-- In a group of nilpotency class at most two, the `n`-th power of a product is given by

`(x * y) ^ n = ⁅y, x⁆ ^ (n.choose 2) * x ^ n * y ^ n`.

The only ingredient needed is that the commutator `⁅y, x⁆` is central. -/
theorem pow_mul_eq_of_commutator_mem_center {G : Type*} [Group G] {x y : G}
    (hc : ⁅y, x⁆ ∈ Subgroup.center G) (n : ℕ) :
    (x * y) ^ n = ⁅y, x⁆ ^ (n.choose 2) * x ^ n * y ^ n := by
  have hcy : Commute y ⁅y, x⁆ := Subgroup.mem_center_iff.mp hc y
  have hcx : Commute x ⁅y, x⁆ := Subgroup.mem_center_iff.mp hc x
  have hyx : y * x = ⁅y, x⁆ * (x * y) := by rw [commutatorElement_def]; group
  have hk : ∀ k : ℕ, y ^ k * x = ⁅y, x⁆ ^ k * (x * y ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * x
          = y * (y ^ k * x) := by rw [pow_succ']; group
        _ = y * (⁅y, x⁆ ^ k * (x * y ^ k)) := by rw [ih]
        _ = (y * ⁅y, x⁆ ^ k) * (x * y ^ k) := by group
        _ = (⁅y, x⁆ ^ k * y) * (x * y ^ k) := by rw [(hcy.pow_right k).eq]
        _ = ⁅y, x⁆ ^ k * (y * (x * y ^ k)) := by group
        _ = ⁅y, x⁆ ^ k * (y * x * y ^ k) := by group
        _ = ⁅y, x⁆ ^ k * ((⁅y, x⁆ * (x * y)) * y ^ k) := by rw [hyx]
        _ = ⁅y, x⁆ ^ k * (⁅y, x⁆ * (x * (y * y ^ k))) := by group
        _ = ⁅y, x⁆ ^ (k + 1) * (x * y ^ (k + 1)) := by rw [pow_succ, pow_succ']; group
  induction n with
  | zero => simp
  | succ n ih =>
    calc (x * y) ^ (n + 1)
        = (x * y) ^ n * (x * y) := by rw [pow_succ]
      _ = ⁅y, x⁆ ^ (n.choose 2) * x ^ n * y ^ n * (x * y) := by rw [ih]
      _ = ⁅y, x⁆ ^ (n.choose 2) * x ^ n * (y ^ n * (x * y)) := by group
      _ = ⁅y, x⁆ ^ (n.choose 2) * x ^ n * (y ^ n * x * y) := by group
      _ = ⁅y, x⁆ ^ (n.choose 2) * x ^ n * ((⁅y, x⁆ ^ n * (x * y ^ n)) * y) := by rw [hk]
      _ = ⁅y, x⁆ ^ (n.choose 2) * (x ^ n * ⁅y, x⁆ ^ n) * ((x * y ^ n) * y) := by group
      _ = ⁅y, x⁆ ^ (n.choose 2) * (⁅y, x⁆ ^ n * x ^ n) * ((x * y ^ n) * y) := by
            rw [((hcx.pow_left n).pow_right n).eq]
      _ = (⁅y, x⁆ ^ (n.choose 2) * ⁅y, x⁆ ^ n) * (x ^ n * ((x * y ^ n) * y)) := by group
      _ = ⁅y, x⁆ ^ (n.choose 2 + n) * (x ^ (n + 1) * y ^ (n + 1)) := by
            rw [← pow_add, pow_succ, pow_succ']; group
      _ = ⁅y, x⁆ ^ (n.choose 2 + n) * x ^ (n + 1) * y ^ (n + 1) := by group
      _ = ⁅y, x⁆ ^ ((n + 1).choose 2) * x ^ (n + 1) * y ^ (n + 1) := by
            rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm (n.choose 2) n]

/-- If `G` is a finite group of nilpotency class at most two, `N ≤ Z(G)` has order `p` (`p` an odd
prime), `G ⧸ N` is abelian of exponent dividing `p` (`⁅⊤, ⊤⁆ ≤ N` and `x ^ p ∈ N` for all `x`),
`|G : N| ≥ p²`, and no element of order `p` lies outside `N`, then we reach a contradiction.

Indeed the map `x ↦ x ^ p` is a homomorphism with image at most `N` and kernel exactly `N`, whence
`|G : N| = |G : ker| ≤ |N| = p`, contradicting `|G : N| ≥ p²`. -/
theorem false_of_class_two_of_no_order_p_outside {M : Type*} [Group M] [Finite M]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Subgroup M) (hN : Nat.card N = p) (hNc : N ≤ Subgroup.center M)
    (hder : ⁅(⊤ : Subgroup M), ⊤⁆ ≤ N) (hexp : ∀ x : M, x ^ p ∈ N)
    (hindex : p ^ 2 ≤ N.index)
    (hall : ∀ w : M, orderOf w = p → w ∈ N) : False := by
  have h2p : 2 < p := by have := hp.two_le; omega
  have hdvd : p ∣ p.choose 2 := hp.dvd_choose_self (by norm_num) h2p
  have hpow : ∀ x y : M, (x * y) ^ p = x ^ p * y ^ p := by
    intro x y
    have hmem : ⁅y, x⁆ ∈ N :=
      hder (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) trivial trivial)
    have hc : ⁅y, x⁆ ∈ Subgroup.center M := hNc hmem
    rw [pow_mul_eq_of_commutator_mem_center hc p]
    have hord : orderOf ⁅y, x⁆ ∣ p := hN ▸ Subgroup.orderOf_dvd_natCard N hmem
    have hord2 : orderOf ⁅y, x⁆ ∣ p.choose 2 := hord.trans hdvd
    rw [orderOf_dvd_iff_pow_eq_one.mp hord2, one_mul]
  let φ : M →* M := { toFun := fun x => x ^ p, map_one' := one_pow p, map_mul' := hpow }
  have hrange : φ.range ≤ N := by rintro x ⟨y, rfl⟩; exact hexp y
  have hker : φ.ker = N := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      change x ^ p = 1 at hx
      have : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx
      rcases (Nat.dvd_prime hp).mp this with h1 | hp'
      · rw [orderOf_eq_one_iff.mp h1]; exact N.one_mem
      · exact hall x hp'
    · intro x hx
      rw [MonoidHom.mem_ker]
      change x ^ p = 1
      exact orderOf_dvd_iff_pow_eq_one.mp (hN ▸ Subgroup.orderOf_dvd_natCard N hx)
  have hiso := QuotientGroup.quotientKerEquivRange φ
  have hcard : Nat.card (M ⧸ φ.ker) ≤ p := by
    rw [Nat.card_congr hiso.toEquiv]
    calc Nat.card φ.range ≤ Nat.card N :=
          Nat.card_le_card_of_injective (fun x : φ.range => (⟨x.1, hrange x.2⟩ : N))
            (by intro a b h; exact Subtype.ext (congrArg (fun z : N => (z : M)) h))
      _ = p := hN
  have hidx : N.index ≤ p := by
    rw [Subgroup.index_eq_card, ← hker]; exact hcard
  have : p ^ 2 ≤ p := le_trans hindex hidx
  nlinarith [hp.two_le]

lemma exists_orderOf_ne_of_quotient {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hG : IsPGroup p G) (N : Subgroup G) [N.Normal] (hN : Nat.card N = p) (hNc : N ≤ Subgroup.center G)
    (h : ∃ Q₁ Q₂ : Subgroup (G ⧸ N), Nat.card Q₁ = p ∧ Nat.card Q₂ = p ∧ Q₁ ≠ Q₂) :
    ∃ w : G, orderOf w = p ∧ w ∉ N := by
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hQne⟩ := h
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  have hH : IsPGroup p (G ⧸ N) := hG.to_quotient N
  obtain ⟨Q, hQcard, hQcomm, hQexp⟩ :=
    exists_elementaryAbelian_card_prime_sq hp hH hQ₁ hQ₂ hQne
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let M : Subgroup G := Q.comap π
  have hNM : N ≤ M := by
    intro n hn
    rw [Subgroup.mem_comap]
    have h1 : π n = 1 := by rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hn
    rw [h1]; exact Q.one_mem
  let f : M →* (G ⧸ N) := π.comp M.subtype
  have hfker : f.ker = N.subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : G)
  have hfrange : f.range = Q := by
    have h1 : Subgroup.map M.subtype ⊤ = M := by ext x; simp [Subgroup.mem_map]
    have h2 : Subgroup.map (π.comp M.subtype) ⊤ = Subgroup.map π (Subgroup.map M.subtype ⊤) :=
      (Subgroup.map_map ⊤ π M.subtype).symm
    rw [MonoidHom.range_eq_map, h2, h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Q
  have hder : ⁅(⊤ : Subgroup M), ⊤⁆ ≤ N.subgroupOf M := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    have hxQ : f x ∈ Q := by rw [← hfrange]; exact ⟨x, rfl⟩
    have hyQ : f y ∈ Q := by rw [← hfrange]; exact ⟨y, rfl⟩
    rw [← hfker, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (setLike_mul_comm hxQ hyQ)
  have hexp : ∀ x : M, x ^ p ∈ N.subgroupOf M := by
    intro x
    rw [← hfker, MonoidHom.mem_ker, map_pow]
    have hxQ : f x ∈ Q := by rw [← hfrange]; exact ⟨x, rfl⟩
    simpa using hQexp ⟨f x, hxQ⟩
  have hidx : (N.subgroupOf M).index = p ^ 2 := by
    rw [← hfker, Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hfrange, hQcard]
  have hcent : N.subgroupOf M ≤ Subgroup.center M := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hNc (Subgroup.mem_subgroupOf.mp hx)) (y : G))
  have hcardNsub : Nat.card (N.subgroupOf M) = p := by
    have he : N.subgroupOf M ≃* N := by
      have h1 := Subgroup.equivMapOfInjective (N.subgroupOf M) M.subtype M.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNM] at h1
      exact h1
    rw [Nat.card_congr he.toEquiv, hN]
  exact false_of_class_two_of_no_order_p_outside hp hp2 (N.subgroupOf M) hcardNsub hcent hder hexp
    hidx.ge (fun w hw => Subgroup.mem_subgroupOf.mpr (hno (w : G) ((Subgroup.orderOf_coe w).trans hw)))

end Work.Frobenius.Complement
