import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.Frobenius.Complement.basicGroup_of_commute
import Submission.Work.Frobenius.Complement.isCyclic_of_commutative_unique_order_p
import Submission.Work.Frobenius.Complement.exists_orderOf_ne_of_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# A finite `p`-group (`p` odd) with no `(ZMod p × ZMod p)` subgroup is cyclic

This file proves `Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup`, the statement
that a finite `p`-group for odd `p` which contains no subgroup isomorphic to `ZMod p × ZMod p`
(i.e. no elementary abelian subgroup of order `p²`) is cyclic.

The mathematical content is Burnside's theorem: for odd `p` a finite `p`-group is cyclic if and
only if it has a unique subgroup of order `p`.  The proof is organised as follows.

* `Work.Frobenius.Complement.eq_of_card_eq_prime_of_no_basicGroup`: if a finite `p`-group has no
  subgroup isomorphic to `ZMod p × ZMod p`, then it has at most one subgroup of order `p`.
  Two distinct subgroups of order `p` would give two commuting independent elements of order
  `p` (`basicGroup_of_commute`), or two non-commuting ones, whence a central element of order
  `p` commuting with one of them — either way a subgroup isomorphic to `ZMod p × ZMod p`.
* `Work.Frobenius.Complement.le_center_of_unique_order_p`: the unique subgroup of order `p` lies
  in the centre (a nontrivial `p`-group has nontrivial centre, which must contain it).
* `Work.Frobenius.Complement.isCyclic_of_isPGroup_of_unique_order_p`: Burnside's theorem for odd
  `p`, by strong induction on `|G|`.
-/

namespace Work.Frobenius.Complement

open scoped Classical Pointwise
open Subgroup

noncomputable section

universe u

variable {p : ℕ}

/-- In a nontrivial finite `p`-group there is an element of order `p`. -/
theorem exists_orderOf_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) [Nontrivial G] : ∃ x : G, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn, hcard⟩ := hG.nontrivial_iff_card.mp (inferInstance : Nontrivial G)
  exact exists_prime_orderOf_dvd_card' p (by rw [hcard]; exact dvd_pow_self p hn.ne')

/-- If `G` is a finite `p`-group having a *unique* subgroup `N` of order `p`, then `N` is
contained in the centre of `G`.

Indeed the centre of the nontrivial `p`-group `G` is nontrivial, hence contains an element `z`
of order `p`; the subgroup `⟨z⟩` has order `p` and so must coincide with `N`. -/
theorem le_center_of_unique_order_p {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) (N : Subgroup G) (hN : Nat.card N = p)
    (huniq : ∀ Q : Subgroup G, Nat.card Q = p → Q = N) : N ≤ Subgroup.center G := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (G := ↥N) (by rw [hN])
  have hzG : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hz]
  have hzgen : Subgroup.zpowers (z : G) = N := huniq _ (by rw [Nat.card_zpowers, hzG])
  have hz1 : (z : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzG
    exact hp.ne_one hzG.symm
  haveI : Nontrivial G := ⟨⟨(z : G), 1, hz1⟩⟩
  haveI : Nontrivial ↥(Subgroup.center G) := hG.center_nontrivial
  obtain ⟨w, hw⟩ := exists_orderOf_eq_prime hp (hG.to_subgroup (Subgroup.center G))
  have hwG : orderOf (w : G) = p := by rw [Subgroup.orderOf_coe, hw]
  have hwgen : Subgroup.zpowers (w : G) = N := huniq _ (by rw [Nat.card_zpowers, hwG])
  rw [← hwgen]
  exact Subgroup.zpowers_le.mpr w.2

/-- If a finite `p`-group has no subgroup isomorphic to `ZMod p × ZMod p`, then any two of its
subgroups of cardinality `p` coincide. -/
theorem eq_of_card_eq_prime_of_no_basicGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hG : IsPGroup p G)
    (h : ∀ Q : Subgroup G, ¬ Nonempty (Q ≃* Multiplicative (ZMod p × ZMod p)))
    {A B : Subgroup G} (hA : Nat.card A = p) (hB : Nat.card B = p) : A = B := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hAB
  -- `A ≠ B` gives an element `x ∈ A \ B` and an element `y ∈ B` of order `p`.
  obtain ⟨x, hxA, hxB⟩ : ∃ x, x ∈ A ∧ x ∉ B := by
    by_contra hcon
    push_neg at hcon
    exact hAB (Subgroup.eq_of_le_of_card_ge (fun x hx => hcon x hx) (le_of_eq (hB.trans hA.symm)))
  obtain ⟨y, hyB, hy1⟩ : ∃ y, y ∈ B ∧ y ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hbot : B = ⊥ := Subgroup.eq_bot_iff_forall B |>.mpr hcon
    rw [hbot, Subgroup.card_bot] at hB
    exact hp.ne_one hB.symm
  have hx1 : x ≠ 1 := fun h1 => hxB (h1 ▸ B.one_mem)
  have hxord : orderOf x = p := by
    have hdv := Subgroup.orderOf_dvd_natCard A hxA
    rw [hA] at hdv
    rcases (Nat.dvd_prime hp).mp hdv with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hyord : orderOf y = p := by
    have hdv := Subgroup.orderOf_dvd_natCard B hyB
    rw [hB] at hdv
    rcases (Nat.dvd_prime hp).mp hdv with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hxyz : x ∉ Subgroup.zpowers y :=
    fun hmem => hxB ((Subgroup.zpowers_le.mpr hyB) hmem)
  by_cases hcomm : x * y = y * x
  · obtain ⟨Q, hQ⟩ := basicGroup_of_commute hp hxord hyord hcomm hxyz
    exact (h Q) hQ
  · -- `x` and `y` do not commute: pass to `H = ⟨x, y⟩` and use a central element of order `p`.
    set H : Subgroup G := Subgroup.closure {x, y} with hH
    have hxH : x ∈ H := Subgroup.subset_closure (by simp)
    have hyH : y ∈ H := Subgroup.subset_closure (by simp)
    haveI : Nontrivial ↥H :=
      ⟨⟨⟨x, hxH⟩, ⟨1, H.one_mem⟩, by simp [hx1]⟩⟩
    haveI : Nontrivial ↥(Subgroup.center ↥H) := (hG.to_subgroup H).center_nontrivial
    obtain ⟨z, hzord⟩ :=
      exists_orderOf_eq_prime hp ((hG.to_subgroup H).to_subgroup (Subgroup.center ↥H))
    set xH : ↥H := ⟨x, hxH⟩ with hxHdef
    set yH : ↥H := ⟨y, hyH⟩ with hyHdef
    have hxHord : orderOf xH = p := by rw [← Subgroup.orderOf_coe]; exact hxord
    have hyHord : orderOf yH = p := by rw [← Subgroup.orderOf_coe]; exact hyord
    have hzHord : orderOf (z : ↥H) = p := by rw [Subgroup.orderOf_coe, hzord]
    -- `xH` and `yH` do not commute
    have hxyH : xH * yH ≠ yH * xH := by
      intro hcon
      exact hcomm (Subtype.ext_iff.mp hcon)
    have hnotboth : ¬ (xH ∈ Subgroup.center ↥H ∧ yH ∈ Subgroup.center ↥H) := fun ⟨h1, h2⟩ =>
      hxyH (Subgroup.mem_center_iff.mp h1 yH).symm
    -- transporting a witness from `↥H` back to `G`
    have key : ∀ u v : ↥H, orderOf u = p → orderOf v = p → u * v = v * u →
        u ∉ Subgroup.zpowers v →
        ∃ Q : Subgroup G, Nonempty (Q ≃* Multiplicative (ZMod p × ZMod p)) := by
      intro u v hu hv huv huvne
      obtain ⟨Q, hQ⟩ := basicGroup_of_commute hp hu hv huv huvne
      exact ⟨Q.map H.subtype,
        ⟨(Q.equivMapOfInjective H.subtype H.subtype_injective).symm.trans hQ.some⟩⟩
    rcases em (xH ∈ Subgroup.center ↥H) with hxc | hxc
    · have hyc : yH ∉ Subgroup.center ↥H := fun hyc => hnotboth ⟨hxc, hyc⟩
      obtain ⟨Q, hQ⟩ := key yH (z : ↥H) hyHord hzHord
        (Subgroup.mem_center_iff.mp z.2 yH)
        (fun hmem => hyc ((Subgroup.zpowers_le.mpr z.2) hmem))
      exact (h Q) hQ
    · obtain ⟨Q, hQ⟩ := key xH (z : ↥H) hxHord hzHord
        (Subgroup.mem_center_iff.mp z.2 xH)
        (fun hmem => hxc ((Subgroup.zpowers_le.mpr z.2) hmem))
      exact (h Q) hQ

/-- Auxiliary form of Burnside's theorem for odd `p`, with the universe level of `G` made
explicit so that the induction hypothesis can be applied to the quotient `G ⧸ N`
(an auxiliary is necessary because the induction hypothesis must be re-quantified over types). -/
theorem isCyclic_of_isPGroup_of_unique_order_p_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ n, ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → IsPGroup p G →
      ∀ N : Subgroup G, Nat.card N = p →
      (∀ Q : Subgroup G, Nat.card Q = p → Q = N) → IsCyclic G := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ hcard hG N hN huniq
    have hNc : N ≤ Subgroup.center G := le_center_of_unique_order_p hp hG N hN huniq
    haveI : N.Normal := Subgroup.normal_of_le_center hNc
    by_cases hsmall : Nat.card G ≤ p
    · -- `G` has order `1` or `p`
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p)).mp hG
      have hj1 : j ≤ 1 := by
        by_contra hlt
        push_neg at hlt
        have h2 : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos hlt
        rw [← hj] at h2
        have : p ^ 2 ≤ p := h2.trans hsmall
        nlinarith [hp.two_le]
      have hdvd : Nat.card G ∣ p := by
        rw [hj]
        interval_cases j <;> simp
      exact isCyclic_of_card_dvd_prime (α := G) hdvd
    · push_neg at hsmall
      have hidx : 0 < N.index := by
        rcases Nat.eq_zero_or_pos N.index with h | h
        · have hcard' : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index N
          rw [h, mul_zero] at hcard'
          omega
        · exact h
      have hlt : Nat.card (G ⧸ N) < n := by
        rw [← Subgroup.index_eq_card]
        have hcard' : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index N
        rw [hN] at hcard'
        nlinarith [hidx, hp.two_le, hcard']
      by_cases hQ : ∃ Q₁ Q₂ : Subgroup (G ⧸ N), Nat.card Q₁ = p ∧ Nat.card Q₂ = p ∧ Q₁ ≠ Q₂
      · -- `G ⧸ N` has two subgroups of order `p`: then `G` has a second one
        obtain ⟨w, hw⟩ := exists_orderOf_ne_of_quotient hp hp2 hG N hN hNc hQ
        exact absurd ((huniq (Subgroup.zpowers w) (by rw [Nat.card_zpowers, hw.1])) ▸
          Subgroup.mem_zpowers w) hw.2
      · -- `G ⧸ N` has a unique subgroup of order `p`, hence (induction) is cyclic
        push_neg at hQ
        haveI : Nontrivial (G ⧸ N) := by
          rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index_eq_card]
          have hcard' : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index N
          rw [hN] at hcard'
          nlinarith [hidx, hp.two_le, hcard', hsmall]
        obtain ⟨q, hq⟩ := exists_orderOf_eq_prime hp (hG.to_quotient N)
        have hM : Nat.card (Subgroup.zpowers q) = p := by rw [Nat.card_zpowers, hq]
        have huniqQ : ∀ Q : Subgroup (G ⧸ N), Nat.card Q = p → Q = Subgroup.zpowers q :=
          fun Q hQ' => hQ Q (Subgroup.zpowers q) hQ' hM
        have hGQ : IsPGroup p (G ⧸ N) := hG.to_quotient N
        have hcyc : IsCyclic (G ⧸ N) :=
          ih (Nat.card (G ⧸ N)) hlt (G ⧸ N) rfl hGQ (Subgroup.zpowers q) hM huniqQ
        haveI : IsCyclic (G ⧸ N) := hcyc
        have hcomm : IsMulCommutative G :=
          MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' N)
            (by rw [QuotientGroup.ker_mk']; exact hNc)
        exact isCyclic_of_commutative_unique_order_p hp hcomm hG N hN huniq

/-- **Burnside's theorem for odd `p`.** A finite `p`-group with a unique subgroup of order `p`
is cyclic. -/
theorem isCyclic_of_isPGroup_of_unique_order_p {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hG : IsPGroup p G) (N : Subgroup G) (hN : Nat.card N = p)
    (huniq : ∀ Q : Subgroup G, Nat.card Q = p → Q = N) : IsCyclic G :=
  isCyclic_of_isPGroup_of_unique_order_p_aux hp hp2 (Nat.card G) G rfl hG N hN huniq

theorem isPGroup_isCyclic_of_no_basicGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup p P)
    (h : ∀ Q : Subgroup P, ¬ Nonempty (Q ≃* Multiplicative (ZMod p × ZMod p))) :
    IsCyclic P := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases em (Subsingleton P) with htriv | htriv
  · exact isCyclic_of_subsingleton (α := P)
  · haveI : Nontrivial P := not_subsingleton_iff_nontrivial.mp htriv
    obtain ⟨x, hx⟩ := exists_orderOf_eq_prime hp hP
    have hN : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
    have huniq : ∀ Q : Subgroup P, Nat.card Q = p → Q = Subgroup.zpowers x :=
      fun Q hQ => eq_of_card_eq_prime_of_no_basicGroup hp hP h hQ hN
    exact isCyclic_of_isPGroup_of_unique_order_p hp hp2 hP (Subgroup.zpowers x) hN huniq

end

end Work.Frobenius.Complement
