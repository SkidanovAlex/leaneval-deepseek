import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerData
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausSuzuki.Q0sub_card_eq_center_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

/-!
Suzuki 1962, §8, p. 118 (second half): with `S` the Singer-cycle data inside
`X5 H t ≅ LF(2,q)` in the Zassenhaus split rank-one setting with `Q` a non-abelian `2`-group and
`σ = ρ`, and given `C_G(S.V) = S.V`, distinct `G`-conjugates of `S.V` meet trivially.

Route.  `|S.V| = |Q0sub H| + 1` is odd and `> 1` (`Q0sub_card_eq_center_card` +
`|twoPoint H t| + 1 = |Z(Q)|` shows `|Q0sub H| = |Z(Q)| = 2^m`, so `|S.V| = 2^m + 1`).
Suppose `1 ≠ x ∈ S.V ⊓ conj g S.V`.  Then `x` is an element of odd order `≠ 1`, so `x * x ≠ 1`,
and `x` is strongly real by `S.stronglyReal`; Proposition 14
(`Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real`, hypotheses `h.split`, `h.zass`,
`h.two`) makes `C_G(x)` **abelian**.  Both `S.V` and `conj g S.V` are abelian (cyclic) subgroups
containing `x`, so both are contained in `C_G(x)`; being subgroups of one abelian group they
commute elementwise, so `conj g S.V ≤ C_G(S.V) = S.V`, and comparing orders gives
`conj g S.V = S.V`, contradicting the hypothesis.
-/

/-- `|S.V|` is odd: `|S.V| = |Q0sub H| + 1 = (|twoPoint H t| + 1) + 1`, and `|twoPoint H t|`
is odd. -/
theorem singer_odd_card_V {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s)
    (S : Work.ZassenhausSuzuki.SingerCycle.Data G H t) :
    Odd (Nat.card ↥S.V) := by
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := Work.ThmF.split_odd_card_twoPoint h.split
  have hDinv : Nat.card ↥(twoPoint H t) = (involutions (Q : Set G)).ncard :=
    twoPoint_card_eq_involutions h.split h.zass h.two
  have hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = (involutions (H : Set G)).ncard + 1 :=
    Q0sub_card_eq_involutions_add_one h.split h.two
  have hInv : involutions (H : Set G) = involutions (Q : Set G) :=
    involutions_H_eq_involutions_Q h.split h.two
  have h1 : Nat.card ↥S.V = Nat.card ↥(twoPoint H t) + 2 := by
    rw [S.card_V, hQ0, hInv, ← hDinv]
  rw [h1]
  exact hDodd.add_even even_two

theorem singer_conj_inf_eq_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s)
    (S : Work.ZassenhausSuzuki.SingerCycle.Data G H t)
    (hcent : Subgroup.centralizer (S.V : Set G) = S.V) :
    ∀ g : G, Submission.Blueprint.conj g S.V ≠ S.V →
      S.V ⊓ Submission.Blueprint.conj g S.V = ⊥ := by
  have hOddV : Odd (Nat.card ↥S.V) := singer_odd_card_V h S
  haveI hcyc : IsCyclic ↥S.V := S.cyclic
  intro g hgne
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hxne
  have hxA : x ∈ S.V := (Subgroup.mem_inf.mp hx).1
  have hxB : x ∈ Submission.Blueprint.conj g S.V := (Subgroup.mem_inf.mp hx).2
  -- odd order of `x`, hence `x * x ≠ 1`
  have hoddx : Odd (orderOf x) := hOddV.of_dvd_nat (Subgroup.orderOf_dvd_natCard S.V hxA)
  have hxx : x * x ≠ 1 := by
    intro hsq
    have hdvd : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact hxne (orderOf_eq_one_iff.mp h1)
    · rw [h2] at hoddx
      obtain ⟨k, hk⟩ := hoddx
      omega
  -- `x` is strongly real, so `C_G(x)` is abelian (Suzuki Prop. 14)
  have hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x := S.stronglyReal x hxA
  have habelC : IsMulCommutative ↥(Subgroup.centralizer ({x} : Set G)) :=
    (Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real h.split h.zass h.two
      hxx hsr).1
  -- both `S.V` and `conj g S.V` lie in `C_G(x)`
  have hAcl : ∀ a ∈ S.V, a ∈ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (M := ↥S.V) ⟨a, ha⟩ ⟨x, hxA⟩)
  have hBcl : ∀ b ∈ Submission.Blueprint.conj g S.V, b ∈ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Submission.Blueprint.conj, Subgroup.mem_map] at hb
    obtain ⟨v, hv, rfl⟩ := hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Submission.Blueprint.conj, Subgroup.mem_map] at hxB
    obtain ⟨w, hw, hwx⟩ := hxB
    rw [← hwx]
    have hvw : v * w = w * v :=
      congrArg Subtype.val (mul_comm' (M := ↥S.V) ⟨v, hv⟩ ⟨w, hw⟩)
    have hmap : (MulAut.conj g).toMonoidHom (v * w) = (MulAut.conj g).toMonoidHom (w * v) :=
      congrArg (MulAut.conj g).toMonoidHom hvw
    rwa [map_mul, map_mul] at hmap
  -- hence `conj g S.V ≤ C_G(S.V) = S.V`
  have hBA : Submission.Blueprint.conj g S.V ≤ S.V := by
    intro b hb
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro a ha
    haveI := habelC
    exact congrArg Subtype.val (mul_comm' (M := ↥(Subgroup.centralizer ({x} : Set G)))
      ⟨a, hAcl a ha⟩ ⟨b, hBcl b hb⟩)
  -- and comparing orders gives equality
  have hcard : Nat.card ↥(Submission.Blueprint.conj g S.V) = Nat.card ↥S.V := by
    rw [Submission.Blueprint.conj]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (fun a b hab => MulEquiv.injective (MulAut.conj g) hab)
  exact hgne (Subgroup.eq_of_le_of_card_ge hBA (le_of_eq hcard.symm))

end Work.ZassenhausSuzuki
