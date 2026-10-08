import Mathlib
import Submission.Work.PSU3.StageA.caseWbot_setup
import Submission.Work.PSU3.StageA.sq_fiber_card_of_card_sq
import Submission.Work.PSU3.StageA.prime_dvd_card_sq_fiber

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-!
# `Work.PSU3.StageA.caseWbot_branch_one_false_of_card_square`

Branch (i) of Peterfalvi II, Ch. V §2 Lemma 2 c is **impossible** when `|Q| = q²`
(`q = |Q0sub H|`), for `Q` non-abelian.

In the notation of `lemma2cHig` (`C = Q ⊓ C_G(P)`, `ℓ = |Q0sub H ⊓ C_G(P)|`), the first
alternative reads

  `orderOf (s * t) = 3`, `C` abelian, `|C| = ℓ`,

and the claim is that it cannot hold.  (The extra hypothesis `|Q| = q²` is carried by the
caller: in the assembly `caseWbot_nonabelian_card_order` the dichotomy `|Q| = q² ∨ q³` is
dispatched by the three branch exclusions, and this file is the `q²`-case of branch (i).)

## The argument

Nothing about `orderOf (s * t) = 3` is used: the exclusion is a counting argument.

1. **`C ≤ Q0sub H`.**  Since `Q0sub H ≤ Q` we have `Q0sub H ⊓ C_G(P) ≤ C`, and the hypothesis
   `|C| = ℓ = |Q0sub H ⊓ C_G(P)|` upgrades this to the equality `C = Q0sub H ⊓ C_G(P)`.
   Hence `C_Q(P) = C` lies in `Z := Q0sub H` — equivalently, `P` acts fixed point freely on
   `Q ∖ Z`.

2. **The squaring fibre over `s` has `q` elements.**  `s` is the distinguished involution,
   so `s ∈ Q0sub H = Z` and `P` centralises `s`; `q = |Z| = 2ⁿ` and `Z = Z(Q)` with
   `Q/Z(Q)` elementary abelian (`Q` is a Suzuki `2`-group of order `q²` by Ch. V §1
   Corollary of Prop. 2 and Higman's Theorem 1, `caseWbot_setup`).  The fibre
   `F = {x ∈ Q | x² = s}` therefore has exactly `|Z| = q` elements
   (`sq_fiber_card_of_card_sq`).

3. **`|P|` divides `|F|`.**  Conjugation by `P ≤ H = N_G(Q)` preserves `F`
   (`(gxg⁻¹)² = g x² g⁻¹ = s` because `P ≤ V = centD H t = C_D(s)`), and a fixed point would
   lie in `C_G(P) ∩ Q = C ≤ Z`, where `x² = 1` — contradicting `x² = s ≠ 1`.  Hence `P` acts
   on the finite set `F` with all orbits of size `|P|`, so `|P| ∣ |F| = q`
   (`prime_dvd_card_sq_fiber`).

4. **Contradiction.**  `P ≤ V ≤ D` has odd order, so `|P| = p` is an odd prime; but
   `p ∣ q = 2ⁿ` forces `p = 2`.
-/

theorem caseWbot_branch_one_false_of_card_square {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} {s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2)
    {P : Subgroup G} (hP : P ≤ Submission.Blueprint.centD H t) (hp : (Nat.card P).Prime) :
    ¬ (orderOf (s * t) = 3 ∧
      Submission.Blueprint.IsAbelianSubgroup (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) =
        Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))) := by
  classical
  rintro ⟨hst3, hCab, hcardC⟩
  set C : Subgroup G := Q ⊓ Subgroup.centralizer (P : Set G) with hCdef
  set Z : Subgroup G := Work.ThmF.Q0sub H with hZdef
  -- ## 1. `C = Q0sub H ⊓ C_G(P)`, whence `C ≤ Q0sub H`
  have hcardC' : Nat.card ↥C = Nat.card ↥(Z ⊓ Subgroup.centralizer (P : Set G)) := by
    rw [hCdef, hZdef]; exact hcardC
  have hQ0_le_Q : Z ≤ Q := by rw [hZdef]; exact Q0sub_le_Q hS.split
  have hZle : Z ⊓ Subgroup.centralizer (P : Set G) ≤ C := by
    rw [hCdef]; exact inf_le_inf_right _ hQ0_le_Q
  have hCeq : Z ⊓ Subgroup.centralizer (P : Set G) = C :=
    Subgroup.eq_of_le_of_card_ge hZle hcardC'.le
  have hCle : C ≤ Z := by rw [← hCeq]; exact inf_le_left
  -- `s ∈ C` and `s ≠ 1`
  have hsZ : s ∈ Z := by
    rw [hZdef]
    exact Work.ThmF.Q0_le_Q0sub H
      (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le hs, hs2⟩)
  have hsCG : s ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxV : x ∈ Submission.Blueprint.centD H t := hP hx
    rw [Work.PSU3.StageA.centD_eq_centralizer_s hS hs hs2 hr hsr] at hxV
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxV).2
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  -- ## 2. the Suzuki structure of `Q`, and the squaring fibre over `s`
  have hSuzB : Submission.Blueprint.IsSuzukiTwoGroup ↥Q := caseWbot_isSuzukiTwoGroup hS hFT hC4 hnab
  have hSuz : Work.Higman.IsSuzuki2Grp ↥Q :=
    (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp (P := ↥Q)).mp hSuzB |>.some
  have hZc : Subgroup.center ↥Q = Z.subgroupOf Q := by
    rw [hZdef]; exact caseWbot_center_subgroupOf hS hFT hC4 hnab
  have hcq : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥Z := by
    rw [hZc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0_le_Q).toEquiv
  have hcardQ : Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2 := by
    rw [hcq]; exact hcard
  have hsz : (⟨s, hs⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [hZc, Subgroup.mem_subgroupOf]; exact hsZ
  have hsz1 : (⟨s, hs⟩ : ↥Q) ≠ 1 := fun h1 => hs1 (congrArg Subtype.val h1)
  have hfib : Nat.card {x : ↥Q // x ^ 2 = (⟨s, hs⟩ : ↥Q)} = Nat.card ↥Z := by
    rw [sq_fiber_card_of_card_sq Work.Higman.higmanProp hSuz hcardQ hsz hsz1, hcq]
  -- ## 3. `P` acts on the fibre with no fixed point
  have hPQ : ∀ g ∈ P, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
    intro g hg x hx
    have hgD : g ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp (hP hg)).1
    have hgH : g ∈ H := (Subgroup.mem_inf.mp hgD).1
    exact (Subgroup.mem_normalizer_iff.mp (hS.split.normal hgH) x).mp hx
  have hPs : ∀ g ∈ P, g * s * g⁻¹ = s := by
    intro g hg
    have hc : g * s = s * g := by
      have hxV : g ∈ Submission.Blueprint.centD H t := hP hg
      rw [Work.PSU3.StageA.centD_eq_centralizer_s hS hs hs2 hr hsr] at hxV
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxV).2
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hcommH : ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u :=
    Work.ThmF.ChV12.involutions_of_H_commute hS.situation hC4 H Q t hS.split
  have hQ0sq : ∀ x ∈ Z, x * x = 1 := by
    intro x hx
    rw [hZdef] at hx
    exact (Work.ThmF.ChV12.Q0sub_elementary H hcommH).1 x hx
  have hfix : ∀ x ∈ Q, x * x = s → x ∈ Subgroup.centralizer (P : Set G) → False := by
    intro x hxQ hxsqx hxC
    have hxZ : x ∈ Z := hCle (by rw [hCdef]; exact ⟨hxQ, hxC⟩)
    have h1 := hQ0sq x hxZ
    rw [hxsqx] at h1
    exact hs1 h1
  have hdiv : Nat.card P ∣ Nat.card {x : ↥Q // x ^ 2 = (⟨s, hs⟩ : ↥Q)} :=
    prime_dvd_card_sq_fiber hs hp hs2 hPQ hPs hfix
  -- ## 4. `|P| ∣ q = 2ⁿ` with `|P|` an odd prime is impossible
  obtain ⟨n, hn⟩ := caseWbot_Q0sub_card_pow_two (H := H) (Q := Q) (t := t) hS hC4
  have hZeq : Nat.card ↥Z = 2 ^ n := by rw [hZdef]; exact hn
  have hpdvd : Nat.card P ∣ Nat.card ↥Z := hfib ▸ hdiv
  have hpodd : Odd (Nat.card P) :=
    (Work.ThmF.split_odd_card_twoPoint hS.split).of_dvd_nat
      (Subgroup.card_dvd_of_le
        (show P ≤ Submission.Blueprint.twoPoint H t from
          fun x hx => (Subgroup.mem_inf.mp (hP hx)).1))
  have hpdvd2 : Nat.card P ∣ 2 := hp.dvd_of_dvd_pow (hZeq ▸ hpdvd)
  rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd2 with h1 | h2
  · exact absurd h1 hp.ne_one
  · rw [h2] at hpodd
    exact absurd hpodd (by rintro ⟨k, hk⟩; omega)

end Work.PSU3.StageA
