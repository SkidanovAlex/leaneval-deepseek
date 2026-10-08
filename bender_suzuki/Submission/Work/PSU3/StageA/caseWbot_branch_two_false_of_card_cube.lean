import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.Higman.Main
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.lemma2cHig
import Submission.Work.PSU3.StageA.BranchTwo.ncard_modEq_fixed_of_prime_normalizer
import Submission.Work.PSU3.StageA.BranchTwo.sq_mem_Q0sub
import Submission.Work.PSU3.StageA.BranchTwo.ncard_sqFibre_eq
import Submission.Work.PSU3.StageA.BranchTwo.ncard_sqFibre_inf_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Branch (ii) of Ch. V §2 Lemma 2c is impossible when `|Q| = |Q0sub H|³`

Peterfalvi II, Ch. V §2 Lemma 2 c) trichotomy together with Ch. VI §1: in the `W = ⊥` branch
with `Q` non-abelian and `|Q| = q³` (`q = |Q0sub H|`), the Suzuki case (ii)
(`orderOf (s * t) = 5`, `C = Q ⊓ C_G(P)` non-abelian of order `ℓ²`,
`x² = y² ⇒ x y⁻¹ ∈ Q0sub H` for `x, y ∈ C`) cannot occur.

## The argument

Write `q = |Q0sub H|`, `C = Q ⊓ C_G(P)`, `C₀ = Q0sub H ⊓ C_G(P)`, `ℓ = |C₀|`, `p = |P|`.

* `Q` is a Suzuki `2`-group of order `q³` with `Ω₁(Q) = Z(Q) = Q0sub H` (Higman's Theorem 1
  plus `caseWbot_center_subgroupOf`); in particular `x² ∈ Q0sub H` for `x ∈ Q`
  (`Work.PSU3.StageA.BranchTwo.sq_mem_Q0sub`).
* **Step 1.** `P` normalises `Q0sub H` (conjugation by `H` permutes the involutions of `H`,
  `Work.ThmF.ChV12.conj_mem_Q0sub`), and its fixed points there are exactly `C₀`.  Since `|P| = p`
  is prime, every orbit of `P` on `Q0sub H` has size `1` or `p`, whence
  `q ≡ ℓ (mod p)` (`ncard_modEq_fixed_of_prime_normalizer`).
* **Step 2.** For `s ∈ Q0sub H \ {1}` let `F_s = {x ∈ Q | x² = s}`.  The group `K = J(D,t)` acts
  on `Q` by conjugation and `(k x k⁻¹)² = k x² k⁻¹`, so it permutes the fibres `F_s` according to
  its transitive action on `Q0sub H♯ = Inv H` (`Work.ThmF.L5.Kset_regular`).  Hence all fibres
  over `Q0sub H♯` have the same size `c`, and `q³ = |Q| = q + (q-1)·c` gives `c = q(q+1)`
  (`ncard_sqFibre_eq`).
* **Step 3.** `s` is centralised by `P` (the structure identity, `centD_eq_centralizer_s`), so
  `F_s` is `P`-invariant and `|F_s| ≡ |F_s ⊓ C_G(P)| (mod p)`.  On the other hand `x ↦ x²` maps
  `C` onto `C₀` with all fibres of size `ℓ` — this is exactly the content of the "equal squares"
  clause together with `|C| = ℓ²` — so `|F_s ⊓ C_G(P)| = ℓ` (`ncard_sqFibre_inf_eq`).
* Combining: `q(q+1) = |F_s| ≡ ℓ ≡ q (mod p)`, hence `p ∣ q²`, so `p ∣ q`, so `p ∣ |Q| = 2ⁿ` and
  `p = 2`, contradicting the oddness of `p` (`P ≤ twoPoint H t` has odd order).

None of this uses `hW : W H t = ⊥`, so the lemma is stated (and proved) without it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageA

theorem caseWbot_branch_two_false_of_card_cube {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp) {s r : G}
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3)
    {P : Subgroup G} (hP : P ≤ Submission.Blueprint.centD H t) (hp : (Nat.card P).Prime) :
    ¬ (orderOf (s * t) = 5 ∧
      ¬ Submission.Blueprint.IsAbelianSubgroup (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) =
          Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) ^ 2 ∧
      ∀ x ∈ Q ⊓ Subgroup.centralizer (P : Set G),
        ∀ y ∈ Q ⊓ Subgroup.centralizer (P : Set G),
          x ^ 2 = y ^ 2 → x * y⁻¹ ∈ Work.ThmF.Q0sub H) := by
  classical
  intro ⟨h5, hnabC, hcardC, heqsq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- conjugation fixes `x` iff it commutes with `x`
  have conj_eq_iff : ∀ a x : G, a * x * a⁻¹ = x ↔ a * x = x * a := by
    intro a x
    constructor
    · intro h
      calc a * x = (a * x * a⁻¹) * a := by group
        _ = x * a := by rw [h]
    · intro h
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hconjsq : ∀ a b : G, (a * b * a⁻¹) ^ 2 = a * b ^ 2 * a⁻¹ := by
    intro a b
    calc (a * b * a⁻¹) ^ 2 = ((MulAut.conj a) b) ^ 2 := by rw [MulAut.conj_apply]
      _ = (MulAut.conj a) (b ^ 2) := (map_pow (MulAut.conj a) b 2).symm
      _ = a * b ^ 2 * a⁻¹ := by rw [MulAut.conj_apply]
  -- ## `P` lies in `twoPoint H t`, whose order is odd, so `|P| = p ≠ 2`
  have hP_D : P ≤ Submission.Blueprint.twoPoint H t :=
    hP.trans (show Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t from
      inf_le_left)
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    hS.split.stronglyEmbedded.2.2 t hS.split.not_mem
  have hPodd : Odd (Nat.card P) := hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hP_D)
  have hpne2 : Nat.card P ≠ 2 := by
    intro h2
    obtain ⟨k, hk⟩ := hPodd
    omega
  -- ## The structure identity: `s` is centralised by `P`
  have hPI : Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    Work.PSU3.StageA.centD_eq_centralizer_s hS hs hs2 hr hsr
  have hscP : s ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have hpV : p ∈ Submission.Blueprint.centD H t := hP hpP
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hPI ▸ hpV)).2
  have hPH : ∀ p ∈ P, p ∈ H := fun p hpP => (Subgroup.mem_inf.mp (hP_D hpP)).1
  have hpq : ∀ p ∈ P, ∀ x ∈ Q, p * x * p⁻¹ ∈ Q := by
    intro p hpP x hx
    exact (Subgroup.mem_normalizer_iff.mp (hS.split.normal (hPH p hpP)) x).mp hx
  -- ## Step 1: `|Q0sub H| ≡ |Q0sub H ⊓ C_G(P)| (mod |P|)`
  have hNQ0 : ∀ p ∈ P, ∀ x ∈ (Work.ThmF.Q0sub H : Set G),
      p * x * p⁻¹ ∈ (Work.ThmF.Q0sub H : Set G) :=
    fun p hpP x hx => Work.ThmF.ChV12.conj_mem_Q0sub (hPH p hpP) hx
  have hfixQ0 : (Work.ThmF.Q0sub H : Set G) ∩ {x : G | ∀ p ∈ P, p * x * p⁻¹ = x}
      = ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ, hfx⟩ := hx
      exact ⟨hxQ, Subgroup.mem_centralizer_iff.mpr
        (fun p hpP => (conj_eq_iff p x).mp (hfx p hpP))⟩
    · intro hx
      obtain ⟨hxQ, hxc⟩ := hx
      refine ⟨hxQ, fun p hpP => ?_⟩
      exact (conj_eq_iff p x).mpr ((Subgroup.mem_centralizer_iff.mp hxc) p hpP)
  have hQ0n : (Work.ThmF.Q0sub H : Set G).ncard = Nat.card ↥(Work.ThmF.Q0sub H) :=
    (Nat.card_coe_set_eq (Work.ThmF.Q0sub H : Set G)).symm
  have hC0n : ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G).ncard
      = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) :=
    (Nat.card_coe_set_eq _).symm
  have hCmod : Nat.card ↥(Work.ThmF.Q0sub H) ≡
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) [MOD Nat.card P] := by
    have h := Work.PSU3.StageA.BranchTwo.ncard_modEq_fixed_of_prime_normalizer hp
      (Work.ThmF.Q0sub H : Set G) hNQ0
    rw [hfixQ0] at h
    rwa [hQ0n, hC0n] at h
  -- ## Step 2: the square fibre over `s`
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs2
    omega
  have hFs : {x : G | x ∈ Q ∧ x ^ 2 = s}.ncard =
      Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) + 1) :=
    Work.PSU3.StageA.BranchTwo.ncard_sqFibre_eq hS hC4 hFT hnab hcard hs hs2 hs1
  have hFsinf : {x : G | x ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ x ^ 2 = s}.ncard =
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) :=
    Work.PSU3.StageA.BranchTwo.ncard_sqFibre_inf_eq hS hC4 hFT hnab hs hs2 hs1 hP hp hscP
      hcardC heqsq
  have hNF : ∀ p ∈ P, ∀ x ∈ {x : G | x ∈ Q ∧ x ^ 2 = s},
      p * x * p⁻¹ ∈ {x : G | x ∈ Q ∧ x ^ 2 = s} := by
    intro p hpP x hx
    obtain ⟨hxQ, hx2⟩ := hx
    refine ⟨hpq p hpP x hxQ, ?_⟩
    calc (p * x * p⁻¹) ^ 2 = p * x ^ 2 * p⁻¹ := hconjsq p x
      _ = p * s * p⁻¹ := by rw [hx2]
      _ = s := (conj_eq_iff p s).mpr ((Subgroup.mem_centralizer_iff.mp hscP) p hpP)
  have hFixF : ({x : G | x ∈ Q ∧ x ^ 2 = s} ∩ {x : G | ∀ p ∈ P, p * x * p⁻¹ = x}).ncard =
      {x : G | x ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ x ^ 2 = s}.ncard := by
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨⟨hxQ, hx2⟩, hfx⟩ := hx
      refine ⟨⟨hxQ, ?_⟩, hx2⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun p hpP => (conj_eq_iff p x).mp (hfx p hpP))
    · intro hx
      obtain ⟨⟨hxQ, hxc⟩, hx2⟩ := hx
      refine ⟨⟨hxQ, hx2⟩, fun p hpP => ?_⟩
      exact (conj_eq_iff p x).mpr ((Subgroup.mem_centralizer_iff.mp hxc) p hpP)
  have hFmod : {x : G | x ∈ Q ∧ x ^ 2 = s}.ncard ≡
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) [MOD Nat.card P] := by
    have h := Work.PSU3.StageA.BranchTwo.ncard_modEq_fixed_of_prime_normalizer hp
      ({x : G | x ∈ Q ∧ x ^ 2 = s}) hNF
    rw [hFixF, hFsinf] at h
    exact h
  -- ## Step 3: arithmetic — `p ∣ q²`, hence `p ∣ |Q| = 2ⁿ`, hence `p = 2`
  have h2c : Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) + 1) ≡
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) [MOD Nat.card P] := by
    rw [← hFs]
    exact hFmod
  have h3 : Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H) ≡ 0
      [MOD Nat.card P] := by
    have h4 : Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) + 1) ≡
        Nat.card ↥(Work.ThmF.Q0sub H) [MOD Nat.card P] := h2c.trans hCmod.symm
    have h4' : Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H)
        + Nat.card ↥(Work.ThmF.Q0sub H) ≡ 0 + Nat.card ↥(Work.ThmF.Q0sub H) [MOD Nat.card P] := by
      simpa [Nat.mul_add, Nat.mul_one] using h4
    exact Nat.ModEq.add_right_cancel' (Nat.card ↥(Work.ThmF.Q0sub H)) h4'
  have hp_dvd_q2 : Nat.card P ∣ Nat.card ↥(Work.ThmF.Q0sub H) ^ 2 := by
    simpa [pow_two] using Nat.modEq_zero_iff_dvd.mp h3
  have hp_dvd_q : Nat.card P ∣ Nat.card ↥(Work.ThmF.Q0sub H) := hp.dvd_of_dvd_pow hp_dvd_q2
  have hp_dvd_Q : Nat.card P ∣ Nat.card Q :=
    hp_dvd_q.trans (Subgroup.card_dvd_of_le (Work.ThmF.ChV12.Q0sub_le_Q hS.split))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS.two
  have hp_dvd_two : Nat.card P ∣ 2 := by
    have h : Nat.card P ∣ 2 ^ n := by
      rw [← hn]
      exact hp_dvd_Q
    exact hp.dvd_of_dvd_pow h
  have hpeq : Nat.card P = 2 := by
    have hle : Nat.card P ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_two
    have hge : 2 ≤ Nat.card P := hp.two_le
    omega
  exact hpne2 hpeq

end Work.PSU3.StageA
