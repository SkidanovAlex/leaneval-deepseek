import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.maximal_abelian_invariant_ge_phi

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

open LeanEval.GroupTheory.Defs

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- The centre of a Suzuki 2-group is `ξ`-invariant (it is characteristic). -/
theorem map_center_xi_sq (h : IsSuzuki2Grp P) :
    (Subgroup.center P).map (h.xi : MulAut P).toMonoidHom = Subgroup.center P :=
  (Subgroup.characteristic_iff_map_eq.mp
    (inferInstance : (Subgroup.center P).Characteristic)) h.xi

/-- **Assembly step.**  Let `A` be a maximal normal abelian `ξ`-invariant subgroup of the Suzuki
2-group `P`, containing `Ω₁(P)` and with `exp A ≤ 4` (Higman's Lemma 9, existential form
`maximal_abelian_invariant_ge_phi`).  If `|P| = |Z(P)| ^ 2` then `A` is the centre.

Indeed, by Higman's Lemma 1, `|A| = |Ω₁| ^ a` with `a ≤ 2` (the exponent bound), and
`|Z(P)| = |Ω₁| ^ f`; maximality gives `Z(P) ≤ A` (as `A ⊔ Z(P)` is again a normal abelian
`ξ`-invariant subgroup containing `A`), so `f ≤ a ≤ 2`.  The only consistent values of the pair
`(a,f)` give `|A| = |Z(P)|`: for `a = 2`, `f = 1` would force `|A| = |P|`, so `A = P` would be
abelian, contradicting `h.noncomm`. -/
theorem eq_center_of_lemma9 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2)
    {A : Subgroup P} (hAn : A.Normal)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAmax : ∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A)
    (hOmegaA : Work.Higman.omega1 P ≤ A) (hpow4 : Work.Higman.powSub A 4 = ⊥) :
    A = Subgroup.center P := by
  classical
  -- The centre is contained in `A` (maximality; `A ⊔ Z(P)` is again `ξ`-invariant abelian normal).
  have hZA : Subgroup.center P ≤ A :=
    center_le_of_maximal h ⟨hAn, hAxi, hAab⟩
      (fun B hB hAB => hAmax B hB.1 hB.2.1 hB.2.2 hAB)
  -- Numerics.  `q = |Ω₁(P)|`, `|A| = q ^ a`, `|Z(P)| = q ^ f`.
  set q : ℕ := Nat.card ↥(Work.Higman.omega1 P) with hq
  have hq4 : 4 ≤ q := by rw [hq]; exact h.omega1_card_ge_four
  obtain ⟨f, _hfE, _hfA, hf3⟩ := higman_lemma1 h
    (fun x hx y hy => (Subgroup.mem_center_iff.mp hx y).symm) (map_center_xi_sq h)
  have hZcard : Nat.card ↥(Subgroup.center P) = q ^ f := by
    rw [hf3, inf_eq_right.mpr h.omega1_le_center, hq]
  obtain ⟨a, _haE, haA, ha3⟩ := higman_lemma1 h hAab hAxi
  have hAcard : Nat.card ↥A = q ^ a := by
    rw [ha3, inf_eq_right.mpr hOmegaA, hq]
  -- `a ≤ 2` because `exp A ≤ 4`.
  have ha2 : a ≤ 2 := by
    obtain ⟨xA, hxAA, hxAord⟩ := haA
    have hxA4 : xA ^ 4 = 1 := by
      have hmem := Work.Higman.pow_mem_powSub (A := A) (n := 4) hxAA
      rw [hpow4] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hdvd : 2 ^ a ∣ 4 := by
      rw [← hxAord]
      exact orderOf_dvd_iff_pow_eq_one.mpr hxA4
    have hle : 2 ^ a ≤ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact Nat.le_of_dvd (by norm_num) hdvd
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  -- `1 ≤ a` and `1 ≤ f ≤ a`.
  have ha1 : 1 ≤ a := by
    have h0 : Nat.card ↥(Work.Higman.omega1 P) ≤ Nat.card ↥A := Subgroup.card_le_of_le hOmegaA
    rw [hAcard, ← hq] at h0
    have hle : q ^ 1 ≤ q ^ a := by simpa using h0
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < q)).mp hle
  have hf1 : 1 ≤ f := by
    have h0 : Nat.card ↥(Work.Higman.omega1 P) ≤ Nat.card ↥(Subgroup.center P) :=
      Subgroup.card_le_of_le h.omega1_le_center
    rw [hZcard, ← hq] at h0
    have hle : q ^ 1 ≤ q ^ f := by simpa using h0
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < q)).mp hle
  have hfa : f ≤ a := by
    have h0 : Nat.card ↥(Subgroup.center P) ≤ Nat.card ↥A := Subgroup.card_le_of_le hZA
    rw [hZcard, hAcard] at h0
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < q)).mp h0
  -- `|P| = q ^ (2 * f)`.
  have hPcard : Nat.card P = q ^ (2 * f) := by
    rw [hcard, hZcard, ← pow_mul, Nat.mul_comm]
  -- `|A| = |Z(P)|`.
  have hcardAZ : Nat.card ↥A = Nat.card ↥(Subgroup.center P) := by
    have ha12 : a = 1 ∨ a = 2 := by omega
    have hf12 : f = 1 ∨ f = 2 := by omega
    rcases ha12 with ha | ha
    · have hf : f = 1 := by omega
      simp [hAcard, hZcard, ha, hf]
    · rcases hf12 with hf | hf
      · exfalso
        -- Then `|A| = q ^ 2 = |P|`, so `A = ⊤` is abelian, contradicting `h.noncomm`.
        have hAtop : A = ⊤ := by
          refine Subgroup.eq_top_of_card_eq (H := A) ?_
          simp [hAcard, hPcard, ha, hf]
        obtain ⟨u, v, huv⟩ := h.noncomm
        exact huv (hAab u (by rw [hAtop]; trivial) v (by rw [hAtop]; trivial))
      · simp [hAcard, hZcard, ha, hf]
  exact (Subgroup.eq_of_le_of_card_ge hZA (le_of_eq hcardAZ)).symm

/-- **Class-two route.**  If `[P,P] ≤ Ω₁(P)` (Higman's theorem) then every square of the Suzuki
2-group is central: every commutator is a central involution, so in class `2`
`⁅x ^ 2, y⁆ = ⁅x, y⁆ ^ 2 = 1`. -/
theorem sq_mem_center_of_commutator_le {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P) (x : P) :
    x ^ 2 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  -- `⁅x, y⁆ ∈ Ω₁(P)`, hence is a central involution.
  have hmem : ⁅x, y⁆ ∈ Work.Higman.omega1 P :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hcen : ⁅x, y⁆ ∈ Subgroup.center P := h.omega1_le_center hmem
  have hsq : ⁅x, y⁆ ^ 2 = 1 := h.mem_omega1.mp hmem
  -- In class `2`, `⁅x ^ 2, y⁆ = ⁅x, y⁆ ^ 2 = 1`, so `x ^ 2` commutes with `y`.
  have hc : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hcen x
  have key : ⁅x ^ 2, y⁆ = 1 := by
    rw [← Commute.commutatorElement_pow_left hc 2, hsq]
  exact (commutatorElement_eq_one_iff_mul_comm (g₁ := x ^ 2) (g₂ := y)).mp key |>.symm

/-- If `|P| = |Z(P)| ^ 2` in a Suzuki 2-group then every square is central (Higman 1963,
Theorem 1 in the order-`q ^ 2` case; the argument is Higman's Lemma 9 in its existential form
`maximal_abelian_invariant_ge_phi`, which produces a normal abelian `ξ`-invariant subgroup `A`
containing `Ω₁(P)`, `[P,P]` and all squares, with `exp A ≤ 4`; `eq_center_of_lemma9` shows
`A = Z(P)`). -/
theorem sq_mem_center_of_card_eq_center_sq {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2) :
    ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  obtain ⟨A, hAn, hAxi, hAab, hAmax, hOmegaA, _hcomm, hsqA, hpow4⟩ :=
    maximal_abelian_invariant_ge_phi h
  have hAZ : A = Subgroup.center P :=
    eq_center_of_lemma9 h hcard hAn hAxi hAab hAmax hOmegaA hpow4
  intro x
  rw [← hAZ]
  exact hsqA x

end Work.Higman
