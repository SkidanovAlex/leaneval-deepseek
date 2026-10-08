import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.Prove.Sig_sup_P_le_normalizer_CQ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.Sig_nontrivial_on_RP` — §3 leaf: `Σ` acts faithfully on `R/P`

Peterfalvi II Ch. V §3, step (11) (p. 252), uses the source's "`Σ` acts non-trivially on
`R/P ≅ F`".  In this workspace the conclusion is *not* taken from the near-field identification of
`C_G(P)/N` (App. XI Prop. 1 (2)b), but derived from the two hypotheses of the chain that are
available: the fixed-point-freeness clause `h15.hfpf` of step (2) and the vanishing of the kernel
`h7 : Ker H Q P t = P` of step (7).  Concretely:

* `P ≤ Ker H Q P t ≤ R` (`h7`), so `P ⊴` ... and, since `R ≤ C_G(P)`, `P` is central in `R`;
  the hypothesis `h` says `σ` acts trivially on `R/P`;
* `σ ∈ Σ = W ⊓ C_G(P) ≤ C_G(P) ≤ N_G(R)`, so `σ` acts on `R` by conjugation and fixes `P`
  pointwise;
* the main computation (`conj_action_compat`) shows that if `σ` acts trivially on `R/P`, then
  `σ y σ⁻¹ y⁻¹` acts trivially on `R/P` for every `y ∈ C_Q(P)`;
* `C_Q(P)` acts fixed-point-freely on `(R/P)^#` (`h15.hfpf`, since `P = Ker`) and `R ≠ P`
  (`|R| = |P| · f ^ m` with `f = o(st)` prime and `m ≥ 1`), so the only element of `C_Q(P)` acting
  trivially on `R/P` is `1`; hence `σ` centralises `C_Q(P)`;
* thus `σ ∈ D ⊓ C_G(C_Q(P)) ⊓ C_G(P) = Ker H Q P t = P`, while `σ ∈ Σ ≤ W` and
  `W ⊓ P = ⊥` (step (1)), so `σ = 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

/-- Elementary shuffle: if `a` and `b` commute then conjugating `b * w` by `a` moves `b` out. -/
theorem mul_conj_eq_of_mul_comm {G : Type*} [Group G] {a b w : G} (h : a * b = b * a) :
    a * (b * w) * a⁻¹ = b * (a * w * a⁻¹) := by
  rw [← mul_assoc a b w, h, mul_assoc b a w, mul_assoc b (a * w) a⁻¹]

/-- **The action of `Σ` on `R/P` and on `C_Q(P)` are compatible.**

Let `R, P ≤ G`, `y ∈ N_G(R) ∩ C_G(P)`, `σ ∈ N_G(R) ∩ C_G(P)`, and suppose that `σ` acts
trivially on `R/P` (the hypothesis `hσ`).  Then `σ y σ⁻¹ y⁻¹` acts trivially on `R/P`: for
`x ∈ R` the conjugate of `x` by `σ y σ⁻¹ y⁻¹` is `x` times an element of `P`. -/
theorem conj_action_compat {G : Type*} [Group G] {R P : Subgroup G} {σ y x : G}
    (hσ : ∀ u ∈ R, σ * u * σ⁻¹ * u⁻¹ ∈ P)
    (hyC : y ∈ Subgroup.centralizer (P : Set G))
    (hyN : y ∈ Subgroup.normalizer (R : Set G))
    (hσN : σ ∈ Subgroup.normalizer (R : Set G))
    (hσC : σ ∈ Subgroup.centralizer (P : Set G))
    (hx : x ∈ R) :
    ∃ p ∈ P, σ * y * σ⁻¹ * y⁻¹ * x * (σ * y * σ⁻¹ * y⁻¹)⁻¹ = p * x := by
  classical
  -- `u := y⁻¹ x y ∈ R`
  set u : G := y⁻¹ * x * y with hudef
  have hu : u ∈ R := by
    rw [hudef]
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (R : Set G)).inv_mem hyN) x).mp hx
  -- `q := σ⁻¹ u σ u⁻¹ ∈ P`, so that `σ⁻¹ u σ = q * u`
  have hσN' : σ⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normalizer (R : Set G)).inv_mem hσN
  have hσu : σ⁻¹ * u * σ ∈ R := by
    simpa using (Subgroup.mem_normalizer_iff.mp hσN' u).mp hu
  have hqP : σ⁻¹ * u * σ * u⁻¹ ∈ P := by
    have h1 := hσ (σ⁻¹ * u * σ) hσu
    have h2 : σ * (σ⁻¹ * u * σ) * σ⁻¹ * (σ⁻¹ * u * σ)⁻¹ = u * σ⁻¹ * u⁻¹ * σ := by group
    rw [h2] at h1
    have h3 : σ⁻¹ * u * σ * u⁻¹ = (u * σ⁻¹ * u⁻¹ * σ)⁻¹ := by group
    rw [h3]
    exact P.inv_mem h1
  have hqu : σ⁻¹ * u * σ = (σ⁻¹ * u * σ * u⁻¹) * u := by group
  -- the commuting facts
  have hyq : y * (σ⁻¹ * u * σ * u⁻¹) = (σ⁻¹ * u * σ * u⁻¹) * y :=
    (Subgroup.mem_centralizer_iff.mp hyC _ hqP).symm
  have hσq : σ * (σ⁻¹ * u * σ * u⁻¹) = (σ⁻¹ * u * σ * u⁻¹) * σ :=
    (Subgroup.mem_centralizer_iff.mp hσC _ hqP).symm
  have hyu : y * u * y⁻¹ = x := by rw [hudef]; group
  refine ⟨(σ⁻¹ * u * σ * u⁻¹) * (σ * x * σ⁻¹ * x⁻¹), P.mul_mem hqP (hσ x hx), ?_⟩
  set q : G := σ⁻¹ * u * σ * u⁻¹ with hqdef
  calc σ * y * σ⁻¹ * y⁻¹ * x * (σ * y * σ⁻¹ * y⁻¹)⁻¹
      = σ * (y * (σ⁻¹ * u * σ) * y⁻¹) * σ⁻¹ := by rw [hudef]; group
    _ = σ * (y * (q * u) * y⁻¹) * σ⁻¹ := by rw [hqu]
    _ = σ * (q * (y * u * y⁻¹)) * σ⁻¹ := by
          rw [mul_conj_eq_of_mul_comm hyq]
    _ = q * (σ * (y * u * y⁻¹) * σ⁻¹) := by
          rw [mul_conj_eq_of_mul_comm hσq]
    _ = q * (σ * x * σ⁻¹) := by rw [hyu]
    _ = (q * (σ * x * σ⁻¹ * x⁻¹)) * x := by group

/-- `P ≤ R` in the chain, since `P = Ker H Q P t ≤ R` by step (7) and step (2). -/
theorem P_le_R_of_ker_eq {G : Type} [Group G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) (h7 : Work.ThmF.ChV3.Ker H Q P t = P) :
    P ≤ h15.R := fun x hx => h15.hNR (h7.symm ▸ hx)

/-- The lemma of §3 step (11): `Σ = C_W(P)` acts faithfully on `R/P`.

For `σ ∈ Σ` with `σ ≠ 1` there is `x ∈ R` with `σ x σ⁻¹ x⁻¹ ∉ P`. -/
theorem Sig_nontrivial_on_RP {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) :
    ∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 → ∃ x ∈ h15.R, σ * x * σ⁻¹ * x⁻¹ ∉ P := by
  classical
  intro σ hσSig hσne
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  -- `hcon : ∀ x, x ∈ R → σ * x * σ⁻¹ * x⁻¹ ∈ P`
  have hSigW : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hSigC : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  have hSigD : Work.ThmF.ChV3.Sig H t P ≤ twoPoint H t :=
    (hSigW.trans (Work.ThmF.W_le_centD H t)).trans (Work.ThmF.centD_le_twoPoint t)
  have hSigNR : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (h15.R : Set G) :=
    hSigC.trans h15.hRn
  have hSigNCQ : Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer (Work.ThmF.ChV3.CQ Q P : Set G) :=
    le_sup_left.trans (Sig_sup_P_le_normalizer_CQ c)
  have hσW : σ ∈ Work.ThmF.W H t := hSigW hσSig
  have hσC : σ ∈ Subgroup.centralizer (P : Set G) := hSigC hσSig
  have hσD : σ ∈ twoPoint H t := hSigD hσSig
  have hσNR : σ ∈ Subgroup.normalizer (h15.R : Set G) := hSigNR hσSig
  have hσNCQ : σ ∈ Subgroup.normalizer (Work.ThmF.ChV3.CQ Q P : Set G) := hSigNCQ hσSig
  -- ## `R ≠ P`, so there is `x ∈ R ∖ P`
  have hcardR' : Nat.card h15.R = Nat.card P * orderOf (s * t) ^ h15.m := by
    rw [h15.hcardR, h7]
  have hpow2 : 2 ≤ orderOf (s * t) ^ h15.m := by
    have h1 : orderOf (s * t) ^ 1 ≤ orderOf (s * t) ^ h15.m :=
      Nat.pow_le_pow_right (Nat.Prime.pos h15.hf) h15.hm
    have h2 : orderOf (s * t) ≤ orderOf (s * t) ^ h15.m := by simpa using h1
    exact h15.hf.two_le.trans h2
  have hlt : Nat.card P < Nat.card h15.R := by
    rw [hcardR']
    calc Nat.card P = Nat.card P * 1 := (Nat.mul_one _).symm
      _ < Nat.card P * 2 := Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.card_pos (α := P))
      _ ≤ Nat.card P * orderOf (s * t) ^ h15.m := Nat.mul_le_mul_left _ hpow2
  obtain ⟨x0, hx0R, hx0P⟩ : ∃ x ∈ h15.R, x ∉ P := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    have hdvd : Nat.card h15.R ∣ Nat.card P := Subgroup.card_dvd_of_le hc
    have hle : Nat.card h15.R ≤ Nat.card P := Nat.le_of_dvd (Nat.card_pos (α := P)) hdvd
    omega
  -- ## `σ` centralises `C_Q(P)`
  have hcent : σ ∈ Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyC : y ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hy).2
    have hyN : y ∈ Subgroup.normalizer (h15.R : Set G) := h15.hRn hyC
    have hz : σ * y * σ⁻¹ ∈ Work.ThmF.ChV3.CQ Q P :=
      (Subgroup.mem_normalizer_iff.mp hσNCQ y).mp hy
    obtain ⟨p, hpP, hp⟩ := conj_action_compat hcon hyC hyN hσNR hσC hx0R
    have hwCQ : σ * y * σ⁻¹ * y⁻¹ ∈ Work.ThmF.ChV3.CQ Q P :=
      (Work.ThmF.ChV3.CQ Q P).mul_mem hz ((Work.ThmF.ChV3.CQ Q P).inv_mem hy)
    have hwP : σ * y * σ⁻¹ * y⁻¹ * x0 * (σ * y * σ⁻¹ * y⁻¹)⁻¹ * x0⁻¹ ∈
        Work.ThmF.ChV3.Ker H Q P t := by
      rw [h7]
      have hp' : σ * y * σ⁻¹ * y⁻¹ * x0 * (σ * y * σ⁻¹ * y⁻¹)⁻¹ = p * x0 := hp
      have : σ * y * σ⁻¹ * y⁻¹ * x0 * (σ * y * σ⁻¹ * y⁻¹)⁻¹ * x0⁻¹ = p := by
        rw [hp']; group
      rw [this]
      exact hpP
    have hw1 : σ * y * σ⁻¹ * y⁻¹ = 1 :=
      h15.hfpf x0 hx0R (by rw [h7]; exact hx0P) (σ * y * σ⁻¹ * y⁻¹) hwCQ hwP
    calc y * σ = (σ * y * σ⁻¹ * y⁻¹) * (y * σ) := by rw [hw1, one_mul]
      _ = σ * y := by group
  -- ## hence `σ ∈ Ker = P`, and `Σ ⊓ P = ⊥`
  have hσKer : σ ∈ Work.ThmF.ChV3.Ker H Q P t :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨hσD, hcent⟩, hσC⟩
  have hσP : σ ∈ P := by rw [← h7]; exact hσKer
  have hbot : σ ∈ Work.ThmF.W H t ⊓ P := ⟨hσW, hσP⟩
  rw [h15.hWP] at hbot
  exact hσne (Subgroup.mem_bot.mp hbot)

end Work.ThmF.ChV3.Prove
