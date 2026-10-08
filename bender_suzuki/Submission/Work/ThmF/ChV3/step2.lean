import Submission.Work.ThmF.ChV3.NearField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.step2` — Peterfalvi II Ch. V §3 step (2)

The source's step (2) reads (p. 248):

> **(2)** a) `(C_G(P), C_H(P)) ∈ 𝓕` and its kernel is `N = C_D(C_Q(P)) ∩ C(P)`.  b) There is a
> near-field `F` with `C_G(P)/N = (F ⋊ C_Q(P)) ⋊ Σ`, `C_Q(P) ≅ F^*`, `Σ = \overline{C_W(P)}`.

Only the *group-theoretic and numerical shadow* of (2) is used by the rest of §3, and that shadow
is exactly the conclusion of the external input `ChV3.NearFieldAppXIProp` (`ChV3/NearField.lean`,
App. XI Prop. 1 with App. III).  This file unpacks it into the form the later steps consume:

* `N = Ker H Q P t = D ⊓ C_G(C_Q(P)) ⊓ C_G(P)`;
* `1 ≤ m` and `f = orderOf (s * t)` is prime (the characteristic of `F`);
* the preimage `R` of `F`: `N ≤ R ≤ C_G(P) ≤ N_G(R)`;
* `|R| = |N| · f^m` and `|C_Q(P)| + 1 = f^m` (so `|F| = f^m`);
* `C_Q(P) ≅ F^*` acts fixed-point-freely on `(R/N)^#`.

The near-field itself (and thereby App. XI itself) is *not* built; see `NOTES.md` §4.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- **Step (2)**: the shadow of App. XI Prop. 1 for `(C_G(P), C_H(P))`, unpacked from the named
input `NearFieldAppXIProp`. -/
theorem step2 {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hNF : NearFieldAppXIProp) (c : CtxF H Q t s r P) :
    ∃ (m : ℕ) (R : Subgroup G), 1 ≤ m ∧ (orderOf (s * t)).Prime ∧
      Ker H Q P t ≤ R ∧ R ≤ Subgroup.centralizer (P : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      Nat.card R = Nat.card ↥(Ker H Q P t) * orderOf (s * t) ^ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m ∧
      ∀ x ∈ R, x ∉ Ker H Q P t → ∀ y ∈ CQ Q P, y * x * y⁻¹ * x⁻¹ ∈ Ker H Q P t → y = 1 := by
  obtain ⟨m, R, N, hN, hm, hp, hNR, hRc, hRn, _hNn, hcard, hcq, hfpf⟩ := hNF G H Q t s r P c
  rw [hN] at hNR hcard hfpf
  exact ⟨m, R, hm, hp, hNR, hRc, hRn, hcard, hcq, hfpf⟩

end Work.ThmF.ChV3
