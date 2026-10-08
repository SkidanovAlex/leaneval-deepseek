import Mathlib
import Submission.Work.ThmF.ChV3.Step16ChainTail
import Submission.Work.ThmF.ChV3.NearFieldExp

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF17.AppXI.Defs` — the App. XI interface of `ThmF17`

App. XI Prop. 1 and Prop. 2 are the three remaining *proved-once* inputs of the §3 chain
(`NearFieldAppXIProp`, `AppXIProp2`, `NearFieldFieldProp`, `ChV3/NearFieldExp.lean`,
`ChV3/AppXI.lean`).  BS pass 17 item D5 observed that one conjunct of `NearFieldFieldProp` — the
injectivity of `act : Σ → Aut F` — is *not* an App. XI fact: it is `Σ ⊓ C_G(C_Q(P)) = 1`, i.e.
step (7) of the chain, and is recovered from the direct step-(7) crux
`sig_inf_centralizer_CQ_eq_bot_of_comm`.

This module fixes the interface:

* `NearFieldAppXIPropPlus` (App. III (2) + App. XI Prop. 1 *without* the exponent clause: the
  honest statement, with `[R,R] ≤ N` as the only extra clause);
* `NearFieldAppXIPropPlus.toShadow` (the delivered `NearFieldAppXIProp`);
* `NearFieldFieldPropNI` (`NearFieldFieldProp` minus `Function.Injective act`);
* `fixP` (the fixed-point set of `P` on `Ω = G ⧸ H`).

The producers live in the sibling modules of `Submission/Work/ThmF17/AppXI/`; the assembly is
`Work.ThmF17.Closed.thmF_appXI_closed`.

All statements are verbatim `_design17/ThmF17_AppXI.lean` (`Design17.XI`), namespace `Work.ThmF17.AppXI`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section
open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF17.AppXI

open Work.ThmF.ChV3 Work.ThmF

/-- The fixed points of `P` on `Ω = G ⧸ H`. -/
def fixP {G : Type} [Group G] (H P : Subgroup G) : Set (G ⧸ H) := {ω | ∀ x ∈ P, x • ω = ω}

/-- The step-(2) shadow plus `[R,R] ≤ N` (what App. III (2) actually gives). -/
def NearFieldAppXIPropPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H Q : Subgroup G) (t s r : G) (P : Subgroup G),
    CtxF H Q t s r P →
    ∃ (m : ℕ) (R N : Subgroup G), N = Ker H Q P t ∧
      1 ≤ m ∧ (orderOf (s * t)).Prime ∧ N ≤ R ∧
      R ≤ Subgroup.centralizer (P : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (N : Set G) ∧
      Nat.card R = Nat.card N * orderOf (s * t) ^ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m ∧
      (∀ x ∈ R, x ∉ N → ∀ y ∈ CQ Q P, y * x * y⁻¹ * x⁻¹ ∈ N → y = 1) ∧
      (∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ N)

theorem NearFieldAppXIPropPlus.toShadow (h : NearFieldAppXIPropPlus) : NearFieldAppXIProp := by
  intro G _ _ H Q t s r P c
  obtain ⟨m, R, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := h G H Q t s r P c
  exact ⟨m, R, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- `NearFieldFieldProp` minus `Function.Injective act` (the genuine App. XI Prop. 1 (2)b content). -/
def NearFieldFieldPropNI : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} {m : ℕ},
    CtxF H Q t s r P →
    1 ≤ m →
    Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m →
    IsMulCommutative ↥(CQ Q P) →
    ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (_ : CharP F (orderOf (s * t))) (_ : Fact (orderOf (s * t)).Prime)
      (act : ↥(Sig H t P) →* (F ≃+* F)),
      Nat.card F = orderOf (s * t) ^ m ∧
      (∀ w : ↥(Sig H t P), w ≠ 1 →
        Nat.card (Function.fixedPoints (act w)) =
          Nat.card ↥(CQ Q P ⊓ Subgroup.centralizer ({(w : G)} : Set G)) + 1)

end Work.ThmF17.AppXI

#print axioms Work.ThmF17.AppXI.NearFieldAppXIPropPlus.toShadow
