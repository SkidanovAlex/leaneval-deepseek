import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV12.Lemma5Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Step16Defs` — vocabulary of the §3 second half (steps (11)–(17))

The lead's pass-16 design (`Submission/Work/NOTES_LEAD_bs_pass16.md`,
`ThmF/_design16/ThmF16.lean`) fixes the objects and the standing hypotheses of steps (11)–(17):

* `Z1 s t = ⟨st⟩`, the cyclic group `Z₁` of (13)–(17);
* `Cst s t = C_G(st)` (the Sylow 3-subgroup `R₂` of (14));
* `Lsub H s t = ⟨Q₀,K,t⟩ ∩ C_G(st)` (the cyclic `L` of (15));
* `Asub H P s t = Z₁ P Σ` (the elementary abelian `A` of (15)–(17));
* `StronglyReal`, `Step11Out` (step (11)'s output), `Case101`/`Case102` (step (10)'s dichotomy).

This module contains the vocabulary only; the leaves of the design live in
`Submission/Work/ThmF/Prove/` (one file per leaf), and the step assemblies in
`ChV3/Step16Step12.lean`, `ChV3/Step16Step17.lean` and `ChV3/Step16ChainTail.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3

open Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-- The conjugate `g A g⁻¹`, in the form used by `HallWielandtProp`. -/
abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

/-- `C_G(X)`. -/
abbrev CG (X : Subgroup G) : Subgroup G := Subgroup.centralizer (X : Set G)

/-- `N_G(X)`. -/
abbrev NG (X : Subgroup G) : Subgroup G := Subgroup.normalizer (X : Set G)

/-- `Z₁ = ⟨st⟩` (p. 252). -/
abbrev Z1 (s t : G) : Subgroup G := Subgroup.zpowers (s * t)

/-- `C_G(st)`; it is the Sylow 3-subgroup `R₂` of step (14). -/
abbrev Cst (s t : G) : Subgroup G := Subgroup.centralizer ({s * t} : Set G)

/-- `L = ⟨Q₀, K, t⟩ ∩ C_G(st)` (step (15)). -/
abbrev Lsub (H : Subgroup G) (s t : G) : Subgroup G := Lemma5.X5 H t ⊓ Cst s t

/-- `A = Z₁ P Σ` (steps (16), (17)). -/
abbrev Asub (H P : Subgroup G) (s t : G) : Subgroup G := Z1 s t ⊔ P ⊔ Sig H t P

/-- Strongly real (p. 246): a product of two involutions (the form of `ChV12.lemma4`). -/
def StronglyReal (x : G) : Prop := ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x

/-- Step (11)'s output: the conclusion of `Prove/step11Structure` together with `R` abelian
(the part of (11) that `step11Structure` takes as its hypothesis `hcomm`). -/
structure Step11Out (H Q : Subgroup G) (t : G) (P R T : Subgroup G) : Prop where
  comm : IsMulCommutative ↥R
  TP : T ⊓ P = ⊥
  TPR : T ⊔ P = R
  Tn : CQ Q P ⊔ Sig H t P ≤ Subgroup.normalizer (T : Set G)
  reg : ∀ A B : Subgroup G, A ≤ R → B ≤ R → Nat.card A = Nat.card P → Nat.card B = Nat.card P →
    ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
    ∃! y : ↥(CQ Q P), A.map (MulAut.conj (y : G)).toMonoidHom = B

/-- Case (10-1) of step (10) (first disjunct of `Prove.step10Wrapper`'s conclusion). -/
def Case101 (H : Subgroup G) (t : G) (P : Subgroup G) (m : ℕ) : Prop :=
  ¬ Nat.card P ∣ Nat.card ↥(Sig H t P) ∧
    pPart (Nat.card P) (Nat.card G) = Nat.card P ^ (m + 2)

/-- Case (10-2) of step (10), with `f = p = 3` (step (9)/(10)) and `W` cyclic (§2 Lemma 6,
`ChV12.lemma6`, the same call that gives `|W| ∈ {3, 9}` to `step10Wrapper`'s `hcase2`). -/
structure Case102 (H Q : Subgroup G) (t s : G) (P : Subgroup G) : Prop where
  p3 : Nat.card P = 3
  sig3 : Nat.card ↥(Sig H t P) = 3
  cq8 : Nat.card ↥(CQ Q P) = 8
  W39 : Nat.card ↥(W H t) = 3 ∨ Nat.card ↥(W H t) = 9
  G3 : pPart 3 (Nat.card G) = 3 ^ 4 * Nat.card ↥(W H t)
  f3 : orderOf (s * t) = 3
  Wcyc : IsCyclic ↥(W H t)

end Work.ThmF.ChV3
