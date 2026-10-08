import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.ChV3.AppXI
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Prove.step1
import Submission.Work.ThmF.Prove.step3
import Submission.Work.ThmF.Prove.step4
import Submission.Work.ThmF.Prove.step5
import Submission.Work.ThmF.ChV3.step2
import Submission.Work.ThmF.ChV12.prop1b
import Submission.Work.ThmF.ChV12.L6faith

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Chain15` — the composable part of the Ch. V §3 chain

Steps (1)–(5) of Peterfalvi II Ch. V §3 are proved on disk as separate theorems
(`Prove/step1`, `ChV3/step2`, `Prove/step3`, `Prove/step4`, `Prove/step5`).  Unlike (6) and (7),
they are *not* mutually dependent, so they compose: this module assembles their conclusions
into the single structure `Chain15` (step (3) is the arithmetic statement on the prime divisors
of `|O_{2'}(Q)|`, step (4) the order formula `|Q| = |C_Q(P)|^{|P|}`, step (5) the non-abelian
dichotomy `|C_Q(P)| = 8` and `O_{2'}(Q) = 1`).

Steps (6) and (7) are the ones the chain cannot yet continue through: `Prove/step6` needs
`Ker H Q P t = P` and `Prove/step7` needs (6)'s conclusion, so neither can be applied first.
See `NOTES.md` §8.2 for the precise blocker (the missing input is the near-field structure of
`C_G(P)/N`, App. XI Prop. 1).  This module therefore stops at step (5) and records the state
honestly rather than pretending to a chain that does not compose.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- The accumulated conclusions of §3 steps (1)–(5). -/
structure Chain15 (H Q : Subgroup G) (t s r : G) (P : Subgroup G) where
  /-- step (1): `W ⊓ P = ⊥` -/
  hWP : W H t ⊓ P = ⊥
  /-- step (1): `V = W ⋊ P` -/
  hV : W H t ⊔ P = centD H t
  /-- step (1): `|Q₀| = 2 ^ |P|` -/
  hQ0 : Nat.card ↥(Q0sub H) = 2 ^ Nat.card P
  /-- step (1): `N_G(P) = C_G(P)` -/
  hNG : Subgroup.normalizer (P : Set G) = Subgroup.centralizer (P : Set G)
  /-- step (1): `D ⊓ C_G(P) = Σ ⋊ P` -/
  h1e : twoPoint H t ⊓ Subgroup.centralizer (P : Set G) = Sig H t P ⊔ P
  /-- step (2): the near-field shadow -/
  m : ℕ
  R : Subgroup G
  hm : 1 ≤ m
  hf : (orderOf (s * t)).Prime
  hNR : Ker H Q P t ≤ R
  hRc : R ≤ Subgroup.centralizer (P : Set G)
  hRn : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G)
  hcardR : Nat.card R = Nat.card ↥(Ker H Q P t) * orderOf (s * t) ^ m
  hcq : Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m
  hfpf : ∀ x ∈ R, x ∉ Ker H Q P t → ∀ y ∈ CQ Q P, y * x * y⁻¹ * x⁻¹ ∈ Ker H Q P t → y = 1
  /-- step (3) -/
  h3 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥(oddPart Q) →
    (∃ i < Nat.card P, ℓ ≡ 2 ^ i [MOD 2 ^ Nat.card P - 1]) ∧ ℓ ≠ Nat.card P
  /-- step (4): `|Q| = |C_Q(P)| ^ |P|` -/
  h4 : Nat.card Q = Nat.card ↥(CQ Q P) ^ Nat.card P
  /-- step (5): the non-abelian dichotomy -/
  h5 : ¬ IsMulCommutative ↥(CQ Q P) → Nat.card ↥(CQ Q P) = 8 ∧ oddPart Q = ⊥

/-- **Steps (1)–(5) of Ch. V §3, assembled.**  The inputs are the other areas' `Prop`s, the three
literature inputs of §3 ((4) needs `WielandtFixedPoint`, (5) needs `AppXIProp2`), and the standing
context `CtxF`. -/
theorem chain15 (hFT : FeitThompsonProp) (hW : Work.ThmF.WielandtFixedPoint)
    (hTh : ThompsonFrobeniusProp) (hNF : NearFieldAppXIProp) (hXI2 : AppXIProp2)
    (hC4 : ChIIFourProp) {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) : Nonempty (Chain15 H Q t s r P) := by
  -- ## step (1)
  obtain ⟨hWP, hV, hQ0, hNG, h1e⟩ := Work.ThmF.Prove.step1 hFT hC4 c
  -- ## step (2)
  obtain ⟨m, R, hm, hf, hNR, hRc, hRn, hcardR, hcq, hfpf⟩ := step2 hNF c
  -- ## `P ∩ C_G(Q) = 1` (`D` acts faithfully on `Q`, `L6faith`)
  have hPleD : P ≤ twoPoint H t := c.P_le.trans inf_le_left
  have hPfaith : ∀ p ∈ P, (∀ q ∈ Q, p * q * p⁻¹ = q) → p = 1 := by
    intro p hp hfix
    refine Work.ThmF.ChV12.eq_one_of_centralizes_Q c.sit c.split (hPleD hp) ?_
    intro q hq
    have h := hfix q hq
    calc p * q = (p * q * p⁻¹) * p := by group
      _ = q * p := by rw [h]
  -- ## step (3)
  have h3 := Work.ThmF.Prove.step3 hFT hTh hNF hC4 c
  -- ## step (4)
  have h4 := Work.ThmF.Prove.step4 hW hFT hTh hC4 c h3 hPfaith
  -- ## step (5)
  have hnil : Group.IsNilpotent ↥Q :=
    Work.ThmF.ChV12.prop1b c.sit hC4 hTh H Q t c.split (CtxF.Kset_nontrivial c)
  have h5 := Work.ThmF.Prove.step5 hXI2 hFT hTh hNF hC4 hnil c h4
  exact ⟨⟨hWP, hV, hQ0, hNG, h1e, m, R, hm, hf, hNR, hRc, hRn, hcardR, hcq, hfpf,
    h3, h4, h5⟩⟩

end Work.ThmF.ChV3
