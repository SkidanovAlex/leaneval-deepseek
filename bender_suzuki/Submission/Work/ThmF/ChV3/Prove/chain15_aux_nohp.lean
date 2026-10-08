import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.Prove.hD_of_chain15
import Submission.Work.ThmF.ChV3.Prove.hSigW_of_chain15

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.chain15_aux_nohp` — the `hpf`-free §3 aux pair

The two §3 auxiliary facts

* `|D| = (2^p − 1) · |W| · p` (`hD_of_chain15`), and
* `¬ p ∣ |Σ| → ¬ p ∣ |W|` (`hSigW_of_chain15`),

are proved on disk with a spurious extra hypothesis `hpf : Nat.card P = orderOf (s * t)`.
That hypothesis is *not used* by either proof: the first is pure counting
(`|D| = |V|·|K|`, `|K| = |Inv H| = 2^p − 1`, `|V| = |W|·p`) and the second a `mod p`
orbit congruence for the conjugation action of the `p`-group `P` on `W`.  Here we simply
replay the two proofs without `hpf`, which is exactly the pair recorded by the name of this
file (`nohp`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

theorem chain15_aux_nohp {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) :
    (Nat.card ↥(Submission.Blueprint.twoPoint H t) =
        (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P) ∧
      (¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) →
        ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.W H t)) := by
  constructor
  · -- ## `|D| = (2^p − 1)·|W|·p`,  replay of `hD_of_chain15` without `hpf`
    classical
    -- Ch. V §1 Prop. 1 (c): the involutions of `H` commute pairwise.
    have hcomm : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), a * b = b * a :=
      Work.ThmF.L5.involutions_commute c.sit hC4 c.split
    -- `|Inv H| = |Q₀| - 1 = 2 ^ |P| - 1`.
    have hInv : (involutions (H : Set G)).ncard = 2 ^ Nat.card P - 1 := by
      have h := Work.ThmF.L5.card_Q0sub_eq (H := H) hcomm
      rw [h15.hQ0] at h
      have hpos : 1 ≤ 2 ^ Nat.card P := Nat.one_le_two_pow
      omega
    -- Ch. I §2: `|K| = |Inv H|`.
    have hKinv : (Work.ThmF.Kset H t).ncard = (involutions (H : Set G)).ncard :=
      Work.ThmF.Bender.cardKsetEqInv c.split.stronglyEmbedded c.split.invol c.split.not_mem
    -- Peterfalvi I App. I (1)(b): `|D| = |V| · |K|`.
    have hDcard : Nat.card ↥(Submission.Blueprint.twoPoint H t) =
        Nat.card ↥(Submission.Blueprint.centD H t) * (Work.ThmF.Kset H t).ncard :=
      (Work.ThmF.card_centD_mul_card_Kset (H := H) (Q := Q) (t := t)
        (Work.ThmF.IsSplitRankOne.toData c.split)).symm
    -- Step (1): `V = W ⊔ P`, `W ⊓ P = ⊥`, `P` normalises `W`, so `|V| = |W| · |P|`.
    have hVcard : Nat.card ↥(Submission.Blueprint.centD H t) =
        Nat.card ↥(Work.ThmF.W H t) * Nat.card P := by
      have h := Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer
        (A := Work.ThmF.W H t) (B := P)
        (Work.ThmF.ChV3.Prove.P_le_normalizer_W (H := H) (t := t) c) h15.hWP
      rwa [h15.hV] at h
    rw [hDcard, hKinv, hInv, hVcard]
    ring
  · -- ## `¬ p ∣ |Σ| → ¬ p ∣ |W|`,  replay of `hSigW_of_chain15` without `hpf`
    intro hS hW
    apply hS
    -- `p = |P|` is prime, so `↥P` is a `p`-group.
    have hp : (Nat.card P).Prime := c.P_prime
    haveI : Fact (Nat.card P).Prime := ⟨hp⟩
    -- `W` is invariant under conjugation by `P` (via `V = C_D(t) ≤ N_G(W)`).
    have hsmul : ∀ (a : ↥P) (b : ↥(Work.ThmF.W H t)),
        (a : G) * (b : G) * (a : G)⁻¹ ∈ Work.ThmF.W H t :=
      fun a b => Work.ThmF.Prove.step9WV (a : G) (c.P_le a.2) (b : G) b.2
    -- the conjugation action of `↥P` on `↥W`
    letI : MulAction ↥P ↥(Work.ThmF.W H t) :=
    { smul := fun a b => ⟨(a : G) * (b : G) * (a : G)⁻¹, hsmul a b⟩
      one_smul := fun b => Subtype.ext (by
        show (1 : G) * (b : G) * (1 : G)⁻¹ = (b : G); simp)
      mul_smul := fun a c b => Subtype.ext (by
        show ((a : G) * (c : G)) * (b : G) * ((a : G) * (c : G))⁻¹ =
          (a : G) * ((c : G) * (b : G) * (c : G)⁻¹) * (a : G)⁻¹
        group) }
    have hPg : IsPGroup (Nat.card P) ↥P := IsPGroup.of_card (n := 1) (by simp)
    -- `|W| ≡ |fixed points| = |C_W(P)| = |Σ| [MOD p]`.
    have hmod0 := hPg.card_modEq_card_fixedPoints (α := ↥(Work.ThmF.W H t))
    -- the fixed points of the conjugation action are exactly `Σ = W ⊓ C_G(P)`.
    let fixEquiv :
        ↥(MulAction.fixedPoints ↥P ↥(Work.ThmF.W H t)) ≃ ↥(Work.ThmF.ChV3.Sig H t P) :=
    { toFun := fun y => ⟨(y.1 : G), by
        refine Subgroup.mem_inf.mpr ⟨y.1.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have h1 : (⟨h, hh⟩ : ↥P) • y.1 = y.1 := y.2 ⟨h, hh⟩
        have h2 : h * (y.1 : G) * h⁻¹ = (y.1 : G) := congrArg Subtype.val h1
        calc h * (y.1 : G) = (h * (y.1 : G) * h⁻¹) * h := by group
          _ = (y.1 : G) * h := by rw [h2]
      ⟩
      invFun := fun z => ⟨⟨(z.1 : G), (Subgroup.mem_inf.mp z.2).1⟩, by
        intro a
        apply Subtype.ext
        have hc := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp z.2).2) (a : G) a.2
        show (a : G) * (z.1 : G) * (a : G)⁻¹ = (z.1 : G)
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      ⟩
      left_inv := fun y => Subtype.ext (Subtype.ext rfl)
      right_inv := fun z => Subtype.ext rfl }
    have hcardFix : Nat.card ↥(MulAction.fixedPoints ↥P ↥(Work.ThmF.W H t)) =
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := Nat.card_congr fixEquiv
    rw [hcardFix] at hmod0
    exact Nat.modEq_zero_iff_dvd.mp (hmod0.symm.trans (Nat.modEq_zero_iff_dvd.mpr hW))

end Work.ThmF.ChV3.Prove
