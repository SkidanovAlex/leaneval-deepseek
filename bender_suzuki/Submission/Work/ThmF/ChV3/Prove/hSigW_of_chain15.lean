import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.step9WV

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

/-- `P ≤ V = C_D(t)` normalises `W = C_V(K)` (`Prove/step9WV`), so `P` acts on `W` by
conjugation.  Since `P` has prime order `p = |P|`, every orbit of this action has size `1` or
`p`, hence `|W| ≡ |C_W(P)| [MOD p]`; and `C_W(P) = W ⊓ C_G(P) = Σ`.  Therefore `p ∣ |W|` iff
`p ∣ |Σ|`, which is the contrapositive direction recorded here. -/
theorem hSigW_of_chain15 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (hpf : Nat.card P = orderOf (s * t)) :
    ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) →
      ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.W H t) := by
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
