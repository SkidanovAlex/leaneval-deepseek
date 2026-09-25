import Mathlib
import Submission.Work.ProPGS.CommonsBridge

/-!
# `Work.ProPGS.finrank_Tq_le_card_mul`

**Namespace** `Work.ProPGS`; module `Submission.Work.ProPGS.finrank_Tq_le_card_mul`.

The Serre dimension count `dim (Q n ⧸ P n) ≤ #S · dim (B ⧸ b^k)` in a form that only needs the
*two* inputs the Golod--Shafarevich argument actually consumes from a relator set `S`:

* `ker Φ ≤ range dRel` -- exactness of the Fox/Serre sequence at the middle term, i.e. that the
  relations of `π` are carried by `S` (this is weaker than `normalClosure S = ker π`, and in the
  intended application it is supplied by the spanning argument
  `Work.ProPGS.relSpan_add_JmulIW_of_spanning` together with
  `Work.ProPGS.ker_Phi_le_range_dRel_of_ideal_le`); and
* the *filtration shift* `dRel (∏ᵢ b^m) ⊆ ∏ᵢ b^(m+1)` -- the statement that the relators of `S`
  have order `≥ 2`.

The commons prove the same inequality (`ScratchSerre.Qker_le_card_aux`) under the single stronger
hypothesis `Subgroup.normalClosure S = π.ker`; the point of this lemma is that the dimension count
never uses `Φ ∘ dRel = 0` on *all* of `S → B` (which is what `normalClosure S = ker π` buys), only
the two facts above -- the inclusion `map mkQ (Q n) ≤ range ψ` uses exactness, and the
well-definedness of the induced map on `(S → B) ⧸ ∏ b^k` uses the shift.

## Proof outline

Write `P n = ∏ᵢ b^n`, `Q n = ker Φ ⊔ P n` and `ψ = mkQ(P (k+1)) ∘ dRel : (S → B) → (α → B) ⧸ P (k+1)`.

* `map (mkQ (P (k+1))) (Q (k+1)) ≤ range ψ`: an element of `Q (k+1)` is `a + b` with
  `a ∈ ker Φ`, `b ∈ P (k+1)`; `b` dies in the quotient and `a = dRel f` for some `f` by `hker`,
  so the class is `ψ f`.
* `P k ≤ ker ψ` by `hshift` (elements of `P k`, i.e. `S`-tuples of elements of `b^k`, are sent by
  `dRel` into `P (k+1)`), so `ψ` induces `ψ̄ : (S → B) ⧸ P k → (α → B) ⧸ P (k+1)` with the same
  range.
* Hence `dim (Q n ⧸ P n) ≤ dim (range ψ̄) ≤ dim ((S → B) ⧸ P k) = #S · dim (B ⧸ b^k)`, the last
  equality being the commons `ScratchSerre.finrank_pi_quotient`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ProPGS

open Commons.GroupTheory.ProPGroup

theorem finrank_Tq_le_card_mul {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    {α : Type} [Fintype α] [DecidableEq α] (hG : IsPGroup p G)
    (π : FreeGroup α →* G) (hπ : Function.Surjective π)
    (hgen : ∀ (T : Finset G), Subgroup.closure (T : Set G) = ⊤ → Fintype.card α ≤ T.card)
    (S : Finset (FreeGroup α))
    (hker : (Commons.GroupTheory.ProPGroup.ScratchSerre.Phi p G α π).ker ≤
      (Commons.GroupTheory.ProPGroup.ScratchSerre.dRel p α G S π).range)
    (hshift : ∀ (m : ℕ) {f : ↥S → MonoidAlgebra (ZMod p) G},
      f ∈ Submodule.pi Set.univ (fun _ : ↥S => Submodule.restrictScalars (ZMod p) (Commons.GroupTheory.ProPGroup.ScratchSerre.bG p G ^ m)) →
      Commons.GroupTheory.ProPGroup.ScratchSerre.dRel p α G S π f ∈
        Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p) (Commons.GroupTheory.ProPGroup.ScratchSerre.bG p G ^ (m + 1))))
    (k : ℕ) :
    Module.finrank (ZMod p) ↥(Submodule.map (Commons.GroupTheory.ProPGroup.ScratchSerre.Ppow p G α (k + 1)).mkQ
        (Commons.GroupTheory.ProPGroup.ScratchSerre.Qker p G α π (k + 1))) ≤
      S.card * Module.finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
        Submodule.restrictScalars (ZMod p) (Commons.GroupTheory.ProPGroup.ScratchSerre.bG p G ^ k)) := by
  classical
  -- `map (mkQ (P (k+1))) (Q (k+1)) ≤ range ψ`
  have hle : Submodule.map (Submodule.mkQ (ScratchSerre.Ppow p G α (k + 1)))
        (ScratchSerre.Qker p G α π (k + 1)) ≤
      LinearMap.range (ScratchSerre.psi p G α π S (k + 1)) := by
    rintro y ⟨q, hq, rfl⟩
    rcases Submodule.mem_sup.mp hq with ⟨a, ha, b, hb, hab⟩
    subst hab
    obtain ⟨f, hf⟩ := hker ha
    refine ⟨f, ?_⟩
    have hb0 : Submodule.mkQ (ScratchSerre.Ppow p G α (k + 1)) b = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hb
    calc ScratchSerre.psi p G α π S (k + 1) f
        = Submodule.Quotient.mk ((ScratchSerre.dRel p α G S π) f) :=
          ScratchSerre.psi_apply p G α π S (k + 1) f
      _ = Submodule.mkQ (ScratchSerre.Ppow p G α (k + 1)) (ScratchSerre.dRel p α G S π f) :=
          (Submodule.mkQ_apply _ _).symm
      _ = Submodule.mkQ (ScratchSerre.Ppow p G α (k + 1)) a := by rw [hf]
      _ = Submodule.mkQ (ScratchSerre.Ppow p G α (k + 1)) (a + b) := by
          rw [map_add, hb0, add_zero]
  -- `∏ᵢ b^k ⊆ ker ψ`
  have hkerpsi : Submodule.pi Set.univ
      (fun _ : ↥S => Submodule.restrictScalars (ZMod p) (ScratchSerre.bG p G ^ k)) ≤
      LinearMap.ker (ScratchSerre.psi p G α π S (k + 1)) := by
    intro f hf
    rw [LinearMap.mem_ker, ScratchSerre.psi_apply, Submodule.Quotient.mk_eq_zero]
    exact hshift k hf
  -- the induced map on the quotient by `∏ᵢ b^k`
  let psiBar := Submodule.liftQ
    (Submodule.pi Set.univ
      (fun _ : ↥S => Submodule.restrictScalars (ZMod p) (ScratchSerre.bG p G ^ k)))
    (ScratchSerre.psi p G α π S (k + 1)) hkerpsi
  have hrange : LinearMap.range psiBar = LinearMap.range (ScratchSerre.psi p G α π S (k + 1)) :=
    Submodule.range_liftQ _ _ _
  calc Module.finrank (ZMod p) ↥(Submodule.map (Submodule.mkQ (ScratchSerre.Ppow p G α (k + 1)))
          (ScratchSerre.Qker p G α π (k + 1)))
      ≤ Module.finrank (ZMod p) ↥(LinearMap.range (ScratchSerre.psi p G α π S (k + 1))) :=
        Submodule.finrank_mono hle
    _ = Module.finrank (ZMod p) ↥(LinearMap.range psiBar) := by rw [hrange]
    _ ≤ Module.finrank (ZMod p) ((↥S → MonoidAlgebra (ZMod p) G) ⧸ Submodule.pi Set.univ
          (fun _ : ↥S => Submodule.restrictScalars (ZMod p) (ScratchSerre.bG p G ^ k))) :=
        LinearMap.finrank_range_le psiBar
    _ = S.card * Module.finrank (ZMod p) (MonoidAlgebra (ZMod p) G ⧸
          Submodule.restrictScalars (ZMod p) (ScratchSerre.bG p G ^ k)) := by
        rw [ScratchSerre.finrank_pi_quotient (K := ZMod p)
          (M := fun _ : ↥S => MonoidAlgebra (ZMod p) G)
          (fun _ => Submodule.restrictScalars (ZMod p) (ScratchSerre.bG p G ^ k))]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]

end Work.ProPGS
