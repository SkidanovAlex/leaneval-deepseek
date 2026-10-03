import Mathlib
import Submission.Work.Peluse.UControl.histPhase1Run

/-!
# The slot-sign invariant along the phase-1 history chain

`histPhase1Run` (`histPhase1Run.lean`) runs the *analytic* invariant `HistInv` along the
history-indexed phase-1 chain: starting from `HistInv N M γ' X.2 F f γ D c` it produces functions
`G, g` at the terminal state with `HistInv N M γ' (phase1Chain X).2 G g (petChainLevel γ (histLen X))
(2 ^ histLen X * D) (c - histLen X)`.

The terminal slot functions `G` are obtained from the initial ones by repeatedly applying the PET
slot map `stepF`, which replaces a slot function by itself or by its conjugate
(`stepF F (j,ε) = if ε then star (F j) else F j`).  Consequently *every* terminal slot function is
either the initial slot function of the same initial index, or its conjugate: this file proves that
companion fact, so that the terminal `G` of the chain has the shape

`G i = if B i then star (Froot i.1.1) else Froot i.1.1`

for some sign pattern `B`.  The proof tracks the sign pattern through the same well-founded
recursion that produces the invariant.

The two ingredients are

* `slotSign_step`/`slotSign_histNextF` — one PET step preserves the slot-sign form (the sign of a
  child is the sign of its parent, flipped exactly when the child carries `ε = true`); and
* `histInv_phase1Chain_sign` — the recursion producing the invariant `HistInv` *together* with the
  sign pattern (they must come from the same `G`, which is why the two are produced in one
  recursion).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The slot-sign form.**  Every slot function of the state is either the corresponding initial
slot function `Froot` or its conjugate. -/
def SlotSign (Froot : InitIdx d → ℤ → ℂ) {n : ℕ} (X : HistData d n)
    (F : (X.toSym).S.ι → ℤ → ℂ) : Prop :=
  ∃ B : (X.toSym).S.ι → Bool,
    ∀ i x, F i x = (if B i then star (Froot i.1.1 x) else Froot i.1.1 x)

/-- The `Bool` case analysis behind `slotSign_step`: a sign flip pushed through a conditional is
the same as flipping the condition. -/
lemma ite_star_eq (e b : Bool) (u : ℂ) :
    (if e then star (if b then star u else u) else (if b then star u else u))
      = (if (if e then !b else b) then star u else u) := by
  cases e <;> cases b <;> simp

/-- **One PET step preserves the slot-sign form.**  The sign of a child slot is the sign of its
parent, flipped exactly when the child carries the Boolean parameter `ε = true` (because
`star (star z) = z`). -/
lemma slotSign_step {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (Froot : InitIdx d → ℤ → ℂ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (hB : SlotSign Froot X F) :
    SlotSign Froot (X.step i₀ h₀ hh) (fun i => stepF F ((X.stepIdx i₀ h₀ hh i).1)) := by
  obtain ⟨B, hB⟩ := hB
  refine ⟨fun i => if (X.stepIdx i₀ h₀ hh i).1.2 then !(B (X.stepIdx i₀ h₀ hh i).1.1)
    else B (X.stepIdx i₀ h₀ hh i).1.1, ?_⟩
  intro i y
  have hfst : (X.stepIdx i₀ h₀ hh i).1.1.1.1 = i.1.1 := by
    rw [HistData.stepIdx_fst]
  simp only [stepF]
  rw [hB (X.stepIdx i₀ h₀ hh i).1.1 y, hfst]
  exact ite_star_eq _ _ _

/-- The sign form is preserved by the *history* successor: the slot functions `histNextF` are the
slot functions of the history step, transported along the slot identification. -/
lemma slotSign_histNextF {X : HState d} {hnl : HState.Go X} {Froot : InitIdx d → ℤ → ℂ}
    {F : (X.2.toSym).S.ι → ℤ → ℂ} (h : SlotSign Froot X.2 F) :
    SlotSign Froot (histStep X hnl).2 (histNextF X hnl F) := by
  refine slotSign_step X.2 (X.2.sel (histHne X hnl)).1 (X.2.sel (histHne X hnl)).2
    (X.2.sel_mem_H (histHne X hnl)) Froot F h

/-! ## The invariant and the sign pattern, along the chain -/

/-- **The invariant `HistInv` and the slot-sign form, at the end of the phase-1 chain.**  The two
are produced by a single well-founded recursion, since they must hold for the *same* terminal slot
functions `G`. -/
theorem histInv_phase1Chain_sign {d : ℕ} (N M : ℕ) (γ' : ℝ) (Froot : InitIdx d → ℤ → ℂ) :
    ∀ (X : HState d) (F : (X.2.toSym).S.ι → ℤ → ℂ)
      (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat X.1 → ℤ → ℂ) (γ : ℝ) (D c : ℕ),
      SlotSign Froot X.2 F →
      HistInv N M γ' X.2 F f γ D c →
      ∃ (G : ((phase1Chain X).2.toSym).S.ι → ℤ → ℂ)
        (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat (phase1Chain X).1 → ℤ → ℂ)
        (B : ((phase1Chain X).2.toSym).S.ι → Bool),
        HistInv N M γ' (phase1Chain X).2 G g (petChainLevel γ (histLen X)) (2 ^ histLen X * D)
          (c - histLen X)
        ∧ (∀ i x, G i x = (if B i then star (Froot i.1.1 x) else Froot i.1.1 x)) := by
  classical
  intro X
  induction X using WellFounded.induction (HState.rel_wf d) with
  | h X ih =>
    intro F f γ D c hsign h
    by_cases hstop : X.2.IsLinearX ∨ Phase1Done X.2
    · rw [histLen_eq_of X hstop, phase1Chain_eq_of X hstop]
      obtain ⟨B, hB⟩ := hsign
      exact ⟨F, f, B, by simpa using h, hB⟩
    · have hgo : HState.Go X := hstop
      obtain ⟨G, g, B, hInv, hSign⟩ := ih (histStep X hgo)
        (X.2.weightH_step_sel_lt (histHne X hgo))
        (histNextF X hgo F) (histNextf X hgo ⌊γ' * (M : ℝ)⌋.toNat F f)
        (petChainLevel γ 1) (2 * D) (c - 1)
        (slotSign_histNextF hsign)
        (histStepInv N M γ' X hgo F f γ D c h)
      have hlen : histLen X = histLen (histStep X hgo) + 1 := histLen_eq_not X hgo
      rw [hlen, phase1Chain_eq_not X hgo]
      refine ⟨G, g, B, ?_, hSign⟩
      have h1 : petChainLevel (petChainLevel γ 1) (histLen (histStep X hgo))
          = petChainLevel γ (histLen (histStep X hgo) + 1) := petChainLevel_div γ _
      have h2 : (2 ^ histLen (histStep X hgo) * (2 * D) : ℕ)
          = 2 ^ (histLen (histStep X hgo) + 1) * D := by rw [pow_succ]; ring
      have h3 : (c - 1) - histLen (histStep X hgo) = c - (histLen (histStep X hgo) + 1) := by
        rw [Nat.sub_sub, Nat.add_comm]
      rw [← h1, ← h2, ← h3]
      exact hInv

/-! ## The target -/

theorem histPhase1RunInv {d : ℕ} (N M : ℕ) (γ' : ℝ) (X : HistData d 0)
    (Froot : InitIdx d → ℤ → ℂ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat 0 → ℤ → ℂ)
    (γ : ℝ) (D c : ℕ) (h : HistInv N M γ' X F f γ D c)
    (hroot : ∀ i x, F i x = Froot i.1.1 x) :
    ∃ (B : ((phase1Chain (⟨0, X⟩ : HState d)).2.toSym).S.ι → Bool)
      (G : ((phase1Chain (⟨0, X⟩ : HState d)).2.toSym).S.ι → ℤ → ℂ)
      (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat (phase1Chain (⟨0, X⟩ : HState d)).1 → ℤ → ℂ),
      HistInv N M γ' (phase1Chain (⟨0, X⟩ : HState d)).2 G g
          (petChainLevel γ (histLen (⟨0, X⟩ : HState d)))
          (2 ^ histLen (⟨0, X⟩ : HState d) * D) (c - histLen (⟨0, X⟩ : HState d))
      ∧ (∀ i x, G i x = (if B i then star (Froot i.1.1 x) else Froot i.1.1 x)) := by
  have hsign : SlotSign Froot X F := by
    refine ⟨fun _ => false, ?_⟩
    intro i x
    simp [hroot]
  obtain ⟨G, g, B, hInv, hSign⟩ :=
    histInv_phase1Chain_sign N M γ' Froot ⟨0, X⟩ F f γ D c hsign h
  exact ⟨B, G, g, hInv, hSign⟩

end

end Work.Peluse.UControl
