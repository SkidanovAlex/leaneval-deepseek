import Mathlib
import Submission.Work.Peluse.UControl.levCubeDefs
import Submission.Work.Peluse.UControl.levNextDefs

/-!
# The analytic transfer along a chain of PET steps (the level chain)

`LevRound` (Peluse's Lemma 4.8) is a chain of PET steps; its analytic half is the iteration of
`levStepAnalytic_lam` (correlation `B -> petChainLevel B 1`) and `levStepAnalytic_sb` (shift bound
`(c, Dsb) -> (c - 1, 2 * Dsb)`) along the reachability relation `Reach`.

This file starts that iteration: `reach_analytic_refl` is the base case (`Reach.refl`).  The
inductive step (`Reach.step`) consumes one `levStepAnalytic_lam`/`levStepAnalytic_sb` and then the
induction hypothesis at the shorter chain, composing the levels by `petChainLevel_div`
(`petChainLevel (petChainLevel γ 1) k = petChainLevel γ (k + 1)`) and the shift constants by
`2 ^ (k+1) * Dsb`.

`/tmp` is not writable in this sandbox: `export TMPDIR=$PWD/.tmpdir` before any invocation of the
Lean CLI.
-/

/-
## Writing the `Reach.rec` induction (two traps, both hit in `reach_length_le`)

1. `Reach` is defined in `levCubeDefs.lean`, which this file must import (it is *not* re-exported by
   `HistInv`/`histStepTransfer`).
2. The `step` constructor is `step {L} (X) (i₀) (h₀) (hh) {L'} {Z} (h)`: `L'` and `Z` are
   **implicit and not pattern-bindable**, so the case takes five names plus the hypothesis, i.e.
   `| step X i₀ h₀ hh hrest ih => ...` (seven names gives "Too many variable names provided at
   alternative `step`: 7 provided, but 6 expected").  The target state `Z` is therefore not
   nameable in the case; get its length from `reach_length_le` (below) if needed.

-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

/-- **The base case of the analytic transfer** (`Reach.refl`): with no PET steps the data is
unchanged, and `petChainLevel B 0 = B`, `c - 0 = c`, `2 ^ 0 * Dsb = Dsb`. -/
theorem reach_analytic_refl {d L : ℕ} (X : HistData d L) (N M c Dsb : ℕ) (γ' B : ℝ)
    (F : (X.toSym).S.ι → ℤ → ℂ) (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat L → ℤ → ℂ)
    (hSB : (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.ShiftBound N M c Dsb)
    (hlam : B ≤ (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.lam N M) :
    ∃ (F' : (X.toSym).S.ι → ℤ → ℂ)
      (g' : WinTower ⌊γ' * (M : ℝ)⌋.toNat L → ℤ → ℂ),
      petChainLevel B 0 ≤ (histPet X ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.lam N M ∧
      (histPet X ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.ShiftBound N M (c - 0)
        ((2 : ℕ) ^ 0 * Dsb) := by
  refine ⟨F, g, ?_, ?_⟩
  · simpa using hlam
  · simpa using hSB

/-- **A chain of PET steps never shortens the parameter set**: `Reach X X'` implies
`(length of X) <= (length of X')`.  This is what turns `L' - L` into `(L' - (L+1)) + 1` in the step
case of `reach_analytic` (each step adds exactly one parameter). -/
theorem reach_length_le {d : ℕ} : ∀ {L L' : ℕ} {X : HistData d L} {X' : HistData d L'},
    Reach X X' → L ≤ L' := by
  intro L L' X X' hr
  induction hr with
  | refl X => exact le_rfl
  | step X i₀ h₀ hh hrest ih => exact le_trans (Nat.le_succ _) ih

/-- **The analytic transfer along a chain of PET steps.**  From a state `X` satisfying the
correlation lower bound `B`, the shift bound `(c, Dsb)` and the window hypothesis `hw`, every state
`X'` reachable from `X` by PET steps carries the same data with the level lowered to
`petChainLevel B (L' - L)` and the shift bound `(c - (L' - L), 2 ^ (L' - L) * Dsb)`.

The recursion is `Reach.rec` with an *explicit motive*, so that each case binds its own `L`, `L'`,
`X`, `X'`/`Z` and every name in the body is the one written (with `induction hr` instead, Lean
generalizes and renames exactly `L`, `X`, `X'` -- they depend on `hr` -- and any annotation naming
them silently refers to the outer variables). -/
theorem reach_analytic {d : ℕ} :
    ∀ {L L' : ℕ} (X : HistData d L) (X' : HistData d L') (hr : Reach X X')
      (N M c Dsb : ℕ) (γ' B : ℝ) (F : (X.toSym).S.ι → ℤ → ℂ)
      (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat L → ℤ → ℂ),
      0 < N → 0 < M → 0 < γ' → γ' ≤ 1 → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat → 0 < B → B ≤ 1 →
      (L' - L) + 1 ≤ c →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, SupportIn (F i) N) →
      (∀ a x, ‖g a x‖ ≤ 1) → (∀ a, SupportIn (g a) N) →
      (∀ k < L' - L, γ' ≤ petChainLevel B k ^ 2 /
        (20000 * ((((2 : ℕ) ^ k * Dsb : ℕ) : ℝ) + 1))) →
      (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.ShiftBound N M c Dsb →
      B ≤ (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.lam N M →
      ∃ (F' : (X'.toSym).S.ι → ℤ → ℂ)
        (g' : WinTower ⌊γ' * (M : ℝ)⌋.toNat L' → ℤ → ℂ),
        petChainLevel B (L' - L) ≤ (histPet X' ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.lam N M ∧
        (histPet X' ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.ShiftBound N M (c - (L' - L))
          ((2 : ℕ) ^ (L' - L) * Dsb) := by
  intro L L' X X' hr
  refine Reach.rec (motive := fun {L L'} (X : HistData d L) (X' : HistData d L')
      (_ : Reach X X') =>
      ∀ (N M c Dsb : ℕ) (γ' B : ℝ) (F : (X.toSym).S.ι → ℤ → ℂ)
        (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat L → ℤ → ℂ),
        0 < N → 0 < M → 0 < γ' → γ' ≤ 1 → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat → 0 < B → B ≤ 1 →
        (L' - L) + 1 ≤ c →
        (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, SupportIn (F i) N) →
        (∀ a x, ‖g a x‖ ≤ 1) → (∀ a, SupportIn (g a) N) →
        (∀ k < L' - L, γ' ≤ petChainLevel B k ^ 2 /
          (20000 * ((((2 : ℕ) ^ k * Dsb : ℕ) : ℝ) + 1))) →
        (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.ShiftBound N M c Dsb →
        B ≤ (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.lam N M →
        ∃ (F' : (X'.toSym).S.ι → ℤ → ℂ)
          (g' : WinTower ⌊γ' * (M : ℝ)⌋.toNat L' → ℤ → ℂ),
          petChainLevel B (L' - L) ≤ (histPet X' ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.lam N M ∧
          (histPet X' ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.ShiftBound N M (c - (L' - L))
            ((2 : ℕ) ^ (L' - L) * Dsb)) ?_ ?_ hr
  · -- `refl`: `X' := X`, `L' := L`
    intro L X N M c Dsb γ' B F g _ _ _ _ _ _ _ _ _ _ _ _ _ hSB hlam
    refine ⟨F, g, ?_, ?_⟩
    · simpa using hlam
    · simpa using hSB
  · -- `step`: the case binds its own `L`, `X`, `i₀`, `h₀`, `hh`, `L'`, `Z`, `hrest`, `ih`
    intro L X i₀ h₀ hh L' Z hrest ih
    intro N M c Dsb γ' B F g hN hM hγ'0 hγ'1 hH hB0 hB1 hc hFb hFs hfb hfs hw hSB hlam
    have hlen := reach_length_le hrest
    have hc1 : 1 ≤ c := by omega
    have hw0 : γ' ≤ B ^ 2 / (20000 * ((Dsb : ℝ) + 1)) := by
      simpa using hw 0 (by omega)
    have hlam₁ := levStepAnalytic_lam_named X i₀ h₀ hh N M c Dsb γ' B F g
      hN hM hγ'0 hH hc1 hB0 hB1 hFb hFs hfb hfs hw0 hSB hlam
    have hSB₁ := levStepAnalytic_sb_named X i₀ h₀ hh N M c Dsb γ' F g hγ'0 hγ'1
      (by omega) hSB
    have hFb₁ : ∀ i x, ‖levNextF X i₀ h₀ hh F i x‖ ≤ 1 := levNextF_bdd X i₀ h₀ hh F hFb
    have hFs₁ : ∀ i, SupportIn (levNextF X i₀ h₀ hh F i) N := levNextF_supp X i₀ h₀ hh F hFs
    have hfb₁ : ∀ a x, ‖levNextg X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat F g a x‖ ≤ 1 :=
      levNextg_bdd X i₀ h₀ hh _ F g hFb
    have hfs₁ : ∀ a, SupportIn (levNextg X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat F g a) N :=
      levNextg_supp X i₀ h₀ hh _ F g hFs
    have hB0₁ : 0 < petChainLevel B 1 := petChainLevel_pos B hB0 1
    have hB1₁ : petChainLevel B 1 ≤ 1 := petChainLevel_le_one B hB0 hB1 1
    have hw₁ : ∀ k < L' - (L + 1), γ' ≤ petChainLevel (petChainLevel B 1) k ^ 2 /
        (20000 * ((((2 : ℕ) ^ k * (2 * Dsb) : ℕ) : ℝ) + 1)) := by
      intro k hk
      have h2 := hw (k + 1) (by omega)
      have h3 : petChainLevel (petChainLevel B 1) k = petChainLevel B (k + 1) :=
        petChainLevel_div B k
      have h4 : (((2 : ℕ) ^ (k + 1) * Dsb : ℕ) : ℝ) = (((2 : ℕ) ^ k * (2 * Dsb) : ℕ) : ℝ) := by
        push_cast [pow_succ]
        ring
      simpa [← h3, ← h4] using h2
    have hc₁ : (L' - (L + 1)) + 1 ≤ c - 1 := by omega
    obtain ⟨F₂, g₂, hlam₂, hSB₂⟩ := ih N M (c - 1) (2 * Dsb) γ' (petChainLevel B 1)
      (levNextF X i₀ h₀ hh F) (levNextg X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat F g)
      hN hM hγ'0 hγ'1 hH hB0₁ hB1₁ hc₁ hFb₁ hFs₁ hfb₁ hfs₁ hw₁ hSB₁ hlam₁
    refine ⟨F₂, g₂, ?_, ?_⟩
    · have h2 := hlam₂
      have h2' := (petChainLevel_div B (L' - (L + 1))) ▸ h2
      convert h2' using 2
      omega
    · have h2 := hSB₂
      have h5 : (c - 1) - (L' - (L + 1)) = c - (L' - L) := by omega
      have h7 : L' - L = (L' - (L + 1)) + 1 := by omega
      have h6 : ((2 : ℕ) ^ (L' - (L + 1)) * (2 * Dsb) : ℕ) = ((2 : ℕ) ^ (L' - L) * Dsb : ℕ) := by
        rw [h7, pow_succ]
        ring
      simpa [h5, h6] using h2

/-- **`Reach` is transitive.**  Needed by the iteration of the round: the chain from `X₀` to the
level-`1` state is built one round at a time. -/
theorem Reach_trans {d : ℕ} :
    ∀ {L L' L'' : ℕ} {X : HistData d L} {Y : HistData d L'} {Z : HistData d L''},
      Reach X Y → Reach Y Z → Reach X Z := by
  intro L L' L'' X Y Z hXY hYZ
  revert hYZ
  induction hXY with
  | refl X => intro hYZ; exact hYZ
  | step X i₀ h₀ hh hrest ih => intro hYZ; exact Reach.step X i₀ h₀ hh (ih hYZ)

end

end Work.Peluse.UControl
