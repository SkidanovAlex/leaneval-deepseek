import Mathlib
import Submission.Work.Peluse.UControl.histStepTransfer
import Submission.Work.Peluse.UControl.petStepLink

/-!
# The transported data of one PET step (the successor's functions, at an arbitrary slot)

The analytic transfer along a chain of PET steps (`reach_analytic`) threads the slot functions `F`
and the base function `g` through the chain.  At each step at `(i₀, h₀)` the successor's functions are

* `levNextF X i₀ h₀ hh F = fun x => stepF F ((X.stepIdx i₀ h₀ hh x).1)` — the slot functions
  (`F i` or its conjugate, cf. `stepF`);
* `levNextg X i₀ h₀ hh H F g = ((toPetP H F g).step ⟨(i₀,h₀),hh⟩ H).drop (petStepConsts …)) .f` —
  the base function (the dropped constant slots absorbed into the base, cf. `PetStateP.drop`).

This file gives those two functions and their elementary properties (boundedness by `1` and support
in `symIcc N`), which is what the step case of the induction must feed back into
`levStepAnalytic_lam`/`levStepAnalytic_sb`.  It is the arbitrary-slot version of
`histNextF`/`histNextf` (`HistInv.lean`), whose lemmas are stated for the deterministic selection.

`/tmp` is not writable in this sandbox: `export TMPDIR=$PWD/.tmpdir` before invoking the Lean CLI.
-/

/-
## What the step case of `reach_analytic` still needs (design note)

`levStepAnalytic_lam` (in the imported file) concludes an *existential* `∃ F' g', ...`.  The induction
cannot use an existential: it must thread the *same* functions through the chain, so it needs the
one-step lemmas stated with the **named** transported functions of this file:

```
theorem levStepAnalytic_lam_named ... :
    petChainLevel B 1 ≤ (histPet (X.step i₀ h₀ hh) H
      (levNextF X i₀ h₀ hh F) (levNextg X i₀ h₀ hh H F g)).toState.lam N M
```

(or, equivalently, a proof that the witness of the existential *is* `levNextF`/`levNextg`; the proof
of `levStepAnalytic_lam` already ends by exhibiting exactly these two functions, so the named version
is the same proof without the `∃`).  The same holds for `levStepAnalytic_sb`.  Then the `Reach.rec`
step case is: apply the two named one-step lemmas at `(i₀,h₀,hh)`, feed `levNextF_bdd`/
`levNextF_supp`/`levNextg_bdd`/`levNextg_supp` into the induction hypothesis, and compose the levels
by `petChainLevel_div` (`petChainLevel (petChainLevel B 1) k = petChainLevel B (k+1)`) and the shift
constants by `2 ^ (k+1) * Dsb`; the window hypothesis at step `k+1` is `hwin (k+1)` verbatim, so no
re-indexing lemma is needed for it.  The range arithmetic in the step case is
`(L' - (L+1)) + 1 ≤ c - 1` from `(L' - L) + 1 ≤ c` and `1 ≤ c`.

-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

/-- The slot functions of the successor of the PET step at `(i₀, h₀)`. -/
def levNextF {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (F : (X.toSym).S.ι → ℤ → ℂ) :
    ((X.step i₀ h₀ hh).toSym).S.ι → ℤ → ℂ :=
  fun x => stepF F ((X.stepIdx i₀ h₀ hh x).1)

/-- The base function of the successor of the PET step at `(i₀, h₀)`: the base of the stepped state
with its constant slots absorbed (`PetStateP.drop`). -/
def levNextg {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (H : ℕ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (g : WinTower H n → ℤ → ℂ) : WinTower H (n + 1) → ℤ → ℂ :=
  fun a x => ((((X.toSym).S.toPetP H F g).step ⟨(i₀, h₀), hh⟩ H).drop
    (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).f a x

/-- The successor's slot functions are `1`-bounded. -/
lemma levNextF_bdd {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (F : (X.toSym).S.ι → ℤ → ℂ)
    (hFb : ∀ i x, ‖F i x‖ ≤ 1) : ∀ i x, ‖levNextF X i₀ h₀ hh F i x‖ ≤ 1 :=
  fun i x => stepF_bdd F hFb _ x

/-- The successor's slot functions are supported in `symIcc N`. -/
lemma levNextF_supp {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (F : (X.toSym).S.ι → ℤ → ℂ) {N : ℕ}
    (hFs : ∀ i, SupportIn (F i) N) : ∀ i, SupportIn (levNextF X i₀ h₀ hh F i) N :=
  fun i => stepF_supp F hFs _

/-- The successor's base function is `1`-bounded.  The base of a stepped state is `F i₀` (the
dropped constant slots multiply it, and `PetStateP.drop` absorbs them), so the bound is on `F`, not
on `g`; `g` does not occur in the bound at all. -/
lemma levNextg_bdd {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (H : ℕ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (g : WinTower H n → ℤ → ℂ) (hFb : ∀ i x, ‖F i x‖ ≤ 1) :
    ∀ a x, ‖levNextg X i₀ h₀ hh H F g a x‖ ≤ 1 :=
  fun a x => toPetP_stepf_bdd (X.toSym).S ⟨(i₀, h₀), hh⟩ F g
    (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩) hFb a x

/-- The successor's base function is supported in `symIcc N` (again the bound comes from `F`). -/
lemma levNextg_supp {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (H : ℕ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (g : WinTower H n → ℤ → ℂ) {N : ℕ} (hFs : ∀ i, SupportIn (F i) N) :
    ∀ a, SupportIn (levNextg X i₀ h₀ hh H F g a) N :=
  fun a => toPetP_stepf_supp (X.toSym).S ⟨(i₀, h₀), hh⟩ F g
    (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩) hFs a

/-- **The correlation of one step, with the *named* transported functions** (what the induction
threads through the chain; the existential version is `levStepAnalytic_lam`). -/
theorem levStepAnalytic_lam_named {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d)
    (h₀ : Fin n → Bool) (hh : (i₀, h₀) ∈ X.H) (N M c Dsb : ℕ) (γ' B : ℝ)
    (F : (X.toSym).S.ι → ℤ → ℂ) (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat n → ℤ → ℂ)
    (hN : 0 < N) (hM : 0 < M) (hγ'0 : 0 < γ') (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat) (hc : 1 ≤ c)
    (hB0 : 0 < B) (hB1 : B ≤ 1)
    (hFb : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, SupportIn (F i) N)
    (hfb : ∀ a x, ‖g a x‖ ≤ 1) (hfs : ∀ a, SupportIn (g a) N)
    (hwin : γ' ≤ B ^ 2 / (20000 * ((Dsb : ℝ) + 1)))
    (hSB : (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.ShiftBound N M c Dsb)
    (hlam : B ≤ (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.lam N M) :
    petChainLevel B 1 ≤ (histPet (X.step i₀ h₀ hh) ⌊γ' * (M : ℝ)⌋.toNat
      (levNextF X i₀ h₀ hh F) (levNextg X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat F g)).toState.lam N M := by
  classical
  have hstep := PetState.lam_step (((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F g)).toState
    ⟨(i₀, h₀), hh⟩ (c := c) (D := Dsb) (γ := B) (γ' := γ')
    hc hN hM hB0 hB1 hγ'0
    (toPetP_nu_nonneg (X.toSym).S ⌊γ' * (M : ℝ)⌋.toNat F g)
    (toPetP_sum_nu (X.toSym).S ⌊γ' * (M : ℝ)⌋.toNat F g hH)
    hwin hH hfb hfs hFb hFs hSB hlam
  have hcst := toPetP_step_drop_hc (X.toSym).S ⟨(i₀, h₀), hh⟩ ⌊γ' * (M : ℝ)⌋.toNat F g
    (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)
    (fun j hj => by
      simpa only [petStepConsts, Finset.mem_filter, Finset.mem_univ, true_and] using hj)
  have hlamNext : petChainLevel B 1 ≤
      (((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F g).step ⟨(i₀, h₀), hh⟩
        ⌊γ' * (M : ℝ)⌋.toNat).drop
        (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).lam N M) := by
    rw [petChainDrop (((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F g).step ⟨(i₀, h₀), hh⟩
      ⌊γ' * (M : ℝ)⌋.toNat) (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩) hcst N M]
    rw [petChainEvalStep ((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F g) ⟨(i₀, h₀), hh⟩
      ⌊γ' * (M : ℝ)⌋.toNat N M]
    have h1 : petChainLevel B 1 = B ^ 2 / 2000 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, petChainLevel_succ, petChainLevel_zero]
    rw [h1]
    exact hstep
  exact hlamNext.trans
    (le_of_eq ((hstLamGen X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat N M F g).symm))

/-- **The shift bound of one step, with the *named* transported functions.** -/
theorem levStepAnalytic_sb_named {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d)
    (h₀ : Fin n → Bool) (hh : (i₀, h₀) ∈ X.H) (N M c Dsb : ℕ) (γ' : ℝ)
    (F : (X.toSym).S.ι → ℤ → ℂ) (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat n → ℤ → ℂ)
    (hγ'0 : 0 < γ') (hγ'1 : γ' ≤ 1) (hc : 1 ≤ c)
    (hSB : (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.ShiftBound N M c Dsb) :
    (histPet (X.step i₀ h₀ hh) ⌊γ' * (M : ℝ)⌋.toNat
      (levNextF X i₀ h₀ hh F) (levNextg X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat F g)).toState.ShiftBound
        N M (c - 1) (2 * Dsb) := by
  classical
  have hHM : ((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℤ) ≤ (M : ℤ) := winNat_cast_le hγ'0 M hγ'1
  have hstepSB : (((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F g).step ⟨(i₀, h₀), hh⟩
      ⌊γ' * (M : ℝ)⌋.toNat).toState.ShiftBound N M (c - 1) (2 * Dsb) :=
    PetStateP.step_ShiftBound ((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F g)
      ⟨(i₀, h₀), hh⟩ ⌊γ' * (M : ℝ)⌋.toNat N M (c - 1) (2 * Dsb)
      (PetState.ShiftBound.step
        (((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F g).toState)
        ⟨(i₀, h₀), hh⟩ hc hHM hSB)
  have hdropSB : ((((X.toSym).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F g).step ⟨(i₀, h₀), hh⟩
      ⌊γ' * (M : ℝ)⌋.toNat).drop
      (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).toState.ShiftBound N M (c - 1) (2 * Dsb) :=
    PetStateP.drop_ShiftBound _ _ hstepSB
  exact (hstSBGen X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat N M (c - 1) (2 * Dsb) F g).mp hdropSB

end

end Work.Peluse.UControl
