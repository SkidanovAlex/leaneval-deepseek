import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.AVgen_add_I_smul
import Submission.Work.MB.boxSlotSum_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.AVgen_add_I_smul_ae` — `AVgen` is `ℂ`-linear on good states, at the **weak** mode bundle

`Work.BoseBoxFock.AVgen_add_I_smul` proves the `ℂ`-linearity of `AVgen` (on the `SlotGood` states)
under the *strong* mode hypotheses `Continuous (e l)` / `HasCompactSupport (e l)`.  Those hypotheses
are unsatisfiable for the honest modes of the box ↔ model bridge (see
`Submission/Work/BoseBoxFock/FINDING_continuous_hypotheses_UNSATISFIABLE.md`): the condensate mode is
a.e. the box indicator, which has no continuous representative.  The weak bundle replaces them by

* `hmeas : ∀ l, Measurable (e l)`,
* `hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C` (everywhere bounded),
* `hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ`.

This file proves the weak twin of the base instance `Work.BoseBoxFock.GenLin_boxSlotSum`:
at the weak bundle, the first-quantised slot sum `boxSlotSum e T` preserves good states and is
`ℂ`-linear on them (`GenLin_boxSlotSum_weak`).  Its three components are read off the packaged
`Work.MB.boxSlotSum_bdd`:

* the good-state component from the measurability/boundedness conjunct;
* additivity and `ℂ`-homogeneity on good states from the weak linearity conjunct, instantiated at
  the two-element index set `Fin 2` (the same reduction the strong instance uses).

The target `AVgen_add_I_smul_ae` then follows **without a single new row argument**: every row of
`AVgen` is a real multiple of a one-body slot sum `boxSlotSum e T` or of a composition of two of
them, so `Work.BoseBoxFock.GenLin_AVgen` (which is stated for an *arbitrary* base `B` with
`GenLin (B T)`) can be instantiated at the weak instance, exactly as in the strong file.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.MB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Work.BoseB4 Work.BoseDict

/-! ## 1. The weak base instance `GenLin (boxSlotSum e T)` -/

/-- **The weak twin of `Work.BoseBoxFock.GenLin_boxSlotSum`.**  At the weak (measurable, everywhere
bounded, box-supported) mode bundle, the first-quantised slot sum `boxSlotSum e T` preserves good
states and is `ℂ`-linear on them. -/
theorem GenLin_boxSlotSum_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseBoxFock.GenLin
      (fun Θ : Work.BoseDict.Xn d → ℂ => Work.BoseDict.boxSlotSum e T Θ) := by
  obtain ⟨hlin, hreg⟩ := boxSlotSum_bdd hmeas hbdE hsupp T
  refine ⟨?_, ?_, ?_⟩
  · -- `RowGood`: the state is measurable and everywhere bounded
    intro Θ hΘ
    obtain ⟨hm, ⟨C, -, hC⟩, -⟩ := hreg Θ hΘ.1 hΘ.2
    exact ⟨hm, C, hC⟩
  · -- additivity on good states
    intro Φ Ψ hΦ hΨ
    have h := hlin (Finset.univ : Finset (Fin 2)) (fun _ : Fin 2 => (1 : ℂ))
      (fun i : Fin 2 => if i = 0 then Φ else Ψ)
      (fun i => by
        by_cases hi : i = 0
        · simpa [hi] using hΦ.1
        · simpa [hi] using hΨ.1)
      (fun i => by
        by_cases hi : i = 0
        · simpa [hi] using hΦ.2
        · simpa [hi] using hΨ.2)
    have h1 : (fun x : Work.BoseDict.Xn d => Finset.sum Finset.univ
        (fun i : Fin 2 =>
          (fun _ : Fin 2 => (1 : ℂ)) i •
            (fun i : Fin 2 => if i = 0 then Φ else Ψ) i x))
        = Φ + Ψ := by
      funext x
      simp
    have h2 : (fun x : Work.BoseDict.Xn d => Finset.sum Finset.univ
        (fun i : Fin 2 =>
          (fun _ : Fin 2 => (1 : ℂ)) i •
            Work.BoseDict.boxSlotSum e T
              ((fun i : Fin 2 => if i = 0 then Φ else Ψ) i) x))
        = Work.BoseDict.boxSlotSum e T Φ + Work.BoseDict.boxSlotSum e T Ψ := by
      funext x
      simp
    rw [← h1, h, h2]
  · -- `ℂ`-homogeneity on good states
    intro c Φ hΦ
    have h := hlin (Finset.univ : Finset (Fin 2)) (fun i : Fin 2 => if i = 0 then c else 0)
      (fun _ : Fin 2 => Φ) (fun _ => hΦ.1) (fun _ => hΦ.2)
    have h1 : (fun x : Work.BoseDict.Xn d => Finset.sum Finset.univ
        (fun i : Fin 2 =>
          (fun i : Fin 2 => if i = 0 then c else 0) i • (fun _ : Fin 2 => Φ) i x))
        = c • Φ := by
      funext x
      simp
    have h2 : (fun x : Work.BoseDict.Xn d => Finset.sum Finset.univ
        (fun i : Fin 2 =>
          (fun i : Fin 2 => if i = 0 then c else 0) i •
            Work.BoseDict.boxSlotSum e T ((fun _ : Fin 2 => Φ) i) x))
        = c • Work.BoseDict.boxSlotSum e T Φ := by
      funext x
      simp
    rw [← h1, h, h2]

/-! ## 2. The target -/

theorem AVgen_add_I_smul_ae {m n : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (Θ₁ Θ₂ : Work.BoseDict.Xn n → ℂ)
    (h₁ : Work.BoseBoxFock.SlotGood Θ₁) (h₂ : Work.BoseBoxFock.SlotGood Θ₂) :
    Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
        f g T_NH PHs E gHat0 (Θ₁ + Complex.I • Θ₂)
      = Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
          (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
          f g T_NH PHs E gHat0 Θ₁
        + Complex.I • Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
            (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
            f g T_NH PHs E gHat0 Θ₂ := by
  have hlin : Work.BoseBoxFock.GenLin
      (Work.BoseBoxFock.AVgen (ι := Fin n) (fun T => Work.BoseDict.boxSlotSum e T)
        (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
        f g T_NH PHs E gHat0) :=
    Work.BoseBoxFock.GenLin_AVgen (fun T => Work.BoseDict.boxSlotSum e T)
      (fun T => GenLin_boxSlotSum_weak (d := n) hmeas hbdE hsupp T)
      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)) f g T_NH PHs E gHat0
  rw [hlin.add Θ₁ (Complex.I • Θ₂) h₁ (Work.BoseBoxFock.SlotGood.smul Complex.I h₂),
    hlin.smul Complex.I Θ₂ h₂]

end Work.MB
