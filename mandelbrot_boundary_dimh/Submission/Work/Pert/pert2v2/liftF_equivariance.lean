import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.pert2v2.tauC_resonance

/-!
# `Work.Pert.pert2v2.liftF_equivariance` — the deck equivariance of the lift `liftF`

`τ_f = tauC σ α` is the universal cover of `ℂ ∖ {0, σ}` with deck group `(1/α)ℤ`, and
`F_f = liftF u σ α` is the lift of the perturbed germ.  Two facts are used everywhere in the
`pert2v2` R-block:

* **the lift commutes with the deck translations**:
  `liftF u σ α (w + k/α) = liftF u σ α w + k/α` for every `k : ℤ`
  (`liftF_add_int_div`; the case `k = -1` is the basic `Work.Pert.liftF_sub_period`);
* hence the whole **walk** commutes: `F^[n] (w + c) = F^[n] w + c` for `c ∈ (1/α)ℤ`
  (`iterate_add_shift`), and the walk congruence
  `F^[N + l] W = u + c → ∃ V, F^[N] V = u` (`walk_congruence`).

The last one is the formal content of the "τ-coset" bookkeeping of the low band: the level-`(-N)`
presentation of `Φ u` is the deck translate of the level-`l` presentation of `Φ u`.
-/

namespace Work.Pert.pert2v2

open Complex

noncomputable section

/-! ## The deck equivariance -/

/-- `sfun` sees `w` only through `τ_f w`, hence is periodic with period `k/α`. -/
theorem sfun_add_int_div (u : ℂ → ℂ) (σ α : ℂ) (hα : α ≠ 0) (k : ℤ) (w : ℂ) :
    Work.Pert.sfun u σ α (w + (k : ℂ) / α) = Work.Pert.sfun u σ α w := by
  simp only [Work.Pert.sfun, tauC_add_int_div σ α hα k w]

/-- **The lift commutes with the deck translations**: `F_f (w + k/α) = F_f w + k/α`. -/
theorem liftF_add_int_div (u : ℂ → ℂ) (σ α : ℂ) (hα : α ≠ 0) (k : ℤ) (w : ℂ) :
    Work.Pert.liftF u σ α (w + (k : ℂ) / α) = Work.Pert.liftF u σ α w + (k : ℂ) / α := by
  unfold Work.Pert.liftF
  rw [sfun_add_int_div u σ α hα k w]
  ring

/-! ## The walk of a commuting map -/

/-- A map commuting with `z ↦ z + c` commutes with `z ↦ z - c`. -/
theorem sub_shift_of_add_shift {F : ℂ → ℂ} {c : ℂ}
    (h : ∀ z : ℂ, F (z + c) = F z + c) (z : ℂ) : F (z - c) = F z - c := by
  have h1 : F (z - c) + c = F z := by
    have h2 := h (z - c)
    rw [sub_add_cancel] at h2
    exact h2.symm
  calc F (z - c) = F (z - c) + c - c := (add_sub_cancel_right _ _).symm
    _ = F z - c := by rw [h1]

/-- Iterating the commutation with `z ↦ z + c`. -/
theorem iterate_add_shift {F : ℂ → ℂ} {c : ℂ} (h : ∀ z : ℂ, F (z + c) = F z + c) :
    ∀ (n : ℕ) (z : ℂ), F^[n] (z + c) = F^[n] z + c := by
  intro n
  induction n with
  | zero => intro z; simp
  | succ k ih =>
    intro z
    rw [Function.iterate_succ_apply', ih, h, Function.iterate_succ_apply']

/-- Iterating the commutation with `z ↦ z - c`. -/
theorem iterate_sub_shift {F : ℂ → ℂ} {c : ℂ} (h : ∀ z : ℂ, F (z + c) = F z + c) :
    ∀ (n : ℕ) (z : ℂ), F^[n] (z - c) = F^[n] z - c := by
  intro n
  induction n with
  | zero => intro z; simp
  | succ k ih =>
    intro z
    rw [Function.iterate_succ_apply', ih, sub_shift_of_add_shift h, Function.iterate_succ_apply']

/-- Iterating the deck equivariance of `liftF`. -/
theorem liftF_iterate_add_int_div (u : ℂ → ℂ) (σ α : ℂ) (hα : α ≠ 0) (k : ℤ) :
    ∀ (n : ℕ) (z : ℂ),
      (Work.Pert.liftF u σ α)^[n] (z + (k : ℂ) / α)
        = (Work.Pert.liftF u σ α)^[n] z + (k : ℂ) / α :=
  iterate_add_shift (fun z => liftF_add_int_div u σ α hα k z)

/-- Iterating the deck equivariance of `liftF` in the `-` direction. -/
theorem liftF_iterate_sub_int_div (u : ℂ → ℂ) (σ α : ℂ) (hα : α ≠ 0) (k : ℤ) :
    ∀ (n : ℕ) (z : ℂ),
      (Work.Pert.liftF u σ α)^[n] (z - (k : ℂ) / α)
        = (Work.Pert.liftF u σ α)^[n] z - (k : ℂ) / α :=
  iterate_sub_shift (fun z => liftF_add_int_div u σ α hα k z)

/-! ## The walk congruence -/

/-- **The walk congruence.**  If `F` commutes with `z ↦ z + c` and `F^[N + l] W = u + c`, then the
deck translate `V := F^[l] (W - c)` satisfies `F^[N] V = u`.

This is the formal content of the "τ-coset" bookkeeping: an identity at the level `N + l` of a gate
point, together with the deck equivariance, produces a gate point of the level-`N` point. -/
theorem walk_congruence {F : ℂ → ℂ} {c u W : ℂ} {N l : ℕ}
    (h : ∀ z : ℂ, F (z + c) = F z + c) (htop : F^[N + l] W = u + c) :
    ∃ V : ℂ, F^[N] V = u := by
  refine ⟨F^[l] (W - c), ?_⟩
  have h1 : F^[N] (F^[l] (W - c)) = F^[N + l] (W - c) := by
    rw [Function.iterate_add_apply]
  have h2 : F^[N + l] (W - c) = F^[N + l] W - c := iterate_sub_shift h (N + l) W
  rw [h1, h2, htop]
  ring

end

end Work.Pert.pert2v2
