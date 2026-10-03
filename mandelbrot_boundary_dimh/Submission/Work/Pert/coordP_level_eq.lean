import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.coordP_level_eq`: `φ_f` at any legal level

The value `coordP f Df τ Φ Q w` of the maximal-domain coordinate is `f^{mIdx} (τ (Φ⁻¹ (w - mIdx)))`
at the **minimal** level `mIdx`; this file shows that any *legal* level `(n, ζ)` of `w` — `ζ ∈ Q`,
`Φ ζ = w - n`, with the `f`-orbit of `τ ζ` inside `Df` for `j < n` — gives the same value:

  `coordP f Df τ Φ Q w = f^[n] (τ ζ)`.

The key point is that two levels of the same point `w` are related by an iterate of the lift `F`
(`hOrb`): if `ζ` is at level `n`, `ζm` at level `m` and `m ≥ n`, then `ζ = F^[m-n] ζm`, and the
intertwining `τ ∘ F = f ∘ τ` along the legal walk (`hOrb` supplies the walk) converts the iterate
of `τ` of `ζm` into the iterate of `τ` of `ζ`.  The `m ≤ n` case is symmetric.
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-- Iterating `τ ∘ F = f ∘ τ` along a legal walk: if `F^[j] ζ ∈ Q` for `j ≤ k` then
`τ (F^[k] ζ) = f^[k] (τ ζ)`. -/
lemma tau_walk_iterate {f F τ : ℂ → ℂ} {Q : Set ℂ} {ζ : ℂ} {k : ℕ}
    (hwalk : ∀ j : ℕ, j ≤ k → F^[j] ζ ∈ Q) (hτF : ∀ z ∈ Q, τ (F z) = f (τ z)) :
    τ (F^[k] ζ) = f^[k] (τ ζ) := by
  induction k with
  | zero => simp
  | succ j ih =>
    have hwalkj : ∀ i : ℕ, i ≤ j → F^[i] ζ ∈ Q := fun i hi => hwalk i (by omega)
    have hjQ : F^[j] ζ ∈ Q := hwalk j (by omega)
    rw [Function.iterate_succ_apply', hτF (F^[j] ζ) hjQ, ih hwalkj]
    exact (Function.iterate_succ_apply' f j (τ ζ)).symm

/-- The seed value `seedP τ Φ Q u = τ (invOn Φ Q u)` at an image point is `τ` of any preimage in
`Q` (`hinj` makes the chosen preimage irrelevant). -/
lemma seedP_eq_of_mem' {τ Φ : ℂ → ℂ} {Q : Set ℂ} {u ζ : ℂ} (hinj : Set.InjOn Φ Q)
    (hu : ∃ z ∈ Q, Φ z = u) (hζ : ζ ∈ Q) (hΦ : Φ ζ = u) : seedP τ Φ Q u = τ ζ := by
  rw [seedP, invOn_eq hinj hu hζ hΦ]

/-- If `z'` is the point of `Q` at `Φ`-level `k` above `z`, then `τ z' = f^[k] (τ z)`
(`hOrb` provides both the identification `F^[k] z = z'` and the legal walk of `z`). -/
lemma tau_eq_iterate_of_shift {f F τ Φ : ℂ → ℂ} {Q : Set ℂ} {z z' : ℂ} {k : ℕ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hz : z ∈ Q) (hz' : z' ∈ Q) (hΦ : Φ z' = Φ z + (k : ℂ)) :
    τ z' = f^[k] (τ z) := by
  obtain ⟨hwalk, hfin⟩ := hOrb z hz z' hz' k hΦ
  rw [← hfin]
  exact tau_walk_iterate hwalk hτF

theorem coordP_level_eq {f : ℂ → ℂ} {Df : Set ℂ} {F τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ} (hinj : Set.InjOn Φ Q) (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1) (hτF : ∀ z ∈ Q, τ (F z) = f (τ z)) (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) → (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z') (h : GoodP f Df τ Φ Q w) {n : ℕ} {ζ : ℂ} (hζ : ζ ∈ Q) (hΦ : Φ ζ = w - (n : ℂ)) (hn : ∀ j : ℕ, j < n → f^[j] (τ ζ) ∈ Df) : coordP f Df τ Φ Q w = f^[n] (τ ζ) := by
  -- the minimal level of `w`
  obtain ⟨himg, -⟩ := mIdxP_spec h
  obtain ⟨ζm, hζmQ, hζmΦ⟩ := himg
  obtain ⟨m, hm⟩ : ∃ m : ℕ, mIdxP f Df τ Φ Q w = m := ⟨_, rfl⟩
  rw [hm] at hζmΦ
  have hseed : seedP τ Φ Q (w - (m : ℂ)) = τ ζm :=
    seedP_eq_of_mem' hinj ⟨ζm, hζmQ, hζmΦ⟩ hζmQ hζmΦ
  have hcoord : coordP f Df τ Φ Q w = f^[m] (τ ζm) := by
    rw [coordP_self, hm, hseed]
  rcases le_or_gt n m with hnm | hnm
  · -- `ζ` is the `(m - n)`-th iterate of `ζm`
    have hk : n + (m - n) = m := by omega
    have hΦk : Φ ζ = Φ ζm + ((m - n : ℕ) : ℂ) := by
      have hcast : ((n : ℂ)) + ((m - n : ℕ) : ℂ) = (m : ℂ) := by
        have hh := congrArg (fun t : ℕ => (t : ℂ)) hk
        push_cast at hh
        exact hh
      rw [hΦ, hζmΦ, ← hcast]; ring
    have hτζ : τ ζ = f^[m - n] (τ ζm) := tau_eq_iterate_of_shift hτF hOrb hζmQ hζ hΦk
    rw [hcoord, hτζ, ← Function.iterate_add_apply, hk]
  · -- `ζm` is the `(n - m)`-th iterate of `ζ`
    have hk : m + (n - m) = n := by omega
    have hΦk : Φ ζm = Φ ζ + ((n - m : ℕ) : ℂ) := by
      have hcast : ((m : ℂ)) + ((n - m : ℕ) : ℂ) = (n : ℂ) := by
        have hh := congrArg (fun t : ℕ => (t : ℂ)) hk
        push_cast at hh
        exact hh
      rw [hζmΦ, hΦ, ← hcast]; ring
    have hτζm : τ ζm = f^[n - m] (τ ζ) := tau_eq_iterate_of_shift hτF hOrb hζ hζmQ hΦk
    rw [hcoord, hτζm, ← Function.iterate_add_apply, hk]

end

end Work.Pert
