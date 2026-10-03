import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.coordP_abel`: the Abel equation `φ_f (w+1) = f (φ_f w)` on the maximal domain

This file proves the two facts that make the level-defined coordinate `coordP` of
`Submission.Work.Pert.MaxDom` (Shishikura (4.2.1)) usable:

* `coordP f Df τ Φ Q w ∈ Df` — the value at `w` stays inside the domain of `f`;
* `coordP f Df τ Φ Q (w+1) = f (coordP f Df τ Φ Q w)` — the Abel equation.

Setting `n = mIdxP f Df τ Φ Q w` (the *minimal* admissible level of `w`) and
`n' = mIdxP f Df τ Φ Q (w+1)`, and choosing `ζ ∈ Q`, `ζ' ∈ Q` with

`Φ ζ = w - n`, `Φ ζ' = (w+1) - n'` (`mIdxP_spec`), the values are
`coordP … w = f^[n] (τ ζ)` and `coordP … (w+1) = f^[n'] (τ ζ')` — because the seed value
`seedP τ Φ Q (w-n) = τ (invOn Φ Q (w-n)) = τ ζ` is determined by `hinj`.

The whole content is the comparison of the two seeds.  `hOrb` says that any point of `Q` whose
`Φ`-value is a nonnegative integer translate of `Φ`-value of another point of `Q` is the
corresponding iterate, *and that the whole walk stays in `Q`*.  This gives two regimes:

* `n' ≤ n+1`: `Φ ζ' = Φ ζ + k` with `k = n+1-n' ≥ 0`, so `F^[k] ζ = ζ'` and `τ ζ' = f^[k] (τ ζ)`
  (`tau_iterate_of_walk`).  Then `coordP … (w+1) = f^[n'] (f^[k] (τ ζ)) = f^[n+1] (τ ζ)`, and
  `coordP … w = f^[n] (τ ζ) = f^[n'-1] (τ ζ')` is in `Df` because `n'-1 < n'` and `n'` is a good
  level of `w+1` — unless `n' = 0`, when `GoodP` gives no orbit information and one instead uses
  `hseed` at the point `F^[n] ζ ∈ Q`, whose `Φ`-value is `w` (so `w ∈ Φ '' Q` and
  `seedP τ Φ Q w = τ (F^[n] ζ) = f^[n] (τ ζ)`).
* `n+1 < n'`: symmetrically `Φ ζ = Φ ζ' + k` with `k = n'-n-1 > 0`, so `F^[k] ζ' = ζ` and
  `τ ζ = f^[k] (τ ζ')`; then `coordP … w = f^[n'-1] (τ ζ') ∈ Df` and
  `coordP … (w+1) = f^[n'] (τ ζ') = f^[n+1+k] (τ ζ') = f^[n+1] (τ ζ) = f (coordP … w)`.

(The hypotheses are slightly stronger than needed: the orbit condition `hzworb` of the *minimal*
level of `w` is never used, only the existence of the level and the orbit condition at a level of
`w+1`.)
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-- Iterating `τ ∘ F = f ∘ τ` along a walk: if `F^[j] ζ ∈ Q` for `j ≤ n` and `τ (F z) = f (τ z)`
on `Q`, then `τ (F^[n] ζ) = f^[n] (τ ζ)`. -/
lemma tau_iterate_of_walk {f F τ : ℂ → ℂ} {Q : Set ℂ} {ζ : ℂ} {n : ℕ}
    (hwalk : ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q) (hτF : ∀ z ∈ Q, τ (F z) = f (τ z)) :
    τ (F^[n] ζ) = f^[n] (τ ζ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hwalkk : ∀ j : ℕ, j ≤ k → F^[j] ζ ∈ Q := fun j hj => hwalk j (by omega)
    have hkQ : F^[k] ζ ∈ Q := hwalk k (by omega)
    rw [Function.iterate_succ_apply', hτF (F^[k] ζ) hkQ, ih hwalkk]
    exact (Function.iterate_succ_apply' f k (τ ζ)).symm

/-- The seed value `seedP τ Φ Q w = τ (invOn Φ Q w)` at an image point is determined by `hinj`:
if `ζ ∈ Q` and `Φ ζ = w` then `seedP τ Φ Q w = τ ζ`. -/
lemma seedP_eq_of_mem {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w ζ : ℂ} (hinj : Set.InjOn Φ Q)
    (h : ∃ z ∈ Q, Φ z = w) (hζ : ζ ∈ Q) (hΦ : Φ ζ = w) : seedP τ Φ Q w = τ ζ := by
  rw [seedP, invOn_eq hinj h hζ hΦ]

theorem coordP_abel {f : ℂ → ℂ} {Df : Set ℂ} {F τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ} (hinj : Set.InjOn Φ Q) (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1) (hτF : ∀ z ∈ Q, τ (F z) = f (τ z)) (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) → (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z') (hseed : ∀ u ∈ Φ '' Q, seedP τ Φ Q u ∈ Df) (hw : w ∈ DphiP f Df τ Φ Q) (hw1 : w + 1 ∈ DphiP f Df τ Φ Q) : coordP f Df τ Φ Q w ∈ Df ∧ coordP f Df τ Φ Q (w + 1) = f (coordP f Df τ Φ Q w) := by
  set n := mIdxP f Df τ Φ Q w with hn
  set n' := mIdxP f Df τ Φ Q (w + 1) with hn'
  obtain ⟨hzw, hzworb⟩ := mIdxP_spec hw
  obtain ⟨hzw1, hzw1orb⟩ := mIdxP_spec hw1
  obtain ⟨ζ, hζQ, hζΦ⟩ := hzw
  obtain ⟨ζ', hζ'Q, hζ'Φ⟩ := hzw1
  have hζΦn : Φ ζ = w - (n : ℂ) := by rw [hn]; exact hζΦ
  have hζ'Φn : Φ ζ' = (w + 1) - (n' : ℂ) := by rw [hn']; exact hζ'Φ
  have hseedw : seedP τ Φ Q (w - (n : ℂ)) = τ ζ :=
    seedP_eq_of_mem hinj ⟨ζ, hζQ, hζΦn⟩ hζQ hζΦn
  have hseedw1 : seedP τ Φ Q ((w + 1) - (n' : ℂ)) = τ ζ' :=
    seedP_eq_of_mem hinj ⟨ζ', hζ'Q, hζ'Φn⟩ hζ'Q hζ'Φn
  have hcw : coordP f Df τ Φ Q w = f^[n] (τ ζ) := by
    rw [coordP_self, ← hn, hseedw]
  have hcw1 : coordP f Df τ Φ Q (w + 1) = f^[n'] (τ ζ') := by
    rw [coordP_self, ← hn', hseedw1]
  have hzw1orb' : ∀ j : ℕ, j < n' → f^[j] (τ ζ') ∈ Df := by
    intro j hj
    have h := hzw1orb j (by rw [← hn']; exact hj)
    rwa [← hn', hseedw1] at h
  rcases le_or_gt n' (n + 1) with hcase | hcase
  · -- `n' ≤ n+1`: `ζ' = F^[k] ζ` with `k = n+1-n'`
    set k := n + 1 - n' with hk
    have hnk : n' + k = n + 1 := by omega
    have hΦk : Φ ζ' = Φ ζ + (k : ℂ) := by
      have hcast : (n' : ℂ) + (k : ℂ) = (n : ℂ) + 1 := by
        have h := congrArg (fun m : ℕ => (m : ℂ)) hnk
        push_cast at h
        exact h
      have hsub : w + 1 - (n' : ℂ) = (w - (n : ℂ)) + (k : ℂ) := by
        calc w + 1 - (n' : ℂ) = w + 1 - ((n' : ℂ) + (k : ℂ)) + (k : ℂ) := by ring
          _ = w + 1 - ((n : ℂ) + 1) + (k : ℂ) := by rw [hcast]
          _ = (w - (n : ℂ)) + (k : ℂ) := by ring
      rw [hζ'Φn, hζΦn, hsub]
    obtain ⟨hwalkk, hfink⟩ := hOrb ζ hζQ ζ' hζ'Q k hΦk
    have hτζ' : τ ζ' = f^[k] (τ ζ) := by
      rw [← hfink, tau_iterate_of_walk hwalkk hτF]
    have hb : coordP f Df τ Φ Q (w + 1) = f (coordP f Df τ Φ Q w) := by
      rw [hcw1, hcw, hτζ', ← Function.iterate_add_apply, hnk]
      exact Function.iterate_succ_apply' f n (τ ζ)
    rcases Nat.eq_zero_or_pos n' with h0 | hpos
    · -- `n' = 0`: no orbit information from `GoodP`; use `hseed` at `w ∈ Φ '' Q`
      have hkval : k = n + 1 := by omega
      have hwalkn : ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q := fun j hj => hwalkk j (by omega)
      have hξQ : F^[n] ζ ∈ Q := hwalkn n le_rfl
      have hΦξ : Φ (F^[n] ζ) = w := by
        rw [abel_iter hwalkn hab, hζΦn]
        ring
      have hmem : w ∈ Φ '' Q := ⟨F^[n] ζ, hξQ, hΦξ⟩
      have hsd : seedP τ Φ Q w = f^[n] (τ ζ) := by
        rw [seedP_eq_of_mem hinj hmem hξQ hΦξ, tau_iterate_of_walk hwalkn hτF]
      refine ⟨?_, hb⟩
      rw [hcw, ← hsd]
      exact hseed w hmem
    · -- `n' ≥ 1`: `n = (n'-1) + k`, so `coordP … w = f^[n'-1] (τ ζ')`
      have hn_eq : n = (n' - 1) + k := by omega
      refine ⟨?_, hb⟩
      rw [hcw, hn_eq, Function.iterate_add_apply, ← hτζ']
      exact hzw1orb' (n' - 1) (by omega)
  · -- `n+1 < n'`: `ζ = F^[k] ζ'` with `k = n'-n-1`
    set k := n' - (n + 1) with hk
    have hnk : n + 1 + k = n' := by omega
    have hΦk : Φ ζ = Φ ζ' + (k : ℂ) := by
      have hcast : (n : ℂ) + 1 + (k : ℂ) = (n' : ℂ) := by
        have h := congrArg (fun m : ℕ => (m : ℂ)) hnk
        push_cast at h
        exact h
      have hsub : w - (n : ℂ) = (w + 1 - (n' : ℂ)) + (k : ℂ) := by
        calc w - (n : ℂ) = w + 1 - ((n : ℂ) + 1 + (k : ℂ)) + (k : ℂ) := by ring
          _ = w + 1 - (n' : ℂ) + (k : ℂ) := by rw [hcast]
          _ = (w + 1 - (n' : ℂ)) + (k : ℂ) := by ring
      rw [hζΦn, hζ'Φn, hsub]
    obtain ⟨hwalkk, hfink⟩ := hOrb ζ' hζ'Q ζ hζQ k hΦk
    have hτζ : τ ζ = f^[k] (τ ζ') := by
      rw [← hfink, tau_iterate_of_walk hwalkk hτF]
    have ha : coordP f Df τ Φ Q w ∈ Df := by
      have hn_eq : n = (n' - 1) - k := by omega
      have hkn : ((n' - 1) - k) + k = n' - 1 := by omega
      rw [hcw, hn_eq, hτζ, ← Function.iterate_add_apply, hkn]
      exact hzw1orb' (n' - 1) (by omega)
    have hb : coordP f Df τ Φ Q (w + 1) = f (coordP f Df τ Φ Q w) := by
      rw [hcw1, hcw, ← hnk, Function.iterate_add_apply, ← hτζ]
      exact Function.iterate_succ_apply' f n (τ ζ)
    exact ⟨ha, hb⟩

end

end Work.Pert
