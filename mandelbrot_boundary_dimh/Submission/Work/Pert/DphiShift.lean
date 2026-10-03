import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Setup

/-!
# `Work.Pert.DphiShift` — the shift behaviour of `DphiP`

`DphiP f Df τ Φ Q = {w | GoodP f Df τ Φ Q w}` with

```
GoodP f Df τ Φ Q w  ≡  ∃ n : ℕ, w - n ∈ Φ '' Q ∧ ∀ j < n, f^[j] (seedP τ Φ Q (w - n)) ∈ Df
```

(`MaxDom`).  This file records the two halves of `IsTInvariant (DphiP …)`, which the repaired
return-map domain `Pert.retDR = DphiP ∩ T-sat (Φ '' Wa)` needs for `PertData.R_equiv`:

* `DphiP_add_one` — the **forward** half.  It is a pure level upgrade: a level-`n` witness for `w`
  becomes a level-`n + 1` witness for `w + 1` (same base point `w - n = (w + 1) - (n + 1)`), and
  the only new walk condition is the iterate `f^n` of the seed, which is supplied by the
  hypothesis `hDf` — in the intended application this is exactly `PertData.φ_abel`'s conclusion
  `φ w ∈ Df` (equivalently `coordP f Df τ Φ Q w ∈ Df`).
* the **backward** half is *not* free and is deliberately NOT asserted here: from a witness for
  `w + 1` one gets a witness for `w` only after showing that `w` itself has a level, i.e. that the
  gate image `Φ '' Q` is closed far enough to the left (`Φ ς' - 1 - n' ∈ Φ '' Q` for some
  `n' ≥ 0`) — the same "gate walks in both directions" sub-fact that
  `NOTES_pert2_session15.md` §5.2 isolates.  See §5.4 of those notes.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- **The forward half of `IsTInvariant (DphiP …)`**: an admissible level of `w` gives an
admissible level of `w + 1`.  The extra walk condition is `f^n` of the seed, supplied by `hDf`. -/
theorem DphiP_add_one {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (hDf : ∀ n : ℕ, w - (n : ℂ) ∈ Φ '' Q →
      (∀ j : ℕ, j < n → f^[j] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df) →
      f^[n] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df)
    (hw : w ∈ DphiP f Df τ Φ Q) : w + 1 ∈ DphiP f Df τ Φ Q := by
  obtain ⟨n, hn, hwalk⟩ := hw
  have key : w + 1 - ((n + 1 : ℕ) : ℂ) = w - (n : ℂ) := by push_cast; ring
  refine ⟨n + 1, ?_, ?_⟩
  · rw [key]; exact hn
  · intro j hj
    rw [key]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact hwalk j hlt
    · rw [heq]
      exact hDf n hn hwalk

/-! ## The usable form of the gate-image leftward closure (row of §5.2/§5.4)

The *conditional* form: if `z` has a `k`-step backward walk inside the gate from a point `z'`, then
`Φ z - k` is again in the gate image.  This is what §5.2's blocked case and §5.4's backward
`DphiP` shift both need; only the *geometric* availability of the backward walk (`F^{-k} ς ∈ Q`
for the needed `k`) remains open, and that needs the near-translation geometry, not the Abel
equation.  (The unconditional form is false: `Qm Ξ α` runs out on the left.) -/

/-- **Gate-image leftward closure, conditional form.**  Given a `k`-step walk `z, F z', …, F^[k] z'`
inside `Q` ending at `z`, the point `Φ z - k` is in `Φ '' Q`. -/
theorem Phi_sub_mem_image {F Φ : ℂ → ℂ} {Q : Set ℂ} {z z' : ℂ} {k : ℕ}
    (habel : ∀ u ∈ Q, F u ∈ Q → Φ (F u) = Φ u + 1)
    (hz' : z' ∈ Q) (hwalk : ∀ j : ℕ, j ≤ k → F^[j] z' ∈ Q) (hfin : F^[k] z' = z) :
    Φ z - (k : ℂ) ∈ Φ '' Q := by
  have h := abel_iter (F := F) (Φ := Φ) (Q := Q) (n := k) (ζ := z') hwalk habel
  refine ⟨z', hz', ?_⟩
  rw [← hfin, h]
  ring

/-- **(a) Backward `DphiP` shift, `n >= 1` case** (see `NOTES_pert2_session15.md` 5.15): if
`w + 1` has an admissible level `n >= 1`, then the *same* base point is an admissible level `n - 1`
for `w`.  Mirror of `DphiP_add_one`; the `n = 0` case needs the gate preimage and is treated
separately. -/
theorem mem_DphiP_of_witness_succ {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    {n : ℕ} (hn : 1 ≤ n)
    (hbase : (w + 1) - (n : ℂ) ∈ Φ '' Q)
    (hwalk : ∀ j : ℕ, j < n → f^[j] (seedP τ Φ Q ((w + 1) - (n : ℂ))) ∈ Df) :
    w ∈ DphiP f Df τ Φ Q := by
  have hcast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  have key : w - ((n - 1 : ℕ) : ℂ) = (w + 1) - (n : ℂ) := by
    rw [hcast]; ring
  refine ⟨n - 1, ?_, ?_⟩
  · rw [key]; exact hbase
  · intro j hj
    rw [key]
    exact hwalk j (by omega)

/-- **(b) Backward `DphiP` shift, `n = 0` case** (`NOTES_pert2_session15.md` 5.15): if `w + 1 = Φ ς`
with `ς` a gate point having a one-step preimage `z'` inside the gate, then `w` is at level `0`.
Note the instantiation: `Phi_sub_mem_image` is applied at the **gate point** `ς` (not at `w + 1`,
which lives on the coordinate side), with `k = 1`. -/
theorem mem_DphiP_of_phi_eq_add_one {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ F : ℂ → ℂ} {Q : Set ℂ}
    {w ς z' : ℂ}
    (habel : ∀ u ∈ Q, F u ∈ Q → Φ (F u) = Φ u + 1)
    (hς : ς ∈ Q) (hbase : Φ ς = w + 1)
    (hz' : z' ∈ Q) (hFz' : F z' ∈ Q) (hfin : F z' = ς) :
    w ∈ DphiP f Df τ Φ Q := by
  have hwalk : ∀ j : ℕ, j ≤ 1 → F^[j] z' ∈ Q := by
    intro j hj
    interval_cases j
    · simpa using hz'
    · simpa using hFz'
  have h := Phi_sub_mem_image (F := F) (Φ := Φ) (Q := Q) (z := ς) (z' := z') (k := 1)
    habel hz' hwalk hfin
  obtain ⟨ζ', hζ'Q, hζ'eq⟩ := h
  have : Φ ζ' = w := by rw [hζ'eq, hbase]; ring
  rw [← this]
  exact ⟨0, ⟨ζ', hζ'Q, by simp⟩, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- **`IsTInvariant (DphiP f Df τ Φ Q)`**, recombined from the two cases of 5.15/5.16.

Forward: `DphiP_add_one`.  Backward: case split on the level `n` of the witness for `w + 1` --
`n = m + 1` goes through `mem_DphiP_of_witness_succ` (a), `n = 0` through
`mem_DphiP_of_phi_eq_add_one` (b) with the one-step gate preimage `hOnestep` (supplied
geometrically by `shift_subset_image` + `ball_subset_Qm_of_margin`, via `backward_walk_exists` at
`k = 1`).  `hDf` is the forward direction's extra walk condition (`PertData.phi_abel`'s conclusion
`phi w in Df` in the application). -/
theorem isTInvariant_DphiP {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ F : ℂ → ℂ} {Q : Set ℂ}
    (habel : ∀ u ∈ Q, F u ∈ Q → Φ (F u) = Φ u + 1)
    (hOnestep : ∀ ς ∈ Q, ∃ z' ∈ Q, F z' ∈ Q ∧ F z' = ς)
    (hDf : ∀ w : ℂ, w ∈ DphiP f Df τ Φ Q →
      ∀ n : ℕ, w - (n : ℂ) ∈ Φ '' Q →
        (∀ j : ℕ, j < n → f^[j] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df) →
        f^[n] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df) :
    IsTInvariant (DphiP f Df τ Φ Q) := by
  intro w
  constructor
  · -- forward: `w ∈ DphiP → w + 1 ∈ DphiP`
    intro hw
    exact DphiP_add_one (hDf w hw) hw
  · -- backward: `w + 1 ∈ DphiP → w ∈ DphiP`
    intro hw1
    obtain ⟨n, hbase, hwalk⟩ := hw1
    rcases n with _ | m
    · -- `n = 0`: `w + 1 in Φ '' Q`, use the gate point
      simp only [Nat.cast_zero, sub_zero] at hbase
      obtain ⟨ς, hςQ, hςeq⟩ := hbase
      obtain ⟨z', hz'Q, hFz'Q, hfin⟩ := hOnestep ς hςQ
      exact mem_DphiP_of_phi_eq_add_one (f := f) (Df := Df) (τ := τ) (Φ := Φ) (F := F)
        (Q := Q) habel hςQ hςeq hz'Q hFz'Q hfin
    · -- `n = m + 1`: (a)
      exact mem_DphiP_of_witness_succ (f := f) (Df := Df) (τ := τ) (Φ := Φ) (Q := Q)
        (w := w) (n := m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hbase hwalk

end

end Work.Pert
