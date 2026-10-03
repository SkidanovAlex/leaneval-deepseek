import Mathlib
import Submission.Work.Pert.pert2v2.norm_iterate_sub_landed_lt
import Submission.Work.Pert.pert2v2.RBlockDefs
import Submission.Work.Pert.pert2v2.level_translate
import Submission.Work.Pert.pert2v2.Rlow_eq_retOf_crux_walk

/-!
# `Work.Pert.pert2v2.HcoincRow` — the coincidence `ζ = F^m ς` at the overlap

The row `hcoinc` of the `hcross` chain (session 40 §3, step (iv)): the crux's landing point
`ζ = invOn τ Qp' (f^m (φ w))` coincides with the *walk endpoint* `F^m ς` of the waist point `ς` of
`w`.  Everything is a triangle inequality plus the fibre structure of `τ_f`:

* both `ζ` and `F^m ς` are `τ`-preimages of the same value (`τ ζ = f^m (τ ς) = τ (F^m ς)` by
  `tau_walk_iterate` along the waist walk);
* they are within `1/‖α‖` of each other (`norm_iterate_sub_landed_lt`: the walk defect
  `‖F^m ς - ς - m‖ ≤ m κ`, the deviation `‖ς - w‖ ≤ C`, the model shift `‖v - w‖ ≤ B`, and the
  located landing point `‖ζ - m - v‖ ≤ 2`);
* hence `ζ - F^m ς ∈ (1/α)ℤ` has modulus `< 1/‖α‖`, so it vanishes
  (`Work.Pert.tauC_inj_of_dist_lt`).

Used by `hcross` (`Rlow_eq_retOf_crux_walk` needs it as the hypothesis `hcoinc`).
-/

namespace Work.Pert.pert2v2

open Work.Pert MandelDim Complex Set

noncomputable section

/-- **The walk endpoint coincides with the crux's landing point.**  If `ζ` is a `τ`-preimage of
`f^m (τ ς)` which is close to the *model* landing point `v + m` (`‖ζ - m - v‖ ≤ 2`), and the walk
`F^j ς` of the waist point stays in the upper gate, then `ζ = F^m ς`.

The four size hypotheses are exactly the shape the crux's data provides:
`C` = the deviation `‖invOn Φ (Qm Ξ α) w - w‖`, `B` = the model orbit shift
`‖τ₀ (f₀^m (d.φ w)) - m - w‖`, `κ` = the near-translation defect (`1/32`), and `hsmall` is a
`δ₀`-condition (the crux's landing time `m` is bounded by a datum-level constant). -/
theorem iterate_eq_of_landed_close {f F : ℂ → ℂ} {Qp : Set ℂ} {σ α : ℂ} {m : ℕ}
    {ς w v ζ : ℂ} {C κ B : ℝ} (hσ : σ ≠ 0) (hα : α ≠ 0)
    (hτF : ∀ z ∈ Qp, Work.Pert.tauC σ α (F z) = f (Work.Pert.tauC σ α z))
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Qp)
    (hτζ : Work.Pert.tauC σ α ζ = f^[m] (Work.Pert.tauC σ α ς))
    (hFm : ‖F^[m] ς - (ς + (m : ℂ))‖ ≤ (m : ℝ) * κ)
    (hw : ‖ς - w‖ ≤ C) (hv : ‖v - w‖ ≤ B) (hζv : ‖ζ - (m : ℂ) - v‖ ≤ 2)
    (hsmall : (C + (m : ℝ) * κ + B + 2) * ‖α‖ < 1) :
    ζ = F^[m] ς := by
  have hdist : ‖F^[m] ς - ζ‖ < 1 / ‖α‖ :=
    norm_iterate_sub_landed_lt (F := F) (ς := ς) (ζ := ζ) (w := w) (v := v) (α := α)
      (m := m) (C := C) (κ := κ) (B := B) hα hw hFm hv hζv hsmall
  have hτeq : Work.Pert.tauC σ α (F^[m] ς) = Work.Pert.tauC σ α ζ := by
    rw [Work.Pert.tau_walk_iterate hwalk hτF, hτζ]
  exact (Work.Pert.tauC_inj_of_dist_lt σ α (F^[m] ς) ζ hσ hα hdist hτeq).symm

/-- **The `invOn` form of the coincidence.**  With `ζ := invOn τ Qp' (f^m (τ ς))` the hypothesis
`τ ζ = f^m (τ ς)` is automatic; the only remaining inputs are the located bound on the *crux's*
chosen landing point and the sizes. -/
theorem invOn_eq_iterate_of_close {f F : ℂ → ℂ} {Qp Qp' : Set ℂ} {σ α : ℂ} {m : ℕ}
    {ς w v : ℂ} {C κ B : ℝ} (hσ : σ ≠ 0) (hα : α ≠ 0)
    (hτF : ∀ z ∈ Qp, Work.Pert.tauC σ α (F z) = f (Work.Pert.tauC σ α z))
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Qp)
    (hland : f^[m] (Work.Pert.tauC σ α ς) ∈ Work.Pert.tauC σ α '' Qp')
    (hFm : ‖F^[m] ς - (ς + (m : ℂ))‖ ≤ (m : ℝ) * κ)
    (hw : ‖ς - w‖ ≤ C) (hv : ‖v - w‖ ≤ B)
    (hζv : ‖Work.Pert.invOn (Work.Pert.tauC σ α) Qp' (f^[m] (Work.Pert.tauC σ α ς))
      - (m : ℂ) - v‖ ≤ 2)
    (hsmall : (C + (m : ℝ) * κ + B + 2) * ‖α‖ < 1) :
    Work.Pert.invOn (Work.Pert.tauC σ α) Qp' (f^[m] (Work.Pert.tauC σ α ς)) = F^[m] ς :=
  iterate_eq_of_landed_close (F := F) (Qp := Qp) (σ := σ) (α := α) (m := m)
    (ς := ς) (w := w) (v := v)
    (ζ := Work.Pert.invOn (Work.Pert.tauC σ α) Qp' (f^[m] (Work.Pert.tauC σ α ς)))
    hσ hα hτF hwalk (Work.Pert.invOn_spec hland) hFm hw hv hζv hsmall

/-- **The near-translation defect accumulated along a walk.**  If `F` is a near-translation of
`z ↦ z + 1` with defect `κ` on the gate `Q`, then along a legal walk of length `m` the accumulated
displacement is at most `m κ`:

  `‖F^m ς - (ς + m)‖ ≤ m κ`.

This is the hypothesis `hFm` of `iterate_eq_of_landed_close`, here in the form in which a
`NearTranslationL1` gate supplies it (`‖F z - (z + 1)‖ ≤ 1/32`). -/
theorem iterate_sub_shift_le {F : ℂ → ℂ} {Q : Set ℂ} {ς : ℂ} {m : ℕ} {κ : ℝ}
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Q)
    (hdef : ∀ z ∈ Q, ‖F z - (z + 1)‖ ≤ κ) (hκ : 0 ≤ κ) :
    ‖F^[m] ς - (ς + (m : ℂ))‖ ≤ (m : ℝ) * κ := by
  induction m with
  | zero => simp
  | succ n ih =>
    have hwalkn : ∀ j : ℕ, j ≤ n → F^[j] ς ∈ Q := fun j hj => hwalk j (by omega)
    have hmem : F^[n] ς ∈ Q := hwalk n (by omega)
    have hsplit : F^[n + 1] ς - (ς + ((n + 1 : ℕ) : ℂ))
        = (F (F^[n] ς) - (F^[n] ς + 1)) + (F^[n] ς - (ς + (n : ℂ))) := by
      rw [Function.iterate_succ_apply']; push_cast; ring
    rw [hsplit]
    calc ‖(F (F^[n] ς) - (F^[n] ς + 1)) + (F^[n] ς - (ς + (n : ℂ)))‖
        ≤ ‖F (F^[n] ς) - (F^[n] ς + 1)‖ + ‖F^[n] ς - (ς + (n : ℂ))‖ := norm_add_le _ _
      _ ≤ κ + (n : ℝ) * κ := add_le_add (hdef _ hmem) (ih hwalkn)
      _ = ((n + 1 : ℕ) : ℝ) * κ := by push_cast; ring

/-- **`hcross`: the two pieces agree at a level-`0` overlap point.**  The whole session-40 §3 chain
in one lemma: at the waist point `ς` with `w = ΨE ς`, the crux's clause at `w` (the landing
`f^m (τ ς) ∈ τ '' Qp'`) and the located landing point `ζ = invOn τ Qp' (f^m (τ ς))`
(`‖ζ - m - v‖ ≤ 2`) force `ζ = F^m ς`, whence the low piece equals the high piece
(`Rlow_eq_retOf_crux_walk`).

All the analytic inputs are hypotheses; the design produces them by
`walk_Qp_waist_unified` (`hwalk`), `iterate_sub_shift_le` (`hFm`), the deviation bound
(`hw`), the model orbit shift (`hv`) and the located crux landing point (`hζv`). -/
theorem Rlow_eq_retOf_of_crux {f F ΨE Ψp : ℂ → ℂ} {Df Qp' : Set ℂ} {Ξ : ℝ} {σ α d : ℂ}
    {m : ℕ} {ς v : ℂ} {C κ B : ℝ} (hσ : σ ≠ 0) (hα : α ≠ 0)
    (hE : MandelDim.IsFatouCoordOn F ΨE (Work.Pert.Qm Ξ α))
    (hrel : ∀ z ∈ Work.Pert.Qp Ξ α, Ψp z = ΨE (Work.Pert.Tt α z) - d)
    (hτF : ∀ z ∈ Work.Pert.Qp Ξ α,
      Work.Pert.tauC σ α (F z) = f (Work.Pert.tauC σ α z))
    (hAbel : ∀ z ∈ Work.Pert.Qp Ξ α, F z ∈ Work.Pert.Qp Ξ α → Ψp (F z) = Ψp z + 1)
    (hinjτ : Set.InjOn (Work.Pert.tauC σ α) Qp')
    (hQp'sub : Qp' ⊆ Work.Pert.Qp Ξ α)
    (hς : ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Work.Pert.Qp Ξ α)
    (hland : f^[m] (Work.Pert.tauC σ α ς) ∈ Work.Pert.tauC σ α '' Qp')
    (hFm : ‖F^[m] ς - (ς + (m : ℂ))‖ ≤ (m : ℝ) * κ)
    (hw : ‖ς - ΨE ς‖ ≤ C) (hv : ‖v - ΨE ς‖ ≤ B)
    (hζv : ‖Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
      (f^[m] (Work.Pert.tauC σ α ς)) - (m : ℂ) - v‖ ≤ 2)
    (hsmall : (C + (m : ℝ) * κ + B + 2) * ‖α‖ < 1) :
    Work.Pert.Rlow f Qp' (Work.Pert.tauC σ α) Ψp
        (Work.Pert.coordP f Df (Work.Pert.tauC σ α) ΨE (Work.Pert.Qm Ξ α)) m 0 d (ΨE ς)
      = Work.Pert.retOf ΨE (Work.Pert.Qm Ξ α) α (ΨE ς) := by
  have hcoinc : Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
      (f^[m] (Work.Pert.tauC σ α ς)) = F^[m] ς :=
    invOn_eq_iterate_of_close (F := F) (Qp := Work.Pert.Qp Ξ α) (Qp' := Qp')
      (σ := σ) (α := α) (m := m) (ς := ς) (w := ΨE ς) (v := v)
      hσ hα hτF hwalk hland hFm hw hv hζv hsmall
  exact Rlow_eq_retOf_crux_walk hE hrel hτF hAbel hinjτ hQp'sub hς hwalk hcoinc

/-- **The low piece at every shift `l ≥ m`.**  `Work.Pert.pert2v2.Rlow_phi_add_nat` restated with an
arbitrary shift `l ≥ m` (writing `l = m + c`), which is the shape `orbit`'s piece relations ask for
(the level condition of the two-chart telescoping is `m₀ ≤ l` with `m₀` the crux's landing time). -/
theorem Rlow_phi_ge {f F τ Φ Φp φ : ℂ → ℂ} {Df Q Qp' : Set ℂ} {α d : ℂ} {m l : ℕ} {w : ℂ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ i : ℕ, i ≤ k → F^[i] z ∈ Q) ∧ F^[k] z = z')
    (hA42 : ∀ z ∈ Qp', Φ (Work.Pert.Tt α z) = Φp z + d)
    (hland : f^[m] (φ w) ∈ τ '' Qp')
    (hζQ : Work.Pert.Tt α (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Q)
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hml : m ≤ l)
    (hDφ : RlowPiece f Qp' τ Φp φ m d w + (l : ℂ) ∈ Work.Pert.DphiP f Df τ Φ Q) :
    Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w + (l : ℂ)) = f^[l] (φ w) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hml
  exact Rlow_phi_add_nat (c := c) hτF hOrb hA42 hland hζQ hτT hDφ

end

end Work.Pert.pert2v2
