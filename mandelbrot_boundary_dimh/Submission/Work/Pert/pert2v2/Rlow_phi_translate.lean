import Mathlib
import Submission.Work.Pert.pert2v2.Rlow_gate_value
import Submission.Work.Pert.pert2v2.level_translate
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Gates
import Submission.Work.Pert.coordP_level_eq

/-!
# `Work.Pert.pert2v2.Rlow_phi_translate` — the low piece at shifts `1 ≤ j < m`

`pert2v2.Rlow_phi_add_nat` covers the shifts `j ≥ m` of the low piece (`j = m + c`, `c ≥ 0`) by
the *level* trick: `RlowPiece w + j = Φ u + c` with `u = Tt α ζ_w ∈ Qm`, so the value is
`f^[c] (τ u) = f^[j] (φ w)`.

This file covers the remaining shifts `1 ≤ j < m`.  Here the point
`U := RlowPiece w + j = Φ u - (m - j)` lies *below* `u` in the `Φ`-coordinate, so its gate point
`ς` (at the minimal level `E = mIdxP U`) is an `F`-iterate of `u` *backwards*: `u = F^[E + m - j] ς`
(`hOrb`).  Hence

* `τ u = f^[E + m - j] (τ ς)`  (`tau_eq_iterate_of_shift`), and
* `φ U = f^[E] (τ ς)`  (the seed formula at the minimal level),

so `f^[m - j] (φ U) = f^[E + m - j] (τ ς) = τ u = f^[m] (φ w) = f^[m - j] (f^[j] (φ w))`, and
injectivity of `f^[m - j]` on the seed ball gives `φ U = f^[j] (φ w)`.

Together with `Rlow_phi_add_nat` this settles *every* positive shift of the low piece, with no
walk and no waist hypothesis: the only inputs are the level structure (`hOrb`), the crux's
`τ ζ_w = f^[m] (φ w)`, and the (design-side) injectivity of `f^[m-j]` on the seed ball.
-/

namespace Work.Pert.pert2v2

open Work.Pert MandelDim

/-- **The low piece at shifts `1 ≤ j < m`.** -/
theorem Rlow_phi_translate_lt {f F τ Φ Φp φ : ℂ → ℂ} {Df Q Qp' : Set ℂ} {α d : ℂ}
    {m j : ℕ} {w : ℂ} {δ : ℝ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ i : ℕ, i ≤ k → F^[i] z ∈ Q) ∧ F^[k] z = z')
    (hA42 : ∀ z ∈ Qp', Φ (Work.Pert.Tt α z) = Φp z + d)
    (hland : f^[m] (φ w) ∈ τ '' Qp')
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hζQ : Work.Pert.Tt α (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Q)
    (hinjf : Set.InjOn (f^[m - j]) (Metric.ball (0 : ℂ) δ))
    (hj1 : 1 ≤ j) (hjm : j < m)
    (hDφ : (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ)) ∈ Work.Pert.DphiP f Df τ Φ Q)
    (hmemU : Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ))
      ∈ Metric.ball (0 : ℂ) δ)
    (hmemY : f^[j] (φ w) ∈ Metric.ball (0 : ℂ) δ) :
    Work.Pert.coordP f Df τ Φ Q (RlowPiece f Qp' τ Φp φ m d w + (j : ℂ))
      = f^[j] (φ w) := by
  -- Φ is injective on the gate, from the orbit rule at `k = 0`
  have hinjQ : Set.InjOn Φ Q := fun z hz z' hz' hzz' => by
    have h := (hOrb z hz z' hz' 0 (by rw [hzz']; simp)).2
    simpa using h
  -- the crux's landing point and its deck translate
  set ζ : ℂ := Work.Pert.invOn τ Qp' (f^[m] (φ w)) with hζdef
  have hτζ : τ ζ = f^[m] (φ w) := Work.Pert.invOn_spec hland
  set u : ℂ := Work.Pert.Tt α ζ with hudef
  -- the crux formula is the gate value minus the level `m`
  have hR : RlowPiece f Qp' τ Φp φ m d w = Φ u - (m : ℂ) := by
    rw [hudef, hζdef]
    exact RlowPiece_eq_gateValue hA42 hland
  set U : ℂ := RlowPiece f Qp' τ Φp φ m d w + (j : ℂ) with hUdef
  have hUu : Φ u = U + ((m : ℂ) - (j : ℂ)) := by
    rw [hUdef, hR]
    push_cast
    ring
  -- the gate point of `U` at its minimal level `E`
  set E : ℕ := Work.Pert.mIdxP f Df τ Φ Q U with hEdef
  set ς : ℂ := Work.Pert.invOn Φ Q (U - (E : ℂ)) with hςdef
  have hςQ : ς ∈ Q := Work.Pert.invOn_mem (Work.Pert.mIdxP_spec hDφ).1
  have hΦς : Φ ς = U - (E : ℂ) := Work.Pert.invOn_spec (Work.Pert.mIdxP_spec hDφ).1
  -- the seed formula at the minimal level
  have hseed : Work.Pert.seedP τ Φ Q (U - (E : ℂ)) = τ ς :=
    Work.Pert.seedP_eq_of_mem' hinjQ ⟨ς, hςQ, hΦς⟩ hςQ hΦς
  have hφU : Work.Pert.coordP f Df τ Φ Q U = f^[E] (τ ς) := by
    rw [Work.Pert.coordP_self, ← hEdef, hseed]
  -- `u` is the `(E + m - j)`-th `F`-iterate of `ς`
  have hjm' : j ≤ m := le_of_lt hjm
  have hΦu' : Φ u = Φ ς + ((E + (m - j) : ℕ) : ℂ) := by
    rw [hUu, hΦς, Nat.cast_add, Nat.cast_sub hjm']
    ring
  have hτu : τ u = f^[E + (m - j)] (τ ς) :=
    Work.Pert.tau_eq_iterate_of_shift hτF hOrb hςQ hζQ hΦu'
  -- `τ u = f^m (φ w)`
  have hτζu : τ u = f^[m] (φ w) := by
    rw [hudef, hτT, hτζ]
  -- the key identity `f^{m-j} (φ U) = f^{m-j} (f^j (φ w))`
  have h1 : f^[m - j] (Work.Pert.coordP f Df τ Φ Q U) = f^[m - j] (f^[E] (τ ς)) := by
    rw [hφU]
  have h2 : f^[m - j] (f^[E] (τ ς)) = τ u := by
    rw [← Function.iterate_add_apply, Nat.add_comm (m - j) E]
    exact hτu.symm
  have h3 : f^[m - j] (f^[j] (φ w)) = f^[m] (φ w) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjm']
  have hkey : f^[m - j] (Work.Pert.coordP f Df τ Φ Q U) = f^[m - j] (f^[j] (φ w)) := by
    rw [h1, h2, hτζu, h3]
  exact hinjf hmemU hmemY hkey

end Work.Pert.pert2v2
