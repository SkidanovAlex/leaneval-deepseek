import Mathlib
import Submission.Work.Pert.pert2v2.RBlockDefs
import Submission.Work.Pert.pert2v2.Rlow_phi_inv

/-!
# `Work.Pert.pert2v2.Rlow_gate_value` — the crux formula is a *gate value minus a level*

Two little structural lemmas that pin down the low piece `RlowPiece`:

* `RlowPiece_eq_gateValue`: using (A.4.2) (`Φ (Tt α z) = Φp z + d` on the subgate `Qp'`), the crux
  formula collapses to the **level-`(-m)`** point of the gate image of `ζ - 1/α`:

  `RlowPiece f Qp' τ Φp φ m d w = Φ (Tt α ζ) - m`,  `ζ := invOn τ Qp' (f^[m] (φ w)) ∈ Qp'`.

  Consequence (session-21 note §3.1): `R_close`'s residual is exactly the crux's pinning estimate
  `‖Φp ζ - m - d.E w‖ < δ` plus the (A.4.4) constant `‖d + 1/α‖ = ‖cm - cp‖`; **no walk is needed**
  for `R_close`.

* `coordP_gateValue`: the exact coordinate identity behind `(INV)` at an **arbitrary** admissible
  level `E`.  If `E` is an admissible level of `w` with gate point `ς` (`Φ ς = w - E`, hence
  `φ w = f^E (τ ς)`) *and* the deck translate `Tt α ς = ς - 1/α` lies in the same gate `Q`, then the
  level-`E` point above it is in the fibre of `φ` over `φ w`:

  `φ (Φ (Tt α ς) + E) = φ w`

  because `τ ∘ Tt α = τ`.  This is the "one `Tt`-shift" form of the return map, and it makes the
  obstruction precise: it needs `ς ∈ Qp Ξ α` (the waist), which for the low band is *never* the
  case (session-21 note §2).
-/

namespace Work.Pert.pert2v2

open Work.Pert

/-- **The crux formula is a gate value minus the level `m`.**  Uses (A.4.2) on the subgate `Qp'`
and the fact that the chosen `τ`-preimage lies in `Qp'`. -/
theorem RlowPiece_eq_gateValue {f Φ Φp τ φ : ℂ → ℂ} {Qp' : Set ℂ} {α d : ℂ} {m : ℕ} {w : ℂ}
    (hA42 : ∀ z ∈ Qp', Φ (Work.Pert.Tt α z) = Φp z + d)
    (hland : f^[m] (φ w) ∈ τ '' Qp') :
    RlowPiece f Qp' τ Φp φ m d w
      = Φ (Work.Pert.Tt α (Work.Pert.invOn τ Qp' (f^[m] (φ w)))) - (m : ℂ) := by
  have hmem : Work.Pert.invOn τ Qp' (f^[m] (φ w)) ∈ Qp' := Work.Pert.invOn_mem hland
  have h := hA42 _ hmem
  simp only [RlowPiece, Work.Pert.Rlow]
  rw [show Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w))) - (m : ℂ) - ((0 : ℤ) : ℂ) + d
      = (Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w))) + d) - (m : ℂ) by ring, ← h]

/-- **`(INV)` at an arbitrary admissible level, in the `Tt`-shift form.**  If `E` is an admissible
level of `w` with gate point `ς` (`Φ ς = w - E`, hence `φ w = f^E (τ ς)`), and `Tt α ς = ς - 1/α`
is again in the gate `Q`, then the level-`E` point above `Tt α ς` has the same `φ`-value as `w`.

The proof is the definition of `coordP` at level `E` for the point `Φ (Tt α ς) + E`
(`coordP_eq_iterate_of_level`) followed by `τ (ς - 1/α) = τ ς`. -/
theorem coordP_gateValue {f F τ Φ : ℂ → ℂ} {Df Q : Set ℂ} {α E : ℕ} {w ς : ℂ}
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hTt : Work.Pert.Tt α ς ∈ Q)
    (hDφR : Work.Pert.DphiP f Df τ Φ Q (Φ (Work.Pert.Tt α ς) + (E : ℂ)))
    (hτT : τ (Work.Pert.Tt α ς) = τ ς)
    (hφw : Work.Pert.coordP f Df τ Φ Q w = f^[E] (τ ς)) :
    Work.Pert.coordP f Df τ Φ Q (Φ (Work.Pert.Tt α ς) + (E : ℂ))
      = Work.Pert.coordP f Df τ Φ Q w := by
  have hcoord : Work.Pert.coordP f Df τ Φ Q (Φ (Work.Pert.Tt α ς) + (E : ℂ))
      = f^[E] (τ (Work.Pert.Tt α ς)) := by
    refine coordP_eq_iterate_of_level (E := E) (ζ := Work.Pert.Tt α ς) hτF hOrb hDφR hTt ?_
    ring
  rw [hcoord, hτT, ← hφw]

/-- **`RlowPiece` is a gate value plus a level, whenever the backward walk exists.**  If the gate
point `ς'` of the *backward* walk satisfies `F^[m+n] ς' = ζ - 1/α` (with `ζ = invOn τ Qp'
(f^[m] (φ w))` the crux's preimage) and the walk is legal in the gate `Q`, then

  `RlowPiece f Qp' τ Φp φ m d w = Φ ς' + n`,

i.e. `R w` is the *level-`n`* point above the gate point `ς' ∈ Q` (so `R w ∈ DphiP` at level `n`,
and `φ (R w) = f^n (τ ς')`).  This is the mechanism by which the low piece lands back in the
coordinate's domain; the remaining content is then the *value* comparison `f^n (τ ς') = φ w`
(session-21 note §4). -/
theorem RlowPiece_eq_gateValue_of_walk {f F Φ Φp τ φ : ℂ → ℂ} {Q Qp' : Set ℂ} {α d : ℂ}
    {m n : ℕ} {w ς' : ℂ}
    (hA42 : ∀ z ∈ Qp', Φ (Work.Pert.Tt α z) = Φp z + d)
    (hland : f^[m] (φ w) ∈ τ '' Qp')
    (habel : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hwalk : ∀ i : ℕ, i ≤ m + n → F^[i] ς' ∈ Q)
    (hend : F^[m + n] ς' = Work.Pert.invOn τ Qp' (f^[m] (φ w)) - 1 / α) :
    RlowPiece f Qp' τ Φp φ m d w = Φ ς' + (n : ℂ) := by
  have h1 : RlowPiece f Qp' τ Φp φ m d w
      = Φ (Work.Pert.invOn τ Qp' (f^[m] (φ w)) - 1 / α) - (m : ℂ) := by
    rw [RlowPiece_eq_gateValue hA42 hland, Work.Pert.Tt]
  have h2 : Φ (Work.Pert.invOn τ Qp' (f^[m] (φ w)) - 1 / α)
      = Φ ς' + ((m + n : ℕ) : ℂ) := by
    rw [← hend]
    exact Work.Pert.abel_iter hwalk habel
  rw [h1, h2]
  push_cast
  ring

end Work.Pert.pert2v2
