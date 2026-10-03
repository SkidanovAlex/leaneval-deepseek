import Mathlib
import Submission.Work.Pert.pert2v2.coordP_mono_gate
import Submission.Work.Pert.pert2v2.dphiP_coordP_congr_of_eqOn

/-!
# PERT · `Work.Pert.pert2v2.DphiP_transfer_gate`: two-sided change of gate and of representative

The perturbed Fatou coordinate `φ_f = coordP f Df τ Φ Q` on its maximal domain
`DphiP f Df τ Φ Q` (Shishikura A.3/A.4, `Submission/Work/Pert/MaxDom.lean`) is built from

* the gate image `Φ '' Q` (the *domain* condition), and
* the chosen preimage `invOn Φ Q` (the *seed value* `τ (invOn Φ Q _)`),

and it is therefore insensitive to `Φ` away from `Q`.  This file states the combined
"transfer" that the two-dimensional R-block assembly needs: given

* `Φ` injective on the *small* gate `Q`, and `ΨE` agreeing with `Φ` on `Q` (`hag`),
* the *large* gate `Q' ⊇ Q` carrying the level structure of the lift `F`
  (`hab`, `hτF`, `hOrb`) with `ΨE` injective on `Q'`,

one may simultaneously replace the map `Φ` by the extension `ΨE` **and** the gate `Q` by the
larger `Q'`, without changing the domain membership of a point of `DphiP … Φ Q` nor its value.

The proof is the composite of the two on-disk lemmas:

* `dphiP_coordP_congr_of_eqOn` — the coordinate only sees the representative on the gate, so
  `DphiP … ΨE Q = DphiP … Φ Q` and the values agree there;
* `coordP_mono_gate` — enlarging the gate along the level structure of `F` preserves the domain
  and the value.
-/

namespace Work.Pert.pert2v2

open Work.Pert

theorem DphiP_transfer_gate {f F τ Φ ΨE : ℂ → ℂ} {Df : Set ℂ} {Q Q' : Set ℂ} {w : ℂ}
    (hsub : Q ⊆ Q')
    (hinj : Set.InjOn ΨE Q')
    (hab : ∀ z ∈ Q', F z ∈ Q' → ΨE (F z) = ΨE z + 1)
    (hτF : ∀ z ∈ Q', τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q', ∀ z' ∈ Q', ∀ k : ℕ, ΨE z' = ΨE z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q') ∧ F^[k] z = z')
    (hinjQ : Set.InjOn Φ Q) (hag : ∀ z ∈ Q, ΨE z = Φ z)
    (hw : w ∈ Work.Pert.DphiP f Df τ Φ Q) :
    w ∈ Work.Pert.DphiP f Df τ ΨE Q' ∧
      Work.Pert.coordP f Df τ Φ Q w = Work.Pert.coordP f Df τ ΨE Q' w := by
  -- **Step 1.** On the small gate `Q`, the representative is irrelevant: `Φ` and `ΨE` agree there,
  -- so the domain and the value of the coordinate coincide.
  have hcongr := dphiP_coordP_congr_of_eqOn (f := f) (Df := Df) (τ := τ) (Q := Q)
    (Φ := Φ) (Ψ := ΨE) hinjQ hag
  have hw' : w ∈ Work.Pert.DphiP f Df τ ΨE Q := by
    rw [hcongr.1]
    exact hw
  -- **Step 2.** Enlarging the gate from `Q` to `Q'` along the level structure of `F` preserves
  -- both the domain and the value (`coordP_mono_gate`).
  obtain ⟨hmem, hval⟩ := coordP_mono_gate (f := f) (Df := Df) (τ := τ) (Φ := ΨE)
    (Q := Q) (Q' := Q') hsub hinj hab hτF hOrb hw'
  exact ⟨hmem, (hcongr.2 w).symm.trans hval⟩

end Work.Pert.pert2v2
