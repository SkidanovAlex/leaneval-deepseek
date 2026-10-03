import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.RBlock`: the lifted return map `R̃_f` on the maximal domain

`PertData.R` (Shishikura's `R̃_f`, (4.2.2)/(4.2.3)/(4.3.4)) is a lift of the return map of the
cylinder to the universal cover: it must satisfy

* `φ_f ∘ R̃_f = φ_f` exactly (this is what makes the orbit relation (4.2.3) hold),
* `R̃_f (w+1) = R̃_f w + 1` (`T`-equivariance, `ParabData.E_add_one`'s counterpart),
* `R̃_f + 1/α → d.E` (4.2.4) and `R̃_f w - w + 1/α → 0` at the upper end (4.2.2).

The paper defines `R̃_f = Φ₋,f ∘ T_f ∘ Φ₋,f⁻¹`; that formula is only available on `Φ₋,f '' Q_f^-`,
which is *not* where the assembly needs `R` (`DR ⊇ K ∪ {y₁ ≤ |Im w|}`).  The lift that is available
everywhere on the maximal domain `DphiP f Df τ Φ Q` is the **level-shifted** one:

> at the minimal admissible level `n = mIdxP f Df τ Φ Q w` of `w` (so `w - n = Φ ς` with `ς ∈ Q`
> on the gate), move the gate point by the deck translation `Tt α` and put back the level,

`retP f Df τ Φ Q α w = n + Φ (Tt α (Φ⁻¹ (w - n)))`.

Because `Tt α '' Q ⊆ Q` for the gate `Q = Qm Ξ α` and `τ = tauC σ α` is `Tt α`-invariant, the
orbit data of the level `n` of `w` is *identical* to that of the level `n` of `retP … w`, so
`φ_f (retP … w) = φ_f w` holds exactly (`coordP_retP` below).
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-- **CANDIDATE (superseded) lifted return map.**  WARNING (see
`NOTES_pert2_findings.md` §K.3): this definition is only useful with a hypothesis
`hTQ : ∀ z ∈ Q, Tt α z ∈ Q`, and that hypothesis is **FALSE for the gate** `Q = Qm Ξ α`
(the truth is `Tt α '' Qp = Qm`, `Work.Pert.Tt_mem_Qm_iff`).  It is kept only because the
conditional lemma `retP_coordP` (shift the gate point at the minimal level, keep the level) is a
correct general statement, and any future `Tt α`-invariant region may use it.  The design's `R̃`
must instead be the extended horn map `Φp ∘ Φm⁻¹ + d₁`; see §K.4.

Shift the gate coordinate at the minimal level of `w` by the deck translation `Tt α`. -/
def retP (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Q : Set ℂ) (α w : ℂ) : ℂ :=
  ((mIdxP f Df τ Φ Q w : ℕ) : ℂ) +
    Φ (Tt α (invOn Φ Q (w - ((mIdxP f Df τ Φ Q w : ℕ) : ℂ))))

/-! ## The low part of the return map (lead's design, 2026-10-05)

On the *waist* `{|Im| > Ξ + |Re|}` the two gates `Qm Ξ α`, `Qp Ξ α` overlap, and there the return
map is `Φm ∘ Tt α ∘ Φm⁻¹` (`retOf`).  At small heights (the band `y₁ ≤ |Im| ≤ Ξ`) the gate point has
to be *walked into* the overlap by iterating `f`, which is what `Rlow` records: evaluate the horn
map `Φp` at the gate point of `f^[m] (φ w)` inside a subgate `Qp'` where `τ_C` is injective, then
undo the iterate `m` and the deck shift `k` (A.4.4) and add the normalising constant `d_low`. -/

/-- The low part of the lifted return map. -/
def Rlow (f : ℂ → ℂ) (Qp' : Set ℂ) (τ Φp φ : ℂ → ℂ) (m : ℕ) (k : ℤ) (dlow w : ℂ) : ℂ :=
  Φp (invOn τ Qp' (f^[m] (φ w))) - (m : ℂ) - (k : ℂ) + dlow

end

end Work.Pert
