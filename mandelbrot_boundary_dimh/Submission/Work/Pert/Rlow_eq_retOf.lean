import Mathlib
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.gate_T_relation
import Submission.Work.Pert.Setup
import Submission.Work.Pert.coordP_abel

namespace Work.Pert

/-!
# PERT · `Work.Pert.Rlow_eq_retOf`: the low return map at a waist point is `retOf`

At a point `ζ` of the waist (`ζ ∈ Qm H α ∩ Qp H α`) the lifted return map `R̃_f` of Shishikura
(4.2.2)/(4.2.3) admits two descriptions, and this file shows they agree at the point `w = ΦH ζ`:

* the **low** form `Rlow f Qp'' τ Φp φ m k dlow w`: walk the level-`m` point `f^[m] (φ w)` of `w`
  back through `τ` into the subgate `Qp''`, apply the upper Fatou coordinate `Φp`, undo the iterate
  `m` and the deck shift `k` (A.4.4), and add the normalising constant `dlow`;
* the **overlap** form `retOf ΦH (Qm H α) α (ΦH ζ) = ΦH (Tt α ζ) = ΦpH ζ + dH`: move the gate
  point `ζ` itself by the deck translation and read the coordinate.

The two agree because (i) `invOn τ Qp'' (f^[m] (φ (ΦH ζ))) = F^[m] ζ` — the intertwining
`τ ∘ F = f ∘ τ` along the legal walk `hwalk` turns `f^[m] (φ (ΦH ζ)) = f^[m] (τ ζ)` into
`τ (F^[m] ζ)`, and `τ` is injective on `Qp''` (`hinjτ`, `hFm`); (ii) the iterated Abel equation
`Φp (F^[m] ζ) = Φp ζ + m` (`abel_iter`, using `hAbel` along `hwalk`); (iii) the two normalisations
`Φp ζ = ΦpH ζ + cst` (`hconst`) and `ΦH (Tt α ζ) = ΦpH ζ + dH` (`hTtr`).  The deck shift `k` and
the constant `dH` cancel algebraically.
-/

open MandelDim Complex Set

noncomputable section

theorem Rlow_eq_retOf {f F ΦH ΦpH Φp φ τ : ℂ → ℂ} {Ξ' H : ℝ} {α dH cst : ℂ}
    {m : ℕ} {k : ℤ} {Qp'' : Set ℂ} {ζ : ℂ}
    (hτF : ∀ z ∈ Work.Pert.Qp Ξ' α, τ (F z) = f (τ z))
    (hAbel : ∀ z ∈ Work.Pert.Qp Ξ' α, F z ∈ Work.Pert.Qp Ξ' α → Φp (F z) = Φp z + 1)
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ζ ∈ Work.Pert.Qp Ξ' α)
    (hFm : F^[m] ζ ∈ Qp'')
    (hinjτ : Set.InjOn τ Qp'')
    (hQp''sub : ∀ z ∈ Qp'', τ (F z) = f (τ z))
    (hφ : φ (ΦH ζ) = τ ζ)
    (hζH : ζ ∈ Work.Pert.Qm H α) (hζpH : ζ ∈ Work.Pert.Qp H α)
    (hTtr : ΦH (Work.Pert.Tt α ζ) = ΦpH ζ + dH)
    (hconst : Φp ζ = ΦpH ζ + cst)
    (hinjΦH : Set.InjOn ΦH (Work.Pert.Qm H α)) :
    Work.Pert.Rlow f Qp'' τ Φp φ m k (dH + (k : ℂ) - cst) (ΦH ζ)
      = Work.Pert.retOf ΦH (Work.Pert.Qm H α) α (ΦH ζ) := by
  -- (i) the level-`m` point of `w = ΦH ζ` in `Qp''` is `F^[m] ζ`
  have hiter : τ (F^[m] ζ) = f^[m] (φ (ΦH ζ)) := by
    rw [tau_iterate_of_walk hwalk hτF, hφ]
  have hinv : invOn τ Qp'' (f^[m] (φ (ΦH ζ))) = F^[m] ζ :=
    invOn_eq hinjτ ⟨F^[m] ζ, hFm, hiter⟩ hFm hiter
  -- (ii) the iterated Abel equation along the legal walk `hwalk`
  have habelm : Φp (F^[m] ζ) = Φp ζ + (m : ℂ) := abel_iter hwalk hAbel
  -- (iii) the overlap description of `R̃_f` at the waist point `ζ`
  have hret : retOf ΦH (Work.Pert.Qm H α) α (ΦH ζ) = ΦpH ζ + dH := by
    rw [retOf_eq hinjΦH ⟨ζ, hζH, rfl⟩ hζH rfl, hTtr]
  simp only [Work.Pert.Rlow]
  rw [hinv, habelm, hconst, hret]
  ring

end

end Work.Pert
