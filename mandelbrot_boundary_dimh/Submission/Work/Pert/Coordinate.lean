import Mathlib
import Submission.Work.Pert.Basic

/-!
# PERT: the perturbed coordinate `φ_f = τ_f ∘ Φ⁻¹` and the lifted return map `R̃_f`

Abstract form of (4.2.3)/(4.3.4).  `Φ` is a Fatou coordinate of the lift `F_f` of `f` on the gate
(`Φ (F_f ζ) = Φ ζ + 1`), `g` an inverse of `Φ`, `T` the deck translation (`T(ζ) = ζ - 1/α`, on which
`τ_f` is invariant), and

* `phiG τ g w = τ (g w)` is `φ_f = τ_f ∘ Φ⁻¹`;
* `retG T Φ g w = Φ (T (g w))` is the lifted return map `R̃_f = Φ ∘ T_f ∘ Φ⁻¹`.

The two structural identities the orbit relation of `PertData.orbit` rests on are `phiG_retG`
(`φ_f ∘ R̃_f = φ_f`, *exact*, because `τ_f ∘ T_f = τ_f`) and `phiG_add_one`
(`φ_f (w+1) = f (φ_f w)`, the Abel equation of `φ_f`).
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- `φ = τ ∘ g`, the coordinate attached to a Fatou coordinate `Φ` with inverse `g`. -/
def phiG (τ g : ℂ → ℂ) (w : ℂ) : ℂ := τ (g w)

/-- `R̃ = Φ ∘ T ∘ g`, the lifted return map attached to `Φ`, its inverse `g` and the deck
translation `T`. -/
def retG (T Φ g : ℂ → ℂ) (w : ℂ) : ℂ := Φ (T (g w))

/-- **`φ_f ∘ R̃_f = φ_f` is exact** (Shishikura (4.2.3)/(4.3.4): `τ_f ∘ T_f = τ_f`). -/
theorem phiG_retG {τ T Φ g : ℂ → ℂ} (hT : ∀ ζ, τ (T ζ) = τ ζ)
    (hΦg : ∀ w, Φ (g w) = w) (hgΦ : ∀ ζ, g (Φ ζ) = ζ) (w : ℂ) :
    phiG τ g (retG T Φ g w) = phiG τ g w := by
  unfold phiG retG
  rw [hgΦ, hT]

/-- **The Abel equation `φ_f (w+1) = f (φ_f w)`** for `φ_f = τ_f ∘ Φ⁻¹`, from the Abel equation
`Φ (F_f ζ) = Φ ζ + 1` of the Fatou coordinate and the lift relation `τ_f (F_f ζ) = f (τ_f ζ)`
(`Work.Pert.abel`). -/
theorem phiG_add_one {τ f F Φ g : ℂ → ℂ} (hab : ∀ ζ, τ (F ζ) = f (τ ζ))
    (hΦ : ∀ ζ, Φ (F ζ) = Φ ζ + 1) (hΦg : ∀ w, Φ (g w) = w) (hgΦ : ∀ ζ, g (Φ ζ) = ζ) (w : ℂ) :
    phiG τ g (w + 1) = f (phiG τ g w) := by
  have h1 : w + 1 = Φ (F (g w)) := by rw [hΦ, hΦg]
  unfold phiG
  rw [h1, hgΦ, hab]

end

end Work.Pert
