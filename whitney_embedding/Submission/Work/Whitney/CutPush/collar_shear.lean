import Mathlib

/-!
# The fibered shear

The last step of the collar flattening (`CutPush/NOTES_STATE_S60.md` §2) flattens the sheet into
`K' ⊕ K'^⊥` by the *shear along the fibers of the projection* `π : E →L[ℝ] E` onto `K'`:

    A₃ y = y - g (π y),        inverse:  z ↦ z + g (π z).

The point of this file is that **such a shear is automatically a `C^∞` diffeomorphism with an explicit
inverse**, with no estimates at all: the only facts used are that the displacement `G y = g (π y)` is
*constant on the fibers of `π`* and takes values in `ker π`.  The two identities are then
`G (y - G y) = G y` and `G (z + G z) = G z`, both immediate from `π (y - G y) = π y - π (G y) = π y`
and `π (z + G z) = π z + π (G z) = π z`.
-/

namespace Work.Whitney.CutPush

/-- **A shear along the fibers of a projection is a bijection.**  If `G : E → E` is constant on the
fibers of the linear map `π` and takes values in `ker π`, then `y ↦ y - G y` and `z ↦ z + G z` are
mutually inverse. -/
theorem shear_leftInverse_rightInverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    (π : E →ₗ[ℝ] E) (G : E → E)
    (hG : ∀ x y : E, π x = π y → G x = G y) (hker : ∀ x : E, π (G x) = 0) :
    Function.LeftInverse (fun z : E => z + G z) (fun y : E => y - G y) ∧
      Function.RightInverse (fun z : E => z + G z) (fun y : E => y - G y) := by
  have hstep : ∀ y : E, π (y - G y) = π y := by
    intro y
    rw [map_sub, hker y, sub_zero]
  constructor
  · intro y
    show (y - G y) + G (y - G y) = y
    rw [hG (y - G y) y (hstep y)]
    abel
  · intro z
    show (z + G z) - G (z + G z) = z
    rw [hG (z + G z) z (by rw [map_add, hker z, add_zero])]
    abel

/-- **The fibered shear of a projection.**  Given a continuous linear projection `π` and a smooth `g`
with values in `ker π`, the map `y ↦ y - g (π y)` is a `C^∞` diffeomorphism of `E` with inverse
`z ↦ z + g (π z)`. -/
theorem fibered_shear_diffeomorphism {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (π : E →L[ℝ] E) (g : E → E) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hker : ∀ x : E, π (g x) = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => y - g (π y)) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : E => z + g (π z)) ∧
    Function.LeftInverse (fun z : E => z + g (π z)) (fun y : E => y - g (π y)) ∧
    Function.RightInverse (fun z : E => z + g (π z)) (fun y : E => y - g (π y)) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => g (π y)) := hg.comp π.contDiff
  have h2 := shear_leftInverse_rightInverse (π.toLinearMap) (fun y : E => g (π y))
    (fun x y h => congrArg g h) (fun x => hker (π x))
  exact ⟨contDiff_id.sub h1, contDiff_id.add h1, h2.1, h2.2⟩

end Work.Whitney.CutPush
