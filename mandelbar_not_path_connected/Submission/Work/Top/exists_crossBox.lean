import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.exists_box_small
import Submission.Work.Top.extAngle_close_of_Phi_close

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.Top

/-! ## Elementary facts about the rotation `rayRot` -/

theorem rayRot_sub (θ : ℝ) (u v : ℂ) :
    rayRot θ (u - v) = rayRot θ u - rayRot θ v := by
  simp only [rayRot_apply]
  ring

/-- The rotation `rayRot θ` fixes the point `rayPoint θ R` of the exterior disc at level `R`,
carrying it to the real point `R`. -/
theorem rayRot_rayPoint_self (θ R : ℝ) :
    rayRot θ (NakaneData.rayPoint θ R) = (R : ℂ) := by
  rw [NakaneData.rayPoint, rayRot_apply, mul_assoc, ← Complex.exp_add]
  rw [show 2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I +
      -(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) = 0 from by ring, Complex.exp_zero]
  ring

/-- `rayRot θ` is a Euclidean isometry fixing `rayPoint θ R`, so distance to `rayPoint θ R`
in the Böttcher plane equals distance to `R` in the rotated plane. -/
theorem norm_sub_rayPoint_eq_norm_rayRot_sub (θ R : ℝ) (w : ℂ) :
    ‖w - NakaneData.rayPoint θ R‖ = ‖rayRot θ w - (R : ℂ)‖ := by
  rw [← norm_rayRot θ (w - NakaneData.rayPoint θ R), rayRot_sub, rayRot_rayPoint_self]

/-- The box `|Re w - R| < a`, `|Im w| < b` about `(R, 0)` is contained in the disc of radius
`a + b` centred at `R`. -/
theorem norm_sub_le_of_re_im {R a b : ℝ} {w : ℂ} (hre : |w.re - R| < a) (him : |w.im| < b) :
    ‖w - (R : ℂ)‖ < a + b := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (w - (R : ℂ))
  rw [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero] at h1
  linarith

/-- **The cross box lemma.** Near the point `q` of the parameter ray of angle `θ` and level `R`
there is a small box in the rotated Böttcher plane, contained in the horizontal band
`Φ c`-close to `rayPoint θ R` (hence with external angle within `η` of `θ`) and inside the
`ε`-ball around `q`. -/
theorem exists_crossBox {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {q : ℂ} {θ R : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hR : 1 < R) (hq : Φ q = Work.Top.NakaneData.rayPoint θ R)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ≤ R - 1 ∧
      (∀ c : ℂ, c ∉ Mb → |(Work.Top.rayRot θ (Φ c)).re - R| < a →
        |(Work.Top.rayRot θ (Φ c)).im| < b → |Work.Top.NakaneData.extAngle Φ c - θ| < η) ∧
      (∀ c : ℂ, c ∉ Mb → |(Work.Top.rayRot θ (Φ c)).re - R| < a →
        |(Work.Top.rayRot θ (Φ c)).im| < b → dist c q < ε) := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hw₀ : Work.Top.NakaneData.rayPoint θ R ∈ Work.Top.exteriorDisc :=
    Work.Top.NakaneData.rayPoint_mem_exteriorDisc hR
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := extAngle_close_of_Phi_close hN hθ₀ hθ₁ hR hη
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_box_small hN hq hw₀ hε
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  have hδle₁ : δ ≤ δ₁ := min_le_left _ _
  have hδle₂ : δ ≤ δ₂ := min_le_right _ _
  refine ⟨min (R - 1) (δ / 4), δ / 4, lt_min (by linarith) (by linarith), by linarith,
    min_le_left _ _, ?_, ?_⟩
  · intro c hc hre him
    apply hδ₁ c hc
    rw [norm_sub_rayPoint_eq_norm_rayRot_sub]
    have hbox := norm_sub_le_of_re_im (R := R) hre him
    have hle : min (R - 1) (δ / 4) + δ / 4 ≤ δ := by
      have := min_le_right (R - 1) (δ / 4)
      linarith
    exact lt_of_lt_of_le hbox (le_trans hle hδle₁)
  · intro c hc hre him
    apply hδ₂ c hc
    rw [norm_sub_rayPoint_eq_norm_rayRot_sub]
    have hbox := norm_sub_le_of_re_im (R := R) hre him
    have hle : min (R - 1) (δ / 4) + δ / 4 ≤ δ := by
      have := min_le_right (R - 1) (δ / 4)
      linarith
    exact lt_of_lt_of_le hbox (le_trans hle hδle₂)

end Work.Top
