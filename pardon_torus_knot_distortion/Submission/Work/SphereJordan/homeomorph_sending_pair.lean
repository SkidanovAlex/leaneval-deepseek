import Mathlib
import Submission.Work.Smooth.SphereJordan.mobiusAddInv

namespace Work.SphereJordan

open scoped OnePoint

noncomputable section

/-!
# Moving two distinct points of the Riemann sphere to `0` and `∞`

The Riemann sphere `OnePoint ℂ = ℂ ∪ {∞}` is the one-point compactification of `ℂ`.  Its
homeomorphism group contains the Möbius transformations, and in particular it acts
`2`-transitively on the sphere: any two distinct points can be carried to any other two distinct
points.

Here we prove the concrete statement that any pair `p ≠ q` can be carried to `(0, ∞)`.  The proof
is assembled from three explicit moves:

* `sphereTranslate c` — the translation `z ↦ z + c` of the finite part, fixing `∞`
  (`Homeomorph.onePointCongr (Homeomorph.addRight c)`);
* `Work.Smooth.SphereJordan.mobiusAddInv 0` — the Möbius map `z ↦ z⁻¹` extended to the sphere,
  sending `0 ↦ ∞` and `∞ ↦ 0`;
* the symmetric-inverse trick `exists_homeomorph_infty_eq`, which places either prescribed point
  at `∞` first.

Concretely `exists_homeomorph_normalize a b` first sends `b` to `∞` (via a Möbius map built from
`exists_homeomorph_infty_eq`), then translates the image of `a` to `0`, and finally applies
inversion to exchange `0` and `∞`.
-/

/-- The translation `z ↦ z + c` of the Riemann sphere, fixing `∞`. -/
def sphereTranslate (c : ℂ) : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  Homeomorph.onePointCongr (Homeomorph.addRight c)

@[simp] theorem sphereTranslate_infty (c : ℂ) : sphereTranslate c ∞ = ∞ := by
  simp [sphereTranslate]

@[simp] theorem sphereTranslate_coe (c : ℂ) (z : ℂ) :
    sphereTranslate c (z : OnePoint ℂ) = ((z + c : ℂ) : OnePoint ℂ) := by
  simp [sphereTranslate]

/-- **Every point of the Riemann sphere can be obtained as the image of `∞`.**  This is the
Möbius map `z ↦ λ + z⁻¹` when the point is finite, and the identity when it is `∞`. -/
theorem exists_homeomorph_infty_eq (p : OnePoint ℂ) :
    ∃ Φ : OnePoint ℂ ≃ₜ OnePoint ℂ, Φ ∞ = p := by
  by_cases hp : p = ∞
  · exact ⟨Homeomorph.refl _, hp.symm⟩
  · obtain ⟨lam, hlam⟩ := OnePoint.ne_infty_iff_exists.mp hp
    obtain ⟨Φ, hΦ, -, -⟩ := Work.Smooth.SphereJordan.mobiusAddInv lam
    exact ⟨Φ, by rw [hΦ, hlam]⟩

/-- **Any two distinct points of the Riemann sphere can be sent to `∞` and `0`** (in that order).
-/
theorem exists_homeomorph_normalize (a b : OnePoint ℂ) (hab : a ≠ b) :
    ∃ Φ : OnePoint ℂ ≃ₜ OnePoint ℂ,
      Φ a = ∞ ∧ Φ b = ((0:ℂ) : OnePoint ℂ) := by
  obtain ⟨Φ0, hΦ0⟩ := exists_homeomorph_infty_eq b
  set Φ1 : OnePoint ℂ ≃ₜ OnePoint ℂ := Φ0.symm with hΦ1
  have hΦ1b : Φ1 b = ∞ := by
    rw [hΦ1, ← hΦ0, Homeomorph.symm_apply_apply]
  have hane : Φ1 a ≠ ∞ := fun h => hab (Φ1.injective (h.trans hΦ1b.symm))
  obtain ⟨α, hα⟩ := OnePoint.ne_infty_iff_exists.mp hane
  obtain ⟨ι, hιinf, hι0, -⟩ := Work.Smooth.SphereJordan.mobiusAddInv (0:ℂ)
  refine ⟨Φ1.trans ((sphereTranslate (-α)).trans ι), ?_, ?_⟩
  · simp only [Homeomorph.trans_apply]
    rw [← hα, sphereTranslate_coe, add_neg_cancel]
    rw [hι0]
  · simp only [Homeomorph.trans_apply]
    rw [hΦ1b, sphereTranslate_infty, hιinf]

/-- **Any two distinct points of the Riemann sphere can be sent to `0` and `∞`** (in that order).
-/
theorem homeomorph_sending_pair {p q : OnePoint ℂ} (hpq : p ≠ q) :
    ∃ Φ : OnePoint ℂ ≃ₜ OnePoint ℂ,
      Φ p = ((0 : ℂ) : OnePoint ℂ) ∧ Φ q = OnePoint.infty := by
  obtain ⟨Φ, hΦq, hΦp⟩ := exists_homeomorph_normalize q p (Ne.symm hpq)
  exact ⟨Φ, hΦp, hΦq⟩

end

end Work.SphereJordan
