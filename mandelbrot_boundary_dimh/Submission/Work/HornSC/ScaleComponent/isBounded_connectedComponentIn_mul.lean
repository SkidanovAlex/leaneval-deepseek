import Mathlib

/-!
# Boundedness of complementary components is invariant under a positive real scaling

For a real `c > 0`, the map `z ↦ c * z` is a homeomorphism of `ℂ` onto itself that is moreover
Lipschitz with constant `c`.  Consequently it carries `Kᶜ` onto `((z ↦ c*z) '' K)ᶜ` and maps the
connected component of `a` in `Kᶜ` onto the connected component of `c * a` in that image
complement; being a Lipschitz image of the bounded set `connectedComponentIn Kᶜ a`, the latter is
bounded.
-/

namespace Work.HornSC.ScaleComponent

open Set

theorem isBounded_connectedComponentIn_mul {c : ℝ} (hc : 0 < c) {K : Set ℂ} {a : ℂ}
    (hb : Bornology.IsBounded (connectedComponentIn (Kᶜ) a)) :
    Bornology.IsBounded
      (connectedComponentIn (((fun z : ℂ => (c : ℂ) * z) '' K)ᶜ) ((c : ℂ) * a)) := by
  by_cases ha : a ∈ Kᶜ
  · -- the scaling is a homeomorphism and the complement is carried onto the complement
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hbij : Function.Bijective (fun z : ℂ => (c : ℂ) * z) := by
      constructor
      · intro x y h
        exact mul_left_cancel₀ hcne h
      · intro w
        exact ⟨(c : ℂ)⁻¹ * w, by change (c : ℂ) * ((c : ℂ)⁻¹ * w) = w; rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]⟩
    have himg : (fun z : ℂ => (c : ℂ) * z) '' Kᶜ = ((fun z : ℂ => (c : ℂ) * z) '' K)ᶜ :=
      Set.image_compl_eq hbij
    set Φ : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero (c : ℂ) hcne with hΦdef
    have hΦcoe : ⇑Φ = fun z : ℂ => (c : ℂ) * z := by
      funext z
      simp [hΦdef, Homeomorph.smulOfNeZero, Homeomorph.smul, smul_eq_mul]
    have hcc := Homeomorph.image_connectedComponentIn Φ ha
    rw [hΦcoe] at hcc
    rw [himg] at hcc
    -- both sides are now the image of `connectedComponentIn Kᶜ a` under the scaling
    rw [← hcc]
    exact (lipschitzWith_smul (c : ℂ)).isBounded_image hb
  · -- if `a ∈ K` then the component is empty on both sides
    simp only [Set.mem_compl_iff, not_not] at ha
    have hmem : (c : ℂ) * a ∈ (fun z : ℂ => (c : ℂ) * z) '' K := ⟨a, ha, rfl⟩
    rw [connectedComponentIn_eq_empty (F := ((fun z : ℂ => (c : ℂ) * z) '' K)ᶜ)
      (x := (c : ℂ) * a) (fun h => h hmem)]
    exact Bornology.isBounded_empty

end Work.HornSC.ScaleComponent
