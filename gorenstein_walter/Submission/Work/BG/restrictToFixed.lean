import Mathlib
import Submission.Work.BG.Glauberman

/-!
# BG-L2: the restricted action on the fixed points (`RestrictToFixedProp`)

If an automorphism `σ` of a group `U` commutes with every `φ s` (`s : S`), then each `φ s`
preserves the fixed-point subgroup `fixedSubgroup σ = C_U(σ)` and restricts to an automorphism
of it, giving a monoid homomorphism `φ₁ : S →* MulAut ↥(fixedSubgroup σ)` whose composition
with the coercion back to `U` is `φ s`.

This is leaf **BG-L2** of `Submission/Work/BG/Glauberman.lean`, the first step of the
induction underlying BG-Lemma 1.9 (`glauberman_two`, `glaubermanGeneralProp`).

Concretely, from `φ s * σ = σ * φ s` and `MulAut.mul_apply` (`(f * g) u = f (g u)`) we get
`σ (φ s u) = φ s (σ u)`, so `φ s` maps fixed points to fixed points; the same for `φ s⁻¹`,
which provides the two-sided inverse.  Everything is then checked at the level of the ambient
group `U` via `Subtype.ext`.
-/

namespace Work.BG

theorem restrictToFixed : Work.BG.RestrictToFixedProp := by
  intro S U _ _ φ σ hcomm
  -- `φ s` maps fixed points of `σ` to fixed points of `σ`
  have key : ∀ (s : S) (u : U), σ u = u → σ (φ s u) = φ s u := by
    intro s u hu
    have h : (φ s * σ) u = (σ * φ s) u := by rw [hcomm s]
    simp only [MulAut.mul_apply] at h
    rw [hu] at h
    exact h.symm
  -- and so does `(φ s)⁻¹ = φ s⁻¹`
  have key' : ∀ (s : S) (u : U), σ u = u → σ (φ s⁻¹ u) = φ s⁻¹ u := by
    intro s u hu
    have h : (φ s⁻¹ * σ) u = (σ * φ s⁻¹) u := by rw [hcomm s⁻¹]
    simp only [MulAut.mul_apply] at h
    rw [hu] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · refine { toFun := fun s => ?_, map_one' := ?_, map_mul' := ?_ }
    · refine { toFun := fun u => ⟨φ s u, key s u u.2⟩,
               invFun := fun u => ⟨φ s⁻¹ u, key' s u u.2⟩,
               left_inv := ?_, right_inv := ?_, map_mul' := ?_ }
      · intro u; ext; simp
      · intro u; ext; simp
      · intro x y; ext; simp [map_mul]
    · ext u; simp
    · intro a b; ext u; simp [map_mul]
  · intro s u; rfl

end Work.BG
