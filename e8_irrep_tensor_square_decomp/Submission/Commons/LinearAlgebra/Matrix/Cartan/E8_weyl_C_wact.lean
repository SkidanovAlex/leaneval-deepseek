import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_denom
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_denom_refl

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- The positive roots of `E₈` in the form used by `E8_weyl_denom_refl`: nonzero lattice vectors
of squared length `2` with nonnegative simple-root coordinates. -/
private lemma P_spec (v : Fin 8 → ℤ) :
    v ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)) ↔
      v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i := by
  rw [E8posRoots.memP]
  constructor
  · rintro ⟨hq, hv, hc⟩; exact ⟨hv, hq, hc⟩
  · rintro ⟨hv, hq, hc⟩; exact ⟨hq, hv, hc⟩

/-- The coefficient of `e^{-γ}` in the Weyl denominator `∏_{α>0}(1 - e^{-α})`. -/
private noncomputable def C (γ : Fin 8 → ℤ) : ℤ :=
  ∑ T ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)).powerset,
    (if (∑ β ∈ T, β) = γ then (-1 : ℤ) ^ T.card else 0)

private lemma wact_sub (L : List (Fin 8)) (a b : Fin 8 → ℤ) :
    wact L (a - b) = wact L a - wact L b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, wact_add]
  congr 1
  rw [show -b = (-1 : ℤ) • b from by simp, wact_smul]
  simp

/-- The reflection identity `C (αᵢ + sᵢδ) = - C δ` for the coefficient form of the Weyl
denominator. -/
private lemma C_sref (i : Fin 8) (δ : Fin 8 → ℤ) : C (alpha i + sref i δ) = - C δ :=
  E8_weyl_denom_refl (E8posRoots.P : Finset (Fin 8 → ℤ)) P_spec i δ

/-- The coefficient identity along a word of simple reflections. -/
private lemma key (L : List (Fin 8)) (γ : Fin 8 → ℤ) :
    C (wact L γ + (rhoZ - wact L rhoZ)) = (-1 : ℤ) ^ L.length * C γ := by
  induction L generalizing γ with
  | nil =>
      rw [List.length_nil, pow_zero, one_mul]
      congr 1
      simp [wact]
  | cons i L ih =>
      have hsrefrho : sref i rhoZ = rhoZ - alpha i := by
        funext j
        simp only [sref_apply, rhoZ, Pi.sub_apply, alpha_apply]
        ring
      have hwv : wact (i :: L) γ = wact L (sref i γ) := rfl
      have h1 : wact (i :: L) rhoZ = wact L (rhoZ - alpha i) := by
        rw [show wact (i :: L) rhoZ = wact L (sref i rhoZ) from rfl, hsrefrho]
      have hht : rhoZ - wact (i :: L) rhoZ = (rhoZ - wact L rhoZ) + wact L (alpha i) := by
        rw [h1, wact_sub]
        abel
      rw [hwv, hht, List.length_cons]
      have hlin : wact L (sref i γ) + ((rhoZ - wact L rhoZ) + wact L (alpha i))
          = wact L (sref i γ + alpha i) + (rhoZ - wact L rhoZ) := by
        rw [wact_add]
        abel
      rw [hlin, ih (sref i γ + alpha i), pow_succ]
      rw [add_comm (sref i γ) (alpha i), C_sref]
      ring

/-- The coefficients of the Weyl denominator are Weyl-equivariant up to sign, in the `ρ`-shifted form. -/
theorem E8_weyl_C_wact (L : List (Fin 8)) (γ : Fin 8 → ℤ) :
    (∑ T ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)).powerset,
        (if (∑ β ∈ T, β) = Commons.LinearAlgebra.Matrix.Cartan.wact L γ +
            (Commons.LinearAlgebra.Matrix.Cartan.rhoZ -
              Commons.LinearAlgebra.Matrix.Cartan.wact L Commons.LinearAlgebra.Matrix.Cartan.rhoZ)
          then (-1 : ℤ) ^ T.card else 0))
      = (-1 : ℤ) ^ L.length *
        (∑ T ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)).powerset,
          (if (∑ β ∈ T, β) = γ then (-1 : ℤ) ^ T.card else 0)) := by
  exact key L γ

end Commons.LinearAlgebra.Matrix.Cartan
