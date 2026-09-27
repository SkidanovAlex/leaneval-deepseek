import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kl_defs
import Submission.Work.KT.Fund.kl_v_cls

/-!
# `Work.KT.Fund.klV_unit` — the two factors of the linear clutching splitting are units

The "inside" factor `klV X n b E = z • E + E b + (1 - E)` and the Bott unit
`klV0 X n E = z • E + (1 - E)` of the linear clutching splitting
(`Work.KT.Fund.kl_defs`) are units of matrices over `C(X × S¹, ℂ)`, under the pointwise
invertibility hypothesis `hins` on `z • 1 + t • (E b)(x)`.

Both are slices of the homotopy matrix `klHom X n b E` over `(X × I) × S¹`
(`Work.KT.Fund.kl_hom_defs`), which is a unit by `Work.KT.Fund.isUnit_klHom`; the two
slices `incl1 X` (`t = 1`) and `incl0 X` (`t = 0`) give `klV` and `klV0`
(`klHom_slice1`, `klHom_slice0`), and units are preserved by pull-back along a continuous map.
-/

namespace Work.KT.Fund

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Pull-back of a unit of matrices over `C(Z, ℂ)` along a continuous map `g : C(Y, Z)`:
precomposition with `g` is a ring homomorphism, hence preserves units. -/
lemma isUnit_map_comp {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    {n : ℕ} (g : C(Y, Z)) {M : Matrix (Fin n) (Fin n) C(Z, ℂ)} (hM : IsUnit M) :
    IsUnit (M.map (fun f => f.comp g)) := by
  have hφ : ⇑((ContinuousMap.compRightAlgHom ℂ ℂ g).toRingHom : C(Z, ℂ) →+* C(Y, ℂ))
      = fun f : C(Z, ℂ) => f.comp g := by
    funext f
    exact ContinuousMap.compRightAlgHom_apply ℂ ℂ g f
  have h := IsUnit.map
    (f := (ContinuousMap.compRightAlgHom ℂ ℂ g).toRingHom.mapMatrix) hM
  rw [RingHom.mapMatrix_apply, hφ] at h
  exact h

/-- The "inside" factor `klV` of the linear clutching splitting is a unit. -/
theorem klV_isUnit (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hins : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + t • ((E * b).map (fun f => f x)))) :
    IsUnit (klV X n b E) := by
  have hH : IsUnit (klHom X n b E) := isUnit_klHom X n b E hE hins
  rw [← klHom_slice1 X n b E]
  exact isUnit_map_comp (incl1 X) hH

/-- The Bott unit `klV0` is a unit. -/
theorem klV0_isUnit (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hins : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + t • ((E * b).map (fun f => f x)))) :
    IsUnit (klV0 X n E) := by
  have hH : IsUnit (klHom X n b E) := isUnit_klHom X n b E hE hins
  rw [← klHom_slice0 X n b E]
  exact isUnit_map_comp (incl0 X) hH

theorem klV_unit (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) (hc : E * b = b * E)
    (hins : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + t • ((E * b).map (fun f => f x)))) :
    IsUnit (Work.KT.Fund.klV X n b E) ∧ IsUnit (Work.KT.Fund.klV0 X n E) :=
  ⟨klV_isUnit X n b E hE hins, klV0_isUnit X n b E hE hins⟩

end

end Work.KT.Fund
