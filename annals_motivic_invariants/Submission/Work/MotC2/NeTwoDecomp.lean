import Mathlib
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

/-- Decomposition of an element of `L(E)` as `(b₁ + b₂y)/(s₁ + s₂y)` with `bᵢ, sᵢ ∈ L[x]`, and
the first "norm" identity.  Here `y = genY E`, `eK`, `cK` are as in `NeTwoSetup` (so `y ^ 2 + eK * y = cK`).

Route: `IsFractionRing.div_surjective (Coord E) h` writes `h = b / s` with `b, s ∈ L[X,Y]/(W)`;
`CoordinateRing.exists_smul_basis_eq` writes `b = P₁ • 1 + Q₁ • mk Y`, `s = P₂ • 1 + Q₂ • mk Y`;
the workspace lemma `algebraMap_smul_eq_aeval` identifies the images in `L(E)` as
`b₁ + b₂ * y`, `s₁ + s₂ * y` with `bᵢ = xPhi E Pᵢ ∈ Ax E`, `sᵢ = xPhi E Qᵢ ∈ Ax E`.
The remaining identities are the field computation with `y ^ 2 + eK * y = cK`:
`(s₁ + s₂y) * ((s₁ - s₂e) - s₂y) = N₂` and `(b₁ + b₂y) * ((s₁ - s₂e) - s₂y) = u₁ + u₂y`, so
`h * N₂ = u₁ + u₂ * y` (`linear_combination` with `y_sq`).  `N₂ ≠ 0` because `N₂` is the product of
`s₁ + s₂y ≠ 0` and its `negAlgEquiv`-image. -/
lemma NeTwoDecomp (L : Type*) [Field L] (E : WeierstrassCurve L) (h : Func E) :
    ∃ b₁ b₂ s₁ s₂ : Func E, b₁ ∈ Ax E ∧ b₂ ∈ Ax E ∧ s₁ ∈ Ax E ∧ s₂ ∈ Ax E ∧
      s₁ + s₂ * genY E ≠ 0 ∧
      h = (b₁ + b₂ * genY E) / (s₁ + s₂ * genY E) ∧
      (s₁ ^ 2 - s₁ * s₂ * eK E - s₂ ^ 2 * cK E) ≠ 0 ∧
      h * (s₁ ^ 2 - s₁ * s₂ * eK E - s₂ ^ 2 * cK E) =
        (b₁ * s₁ - b₁ * s₂ * eK E - b₂ * s₂ * cK E) +
          (b₂ * s₁ - b₁ * s₂) * genY E := by
  -- Write `h = b / s` with `b, s ∈ L[X,Y]/(W_E)` and both in the `L[X]`-basis `1, Y`.
  obtain ⟨b, s, hs, hbs⟩ := IsFractionRing.div_surjective (Coord E) h
  obtain ⟨P₁, Q₁, hQ₁⟩ := CoordinateRing.exists_smul_basis_eq (W' := E) b
  obtain ⟨P₂, Q₂, hQ₂⟩ := CoordinateRing.exists_smul_basis_eq (W' := E) s
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  -- Images in `L(E)`: `xPhi E Pᵢ` and `xPhi E Qᵢ` times `y = genY E`.
  have hb : algebraMap (Coord E) (Func E) b = xPhi E P₁ + xPhi E Q₁ * genY E := by
    rw [← hQ₁, map_add, (algebraMap_smul_eq_aeval L E P₁).1,
        (algebraMap_smul_eq_aeval L E Q₁).2]
    rfl
  have hs' : algebraMap (Coord E) (Func E) s = xPhi E P₂ + xPhi E Q₂ * genY E := by
    rw [← hQ₂, map_add, (algebraMap_smul_eq_aeval L E P₂).1,
        (algebraMap_smul_eq_aeval L E Q₂).2]
    rfl
  have hss : xPhi E P₂ + xPhi E Q₂ * genY E ≠ 0 := by
    rw [← hs']
    exact fun h0 => hs0 (IsFractionRing.injective (Coord E) (Func E) (by simpa using h0))
  have hh : h = (xPhi E P₁ + xPhi E Q₁ * genY E) / (xPhi E P₂ + xPhi E Q₂ * genY E) := by
    rw [← hbs, hb, hs']
  have hb1 : xPhi E P₁ ∈ Ax E := xPhi_range E ▸ (AlgHom.mem_range (xPhi E)).mpr ⟨P₁, rfl⟩
  have hb2 : xPhi E Q₁ ∈ Ax E := xPhi_range E ▸ (AlgHom.mem_range (xPhi E)).mpr ⟨Q₁, rfl⟩
  have hs1 : xPhi E P₂ ∈ Ax E := xPhi_range E ▸ (AlgHom.mem_range (xPhi E)).mpr ⟨P₂, rfl⟩
  have hs2 : xPhi E Q₂ ∈ Ax E := xPhi_range E ▸ (AlgHom.mem_range (xPhi E)).mpr ⟨Q₂, rfl⟩
  -- The `negAlgEquiv`-image of `s₁ + s₂y` is the conjugate `s₁ - s₂e - s₂y`.
  have hconj : negAlgEquiv E (xPhi E P₂ + xPhi E Q₂ * genY E) =
      xPhi E P₂ - xPhi E Q₂ * eK E - xPhi E Q₂ * genY E := by
    rw [map_add, map_mul, negAlgEquiv_mem_Ax E hs1, negAlgEquiv_mem_Ax E hs2,
      negAlgEquiv_genY E, eK]
    first | refl_ring1 | ring
  -- The norm is the product of `s₁ + s₂y` with its conjugate.
  have hNfac : (xPhi E P₂ + xPhi E Q₂ * genY E) *
      (xPhi E P₂ - xPhi E Q₂ * eK E - xPhi E Q₂ * genY E) =
      xPhi E P₂ ^ 2 - xPhi E P₂ * xPhi E Q₂ * eK E - xPhi E Q₂ ^ 2 * cK E := by
    linear_combination (norm := first | refl_ring1 | ring1) (-(xPhi E Q₂ ^ 2)) * (y_sq E)
  have hNne : xPhi E P₂ ^ 2 - xPhi E P₂ * xPhi E Q₂ * eK E - xPhi E Q₂ ^ 2 * cK E ≠ 0 := by
    rw [← hNfac]
    refine mul_ne_zero hss ?_
    rw [← hconj]
    exact fun h0 => hss ((negAlgEquiv E).injective (by rw [h0, map_zero]))
  -- Cancel the denominator against the conjugate factor.
  have h1 : ((xPhi E P₁ + xPhi E Q₁ * genY E) / (xPhi E P₂ + xPhi E Q₂ * genY E)) *
      ((xPhi E P₂ + xPhi E Q₂ * genY E) * (xPhi E P₂ - xPhi E Q₂ * eK E - xPhi E Q₂ * genY E))
      = (xPhi E P₁ + xPhi E Q₁ * genY E) *
        (xPhi E P₂ - xPhi E Q₂ * eK E - xPhi E Q₂ * genY E) := by
    rw [← mul_assoc, div_mul_cancel₀ _ hss]
  have hfinal : h * (xPhi E P₂ ^ 2 - xPhi E P₂ * xPhi E Q₂ * eK E - xPhi E Q₂ ^ 2 * cK E) =
      (xPhi E P₁ * xPhi E P₂ - xPhi E P₁ * xPhi E Q₂ * eK E -
        xPhi E Q₁ * xPhi E Q₂ * cK E) +
        (xPhi E Q₁ * xPhi E P₂ - xPhi E P₁ * xPhi E Q₂) * genY E := by
    rw [← hNfac, hh, h1]
    linear_combination (norm := first | refl_ring1 | ring1) (-(xPhi E Q₁ * xPhi E Q₂)) * (y_sq E)
  exact ⟨xPhi E P₁, xPhi E Q₁, xPhi E P₂, xPhi E Q₂, hb1, hb2, hs1, hs2, hss, hh, hNne,
    hfinal⟩

end Work.MotC2
