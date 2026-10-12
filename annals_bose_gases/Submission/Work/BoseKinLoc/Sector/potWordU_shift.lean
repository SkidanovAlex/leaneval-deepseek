import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `potWordU` is translation covariant at fixed window anchor

`potWordU N v g ℓ μ u x` is the potential part of FS's localised box word
`H_{Λ,u}(μ)_N` (FS `eq:Def_HB`), built from the cell-`u` translates
`wLoc ℓ h u x y = χ_u(x)·W(x−y)·χ_u(y)` (`χ_u(x) = χ((ℓ⁻¹)•x − u)`).

The moving box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` is the translate by `ℓu` of the
anchored box `Λ(0)`, and the window is the correspondingly shifted one,

    `χ_u(x) = χ_0(x − ℓu)`,   hence   `wLoc ℓ h u x y = wLoc ℓ h 0 (x−ℓu) (y−ℓu)`.

The pair term of `potWordU` is therefore invariant under shifting the
configuration by `−ℓu`, and the one-body `y`-integral is invariant too once
one translates the integration variable `y ↦ y − ℓu`.  That is the content
of the present lemma.
-/

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

/-- The cell-`u` window is the anchored window of the shifted argument:
`χ_u(x) = χ_0(x − ℓu)`. -/
lemma chiU_shift (ℓ : ℝ) (hℓ : ℓ ≠ 0) (u x : ℝ³) :
    chiU ℓ u x = chiU ℓ 0 (x - ℓ • u) := by
  rw [chiU, chiU, sub_zero]
  congr 1
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hℓ, one_smul]

/-- The localised kernel is translation covariant:
`wLoc ℓ h u x y = wLoc ℓ h 0 (x−ℓu) (y−ℓu)`. -/
lemma wLoc_shift (ℓ : ℝ) (hℓ : ℓ ≠ 0) (h : ℝ³ → ℝ) (u x y : ℝ³) :
    wLoc ℓ h u x y = wLoc ℓ h 0 (x - ℓ • u) (y - ℓ • u) := by
  rw [wLoc, wLoc, chiU_shift ℓ hℓ u x, chiU_shift ℓ hℓ u y,
    show (x - ℓ • u) - (y - ℓ • u) = x - y from by abel]

/-- The one-body `y`-integral of the localised kernel is translation covariant:
`∫ y, wLoc ℓ g u t y = ∫ y, wLoc ℓ g 0 (t−ℓu) y`
(the integration variable absorbs the window shift). -/
lemma integral_wLoc_shift (ℓ : ℝ) (hℓ : ℓ ≠ 0) (g : ℝ³ → ℝ) (u t : ℝ³) :
    (∫ y : ℝ³, wLoc ℓ g u t y) = ∫ y : ℝ³, wLoc ℓ g 0 (t - ℓ • u) y := by
  simp_rw [wLoc_shift ℓ hℓ g u t]
  exact MeasureTheory.integral_sub_right_eq_self
    (fun y : ℝ³ => wLoc ℓ g 0 (t - ℓ • u) y) (ℓ • u)

theorem potWordU_shift {N : ℕ} (v g : ℝ³ → ℝ) (ℓ μ : ℝ) (hℓ : 0 < ℓ) (u : ℝ³)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.potWordU N v g ℓ μ 0 (fun i : Fin N => x i - ℓ • u)
      = Work.BoseKinLoc.potWordU N v g ℓ μ u x := by
  have hℓ' : ℓ ≠ 0 := ne_of_gt hℓ
  have h1 : (∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g 0 (x i - ℓ • u) y)
      = ∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g u (x i) y := by
    exact Finset.sum_congr rfl fun i _ => (integral_wLoc_shift ℓ hℓ' g u (x i)).symm
  have h2 : (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
        wLoc ℓ v 0 (x ij.1.1 - ℓ • u) (x ij.1.2 - ℓ • u))
      = ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
        wLoc ℓ v u (x ij.1.1) (x ij.1.2) := by
    exact Finset.sum_congr rfl fun ij _ =>
      (wLoc_shift ℓ hℓ' v u (x ij.1.1) (x ij.1.2)).symm
  show -μ * (∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g 0 (x i - ℓ • u) y)
      + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
          wLoc ℓ v 0 (x ij.1.1 - ℓ • u) (x ij.1.2 - ℓ • u)
    = -μ * (∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g u (x i) y)
      + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
          wLoc ℓ v u (x ij.1.1) (x ij.1.2)
  rw [h1, h2]

end Work.BoseKinLoc.Sector
