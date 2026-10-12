import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Quant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.ppMass_two_eq` — the two-particle condensate pair mass

For `N = 2` the ordered-pair set is `pairSet 2 = {(0,1), (1,0)}`, and for a *distinct* pair
`(i,j)` the function `PᵢPⱼΦ` is constant in the `i`-th and in the `j`-th coordinate
(`Q0Sector.aP_pair_const_in_i`, `aP_pair_const_in_j`).  As `Fin 2` has exactly the two
coordinates `0,1`, `P₀P₁Φ` is constant on the whole configuration space with value
`P₀P₁Φ 0`; by `aP_comm` the same holds for `P₁P₀Φ`.  Hence each of the two square
integrals over `abox 2 ℓ` (volume `ℓ⁶`) is `(P₀P₁Φ 0)²·ℓ⁶`, and the prefactor
`(ℓ³)⁻¹·(ℓ³)⁻¹` cancels the volume:

    ppMass ℓ Φ = (ℓ³)⁻¹(ℓ³)⁻¹·(2·(P₀P₁Φ 0)²·ℓ⁶) = 2·(P₀P₁Φ 0)².
-/

namespace Work.BoseFixB3.CS.Pieces

open Submission.BoseGases

theorem ppMass_two_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X 2 → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB3.CS.ppMass ℓ Φ
      = 2 * (Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) 0) ^ 2 := by
  set c : ℝ := aP ℓ 0 (aP ℓ 1 Φ) 0
  -- `P₀P₁Φ` is constant, with value `c`
  have hconst0 : ∀ x : Submission.BoseGases.X 2, aP ℓ 0 (aP ℓ 1 Φ) x = c := by
    intro x
    have hx : x = Function.update (Function.update (0 : Submission.BoseGases.X 2) 0 (x 0)) 1 (x 1) := by
      funext k; fin_cases k <;> simp
    rw [hx, aP_pair_const_in_j (ℓ := ℓ) hℓ (i := (0:Fin 2)) (j := (1:Fin 2)) (by decide) hΦc
          (Function.update (0 : Submission.BoseGases.X 2) 0 (x 0)) (x 1),
        aP_pair_const_in_i (ℓ := ℓ) hℓ (i := (0:Fin 2)) (j := (1:Fin 2)) (by decide) hΦc
          (0 : Submission.BoseGases.X 2) (x 0)]
  -- and so is `P₁P₀Φ = P₀P₁Φ`
  have hconst1 : ∀ x : Submission.BoseGases.X 2, aP ℓ 1 (aP ℓ 0 Φ) x = c := by
    intro x
    rw [aP_comm (ℓ := ℓ) hℓ (1 : Fin 2) (0 : Fin 2) hΦc x]
    exact hconst0 x
  -- the two square integrals are `c²·ℓ⁶`
  have hI0 : (∫ x in abox 2 ℓ, (aP ℓ 0 (aP ℓ 1 Φ) x) ^ 2) = c ^ 2 * ℓ ^ 6 := by
    have hfun : (fun x : Submission.BoseGases.X 2 => (aP ℓ 0 (aP ℓ 1 Φ) x) ^ 2) = fun _ => c ^ 2 := by
      funext x; rw [hconst0 x]
    rw [hfun, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      abox_volume 2 ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    ring
  have hI1 : (∫ x in abox 2 ℓ, (aP ℓ 1 (aP ℓ 0 Φ) x) ^ 2) = c ^ 2 * ℓ ^ 6 := by
    have hfun : (fun x : Submission.BoseGases.X 2 => (aP ℓ 1 (aP ℓ 0 Φ) x) ^ 2) = fun _ => c ^ 2 := by
      funext x; rw [hconst1 x]
    rw [hfun, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      abox_volume 2 ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    ring
  have hpair : pairSet 2 = {(0,1), (1,0)} := by decide
  have hnotmem : ((0,1) : Fin 2 × Fin 2) ∉ ({(1,0)} : Finset (Fin 2 × Fin 2)) := by decide
  rw [Work.BoseFixB3.CS.ppMass, hpair, Finset.sum_insert hnotmem, Finset.sum_singleton]
  rw [hI0, hI1]
  have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  field_simp
  ring

end Work.BoseFixB3.CS.Pieces
