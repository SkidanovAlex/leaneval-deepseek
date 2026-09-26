import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic

namespace Work.Kernels.ClearLink

open Work.Kernels
open Matrix

/-- `Π^Δ_{k₁,k₂,k₃}(τ) = Δ(τ) · Π_{k₁,k₂,k₃}(τ)`: the cleared diagonal matrix is the
diagonal matrix scaled by `Δ(τ)`. -/
private lemma PiMatDelta_eq_smul (v : Fin 3 → ℤ) (τ : UpperHalfPlane) :
    PiMatDelta v τ = DeltaFun τ • PiMat v τ := by
  ext i j
  simp only [PiMatDelta, PiMat, Matrix.diagonal, Matrix.smul_apply]
  by_cases hij : i = j <;> simp [hij]

/-- The matrix form of `K_+^{clear} = Δ(τ)Δ(z)^e(j(τ)−j(z)) · Υ_+`: multiplying each entry
of `Υ_+` by the growth prefactor clears the pole `(j(τ)−j(z))⁻¹`.  This is the entrywise
algebraic identity underlying the kernel identity `KPlusClear_eq_smul`. -/
private lemma UpsilonPlusClear_eq_smul_aux (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : UpperHalfPlane) (h : jInvariantFun τ ≠ jInvariantFun z) :
    UpsilonPlusClear d τ z = growthPrefactor d τ z • UpsilonPlus d τ z := by
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr h
  rcases hd with rfl | rfl
  · rw [show UpsilonPlusClear 8 τ z =
          ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ •
            (PiMatDelta ![6, 4, 2] τ *
              !![jInvariantFun τ - jInvariantFun z, 0, 1;
                 -2 * (jInvariantFun τ - jInvariantFun z), -2, 0; 1, 0, 0] *
              PiMat ![12, 10, 8] z) from rfl,
        show UpsilonPlus 8 τ z =
          ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z *
              (jInvariantFun τ - jInvariantFun z))⁻¹ •
            (PiMat ![6, 4, 2] τ *
              !![jInvariantFun τ - jInvariantFun z, 0, 1;
                 -2 * (jInvariantFun τ - jInvariantFun z), -2, 0; 1, 0, 0] *
              PiMat ![12, 10, 8] z) from rfl,
        show growthPrefactor 8 τ z =
          DeltaFun τ * DeltaFun z ^ 1 * (jInvariantFun τ - jInvariantFun z) from rfl]
    set J := jInvariantFun τ - jInvariantFun z with hJdef
    set C := (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hC
    rw [PiMatDelta_eq_smul]
    simp only [Matrix.smul_mul, smul_smul, pow_one]
    congr 1
    field_simp
  · rw [show UpsilonPlusClear 24 τ z =
          ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ •
            (PiMatDelta ![14, 12, 10] τ *
              !![6 * (jInvariantFun τ - jInvariantFun z), 0,
                 c1728 - 6 * (jInvariantFun τ - jInvariantFun z);
                 -12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z) +
                     5 * c1728 * (jInvariantFun τ - jInvariantFun z),
                   -2 * c1728,
                   12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z) -
                     7 * c1728 * (jInvariantFun τ - jInvariantFun z);
                 c1728 + 6 * (jInvariantFun τ - jInvariantFun z), 0,
                   -6 * (jInvariantFun τ - jInvariantFun z)] *
              (DeltaFun z • PiMat ![4, 2, 0] z)) from rfl,
        show UpsilonPlus 24 τ z =
          ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ •
            (PiMat ![14, 12, 10] τ *
              !![6, 0, c1728 * (jInvariantFun τ - jInvariantFun z)⁻¹ - 6;
                 -12 * jInvariantFun τ + 5 * c1728,
                   -2 * c1728 * (jInvariantFun τ - jInvariantFun z)⁻¹,
                   12 * jInvariantFun τ - 7 * c1728;
                 c1728 * (jInvariantFun τ - jInvariantFun z)⁻¹ + 6, 0, -6] *
              PiMat ![4, 2, 0] z) from rfl,
        show growthPrefactor 24 τ z =
          DeltaFun τ * DeltaFun z ^ 2 * (jInvariantFun τ - jInvariantFun z) from rfl]
    set J := jInvariantFun τ - jInvariantFun z with hJdef
    set C := (36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hC
    have hMJ : (!![6 * J, 0, c1728 - 6 * J;
          -12 * jInvariantFun τ * J + 5 * c1728 * J, -2 * c1728,
            12 * jInvariantFun τ * J - 7 * c1728 * J;
          c1728 + 6 * J, 0, -6 * J] : Matrix (Fin 3) (Fin 3) ℂ)
        = J • !![6, 0, c1728 * J⁻¹ - 6;
                  -12 * jInvariantFun τ + 5 * c1728, -2 * c1728 * J⁻¹,
                    12 * jInvariantFun τ - 7 * c1728;
                  c1728 * J⁻¹ + 6, 0, -6] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> field_simp
    rw [hMJ, PiMatDelta_eq_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    field_simp

theorem KPlusClear_eq_smul (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : UpperHalfPlane)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KPlusClear d τ z = Work.Kernels.growthPrefactor d τ z * Work.Kernels.KPlus d τ z := by
  have hU := UpsilonPlusClear_eq_smul_aux d hd τ z h
  simp only [KPlusClear, KPlus]
  rw [hU]
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end Work.Kernels.ClearLink
