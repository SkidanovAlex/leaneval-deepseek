/-
# `φ = 0` on the four "grazing" group-algebra elements

CKMRV Theorem 4.9(3) expresses the residue of the kernel along the orbit of `z` through the
functional `φ = (φ₊ + φ₋)/2` on `ℂ[SL(2,ℤ)]`.  Along the tangency arcs of the domain `𝒟`
(`Work.Asymptotics.arcT`) the relevant orbit elements are the four

  `T S T`, `(T S)⁻¹`, `S T`, `(T S T)⁻¹`,

and on each of them `φ` vanishes (equivalently `φ₊ + φ₋ = 0`), which is what makes the
corresponding coincidences of the kernel contour removable.  Since `φ` is computed from the
six-dimensional representation by `φ x = (σ_R x) 0 1` and `σ_R` kills the central `-I`, `φ` is
insensitive to the sign of a group element, so the vanishings also hold for the negatives of
the four elements (which act on `ℍ` by the same Möbius map).
-/
import Mathlib
import Submission.Work.Residues.Quotient
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Residues.phi_Tpow_mul_inv_eq_zero
import Submission.Work.Residues.phiPlus_crossed_translates_eq_zero
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics.Graze

open Work.Kernels

/-- The four "grazing" elements of `SL(2,ℤ)` of the tangency arcs. -/
def GrazeElem (γ : SL(2, ℤ)) : Prop :=
  γ = ModularGroup.T * ModularGroup.S * ModularGroup.T ∨ γ = (ModularGroup.T * ModularGroup.S)⁻¹
    ∨ γ = ModularGroup.S * ModularGroup.T ∨ γ = (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹

private lemma single_mul_single_one (a b : SL(2,ℤ)) :
    (MonoidAlgebra.single a (1 : ℂ)) * (MonoidAlgebra.single b (1 : ℂ)) = MonoidAlgebra.single (a * b) (1 : ℂ) := by
  rw [MonoidAlgebra.single_mul_single, mul_one]

/-- `φ` vanishes on `T S T`. -/
theorem phi_TST_eq_zero :
    Work.Residues.phi (MonoidAlgebra.single (ModularGroup.T * ModularGroup.S * ModularGroup.T) (1:ℂ)) = 0 := by
  rw [Work.Residues.phi_eq_sigmaR]
  have h : (MonoidAlgebra.single (ModularGroup.T * ModularGroup.S * ModularGroup.T) (1:ℂ) : R)
      = (R_T * R_S) * R_T := by
    rw [R_T, R_S, single_mul_single_one, single_mul_single_one]
  rw [h, map_mul, map_mul, Work.Residues.sigmaR_R_T, Work.Residues.sigmaR_R_S]
  simp [Matrix.mul_apply, Fin.sum_univ_six, Work.Modular.sigmaT, Work.Modular.sigmaS]

/-- `φ` vanishes on `(T S)⁻¹`. -/
theorem phi_TSinv_eq_zero :
    Work.Residues.phi (MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S)⁻¹) (1:ℂ)) = 0 := by
  rw [Work.Residues.phi_eq_sigmaR, Work.Residues.sigmaR_single_TS_inv]
  simp [Matrix.mul_apply, Fin.sum_univ_six, Work.Modular.sigmaS, Work.Modular.sigmaTinv]

/-- `φ` vanishes on `S T`. -/
theorem phi_ST_eq_zero :
    Work.Residues.phi (MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) (1:ℂ)) = 0 := by
  rw [Work.Residues.phi_eq_sigmaR]
  have h : (MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) (1:ℂ) : R)
      = R_S * R_T := by
    rw [R_T, R_S, single_mul_single_one]
  rw [h, map_mul, Work.Residues.sigmaR_R_S, Work.Residues.sigmaR_R_T]
  simp [Matrix.mul_apply, Fin.sum_univ_six, Work.Modular.sigmaS, Work.Modular.sigmaT]

/-- `φ` vanishes on `(T S T)⁻¹`. -/
theorem phi_TSTinv_eq_zero :
    Work.Residues.phi (MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) (1:ℂ)) = 0 := by
  rw [Work.Residues.phi_eq_sigmaR]
  have h : (MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) (1:ℂ) : R)
      = (MonoidAlgebra.single (ModularGroup.T)⁻¹ (1:ℂ))
        * ((MonoidAlgebra.single (ModularGroup.S)⁻¹ (1:ℂ))
            * (MonoidAlgebra.single (ModularGroup.T)⁻¹ (1:ℂ))) := by
    rw [single_mul_single_one, single_mul_single_one]
    congr 1
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  rw [h, map_mul, map_mul, Work.Residues.sigmaR_single_T_inv, Work.Residues.sigmaR_single_S_inv]
  simp [Matrix.mul_apply, Fin.sum_univ_six, Work.Modular.sigmaTinv, Work.Modular.sigmaS]

/-- `φ` vanishes on the four grazing elements. -/
theorem phi_graze (γ : SL(2, ℤ)) (hγ : GrazeElem γ) : Work.Residues.phi (MonoidAlgebra.single γ (1:ℂ)) = 0 := by
  rcases hγ with h | h | h | h <;> subst h
  · exact phi_TST_eq_zero
  · exact phi_TSinv_eq_zero
  · exact phi_ST_eq_zero
  · exact phi_TSTinv_eq_zero

/-- `σ_R` kills the central `-I`, so `φ (single (-γ) 1) = φ (single γ 1)`. -/
theorem phi_neg (δ : SL(2, ℤ)) :
    Work.Residues.phi (MonoidAlgebra.single (-δ) (1:ℂ)) = Work.Residues.phi (MonoidAlgebra.single δ (1:ℂ)) := by
  have h : (MonoidAlgebra.single (-δ) (1:ℂ) : R) = Work.Residues.Rneg * MonoidAlgebra.single δ 1 := by
    rw [Work.Residues.Rneg, single_mul_single_one]
    congr 1
    rw [neg_mul, one_mul]
  rw [h, Work.Residues.phi_eq_sigmaR, Work.Residues.phi_eq_sigmaR, map_mul,
    Work.Residues.sigmaR_Rneg, one_mul]

/-- The relation `φ₊ + φ₋ = 2 φ` in the direction used below. -/
theorem two_mul_phi (x : R) :
    Work.Residues.phiPlus x + Work.Residues.phiMinus x = 2 * Work.Residues.phi x := by
  rw [Work.Residues.phi_eq_half_phiPlus_add_phiMinus x]; ring

/-- `φ = 0` implies `φ₊ + φ₋ = 0`. -/
theorem phiPlus_add_phiMinus_eq_zero {x : R} (h : Work.Residues.phi x = 0) :
    Work.Residues.phiPlus x + Work.Residues.phiMinus x = 0 := by
  rw [two_mul_phi, h, mul_zero]

/-- `φ₊ + φ₋` vanishes on the four grazing elements. -/
theorem phiPair_graze (γ : SL(2, ℤ)) (hγ : GrazeElem γ) :
    Work.Residues.phiPlus (MonoidAlgebra.single γ (1:ℂ))
      + Work.Residues.phiMinus (MonoidAlgebra.single γ (1:ℂ)) = 0 :=
  phiPlus_add_phiMinus_eq_zero (phi_graze γ hγ)

/-- `φ₊ + φ₋` vanishes on the negatives of the grazing elements. -/
theorem phiPair_graze_neg (γ : SL(2, ℤ)) (hγ : GrazeElem γ) :
    Work.Residues.phiPlus (MonoidAlgebra.single (-γ) (1:ℂ))
      + Work.Residues.phiMinus (MonoidAlgebra.single (-γ) (1:ℂ)) = 0 := by
  have h : Work.Residues.phiPlus (MonoidAlgebra.single (-γ) (1:ℂ))
      + Work.Residues.phiMinus (MonoidAlgebra.single (-γ) (1:ℂ))
      = Work.Residues.phiPlus (MonoidAlgebra.single γ (1:ℂ))
      + Work.Residues.phiMinus (MonoidAlgebra.single γ (1:ℂ)) := by
    rw [two_mul_phi, two_mul_phi, phi_neg γ]
  rw [h, phiPair_graze γ hγ]

/-- The cleared kernel vanishes on the orbit of a grazing element (away from the elliptic points). -/
theorem KfunClear_vanish_graze (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (γ : SL(2, ℤ)) (hγ : GrazeElem γ) :
    ∀ z : UpperHalfPlane, Work.Residues.jprime z ≠ 0 →
      KfunClear ℓ d (γ • z) z = 0 :=
  KfunClear_vanish_of_phiPair ℓ d hd γ (phiPair_graze γ hγ)

/-- The cleared kernel vanishes on the orbit of a *negative* grazing element. -/
theorem KfunClear_vanish_graze_neg (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (γ : SL(2, ℤ)) (hγ : GrazeElem γ) :
    ∀ z : UpperHalfPlane, Work.Residues.jprime z ≠ 0 →
      KfunClear ℓ d ((-γ) • z) z = 0 :=
  KfunClear_vanish_of_phiPair ℓ d hd (-γ) (phiPair_graze_neg γ hγ)

end Work.Asymptotics.Graze
