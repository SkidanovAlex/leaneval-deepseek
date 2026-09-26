/-
# The crossed orbit points carry no pole of the kernel

For `τ = n +ᵥ w` with `n = ±1` and the **crossed** orbit point
`ζ = (S T^{-j} S) • w` with `j` odd (`|j| ∈ {1,3}`), the value function of the kernel's
numerator vanishes:

  `AfunFun ℓ d (n +ᵥ w) ((S T^{-j} S) • w) = 0`.

Since `K^{(d)}(τ,·)` has residue `AfunFun ℓ d (γ•w) w / j'(γ•w)` at the orbit point `γ•w`
(`Work.Residues.hasResidue_of_cleared`), this says that the crossed points carry no pole of
the kernel: the two half-kernels `K_±` have opposite residues there
(`Work.Residues.hasResidue_slash_KPlus_orbit'` / `..._KMinus_orbit'`), and the combination is
regular.

The two ingredients are

* `Work.Residues.phi_Tpow_S_Tpow_S_eq_zero` : `φ (T^n S T^j S) = 0` for `n = ±1` and odd `j`,
  where `φ = (φ₊ + φ₋)/2` is the functional CKMRV (3.12);
* `Work.Asymptotics.KfunClear_vanish_of_phiPair` : `φ₊(δ) + φ₋(δ) = 0` forces
  `KfunClear ℓ d (δ • z) z = 0`, hence `AfunFun ℓ d (δ • z) z = 0`.

The group element `δ = T^n S T^j S` satisfies `δ • ((S T^{-j} S) • w) = T^n • w = n +ᵥ w`
(the point computation is `STinvpowS_smul` below).

This is a load-bearing input of the spike (`tilePPWindow_spike`) part of the tile
principal-part window `Work.Asymptotics.tilePPWindow_lowHalf`: on the spike the contour point
`ζ = i t` may approach one of the crossed orbit points, and the maximum-principle argument needs
`K(τ,·) − (n/2π)/(· − w)` to be holomorphic there.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Asymptotics.phi_Tpow_S_Tpow_S_eq_zero

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra

namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-- The point computation behind the crossed-point vanishing:
`(T^n S T^j S) • ((S T^{-j} S) • w) = T^n • w`. -/
lemma STinvpowS_smul (n j : ℤ) (w : ℍ) :
    ((ModularGroup.T ^ n * ModularGroup.S * ModularGroup.T ^ j * ModularGroup.S)
        • ((ModularGroup.S * ModularGroup.T ^ (-j) * ModularGroup.S) • w))
      = (ModularGroup.T ^ n) • w := by
  simp only [mul_smul]
  rw [S_smul_S_smul]
  have h1 : ModularGroup.T ^ j • (ModularGroup.T ^ (-j) • (ModularGroup.S • w))
      = (ModularGroup.T ^ j * ModularGroup.T ^ (-j)) • (ModularGroup.S • w) :=
    (mul_smul _ _ _).symm
  rw [h1, ← _root_.zpow_add, add_neg_cancel, zpow_zero, one_smul, S_smul_S_smul]

/-- **The crossed orbit points carry no pole.**  For `τ = n +ᵥ w` (`n = ±1`) and `j` odd
(`|j| ∈ {1,3}`), the numerator `AfunFun` of the kernel vanishes at the crossed orbit point
`(S T^{-j} S) • w`. -/
theorem AfunFun_crossed_vanish (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n j : ℤ) (hn : n = 1 ∨ n = -1) (hj : j = 1 ∨ j = -1 ∨ j = 3 ∨ j = -3)
    (w : ℍ) (hw : jprime w ≠ 0) :
    AfunFun ℓ d ((n : ℝ) +ᵥ w)
      ((ModularGroup.S * ModularGroup.T ^ (-j) * ModularGroup.S) • w) = 0 := by
  set δ : SL(2,ℤ) := ModularGroup.T ^ n * ModularGroup.S * ModularGroup.T ^ j * ModularGroup.S
    with hδ
  set z : ℍ := (ModularGroup.S * ModularGroup.T ^ (-j) * ModularGroup.S) • w with hz
  have hphi : Work.Residues.phi (MonoidAlgebra.single δ (1 : ℂ)) = 0 := by
    rw [hδ]
    exact Work.Residues.phi_Tpow_S_Tpow_S_eq_zero n j hn hj
  have hδpair : Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ))
      + Work.Residues.phiMinus (MonoidAlgebra.single δ (1 : ℂ)) = 0 := by
    have h := Work.Residues.phi_eq_half_phiPlus_add_phiMinus (MonoidAlgebra.single δ (1 : ℂ))
    rw [hphi] at h
    rcases div_eq_zero_iff.mp h.symm with h0 | h2
    · exact h0
    · exact absurd h2 (by norm_num)
  have hz' : jprime z ≠ 0 := by
    rw [hz]
    exact jprime_smul_ne_zero_of_slash
      (ModularGroup.S * ModularGroup.T ^ (-j) * ModularGroup.S) w hw
  have hv := KfunClear_vanish_of_phiPair ℓ d hd δ hδpair z hz'
  rw [KfunClear_eq_mul_AfunFun] at hv
  have hD : DeltaFun (δ • z) * DeltaFun z ^ dpow d ≠ 0 :=
    mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero _)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero _))
  have hfac : AfunFun ℓ d (δ • z) z = 0 := by
    rcases mul_eq_zero.mp hv with h0 | h0
    · exact absurd h0 hD
    · exact h0
  have hpt : δ • z = (n : ℝ) +ᵥ w := by
    rw [hδ, hz, STinvpowS_smul]
    exact modular_T_zpow_smul w n
  rwa [hpt] at hfac

end Work.Asymptotics
