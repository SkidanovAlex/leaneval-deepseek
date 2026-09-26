import Mathlib
import Submission.Work.Asymptotics.Graze.KfunClear_vanish_of_phiPair_uncond
import Submission.Work.Residues.phi_Tpow_mul_inv_eq_zero

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

/-- **The `T^m S T^{-n}`-branch vanishing of the cleared CKMRV kernel.**  For `n, m = ±1` and
any `σ ∈ ℍ` the cleared CKMRV kernel vanishes at the pair
`(n +ᵥ σ, m +ᵥ (S • σ))`, i.e. at `(τ, z)` with `j τ = j z` on the branch `z = T^m S T^{-n} • τ`.

Route (all ingredients already proved in the workspace, no new analysis needed):
put `z := (m:ℝ) +ᵥ (S • σ)`; then `(n:ℝ) +ᵥ σ = δ • z` for
`δ = T^m * S * T^n`-conjugate (`δ = T^m * S * T^{-n}` as an element of `SL(2,ℤ)`, up to the
central `-I`), and `z = (m:ℝ) +ᵥ (S•σ)` means `τ = T^{-n}•(S•z)`, so `δ` is one of
`T^k * (T*S)⁻¹`, `T^k * (T⁻¹*S)⁻¹` with `k = m ∈ {±1}`.  Finally
`Work.Residues.phi_Tpow_mul_inv_eq_zero (k)` gives `φ` of that monomial `= 0`,
`Work.Residues.phi_eq_half_phiPlus_add_phiMinus` turns `φ = 0` into
`φ₊ + φ₋ = 0`, and
`Work.Asymptotics.Graze.KfunClear_vanish_of_phiPair_uncond` (see
`Submission/Work/Asymptotics/Graze/KfunClear_vanish_of_phiPair_uncond.lean`, whose usage
template is `Submission/Work/Asymptotics/arcT_grazing_vanish.lean`) gives
`KfunClear ℓ d (δ • z) z = 0` for every `z`.

Numerically verified (faithful mirror of `Kernels.lean`, `dps = 40`): for general `σ`,
`KPlusClear` and `KMinusClear` are individually NONzero at the `m = ±1` pairs but are *equal*
there, so the sum `KfunClear = (KPlusClear + KMinusClear)/2` vanishes to `~1e-37`; at the
`m = 0` pairs both halves vanish separately.  (A reviewer's mirror that found the `m = ±1`
cases "failing" only checked `KPlusClear` alone.)  Numerically
`(j τ - j z) · Kfun(τ, z) → 0` linearly along all four branches. -/
theorem tile_KfunClear_shift_vanish (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n m : ℤ) (hn : n = 1 ∨ n = -1) (hm : m = 1 ∨ m = -1) (σ : UpperHalfPlane) :
    Work.Kernels.KfunClear ℓ d ((n : ℝ) +ᵥ σ) ((m : ℝ) +ᵥ (ModularGroup.S • σ)) = 0 := by
  -- From `φ (single δ 1) = 0` deduce `φ₊ (single δ 1) + φ₋ (single δ 1) = 0`.
  have pair_of_phi : ∀ δ : SL(2, ℤ),
      Work.Residues.phi (MonoidAlgebra.single δ (1 : ℂ)) = 0 →
      Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ))
        + Work.Residues.phiMinus (MonoidAlgebra.single δ (1 : ℂ)) = 0 := by
    intro δ hδ
    have hh := Work.Residues.phi_eq_half_phiPlus_add_phiMinus (MonoidAlgebra.single δ (1 : ℂ))
    rw [hδ] at hh
    rcases div_eq_zero_iff.mp hh.symm with h0 | h2
    · exact h0
    · exact absurd h2 (by norm_num)
  rcases hm with hm | hm
  · -- branch `m = 1`
    subst hm
    push_cast
    set δ : SL(2, ℤ) := ModularGroup.T ^ n * (ModularGroup.T * ModularGroup.S)⁻¹ with hδdef
    have hphi : Work.Residues.phi (MonoidAlgebra.single δ (1 : ℂ)) = 0 := by
      have heq : MonoidAlgebra.single δ (1 : ℂ)
          = MonoidAlgebra.single (ModularGroup.T ^ n) (1 : ℂ)
            * MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S)⁻¹) (1 : ℂ) := by
        rw [hδdef, MonoidAlgebra.single_mul_single, mul_one]
      rw [heq]
      exact (Work.Residues.phi_Tpow_mul_inv_eq_zero n).1
    have hz : (1 : ℝ) +ᵥ (ModularGroup.S • σ) = (ModularGroup.T * ModularGroup.S) • σ := by
      rw [mul_smul, ← UpperHalfPlane.modular_T_smul (ModularGroup.S • σ)]
    have hδz : δ • ((1 : ℝ) +ᵥ (ModularGroup.S • σ)) = (n : ℝ) +ᵥ σ := by
      rw [hz, hδdef, mul_smul, inv_smul_smul, UpperHalfPlane.modular_T_zpow_smul]
    have hv := Work.Asymptotics.Graze.KfunClear_vanish_of_phiPair_uncond ℓ d hd δ
      (pair_of_phi δ hphi) ((1 : ℝ) +ᵥ (ModularGroup.S • σ))
    rw [hδz] at hv
    exact hv
  · -- branch `m = -1`
    subst hm
    set δ : SL(2, ℤ) := ModularGroup.T ^ n * (ModularGroup.T⁻¹ * ModularGroup.S)⁻¹ with hδdef
    have hphi : Work.Residues.phi (MonoidAlgebra.single δ (1 : ℂ)) = 0 := by
      have heq : MonoidAlgebra.single δ (1 : ℂ)
          = MonoidAlgebra.single (ModularGroup.T ^ n) (1 : ℂ)
            * MonoidAlgebra.single ((ModularGroup.T⁻¹ * ModularGroup.S)⁻¹) (1 : ℂ) := by
        rw [hδdef, MonoidAlgebra.single_mul_single, mul_one]
      rw [heq]
      exact (Work.Residues.phi_Tpow_mul_inv_eq_zero n).2
    have hz : (((-1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • σ))
        = (ModularGroup.T⁻¹ * ModularGroup.S) • σ := by
      rw [mul_smul, ← UpperHalfPlane.modular_T_zpow_smul (ModularGroup.S • σ) (-1),
        _root_.zpow_neg_one]
    have hδz : δ • ((((-1 : ℤ) : ℝ)) +ᵥ (ModularGroup.S • σ)) = (n : ℝ) +ᵥ σ := by
      rw [hz, hδdef, mul_smul, inv_smul_smul, UpperHalfPlane.modular_T_zpow_smul]
    have hv := Work.Asymptotics.Graze.KfunClear_vanish_of_phiPair_uncond ℓ d hd δ
      (pair_of_phi δ hphi) ((((-1 : ℤ) : ℝ)) +ᵥ (ModularGroup.S • σ))
    rw [hδz] at hv
    exact hv

end Work.Asymptotics.Tile
