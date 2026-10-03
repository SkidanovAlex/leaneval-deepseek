import Mathlib
import Submission.Work.Peluse.UControl.PetLevelChainDefs
import Submission.Work.Peluse.UControl.level1Compare

/-!
# The level chain for quadratic `P`

For `P.natDegree = 2` the `Phase1Terminal` state is already the level-`(d-1)` = level-`1` state
(its slots have degree one), so `PetLevelChain P` is `level1Compare` with `Nstep = 1`,
`D = levelOneDatum n` and `C₀ = 3^n`: the comparison of `level1Compare` is *lossless*
(`B ≤ 3^n · linFamAvg`), and `petChainLevel B 1 = B^2/2000 ≤ B` because `B ≤ 1`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

theorem petLevelChain_quadratic (P : Polynomial ℤ) (hdeg : P.natDegree = 2) :
    PetLevelChain P := by
  unfold PetLevelChain
  rw [hdeg]
  intro n hn lc Y hT
  refine ⟨1, levelOneDatum n, (3 : ℝ) ^ n, le_refl 1,
    one_le_pow₀ (n := n) (by norm_num : (1:ℝ) ≤ 3), ?_, ?_⟩
  · rw [levelOneDatum_card_I_one]
    have h4 : 2 ^ n ≥ 4 := by
      calc (2 : ℕ) ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
        _ = 4 := by norm_num
    omega
  · intro Nx M γ' Ftop G g c Dsb B hNx1 hGb hGs hgb hgs hM hH hc hB0 hB1 hwin hSB htop hg hlam
    obtain ⟨b, β, hshift, havg⟩ :=
      level1Compare (n := n) hn lc Y hT Nx M γ' Ftop G g htop hg hSB (by omega) hH hlam
    refine ⟨b, β, ?_, ?_⟩
    · intro a ha i y hy
      have hD : (0 : ℤ) ≤ (Dsb : ℤ) := by positivity
      have hN : (0 : ℤ) ≤ (Nx : ℤ) := by positivity
      have h1 := hshift a ha i y hy
      have h2 : ((2 ^ 1 * Dsb : ℕ) : ℤ) * (Nx : ℤ) = 2 * (Dsb : ℤ) * (Nx : ℤ) := by
        push_cast; ring
      rw [h2]
      nlinarith [h1, hD, hN]
    · have hB2 : petChainLevel B 1 = B ^ 2 / 2000 := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, petChainLevel_succ, petChainLevel_zero]
      rw [hB2]
      have hBle : B ^ 2 / 2000 ≤ B := by
        have h1 : B ^ 2 ≤ B := by nlinarith
        linarith
      exact le_trans hBle havg

end

end Work.Peluse.UControl
