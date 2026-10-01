import Mathlib
import Submission.Commons.Analysis.Integral.boxWindow_C1_facts

namespace Commons.Analysis.Integral

set_option maxHeartbeats 4000000

/-- The polynomial identity underlying `boxWindow_regionB_mid`: on `[1/2,3/4]` the
difference `4β²·boxDEN β·(1/30 - (3/4-β)m) - (4β²·boxNUM β + boxDEN β(1-16β²))(β-1/2)²`
(which is `4β²·boxDEN β` times the difference of the two sides) is a sum of nonnegative
terms `c_k (β-1/2)^k (3/4-β)^(23-k)`. -/
lemma boxWindow_regionB_mid_cert {β : ℝ} :
    4*β^2*boxDEN β*(1/30 - (3/4-β)*(668528197/10^10))
      - (4*β^2*boxNUM β + boxDEN β*(1-16*β^2))*(β-1/2)^2
    = 762277440080314368/625*(3/4-β)^23
      + 87810296488446394368/3125*(β-1/2)*(3/4-β)^22
      + 4818960207975015776256/15625*(β-1/2)^2*(3/4-β)^21
      + 167815102427408219111424/78125*(β-1/2)^3*(3/4-β)^20
      + 4164266559999586002386944/390625*(β-1/2)^4*(3/4-β)^19
      + 78346588810547633856667648/1953125*(β-1/2)^5*(3/4-β)^18
      + 1160556614833926663263404032/9765625*(β-1/2)^6*(3/4-β)^17
      + 8323253645342307603071676416/29296875*(β-1/2)^7*(3/4-β)^16
      + 5440846504595930851481924736/9765625*(β-1/2)^8*(3/4-β)^15
      + 26550956606115635613596880064/29296875*(β-1/2)^9*(3/4-β)^14
      + 36080371962332158826400377216/29296875*(β-1/2)^10*(3/4-β)^13
      + 13708710100257812771039629408/9765625*(β-1/2)^11*(3/4-β)^12
      + 39375970608341924856287278664/29296875*(β-1/2)^12*(3/4-β)^11
      + 31633841734946738405044771732/29296875*(β-1/2)^13*(3/4-β)^10
      + 21248508010574898657930487876/29296875*(β-1/2)^14*(3/4-β)^9
      + 3952498803322072902170199748/9765625*(β-1/2)^15*(3/4-β)^8
      + 2177551043553218767555286281/11718750*(β-1/2)^16*(3/4-β)^7
      + 324372104217206039855340821/4687500*(β-1/2)^17*(3/4-β)^6
      + 960125963929582356575363/46875*(β-1/2)^18*(3/4-β)^5
      + 350853252125386238951717/75000*(β-1/2)^19*(3/4-β)^4
      + 236428708631075469341243/300000*(β-1/2)^20*(3/4-β)^3
      + 10918755446469455578667/120000*(β-1/2)^21*(3/4-β)^2
      + 50241148340000551947/8000*(β-1/2)^22*(3/4-β)
      + 186050210693776*(β-1/2)^23 := by
  simp only [boxNUM, boxDEN]
  ring

theorem boxWindow_regionB_mid {β : ℝ} (h0 : (1:ℝ)/2 ≤ β) (h1 : β ≤ 3/4) :
    max 0 (boxC1 β + 1/(4*β^2) - 4)*(β-1/2)^2 + (3/4-β)*(668528197/10^10) ≤ 1/30 := by
  have hβ0 : (0:ℝ) < β := by linarith
  have hβ2 : β < 2 := by linarith
  have hu : (0:ℝ) ≤ β - 1/2 := by linarith
  have hv : (0:ℝ) ≤ 3/4 - β := by linarith
  have hDEN : (0:ℝ) < boxDEN β := boxDEN_pos β hβ2
  have hid : boxC1 β = boxNUM β / boxDEN β := by
    rw [eq_div_iff hDEN.ne']
    exact boxC1_mul_den β (by linarith)
  have hpos : (0:ℝ) < 4*β^2*boxDEN β := by positivity
  -- certificate: the difference is ≥ 0
  have hnn : 0 ≤ 4*β^2*boxDEN β*(1/30 - (3/4-β)*(668528197/10^10))
      - (4*β^2*boxNUM β + boxDEN β*(1-16*β^2))*(β-1/2)^2 := by
    rw [boxWindow_regionB_mid_cert]
    positivity
  -- rewrite `boxC1` with the common denominator
  have hf : boxC1 β + 1/(4*β^2) - 4
      = (4*β^2*boxNUM β + boxDEN β*(1-16*β^2))/(4*β^2*boxDEN β) := by
    rw [hid, eq_div_iff hpos.ne']
    field_simp
    ring
  have hmain : (boxC1 β + 1/(4*β^2) - 4)*(β-1/2)^2
      ≤ 1/30 - (3/4-β)*(668528197/10^10) := by
    rw [hf, div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith [hnn]
  have hRHS : 0 ≤ 1/30 - (3/4-β)*(668528197/10^10) := by
    have hm : (0:ℝ) ≤ 668528197/10^10 := by norm_num
    have hle : 3/4 - β ≤ 1/4 := by linarith
    have hstep : (3/4-β)*(668528197/10^10) ≤ (1/4)*(668528197/10^10) :=
      mul_le_mul_of_nonneg_right hle hm
    have hfin : (1/4)*(668528197/10^10) ≤ (1/30:ℝ) := by norm_num
    linarith
  have hmaxeq : max 0 (boxC1 β + 1/(4*β^2) - 4)*(β-1/2)^2
      = max 0 ((boxC1 β + 1/(4*β^2) - 4)*(β-1/2)^2) := by
    rw [max_mul_of_nonneg _ _ (by positivity : (0:ℝ) ≤ (β-1/2)^2)]
    simp
  calc max 0 (boxC1 β + 1/(4*β^2) - 4)*(β-1/2)^2 + (3/4-β)*(668528197/10^10)
      = max 0 ((boxC1 β + 1/(4*β^2) - 4)*(β-1/2)^2) + (3/4-β)*(668528197/10^10) := by
        rw [hmaxeq]
    _ ≤ (1/30 - (3/4-β)*(668528197/10^10)) + (3/4-β)*(668528197/10^10) := by
        linarith [max_le hRHS hmain]
    _ = 1/30 := by ring

end Commons.Analysis.Integral
