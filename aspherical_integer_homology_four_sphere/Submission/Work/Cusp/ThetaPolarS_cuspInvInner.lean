import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.bndOfU_mem
import Submission.Work.Cusp.bndOfU_u
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.u_smul
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.wOf_invY
import Submission.Work.Cusp.radial_collar
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Cusp.slope_ne_zero
import Submission.Work.Cusp.ThetaPolarS_continuousOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open scoped Real InnerProductSpace

/-- `u (bndOfU t) = Int.fract t`. -/
lemma u_bndOfU (t : ℝ) : u (bndOfU t) = Int.fract t := by
  rw [u, show bnd (bndOfU t) = bndOfU t by rw [bnd, nrm_bndOfU t, inv_one, one_smul]]
  exact uPerim_bndOfU t

/-- `nrm (t • bndOfU x) = t` for `t ≥ 0`. -/
lemma nrm_smul_bndOfU {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : nrm (t • bndOfU x) = t := by
  rw [nrm_smul, nrm_bndOfU, mul_one, abs_of_nonneg ht]

/-- `u (t • bndOfU x) = Int.fract x` for `t > 0`. -/
lemma u_smul_bndOfU {t : ℝ} (ht : 0 < t) (x : ℝ) : u (t • bndOfU x) = Int.fract x := by
  rw [u_smul ht, u_bndOfU]

/-- `cuspInvInner`'s own perimeter coordinate is `uqOf v q`. -/
lemma cuspInvInner_uu (v : Fin 5) (q : E4) :
    (q 1 - 2 * π * (⟪cuspY v (invY v !₂[q 2, q 3]), slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π)
      = uqOf v q := by
  rw [uqOf]; ring

theorem ThetaPolarS_cuspInvInner (v : Fin 5) (c : ℝ) (q : E4) (hq : q ∈ polarBox)
    (hu : uqOf v q - c ∈ Set.Ico 0 1) :
    ThetaPolarS v c (cuspInvInner v q).1 (cuspInvInner v q).2 = q := by
  obtain ⟨hq0lo, hq0hi⟩ := hq
  have hq0pos : 0 < q 0 := by linarith
  simp only [cuspInvInner]
  set y : E2 := invY v !₂[q 2, q 3] with hy
  set uu : ℝ := (q 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π) with huu
  set b : ℝ := beta (cuspX v uu y) with hb
  set t : ℝ := (if q 0 ≤ rJ then q 0 / (2 * rJ)
      else 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ))) with ht
  -- basic facts about the abbreviations
  have hR0v : R0 = 7 / 2 := rfl
  have hlogsJ : Real.log sJ = 1 / 2 := by rw [sJ, Real.log_exp]
  have hminsq : (0 : ℝ) < betaMin := by rw [betaMin]; exact Real.sqrt_pos_of_pos (by norm_num)
  have hbmin : betaMin ≤ b := by rw [hb]; exact beta_min_le _
  have hbmax : b ≤ betaMax := by rw [hb]; exact beta_le_max _
  have hbpos : 0 < b := lt_of_lt_of_le hminsq hbmin
  have hblt : b < sJ := lt_of_le_of_lt hbmax betaMax_lt_sJ
  have hlogb_lt : Real.log b < Real.log sJ := Real.log_lt_log hbpos hblt
  have hDneg : Real.log b - Real.log sJ < 0 := by linarith
  have hDne : Real.log b - Real.log sJ ≠ 0 := ne_of_lt hDneg
  have h2Dne : 2 * (Real.log b - Real.log sJ) ≠ 0 := mul_ne_zero two_ne_zero hDne
  have huq : uqOf v q = uu := by rw [huu, hy]; exact (cuspInvInner_uu v q).symm
  have hu'mem : uu - c ∈ Set.Ico 0 1 := by rw [← huq]; exact hu
  have hu0 : 0 ≤ uu - c := (Set.mem_Ico.mp hu'mem).1
  have hu1 : uu - c < 1 := (Set.mem_Ico.mp hu'mem).2
  -- the key scalar identity behind the collar height
  have hkey : ∀ s : ℝ, 1 + (R0 - s - Real.log b) / (2 * (Real.log b - Real.log sJ)) - 1/2
      = (R0 - s - Real.log sJ) / (2 * (Real.log b - Real.log sJ)) := by
    intro s
    field_simp
    ring
  -- positivity of `t`
  have ht_pos : 0 < t := by
    by_cases hc0 : q 0 ≤ rJ
    · rw [ht, if_pos hc0]
      exact div_pos hq0pos (by norm_num [rJ])
    · have hq0gt3 : 3 < q 0 := by
        have h := not_le.mp hc0
        rw [rJ] at h; linarith
      have htB : t = 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ)) := by
        rw [ht, if_neg hc0]
      have hnum : R0 - q 0 - Real.log sJ < 0 := by rw [hR0v, hlogsJ]; linarith
      have hpos : 0 < 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ)) - 1/2 := by
        rw [hkey (q 0)]; exact div_pos_of_neg_of_neg hnum (by linarith)
      rw [htB]; linarith
  have hnrm_eq : nrm (t • bndOfU uu) = t := nrm_smul_bndOfU (le_of_lt ht_pos) uu
  -- the angle coordinate
  have hUS : uS c (t • bndOfU uu) = uu := by
    have hup : u (t • bndOfU uu) = Int.fract uu := u_smul_bndOfU ht_pos uu
    rw [uS, hup]
    have hfr : Int.fract (Int.fract uu - c) = Int.fract (uu - c) := by
      have hthis : uu - c = (Int.fract uu - c) + ⌊uu⌋ := by
        have hf : (⌊uu⌋ : ℝ) + Int.fract uu = uu := Int.floor_add_fract uu
        linarith
      rw [hthis, Int.fract_add_intCast]
    rw [hfr, Int.fract_eq_self.mpr ⟨hu0, hu1⟩]
    ring
  have hangle : 2 * π * uS c (t • bndOfU uu) + 2 * π * inner ℝ (cuspY v y) (slope v)
      / ‖slope v‖ ^ 2 = q 1 := by
    rw [hUS, huu]
    have hs : ‖slope v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (slope_ne_zero v))
    field_simp
    ring
  -- the `w` coordinates
  have hw : wOf v y = !₂[q 2, q 3] := by rw [hy]; exact wOf_invY v !₂[q 2, q 3]
  -- the radial coordinate
  have hrad : radial v (t • bndOfU uu) y = q 0 := by
    by_cases hc0 : q 0 ≤ rJ
    · have htA : t = q 0 / (2 * rJ) := by rw [ht, if_pos hc0]
      have htle : t ≤ 1/2 := by
        rw [htA, div_le_iff₀ (by norm_num [rJ] : (0:ℝ) < 2 * rJ)]
        rw [show (1/2) * (2 * rJ) = rJ by ring]
        exact hc0
      have hnrmle : nrm (t • bndOfU uu) ≤ 1/2 := by rw [hnrm_eq]; exact htle
      rw [radial_eq_inner v _ _ hnrmle, hnrm_eq, htA]
      simp only [rJ]; ring
    · have htB : t = 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ)) := by
        rw [ht, if_neg hc0]
      have hq0gt3 : 3 < q 0 := by
        have h := not_le.mp hc0
        rw [rJ] at h; linarith
      have hnum : R0 - q 0 - Real.log sJ < 0 := by rw [hR0v, hlogsJ]; linarith
      have hgt : 1/2 < t := by
        have hpos : 0 < 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ)) - 1/2 := by
          rw [hkey (q 0)]; exact div_pos_of_neg_of_neg hnum (by linarith)
        rw [htB]; linarith
      have hnrmgt : 1/2 < nrm (t • bndOfU uu) := by rw [hnrm_eq]; exact hgt
      have hb_eq : beta (cuspX v (u (t • bndOfU uu)) y) = b := by
        have h := beta_cuspX_eq v c (t • bndOfU uu) y
        rw [hUS] at h
        rw [h, hb]
        rfl
      have hcollar : collarHeight t b = Real.exp (R0 - q 0) := by
        rw [collarHeight, htB, Real.exp_eq_exp]
        field_simp
        ring
      rw [radial_collar v (t • bndOfU uu) y (le_of_lt hnrmgt), collarS, hnrm_eq, hb_eq, hcollar,
        Real.log_exp]
      ring
  ext i
  fin_cases i
  · exact hrad
  · exact hangle
  · show wOf v y 0 = q 2
    rw [hw]; simp
  · show wOf v y 1 = q 3
    rw [hw]; simp

end Work.Cusp
