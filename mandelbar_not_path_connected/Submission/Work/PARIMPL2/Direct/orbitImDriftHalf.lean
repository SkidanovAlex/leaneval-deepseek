import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.modelDisp_re_ge
import Submission.Work.PARIMPL2.Direct.modelDisp_re_le_signed
import Submission.Work.PARIMPL2.Direct.disp_im_split
import Submission.Work.PARIMPL2.Direct.sum_zeta_sq_24
import Submission.Work.PARIMPL2.Direct.sum_lam2_div_D_le
import Submission.Work.PARIMPL2.Direct.sum_re_ecalPt_24
import Submission.Work.PARIMPL2.Direct.sum_re_ecalPt_30
import Submission.Work.PARIMPL2.Direct.drift_eta_le
import Submission.Work.PARIMPL2.Direct.orbitImDriftHalf_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

namespace Work.PARIMPL2.Direct

open Complex

theorem orbitImDriftHalf (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hrr : 16 ≤ R * r)
    (hτpi : (Real.pi / lam) * ‖τ - 1‖ ≤ 1 / (8 * R))
    (n : ℕ) (u : ℕ → ℂ)
    (hu : ∀ j < n, u (j + 1) = u j + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j))
    (htop : Real.pi / lam - 2 * R ≤ (u 0).re)
    (hxn : (u n).re ≤ R / 4 + 4)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3)
    (hzn : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ≤ 4 / R)
    (hzr : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ < r)
    (hy0 : |(u 0).im| ≤ R / 4 + 4 + Real.log R) :
    |(u n).im| ≤ Real.exp (40 * max h1.re 0 / R) *
      (|(u 0).im| + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) + 20 * A / R + 32) := by
  have hstepL : ∀ j ≤ n, -1 - 35 * lam ^ 2
      - (B + 2) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖
      - (A + 35) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
      ≤ (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).re :=
    fun j hj => modelDisp_re_ge lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr hτpi hrr
      (u j) (hzn j hj) (hzr j hj)
  have hstepS : ∀ j ≤ n, (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).re
      ≤ -1 + 35 * lam ^ 2 + (B + 8) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖
        - (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
        + 35 * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2 :=
    fun j hj => modelDisp_re_le_signed lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hτpi hrr
      (u j) (hzn j hj) (hzr j hj)
  have hsplit : ∀ j < n,
      |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).im + τ.im
        + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
        + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im
        + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im|
      ≤ 100 * lam ^ 2
        + (9 / 4) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 3
        + (33 / 10) * ‖h1‖ * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
        + (11 / 5) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
        + (3 / R) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2 :=
    fun j hj => disp_im_split lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr hrr
      (u j) (hzn j (le_of_lt hj)) (hzr j (le_of_lt hj))
  have hS : ∑ j ∈ Finset.range n,
      ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2 ≤ 24 / R :=
    sum_zeta_sq_24 lam R hlam hR hlamR n u hx1 hx2 hdec
  have hG : ∑ j ∈ Finset.range n,
      lam ^ 2 / (Real.sin (lam * (u j).re) ^ 2 + Real.sinh (lam * (u j).im) ^ 2) ≤ 24 / R :=
    sum_lam2_div_D_le lam R hlam hR hlamR n u hx1 hx2 hdec
  have hRre : |∑ j ∈ Finset.range n,
      (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re| ≤ 8 * (1 + Real.log R) :=
    sum_re_ecalPt_24 lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr hrr hτpi n u hu
      htop hxn hx1 hx2 hdec hzn hzr hy0 (fun j hj => ⟨hstepS j hj, hstepL j hj⟩) hS
  have hRre30 : |∑ j ∈ Finset.range n,
      (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re| ≤ 30 :=
    sum_re_ecalPt_30 lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr hrr hτpi n u hu
      htop hxn hx1 hx2 hdec hzn hzr hy0 (fun j hj => ⟨hstepS j hj, hstepL j hj⟩) hS
  have hEta : ∑ j ∈ Finset.range n,
      |(h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
          - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im| ≤ 20 * A / R + 8 :=
    drift_eta_le lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr hrr hτpi n u hu
      hx1 hx2 hdec hzn hzr hstepS
  exact orbitImDriftHalf_aux lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr hrr hτpi
    n u hu hx1 hx2 hdec hzn hsplit hS hG hy0 hRre hRre30 hEta

end Work.PARIMPL2.Direct
