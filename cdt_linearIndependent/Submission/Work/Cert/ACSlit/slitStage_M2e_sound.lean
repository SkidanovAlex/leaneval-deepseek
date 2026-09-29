import Mathlib
import Submission.Work.Cert.ACSlit.M2eSpec
import Submission.Work.Cert.ACSlit.Shadow
import Submission.Work.ANum3.slit_crude_bound
import Submission.Work.APsi.defs
import Submission.Work.Cert.ACSlit.slit_deriv2_explicit_le
import Submission.Work.Cert.ACSlit.slitM2e_rounding

namespace Work.Cert.ACSlit
open Work.Cert

/-- The explicit branch of the second-derivative bound of `Work.Cert.slitStage`: when `suseE` holds and
`sdd > 0`, `sM2e = ⌈snum/sdd⌉` bounds `S·sup_D‖slit''‖` on the input disc.

Route: from `hokM` get `0 ≤ cU`, `cr²+ci² ≤ cU²`, `0 ≤ qU`, `|Q-centre| ≤ qU`, `0 ≤ qL`,
`qL ≤ |Q-centre|`, `0 ≤ qpU`, `|Qp-centre| ≤ qpU`, `0 ≤ m1U`, `(cr−S)²+ci² ≤ m1U²`; with `hQ`/`hQp`
(`BallMem`, from `ACSlit.ballMem_sQ_Qp`) these give `‖c‖ ≤ cU/S`, `‖Q(c)‖ ≤ (qU + sQ.r)/S`,
`‖Q(c)‖ ≥ (qL − sQ.r)/S`, `‖Q'(c)‖ ≤ (qpU + sQp.r)/S`, `‖c−1‖ ≤ m1U/S`; from `hokB`
(`binvOK (sC st) w.cL`) get `0 < cL ≤ S‖c‖`. With `hrho` and `hwhi` (`cU + ρ + 1 < S`),
`huse` (`0 < sQlo`, `0 < swlo`) and `hokW` (`0 < sL`, `sL² ≤ sQlo·S`, `0 ≤ sH`, `sQhi·S ≤ sH²`)
the side conditions of `Work.ANum3.slit_crude_bound` (instantiated at `c := cIn st`, `w := u`,
`ρ := st.rho/S`, `Ab := (1+r)²`, `Bh := |2(1−6r+r²)|`, `Eh := 2(r−1)²`, `Cb := 1+r`,
`W := swhi/S`, `wm1 := swm1/S`, `Wlo := swlo/S`, `Qp := sQpD/S`, `Qhi := sQhi/S`, `Slo := sL/S`,
`Shi := sH/S`) all hold, giving `‖slit'' u‖ ≤ numR/(8 r Wlo³)`. Finally `numR·S ≤ snum`
(termwise `mu_ge`/`dvu_ge`, using `E/S = 2(r−1)²`, `A/S = (1+r)²`, `C1/S = 1+r`, `A2/S = 2(1+r)²`,
`G8/S = 8r`) and `sdd ≤ S³·8 r Wlo³` (`md_le` twice), so
`numR/(8r Wlo³) ≤ (snum/S)/(sdd/S) ≤ (dvu snum sdd)/S`.
The style of the rounding comparison is in `Submission/Work/Cert/ACBall/scratch_M2.lean`
(`lM2e_rounding`, the lune analogue — scratch, do not import it, but the `mu_ge`/`dvu_ge`/`md_le`
pattern there is the model). Namespace: `Work.Cert.ACSlit`. -/
theorem slitStage_M2e_sound (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hA : (A : ℝ) = (Work.Cert.S : ℝ) * (1 + r) ^ 2)
    (hB2 : (B2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 - 6 * r + r ^ 2)))
    (hE : (E : ℝ) = (Work.Cert.S : ℝ) * (2 * (r - 1) ^ 2))
    (hC1 : (C1 : ℝ) = (Work.Cert.S : ℝ) * (1 + r))
    (hG8 : (G8 : ℝ) = (Work.Cert.S : ℝ) * (8 * r))
    (hA2 : (A2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 + r) ^ 2))
    (hokB : Work.Cert.ACSlit.sokB A B2 E C1 G8 A2 ror roi st w = true)
    (hokM : Work.Cert.ACSlit.sokM A B2 E C1 G8 A2 ror roi st w = true)
    (hokW : Work.Cert.ACSlit.sokW A B2 E C1 G8 A2 ror roi st w = true)
    (hwhi : Work.Cert.ACSlit.swhi A B2 E C1 G8 A2 ror roi st w < Work.Cert.S)
    (hrho : 0 ≤ st.rho)
    (huse : Work.Cert.ACSlit.suseE A B2 E C1 G8 A2 ror roi st w = true)
    (hdd : 0 < Work.Cert.ACSlit.sdd A B2 E C1 G8 A2 ror roi st w)
    (hQ : Work.Cert.ACBall.BallMem (Work.Cert.ACSlit.sQ A B2 E C1 G8 A2 ror roi st w)
        (Work.APsi.slitQ r (Work.Cert.ACSlit.cIn st)))
    (hQp : Work.Cert.ACBall.BallMem (Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w)
        (2 * (1 + (r : ℂ)) ^ 2 * Work.Cert.ACSlit.cIn st
          - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)))
    {u : ℂ} (hu : ‖u - Work.Cert.ACSlit.cIn st‖ ≤ (st.rho : ℝ) / (Work.Cert.S : ℝ)) :
    ‖deriv (deriv (Submission.CDTPlan.slit r)) u‖
      ≤ ((Work.Cert.ACSlit.sM2e A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
  -- ## read off the flags
  obtain ⟨_, _, hcU0, _, hqU0, _, _, _, hqpU0, _, hm1U0, _⟩ :=
    sokM_spec A B2 E C1 G8 A2 ror roi st w hokM
  obtain ⟨_, hsQr, _, _, _, _, _, _, _, _⟩ :=
    sokB_spec A B2 E C1 G8 A2 ror roi st w hokB
  obtain ⟨hsL, _, hsH, _⟩ := sokW_spec A B2 E C1 G8 A2 ror roi st w hokW huse
  obtain ⟨_, hwlo⟩ := suseE_spec A B2 E C1 G8 A2 ror roi st w huse
  have hQpr : 0 ≤ (sQp A B2 E C1 G8 A2 ror roi st w).r :=
    sQp_r_nonneg A B2 E C1 G8 A2 ror roi st w
  -- ## the two branches
  have h1 := slit_deriv2_explicit_le A B2 E C1 G8 A2 ror roi st w hr0 hr1 hA hB2 hE hC1 hG8 hA2
    hokB hokM hokW hwhi hrho huse hQ hQp hu
  have h2 := slitM2e_rounding A B2 E C1 G8 A2 ror roi st w hr0 hr1 hA hE hC1 hG8 hA2
    hrho hcU0 hm1U0 hqU0 hsQr hqpU0 hQpr hsL hsH hwlo hdd
  -- ## `sM2e` is the explicit quotient on this branch
  have hcond : (suseE A B2 E C1 G8 A2 ror roi st w
      && decide (0 < sdd A B2 E C1 G8 A2 ror roi st w)) = true := by
    rw [Bool.and_eq_true]
    exact ⟨huse, by simpa using hdd⟩
  have hsM2e : sM2e A B2 E C1 G8 A2 ror roi st w
      = dvu (snum A B2 E C1 G8 A2 ror roi st w) (sdd A B2 E C1 G8 A2 ror roi st w) := by
    simp only [sM2e, hcond, if_true]
  rw [hsM2e]
  exact h1.trans h2

end Work.Cert.ACSlit
