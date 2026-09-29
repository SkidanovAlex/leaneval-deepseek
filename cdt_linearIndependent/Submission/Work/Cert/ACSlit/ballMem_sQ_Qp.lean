import Mathlib
import Submission.Work.Cert.ACSlit.Shadow
import Submission.Work.Cert.ball_ops
import Submission.Work.APsi.defs

namespace Work.Cert.ACSlit

open Work.Cert Work.Cert.ACBall

/-- `bK k` contains the real number `v` whenever `(k:ℝ) = S·v`. -/
lemma ballMem_bK_of {k : ℤ} {v : ℝ} (h : (k : ℝ) = (Work.Cert.S : ℝ) * v) :
    BallMem (bK k) (v : ℂ) := by
  have h1 := ballMem_bK k
  have hv : (k : ℝ) / (Work.Cert.S : ℝ) = v := by
    rw [h, mul_div_cancel_left₀ v (ne_of_gt Work.Cert.ACBall.S_posR)]
  rwa [hv] at h1

/-- `bK k` contains the complex number `w` whenever `(k:ℝ) = S·v` and `w = (v:ℂ)`. -/
lemma ballMem_bK_of_complex {k : ℤ} {v : ℝ} {w : ℂ}
    (h : (k : ℝ) = (Work.Cert.S : ℝ) * v) (hw : (v : ℂ) = w) : BallMem (bK k) w := by
  rw [← hw]; exact ballMem_bK_of h

/-- Ball semantics of the two quadratic pieces of `Work.Cert.slitStage`: `sQ` contains `slitQ r c` and
`sQp` contains `Q'(c) = 2(1+r)²c − 2(1−6r+r²)`, where `c = cIn st`. Pure ball arithmetic
(`ballMem_badd`/`ballMem_bsub` from `Work.Cert.ACBall.Basic` and `bmul_sound` from
`Work.Cert.ball_ops`) plus `ring`. Namespace of this declaration: `Work.Cert.ACSlit`. -/
theorem ballMem_sQ_Qp (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW) {r : ℝ}
    (hA : (A : ℝ) = (Work.Cert.S : ℝ) * (1 + r) ^ 2)
    (hB2 : (B2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 - 6 * r + r ^ 2)))
    (hA2 : (A2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 + r) ^ 2)) :
    Work.Cert.ACBall.BallMem (Work.Cert.ACSlit.sQ A B2 E C1 G8 A2 ror roi st w)
        (Work.APsi.slitQ r (Work.Cert.ACSlit.cIn st)) ∧
      Work.Cert.ACBall.BallMem (Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w)
        (2 * (1 + (r : ℂ)) ^ 2 * Work.Cert.ACSlit.cIn st
          - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) := by
  have hc : BallMem (sC A B2 E C1 G8 A2 ror roi st w) (cIn st) := by
    simp [BallMem, sC, cIn]
  have hAc : BallMem (bK A) ((1 + (r : ℂ)) ^ 2) :=
    ballMem_bK_of_complex hA (by push_cast; ring)
  have hB2c : BallMem (bK B2) (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) :=
    ballMem_bK_of_complex hB2 (by push_cast; ring)
  have hA2c : BallMem (bK A2) (2 * (1 + (r : ℂ)) ^ 2) :=
    ballMem_bK_of_complex hA2 (by push_cast; ring)
  have hc2 : BallMem (sc2 A B2 E C1 G8 A2 ror roi st w) (cIn st * cIn st) :=
    bmul_sound hc hc
  refine ⟨?_, ?_⟩
  · have h1 : BallMem (bmul (bK A) (sc2 A B2 E C1 G8 A2 ror roi st w))
        ((1 + (r : ℂ)) ^ 2 * (cIn st * cIn st)) := bmul_sound hAc hc2
    have h2 : BallMem (bmul (bK B2) (sC A B2 E C1 G8 A2 ror roi st w))
        ((2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) * cIn st) := bmul_sound hB2c hc
    have h3 : BallMem (bsub (bmul (bK A) (sc2 A B2 E C1 G8 A2 ror roi st w))
          (bmul (bK B2) (sC A B2 E C1 G8 A2 ror roi st w)))
        ((1 + (r : ℂ)) ^ 2 * (cIn st * cIn st)
          - (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) * cIn st) := ballMem_bsub h1 h2
    have h4 : BallMem (badd (bsub (bmul (bK A) (sc2 A B2 E C1 G8 A2 ror roi st w))
            (bmul (bK B2) (sC A B2 E C1 G8 A2 ror roi st w))) (bK A))
        ((1 + (r : ℂ)) ^ 2 * (cIn st * cIn st)
          - (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) * cIn st + (1 + (r : ℂ)) ^ 2) :=
      ballMem_badd h3 hAc
    have key : Work.APsi.slitQ r (cIn st)
        = ((1 + (r : ℂ)) ^ 2 * (cIn st * cIn st)
          - (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) * cIn st + (1 + (r : ℂ)) ^ 2) := by
      simp only [Work.APsi.slitQ]; ring
    rw [key]
    exact h4
  · have h5 : BallMem (bmul (bK A2) (sC A B2 E C1 G8 A2 ror roi st w))
        ((2 * (1 + (r : ℂ)) ^ 2) * cIn st) := bmul_sound hA2c hc
    have h6 : BallMem (bsub (bmul (bK A2) (sC A B2 E C1 G8 A2 ror roi st w)) (bK B2))
        ((2 * (1 + (r : ℂ)) ^ 2) * cIn st
          - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) := ballMem_bsub h5 hB2c
    exact h6

end Work.Cert.ACSlit
