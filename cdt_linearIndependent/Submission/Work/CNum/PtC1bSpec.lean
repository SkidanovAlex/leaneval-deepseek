import Mathlib
import Submission.Work.CNum.PtC1bAux
import Submission.Work.CNum.PsiCWfun
import Submission.Work.CNum.WfunArc4
import Submission.Work.CNum.ratIvMem
import Submission.Work.CNum.Fx
import Submission.Work.CNum.CpxSound
import Submission.Work.CNum.ExpISpec
import Submission.Work.CNum.MemIvS
import Submission.Work.CNum.Q1bMem
import Submission.Work.CNum.P1bMem
import Submission.Work.CNum.Arc4Angle

/-!
# `Work.CNum.PtC1bSpec` — soundness of the fourth-arc point table `ptC1b`

`ptC1b k = (3/4)·W1 k (-1)` is the mantissa-level interval enclosure of the boundary value
`ψ_C(e^{iθ_k})`, `θ_k = 2πk/1024`, on the *fourth* arc `(2π - α, 2π)` of the unit circle
(`780 ≤ k ≤ 1024`).  This is the arc where the principal square root of `e^{iθ}` is `-e^{iθ/2}`,
so the sign of `P = √(2A(cos θ - γ))` is flipped (`W1 k (-1)`).

The proof is the composition of four independent ingredients:

* `PsiCWfun` : `ψ_C = (3/4)·Wfun` (the lune map at `c = 23/10` is `-Wfun`);
* `WfunArc4` : on the fourth arc (`θ - 2π ∈ (-α,α)`), whose hypothesis is supplied by
  `Arc4Angle`, the principal branch gives
  `Wfun (e^{iθ}) = ((P(θ) - iQ(θ))·e^{iθ/2})/d`;
* `P1bMem`, `Q1bMem` : the named intervals of `PtC1bAux` enclose `P(θ_k)`, `Q(θ_k)`, and
  `ExpISpec` gives `expI k ∋ e^{iθ_k/2}`;
* `IvMSpec`/`CpxSound.mem_mulr`/`mem_mul`/`mem_neg` transport these through the interval
  expression `W1b k`, with the rational memberships `ratIvMem`.

The only "numerics" are inside the sub-lemmas: `P1bMem` uses the finite side conditions
`X1b_lo_nonneg`/`X1b_hi_lt` of `PtC1bAux` (kernel `decide` over the 245 arc values).
-/

namespace Work.CNum

open Work.ANum

theorem PtC1bSpec {k : ℕ} (h1 : 780 ≤ k) (h2 : k ≤ 1024) : Work.CNum.Cpx.Mem (Work.CNum.ptC1b k) (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024)))) := by
  set θ : ℝ := (k : ℝ) * Real.pi / 512 with hθ
  have harg : (2 * (Real.pi : ℂ) * (k : ℂ) / 1024) = (θ : ℂ) := by
    rw [hθ]; push_cast; ring
  rw [harg, ptC1b_eq k, PsiCWfun]
  have hArc : θ - 2 * Real.pi ∈ Set.Ioo (-alpR) alpR := by
    rw [hθ]; exact Arc4Angle h1 h2
  have hPt : (P1b k).Mem (PR θ) := by rw [hθ]; exact P1bMem h1 h2
  have hQt : (Q1b k).Mem (QR θ) := by rw [hθ]; exact Q1bMem h2
  have hEt : (expI k).Mem (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) := by
    have h := ExpISpec h2
    have hc : ((k : ℂ) * (Real.pi : ℂ) / 1024) = ((θ / 2 : ℝ) : ℂ) := by
      rw [hθ]; push_cast; ring
    rwa [hc] at h
  have hW : (W1b k).Mem (Wfun (Complex.exp (Complex.I * (θ : ℂ)))) := by
    have hz : (⟨Iv.neg (P1b k), Q1b k⟩ : Cpx).Mem
        (((-(PR θ) : ℝ) : ℂ) + (((QR θ) : ℝ) : ℂ) * Complex.I) := by
      refine ⟨?_, ?_⟩
      · simpa using Iv.mem_neg hPt
      · simpa using hQt
    have hr : (ratIv 50 429).Mem ((50 : ℝ) / 429) := by
      simpa using ratIvMem 50 (q := 429) (by norm_num)
    have hstep1 := Work.CNum.mem_mulr hz hr
    have hstep2 := Work.CNum.mem_mul hstep1 hEt
    have hstep3 := Work.CNum.mem_neg hstep2
    have hval : -(((((-(PR θ) : ℝ) : ℂ) + (((QR θ) : ℝ) : ℂ) * Complex.I) *
          (((50 : ℝ) / 429 : ℝ) : ℂ)) * Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)))
        = Wfun (Complex.exp (Complex.I * (θ : ℂ))) := by
      rw [WfunArc4 hArc]
      have hdr : dR = (429 : ℝ) / 50 := by norm_num [dR, cR]
      have hs : (((50 : ℝ) / 429 : ℝ) : ℂ) = ((dR : ℂ))⁻¹ := by
        rw [hdr, ← Complex.ofReal_inv]
        norm_num
      rw [hs]
      push_cast
      ring
    rwa [hval] at hstep3
  have h34 : (ratIv 3 4).Mem ((3 / 4 : ℝ)) := by
    simpa using ratIvMem 3 (q := 4) (by norm_num)
  have hfin := Work.CNum.mem_mulr hW h34
  have hv : Wfun (Complex.exp (Complex.I * (θ : ℂ))) * (((3 / 4 : ℝ)) : ℂ)
      = (3 / 4 : ℂ) * Wfun (Complex.exp (Complex.I * (θ : ℂ))) := by
    push_cast; ring
  rw [hv] at hfin
  exact hfin

end Work.CNum
