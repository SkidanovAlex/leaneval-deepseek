/-
# Theorem `bile` for every `r` in the paper's range (Krause--Mirek--Tao, §10)

`Work.KMTPlan.A6.MdlBileOfR1` proves the paper's Theorem `bile` — in the finite cyclic model
`ℤ/Qℤ`, with a constant uniform in `Q` — for every `2 ≤ r < 2d/(d-1)`, *given* the concentration
endpoint (avg-1)

  `BilinearAverageLqUniformImprov P hd hI : ∀ q ∈ [1, 2d/(d-1)), ∃ C > 0, ∀ Q f g,
     ‖A_{ℤ/Qℤ}(f,g)‖_{L^q} ≤ C ‖f‖_{L²} ‖g‖_{L²}`

as an explicit argument.  That endpoint is now proved (`BilinearAverageLqUniformImprov.lean`), so
this module discharges the argument and obtains the unconditional form: for every `2 ≤ r < 2d/(d-1)`
there is a gain rate `c(r) > 0` such that the arithmetic bilinear average of a minor-arc function
against an arbitrary one gains `2^{-c(r)·l}`, uniformly in the modulus `Q` and the height `l`.

This is the arithmetic input of the `(2,2,1)` case of the model estimate `model-est-2`: the slice
estimate `Work.KMTPlan.A6.MdlSliceCoreGain` uses it at an exponent `r ∈ (2, 2d/(d-1))` (monotonicity
of `V^r` lets one work in that range for any prescribed `r > 2`).

The chain is: `MdlBileR1OfImprov` (the `r = 1` gain, from `ImprovKMT` by the paper's lifting
argument) + `BilinearAverageLqUniformImprov` (the `L^q` endpoint, uniform in `Q`; its uniformity is
the paper's (avg-2) `‖A_{ℤ_p}‖ ≤ 1` for `p` large, which itself comes from `bile-2`) +
`LpNormZMod_logconvex` (log-convexity of the `L^p` norms on `ℤ/Qℤ`), assembled by
`MdlBileOfR1` (and `bile_of_r1`, `bileInterpIw`, `exists_interp_theta`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlBileOfR1
import Submission.Work.KMTPlan.A6.BilinearAverageLqUniformImprov

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

noncomputable section

open Work.Analysis.Concentration (LpNormZMod polyBilinearAverageZMod)

/-- **Theorem `bile`, unconditional form.**  For every `2 ≤ r < 2d/(d-1)` (`d = P.natDegree`) and
every `ρ ∈ (0,1]` there are `c > 0` and `C > 0` with

  `‖A_{ℤ/Qℤ}(f,g)‖_{L^r} ≤ C · 2^{-c·l} · ‖f‖_{L²} ‖g‖_{L²}`

whenever `f` or `g` is minor arc at height `l` — uniformly in the modulus `Q` and the height `l`. -/
theorem MdlBileOfR1Improv (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hI : Work.KMTContract.ImprovKMT P) (r : ℝ) (hr : 2 ≤ r)
    (hrd : r < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℕ) [NeZero Q] (l : ℕ) (f g : ZMod Q → ℂ),
        (MdlIwMinorArc ρ l Q f ∨ MdlIwMinorArc ρ l Q g) →
        LpNormZMod Q r (polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ C * (2 : ℝ) ^ (-(c * (l : ℝ))) * LpNormZMod Q 2 f * LpNormZMod Q 2 g :=
  MdlBileOfR1 P hd (BilinearAverageLqUniformImprov P hd hI) hI r hr hrd

end

end Work.KMTPlan.A6
