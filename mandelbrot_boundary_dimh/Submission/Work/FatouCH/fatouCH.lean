import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.FX8.Assembly
import Submission.Work.FatouCH.fatouDerivEstimate
import Submission.Work.FatouCH.fatouEnds
import Submission.Lib.UnifWrapper

/-!
# The FATOU area contract `MandelDim.FatouStatement` (Shishikura, Appendix A.2 / §4.2)

`MandelDim.FatouStatement` (see `Submission/Work/Interfaces/Fatou.lean`) bundles the six analytic
facts about Fatou coordinates of a near-translation `F` on Shishikura's region `Qreg b₁ b₂`
(`‖F z − (z+1)‖ ≤ 1/32`, `‖F' z − 1‖ ≤ 1/32`):

* `FatouExists`      — a Fatou coordinate `Φ` exists and `Φ (𝒬) = ℂ/ℤ` (A.2.3),
* `FatouOrbit`       — `Φ z' = Φ z + k` forces `z' = F^[k] z` with all intermediate iterates in `𝒬`
                       (A.2.1(i)),
* `FatouUnique`      — two Fatou coordinates on the same region differ by a constant,
* `FatouContinuity`  — A.2.1(iii): the normalised Fatou coordinate depends continuously on `F`
                       (and on the moving regions),
* `FatouDerivEstimate` — Lemma A.2.4(i) (universal bounds for `Φ'`),
* `FatouEnds`        — A.2.4(ii)-type asymptotics `Φ z = z/ρ + c + o(1)` at the ends.

## How this instance is produced

The construction of `Φ` (the "Écalle cylinder" route: `XF = 𝒬 / ⟨F⟩` is uniformised by
`ℂ` after the upper half-plane case is excluded by the length–area argument `QCLiouville`) is
carried out in `Submission/Work/Fatou/FX8/**`:

* `Work.Fatou.FX8.fatouExists`     — FX8: existence of `Φ` with the orbit relation,
* `Work.Fatou.FX8.fatouUnique`     — uniqueness, from the constructed coordinate,
* `Work.Fatou.FX8.fatouContinuity` — A.2.1(iii), from the Koebe-chain local-bound argument of
  `Submission/Work/FatouCH/{Cont,FC}/**` (Shishikura A.2.4(i) bound deep in the region,
  propagated along a uniform walk, then Montel + Hurwitz + uniqueness),
* `MandelDim.uniformizationHyp`    — the uniformization theorem itself (`Submission/Lib/UnifWrapper`).

Two conjuncts are contributed here:

* `Work.FatouCH.fatouDerivEstimate` (submission `Submission/Work/FatouCH/fatouDerivEstimate.lean`)
  — Lemma A.2.4(i), proved from the weak Koebe theorem and Landau's theorem,
* `Work.FatouCH.fatouEnds` (submission `Submission/Work/FatouCH/fatouEnds.lean`) — the end
  asymptotics, proved by integrating the Abel equation along a fundamental window together with
  the derivative estimate.

## Provenance of the *Cauchy–Heine* variant of this area

This file was originally assigned the "Cauchy–Heine" route (solve `ψ(ζ+1) = F(ψ ζ)` on a vertical
strip by a contraction built from the periodic Cauchy–Heine kernel `κ(t) = 1/(1 − e^{2πit})`).
That route is *not* available for this contract, for two independent reasons:

1. Shishikura's own proof of A.2.1(ii) (the existence of `Φ`) goes through the Ahlfors–Bers
   measurable Riemann mapping theorem applied to the pull-back complex structure of the cylinder;
   the Cauchy–Heine construction is a substitute only for the *concrete* maps `F_f` of §4.1, whose
   defect decays exponentially at the ends.
2. In the abstact contract the defect `ε = F − id − 1` is merely *bounded* on `𝒬` (no decay in
   `Im`), so `∫ g(s) κ(ζ − s) ds` is logarithmically divergent along vertical lines and the
   linearised problem `Δu = g` on a strip of width `> 1` has a large kernel (bounded holomorphic
   functions of `e^{2πiζ}` on the corresponding annulus); no log-corrected preconditioner can
   manufacture decay.

The pieces of the Cauchy–Heine analysis that *do* serve the contract (the kernel `κ` and its
identities, the fundamental strip, the injectivity/geometry lemmas, the local-bound and Montel
machinery for continuity, the derivative estimate and the end asymptotics) were built in this
directory and are used above.
-/

namespace Work.FatouCH

open MandelDim

/-- **The FATOU area contract** for near-translations on Shishikura's regions. -/
theorem fatouCH : FatouStatement :=
  Work.Fatou.FX8.fatouStatement_of MandelDim.uniformizationHyp
    (fatouEnds (Work.Fatou.FX8.fatouExists MandelDim.uniformizationHyp)
      (Work.Fatou.FX8.fatouUnique MandelDim.uniformizationHyp) fatouDerivEstimate)

end Work.FatouCH
