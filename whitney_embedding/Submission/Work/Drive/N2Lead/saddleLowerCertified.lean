import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.saddlePacket
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_starRegions
-- H8 (2026-09-27): the statement below is proved in `saddleLowerCertifiedFleet.lean` by the child
-- `…-L3272`; this file only re-exports it under the canonical name (the two statements are
-- identical).
import Submission.Work.Drive.N2Lead.saddleLowerCertifiedFleet

/-!
# §4.2 of the saddle packet: the lower certificate

The anchor level of the saddle window carries two kinds of pieces of the two-piece drawing `W`: on
the model region (`saddleRegion U Z c₀`) the model picture `cE3 (saddlePsi η δ (Z ·))`, off it the
transported picture `A ∘ foot`.  On the *anchor* level `a = f p - lam * ηs` the foot map is the
identity (`foot y = D.Φ (a - f y, y) = D.Φ (0,y) = y`), and on the region the pin row gives
`A = cE3 (saddlePsi η δ (Z ·))`; hence `W = A` on the whole level `a`, and the certificate of `W` at
`a` is the certificate of the *park picture* `A`.

`IsCertifiedAt f a A` depends on `A` only through its values on the level, and those are the packet's
prescribed curves: the marked component `i` is drawn by the polar curve
`C₀ t = cE3 (r (Θ t) * exp (i Θ t))` and every other component by a parked round circle
(`farCurve n j`, centred at `farPos n j = (-20, 20 + 5j, 1)`).

This file states the resulting reduction: *the star rows of the polar curve about `0` and of the
parked circles about their centres certify `A` at `a`*, in the abstract form of the packet data, so
that any formulation of the packet can instantiate it.  The proof feeds the proved interface
`Work.Drive.N2Lead.isCertifiedAt_of_starRegions` with the regions
`Ω 0 = ball 0 (R+1)` (centre `0`, radius `R`) and, for `j : Fin n`, `Ω (j+1) =
ball (proj2 (farPos n j)) 2` (centre `proj2 (farPos n j)`, radius `1`); see
`NOTES_H8_target_rewired_and_certificate_42.md` §4 for the route of the three rows.
-/

open scoped Manifold ContDiff

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set

open scoped Manifold ContDiff in
/-- **§4.2: the lower certificate of the saddle packet.**  With a `LevelCurves` parametrisation `L`
of the regular anchor level `f = a`, a picture `A` of that level with its injectivity and
`ker df`-immersivity rows, whose values on the marked component are the polar curve of a positive
smooth `2π`-periodic profile `r` along a strictly increasing angle function `Θ` with
`Θ (t+1) = Θ t + 2π`, and whose values on every other component are the parked round circles
`farCurve n j`, the picture `A` is certified at `a`. -/
theorem saddleLowerCertified {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {a : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f a n)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ Work.Drive.Morse.IsCritical f x)
    {A : M → EuclideanSpace ℝ (Fin 3)}
    (hAsm : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAinj : ∀ x y : M, f x = a → f y = a → A x = A y → x = y)
    (hAimm : ∀ x : M, f x = a → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0)
    {i : Fin n} {r Θ : ℝ → ℝ} {R : ℝ}
    (hc : ∀ t : ℝ, A (L.γ i t) =
      Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)))
    (hfarA : ∀ j : Fin n, j ≠ i → ∀ t : ℝ, A (L.γ j t) = farCurve n j t)
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) (hrR : ∀ φ : ℝ, r φ ≤ R) (hR : R < 17)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0)
    (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi) :
    Work.Drive.N2C.IsCertifiedAt f a A :=
  saddleLowerCertifiedFleet L hf hreg hAsm hAinj hAimm hc hfarA hr hrpos hrper hrR hR hΘ hΘmono
    hΘderiv hΘper

end Work.Drive.N2Lead
