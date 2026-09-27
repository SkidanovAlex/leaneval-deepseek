import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs

/-!
# The shape data of a Möbius packet (H7 lane)

`Work.Drive.N2Lead.MobiusPacket` exports the *values* of the anchored polar picture
(`hC₀val : C₀ (L.γ i t) = cE3 (r (Θ t) e^{i Θ t})`) but no *shape* information about the radial
profile `r`, and no pinned-arc dictionary.  The star rows of the twisted Möbius picture
(`Work.Drive.N2Lead.mobiusUpperStarRows`, see
`Submission/Work/Drive/N2Lead/NOTES_S48_starRows_DIAGNOSIS.md` §2) need both: the two profile rows
`hrev` (evenness) and `hrdec` (monotonicity on the bridge zone) of `mobius_bridgeStar`, the bridge
lower bound `hlo`, and the arc dictionary `hΘu/hΘl`, `hZu/hZd` (the last pair is what makes the
pinned part of the anchored component meet the model picture `cE3 ∘ Ψ ∘ Z`).

This file names that missing information as a predicate on a packet, so that

* the *existence* of a packet with the shape data is a single statement
  (`Work.Drive.N2C.mobiusPacketExistsShape`), and
* the star rows can be stated and proved conditional on it, without touching the (H8-owned)
  structure `MobiusPacket`.

Everything in `MobiusShape` is supplied by the concrete packet of
`Work.Drive.N2C.mobiusPacketExistsShape` (the profile rows come from
`Work.Drive.N2C.saddleProfileRowsMobiusFull`, the dictionary from the construction itself).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

/-- **The shape data of a Möbius packet**: the two profile rows of `mobius_bridgeStar`
(evenness and bridge-zone monotonicity), the bridge lower bound, and the pinned-arc dictionary of
the marked component of the anchor level. -/
structure MobiusShape {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (η : ℝ)
    (S : Work.Drive.N2Lead.MobiusPacket D η) where
  /-- the radial profile is even -/
  hrev : ∀ φ : ℝ, S.r (-φ) = S.r φ
  /-- the radial profile is nonincreasing on the bridge zone -/
  hrdec : ∀ φ ∈ Set.Icc (0 : ℝ)
    (Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50)), deriv S.r φ ≤ 0
  /-- the bridge lower bound of the radial profile -/
  hlo : ∀ (φ : ℝ) (k : ℤ),
    |φ - k * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50) →
      Real.sqrt ((Work.Drive.N2.packetEta D η) ^ 2 + (99 / 50) ^ 2) ≤ S.r φ ^ 2
  /-- the upper pinned arc lift of the marked component -/
  tauU : ℝ → ℝ
  /-- the lower pinned arc lift of the marked component -/
  tauL : ℝ → ℝ
  hThetau : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
    S.Θ (tauU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / Work.Drive.N2.packetEta D η)
  hThetal : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
    S.Θ (tauL w) = 3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / Work.Drive.N2.packetEta D η)
  hZu : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
    S.Z (S.L.γ S.i (tauU w)) = Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w
  hZd : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
    S.Z (S.L.γ S.i (tauL w)) = -Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w
  hZuPt : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
    S.L.γ S.i (tauU w)
      = Work.Drive.N2Lead.arcUpPt D S.lam0 (Work.Drive.N2.packetEta D η) w
  hZdPt : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
    S.L.γ S.i (tauL w)
      = Work.Drive.N2Lead.arcDnPt D S.lam0 (Work.Drive.N2.packetEta D η) w
  /-- the radial profile is `π`-periodic (the split engine's `hrpi`) -/
  hrpi : ∀ φ : ℝ, S.r (φ + Real.pi) = S.r φ
  /-- the numeric row `c₀ + 2ηs < √(ηs² + m²)` of the bridge (`hnum` of `saddleBridgeRowMobius`) -/
  hnum : 39 / 20 + 2 * Work.Drive.N2.packetEta D η
    < Real.sqrt ((Work.Drive.N2.packetEta D η) ^ 2 + (99 / 50) ^ 2)
  /-- the polar value on the **upper** pinned arc: the profile at the pinned angle is the upper arc -/
  hpolarU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
    (S.r (S.Θ (tauU w)) : ℂ) * Complex.exp (((S.Θ (tauU w) : ℝ) : ℂ) * Complex.I)
      = Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w
  /-- the polar value on the **lower** pinned arc: it is the *conjugate* of the lower arc (the Möbius
  mirror, fixed by `mobiusPinTwist`) -/
  hpolarL : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
    (S.r (S.Θ (tauL w)) : ℂ) * Complex.exp (((S.Θ (tauL w) : ℝ) : ℂ) * Complex.I)
      = star (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w)
  /-- the two arc lifts are differentiable with nonvanishing derivative in the pin interval -/
  hτu : ∀ w ∈ Set.Ioo (-(99 / 50)) (99 / 50),
    DifferentiableAt ℝ tauU w ∧ deriv tauU w ≠ 0
  hτl : ∀ w ∈ Set.Ioo (-(99 / 50)) (99 / 50),
    DifferentiableAt ℝ tauL w ∧ deriv tauL w ≠ 0

end Work.Drive.N2C
