import ChallengeDeps
import Submission.Work.BoseGateFS.GateThresholds
import Submission.Work.BoseRowsFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.HonestInterface` — the honest rows of FS §11/§12 as one object

> **Which fields are FS's own inputs, and which are ours.**  Nothing in this area
> currently inhabits `HonestInterface`, and it is worth being explicit about where
> each field stands:
>
> * **FS's own inputs** (their lemmas `eq:W1-decay`-type hypotheses that `ScatSol`
>   does not imply, because with a merely `L¹` compactly supported `v` the kernel
>   `W₁fun = g₀/(χ⋆χ)(·/ℓ)` is not smooth): `decayW`, `decayg`.
> * **Cube-size data** the caller chooses: `cut`, and the `tail` row (the UV-cut
>   tail of `honest_sum_diff`, provably not implied by `GateThresholds.cube` —
>   `FINDING_session3.md` §2a).
> * **Régime/parameter rows** that the honest data does satisfy and that a caller
>   instantiates from `GateThresholds` plus the honest environment: `fsp`,
>   `fspKz`, `rkh`, `a16`.
>
> Rows 1 and 2 of the gate are **theorems** of this area
> (`RowSumW1sq_regime`, `RowIntOneRegime_honest`) given this structure; nothing
> else of the gate is assumed here.

Everything that row 2 (`hint`, FS `lem:EstimateIntegral`) needs at the honest
model, beyond FS §4's régime and the node's parameter bundle `GateThresholds`,
collected in one structure so that a caller has a single object to instantiate:

* `Cw`, `Cw_nonneg`, `decayW`, `decayg` — FS's two **decay rows** for the honest
  kernels, `|Ŵ₁(p)|(1+‖p‖)² ≤ Cw·a v` and `|ĝ(p)|(1+‖p‖)² ≤ Cw·a v`, uniformly over
  the régime `1 ≤ ℓ`, `R ≤ ℓ·chiR0`.  (`ScatSol` does *not* imply them: with a
  merely `L¹` compactly supported `v`, `W₁fun = g₀/(χ⋆χ)(·/ℓ)` is not smooth and
  `Ŵ₁` does not decay — `FINDING_omega_lattice_honest_ng.md`.)
* `cut` — the **UV-cut cube conditions** (`1/R ≤ 2Λ_N`, `Cw²ℓ ≤ (2Λ_N)³`) that
  `omega_lattice_honest_decay` consumes.  They are *not* among
  `GateThresholds.cube`'s rows.
* `tail` — the **UV-cut tail row** of `honest_sum_diff`: the modes of the cube
  with `‖kmom k‖ > uvRad` contribute `≲ Cw²a(R/ℓ)⁴` to the `ℓ⁻³Σ(ĝ²+Ŵ₁²)/‖k‖²`.
  This row is genuinely new: the cut shell `[uvRad, (2√3/π)·uvRad]` is always
  non-empty, and `GateThresholds.cube` is too weak to control it
  (`FINDING_session3.md` §2a).
* `fsp`, `fspKz` — `FSParamsView` at the honest environment and at the
  `ρ`-re-pointed one.
* `rkh`, `a16` — the two remaining régime rows of FS's argument
  (`(R/ℓ)² ≤ K_H⁻¹` and `a K_H/(s ℓ) ≤ 1/16`).

`Work.BoseRowsFS.exists_honestGateFS_of_honestInterface` (same directory) turns
`HonestInterface` **plus row 3 alone** into `HonestGateFS`.
-/

noncomputable section

open scoped Real BigOperators Topology

namespace Work.BoseRowsFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases
open Work.BoseGateFS

/-- **The honest rows of FS §11/§12 at the node's parameter bundle.** -/
structure HonestInterface {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hthr : GateThresholds v h fc fu R) where
  /-- The absolute constant of FS's two decay rows. -/
  Cw : ℝ
  Cw_nonneg : 0 ≤ Cw
  /-- FS's decay row for `Ŵ₁`. -/
  decayW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
    ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2
        ≤ Cw * _root_.BoseGases.a v
  /-- FS's decay row for `ĝ`. -/
  decayg : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
    ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 2
        ≤ Cw * _root_.BoseGases.a v
  /-- The UV-cut cube conditions. -/
  cut : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    1 / R ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (hthr.Ng μ)
      ∧ Cw ^ 2 * Work.BoseBoxFock.ellH v μ
          ≤ (2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (hthr.Ng μ)) ^ 3
  /-- The UV-cut tail row of `honest_sum_diff`. -/
  tail : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
    (∀ μ, hthr.Ng μ ≤ (HM μ).N) →
    ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              (fun k => Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
                < ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖),
            (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2
              + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                  ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2)
              / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
        ≤ Cw ^ 2 * _root_.BoseGases.a v
            * (R / Work.BoseBoxFock.ellH v μ) ^ 4
  /-- `FSParamsView` at the honest environment. -/
  fsp : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ)
  /-- `FSParamsView` at the `ρ`-re-pointed environment. -/
  fspKz : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    Work.BoseGateFS.AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
    Work.BoseB7.FSParamsView
      (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
  /-- FS's régime row `(R/ℓ)² ≤ K_H⁻¹`. -/
  rkh : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    (R / (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ 2
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).KH⁻¹
  /-- FS's régime row `a K_H/(s ℓ) ≤ 1/16`. -/
  a16 : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
    (Work.BoseRowsFS.honE v h fc fu HM μ).aScat * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
      / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
        * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16

end Work.BoseRowsFS
