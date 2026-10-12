import ChallengeDeps
import Submission.Work.BoseFixB1.boxA2_add_spectral_ge_bogoliubovMain
import Submission.Work.BoseFixB1S.a0A2QPaymentB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
  Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The abstract-parameter joint rung** — verbatim the type of the tree's
`Work.BoseFixB1S.a0A2QJointNormB1` (extracted mechanically from
`Submission/Work/BoseFixB1S/a0A2QPayNormB1.lean`, so the two are syntactically identical), with the
box side `ℓ`, the ratio `d`, the chemical potential `μ` and the spectral index `M` free and the
regime conditions `R0 ≤ ℓd/16`, `R0 ≤ ℓ·chiR0` as hypotheses.  This is the statement the
abstract-parameter consumers (`PerSector`, `SlotWord`'s `FibreWordBound`, `DLWire`) need; see
`FINDING_perBoxCrudeLowerB1_status.md` §11.3. -/
def AbsJointProp {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (R0 : ℝ) (M : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : E3) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
        (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
        (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
          Φ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox ℓ d u)
        (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u))
        (hM2 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
        (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ)
        (hcS2 : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
              ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ),
        Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ
          + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          + Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            * ((1 / 4) * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u - μ) ^ 2
                + (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u + μ)
                  / (2 * Work.SmallBoxSliding.boxMass ℓ d u)
                + 1 / (4 * Work.SmallBoxSliding.boxMass ℓ d u ^ 2))
          + (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
              / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
              * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
          - (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
              * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ)
          + C * (_root_.BoseGases.a v)
              * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
        ≥ 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * (Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
          + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
                * (Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))

/-- **The `chiSmallB`-windowed spectral slot** (FS's *single-cutoff* setup, §14 of the FINDING):
the same `tBwordKinInd` slot as `Work.BoseFixB1.bSpectral`, but with the *cube*-supported kernel
window `chiSmallB` — the window that `boxA2`'s kernel already carries.  Pairing a `chiB`-windowed
spectral word with the `chiSmallB`-windowed pairing is what refuted `BogCoreProp`'s predecessor on
the disjoint-ball `u` (`CornerMismatch.chiB_eq_zero_of_ball_disjoint`). -/
noncomputable def bSpectralCube (v : E3 → ℝ) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.UBBInputs8.tBwordKinInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
    (Work.BoseFixB1.bV v μ u)
    (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u)
    (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ

/-- **The box-normalised spectral slot** (§15): `Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ`
normalises its plane-wave integral by the **ambient** `(a³)⁻¹` — the integral runs over
`abox N a` — so at the sliding box (`a = ℓ`, `volA = V = (ℓd)³`) the corpus's `bSpectralCube` is
smaller than FS's *box*-normalised `Σᵢ Q_Bχ_B[√−Δ−(dsℓ)⁻¹]₊^{-2}χ_BQ_B` by exactly
`volA/a³ = d³`.  Since the `(a³)⁻¹` prefactor is a common factor of the slot sum, the
box-normalised word is the plain multiple `(a³/volA)·tBwordKinInd …`:

    bSpectralBox v μ Φ u = ((bSide v μ)^3 / bV v μ u) · (the cube-windowed slot) .

This is the slot the port must use to be FS-faithful (`d⁻³ → ∞` is the defect of §15). -/
noncomputable def bSpectralBox (v : E3 → ℝ) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  ((Work.BoseFixB1.bSide v μ) ^ 3 / Work.BoseFixB1.bV v μ u) * bSpectralCube v μ Φ u

/-- The multiple is positive at admissible data (both factors are positive), so `bSpectralBox` is
exactly the box-normalised slot and no sign change occurs in the port. -/
theorem bSpectralBox_eq_smul {v : E3 → ℝ} (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) :
    bSpectralBox v μ Φ u
      = ((Work.BoseFixB1.bSide v μ) ^ 3 / Work.BoseFixB1.bV v μ u) * bSpectralCube v μ Φ u := rfl

/-- **The faithful Bogoliubov rung at the sliding box** (FS `eq:refinedaprioribog` / (REPAIRED: the payer carries the state fuel `(n+1)·bFlat`, per FINDING_boxBogCoreSliding_FALSE — `(n+1)·n` alone collapses under scaling)
`eq:simpleaprioribog`, repaired): the payer carries the **particle number** `(n+1)·n/V²`, and the
credit the particle-number line `(μ + n/V)·n₊` (as in `C_ε a((n+1)/|B|)n₊`). -/
def BogPortProp {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        - (C * (_root_.BoseGases.a v)
              * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
              * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u)
          - C * (_root_.BoseGases.a v) * μ
              * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
        ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
            * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
            * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
          + bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u
          + Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u

/-- **The core of the faithful rung**: the same inequality solved for the state-dependent words
(the payer is constant in `Φ`, so this is a *pure rearrangement* — no splitting argument is
needed, unlike the false frozen form whose `(S+1)S` payer forced the discarded square
`α = ½(1+η)ĝω(0)S²·χ/V² + Ca(S/V)n₊`). -/
def BogCoreProp {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        0 ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
              * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
            * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            + bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v)
                * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v) * μ
                * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)

/-- **The core of the port with the box-normalised slot** (§15/§16 of
`FINDING_perBoxCrudeLowerB1_status.md`): the same inequality as `BogCoreProp`, but with the
spectral slot `bSpectralBox` (FS's *box*-normalised `Σᵢ Q_Bχ_B[√−Δ−(dsℓ)⁻¹]₊^{-2}χ_BQ_B`,
i.e. `(ℓ³/V)` times the corpus's ambient-normalised sliding slot), the *matched* `chiSmallB`
window, and the mass-carrying payer `½(1+η)ĝω(0)((n+1)n/V²)·bI·χ`.

**Both failure modes are pre-recorded.**

* If this holds, the port is FS-faithful: the spectral slot pays the pairing's attained
  negativity `−Ω(t^{0.729})` on the mean-free states, and the target's chain proceeds
  (`sbWordAbsorption.sbWord_ge_paid` uses exactly this shape).
* If this fails, the *deliverable is the counterexample family* — and that is the evidence that
  decides whether the sliding pair `(spectral, A₂)` can pay the pairing **at all**, or whether
  the corpus's frozen `sbKin` slot must be re-windowed *and* re-normalised wholesale (a change
  to the frozen vocabulary, hence a decision for this area rather than for one lemma).
  Record the family (parameters, `u ∈ goodSet`, the state, the numbers) in a FINDING next to
  this file: a machine-checked counterexample that forces the vocabulary decision is a permanent
  result, not a dead end.

**Do not** attempt a crude bound of the pairing: `boxA2TwoParticleAttained` shows the sharp zero
point is attained, so the spectral slot is the only possible payer (`FINDING_boxBogCoreSliding_FALSE.md`,
`FINDING_S293_boxCrossJointGen_FALSE.md`).  The estimator to port is
`Submission.BoseGases.lm_appbogolubov_pWord_holds` (`SmallBoxD1Final.lean`) — single bump
`chiScale s`, mass coefficient `d4MassCoeff (N+1) s` — with `NOTES_bogPortSliding.md` listing the
four deltas. -/
def BogCoreBoxProp {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        0 ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
              * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
            * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            + bSpectralBox v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v)
                * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v) * μ
                * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)

/-- **The core closes the rung**: the faithful rung is the core rearranged (the payer does not
involve the state). -/
theorem bogPort_of_core {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (H : BogCoreProp h) :
    BogPortProp h := by
  obtain ⟨ε₀, η, C, hε, hη, hC, Hc⟩ := H
  refine ⟨ε₀, η, C, hε, hη, hC, fun μ hAdm n Φ u hgood => ?_⟩
  have h := Hc μ hAdm n Φ u hgood
  linarith

/-- Conversely the rung gives the core (they are the same inequality). -/
theorem bogCore_of_port {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (H : BogPortProp h) :
    BogCoreProp h := by
  obtain ⟨ε₀, η, C, hε, hη, hC, Hc⟩ := H
  refine ⟨ε₀, η, C, hε, hη, hC, fun μ hAdm n Φ u hgood => ?_⟩
  have h := Hc μ hAdm n Φ u hgood
  linarith

end Work.BoseFixB1S
