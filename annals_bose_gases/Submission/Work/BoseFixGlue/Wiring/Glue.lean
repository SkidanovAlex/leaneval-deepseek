import ChallengeDeps
import Submission.Work.BoseFixGlue.Kinetic.integrable_kinForm
import Submission.Work.BoseFixGlue.Kinetic.kin_le_dspace
import Submission.Work.BoseFixGlue.Ports.LHYBoxB_of_grading
import Submission.Work.BoseFixGlue.Ports.nodeB2gB_of_data
import Submission.Work.BoseFixGlue.Pot.potInput_holds
import Submission.Work.BoseFixGlue.Pot.swapInput_holds
import Submission.Work.BoseFixGlue.Sector.fibreSumBound_of_LHYBoxB
import Submission.Work.BoseFixGlue.Sector.fibreSumBound_to_fibreInput
import Submission.Work.BoseFixGlue.Wiring.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Wiring.Glue` — the wiring, from `LHYBoxB` to `HBoxGSymStateScaled`

The final assembly of the C-side wiring.  `Wiring/Main.lean` proves the wiring conditional on the
four C-side clauses bundled in `CompareInputs`; this module *produces* all four of them:

* **kin** (`KinInput`) — from BoseKinLoc's `KineticLocalisation` (FS `lem:LocKinEn`, proved for
  some `c₀ > 0`) through this chapter's `Kinetic.integrable_kinForm` (the `u`-integrability of the
  kinetic word), `Kinetic.kin_le_dspace` (the `N`-body lifting) and
  `Params.kinRegime_of_params` (FS's parameters lie in `KinRegime c₀` as soon as
  `bValue ≤ c₀` — the `b`-clash fix of the design §5);
* **pot** (`PotInput`) — FS `lem:LocPotential`, from `Pot.potInput_holds`
  (`Work.BoseKinLoc.Pot.pot_average`, proved);
* **swap** (`SwapInput`) — the joint `(u,x)`-integrability of `Φ²·potWordU`, from
  `Pot.swapInput_holds`;
* **fibre** (`FibreInput`) — FS `thm:CompareBoxEnergy`'s `H_{Λ,u}(μ) ≥ E_Λ(μ)` on the symmetric
  sector, from `Sector.fibreSumBound_of_LHYBoxB` (the per-fibre argument, with the bounded-below
  inputs `hEo`/`hEi` supplied by `LHYBoxB` through `EΛ_ge_lambda_of_LHYBoxB`) and
  `Sector.fibreSumBound_to_fibreInput` (the case analysis: the sector decomposition
  `boxForm_fibreSumA_of_integrable` when the potential integrand is integrable, the kinetic word
  otherwise).

Consequently the headline `HBoxGSymStateScaled_of_LHYBoxB` has **no C-side hypothesis** beyond
`LHYBoxB` and `hb`: its consumer is the proved `Work.BoseTop.theorem_1_2_of_HBoxGSymStateScaled`
(through `Work.BoseTop.PerN.HBoxGp_of_scaledState`, see `Tests/Handoff.lean`).
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The kinetic clause -/

/-- **The kinetic lifting at FS's parameters.**  From `KineticLocalisation c₀` (FS
`lem:LocKinEn`, with `bValue ≤ c₀` so that FS's fixed gap coefficient `b = 1/16` is admissible)
and FS's parameter choice, the `N`-body kinetic word is dominated by the total kinetic energy for
every state supported in a centred box `abox N L` with `L ≥ ℓ(μ)`. -/
theorem kinInput_holds {v : ℝ³ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hbc : bValue ≤ c₀)
    (hav : 0 < a v) (hKin : KineticLocalisation c₀) : ∃ ε : ℝ, 0 < ε ∧ KinInput v ε := by
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixGlue.Params.kinRegime_of_params hc₀ hbc hav
  refine ⟨εr, hεr, fun μ hAdm N L hℓL Φ hΦ _hsym hsupp => ?_⟩
  have hμpos : 0 < μ := hAdm.1
  have hregμ : KinRegime c₀ (ℓB v μ) (dB v μ) (sB v μ) (eTB v μ) (bB v μ) :=
    hreg μ hμpos hAdm.2.1
  have hℓpos : 0 < ℓB v μ := hregμ.1
  have hdpos : 0 < dB v μ := hregμ.2.1
  have hLpos : 0 < L := lt_of_lt_of_le hℓpos hℓL
  exact Work.BoseFixGlue.Kinetic.kin_le_dspace hKin hregμ hLpos.le hΦ hsupp
    (Work.BoseFixGlue.Kinetic.integrable_kinForm hℓpos hdpos hLpos hΦ hsupp)

/-! ## 2. The fibre clause -/

/-- **The fibre clause from `LHYBoxB`** (FS `thm:CompareBoxEnergy`'s `H_{Λ,u}(μ) ≥ E_Λ(μ)` on the
symmetric sector): the first half is the per-fibre bound on the fibre sum
(`Sector.fibreSumBound_of_LHYBoxB`), the second the case analysis turning the fibre sum into the
box form (`Sector.fibreSumBound_to_fibreInput`). -/
theorem fibreInput_holds {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hav : 0 < a v) (hC : 0 ≤ C) (hL : LHYBoxB v h η₀ C) :
    ∃ ε : ℝ, 0 < ε ∧ FibreInput v h ε := by
  obtain ⟨ε₁, hε₁, hA⟩ := Work.BoseFixGlue.Sector.fibreSumBound_of_LHYBoxB hav hC hL
  obtain ⟨ε₂, hε₂, _hle, hI⟩ :=
    Work.BoseFixGlue.Sector.fibreSumBound_to_fibreInput hε₁ hA
  exact ⟨ε₂, hε₂, hI⟩

/-! ## 3. The four clauses at a common threshold -/

/-- **The C-side inputs** from the discharged clauses and a given fibre clause at `εf`
(the conditional form, used when only the fibre bound is available). -/
theorem compareInputs_of_fibre {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv1 : MemLp v 1) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    (hb : ∃ c₀ : ℝ, 0 < c₀ ∧ bValue ≤ c₀ ∧ KineticLocalisation c₀)
    {εf : ℝ} (hεf : 0 < εf) (hfib : FibreInput v h εf) : CompareInputs v h := by
  obtain ⟨c₀, hc₀, hbc, hKin⟩ := hb
  obtain ⟨εk, hεk, hkin⟩ := kinInput_holds hc₀ hbc hav hKin
  obtain ⟨εp, hεp, hpot⟩ := Work.BoseFixGlue.Pot.potInput_holds hR hv1 hv_supp hav
  obtain ⟨εs, hεs, hswap⟩ := Work.BoseFixGlue.Pot.swapInput_holds hR hv1 hv_supp hav
  have hε : 0 < min εk (min εp (min εf εs)) :=
    lt_min hεk (lt_min hεp (lt_min hεf hεs))
  have h1 : min εk (min εp (min εf εs)) ≤ εk := min_le_left _ _
  have h2 : min εk (min εp (min εf εs)) ≤ εp :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have h3 : min εk (min εp (min εf εs)) ≤ εf :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : min εk (min εp (min εf εs)) ≤ εs :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨min εk (min εp (min εf εs)), hε, ?_⟩
  intro μ hAdm N L hℓL Φ hΦ hsym hsupp
  exact ⟨KinInput.mono hkin h1 μ hAdm N L hℓL Φ hΦ hsym hsupp,
    FibreInput.mono hfib h3 μ hAdm N L hℓL Φ hΦ hsym hsupp,
    SwapInput.mono hswap h4 μ hAdm N L hℓL Φ hΦ hsym hsupp,
    PotInput.mono hpot h2 μ hAdm N L hℓL Φ hΦ hsym hsupp⟩

/-- **The C-side inputs** with *all four* clauses discharged from `LHYBoxB`, the kinetic
localisation `hb` and the ambient hypotheses. -/
theorem compareInputs_of_data {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ} {R : ℝ}
    (hR : 0 < R) (hv1 : MemLp v 1) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    (hC : 0 ≤ C) (hb : ∃ c₀ : ℝ, 0 < c₀ ∧ bValue ≤ c₀ ∧ KineticLocalisation c₀)
    (hL : LHYBoxB v h η₀ C) : CompareInputs v h := by
  obtain ⟨εf, hεf, hfib⟩ := fibreInput_holds hav hC hL
  exact compareInputs_of_fibre hR hv1 hv_supp hav hb hεf hfib

/-! ## 4. The headline: `LHYBoxB` ⟹ `HBoxGSymStateScaled` -/

/-- **The wiring theorem** (design `BOSE_BOXNODES_LEAD.md` §5, with the C-side inputs discharged).

From FS's box theorem `LHYBoxB` (on symmetric box states, particle number free, at FS's
parameters) and BoseKinLoc's kinetic localisation at `c₀ ≥ bValue` (`hb`), the per-state scaled
handoff `Work.BoseTop.HBoxGSymStateScaled v η₀ C (ρ ↦ sideAt ρ (a v))` follows. -/
theorem HBoxGSymStateScaled_of_LHYBoxB {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀' : η₀ ≤ 1 / 2) (hC : 0 ≤ C)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hav : 0 < a v)
    (hb : ∃ c₀ : ℝ, 0 < c₀ ∧ bValue ≤ c₀ ∧ KineticLocalisation c₀)
    (hL : LHYBoxB v h η₀ C) :
    Work.BoseTop.HBoxGSymStateScaled v η₀ C (fun ρ => sideAt ρ (a v)) :=
  HBoxGSymStateScaled_of_compareInputs hη₀ hη₀' hC hv1 hR hv_supp hav hb
    (compareInputs_of_data hR hv1 hv_supp hav hC hb hL) hL

/-- **The same theorem in the paper's ambient hypotheses** (`0 ≤ v`, radial, `MemLp v 1`,
`tsupport v ⊆ ball 0 R`): the extra hypotheses are not used by the proof, and are carried only to
match the shape of `BOSE_BOXNODES_LEAD.md` §5 (so that a caller can replace the vacuous old
`HBoxG_holds` by this statement without touching its hypothesis list). -/
theorem HBoxGSymStateScaled_of_LHYBoxB_fs {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    (hη₀ : 1 / 2000 < η₀) (hη₀' : η₀ ≤ 1 / 2) (hC : 0 ≤ C)
    (hb : ∃ c₀ : ℝ, 0 < c₀ ∧ bValue ≤ c₀ ∧ KineticLocalisation c₀)
    (hL : LHYBoxB v h η₀ C) :
    Work.BoseTop.HBoxGSymStateScaled v η₀ C (fun ρ => sideAt ρ (a v)) :=
  HBoxGSymStateScaled_of_LHYBoxB hη₀ hη₀' hC hv1 hR hv_supp hav hb hL

/-! ## 5. The end-to-end B-side chain

The §6 data (`NodeB2gB`, from `B2GradingDataB` and the §5 window) and the §7–§11 restricted bound
(`NodeRestrictedB`) give `LHYBoxB` (`Ports.LHYBoxB_of_grading`, at the shifted constant `C + 1`),
which the wiring then converts into `HBoxGSymStateScaled`.  This is the full B-side content of the
corrected chain `B2GradingDataB + NodeB1B → NodeB2gB → LHYBoxB → HBoxGSymStateScaled`. -/
theorem HBoxGSymStateScaled_of_grading {v : ℝ³ → ℝ} {h : ScatSol v} {J J' η₀ C : ℝ}
    (hlhy : lhyC ≤ J) (hJJ : J < J') (hη₀ : 1 / 2000 < η₀) (hη₂ : η₀ < 2 / 323)
    (hC : 0 ≤ C) (hv1 : MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    (hb : ∃ c₀ : ℝ, 0 < c₀ ∧ bValue ≤ c₀ ∧ KineticLocalisation c₀)
    (hg : NodeB2gB v h J J') (hr : NodeRestrictedB v h J' η₀ C) :
    Work.BoseTop.HBoxGSymStateScaled v η₀ (C + 1) (fun ρ => sideAt ρ (a v)) :=
  HBoxGSymStateScaled_of_LHYBoxB hη₀ (by linarith) (by linarith) hv1 hR hv_supp hav hb
    (Work.BoseFixGlue.Ports.LHYBoxB_of_grading hlhy hav hC (by linarith) hη₂ hJJ hg hr)

end Work.BoseFixGlue
