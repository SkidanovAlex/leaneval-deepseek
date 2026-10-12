import ChallengeDeps
import Submission.Work.BoseGateAll.Final
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateAll.Interface` — the honest gate from the interfaces

The top of the port: `BOSE_ALL_DESIGN.md` item 6's deliverable
`exists_honestGateFSAll_of_honestInterface` (plus its `HonestInterfaceL` variant).

* `exists_honestGateFSAll_of_honestInterface` — from FS §4's régime bundle
  `GateThresholds`, the row interface `Work.BoseRowsFS.HonestInterface` and the
  corrected row 3 `Work.BoseRowQ2.RowQ2AllRegimeN`, produce the honest `All` gate
  at one absolute pair `(K₀, b₀)`.  Rows 1 and 2 are supplied by the proved corpus
  theorems `RowSumW1sq_regime` and `RowIntOneRegime_honest`; **row 3 is the only
  input**, exactly as in the corpus — but at `Q₂^{ex,all}`, with **no** reserve
  obligation (`RowReserveLabelZero` is not used anywhere in this directory).
* `Work.BoseGateFS.GateThresholds.promoteNg` — enlarge the cube-size function of
  the threshold bundle (the fields are all monotone in `Ng`, since the row
  hypotheses are `∀ μ, Ng μ ≤ (HM μ).N`).
* `exists_honestGateFSAll_of_honestInterfaceL` — the decay-free variant, stated for
  the live interface `Work.BoseRowsL.HonestInterfaceL` (item 7's field list **plus**
  the continuum far tail `tailC`), so that it composes with
  `Work.BoseRowsL.exists_honestInterfaceL` and item 7's row 2.  Row 1 is still
  derived (`RowSumW1sq_regime` needs no decay); row 2 at `H.Ng'` is the one
  analytic import of item 7 (`latticeCoulomb_approx` + the truncation), taken here
  as the hypothesis `hrow2L` in exactly the form item 7 produces it.
* `exists_honestGateFSAll_of_Ldata` — the same assembly with the two interface
  fields it uses (`Ng'`, `Ng'_ge`) as bare arguments.
* `exists_honestGateFSAll_of_designInterfaceL` — the same for the design's field
  list verbatim (`Work.BoseGateAll.HonestInterfaceL`); see the warning in
  `Defs.lean` §3 — without `tailC`, `tailL` is not licensed by the design's
  hypotheses and that structure has no known inhabitation.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **Enlarging the cube-size function of the small-parameter bundle.**  Every
field of `GateThresholds` is a row of the form
`∀ HM, (∀ μ, Ng μ ≤ (HM μ).N) → …`, so replacing `Ng` by a larger `Ng' ≥ Ng`
preserves all of them (`GateThresholds.mono` is the `εg`-analogue). -/
def GateThresholds.promoteNg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {R : ℝ} (H : GateThresholds v h fc fu R)
    (Ng' : ℝ → ℕ) (hle : ∀ μ, H.Ng μ ≤ Ng' μ) : GateThresholds v h fc fu R where
  Ng := Ng'
  εg := H.εg
  pos := H.pos
  le_one := H.le_one
  cube := fun HM hN μ hμ hε => H.cube HM (fun μ => le_trans (hle μ) (hN μ)) μ hμ hε
  dil := fun HM hN μ hμ hε => H.dil HM (fun μ => le_trans (hle μ) (hN μ)) μ hμ hε
  dilTau := fun HM hN μ hμ hε => H.dilTau HM (fun μ => le_trans (hle μ) (hN μ)) μ hμ hε
  dilKH := fun HM hN μ hμ hε => H.dilKH HM (fun μ => le_trans (hle μ) (hN μ)) μ hμ hε

end Work.BoseGateFS

namespace Work.BoseGateAll

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases
open Work.BoseGateFS

set_option linter.unusedVariables false

/-- **The `All` gate from the honest interface** (design item 6, D4's headline).
From FS §4's régime bundle, the row interface `HonestInterface` and the corrected
row 3 `RowQ2AllRegimeN`, the honest gate `HonestGateFSAll` holds at one absolute
pair `(K₀, b₀)`.  Rows 1 and 2 are derived from the interface
(`RowSumW1sq_regime`, `RowIntOneRegime_honest`); row 3 is the single input. -/
theorem exists_honestGateFSAll_of_honestInterface
    {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : Work.BoseRowsFS.HonestInterface R hthr)
    (hrow3All : Work.BoseRowQ2.RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu)
      hthr.Ng R hthr.εg) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFSAll v h fc fu K₀ b₀ := by
  classical
  -- ## 0. The `HM`-independent régime rows (`1 ≤ ℓ`, `R ≤ ℓ χ_{R₀}`).
  obtain ⟨HM0, hHM0⟩ : ∃ HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ,
      ∀ μ, hthr.Ng μ ≤ (HM μ).N := by
    choose HM hN using fun μ => Work.BoseBoxFock.exists_honestModes v μ (hthr.Ng μ)
    exact ⟨HM, fun μ => le_of_eq (hN μ).symm⟩
  have hrége : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := by
    intro μ hμ hε
    obtain ⟨h1, _h2, h3, _h4, _h5, _h6⟩ := hthr.dil HM0 hHM0 μ hμ hε
    exact ⟨h1, h3⟩
  -- ## 1. The two diluteness-restricted rows at the interface's threshold.
  obtain ⟨Cws, hCws0, hrow1⟩ :=
    Work.BoseRowsFS.RowSumW1sq_regime (v := v) (h := h) (fc := fc) (fu := fu) (R := R)
      hR hav hv_nonneg hvrad hv_supp hthr.εg hrége
  obtain ⟨ε₀, Kint, hε₀pos, hε₀le, hKint0, hrow2⟩ :=
    Work.BoseRowsFS.RowIntOneRegime_honest (v := v) (h := h) (fc := fc) (fu := fu) R hR hav
      hv_nonneg hvrad hv_supp H.Cw H.Cw_nonneg H.decayW H.decayg hthr.Ng hthr.εg hthr.pos hrége
      H.cut H.tail H.fsp H.fspKz H.rkh H.a16
  -- ## 2. Assembly at the shrunk threshold `min εg ε₀`.
  refine exists_honestGateFSAll_of_regime_rows R hR hav hv_nonneg hvrad hv_supp
    (hthr.mono (εg' := min hthr.εg ε₀) (lt_min hthr.pos hε₀pos) (min_le_left _ _))
    Cws hCws0 ?_ Kint hKint0 ?_ ?_
  · -- row 1 below the shrunk threshold
    intro HM hN μ hμ hε
    exact hrow1 HM μ hμ (le_trans hε (min_le_left _ _))
  · -- row 2 below the shrunk threshold (`ε₀`-availability suffices)
    intro HM hN μ hμ hε ρ hρ
    exact hrow2 HM hN μ hμ (le_trans hε (min_le_right _ _)) ρ hρ
  · -- row 3 below the shrunk threshold
    intro HM hN μ hμ hε ρ hρ Ψ
    exact hrow3All HM hN μ hμ (le_trans hε (min_le_left _ _)) ρ hρ Ψ

/-- **The `All` gate from the decay-free data** (design items 6 + 7), abstract
form: the cube size `Ng'`, its domination of the bundle's `Ng`, item 7's row 2 at
`Ng'` (with its own threshold `ε₁ ≤ εg`) and the corrected row 3.

Row 1 needs no decay row and is *derived* here (`RowSumW1sq_regime`); row 3 is the
corrected row `RowQ2AllRegimeN` (the single row input); `hrow2L` is item 7's
`latticeCoulomb_approx`-based K5, the only missing analytic input.  The two
`HonestInterfaceL` variants below are one-line instances. -/
theorem exists_honestGateFSAll_of_Ldata
    {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (Ng' : ℝ → ℕ) (hNg' : ∀ μ, hthr.Ng μ ≤ Ng' μ)
    (hrow2L : ∃ ε₁ Kint : ℝ, 0 < ε₁ ∧ ε₁ ≤ hthr.εg ∧ 0 ≤ Kint ∧
      Work.BoseRowsFS.RowIntOneRegimeN (h := h) (fc := fc) (fu := fu) Ng' R ε₁ Kint)
    (hrow3All : Work.BoseRowQ2.RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu)
      hthr.Ng R hthr.εg) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFSAll v h fc fu K₀ b₀ := by
  classical
  -- ## 0. The régime rows at the interface's cube size `Ng'`.
  obtain ⟨HM0, hHM0⟩ : ∃ HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ,
      ∀ μ, hthr.Ng μ ≤ (HM μ).N := by
    choose HM hN using fun μ => Work.BoseBoxFock.exists_honestModes v μ (hthr.Ng μ)
    exact ⟨HM, fun μ => le_of_eq (hN μ).symm⟩
  have hrége : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := by
    intro μ hμ hε
    obtain ⟨h1, _h2, h3, _h4, _h5, _h6⟩ := hthr.dil HM0 hHM0 μ hμ hε
    exact ⟨h1, h3⟩
  -- ## 1. Row 1 (no decay row is used at all) at the interface threshold.
  obtain ⟨Cws, hCws0, hrow1⟩ :=
    Work.BoseRowsFS.RowSumW1sq_regime (v := v) (h := h) (fc := fc) (fu := fu) (R := R)
      hR hav hv_nonneg hvrad hv_supp hthr.εg hrége
  -- ## 2. Row 2 at `Ng'` (the item 7 input) — the only hypothesis.
  obtain ⟨ε₁, Kint, hε₁pos, hε₁le, hKint0, hrow2⟩ := hrow2L
  -- ## 3. Assembly at the cube size `Ng'` and the threshold `ε₁`.
  refine exists_honestGateFSAll_of_regime_rows R hR hav hv_nonneg hvrad hv_supp
    ((hthr.promoteNg Ng' hNg').mono (εg' := ε₁) hε₁pos hε₁le)
    Cws hCws0 ?_ Kint hKint0 ?_ ?_
  · intro HM hN μ hμ hε
    exact hrow1 HM μ hμ (le_trans hε hε₁le)
  · intro HM hN μ hμ hε ρ hρ
    exact hrow2 HM hN μ hμ hε ρ hρ
  · intro HM hN μ hμ hε ρ hρ Ψ
    exact hrow3All HM (fun μ => le_trans (hNg' μ) (hN μ)) μ hμ (le_trans hε hε₁le) ρ hρ Ψ

/-- **The `All` gate from the live decay-free interface**
`Work.BoseRowsL.HonestInterfaceL` (design item 7's field list **plus** the
continuum far tail `tailC`), i.e. the form that composes with
`Work.BoseRowsL.exists_honestInterfaceL` and item 7's row 2 at `H.Ng'`. -/
theorem exists_honestGateFSAll_of_honestInterfaceL
    {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : Work.BoseRowsL.HonestInterfaceL R hthr)
    (hrow2L : ∃ ε₁ Kint : ℝ, 0 < ε₁ ∧ ε₁ ≤ hthr.εg ∧ 0 ≤ Kint ∧
      Work.BoseRowsFS.RowIntOneRegimeN (h := h) (fc := fc) (fu := fu) H.Ng' R ε₁ Kint)
    (hrow3All : Work.BoseRowQ2.RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu)
      hthr.Ng R hthr.εg) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFSAll v h fc fu K₀ b₀ :=
  exists_honestGateFSAll_of_Ldata R hR hav hv_nonneg hvrad hv_supp hthr H.Ng' H.Ng'_ge
    hrow2L hrow3All

/-- The same for the design's field list verbatim
(`Work.BoseGateAll.HonestInterfaceL`, `Defs.lean` §3), which lacks the continuum
far tail `tailC` of the live interface.  Kept because `Defs.lean` transcribes the
design's statement; for constructive use prefer the `BoseRowsL` form above, whose
`tailL` is accompanied by `tailC` (see the warning in `Defs.lean` §3). -/
theorem exists_honestGateFSAll_of_designInterfaceL
    {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : HonestInterfaceL R hthr)
    (hrow2L : ∃ ε₁ Kint : ℝ, 0 < ε₁ ∧ ε₁ ≤ hthr.εg ∧ 0 ≤ Kint ∧
      Work.BoseRowsFS.RowIntOneRegimeN (h := h) (fc := fc) (fu := fu) H.Ng' R ε₁ Kint)
    (hrow3All : Work.BoseRowQ2.RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu)
      hthr.Ng R hthr.εg) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFSAll v h fc fu K₀ b₀ :=
  exists_honestGateFSAll_of_Ldata R hR hav hv_nonneg hvrad hv_supp hthr H.Ng' H.Ng'_ge
    hrow2L hrow3All

end Work.BoseGateAll
