import ChallengeDeps
import Submission.Work.MGroupInput.D4BoundOfSimpleA2Two
import Submission.Work.MGroupInput.qLHSword_one_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.DLWire` — the re-wiring of the DL bundle's `m`-arm

**Assignment.** Replace the DL bundle's `m`-arm field.  The field as delivered
(`Submission.BoseGases.DLBoxData.hmgroup`, of type `Work.DLRepoint.MGroupInput`)
is the *bare* FS `m`-arm at the group window `u = n′/s³ ≥ 2μ`, and it is
**REFUTED** (`Work.MGroupInput.NoGo.not_mgroupInput`, `diagWeBAt_one_le`,
`diagWeBAt_two_le`, `v_integral_lower_of_groupBound`): FS's `m`-arm needs the
window constant `C_n` LARGE (`final_v2.tex` l. 4004, *"if we choose the constant
`C_n` large enough"*), while `Submission.BoseGases.exists_two_arm_split` fixes
`C_n = 2`.  See `README.md` §0 for the record of the refutation and of the
windowed repair.

The corrected route is PROVED in `Work.MGroupInput` through to the capstone
`Work.MGroupInput.d4_dl_bound_of_simpleA2Two`, whose bundle-level hypotheses are

* `SimpleA2Two E₁ E₂` — FS's *simple* Bogoliubov payment
  (`eq:simpleaprioribog`) at the faithful word, with the count-linear constant
  `E₁` and the `n₊`-coefficient `E₂` split (PROVED from the corpus's sharp
  kernel comparison `wScaled_g0_sharp_ae` + `diagW_simpleA2_two`, with the
  residual `SimpleA2Small` closed for large boxes by
  `Work.MGroupInput.simpleA2Small_of_large_box`);
* `0 ≤ E₁`, `E₁ ≤ μ` (the `m`-arm's window constant `7 + E₁/μ ≤ 8`),
* the `cgap`-absorption `hab` (`totNCoeff + E₂(av)((P+1)/s³) ≤ cgap` on the
  block window), the diluteness `hgap` (`D4Regime.hchi`), the `CorrWord` bound
  `hcorr`, the gap `hcgap` (`D4Regime.hcgap`), and the regime `10 ≤ μs³`.

This module fixes **the corrected input** as one structure, `MGroupData`, and
gives the capstone at that vocabulary (`d4_dl_bound_of_mGroupData`); the DL
bundle's `hmgroup` field is this structure (see
`Submission/Work/SmallBoxDLBound.lean`).

## Interface

| name | meaning |
|---|---|
| `MGroupData s μ v h c₀ cgap` | **the corrected `m`-arm input** (the capstone's bundle-level hypotheses) |
| `mGroupData_of_hyp` | the capstone's hypothesis list, bundled |
| `d4_dl_bound_of_mGroupData` | **the capstone** `d4_dl_bound_of_simpleA2Two` at this vocabulary (the regime slot `D4Regime` supplies `hgap`/`hcgap`) |
| `MGroupData.of_simpleA2Small` | **derivability**: the chapter's PROVED `SimpleA2Small` (large boxes, dilute potentials) plus the regime conditions give the input |
| `mGroupData_nonempty_of_simpleA2Small` | the same, as an inhabitant |
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.DLWire

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1  The corrected `m`-arm input -/

/-- **The corrected `m`-arm input** — FS's *simple* per-group Bogoliubov payment
(`eq:simpleaprioribog`) with the two error constants split, plus the regime data
the assembly consumes.  These are exactly the bundle-level hypotheses of the
PROVED capstone `Work.MGroupInput.d4_dl_bound_of_simpleA2Two`:

* `hA2` — `SimpleA2Two E₁ E₂`: the simple payment
  `pDiagForm + q4PairWord ≥ −½((1+1/20)ĝω(0) + (1/20)a)·d4MassCoeff
   − E₁(av)(N+1) − E₂(av)((N+2)/s³)·n₊`;
* `hE₁`, `hE₂`, `hE₁μ` — the constants' signs and the window bound
  `E₁ ≤ μ` (so that the per-state window `7μ + E₁ ≤ 8μ` fits the corpus's
  block window `u ≤ 9μ`);
* `hμs10` — the regime `10 ≤ μs³` (the count-independent error budget of the
  sharp chain; see `Work.MGroupInput/README.md` §§4.1–4.2);
* `hab` — the `cgap`-absorption of the `n₊`-coefficient `E₂`;
* `hcorr` — the corpus's `CorrWord` bound at the block window.

The diluteness `hgap` (`(μ(av)s²)(1600+1850χ²) ≤ 1`) and the gap
`hcgap` (`1/(36s²) ≤ cgap`) are `Work.DLRepoint.D4Regime` fields (`hchi`,
`hcgap`) and are supplied by the bundle's regime datum. -/
structure MGroupData (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) where
  /-- the `m`-arm's count-linear error constant. -/
  E₁ : ℝ
  /-- the `m`-arm's `n₊`-coefficient. -/
  E₂ : ℝ
  hE₁ : 0 ≤ E₁
  hE₂ : 0 ≤ E₂
  /-- the window bound `E₁ ≤ μ` (the `m`-arm's window constant is `7 + E₁/μ ≤ 8`). -/
  hE₁μ : E₁ ≤ μ
  /-- **the regime datum** `10 ≤ μs³` (the count-independent error budget). -/
  hμs10 : 10 ≤ μ * s ^ 3
  /-- **FS's simple Bogoliubov payment** (`eq:simpleaprioribog`) at the faithful word. -/
  hA2 : Work.MGroupInput.SimpleA2Two E₁ E₂ s c₀ v h
  /-- the `cgap`-absorption of the `n₊`-coefficient on the block window. -/
  hab : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
    Work.SmallBoxA0.totNCoeff s μ v + E₂ * (a v) * (((P : ℝ) + 1) / s ^ 3) ≤ cgap
  /-- the corpus's `CorrWord` bound at the block window (the `cS1 > 0` branch). -/
  hcorr : ∀ (P : ℕ) (Φ : X P → ℝ), 1 ≤ P → ContDiff ℝ ∞ Φ →
    (∫ x in abox P s, (Φ x) ^ 2) = 1 → (P : ℝ) / s ^ 3 ≤ 9 * μ → 0 < cS1 s Φ →
    2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
      ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ

/-- **The capstone's hypothesis list, bundled**: the individual hypotheses of
`Work.MGroupInput.d4_dl_bound_of_simpleA2Two` give an `MGroupData`. -/
def mGroupData_of_hyp {s μ c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} (E₁ E₂ : ℝ)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hE₁μ : E₁ ≤ μ) (hμs10 : 10 ≤ μ * s ^ 3)
    (hA2 : Work.MGroupInput.SimpleA2Two E₁ E₂ s c₀ v h)
    (hab : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      Work.SmallBoxA0.totNCoeff s μ v + E₂ * (a v) * (((P : ℝ) + 1) / s ^ 3) ≤ cgap)
    (hcorr : ∀ (P : ℕ) (Φ : X P → ℝ), 1 ≤ P → ContDiff ℝ ∞ Φ →
      (∫ x in abox P s, (Φ x) ^ 2) = 1 → (P : ℝ) / s ^ 3 ≤ 9 * μ → 0 < cS1 s Φ →
      2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ) :
    MGroupData s μ v h c₀ cgap :=
  ⟨E₁, E₂, hE₁, hE₂, hE₁μ, hμs10, hA2, hab, hcorr⟩

/-- The diluteness input `hgap` of the capstone **is** `D4Regime.hchi`. -/
theorem D4Regime.hgap {s μ R0 K_B Ct c₀ cgap : ℝ} {v : ℝ³ → ℝ} {n : ℕ}
    (reg : Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v n) :
    (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1 :=
  reg.hchi

/-! ## 2  The capstone at the corrected vocabulary -/

/-- **The DL two-arm shape from the corrected `m`-arm input**: the capstone
`Work.MGroupInput.d4_dl_bound_of_simpleA2Two` with its bundle-level hypotheses
packaged as `MGroupData` and its two regime fields (`hcgap`, `hgap`) read off a
`Work.DLRepoint.D4Regime`.  This is the lemma the re-wired DL bundle
(`Submission.BoseGases.smallbox_dl_energy_bound`) calls in its `m`-arm slot. -/
theorem d4_dl_bound_of_mGroupData {s μ R0 R K_B Ct : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap Cb : ℝ} {n : ℕ}
    (hs : 0 < s) (hμ : 0 < μ) (hμβ : 1 ≤ μ * s ^ 3) (hav : 0 < a v)
    (hR0 : 0 < R0) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0s : R0 ≤ s * chiR0) (hR0R : R0 ≤ R)
    (hKB : 0 < K_B) (hCb : 0 ≤ Cb) (hcgap0 : 0 ≤ cgap)
    (hint : Work.BlockBound4.DiagWKinIntegrable s c₀)
    (reg : Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v n)
    (hM : MGroupData s μ v h c₀ cgap)
    (hblk : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      ((1 / 4 : ℝ) * ((P : ℝ) / s ^ 3 - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
        - Cb * μ ^ 2 * (a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
        - Cb * μ * (a v)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap)
    (hzero : 0 ≤ Work.BlockBound4.diagWeBAt 0 s μ v h c₀ cgap)
    (N : ℕ) :
    ((1 / 18 : ℝ) * (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + ((N : ℝ) / s ^ 3) / μ))
        - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (a v) * s ^ 3)
      - Cb * μ ^ 2 * (a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
      - Cb * μ * (a v)
    ≤ Work.BlockBound4.diagWeBAt N s μ v h c₀ cgap :=
  Work.MGroupInput.d4_dl_bound_of_simpleA2Two (E₁ := hM.E₁) (E₂ := hM.E₂) hs hμ hμβ hav
    hR0 hv_nonneg hvrad hv_memL1 hv_supp hR0s hR0R hKB hCb hcgap0 hint hM.hμs10 reg.hcgap
    hM.hE₁ hM.hE₁μ hM.hA2 hM.hab reg.hchi hM.hcorr hblk hzero N

/-! ## 3  Derivability of the corrected input

The corrected input is **not** a new named input in the sense of the refuted
one: `Work.MGroupInput.SimpleA2Small` — FS's `eq:simpleaprioribog` with the
count-linear constant arbitrarily small — is *PROVED* for large boxes and
dilute potentials (`Work.MGroupInput.simpleA2Small_of_large_box`), and it gives
`SimpleA2Two E₁ E₂` with `E₁ ≤ μ/10` (take the chapter's `ε := μ/10`).  What is
left is the regime data (`E₂` small enough for `hab`, the `CorrWord` bound, the
`μs³ ≥ 10` regime), recorded as fields. -/

/-- **Non-vacuity / derivability of the corrected input**: in the large-box,
dilute-potential regime the chapter's PROVED `SimpleA2Small` inhabits
`MGroupData` (given the two count-regime conditions).  The chapter's
`ε`-freedom is used at `ε := μ/10`, so the produced `E₁` obeys `E₁ ≤ μ`. -/
theorem mGroupData_nonempty_of_simpleA2Small {s μ c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hμ : 0 < μ) (hμs10 : 10 ≤ μ * s ^ 3)
    (hsmall : Work.MGroupInput.SimpleA2Small s c₀ v h)
    (hab : ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → E₁ ≤ μ → Work.MGroupInput.SimpleA2Two E₁ E₂ s c₀ v h →
      ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
        Work.SmallBoxA0.totNCoeff s μ v + E₂ * (a v) * (((P : ℝ) + 1) / s ^ 3) ≤ cgap)
    (hcorr : ∀ (P : ℕ) (Φ : X P → ℝ), 1 ≤ P → ContDiff ℝ ∞ Φ →
      (∫ x in abox P s, (Φ x) ^ 2) = 1 → (P : ℝ) / s ^ 3 ≤ 9 * μ → 0 < cS1 s Φ →
      2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ) :
    Nonempty (MGroupData s μ v h c₀ cgap) := by
  obtain ⟨E₁, E₂, hE₁, hE₁ε, hE₂, hA2⟩ := hsmall (μ / 10) (by positivity)
  have hE₁μ : E₁ ≤ μ := by linarith
  exact ⟨mGroupData_of_hyp E₁ E₂ hE₁ hE₂ hE₁μ hμs10 hA2 (hab E₁ E₂ hE₁ hE₁μ hA2) hcorr⟩

/-- The corrected input, unpacked from its non-vacuity statement (a
`Classical.choice` on the Prop-valued `Nonempty`; the data `E₁, E₂` are not
computable from the hypotheses, which is exactly why the input is carried as
bundle data). -/
noncomputable def MGroupData.of_simpleA2Small {s μ c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hμ : 0 < μ) (hμs10 : 10 ≤ μ * s ^ 3)
    (hsmall : Work.MGroupInput.SimpleA2Small s c₀ v h)
    (hab : ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → E₁ ≤ μ → Work.MGroupInput.SimpleA2Two E₁ E₂ s c₀ v h →
      ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
        Work.SmallBoxA0.totNCoeff s μ v + E₂ * (a v) * (((P : ℝ) + 1) / s ^ 3) ≤ cgap)
    (hcorr : ∀ (P : ℕ) (Φ : X P → ℝ), 1 ≤ P → ContDiff ℝ ∞ Φ →
      (∫ x in abox P s, (Φ x) ^ 2) = 1 → (P : ℝ) / s ^ 3 ≤ 9 * μ → 0 < cS1 s Φ →
      2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ) :
    MGroupData s μ v h c₀ cgap :=
  Classical.choice (mGroupData_nonempty_of_simpleA2Small hμ hμs10 hsmall hab hcorr)

end Work.DLWire
