import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.DLWire.PerBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.DLWire.SmallBox` — FS `thm:smallbox` at Door 4, with the re-wired `m`-arm

**This module is the new home of the DL bundle.**  It used to live in
`Submission/Work/SmallBoxDLBound.lean`; it had to move because the re-wired
`m`-arm field is `Work.DLWire.MGroupData` (FS's simple Bogoliubov payment
`SimpleA2Two E₁ E₂`, from the `Work.MGroupInput` chapter) and
`SmallBoxDLBound.lean` lies *upstream* of that chapter in the import graph:
`Work.SlidingSum` imports `SmallBoxDLBound`, `Work.SmallBoxSliding` imports
`Work.SlidingSum`, and the `MGroupInput` chapter reaches `SmallBoxSliding`
through `Work.DLRepoint.All → UBBChain → UBB.Assembly`.  Hence
`SmallBoxDLBound.lean` cannot import anything that reaches
`Work.MGroupInput.SimpleA2Two`; the bundle lives here instead (same
namespaces, same names: `Submission.BoseGases.DLBoxData`,
`Submission.BoseGases.smallbox_dl_energy_bound`).  See
`Submission/Work/DLWire/README.md`.

STATUS: **PROVED at the faithful energy** (`Work.BlockBound4.diagWeBAt`) with
the *corrected* `m`-arm; no `sorry`, axiom-clean.  The module formalises FS
`final_v2.tex` thm:smallbox (the per-small-box ground-energy lower bound) at
Door 4's faithful word, with all hypotheses explicit.

## FS statement (final_v2.tex ~3907)

Assume `B` is a box with shortest side `λ₁ ≥ μ^{-1/3}`; universal `C, C' > 1`,
`0 < c < 1/2`, with `1 ≤ K_B ≤ C'^{-1}(μa³)^{-1/6}`, the regime
`C'(μa³)^{1/2} ≤ ε_T^{1/2}a(dℓ)^{-1} ≤ a(dsℓ)^{-1}ln(dsℓa^{-1}) ≤ K_B(μa³)^{1/2}`
and `R ≤ K_B^{1/2}(μa³)^{1/4}(μa)^{-1/2}`; then the `n`-particle restriction of
`H_B(μ)` (eq:HBU) satisfies

    H_B(μ) ≥ ( c·(n|B|⁻¹−μ)²/(1+n|B|⁻¹μ⁻¹) − ½μ² )·∬w_{1,B}
              − Cμ²a·((Rλ₁⁻¹)² + K_B³(μa³)^{1/2})·∫χ_B² − Cμa .

The proof is FS's **two-arm split** (`N = m·n′ + n″`):

* the `m` groups of `n′` particles contribute the positive per-group bound
  (`Work.MGroupInput.MGroupWindowCapped`, from FS's *simple* Bogoliubov
  payment `eq:simpleaprioribog` — the corrected input
  `Work.DLWire.MGroupData`, capstone `d4_dl_bound_of_simpleA2Two`);
* the single remainder group contributes the *tight block* shape
  (`Work.DLWire.block_bound_family`, from the delivered, unconditional
  `Work.BlockBound4.diagW_block_bound` — no rung, no input);
* the superadditivity is `Work.KinPSuperadd.diagKinPeBAt_group_superadd` and
  the final convexity is `Submission.BoseGases.two_arm_gain` /
  `two_arm_group_bound` — all inside the capstone.

## The data bundle

`DLBoxData` carries the FS regime fields (`hε`, `hKB`, `hKB1`, `hKBcap`,
`hRcap`, …), the faithful-block data (`hWfin`, `hNewton`, `hD`, `hint`), the
range ordering `R0 ≤ R`, the **regime datum** `hblkMax`
(`Work.DLRepoint.D4Regime` at the single maximal window count `⌊9μs³⌋ - 1`,
transported to every count by the PROVED
`Work.DLRepoint.d4Regime_family_of_max`), and the **corrected `m`-arm input**
`hmgroup : Work.DLWire.MGroupData s μ v h c₀ cgap`.

The latter replaces the field as originally delivered
(`Work.DLRepoint.MGroupInput`), which was **REFUTED** — see
`Submission/Work/DLWire/README.md` §0 and `Work.DLWire.Refuted`.

The `c` of the theorem is FS's `1/18`; the `C` is the block bound's own.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The data of FS `thm:smallbox` at scale `s`, re-pointed to Door 4: the box
side `s`, the chemical potential `μ`, the dilute parameter `ε₀`, the regime
constants `K_B, R`, the potential `v` (with its scattering solution `h` and
range `R0`), the faithful-word data `(Ct, c₀, cgap)`, and all the standing
hypotheses, together with the two per-count inputs the two-arm proof consumes
(`hblkMax`/`hfloor`: the maximal window count's regime datum; `hmgroup`: the
corrected `m`-arm input `Work.DLWire.MGroupData`). -/
structure DLBoxData where
  /-- particle number in the box. -/
  N : ℕ
  /-- box side. -/
  s : ℝ
  /-- chemical potential. -/
  μ : ℝ
  /-- dilute-regime parameter (`μ(av)³ ≤ ε₀`). -/
  ε₀ : ℝ
  /-- regime constant `K_B`. -/
  K_B : ℝ
  /-- regime range constant `R` of the error bracket (FS's potential range). -/
  R : ℝ
  /-- the two-body potential. -/
  v : ℝ³ → ℝ
  /-- the range of `v`. -/
  R0 : ℝ
  /-- D1's Taylor constant (`eq:appbogolubov`). -/
  Ct : ℝ
  /-- FS's spectral threshold `(dsℓ)^{-1}`. -/
  c₀ : ℝ
  /-- FS's `ε_T`-gap constant of `eq:appTB`. -/
  cgap : ℝ
  /-- the scattering solution of `v`. -/
  h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v
  hs : 0 < s
  hμ : 0 < μ
  hv_nonneg : 0 ≤ v
  hvrad : IsRadial v
  hv_memL1 : MemLp v 1
  hR0 : 0 < R0
  hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0
  hsR : R0 ≤ s * chiR0
  hε : μ * (a v) ^ 3 ≤ ε₀
  hKB : 0 < K_B
  /-- shortest-side hypothesis `s ≥ μ^{-1/3}` ⟺ `1 ≤ μ·s³`. -/
  hμs : 1 ≤ μ * s ^ 3
  /-- FS's lower regime bound `1 ≤ K_B`. -/
  hKB1 : 1 ≤ K_B
  /-- regime cap `K_B³(μ(av)³)^{1/2} ≤ 1` — FS's `K_B ≤ C'⁻¹(μa³)^{-1/6}`
  cubed, at the (universal) constant `C' = 1`. -/
  hKBcap : K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 1
  /-- regime cap `(R/s)² ≤ K_B³(μ(av)³)^{1/2}` (FS `eq:appRassumption`). -/
  hRcap : (R / s) ^ 2 ≤ K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
  /-- **the range ordering** `R0 ≤ R` (FS's `R` is the potential range; free). -/
  hR0R : R0 ≤ R
  hCt : 0 ≤ Ct
  /-- the spectral threshold is positive. -/
  hc0 : 0 < c₀
  /-- the scattering length is positive. -/
  hav : 0 < a v
  /-- D1's dilute regime `2·c₀·(a v) ≤ 1`. -/
  hdil : 2 * c₀ * (a v) ≤ 1
  /-- the `ε_T`-gap constant is nonnegative. -/
  hcgap0 : 0 ≤ cgap
  /-- D1's finiteness input (the Newtonian energy of `g₀ v h`). -/
  hWfin : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
    wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹)
  /-- D1's sharp-mass (M1) input, with the Taylor constant `Ct`. -/
  hNewton : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
      ((FourierTransform.fourier (fun x : ℝ³ => (wScaled s (g0 v h) x : ℂ))
          (((2 * Real.pi)⁻¹) • q)).re) ^ 2 / ‖q‖ ^ 2
    ≤ 2 * (1 + 6 * Ct * (R0 / s) ^ 2) * g0w0Mass (v := v) h
  /-- the `g₀`-mass bound (`SmallBoxA0.g0w0Mass_le_av`-shape). -/
  hD : g0w0Mass (v := v) h ≤ 8 * π * (a v)
  /-- the `p`-integrability input of the faithful word (`Door4Superadd`'s
  hypothesis). -/
  hint : Work.BlockBound4.DiagWKinIntegrable s c₀
  /-- **the regime datum** (FS's `eq:appdellsassumption` as a finite parameter
  regime): the count-`n` regime fields at the MAXIMAL window count
  `⌊9μs³⌋ - 1`.  The transport to every window count below is the PROVED
  `Work.DLRepoint.d4Regime_family_of_max`; its `hchi` and `hcgap` fields are
  the capstone's diluteness `hgap` and gap `hcgap`. -/
  hblkMax : Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v
    (Nat.floor (9 * μ * s ^ 3) - 1)
  /-- the maximal window count is a genuine count. -/
  hfloor : 1 ≤ Nat.floor (9 * μ * s ^ 3)
  /-- **the corrected `m`-arm input** (FS's *simple* Bogoliubov payment
  `eq:simpleaprioribog`, with the count-linear constant `E₁` and the
  `n₊`-coefficient `E₂` split, plus its regime data).  This replaces the
  REFUTED bare `Work.DLRepoint.MGroupInput`. -/
  hmgroup : Work.DLWire.MGroupData s μ v h c₀ cgap

/-- **FS thm:smallbox at scale `s` (corpus form) AT DOOR 4's faithful energy.**

There are universal constants `0 < c < 1/2` (viz. `1/18`) and `0 ≤ C` (the
faithful block bound's own) such that for EVERY box of side `s ≥ μ^{-1/3}` in
the smallbox regime the per-box faithful ground energy satisfies

    diagWeBAt N … ≥ ( c·((N̂/s³)−μ)²/(1+(N̂/s³)/μ) − ½μ² )·(8π(a v)·s³)
        − C·μ²(a v)·((R/s)² + K_B³(μ(a v)³)^{1/2})·s³ − C·μ(a v) .

**Fidelity.**  As in the corpus's statement (Session-267): `c` and `C` are
chosen ONCE, outside the data quantification, so the bound is uniform in `N`
and in the data — exactly what the a-priori assembly
(`thm:aprioriHLambda`, summing the per-box bounds over the `u`-boxes) needs.
The `∃c` (rather than one fixed `c`) is FS's `∃c ∃C` verbatim.

**Proof.**  The `n″`-arm is `Work.DLWire.block_bound_family` (the delivered
tight block bound, in the DL error shape `Γ`, at every window count); the
`m`-arm slot is the corrected input's capstone
`Work.DLWire.d4_dl_bound_of_mGroupData` (= `d4_dl_bound_of_simpleA2Two` with
the bundle vocabulary), whose body is the windowed two-arm assembly with the
grouping `Work.KinPSuperadd.diagKinPeBAt_group_superadd` and the unchanged
two-arm arithmetic. -/
theorem smallbox_dl_energy_bound :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ D : DLBoxData,
          (c * ((((D.N : ℝ) / D.s ^ 3) - D.μ) ^ 2 / (1 + ((D.N : ℝ) / D.s ^ 3) / D.μ))
              - (1 / 2) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
            - C * D.μ ^ 2 * (a D.v)
                * ((D.R / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ)) * D.s ^ 3
            - C * D.μ * (a D.v)
          ≤ Work.BlockBound4.diagWeBAt D.N D.s D.μ D.v D.h D.c₀ D.cgap := by
  -- one universal `Cb` for BOTH the `n″`-arm and the theorem's error constant
  obtain ⟨Cb, hCb0, hblkRaw⟩ := Work.BlockBound4.diagW_block_bound
  refine ⟨1 / 18, by norm_num, by norm_num, Cb, hCb0, ?_⟩
  intro D
  -- the `n″`-arm at every window count, in the DL error shape `Γ`
  have hblk := Work.DLWire.block_bound_family_of (s := D.s) (μ := D.μ) (R0 := D.R0)
    (R := D.R) (K_B := D.K_B) (Ct := D.Ct) (c₀ := D.c₀) (cgap := D.cgap) (Cb := Cb)
    (v := D.v) (h := D.h) hCb0
    (fun n hwin reg => hblkRaw (Work.DLRepoint.mkBlockData D.s D.μ D.R0 D.K_B D.Ct D.c₀
      D.cgap D.v D.h n D.hs D.hμ D.hv_nonneg D.hvrad D.hv_memL1 D.hR0 D.hv_supp D.hsR D.hμs
      D.hKB D.hCt D.hc0 D.hav D.hdil D.hWfin D.hNewton D.hD hwin reg))
    D.hs D.hav D.hR0 D.hR0R D.hc0 D.hdil D.hblkMax D.hfloor
  have hzero : (0 : ℝ) ≤ Work.BlockBound4.diagWeBAt 0 D.s D.μ D.v D.h D.c₀ D.cgap :=
    Work.DLRepoint.diagWeBAt_zero_nonneg D.s D.μ D.v D.h D.c₀ D.cgap D.hs
  -- the capstone: the corrected `m`-arm + the `n″`-arm + the grouping
  have hmain := Work.DLWire.d4_dl_bound_of_mGroupData (s := D.s) (μ := D.μ) (R0 := D.R0)
    (R := D.R) (K_B := D.K_B) (Ct := D.Ct) (v := D.v) (h := D.h) (c₀ := D.c₀)
    (cgap := D.cgap) (Cb := Cb) (n := Nat.floor (9 * D.μ * D.s ^ 3) - 1)
    D.hs D.hμ D.hμs D.hav D.hR0 D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.hsR D.hR0R D.hKB
    hCb0 D.hcgap0 D.hint D.hblkMax D.hmgroup hblk hzero D.N
  simp only [Work.DLRepoint.d4GammaWith] at hmain
  linarith [hmain]

/-! ## The `m`-arm fields at the bundle level (projections)

The corrected `m`-arm datum is the bundle field `hmgroup : Work.DLWire.MGroupData`,
whose fields are exactly the capstone's bundle-level hypotheses; these
projections expose them at the bundle level so that a caller never has to reach
through `D.hmgroup`. -/

namespace DLBoxData

/-- The bundle's error constant `E₁` of the simple Bogoliubov payment. -/
abbrev E₁ (D : DLBoxData) : ℝ := D.hmgroup.E₁

/-- The bundle's `n₊`-coefficient `E₂`. -/
abbrev E₂ (D : DLBoxData) : ℝ := D.hmgroup.E₂

/-- The bundle's `SimpleA2Two` datum (FS `eq:simpleaprioribog` at the faithful
word, with the error constants split). -/
theorem simpleA2Two (D : DLBoxData) :
    Work.MGroupInput.SimpleA2Two D.E₁ D.E₂ D.s D.c₀ D.v D.h := D.hmgroup.hA2

/-- The `cgap`-absorption of the `n₊`-coefficient. -/
theorem hab (D : DLBoxData) (P : ℕ) (hP : 1 ≤ P) (hwin : (P : ℝ) / D.s ^ 3 ≤ 9 * D.μ) :
    Work.SmallBoxA0.totNCoeff D.s D.μ D.v + D.E₂ * (a D.v) * (((P : ℝ) + 1) / D.s ^ 3)
      ≤ D.cgap :=
  D.hmgroup.hab P hP hwin

/-- The corpus's `CorrWord` bound at the block window. -/
theorem hcorr (D : DLBoxData) (P : ℕ) (Φ : X P → ℝ) (hP : 1 ≤ P) (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox P D.s, (Φ x) ^ 2) = 1) (hwin : (P : ℝ) / D.s ^ 3 ≤ 9 * D.μ)
    (hpos : 0 < cS1 D.s Φ) :
    2 * (D.s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord D.s D.h Φ
      ≤ (1 / (72 * D.s ^ 2)) * cnPlus D.s Φ + 36 * π * (a D.v) * D.μ :=
  D.hmgroup.hcorr P Φ hP hΦc hnorm hwin hpos

/-- The bundle's regime datum `10 ≤ μs³`. -/
theorem hs10 (D : DLBoxData) : 10 ≤ D.μ * D.s ^ 3 := D.hmgroup.hμs10

/-- The `m`-arm's window bound `E₁ ≤ μ`. -/
theorem hE₁μ (D : DLBoxData) : D.E₁ ≤ D.μ := D.hmgroup.hE₁μ

/-- The `m`-arm's capstone at the bundle: the DL two-arm shape from the
bundle's own data, the `n″`-arm `hblk` and the empty box. -/
theorem d4_bound (D : DLBoxData) {R : ℝ} (hR0R : D.R0 ≤ R) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hblk : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / D.s ^ 3 ≤ 9 * D.μ →
      ((1 / 4 : ℝ) * ((P : ℝ) / D.s ^ 3 - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
          * (8 * π * (a D.v) * D.s ^ 3)
        - Cb * D.μ ^ 2 * (a D.v) * D.s ^ 3 * Work.DLRepoint.d4GammaWith R D.s D.K_B D.μ D.v
        - Cb * D.μ * (a D.v)
      ≤ Work.BlockBound4.diagWeBAt P D.s D.μ D.v D.h D.c₀ D.cgap)
    (hzero : 0 ≤ Work.BlockBound4.diagWeBAt 0 D.s D.μ D.v D.h D.c₀ D.cgap) :
    ((1 / 18 : ℝ) * (((D.N : ℝ) / D.s ^ 3 - D.μ) ^ 2 / (1 + ((D.N : ℝ) / D.s ^ 3) / D.μ))
        - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
      - Cb * D.μ ^ 2 * (a D.v) * D.s ^ 3 * Work.DLRepoint.d4GammaWith R D.s D.K_B D.μ D.v
      - Cb * D.μ * (a D.v)
    ≤ Work.BlockBound4.diagWeBAt D.N D.s D.μ D.v D.h D.c₀ D.cgap :=
  Work.DLWire.d4_dl_bound_of_mGroupData (s := D.s) (μ := D.μ) (R0 := D.R0) (R := R)
    (K_B := D.K_B) (Ct := D.Ct) (v := D.v) (h := D.h) (c₀ := D.c₀) (cgap := D.cgap)
    (Cb := Cb) (n := Nat.floor (9 * D.μ * D.s ^ 3) - 1) D.hs D.hμ D.hμs D.hav D.hR0
    D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.hsR hR0R D.hKB hCb D.hcgap0 D.hint D.hblkMax
    D.hmgroup hblk hzero D.N

end DLBoxData

/-! ## Corollaries: the bundle at another count -/

/-- Re-base a DL bundle at another particle count.  Every field of `DLBoxData`
except `N` is count-independent (`hblkMax`/`hfloor` live at the maximal window
count; `hmgroup` is the shared `m`-arm datum), so this is a pure re-packaging —
and it is what lets the per-box bound be applied at the count a *consumer*
needs (the sliding chain's box count, not the bundle's). -/
def DLBoxData.rebase (D : DLBoxData) (N : ℕ) : DLBoxData := { D with N := N }

@[simp] lemma DLBoxData.rebase_N (D : DLBoxData) (N : ℕ) : (D.rebase N).N = N := rfl

/-- **The DL bound at every particle count**: the same `c, C` work for the
re-based bundle, i.e. the per-box lower bound is available at every count `P`
in the block window, not only at the bundle's own `N`.  (The window hypotheses
are carried so that a caller can pipe its block-window data through; the DL
bound itself holds at every count.) -/
theorem smallbox_dl_energy_bound_at_count :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (D : DLBoxData) (P : ℕ), 1 ≤ P → (P : ℝ) / D.s ^ 3 ≤ 9 * D.μ →
          (c * ((((P : ℝ) / D.s ^ 3) - D.μ) ^ 2 / (1 + ((P : ℝ) / D.s ^ 3) / D.μ))
              - (1 / 2) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
            - C * D.μ ^ 2 * (a D.v)
                * ((D.R / D.s) ^ 2 + D.K_B ^ 3 * (D.μ * (a D.v) ^ 3) ^ (1 / 2 : ℝ)) * D.s ^ 3
            - C * D.μ * (a D.v)
          ≤ Work.BlockBound4.diagWeBAt P D.s D.μ D.v D.h D.c₀ D.cgap := by
  obtain ⟨c, hc0, hc1, C, hC0, hb⟩ := smallbox_dl_energy_bound
  exact ⟨c, hc0, hc1, C, hC0, fun D P _hP _hwin => hb (D.rebase P)⟩

end BoseGases

end Submission
