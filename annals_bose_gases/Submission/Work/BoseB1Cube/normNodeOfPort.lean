import ChallengeDeps
import Submission.Work.BoseB1Cube.LargeWinNode
import Submission.Work.BoseB1Cube.SmallWinNode
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- **FS's `n'`-group (linear, error-free) row at `bI = 1`, through the PROVED port rung
`Work.BoseB1Cube.sbWordCube_ge_payPortR3` — NOT through `SharpRow2`.**

`Work.BoseB1Cube.NormNode v h R` (`nomRowLinWindowRow.lean:170`) is piece C of the nominal route at
normalised states, and `Work.BoseB1Cube.nomRowLinWindowRow_of_normNode` (PROVED) turns it into
`NomRowLinWindowRow` (piece C), hence (with the PROVED pieces A = `nomRowSqWindowRow`,
B = `nomRowArbState` and the assembly `nominalPerBoxRow_of_AC`) into `PerBoxFNomSlots`, hence
(PROVED `cubeCrudeBand_of_perBoxFNomSlots`, `countWindow_of_perBoxFNomSlots`,
`nodeB1B_of_perBoxFNomMu`) into `Work.BoseB1Cube.cubeCrudeBand_holds` and into the root's `hB1`.

PROOF ROUTE (no new analysis; every input is a PROVED corpus lemma).  With
`V = bV, W = bW, χ = chiMass, Γ = PBΓ, G = g0w0Mass, S = boxFlatCount, q = boxQCount = n₊,
Pc = boxPairCount, c = sbCut, τ = n/V`, the PROVED rung gives, **at its own `(κ,C)`, which are
extracted inside the proof** (`obtain ⟨ε₀P, κ, C, 0 ≤ κ, 0 ≤ C, hrung⟩ :=
sbWordCube_ge_payPortR3 …`; once extracted they are ordinary terms),

    payPortR3Lower(κ,C) ≤ sbWordCube ,
    payPortR3Lower(κ,C) = a0MainLocBox(V,μ,W,S) + ½((M₂−W)/V²)·Pc
        + (bGapCoeff − C a(μ+S/V) − C a(μ+n/V))·n₊
        − ½(1+κΓ)·G·((n+1)n/V²)·χ − C·a·c³·(n/V)·χ .

⚠ **`payPortR3Lower` is ANTITONE in `C`** (`payPortR3Lower_mono_C`), so one must NOT try to work at
`(0,0)`: the goal is `demand ≤ payPortR3Lower(κ,C)` **for the extracted `(κ,C)`**, and the
`κ`/`C`-rows are paid as follows — this is the whole point of extracting them second:

* the two credit Q-rows `C a(μ+S/V)q`, `C a(μ+τ)q` are paid by the **free gate column**
  `bGapCoeff·Q ≥ K·aμ·qV` with `K` chosen *after* extraction, e.g. `K := 4CCₙ` (legitimate: the
  gate `PerBoxGapAbsorbB1 v h hav K` gives its own `∃ε₀(K)`, and every other threshold is also
  tuned after extraction);
* the band row `C a c³ τ χ` by `c³ ≤ μΓ` (`sbCut_cube_eq` + diluteness) and then either the gate
  column or the flat slack, with the diluteness gate `Γ ≤ ε(a, C, Cₙ)` (`PBGamma_le_of_dilute`,
  any prescribed bound — so κ-dependent choices are fine);
* the mass row `½(1+κΓ)G((n+1)n/V²)χ` by the pair square via the PROVED `ledger_crux`
  (`hypothesis (1−2Γ)Gχ ≤ M₂−W`, supplied by `boxM2_sub_w1MassB_ge_of_windowDichotomy`, branch 2 of
  the PROVED `windowShiftDichotomy`), leaving
  `T4 = [(2+κ)ΓGχn² + 2GχnQ + 2Gχn + κΓGχn]/(2V²)`, whose `n²`-piece is
  `≤ (2+κ)Γ(M₂−W)τ²/(2(1−2Γ)) ≤ (2+κ)ΓWτ²/(2(1−2Γ))` by the PROVED `boxM2_le_two_mul_boxM1`
  (`M₂ ≤ 2W`) — a fixed multiple of `ΓWτ²`, killed by the diluteness gate `Γ ≤ 1/(4(2+κ))`;
* the demand `(1/18)μτWI`: its `q`-part by the gate column (`W ≤ 16πaχ ≤ 16πaCsV`,
  `w1MassB_le_sharp`), its `σ`-part by `a0MainLocBox ≥ W(¼(σ−μ)² − ½μ² − O(μ/V))`, i.e. by the
  elementary flat comparison `1/(18t) + Γ/(1−2Γ) ≤ ¼(1−1/t)² − 1/(2t²)` at `t = τ/μ ≥ Cₙ ≥ 4`
  (true for `Γ ≤ 0.08` at `Cₙ = 4`, and monotone-favourable in `t`);
* the small-window branch of the PROVED `windowShiftDichotomy` (`μ·bW ≤ a v`) is PROVED outright as
  `Work.BoseB1Cube.sbWordCube_ge_crudeSmallWin`;
* all residual terms are `O(Wμ/V)`, `O(W/V²)`, absorbable since `1 ≤ μV` (`one_le_mu_boxMassGood`)
  and `μ(a v)³ ≤ ε₀`; the degenerate cases `n = 0` and `bI = 0` are as in `nomRowI_one`'s tail.

See `Submission/Work/BoseB1Cube/FINDING_cubeCrudeBand_session6.md` §3.2 (and the ⭐ there) for the
full ledger.  Do NOT route this through `SharpRow2`: that statement is strictly stronger (it needs a
*lower* bound on the *sharp* rung's left-hand side, which no upper-bound rung can supply —
`FINDING_sharpRow2Holds_session1.md` §0), whereas the node only needs `demand ≤ sbWordCube`, which
the port rung supplies directly. -/
theorem normNodeOfPort {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseB1Cube.NormNode v h R := by
  intro Cn hCn
  obtain ⟨εs, hεs, hS⟩ := Work.BoseB1Cube.SmallWinNode (v := v) h hv hv1 hvrad hR hv_supp hav Cn hCn
  obtain ⟨εl, hεl, hL⟩ := Work.BoseB1Cube.LargeWinNode (v := v) h hv hv1 hvrad hR hv_supp hav Cn hCn
  refine ⟨min εs εl, lt_min hεs hεl, ?_⟩
  intro μ hAdm n Ψ u hu hΨ hsupp hI hnlo hnhi
  by_cases hw : μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v
  · exact hS μ (Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)) n Ψ u hu hw hΨ hsupp hI hnlo hnhi
  · exact hL μ (Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)) n Ψ u hu hw hΨ hsupp hI hnlo hnhi

end Work.BoseB1Cube
