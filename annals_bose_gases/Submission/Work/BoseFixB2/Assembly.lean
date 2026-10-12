import ChallengeDeps
import Submission.Work.BoseFixB2.Band.dk_gradeA_eq_zero
import Submission.Work.BoseFixB2.DvApriori.dOne_dTwo_le
import Submission.Work.BoseFixB2.Energy.qform_gradeA_eq
import Submission.Work.BoseFixB2.Recomb.recomb_clause
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Assembly` — node D4 (`b2GradingDataB_holds`) assembled

**COMPLETE and sorry-free** (2026-10-03, curric-46).  This file assembles FS §6
(`lem:LocMatrices`, `final_v2.tex` ll. 1365–1445) from the child lemmas of the
subproject — all of them proved, `#print axioms =
[propext, Classical.choice, Quot.sound]`:

| clause | file |
|---|---|
| energy identity `⟨ψ,𝒜ψ⟩‖Φ‖² = ⟨Φ,HΦ⟩` | `Energy/qform_gradeA_eq` |
| band `d_k = 0` (`k ≥ 3`) | `Band/dk_gradeA_eq_zero` |
| recombination (`lem:LocMatrices` output) | `Recomb/recomb_clause` |
| `eq:dvapriori` `\|d₁\|+\|d₂\| ≤ Kμ²ℓ³` | `DvApriori/dOne_dTwo_le` |
| the `d₁`,`d₂` identification | `DvApriori/dk_gradeA_one_two` |
| support / Hermitian / profile support | `Energy/gradeA_support_herm` |
| `‖ψ‖² = 1` | `Energy/normSq_gradePsi` |
| `𝓜 ≥ 8` for small diluteness | `Arith/bigM_ge_eight` |

The §5 input is the frozen `Work.BoseBoxFix.NodeB1B v h J`, whose **first**
conjunct is FS `eq:apriorinn+`'s particle-number window — the only a-priori input
§6 consumes (FS: "Due to our assumptions they, in particular, imply that
`n ≤ Cμℓ³`").  The lead wires `NodeB1B` from subproject `BoseFixB1`.

See `PLAN.md` for the design, in particular the **polarisation trap**: the
parallelogram identity + 2-homogeneity alone do *not* give bilinearity of the
polar form in Lean's foundations (non-zero derivations of `ℝ` exist with choice);
the repair used here is `Polar/polarForm_add` (additivity from the parallelogram
identity alone) plus `Polar/polarisation_of_continuous` (scalar homogeneity from
continuity in the scalar) fed by `Polar/boxFormB_continuous_smul`.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB2

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3
open Work.BoseFixB2.Arith Work.BoseFixB2.Energy Work.BoseFixB2.Band Work.BoseFixB2.Recomb Work.BoseFixB2.DvApriori

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **FS §6 `lem:LocMatrices`** in its corrected form (`B2GradingDataB`), from FS's standing
assumptions on `v` and the §5 node `NodeB1B` (the a-priori particle window).

The data produced for a low state `Φ` of the box `Λ = acube ℓ` (`ℓ = sideAt μ (a v)`):

* `nn = fsNn v μ n = max (n+1) ⌈𝓜/4⌉₊`, `Mw = fsRmw v μ = ⌈𝓜/4⌉₊ + 1` (so that
  `𝓜/4 ≤ Mw ≤ 𝓜/2` and `Mw ≤ nn` as soon as `Adm` forces `𝓜 ≥ 8`);
* `A = gradeA v h μ n ℓ Φ`, FS's matrix `𝒜_{ij} = ⟨1_{n₊=i}Φ, H_Λ1_{n₊=j}Φ⟩/(‖·‖‖·‖)`
  (zero when a sector norm vanishes, FS's convention), built from the polarised box word
  `polB` on the sectors `secProj`;
* `ψv = gradePsi v h μ n ℓ Φ`, FS's unit norm profile `(‖1_{n₊=i}Φ‖/‖Φ‖)`. -/
theorem b2GradingDataB_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) (hB1 : NodeB1B v h J) :
    B2GradingDataB v h J := by
  -- the §5 input: the particle-number window (first conjunct of `NodeB1B`)
  obtain ⟨C₁, C₂, εw, hC₁, hC₂, hεw, hwin⟩ := hB1
  -- the §6 clauses
  obtain ⟨K, εd, hK, hεd, hdv⟩ := dOne_dTwo_le hv hv1 hvrad hR hv_supp hav hC₁ hεw (fun μ hμ hKB n Φ hp hl => (hwin μ hμ hKB n Φ hp hl).1)
  obtain ⟨ε₁, hε₁, hM8⟩ := bigM_ge_eight hav
  refine ⟨K, min ε₁ εd, hK, lt_min hε₁ hεd, ?_⟩
  intro μ hAdm hJKB n Φ hpos hlow
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < fsSide v μ := Work.BoseBox.sideAt_pos hμ hav
  have hAdm₁ : Adm v ε₁ μ := Adm_mono (min_le_left _ _) hAdm
  have hAdm_d : Adm v εd μ := Adm_mono (min_le_right _ _) hAdm
  obtain ⟨hMw3, hMwlo, hMwhi, -⟩ := gradeMw_spec (hM8 μ hAdm₁)
  have hMwle : fsRmw v μ ≤ fsNn v μ n := gradeMw_le_gradeNn n (fsM v μ)
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  obtain ⟨hsuppA, hherm, hsuppψ⟩ := gradeA_support_herm (v := v) (h := h) (μ := μ) (n := n) Φ.contDiff hℓ
  refine ⟨fsNn v μ n, gradeA v h μ n (fsSide v μ) Φ, gradePsi v h μ n (fsSide v μ) Φ,
    fsRmw v μ, hMw3, hMwlo, hMwhi, hMwle, hsuppA, hherm, hsuppψ, ?_, ?_, ?_, ?_, ?_⟩
  · -- `‖ψv‖² = 1`
    exact normSq_gradePsi (v := v) (h := h) (μ := μ) (n := n) hΦc hpos
  · -- the energy identity `⟨ψ,𝒜ψ⟩‖Φ‖² = wordB Φ`
    exact qform_gradeA_eq (v := v) (h := h) hv hv1 hvrad hR hv_supp hav hμ Φ.contDiff hpos
  · -- the band property `d_k = 0` for `k ≥ 3`
    intro k hk
    exact dk_gradeA_eq_zero (v := v) (h := h) hv hv1 hvrad hR hv_supp hav hμ Φ.contDiff k hk
  · -- FS `eq:dvapriori`: `|d₁| + |d₂| ≤ Kμ²ℓ³`
    obtain ⟨h1, h2⟩ := dk_gradeA_one_two (v := v) (h := h) hav hμ Φ.contDiff hpos
    have hb := hdv μ hAdm_d hJKB n Φ hpos hlow
    rw [h1, h2]
    simpa using hb
  · -- the recombination clause
    intro n₀ φ hn₀ hnn hsupp₀ hunit hneg
    exact recomb_clause (v := v) (h := h) hv hv1 hvrad hR hv_supp hav hμ Φ.contDiff Φ.symm hpos
      n₀ φ hn₀ hnn hsupp₀ hunit hneg

end Work.BoseFixB2
