import Mathlib
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.pairRegLinBase
import Submission.Work.Drive.endTripleReg_linPlaneCharts
import Submission.Work.Drive.linPlaneTripleRange
import Submission.Work.Drive.linPlaneChartsEndTripleReg
import Submission.Work.Drive.pairRegRows
import Submission.Work.Drive.classRowRebasing
import Submission.Work.Drive.hendL012Row
import Submission.Work.Drive.exists_meet3Hyp_and_cond_near_of_openDense
import Submission.Work.Drive.analyticDensity
import Submission.Work.Drive.rowA_linDesign_pairReg_openDense
import Submission.Work.Drive.rowB_linTrans_pairReg_openDense
import Submission.Work.Drive.rowCD_linTrans_generalPosition_openDense

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology BigOperators
attribute [local instance] Work.Drive.projCharted

noncomputable section

/-- **A finite intersection of open sets dense at every point of the closed unit ball is again dense
at every such point.**  (The centre may lie on the boundary `‖x‖ = 1`; one first moves strictly
inside.) -/
theorem DenseAtBall.iInter {n : ℕ} {ι : Type*} [Fintype ι]
    {R : ι → Set (EuclideanSpace ℝ (Fin n))} (hopen : ∀ i, IsOpen (R i))
    (hdense : ∀ i, DenseAtBall (R i)) : DenseAtBall (⋂ i, R i) := by
  intro x hx δ hδ
  obtain ⟨x', hx'1, hx'd⟩ := exists_norm_lt_one_near x hx (by linarith : (0:ℝ) < δ / 2)
  obtain ⟨y, hyd, hyall⟩ := exists_mem_all_near_of_isOpen_dense_fintype R hopen
    (fun i => hdense i) hx'1 (δ / 2) (by linarith)
  refine ⟨y, Set.mem_iInter.mpr hyall, ?_⟩
  calc ‖y - x‖ ≤ ‖y - x'‖ + ‖x' - x‖ := by
        have h := norm_add_le (y - x') (x' - x)
        rwa [sub_add_sub_cancel] at h
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring


/-- **Row C from row D.**  `EndTripleReg lin₂ lin₀ lin₁` for the transported linear models is a
consequence of the two general-position clauses alone
(`Work.Drive.endTripleReg_linPlaneCharts_uncond`, which is the proved unconditional form of the
all-linear row). -/
theorem endTripleReg_linTrans_of_generalPosition (A : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12))
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3,
        linSub ((linBase A k).trans (classEquiv ((blk k) t)))) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart ((linBase A k).trans (classEquiv ((blk k) t))) cl hcl z
        ≠ linCommonPt (fun k => (linBase A k).trans (classEquiv ((blk k) t))) cl hcl hrank) :
    EndTripleReg (linTransClass (linBase A 2) (blk 2 t) cl hcl)
      (linTransClass (linBase A 0) (blk 0 t) cl hcl)
      (linTransClass (linBase A 1) (blk 1 t) cl hcl) :=
  endTripleReg_linPlaneCharts_uncond
    (fun k => (linBase A k).trans (classEquiv ((blk k) t))) cl hcl hrank hgen

/-! ## The row producers (proved in their own modules) and the assembly

The five rows `Work.Drive.DesignRowsLinAt` are supplied by three independent producers, each proved in
its own module and each delivered as "open set, dense at every point of the closed unit ball":

* `Work.Drive.rowA_linDesign_pairReg_openDense` (`Drive/rowA_linDesign_pairReg_openDense.lean`) — the
  row `PairReg lin₀ P̂₂` of *linear model `0`* against the design's *third perturbed plane*; it is the
  only row involving the plane chart `Q`.  Its density is produced from the design's own sweep
  genericity (`Work.Drive.exists_loopBoxData_of_small_shift_fam`, moving block `2` only — so the
  transported linear model is frozen at the base parameter) and
  `Work.Drive.pairReg_lin_blockPlane_of_loopBoxData`; openness is
  `Work.Drive.isOpen_pairReg_linPert_er`.
* `Work.Drive.rowB_linTrans_pairReg_openDense` (`Drive/rowB_linTrans_pairReg_openDense.lean`) — the row
  `PairReg lin₀ lin₁` of the two *transported linear models*, from the six incidence conditions of
  `Work.Drive.pairReg_linPlaneCharts_of_incidence`, each an analytic non-vanishing condition with
  witness `t = 0` (`Work.Drive.linIncidence_linBase`), turned into an open dense-at-ball set by
  `Work.Drive.isOpen_denseAtBall_ne_zero` (`Drive/analyticDensity.lean`).
* `Work.Drive.rowCD_linTrans_generalPosition_openDense`
  (`Drive/rowCD_linTrans_generalPosition_openDense.lean`) — the general-position clauses `hrank`/`hgen`
  of the transported family `Ψ k := (linBase A k).trans (classEquiv (blk k t))`, again from analytic
  non-vanishing incidence conditions on the transported planes
  `P k := (linSub (linBase A k)).map (classEquiv (blk k t))` and fold planes
  `M k := (linBdry (linBase A k)).map (classEquiv (blk k t))` (`linSub_trans`, `linBdry_trans`), with
  witnesses at `t = 0` (`Work.Drive.finrank_iInf_linSub_linBase`, `Work.Drive.hgen_linBase`,
  `Work.Drive.linIncidence_linBase`).  The third linear row `EndTripleReg lin₂ lin₀ lin₁` follows from
  `hrank` + `hgen` **alone** (`Work.Drive.endTripleReg_linPlaneCharts_uncond`), which is
  `endTripleReg_linTrans_of_generalPosition` below.

The record of *why* the rows are a genericity statement — and the correction of the (incorrect)
"re-basing" route of `CLASSROWS_DENSITY_MECHANISM.md` §2 — is in `HANDOFF.md` (session of this node)
and in the docstrings of the three producer files. -/

/-- **Rows C and D**: `EndTripleReg lin₂ lin₀ lin₁` and the general-position clauses, on an open set
dense at every point of the closed unit ball.  The `EndTripleReg` clause is *derived* from the
general-position clauses (`endTripleReg_linTrans_of_generalPosition`). -/
theorem exists_openDense_rowCD (A : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧ DenseAtBall R ∧
      ∀ t ∈ R, EndTripleReg (linTransClass (linBase A 2) (blk 2 t) cl hcl)
          (linTransClass (linBase A 0) (blk 0 t) cl hcl)
          (linTransClass (linBase A 1) (blk 1 t) cl hcl) ∧
        (∃ hrank : Module.finrank ℝ ↥(⨅ k : Fin 3,
            linSub ((linBase A k).trans (classEquiv ((blk k) t)))) = 1,
          ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
            linPlaneChart ((linBase A k).trans (classEquiv ((blk k) t))) cl hcl z
              ≠ linCommonPt (fun k => (linBase A k).trans (classEquiv ((blk k) t))) cl hcl
                  hrank) := by
  obtain ⟨R, hRopen, hRdense, hR⟩ := rowCD_linTrans_generalPosition_openDense A cl hcl
  refine ⟨R, hRopen, hRdense, fun t ht => ?_⟩
  obtain ⟨hrank, hgen⟩ := hR t ht
  exact ⟨endTripleReg_linTrans_of_generalPosition A cl hcl t hrank hgen, hrank, hgen⟩

/-- **The five *linear* rows of the ends clause at a parameter of an open dense-at-every-point set**,
for the sheared family `Work.Drive.linBase A` (the family every consumer of
`Work.Drive.exists_classRowFamily` uses).

For an injective curve `γ` with a plane chart `Q`, any angles `a c'`, any `A : Eucl 3 ≃L[ℝ] Eucl 3` and
level `cl > 0`, there is an open set `R` of design parameters meeting every ball around every point of
the closed unit ball on which the five rows

`Work.Drive.DesignRowsLinAt Q a c' (fun k => Work.Drive.linBase A k) cl hcl t`

hold, i.e.:

* `PairReg lin₀(t) P̂₂(t)` — the transported linear model
  `lin₀(t) = linTransClass (linBase A 0) (blk 0 t)` against the design's second perturbed plane;
* `PairReg lin₀(t) lin₁(t)`;
* `EndTripleReg lin₂(t) lin₀(t) lin₁(t)`;
* the general-position clauses `hrank`/`hgen` of the *transported* family
  `k ↦ (linBase A k).trans (classEquiv (blk k t))`.

Route and the reason the statement is restricted to `linBase A`:

* the transported chart is again a sheared chart, `(linBase A k).trans (classEquiv τ)
  = linBase (A.trans (classEquiv τ)) k`, so at each `k` separately the untransported lemmas apply —
  and the *untransported* rows and general-position clauses are the **proved** lemmas
  `Work.Drive.pairReg_linBase` (`A`, `cl`), `Work.Drive.endTripleReg_linPlaneCharts_uncond`,
  `Work.Drive.finrank_iInf_linSub_linBase` and `Work.Drive.hgen_linBase`;
* what has to be proved is therefore only the *relative* general-position statement in the three free
  class coordinates `τ k = blk k t`: the three transported projective planes must be pairwise distinct
  and in general position (for `PairReg`/`EndTripleReg`, whose class maps are linear chart maps), and
  the bad configurations form a closed set with empty interior (an incidence/dimension count on the
  three-parameter family `τ ↦ classEquiv τ`), which is open and dense;
* `hγinj` is needed exactly as in the sibling `Work.Drive.classRowsSweep_openDense` (the constant-chart
  counterexample of `CLASSROW_FALSE_NOTE.md`);
* the density at every point of the parameter is the re-basing mechanism of
  `Drive/classRowRebasing.lean` (only the class coordinates matter, and the conditions re-centre at
  every base point). -/
theorem classRowsLin_openDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {c : ℝ} (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    (a c' : UnitAddCircle) (ha : a ∈ Work.Drive.Zc γ) (hc' : c' ∈ Work.Drive.Zc γ)
    (hac : a + c' ∈ Work.Drive.Zc γ)
    (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧
      (∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
        ∃ y, y ∈ R ∧ ‖y - x‖ < δ) ∧
      (∀ t ∈ R, Work.Drive.DesignRowsLinAt Q a c' (fun k => Work.Drive.linBase A k) cl hcl t) := by
  obtain ⟨RA, hAopen, hAdense, hArows⟩ :=
    rowA_linDesign_pairReg_openDense hγinj hQ hc hcbot hdisjZc a c' ha hc' hac A cl hcl
  obtain ⟨RB, hBopen, hBdense, hBrows⟩ := rowB_linTrans_pairReg_openDense A cl hcl
  obtain ⟨RC, hCopen, hCdense, hCrows⟩ := exists_openDense_rowCD A cl hcl
  set S : Fin 3 → Set (EuclideanSpace ℝ (Fin 12)) := ![RA, RB, RC] with hS
  have hOpen : ∀ i, IsOpen (S i) := by
    intro i
    fin_cases i
    · simpa [hS] using hAopen
    · simpa [hS] using hBopen
    · simpa [hS] using hCopen
  have hDense : ∀ i, DenseAtBall (S i) := by
    intro i
    fin_cases i
    · simpa [hS] using hAdense
    · simpa [hS] using hBdense
    · simpa [hS] using hCdense
  refine ⟨⋂ i, S i, isOpen_iInter_of_finite hOpen, ?_, ?_⟩
  · exact DenseAtBall.iInter hOpen hDense
  · intro t ht
    have h0 : t ∈ RA := by simpa [hS] using Set.mem_iInter.mp ht 0
    have h1 : t ∈ RB := by simpa [hS] using Set.mem_iInter.mp ht 1
    have h2 : t ∈ RC := by simpa [hS] using Set.mem_iInter.mp ht 2
    exact ⟨hArows t h0, hBrows t h1, hCrows t h2⟩

end

end Work.Drive
