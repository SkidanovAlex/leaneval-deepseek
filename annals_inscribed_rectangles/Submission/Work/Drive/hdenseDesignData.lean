import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.sideGermLocalconstUnconditional
import Submission.Work.Drive.sideGerm_parity_eq_of_close_of_separation
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.orderFromTripleCount
import Submission.Work.Drive.refPlaneLevel
import Submission.Work.Drive.hn2CountInterface
import Submission.Work.Drive.chartPert_linPlaneChart
import Submission.Work.Drive.sweepTripleRot
import Submission.Work.Drive.sweepTripleGeneric
import Submission.Work.Drive.hsurjCentred
import Submission.Work.Drive.localSard
import Submission.Work.Drive.denseOpenBall
import Submission.Work.Drive.goodPair_pertChart_isOpen
import Submission.Work.Drive.goodPair_pertChart_exists_near
import Submission.Work.Drive.germLevelBridge
import Submission.Work.Drive.identity_of_dense_localconst
import Submission.Work.Drive.sweepTripleDense
import Submission.Work.Drive.classInjAnnulus
import Submission.Work.Drive.hdenseDiamBridge

/-!
# The design-side data of the `hdense` node, below the node

This module holds the part of `Submission/Work/Drive/hdense_sideGerm.lean` that has to live **below**
the node `Work.Drive.hdense_sideGerm`:

* `Work.Drive.exists_meet3Hyp_and_good_pairFam_rot_local` — the localized joint genericity of the
  design's rotated triple for a finite family of pair conditions (the `hloc`-free form);
* `Work.Drive.sideGerm_hnloc_planeChart`, `Work.Drive.hdense_sideGerm_of_dense_identity` — the
  angle-locality of the germ value and the density-to-everywhere reduction;
* `Work.Drive.exists_eps_level_lt_pertChart` — the uniform level band of small chart perturbations;
* `Work.Drive.DesignGoodData`, `Work.Drive.exists_designGoodData` — the design's goodness data and its
  producer.

**Why below.**  The node's own proof (which must be written in `hdense_sideGerm.lean`, since that is
where the statement lives) has to be able to *import* the design vocabulary
(`Work.Drive.DesignTripleAt`, `Work.Drive.BlockT6At`, `Work.Drive.GermDataAt` of
`Submission/Work/Drive/hdenseOneT.lean`), the germ lane (`Drive/germDataAt`), the endpoint
(`Drive/hdense_identity_of_designTripleAt`) and the transport/ends lane
(`Drive/blockT6Wrapper`, `Drive/encodedGeneric`, `Drive/hasClassLinearization_of_endData`).  `hdenseOneT`
and two other files used to import the node itself (only for the declarations moved here), which made
that impossible; with those declarations here, the imports must point at this module instead.  See
`HDENSE_STATUS.md`, addendum "the import cycle".
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_hdense : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **The *localized* joint genericity of the design's rotated triple, for a finite family of pair
conditions.**  This is `Work.Drive.exists_meet3Hyp_and_good_pairFam` (the design's triple genericity
with an arbitrary finite family of pair-condition pullbacks) with the hypothesis

`hloc : the base triple locus lies in one chart `(chr p).source` for some `p``

**removed**, in the localized form of `Work.Drive.refTripleLocal`: the chart is taken per base point,
and the family's richness (`Work.Drive.richness_sweepChartFam`, proved) replaces the global
residency.  The pair conditions are open and dense in the parameter, so they survive the shrinking
ball in which the localized Sard produces its parameter.

This is the genericity input that both germ-route siblings (`Drive/hn2_sideGerm_reference` and
`Drive/hdense_sideGerm`) can actually consume: `hloc` is *not* provable for the capping space
(`Submission/Work/Drive/CHART_SOURCE_OPACITY.md`). -/
theorem exists_meet3Hyp_and_good_pairFam_rot_local
    {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (u : Fin 3 → UnitAddCircle)
    {ι : Type} [Countable ι] [Finite ι]
    (c' : ι → ℝ) (w : ι → UnitAddCircle)
    (φ : ι → EuclideanSpace ℝ (Fin 12) →L[ℝ]
      (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)))
    (hφ : ∀ i : ι, Function.Surjective (φ i)) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp CappingSpace (sweepChartFam (fun j => rotPresentation Q (u j)) Ξ c t) ∧
        ∀ i : ι, GoodAt Ξ Q (c' i) (w i) (φ i t) := by
  intro ε' hε'
  classical
  let P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace := fun j => rotPresentation Q (u j)
  have hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k) :=
    fun k => contMDiff_rotPresentation Q (u k) (contMDiff_diskPlane (Q := Q) hQ.1)
  have hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P k y = P k (seamInv2 y) :=
    fun k y hy => rotPresentation_seamInv Q hQ.2 (u k) y hy
  let G : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun t k x => sweepChartFam P Ξ c t k x
  have hGfun : ∀ t : EuclideanSpace ℝ (Fin 12),
      G t = sweepChartFam (fun j => rotPresentation Q (u j)) Ξ c t := by
    intro t; rfl
  have hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2) :=
    fun k' => contMDiff_sweepChartSlice_of_family hΞ hP c k'
  have hGsm : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2) :=
    fun k => contMDiff_sweepChartFam P Ξ c hslice k
  -- ## 1. the pair conditions are open and dense
  have hOpenPair : ∀ (c'' : ℝ) (w'' : UnitAddCircle),
      IsOpen {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) | GoodAt Ξ Q c'' w'' q} :=
    fun c'' w'' => goodPair_pertChart_isOpen (Ξ := Ξ) (Q := Q) hΞ hQ.1 c'' w''
  have hDensePair : ∀ (c'' : ℝ) (w'' : UnitAddCircle),
      Dense {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) | GoodAt Ξ Q c'' w'' q} := by
    intro c'' w''
    rw [Metric.dense_iff]
    intro x r hr
    obtain ⟨dp, hdp, hg⟩ :=
      goodPair_pertChart_exists_near (Ξ := Ξ) (Q := Q) hΞ hQ.1 c'' w'' x.1 x.2 r hr
    refine ⟨(x.1 + dp, x.2), ⟨?_, hg⟩⟩
    have h1 : dist (x.1 + dp) x.1 = ‖dp‖ := by
      rw [dist_eq_norm]; congr 1; abel
    have h2 : dist x.2 x.2 = 0 := dist_self _
    have hd : dist ((x.1 + dp, x.2) : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))
        (x.1, x.2) = ‖dp‖ := by
      rw [Prod.dist_eq, h1, h2, max_eq_left (norm_nonneg dp)]
    rw [Metric.mem_ball, hd]
    exact hdp
  let A : ι → Set (EuclideanSpace ℝ (Fin 12)) := fun i => {t | GoodAt Ξ Q (c' i) (w i) (φ i t)}
  have hAopen : ∀ i : ι, IsOpen (A i) := by
    intro i
    rw [show A i = (φ i) ⁻¹' {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
        GoodAt Ξ Q (c' i) (w i) q} from rfl]
    exact IsOpen.preimage (φ i).continuous (hOpenPair (c' i) (w i))
  have hAdense : ∀ i : ι, Dense (A i) := by
    intro i
    have hopenmap : IsOpenMap (φ i) := ContinuousLinearMap.isOpenMap (φ i) (hφ i)
    rw [show A i = (φ i) ⁻¹' {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
        GoodAt Ξ Q (c' i) (w i) q} from rfl]
    exact (hDensePair (c' i) (w i)).preimage hopenmap
  -- ## 2. a point `s` of small norm satisfying all the pair conditions
  haveI : Fintype ι := Fintype.ofFinite ι
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Ps : Fin (Fintype.card ι) → Set (EuclideanSpace ℝ (Fin 12)) := fun n => A (eι.symm n)
  have hPsopen : ∀ n, IsOpen (Ps n) := fun n => hAopen _
  have hPsdense : ∀ n : Fin (Fintype.card ι), ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∃ y : EuclideanSpace ℝ (Fin 12), y ∈ Ps n ∧ ‖y - x‖ < δ := by
    intro n x _ δ hδ
    obtain ⟨y, hyball, hy⟩ := Metric.dense_iff.mp (hAdense (eι.symm n)) x δ hδ
    exact ⟨y, hy, by rw [Metric.mem_ball, dist_eq_norm] at hyball; exact hyball⟩
  set ε₀ : ℝ := min (ε' / 4) (1 / 2) with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min (by linarith) (by norm_num)
  have hε₀le1 : ε₀ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  obtain ⟨s, hsnorm, hsall⟩ :=
    exists_mem_all_of_isOpen_dense (Fintype.card ι) Ps hPsopen hPsdense ε₀ hε₀pos hε₀le1
  have hsPair : ∀ i : ι, s ∈ A i := fun i => by
    simpa [Ps, Equiv.symm_apply_apply] using hsall (eι i)
  have hsnorm' : ‖s‖ < ε' / 4 := lt_of_lt_of_le hsnorm (min_le_left _ _)
  -- ## 3. a ball around `s` on which all the pair conditions hold
  have hOpenInter : IsOpen (⋂ i : ι, A i) := isOpen_iInter_of_finite (fun i => hAopen i)
  obtain ⟨δP, hδPpos, hδPsub⟩ := Metric.isOpen_iff.mp hOpenInter s (Set.mem_iInter.mpr hsPair)
  -- ## 4. the translated family
  let Gs : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun τ k x => G (s + τ) k x
  set ετ : ℝ := min δP ((ε' - ‖s‖) / 2) with hετdef
  have hετpos : 0 < ετ := by
    rw [hετdef]
    exact lt_min hδPpos (by linarith)
  have hετ_δP : ετ ≤ δP := by rw [hετdef]; exact min_le_left _ _
  have hετ_ε' : ετ ≤ (ε' - ‖s‖) / 2 := by rw [hετdef]; exact min_le_right _ _
  have hGs_sm : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => Gs q.1 k q.2) := by
    intro k
    have htrans : ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => (s + q.1, q.2)) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    have hcomp := (hGsm k).comp htrans
    simpa only [Function.comp_def, Gs] using hcomp
  have hGs_slice : ∀ (τ : EuclideanSpace ℝ (Fin 12)) (k : Fin 3),
      ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Gs τ k) := by
    intro τ k
    have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ((s + τ, x) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := (hGsm k).comp (contMDiff_iff_contDiff.mpr hφ')
    simpa only [Function.comp_def, Gs, G, sweepChartFam_apply] using hcomp
  have hGs_seam : ∀ (τ : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)), onSeam x → Gs τ k x = Gs τ k (seamInv x) := by
    intro τ k x hx
    have hinst : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
        (fun z => Ξ (blk k (s + τ)) (P k z)) y
          = (fun z => Ξ (blk k (s + τ)) (P k z)) (seamInv2 y) :=
      fun y hy => congrArg (Ξ (blk k (s + τ))) (hPseam k y hy)
    have h := clampedSweep_seamInv (c k) (fun r => 1 - r)
      (fun z => Ξ (blk k (s + τ)) (P k z)) hinst x hx
    simpa only [Gs, G, sweepChartFam_apply, Function.comp_def] using h
  -- ## 5. the richness of the translated family, from the richness at the centre `s`
  have hrich := richness_sweepChartFam P Ξ c hΞ hc hcdist hP
  have hGs_surj : ∀ (p : CappingSpace) (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ),
      IsCompact K → 0 < δ →
      (∀ (τ : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
        ∀ k : Fin 3, Gs τ k (TParity.bPartC k y) ∈ (chr p).source) →
      ∀ (τ : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
        TParity.chartDiff3 p (Gs τ) y = 0 →
        Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (Gs τ') y) τ) := by
    intro p K δ hK hδ hcont τ y hτ hy hz
    have hcontain : ∀ (t : EuclideanSpace ℝ (Fin 12)) (y' : EuclideanSpace ℝ (Fin 9)),
        ‖t - s‖ < δ → y' ∈ K → ∀ k : Fin 3,
          sweepChartFam P Ξ c t k (TParity.bPartC k y') ∈ (chr p).source := by
      intro t y' ht hy' k
      have hswap : Gs (t - s) = G t := by
        funext k x
        simp only [Gs, G]
        rw [show s + (t - s) = t by abel]
      have h := hcont (t - s) y' ht hy' k
      rw [hswap] at h
      exact h
    have hsrc : ∀ k : Fin 3, G (s + τ) k (TParity.bPartC k y) ∈ (chr p).source := by
      intro k
      have h := hcont τ y hτ hy k
      simpa only [Gs] using h
    have hz' : TParity.chartDiff3 p (G (s + τ)) y = 0 := by
      simpa only [Gs] using hz
    have hsurj := hrich p K s δ hK hδ hcontain (s + τ) y
      (by rw [add_sub_cancel_left]; exact hτ) hy hz'
    have hsm := contDiffAt_chartDiff3_family_fin 12 G hGsm p (s + τ) hsrc
    have hinner : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' : EuclideanSpace ℝ (Fin 12) =>
          ((t', y) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9))) (s + τ) :=
      contDiffAt_id.prodMk contDiffAt_const
    have hsm'' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G q.1) q.2) ∘
          (fun t' : EuclideanSpace ℝ (Fin 12) => (t', y))) (s + τ) :=
      hsm.comp (s + τ) hinner
    have hsm' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G t') y) (s + τ) := hsm''
    have hF : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin 12) =>
        TParity.chartDiff3 p (G t') y)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G t') y) (s + τ)) (s + τ) :=
      (hsm'.differentiableAt top_ne_zero_hdense).hasFDerivAt
    have hshift : HasFDerivAt (fun τ' : EuclideanSpace ℝ (Fin 12) => s + τ')
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 12))) τ := by
      simpa using (hasFDerivAt_id τ).const_add s
    have hcomp := hF.comp τ hshift
    rw [ContinuousLinearMap.comp_id] at hcomp
    have heq : fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (Gs τ') y) τ
        = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G t') y) (s + τ) := by
      have h1 : (fun τ' : EuclideanSpace ℝ (Fin 12) =>
            TParity.chartDiff3 p (Gs τ') y)
          = (fun τ' : EuclideanSpace ℝ (Fin 12) =>
            TParity.chartDiff3 p (G (s + τ')) y) := rfl
      rw [h1]
      exact hcomp.fderiv
    rw [heq]
    exact hsurj
  -- ## 6. the localized Sard at the translated base
  obtain ⟨τ, hτ, hM⟩ := localSard (M := CappingSpace) (m := 12) Gs hGs_sm hGs_slice
    hGs_seam hGs_surj ετ hετpos
  -- ## 7. the conclusion
  refine ⟨s + τ, ?_, ?_, ?_⟩
  · have h1 : ‖τ‖ < (ε' - ‖s‖) / 2 := lt_of_lt_of_le hτ hετ_ε'
    calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
      _ < ‖s‖ + (ε' - ‖s‖) / 2 := by linarith
      _ < ε' := by linarith
  · have hM' : Meet3Hyp CappingSpace (G (s + τ)) := by simpa only [Gs] using hM
    rwa [hGfun (s + τ)] at hM'
  · intro i
    have hmem : s + τ ∈ ⋂ i : ι, A i := hδPsub (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact lt_of_lt_of_le hτ hετ_δP)
    exact Set.mem_iInter.mp hmem i

end

/-- **The angle-locality of the germ value in the `nhds`-membership form, with no `hdisj`.** -/
lemma sideGerm_hnloc_planeChart {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hQ : IsPlaneChart γ hγne Q) (hΞ : ChartPert Q m Ξ)
    (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) :
    ∀ x ∈ Zc γ, ∀ᶠ y in nhds x, y ∈ Zc γ → sideGerm Ξ Q c y = sideGerm Ξ Q c x := by
  intro x hx
  have h := sideGerm_localconst_of_planeChart_unconditional Ξ Q c hγne hγinj hQ hΞ hc hcbot hx
  filter_upwards [h] with y hy hyZ
  exact hy

/-- **`hdense` for the germ count, from the identity on a dense set of *good* triples** — the
`hdisj`-free form of `Work.Drive.hdense_sideGerm_of_good_identity` (whose disjointness hypothesis is
documented as not provable, `Submission/Work/Drive/CHART_SOURCE_OPACITY.md`): the local constancy is
`Work.Drive.sideGerm_localconst_of_planeChart_unconditional`, and the dense-match step is
`Work.Drive.identity_of_dense_localconst`. -/
theorem hdense_sideGerm_of_dense_identity {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (G : Set (UnitAddCircle × UnitAddCircle))
    (hdense : ∀ a c' : UnitAddCircle, a ∈ Work.Drive.Zc γ → c' ∈ Work.Drive.Zc γ →
      a + c' ∈ Work.Drive.Zc γ →
      (a, c') ∈ closure (G ∩ {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Work.Drive.Zc γ ∧ q.2 ∈ Work.Drive.Zc γ ∧ q.1 + q.2 ∈ Work.Drive.Zc γ}))
    (hid : ∀ q ∈ G, q.1 ∈ Work.Drive.Zc γ → q.2 ∈ Work.Drive.Zc γ →
      q.1 + q.2 ∈ Work.Drive.Zc γ →
      Work.Drive.sideGerm Ξ Q c q.1 * Work.Drive.sideGerm Ξ Q c (q.1 + q.2)
        + Work.Drive.sideGerm Ξ Q c (-q.1) * Work.Drive.sideGerm Ξ Q c q.2
        + Work.Drive.sideGerm Ξ Q c (-(q.1 + q.2)) * Work.Drive.sideGerm Ξ Q c (-q.2) = 1) :
    ∀ a c' : UnitAddCircle, a ∈ Work.Drive.Zc γ → c' ∈ Work.Drive.Zc γ →
      a + c' ∈ Work.Drive.Zc γ →
      (a, c') ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Work.Drive.Zc γ ∧ q.2 ∈ Work.Drive.Zc γ ∧ q.1 + q.2 ∈ Work.Drive.Zc γ ∧
          Work.Drive.sideGerm Ξ Q c q.1 * Work.Drive.sideGerm Ξ Q c (q.1 + q.2)
            + Work.Drive.sideGerm Ξ Q c (-q.1) * Work.Drive.sideGerm Ξ Q c q.2
            + Work.Drive.sideGerm Ξ Q c (-(q.1 + q.2)) * Work.Drive.sideGerm Ξ Q c (-q.2) = 1} := by
  have hident := identity_of_dense_localconst (Z := Work.Drive.Zc γ)
    (fun u hu => neg_mem_Zc (γ := γ) hu)
    (fun w : UnitAddCircle => Work.Drive.sideGerm Ξ Q c w)
    (sideGerm_hnloc_planeChart Ξ Q c hγne hγinj hQ hΞ hc hcbot) G hdense hid
  intro a b ha hb hab
  exact subset_closure ⟨ha, hb, hab, hident a b ha hb hab⟩

/-- **Small chart perturbations do not push the chart's disk below a level.**  If the level `c` is
strictly below the levels of `chartDisk Q`, then for every parameter `t` of small enough norm the levels
of the perturbed chart `Ξ t` are still `> c` on `chartDisk Q`.  (This is the level-band input of the
germ route: the design's level `c` has to stay below the levels of the *perturbed* loop and planes, and
the count at level `c` is computed at small perturbation parameters.) -/
lemma exists_eps_level_lt_pertChart {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (hΞ : ChartPert Q m Ξ) (c : ℝ) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε →
      ∀ p ∈ chartDisk Q, c < levelOf (Ξ t p) := by
  have hcont : Continuous fun q : EuclideanSpace ℝ (Fin m) × CappingSpace => Ξ q.1 q.2 :=
    hΞ.2.1.continuous
  have hUopen : IsOpen {q : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ q.1 q.2)} :=
    isOpen_lt continuous_const (continuous_levelOf.comp hcont)
  have hmem : ∀ p : ↥(chartDisk Q),
      (⟨0, (p : CappingSpace)⟩ : EuclideanSpace ℝ (Fin m) × CappingSpace) ∈
        {q : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ q.1 q.2)} := by
    intro p
    show c < levelOf (Ξ 0 (p : CappingSpace))
    rw [hΞ.1 (p : CappingSpace)]
    exact hcbot (p : CappingSpace) p.2
  -- every point of the disk has a product neighbourhood inside the level region
  have hloc : ∀ p : ↥(chartDisk Q), ∃ ρ : ℝ, 0 < ρ ∧ ∃ W : Set CappingSpace, IsOpen W ∧
      (p : CappingSpace) ∈ W ∧
      ∀ (s : EuclideanSpace ℝ (Fin m)) (y : CappingSpace), ‖s‖ < ρ → y ∈ W →
        c < levelOf (Ξ s y) := by
    intro p
    have hUnhds : {q : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ q.1 q.2)} ∈
        𝓝 (⟨0, (p : CappingSpace)⟩ : EuclideanSpace ℝ (Fin m) × CappingSpace) :=
      hUopen.mem_nhds (hmem p)
    rw [nhds_prod_eq] at hUnhds
    obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hUnhds
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨W', hW'W, hW'open, hpW'⟩ := mem_nhds_iff.mp hW
    refine ⟨ρ, hρ, W', hW'open, hpW', fun s y hs hy => ?_⟩
    have hmem' : (⟨s, y⟩ : EuclideanSpace ℝ (Fin m) × CappingSpace) ∈
        {q : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ q.1 q.2)} :=
      hVW ⟨hρV (by rw [Metric.mem_ball, dist_zero_right]; exact hs), hW'W hy⟩
    exact hmem'
  choose ρ hρpos W hWopen hpW hWsub using hloc
  obtain ⟨tfin, htfin⟩ := (chartDisk_compact (IsSmoothChart_of_isPlaneChart hQ).continuous).elim_finite_subcover
    (fun p : ↥(chartDisk Q) => W p) (fun p => hWopen p)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpW ⟨x, hx⟩⟩)
  have hne : (tfin.image ρ).Nonempty := by
    have hx : Q (0 : ℂ) ∈ chartDisk Q := ⟨0, by rw [Metric.mem_closedBall]; simp, rfl⟩
    obtain ⟨q, hq1, -⟩ := Set.mem_iUnion₂.mp (htfin hx)
    exact ⟨ρ q, Finset.mem_image.mpr ⟨q, hq1, rfl⟩⟩
  have hminpos : 0 < (tfin.image ρ).min' hne := by
    rw [Finset.lt_min'_iff]
    intro b hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hb
    exact hρpos q
  refine ⟨(tfin.image ρ).min' hne, hminpos, ?_⟩
  intro s hs p hp
  obtain ⟨q, hq1, hq2⟩ := Set.mem_iUnion₂.mp (htfin hp)
  exact hWsub q s p (lt_of_lt_of_le hs (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hq1, rfl⟩))) hq2
/-- **The design's goodness data at a parameter `t`** for the germ route's triple: the three
chart-perturbed clamped sweeps of the design's triple `(diskPlane Q, rot_a Q, rot_{a+c'} Q)` (the plane
presentations `rotPresentation Q (u j)`, perturbed by the *concrete* chart perturbation `chartPert`)
satisfy `Meet3Hyp`, the six ordered pairs are `GoodAt` both at the truncation level `cblk j` and at the
design's level `c`, and the level bands of the perturbed loops and of the perturbed planes hold.

The wrapper is *instance-free* (the `CappingSpace` charted structure is resolved here, once), so the
identity it implies can be stated in a delegated file; cf. `PPPARITY_STATUS.md` §4. -/
def DesignGoodData (Q : ℂ → CappingSpace) (c : ℝ) (cblk : Fin 3 → ℝ)
    (u : Fin 3 → UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  Meet3Hyp CappingSpace
      (sweepChartFam (fun j => rotPresentation Q (u j)) (fun s p => chartPert s p) cblk t) ∧
    (∀ k j : Fin 3, k ≠ j →
      GoodAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) (blk k t, blk j t)) ∧
    (∀ k j : Fin 3, k ≠ j →
      GoodAt (fun s p => chartPert s p) Q c (u j - u k) (blk k t, blk j t)) ∧
    (∀ k : Fin 3, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      c < levelOf (coreLoop (pertChart (fun s p => chartPert s p) Q (blk k t)) s)) ∧
    (∀ k : Fin 3, ∀ (w : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)),
      y ∈ Submission.Drive.unitBox 1 →
      c ≤ levelOf (rotPresentation (pertChart (fun s p => chartPert s p) Q (blk k t)) w y))

/-- **The design's goodness data exists at every small parameter scale.**  The localized joint
genericity `Work.Drive.exists_meet3Hyp_and_good_pairFam_rot_local` (the `hloc`-free form) applied to
the twelve pair conditions (the six ordered pairs at the truncation levels `cblk j` and at the design's
level `c`), together with the level bands, which hold for small parameters by
`Work.Drive.exists_eps_level_lt_pertChart`. -/
lemma exists_designGoodData {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {c : ℝ} (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (a c' : UnitAddCircle) (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k)
    (hcdist : ∀ k k' : Fin 3, cblk k = cblk k' → k = k') :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      DesignGoodData Q c cblk ![0, a, a + c'] t := by
  intro ε' hε'
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  obtain ⟨εl, hεl, hlvl⟩ := exists_eps_level_lt_pertChart hQ (fun s p => chartPert s p) hΞc c hcbot
  let ι := {q : Fin 3 × Fin 3 // q.1 ≠ q.2} × Fin 2
  let c'' : ι → ℝ := fun q => if q.2 = 0 then cblk ((q.1 : Fin 3 × Fin 3).2) else c
  let w' : ι → UnitAddCircle := fun q =>
    (![0, a, a + c'] : Fin 3 → UnitAddCircle) (q.1 : Fin 3 × Fin 3).2
      - (![0, a, a + c'] : Fin 3 → UnitAddCircle) (q.1 : Fin 3 × Fin 3).1
  let φ : ι → EuclideanSpace ℝ (Fin 12) →L[ℝ]
      (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :=
    fun q => (blk (q.1 : Fin 3 × Fin 3).1).prod (blk (q.1 : Fin 3 × Fin 3).2)
  have hφ : ∀ i : ι, Function.Surjective (φ i) := by
    rintro ⟨⟨⟨k, j⟩, hkj⟩, lvl⟩
    rintro ⟨x, y⟩
    refine ⟨blkSpan k x + blkSpan j y, ?_⟩
    have h1 : blk k (blkSpan k x + blkSpan j y) = x := by
      rw [map_add, blk_blkSpan k x, blk_blkSpan_of_ne (k := j) (j := k) hkj, add_zero]
    have h2 : blk j (blkSpan k x + blkSpan j y) = y := by
      rw [map_add, blk_blkSpan_of_ne (k := k) (j := j) (Ne.symm hkj) x, blk_blkSpan j y,
        zero_add]
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext h1 h2
  have hgen := exists_meet3Hyp_and_good_pairFam_rot_local (Q := Q)
    (IsChartData_of_isPlaneChart hQ) (fun s p => chartPert s p) hΞc cblk hcpos hcdist
    ![0, a, a + c'] c'' w' φ hφ (min ε' εl) (lt_min hε' hεl)
  obtain ⟨t, ht, hmeet, hgood⟩ := hgen
  have ht' : ‖t‖ < ε' := lt_of_lt_of_le ht (min_le_left _ _)
  have htl : ‖t‖ < εl := lt_of_lt_of_le ht (min_le_right _ _)
  refine ⟨t, ht', hmeet, ?_, ?_, ?_, ?_⟩
  · intro k j hkj
    have h := hgood ⟨⟨(k, j), hkj⟩, 0⟩
    simpa [c'', w', φ, ContinuousLinearMap.prod_apply] using h
  · intro k j hkj
    have h := hgood ⟨⟨(k, j), hkj⟩, 1⟩
    simpa [c'', w', φ, ContinuousLinearMap.prod_apply] using h
  · intro k s hs
    have hmem : Q (Complex.exp (Real.pi * (s : ℂ) * Complex.I)) ∈ chartDisk Q := by
      refine ⟨Complex.exp (Real.pi * (s : ℂ) * Complex.I), ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
      simp
    have h := hlvl (blk k t) (lt_of_le_of_lt (norm_blk_le k t) htl) _ hmem
    simpa only [coreLoop, pertChart] using h
  · intro k w y hy
    have hmem : Q (sqDisk (foldBox y)) ∈ chartDisk Q := by
      refine ⟨sqDisk (foldBox y), ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_sqDisk_le_one (foldBox y) (foldBox_mem_unitBox y)
    have h := hlvl (blk k t) (lt_of_le_of_lt (norm_blk_le k t) htl) _ hmem
    have h2 : levelOf (rotPresentation (pertChart (fun s p => chartPert s p) Q (blk k t)) w y)
        = levelOf (pertChart (fun s p => chartPert s p) Q (blk k t) (sqDisk (foldBox y))) := by
      rw [show rotPresentation (pertChart (fun s p => chartPert s p) Q (blk k t)) w y
          = rotCapping w (pertChart (fun s p => chartPert s p) Q (blk k t)
              (sqDisk (foldBox y))) from rfl, levelOf_rotCapping]
    rw [h2]
    exact le_of_lt h

end Work.Drive
