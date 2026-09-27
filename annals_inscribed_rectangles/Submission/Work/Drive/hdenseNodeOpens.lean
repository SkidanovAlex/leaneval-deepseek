import Mathlib
import Submission.Work.Drive.sweepTripleGeneric
import Submission.Work.Drive.hdenseDesignData
import Submission.Work.Drive.denseOpenBall
/-!
# The open-dense localized genericity, **below** the node (agent of `hdense_sideGerm`)

A below-the-node copy of `Submission/Work/Drive/exists_meet3Hyp_rot_local_of_opensN.lean` (which
imports the node itself, for the declarations moved to `hdenseDesignData.lean`).  The declarations
carry the suffix `N`; the proofs are unchanged.  See `NOTE_hdense_import_cycle.md`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_m3hops : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **A finite family of open conditions, dense at every point of the unit ball, has a common point in
every ball of radius `≤ 1`** — the `Fintype`-indexed form of
`Work.Drive.exists_mem_all_of_isOpen_dense`. -/
theorem exists_mem_all_of_isOpen_dense_fintypeN {m : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → Set (EuclideanSpace ℝ (Fin m)))
    (hopen : ∀ i, IsOpen (P i))
    (hdense : ∀ i, ∀ x : EuclideanSpace ℝ (Fin m), ‖x‖ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ y, y ∈ P i ∧ ‖y - x‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ t, ‖t‖ < ε ∧ ∀ i, t ∈ P i := by
  intro ε hε hε1
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨t, ht, hall⟩ := exists_mem_all_of_isOpen_dense (m := m) (Fintype.card ι)
    (fun n => P (e.symm n)) (fun n => hopen _) (fun n => hdense _) ε hε hε1
  refine ⟨t, ht, fun i => ?_⟩
  simpa using hall (e i)

/-- **The *localized* joint genericity of the design's rotated triple, for an arbitrary finite family
of open-dense conditions.**

This is `Work.Drive.exists_meet3Hyp_and_good_pairFam_rot_local` with the specific pair-condition family
replaced by an abstract finite family `Pcond` of *open* sets that are dense at every point of the closed
unit ball: the two properties of the pair conditions that the localized Sard argument actually uses.
(The pair conditions of the design are themselves obtained from those two properties, see
`Work.Drive.exists_meet3Hyp_rot_local_of_opensN`.)

The chart is taken per base point (the localized form of `Work.Drive.refTripleLocal`), and the family's
richness (`Work.Drive.richness_sweepChartFam`, proved) replaces a global residency of the triple locus
in one chart — `hloc` is *not* provable for the capping space
(`Submission/Work/Drive/CHART_SOURCE_OPACITY.md`). -/
theorem exists_meet3Hyp_rot_local_of_openDenseN
    {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (u : Fin 3 → UnitAddCircle)
    {ι : Type} [Finite ι]
    (Pcond : ι → Set (EuclideanSpace ℝ (Fin 12)))
    (hPopen : ∀ i : ι, IsOpen (Pcond i))
    (hPdense : ∀ i : ι, ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ Pcond i ∧ ‖y - x‖ < δ) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp CappingSpace (sweepChartFam (fun j => rotPresentation Q (u j)) Ξ c t) ∧
        (∀ i : ι, t ∈ Pcond i) := by
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
  -- ## 1. a point `s` of small norm satisfying all the conditions
  haveI : Fintype ι := Fintype.ofFinite ι
  set ε₀ : ℝ := min (ε' / 4) (1 / 2) with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min (by linarith) (by norm_num)
  have hε₀le1 : ε₀ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  obtain ⟨s, hsnorm, hsP⟩ :=
    exists_mem_all_of_isOpen_dense_fintypeN Pcond hPopen hPdense ε₀ hε₀pos hε₀le1
  have hsnorm' : ‖s‖ < ε' / 4 := lt_of_lt_of_le hsnorm (min_le_left _ _)
  -- ## 2. a ball around `s` on which all the conditions hold
  have hOpenInter : IsOpen (⋂ i : ι, Pcond i) := isOpen_iInter_of_finite (fun i => hPopen i)
  obtain ⟨δP, hδPpos, hδPsub⟩ := Metric.isOpen_iff.mp hOpenInter s (Set.mem_iInter.mpr hsP)
  -- ## 3. the translated family
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
  -- ## 4. the richness of the translated family, from the richness at the centre `s`
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
      (hsm'.differentiableAt top_ne_zero_m3hops).hasFDerivAt
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
  -- ## 5. the localized Sard at the translated base
  obtain ⟨τ, hτ, hM⟩ := localSard (M := CappingSpace) (m := 12) Gs hGs_sm hGs_slice
    hGs_seam hGs_surj ετ hετpos
  -- ## 6. the conclusion
  refine ⟨s + τ, ?_, ?_, ?_⟩
  · have h1 : ‖τ‖ < (ε' - ‖s‖) / 2 := lt_of_lt_of_le hτ hετ_ε'
    calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
      _ < ‖s‖ + (ε' - ‖s‖) / 2 := by linarith
      _ < ε' := by linarith
  · have hM' : Meet3Hyp CappingSpace (G (s + τ)) := by simpa only [Gs] using hM
    rwa [hGfun (s + τ)] at hM'
  · intro i
    have hmem : s + τ ∈ ⋂ i : ι, Pcond i := hδPsub (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact lt_of_lt_of_le hτ hετ_δP)
    exact Set.mem_iInter.mp hmem i

end

/-- `Work.Drive.exists_meet3Hyp_and_good_pairFam_rot_local` with an arbitrary finite family of extra
*open* conditions that are dense in the unit ball, all met by the same parameter `t` (item §5 P3 of
the project lead's `NOTES_LEAD_hdense.md`).  The `Meet3Hyp` conjunct is written in the `@`-form with
the concrete instances `Work.Drive.cappingCharted`, `Work.Drive.isManifold_cappingCharted`: the
version carrying `[ChartedSpace ...] [IsManifold ...]` *instance binders* is FALSE, because those
binders introduce an arbitrary smooth structure on `CappingSpace` while `IsChartData`, `ChartPert`,
`rotPresentation`, `sweepChartFam`, `GoodAt` and all the available genericity results are pinned to
the concrete structure. -/
theorem exists_meet3Hyp_rot_local_of_opensN
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (hΞ : Work.Drive.ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (u : Fin 3 → UnitAddCircle)
    {ι : Type} [Countable ι] [Finite ι]
    (c' : ι → ℝ) (w : ι → UnitAddCircle)
    (φ : ι → EuclideanSpace ℝ (Fin 12) →L[ℝ]
      (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)))
    (hφ : ∀ i : ι, Function.Surjective (φ i))
    {ι' : Type} [Countable ι'] [Finite ι']
    (A : ι' → Set (EuclideanSpace ℝ (Fin 12)))
    (hAopen : ∀ i : ι', IsOpen (A i))
    (hAdense : ∀ i : ι', ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ A i ∧ ‖y - x‖ < δ) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        @Work.Drive.Meet3Hyp Work.Drive.CappingSpace _ Work.Drive.cappingCharted
          Work.Drive.isManifold_cappingCharted
          (Work.Drive.sweepChartFam (fun j => Work.Drive.rotPresentation Q (u j)) Ξ c t) ∧
        (∀ i : ι, Work.Drive.GoodAt Ξ Q (c' i) (w i) (φ i t)) ∧
        (∀ i : ι', t ∈ A i) := by
  intro ε' hε'
  classical
  -- ## 1. the pair conditions are open and dense in the parameter
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
  let B : ι → Set (EuclideanSpace ℝ (Fin 12)) := fun i => {t | GoodAt Ξ Q (c' i) (w i) (φ i t)}
  have hBopen : ∀ i : ι, IsOpen (B i) := by
    intro i
    rw [show B i = (φ i) ⁻¹' {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
        GoodAt Ξ Q (c' i) (w i) q} from rfl]
    exact IsOpen.preimage (φ i).continuous (hOpenPair (c' i) (w i))
  have hBdense : ∀ i : ι, Dense (B i) := by
    intro i
    have hopenmap : IsOpenMap (φ i) := ContinuousLinearMap.isOpenMap (φ i) (hφ i)
    rw [show B i = (φ i) ⁻¹' {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
        GoodAt Ξ Q (c' i) (w i) q} from rfl]
    exact (hDensePair (c' i) (w i)).preimage hopenmap
  -- ## 2. the combined finite family of open-dense conditions
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype ι' := Fintype.ofFinite ι'
  let Pcond : (ι ⊕ ι') → Set (EuclideanSpace ℝ (Fin 12)) := fun i => match i with
    | Sum.inl a => B a
    | Sum.inr a => A a
  have hPopen : ∀ i : ι ⊕ ι', IsOpen (Pcond i) := by
    rintro (i | i)
    · exact hBopen i
    · exact hAopen i
  have hPdense : ∀ i : ι ⊕ ι', ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ Pcond i ∧ ‖y - x‖ < δ := by
    rintro (i | i) x hx δ hδ
    · obtain ⟨y, hyball, hy⟩ := Metric.dense_iff.mp (hBdense i) x δ hδ
      exact ⟨y, hy, by rw [Metric.mem_ball, dist_eq_norm] at hyball; exact hyball⟩
    · exact hAdense i x hx δ hδ
  -- ## 3. the localized genericity at the combined family
  obtain ⟨t, ht, hmeet, hall⟩ :=
    exists_meet3Hyp_rot_local_of_openDenseN hQ Ξ hΞ c hc hcdist u Pcond hPopen hPdense ε' hε'
  exact ⟨t, ht, hmeet, fun i => hall (Sum.inl i), fun i => hall (Sum.inr i)⟩

end Work.Drive
