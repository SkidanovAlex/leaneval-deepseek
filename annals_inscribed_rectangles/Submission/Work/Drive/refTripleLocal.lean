import Mathlib
import Submission.Work.Drive.refTripleGeneric
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.localSard

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 40000000
set_option linter.style.haveILetI false

noncomputable section

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_refTripleLocal : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **The joint genericity of the reference triple, without the chart-containment hypothesis `hloc`.**

This is `Work.Drive.exists_meet3Hyp_and_goodAt_refTriple` (`refTripleGeneric.lean`) with its hypothesis
`∃ p, ∀ y ∈ unitBox 8, meet3 (G 0) y → ∀ k, G 0 k (bPartC k y) ∈ (chr p).source` — a *single* chart
containing the whole base triple locus, which is not provable for the capping space
(`Submission/Work/Drive/CHART_SOURCE_OPACITY.md`) — replaced by the *richness* hypothesis `hrich` of the
localized Sard `Work.Drive.localSard`.  Unlike `localSard`'s own (centre-`0`) hypothesis, `hrich` is
stated with an arbitrary centre `t₀`, which is what makes it *inherited* by the translated families
`τ ↦ G (t₀ + τ)` used to move the base parameter (containment on `B(0,δ)` for the shifted family *is*
containment on `B(t₀,δ)` for `G`).

The conclusion is unchanged: for every `ε' > 0` there is a parameter `t` of norm `< ε'` at which the
perturbed reference triple satisfies `Meet3Hyp`, and *the same* `t` makes the two ordered pairs `(0,1)`
and `(1,0)` good for the chart perturbation (`GoodAt`), which is what the antisymmetry assembly
`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine` consumes.

Proof plan: the pair-goodness conditions are open and dense on the parameter space
(`Work.Drive.goodPair_pertChart_isOpen`, `Work.Drive.goodPair_pertChart_exists_near`); take a parameter
`t₀` of small norm at which they hold; from `hrich` at the centre `t₀` derive the centre-`0` richness of
the translated family `τ ↦ G (t₀ + τ)` (the derivative of the shift is the identity), apply
`Work.Drive.localSard` to it, and obtain `τ` arbitrarily small with `Meet3Hyp (G (t₀ + τ))`; by openness
of the pair-goodness conditions at `t₀`, the same `t = t₀ + τ` keeps them. -/
theorem refTripleLocal
    {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (hΞ : Work.Drive.ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (u v : UnitAddCircle)
    (R : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hR : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) R)
    (hRseam : ∀ y : EuclideanSpace ℝ (Fin 2),
      Work.Drive.onSeam2 y → R y = R (Work.Drive.seamInv2 y))
    (hrich : ∀ (p : Work.Drive.CappingSpace) (K : Set (EuclideanSpace ℝ (Fin 9)))
      (t₀ : EuclideanSpace ℝ (Fin 12)) (δ : ℝ), IsCompact K → 0 < δ →
      (∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t - t₀‖ < δ → y ∈ K →
        ∀ k : Fin 3,
          Work.Drive.sweepChartFam
            ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t k
            (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source) →
      ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t - t₀‖ < δ → y ∈ K →
        Work.Drive.TParity.chartDiff3 p
          (Work.Drive.sweepChartFam
            ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t) y = 0 →
        Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          Work.Drive.TParity.chartDiff3 p
            (Work.Drive.sweepChartFam
              ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t') y) t)) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Work.Drive.Meet3Hyp Work.Drive.CappingSpace
          (Work.Drive.sweepChartFam
            ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t) ∧
        Work.Drive.GoodAt Ξ Q (c 1) (v - u) (Work.Drive.blk 0 t, Work.Drive.blk 1 t) ∧
        Work.Drive.GoodAt Ξ Q (c 0) (u - v) (Work.Drive.blk 1 t, Work.Drive.blk 0 t) := by
  intro ε' hε'
  classical
  -- ## 0. notation: the reference triple and its family of triples
  let P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    ![rotPresentation Q u, rotPresentation Q v, R]
  have hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k) := by
    intro k
    fin_cases k
    · simpa [P] using contMDiff_rotPresentation Q u (contMDiff_diskPlane (Q := Q) hQ.1)
    · simpa [P] using contMDiff_rotPresentation Q v (contMDiff_diskPlane (Q := Q) hQ.1)
    · simpa [P] using hR
  have hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P k y = P k (seamInv2 y) := by
    intro k y hy
    fin_cases k
    · simpa [P] using rotPresentation_seamInv Q hQ.2 u y hy
    · simpa [P] using rotPresentation_seamInv Q hQ.2 v y hy
    · simpa [P] using hRseam y hy
  let G : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun t k x => sweepChartFam P Ξ c t k x
  have hGeq : ∀ t : EuclideanSpace ℝ (Fin 12),
      G t = sweepChartFam ![rotPresentation Q u, rotPresentation Q v, R] Ξ c t := by
    intro t
    funext k x
    simp only [G, P]
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
  -- ## 1. the two pair goodness conditions are open and dense
  have hOpenPair : ∀ (c' : ℝ) (w : UnitAddCircle),
      IsOpen {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) | GoodAt Ξ Q c' w q} :=
    fun c' w => goodPair_pertChart_isOpen (Ξ := Ξ) (Q := Q) hΞ hQ.1 c' w
  have hDensePair : ∀ (c' : ℝ) (w : UnitAddCircle),
      Dense {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) | GoodAt Ξ Q c' w q} := by
    intro c' w
    rw [Metric.dense_iff]
    intro x r hr
    obtain ⟨dp, hdp, hg⟩ :=
      goodPair_pertChart_exists_near (Ξ := Ξ) (Q := Q) hΞ hQ.1 c' w x.1 x.2 r hr
    refine ⟨(x.1 + dp, x.2), ⟨?_, hg⟩⟩
    have h1 : dist (x.1 + dp) x.1 = ‖dp‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    have h2 : dist x.2 x.2 = 0 := dist_self _
    have hd : dist ((x.1 + dp, x.2) : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))
        (x.1, x.2) = ‖dp‖ := by
      rw [Prod.dist_eq, h1, h2, max_eq_left (norm_nonneg dp)]
    rw [Metric.mem_ball, hd]
    exact hdp
  -- the two pair conditions at the parameters of the blocks `0`, `1`
  let A : Set (EuclideanSpace ℝ (Fin 12)) :=
    {t | GoodAt Ξ Q (c 1) (v - u) (blk 0 t, blk 1 t)}
  let B : Set (EuclideanSpace ℝ (Fin 12)) :=
    {t | GoodAt Ξ Q (c 0) (u - v) (blk 1 t, blk 0 t)}
  have hAopen : IsOpen A := by
    rw [show A = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 0 t, blk 1 t)) ⁻¹'
        {q' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 1) (v - u) q'} from rfl]
    exact IsOpen.preimage (((blk 0).continuous.prodMk (blk 1).continuous))
      (hOpenPair (c 1) (v - u))
  have hBopen : IsOpen B := by
    rw [show B = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 1 t, blk 0 t)) ⁻¹'
        {q' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 0) (u - v) q'} from rfl]
    exact IsOpen.preimage (((blk 1).continuous.prodMk (blk 0).continuous))
      (hOpenPair (c 0) (u - v))
  have hAdense : Dense A := by
    have hsurj : Function.Surjective ((blk 0).prod (blk 1)) := by
      rintro ⟨x, y⟩
      refine ⟨blkSpan 0 x + blkSpan 1 y, ?_⟩
      have h1 : blk 0 (blkSpan 0 x + blkSpan 1 y) = x := by
        rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 1) (j := 0) (by decide), add_zero]
      have h2 : blk 1 (blkSpan 0 x + blkSpan 1 y) = y := by
        rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 0) (j := 1) (by decide), zero_add]
      rw [ContinuousLinearMap.prod_apply]
      exact Prod.ext h1 h2
    have hopen : IsOpenMap (fun t : EuclideanSpace ℝ (Fin 12) => (blk 0 t, blk 1 t)) :=
      ContinuousLinearMap.isOpenMap ((blk 0).prod (blk 1)) hsurj
    rw [show A = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 0 t, blk 1 t)) ⁻¹'
        {q' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 1) (v - u) q'} from rfl]
    exact (hDensePair (c 1) (v - u)).preimage hopen
  have hBdense : Dense B := by
    have hsurj : Function.Surjective ((blk 1).prod (blk 0)) := by
      rintro ⟨x, y⟩
      refine ⟨blkSpan 1 x + blkSpan 0 y, ?_⟩
      have h1 : blk 1 (blkSpan 1 x + blkSpan 0 y) = x := by
        rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 0) (j := 1) (by decide), add_zero]
      have h2 : blk 0 (blkSpan 1 x + blkSpan 0 y) = y := by
        rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 1) (j := 0) (by decide), zero_add]
      rw [ContinuousLinearMap.prod_apply]
      exact Prod.ext h1 h2
    have hopen : IsOpenMap (fun t : EuclideanSpace ℝ (Fin 12) => (blk 1 t, blk 0 t)) :=
      ContinuousLinearMap.isOpenMap ((blk 1).prod (blk 0)) hsurj
    rw [show B = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 1 t, blk 0 t)) ⁻¹'
        {q' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 0) (u - v) q'} from rfl]
    exact (hDensePair (c 0) (u - v)).preimage hopen
  have hOpenInter : IsOpen (A ∩ B) := hAopen.inter hBopen
  have hDenseInter : Dense (A ∩ B) := hAdense.inter_of_isOpen_right hBdense hBopen
  -- ## 2. a small base parameter `s` at which both pair conditions hold
  have hε'4 : 0 < ε' / 4 := by linarith
  obtain ⟨s, hsPair, hsnorm⟩ : ∃ s : EuclideanSpace ℝ (Fin 12), s ∈ A ∩ B ∧ ‖s‖ < ε' / 4 := by
    rw [Metric.dense_iff] at hDenseInter
    obtain ⟨s, hs, hsd⟩ := hDenseInter 0 (ε' / 4) hε'4
    exact ⟨s, hsd, by rwa [Metric.mem_ball, dist_zero_right] at hs⟩
  obtain ⟨δP, hδPpos, hδPsub⟩ := Metric.isOpen_iff.mp hOpenInter s hsPair
  -- ## 3. the translated family `τ ↦ G (s + τ)`
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
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ((s + τ, x) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := (hGsm k).comp (contMDiff_iff_contDiff.mpr hφ)
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
  -- ## 4. the richness of the translated family, from `hrich` at the centre `s`
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
          sweepChartFam ![rotPresentation Q u, rotPresentation Q v, R] Ξ c t k
            (TParity.bPartC k y') ∈ (chr p).source := by
      intro t y' ht hy' k
      have hswap : Gs (t - s) = G t := by
        funext k x
        simp only [Gs, G]
        rw [show s + (t - s) = t by abel]
      have h := hcont (t - s) y' ht hy' k
      rw [hswap] at h
      rwa [hGeq t] at h
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
      (hsm'.differentiableAt top_ne_zero_refTripleLocal).hasFDerivAt
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
    simpa only [hGeq] using hsurj
  -- ## 5. the localized Sard at the translated base
  obtain ⟨τ, hτ, hM⟩ := localSard (M := CappingSpace) (m := 12) Gs hGs_sm hGs_slice
    hGs_seam hGs_surj ετ hετpos
  -- ## 6. the conclusion
  refine ⟨s + τ, ?_, ?_, ?_, ?_⟩
  · have h1 : ‖τ‖ < (ε' - ‖s‖) / 2 := lt_of_lt_of_le hτ hετ_ε'
    calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
      _ < ‖s‖ + (ε' - ‖s‖) / 2 := by linarith
      _ < ε' := by linarith
  · have hM' : Meet3Hyp CappingSpace (G (s + τ)) := by simpa only [Gs] using hM
    rwa [hGeq (s + τ)] at hM'
  · have hmem : s + τ ∈ A ∩ B := hδPsub (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact lt_of_lt_of_le hτ hετ_δP)
    exact hmem.1
  · have hmem : s + τ ∈ A ∩ B := hδPsub (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact lt_of_lt_of_le hτ hετ_δP)
    exact hmem.2

end

end Work.Drive

