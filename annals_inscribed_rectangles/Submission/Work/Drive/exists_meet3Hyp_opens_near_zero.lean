import Mathlib
import Submission.Work.Drive.exists_meet3Hyp_opens
import Submission.Work.Drive.chartIsSmooth

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted Work.Drive.t2Space_cappingSpace Work.Drive.projCharted
/-- **The localized genericity of the reference triple inside a prescribed open *accumulating at
zero* set.**

Same conclusion as `Work.Drive.exists_meet3Hyp_opens`, but the prescribed open set `A ⊆ 𝔼¹²` is only
required to meet every ball around the origin (`hA0`) instead of being dense everywhere: the two
ordered-pair `GoodAt` conditions are open *and* dense in the parameter `t`, so a point of `A`
arbitrarily close to `0` can be adjusted (inside the small ball around it that `A` contains) to lie
in both of them, and the localized parametric Sard `Work.Drive.localSard_family_in_open` then
produces the parameter, inside `A`, with all the required properties. -/
theorem exists_meet3Hyp_opens_near_zero {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsChartData Q) (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace) (hΞ : Work.Drive.ChartPert Q 4 Ξ) (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k) (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (u v : UnitAddCircle) (R : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace) (hR : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) R) (hRseam : ∀ y : EuclideanSpace ℝ (Fin 2), Work.Drive.onSeam2 y → R y = R (Work.Drive.seamInv2 y)) (hrich : ∀ (p : Work.Drive.CappingSpace) (K : Set (EuclideanSpace ℝ (Fin 9))) (t₀ : EuclideanSpace ℝ (Fin 12)) (δ : ℝ), IsCompact K → 0 < δ → (∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t - t₀‖ < δ → y ∈ K → ∀ k : Fin 3, Work.Drive.sweepChartFam ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t k ((Work.Drive.TParity.bPartC k) y) ∈ (Work.Drive.chr p).source) → ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t - t₀‖ < δ → y ∈ K → Work.Drive.TParity.chartDiff3 p (Work.Drive.sweepChartFam ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t) y = 0 → Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) => Work.Drive.TParity.chartDiff3 p (Work.Drive.sweepChartFam ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t') y) t)) (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A) (hA0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t‖ < δ) (ε' : ℝ) (hε' : 0 < ε') : ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧ t ∈ A ∧ Work.Drive.Meet3Hyp Work.Drive.CappingSpace (Work.Drive.sweepChartFam ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t) ∧ Work.Drive.GoodAt Ξ Q (c 1) (v - u) (Work.Drive.blk 0 t, Work.Drive.blk 1 t) ∧ Work.Drive.GoodAt Ξ Q (c 0) (u - v) (Work.Drive.blk 1 t, Work.Drive.blk 0 t) := by

  classical
  -- ## 1. the reference triple `(rotPresentation Q u, rotPresentation Q v, R)`
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
  -- ## 2. the family of chart-perturbed clamped sweeps
  let G : Unit → EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun _ t k x => sweepChartFam P Ξ c t k x
  have hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2) :=
    fun k' => contMDiff_sweepChartSlice_of_family hΞ hP c k'
  have hG : ∀ (j : Unit) (k : Fin 3), ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => G j q.1 k q.2) := by
    intro j k
    simpa only [G] using contMDiff_sweepChartFam P Ξ c hslice k
  have hsmooth : ∀ (j : Unit) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3),
      ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (G j t k) := by
    intro j t k
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ((t, x) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := (hG j k).comp (contMDiff_iff_contDiff.mpr hφ)
    simpa only [Function.comp_def, G] using hcomp
  have hseam : ∀ (j : Unit) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)), onSeam x → G j t k x = G j t k (seamInv x) := by
    intro j t k x hx
    have hinst : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
        (fun z => Ξ (blk k t) (P k z)) y = (fun z => Ξ (blk k t) (P k z)) (seamInv2 y) :=
      fun y hy => congrArg (Ξ (blk k t)) (hPseam k y hy)
    have h := clampedSweep_seamInv (c k) (fun r => 1 - r)
      (fun z => Ξ (blk k t) (P k z)) hinst x hx
    simpa only [G, sweepChartFam_apply, Function.comp_def] using h
  -- ## 3. the richness hypothesis, in the shape the localized Sard consumes
  have hrichG : ∀ (j : Unit) (p : CappingSpace) (K : Set (EuclideanSpace ℝ (Fin 9)))
      (t₀ : EuclideanSpace ℝ (Fin 12)) (δ : ℝ), IsCompact K → 0 < δ →
      (∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y ∈ K → ∀ k : Fin 3,
          G j t k (TParity.bPartC k y) ∈ (chr p).source) →
      ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y ∈ K →
        TParity.chartDiff3 p (G j t) y = 0 →
        Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G j t') y) t) := by
    intro j p K t₀ δ hK hδ hcont t y ht hy hz
    refine hrich p K t₀ δ hK hδ ?_ t y ht hy ?_
    · intro t' y' ht' hy' k
      have h := hcont t' y' ht' hy' k
      simpa only [G, P] using h
    · have h := hz
      simpa only [G, P] using h
  -- ## 4. the two pair conditions are open and dense in the parameter
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
    refine ⟨(x.1 + dp, x.2), ?_, hg⟩
    have h1 : dist (x.1 + dp) x.1 = ‖dp‖ := by rw [dist_eq_norm]; congr 1; abel
    have h2 : dist x.2 x.2 = 0 := dist_self _
    have hd : dist ((x.1 + dp, x.2) : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))
        (x.1, x.2) = ‖dp‖ := by
      rw [Prod.dist_eq, h1, h2, max_eq_left (norm_nonneg dp)]
    rw [Metric.mem_ball, hd]
    exact hdp
  -- the two block projections are onto, hence open maps
  have hblk₁ : Function.Surjective ((blk 0).prod (blk 1)) := by
    rintro ⟨x, y⟩
    refine ⟨blkSpan 0 x + blkSpan 1 y, ?_⟩
    have h1 : blk 0 (blkSpan 0 x + blkSpan 1 y) = x := by
      rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 1) (j := 0) (by decide), add_zero]
    have h2 : blk 1 (blkSpan 0 x + blkSpan 1 y) = y := by
      rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 0) (j := 1) (by decide), zero_add]
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext h1 h2
  have hblk₂ : Function.Surjective ((blk 1).prod (blk 0)) := by
    rintro ⟨x, y⟩
    refine ⟨blkSpan 1 x + blkSpan 0 y, ?_⟩
    have h1 : blk 1 (blkSpan 1 x + blkSpan 0 y) = x := by
      rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 0) (j := 1) (by decide), add_zero]
    have h2 : blk 0 (blkSpan 1 x + blkSpan 0 y) = y := by
      rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 1) (j := 0) (by decide), zero_add]
    rw [ContinuousLinearMap.prod_apply]
    exact Prod.ext h1 h2
  -- the pullbacks of the two pair conditions at the blocks
  let S₁ : Set (EuclideanSpace ℝ (Fin 12)) :=
    {t | GoodAt Ξ Q (c 1) (v - u) (blk 0 t, blk 1 t)}
  let S₂ : Set (EuclideanSpace ℝ (Fin 12)) :=
    {t | GoodAt Ξ Q (c 0) (u - v) (blk 1 t, blk 0 t)}
  have hS₁open : IsOpen S₁ := by
    rw [show S₁ = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 0 t, blk 1 t)) ⁻¹'
        {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 1) (v - u) q} from rfl]
    exact IsOpen.preimage ((blk 0).continuous.prodMk (blk 1).continuous)
      (hOpenPair (c 1) (v - u))
  have hS₂open : IsOpen S₂ := by
    rw [show S₂ = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 1 t, blk 0 t)) ⁻¹'
        {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 0) (u - v) q} from rfl]
    exact IsOpen.preimage ((blk 1).continuous.prodMk (blk 0).continuous)
      (hOpenPair (c 0) (u - v))
  have hS₁dense : Dense S₁ := by
    rw [show S₁ = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 0 t, blk 1 t)) ⁻¹'
        {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 1) (v - u) q} from rfl]
    exact (hDensePair (c 1) (v - u)).preimage
      (ContinuousLinearMap.isOpenMap ((blk 0).prod (blk 1)) hblk₁)
  have hS₂dense : Dense S₂ := by
    rw [show S₂ = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 1 t, blk 0 t)) ⁻¹'
        {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 0) (u - v) q} from rfl]
    exact (hDensePair (c 0) (u - v)).preimage
      (ContinuousLinearMap.isOpenMap ((blk 1).prod (blk 0)) hblk₂)
  -- ## 5. the open set `O` of the localized Sard application
  let O : Set (EuclideanSpace ℝ (Fin 12)) := A ∩ S₁ ∩ S₂
  have hOopen : IsOpen O := (hAopen.inter hS₁open).inter hS₂open
  have hS₁₂dense : Dense (S₁ ∩ S₂) := hS₁dense.inter_of_isOpen_right hS₂dense hS₂open
  -- `A` accumulates at `0` and is open, so a small ball around a point of `A` near `0`
  -- meets the dense open set `S₁ ∩ S₂`; that point lies in `O` and is still close to `0`.
  have hO0 : ∀ ε : ℝ, 0 < ε → ∃ t ∈ O, ‖t‖ < ε := by
    intro ε hε
    obtain ⟨t₀, ht₀A, ht₀ε⟩ := hA0 (ε / 2) (by linarith)
    obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (hAopen.mem_nhds ht₀A)
    obtain ⟨t, htball, htS⟩ :=
      Metric.dense_iff.mp hS₁₂dense t₀ (min (ε / 2) r) (lt_min (by linarith) hrpos)
    rw [Metric.mem_ball] at htball
    refine ⟨t, ?_, ?_⟩
    · exact ⟨⟨hrsub (Metric.mem_ball.mpr (lt_of_lt_of_le htball (min_le_right _ _))), htS.1⟩, htS.2⟩
    · have h1 : ‖t‖ ≤ dist t t₀ + ‖t₀‖ := by
        have h := norm_add_le (t - t₀) t₀
        rw [sub_add_cancel] at h
        rw [dist_eq_norm]
        exact h
      have h2 : dist t t₀ < ε / 2 := lt_of_lt_of_le htball (min_le_left _ _)
      linarith

  -- ## 7. the localized parametric Sard
  obtain ⟨t, htO, htε, hmeet⟩ :=
    localSard_family_in_open (fun _ : Unit => CappingSpace) G hG hsmooth hseam hrichG
      O hOopen hO0 ε' hε'
  refine ⟨t, htε, htO.1.1, ?_, htO.1.2, htO.2⟩
  simpa only [G, P] using hmeet ()


end Work.Drive
