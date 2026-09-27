import Mathlib
import Submission.Work.Drive.analyticDensity
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.rowsOpen
import Submission.Work.Drive.sliceSard
import Submission.Work.Drive.pairReg_of_loopBoxData
import Submission.Work.Drive.endTripleRowOpen
import Submission.Work.Drive.pairRegRows
import Submission.Work.Drive.classRowsSweep_openDense

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartRowA :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Work.Drive.Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The residual (comeagre) form of the density clause -/

/-- **Density at the closed unit ball, in nowhere-dense form.**  If `R` is open and meets every ball
around every point of the closed unit ball, then the part of the complement of `R` that lies in the
closed unit ball is *nowhere dense* in `𝔼ⁿ` — equivalently, the good set is **residual** (comeagre) on
the closed ball.

(The naive form "`Rᶜ` is meagre in `𝔼ⁿ`" would be false: a set that is dense only on the ball may have
nonempty interior outside it.  It is the *intersection with the ball* that is nowhere dense, and this is
the sharp form: the argument below is that a ball `B (x, ε)` contained in `Rᶜ ∩ closedBall` would put
`x` in the closed unit ball, where the density clause produces a point of `R` inside `B (x, ε)`.) -/
theorem isNowhereDense_compl_inter_closedBall {n : ℕ} {R : Set (EuclideanSpace ℝ (Fin n))}
    (hR : IsOpen R) (hd : DenseAtBall R) :
    IsNowhereDense (Rᶜ ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  refine ((isClosed_compl_iff.mpr hR).inter Metric.isClosed_closedBall).isNowhereDense_iff.mpr ?_
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hxmem : x ∈ Rᶜ ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := interior_subset hx
  rw [mem_interior_iff_mem_nhds] at hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hx
  have hxle : ‖x‖ ≤ 1 := by
    have h1 : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := hxmem.2
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
  obtain ⟨y, hyR, hyx⟩ := hd x hxle ε hε
  have hyball : y ∈ Metric.ball x ε := by rwa [Metric.mem_ball, dist_eq_norm]
  exact (hball hyball).1 hyR

/-! ## The density of row A -/

/-- **Row A holds at a parameter arbitrarily close to every point of the closed unit ball.**

The loop of the `LoopBoxData` producer is the *shadow* of the fixed transported linear disk model
`diskPlane (linPlaneChart ((linBase A 0).trans (classEquiv ((blk 0) x))) cl hcl)`: its level is the
constant `lam`, so it satisfies the level band of the sweep producer.  The move is concentrated in
block `2` (the design's third perturbed plane), so that block `0` — hence the transported linear model
— is untouched, and the producer `Work.Drive.pairReg_lin_blockPlane_of_loopBoxData` converts the
resulting `LoopBoxData` into the row. -/
theorem rowA_pairReg_dense {Q : ℂ → CappingSpace} (hQsm : IsSmoothChart Q)
    {c : ℝ} (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (a c' : UnitAddCircle) (A : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < δ ∧
        PairReg (linTransClass (linBase A 0) ((blk 0) t) cl hcl)
          (designPertClass Q (designAngles a c' 2) t 2) := by
  intro x hx δ hδ
  -- ## the level data, bounded by `K`
  set K : ℝ := ‖x‖ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set lam : ℝ := c * Real.exp (-K) / 2 with hlamdef
  set c₂ : ℝ := c * Real.exp (-K) / 4 with hc₂def
  have hlampos : 0 < lam := by rw [hlamdef]; positivity
  have hc₂pos : 0 < c₂ := by rw [hc₂def]; positivity
  have hc₂lam : c₂ < lam := by rw [hc₂def, hlamdef]; linarith [Real.exp_pos (-K)]
  have hlamlt : lam < c * Real.exp (-K) := by rw [hlamdef]; linarith [Real.exp_pos (-K)]
  -- ## the loop: the shadow of the frozen transported linear disk model
  set Ψ : Eucl 3 ≃L[ℝ] Eucl 3 := (linBase A 0).trans (classEquiv ((blk 0) x)) with hΨ
  set A₀ : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun y => shadow lam hlampos (diskPlane (linPlaneChart Ψ cl hcl) y) with hA₀def
  have hA₀sm : SmoothPlane₂ A₀ := by
    rw [hA₀def]
    exact (contMDiff_shadow lam hlampos).comp
      (contMDiff_diskPlane (linPlaneChart_contMDiff Ψ cl hcl))
  have hA₀lev : ∀ u ∈ Submission.Drive.unitBox 1, c₂ < levelOf (A₀ u) := by
    intro u _
    rw [hA₀def]
    simp only [levelOf_shadow]
    exact hc₂lam
  -- ## the parametric Sard of the sweep producer
  set εp : ℝ := min (δ / 2) (1 / 2) with hεpdef
  have hεppos : 0 < εp := by rw [hεpdef]; positivity
  have hεpδ : εp ≤ δ / 2 := by rw [hεpdef]; exact min_le_left _ _
  have hεp1 : εp ≤ 1 / 2 := by rw [hεpdef]; exact min_le_right _ _
  obtain ⟨p, hp, hbox⟩ := exists_loopBoxData_of_small_shift_fam (ι := Unit) (m := 4)
    (fun _ : Unit => A₀) (fun _ => hA₀sm) c₂ hc₂pos (fun _ u hu => hA₀lev u hu)
    (fun s p' => chartPert s p') Q (isChartPert_chartPert Q) hQsm
    (designAngles a c' 2) ((blk 2) x) εp hεppos
  have hbox₀ := hbox ()
  -- ## the moved parameter
  set t₂ : EuclideanSpace ℝ (Fin 12) := x + blkSpan 2 p with ht₂def
  have ht₂b0 : (blk 0) t₂ = (blk 0) x := by
    rw [ht₂def, blk_add_blkSpan_crs]
    simp
  have ht₂b2 : (blk 2) t₂ = (blk 2) x + p := by
    rw [ht₂def, blk_add_blkSpan_crs]
    simp
  have ht₂K : ‖t₂‖ ≤ K := by
    have h1 : ‖t₂ - x‖ = ‖p‖ := by rw [ht₂def, add_sub_cancel_left, norm_blkSpan]
    have h2 : ‖t₂ - x‖ ≤ εp := le_of_lt (by rw [h1]; exact hp)
    have h3 : ‖t₂‖ ≤ ‖t₂ - x‖ + ‖x‖ := by
      have h := norm_add_le (t₂ - x) x
      rwa [sub_add_cancel] at h
    rw [hKdef]
    linarith
  -- ## the row at `t₂`
  have hpair : PairReg (linTransClass (linBase A 0) ((blk 0) t₂) cl hcl)
      (designPertClass Q (designAngles a c' 2) t₂ 2) := by
    have hlevlam : ∀ y : EuclideanSpace ℝ (Fin 2),
        lam < levelOf (blockPlane (fun s p' => chartPert s p') Q (designAngles a c')
          (fun k => (blk k) t₂) 2 y) := by
      intro y
      exact lt_levelOf_blockPresentation_K hcbot hlamlt (designAngles a c' 2) ht₂K 2 y
    have hbox' : LoopBoxData
        (fun w => shadow lam hlampos (diskPlane (linPlaneChart Ψ cl hcl) w))
        (clampedSweep c₂ (fun s : ℝ => 1 - s)
          (blockPlane (fun s p' => chartPert s p') Q (designAngles a c')
            (fun k => (blk k) t₂) 2)) := by
      have hpres : diskPlane (pertChart (fun s p' => chartPert s p')
            (fun z => rotCapping (designAngles a c' 2) (Q z)) ((blk 2) x + p))
          = blockPlane (fun s p' => chartPert s p') Q (designAngles a c')
            (fun k => (blk k) t₂) 2 := by
        funext y
        simp only [blockPlane, diskPlane, pertChart, rotPresentation]
        rw [ht₂b2]
      rw [hA₀def] at hbox₀
      rw [congrArg (fun P => clampedSweep c₂ (fun s : ℝ => 1 - s) P) hpres] at hbox₀
      exact hbox₀
    have h := pairReg_lin_blockPlane_of_loopBoxData (fun s p' => chartPert s p') Q
      (fun _ => Ψ) cl hcl (designAngles a c') (fun k => (blk k) t₂) 2
      (isChartPert_chartPert Q) hQsm c₂ hc₂pos lam hlampos hc₂lam hlevlam hbox'
    have hlt : linTransClass (linBase A 0) ((blk 0) t₂) cl hcl
        = planeClassMap (diskPlane (linPlaneChart Ψ cl hcl)) := by
      rw [ht₂b0, hΨ]
      rfl
    have hdp : designPertClass Q (designAngles a c' 2) t₂ 2
        = planeClassMap (blockPlane (fun s p' => chartPert s p') Q (designAngles a c')
            (fun k => (blk k) t₂) 2) := rfl
    rw [hlt, hdp]
    exact h
  -- ## the norm bound
  refine ⟨t₂, ?_, hpair⟩
  have h1 : ‖t₂ - x‖ ≤ εp := by
    rw [ht₂def, add_sub_cancel_left, norm_blkSpan]
    exact le_of_lt hp
  linarith

/-! **Row A of `Work.Drive.classRowsLin_openDense`** (see the review for this path): the pair
regularity of the *transported first linear model* against the *design's third perturbed plane*, on an
open set of design parameters dense at every point of the closed unit ball.

Route (all ingredients on disk): `PairReg` of two plane presentations on the box is exactly the
surjectivity of the charted pair-difference map at its zeros (`Work.Drive.rowPairDiff_surjective_iff`);
the *density* comes from the parametric Sard statement `Work.Drive.sliceSard_dense_open` (variables
`𝔼⁴` = the pair box, values `𝔼³`, `4 = 3 + 1`) whose richness hypothesis
(`fderiv` of the charted family onto at the zeros) is supplied by the parameter direction alone:
`Work.Drive.range_fderiv_chartAt_classMap_alive` (the class parameter `τ ↦ classMap τ c` is a
submersion onto `ℝP³`); the *openness* is `Work.Drive.eventually_boxPairRegG_at` (with the family
re-centred at the base parameter), and the passage box → all of `ℝ²` is
`Work.Drive.pairReg_of_boxPairReg_affRep` (all presentations involved are invariant under the affine
symmetries of the square).  Only `hQ` (smoothness of the design chart) and `a, c'` enter. -/
theorem rowA_linDesign_pairReg_openDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {c : ℝ} (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    (a c' : UnitAddCircle) (ha : a ∈ Work.Drive.Zc γ) (hc' : c' ∈ Work.Drive.Zc γ)
    (hac : a + c' ∈ Work.Drive.Zc γ)
    (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧ Work.Drive.DenseAtBall R ∧
      ∀ t ∈ R, Work.Drive.PairReg
        (Work.Drive.linTransClass (Work.Drive.linBase A 0) ((Work.Drive.blk 0) t) cl hcl)
        (Work.Drive.designPertClass Q (Work.Drive.designAngles a c' 2) t 2) := by
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  refine ⟨{t : EuclideanSpace ℝ (Fin 12) | Work.Drive.PairReg
      (Work.Drive.linTransClass (Work.Drive.linBase A 0) ((Work.Drive.blk 0) t) cl hcl)
      (Work.Drive.designPertClass Q (Work.Drive.designAngles a c' 2) t 2)}, ?_, ?_,
    fun t ht => ht⟩
  · exact isOpen_pairReg_linPert_er Q (contMDiff_diskPlane hQsm) (designAngles a c' 2)
      (linBase A 0) cl hcl
  · intro x hx δ hδ
    obtain ⟨t, ht, hrow⟩ :=
      rowA_pairReg_dense hQsm hc hcbot a c' A cl hcl x hx δ hδ
    exact ⟨t, hrow, ht⟩

/-! ## The residual form of row A -/

/-- **The residual (comeagre) form of row A.**  The parameters of the closed unit ball at which the
row *fails* form a nowhere dense — hence meagre — subset of `𝔼¹²`; equivalently the row holds at a
**comeagre** set of parameters on the ball.  This is the Baire-category form of the pair
`IsOpen ∧ DenseAtBall` proved above (`isOpen_pairReg_linPert_er` for the openness,
`rowA_pairReg_dense` for the density at every point of the closed unit ball), delivered in the shape
the downstream genericity arguments consume. -/
theorem rowA_bad_isMeagre {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {c : ℝ} (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (a c' : UnitAddCircle)
    (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    IsMeagre ({t : EuclideanSpace ℝ (Fin 12) |
        ¬ Work.Drive.PairReg
          (Work.Drive.linTransClass (Work.Drive.linBase A 0) ((Work.Drive.blk 0) t) cl hcl)
          (Work.Drive.designPertClass Q (Work.Drive.designAngles a c' 2) t 2)}
      ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 12)) 1) := by
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  have hGopen : IsOpen {t : EuclideanSpace ℝ (Fin 12) | Work.Drive.PairReg
      (Work.Drive.linTransClass (Work.Drive.linBase A 0) ((Work.Drive.blk 0) t) cl hcl)
      (Work.Drive.designPertClass Q (Work.Drive.designAngles a c' 2) t 2)} :=
    isOpen_pairReg_linPert_er Q (contMDiff_diskPlane hQsm) (designAngles a c' 2)
      (linBase A 0) cl hcl
  have hGdense : Work.Drive.DenseAtBall {t : EuclideanSpace ℝ (Fin 12) | Work.Drive.PairReg
      (Work.Drive.linTransClass (Work.Drive.linBase A 0) ((Work.Drive.blk 0) t) cl hcl)
      (Work.Drive.designPertClass Q (Work.Drive.designAngles a c' 2) t 2)} :=
    fun x hx δ hδ => by
      obtain ⟨t, ht, hrow⟩ := rowA_pairReg_dense hQsm hc hcbot a c' A cl hcl x hx δ hδ
      exact ⟨t, hrow, ht⟩
  exact (isNowhereDense_compl_inter_closedBall hGopen hGdense).isMeagre

end

end Work.Drive
