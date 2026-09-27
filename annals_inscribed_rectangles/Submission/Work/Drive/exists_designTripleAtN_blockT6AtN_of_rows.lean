import Mathlib
import Submission.Work.Drive.hdenseNodeVocab
import Submission.Work.Drive.hdenseNodeOpens
import Submission.Work.Drive.hdenseDesignData
import Submission.Work.Drive.hdenseBlockT6
import Submission.Work.Drive.isOpen_T6GenAtDBox_design
import Submission.Work.Drive.dense_T6GenAtDBox_design
import Submission.Work.Drive.blockT6Wrapper

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## The local interface lemmas of the `(E4)` producer

The two lemmas below are the two *bulk* inputs of the assembly; the first is delegated as
`Work.Drive.threeBlock_dense_point` (the margined iteration in the three block sets) and the second as
`Work.Drive.exists_meet3Hyp_and_cond_near_of_openDense` (the localized Sard at a base point).  They are
wrapped here so that the assembly can be written against a stable interface. -/

/-- The `0`-th coordinate of the `k`-th block of `v` is bounded by `‖v‖`. -/
private lemma blk_coord_abs_le (k : Fin 3) (v : EuclideanSpace ℝ (Fin 12)) :
    |(blk k v) 0| ≤ ‖v‖ := by
  have h : (blk k v) 0 = v.ofLp (blkIdx k ⟨0, by norm_num⟩) := blk_apply k v ⟨0, by norm_num⟩
  rw [h, ← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (p := 2) v (blkIdx k ⟨0, by norm_num⟩)

/-- A nearby point does not lower any block coordinate by more than the distance. -/
private lemma blk_coord_gt_of_dist {k : Fin 3} {x y : EuclideanSpace ℝ (Fin 12)} {δ : ℝ}
    (h : ‖y - x‖ < δ) : (blk k x) 0 - δ < (blk k y) 0 := by
  have hlin : (blk k y) 0 = (blk k x) 0 + (blk k (y - x)) 0 := by
    have h1 : blk k y = blk k x + blk k (y - x) := by rw [map_sub]; abel
    rw [h1]; rfl
  have hb : |(blk k (y - x)) 0| ≤ ‖y - x‖ := blk_coord_abs_le k (y - x)
  have h3 := (abs_lt.mp (lt_of_le_of_lt hb h)).1
  linarith

/-- A vector whose three block vectors are all `w` has `k`-th block `w`. -/
private lemma blk_sum_single (k : Fin 3) (w : EuclideanSpace ℝ (Fin 4)) :
    blk k (blkSpan 0 w + (blkSpan 1 w + blkSpan 2 w)) = w := by
  fin_cases k <;> simp [map_add, blk_blkSpan, blk_blkSpan_of_ne]

/-- **The three-block dense point**: for three open sets `A k` each dense at every point `x` of the
closed unit ball *at which the `k`-th block coordinate is nonnegative*, there is a point of norm `< ρ`
in all three. -/
private lemma threeBlocks_local
    (A : Fin 3 → Set (EuclideanSpace ℝ (Fin 12)))
    (hopen : ∀ k : Fin 3, IsOpen (A k))
    (hdense : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 12)), ‖x‖ ≤ 1 → 0 ≤ (blk k x) 0 →
      ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A k ∧ ‖y - x‖ < δ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ s : EuclideanSpace ℝ (Fin 12), ‖s‖ < ρ ∧ ∀ k : Fin 3, s ∈ A k := by
  classical
  -- ## the margin and the margined starting point
  set μ : ℝ := min (ρ / 8) (1 / 8) with hμdef
  have hμpos : 0 < μ := by rw [hμdef]; exact lt_min (by linarith) (by norm_num)
  have hμρ : μ ≤ ρ / 8 := by rw [hμdef]; exact min_le_left _ _
  have hμ1 : μ ≤ 1 / 8 := by rw [hμdef]; exact min_le_right _ _
  let e₀ : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single 0 (1 : ℝ)
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have hs₀ : ‖μ • e₀‖ = μ := by
    rw [norm_smul, he₀, mul_one, Real.norm_eq_abs, abs_of_pos hμpos]
  let x₀ : EuclideanSpace ℝ (Fin 12) :=
    blkSpan 0 (μ • e₀) + (blkSpan 1 (μ • e₀) + blkSpan 2 (μ • e₀))
  have he₀c : (μ • e₀) 0 = μ := by
    show (μ • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) 0 = μ
    simp
  have hx₀c : ∀ k : Fin 3, (blk k x₀) 0 = μ := by
    intro k
    have h : blk k x₀ = μ • e₀ := by
      show blk k (blkSpan 0 (μ • e₀) + (blkSpan 1 (μ • e₀) + blkSpan 2 (μ • e₀))) = μ • e₀
      exact blk_sum_single k (μ • e₀)
    rw [h, he₀c]
  have hx₀n : ‖x₀‖ ≤ 3 * μ := by
    have h1 : ‖x₀‖ ≤ ‖blkSpan 0 (μ • e₀)‖
        + ‖blkSpan 1 (μ • e₀) + blkSpan 2 (μ • e₀)‖ := by
      show ‖_ + _‖ ≤ _
      exact norm_add_le _ _
    have h2 : ‖blkSpan 1 (μ • e₀) + blkSpan 2 (μ • e₀)‖
        ≤ ‖blkSpan 1 (μ • e₀)‖ + ‖blkSpan 2 (μ • e₀)‖ := norm_add_le _ _
    simp only [norm_blkSpan, hs₀] at h1 h2
    linarith
  have hx₀le1 : ‖x₀‖ ≤ 1 := by linarith [hx₀n, hμ1]
  -- ## step `0`
  obtain ⟨y₀, hy₀A, hy₀d⟩ := hdense 0 x₀ hx₀le1 (by rw [hx₀c 0]; exact le_of_lt hμpos)
    (μ / 8) (by linarith)
  have hy₀c : ∀ j : Fin 3, μ - μ / 8 < (blk j y₀) 0 := by
    intro j
    have h := blk_coord_gt_of_dist (k := j) hy₀d
    rwa [hx₀c j] at h
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := Metric.isOpen_iff.mp (hopen 0) y₀ hy₀A
  have hy₀le1 : ‖y₀‖ ≤ 1 := by
    have h1 : ‖y₀‖ ≤ ‖x₀‖ + ‖y₀ - x₀‖ := by
      have := norm_add_le x₀ (y₀ - x₀)
      rwa [add_sub_cancel] at this
    linarith [hx₀n, le_of_lt hy₀d, hμ1]
  -- ## step `1`
  have h1c : 0 ≤ (blk 1 y₀) 0 := by linarith [hy₀c 1, hμpos]
  obtain ⟨y₁, hy₁A, hy₁d⟩ := hdense 1 y₀ hy₀le1 h1c (min (ρ₀ / 2) (μ / 8))
    (lt_min (by linarith) (by linarith))
  have hy₁A₀ : y₁ ∈ A 0 :=
    hρ₀sub (by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hy₁d, min_le_left (ρ₀ / 2) (μ / 8), hρ₀pos])
  have hy₁c : ∀ j : Fin 3, μ - μ / 8 - μ / 8 < (blk j y₁) 0 := by
    intro j
    have h := blk_coord_gt_of_dist (k := j) hy₁d
    have h2 : (min (ρ₀ / 2) (μ / 8)) ≤ μ / 8 := min_le_right _ _
    linarith [hy₀c j]
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ :=
    Metric.isOpen_iff.mp ((hopen 0).inter (hopen 1)) y₁ ⟨hy₁A₀, hy₁A⟩
  have hy₁le1 : ‖y₁‖ ≤ 1 := by
    have h1 : ‖y₁‖ ≤ ‖y₀‖ + ‖y₁ - y₀‖ := by
      have := norm_add_le y₀ (y₁ - y₀)
      rwa [add_sub_cancel] at this
    have h2 : ‖y₀‖ ≤ 3 * μ + μ / 8 := by
      have h3 : ‖y₀‖ ≤ ‖x₀‖ + ‖y₀ - x₀‖ := by
        have := norm_add_le x₀ (y₀ - x₀)
        rwa [add_sub_cancel] at this
      linarith [hx₀n, le_of_lt hy₀d]
    have h4 : ‖y₁ - y₀‖ < μ / 8 := lt_of_lt_of_le hy₁d (min_le_right _ _)
    linarith [hμ1]
  -- ## step `2`
  have h2c : 0 ≤ (blk 2 y₁) 0 := by linarith [hy₁c 2, hμpos]
  obtain ⟨y₂, hy₂A, hy₂d⟩ := hdense 2 y₁ hy₁le1 h2c (min (ρ₁ / 2) (μ / 8))
    (lt_min (by linarith) (by linarith))
  have hy₂A01 : y₂ ∈ A 0 ∧ y₂ ∈ A 1 :=
    hρ₁sub (by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hy₂d, min_le_left (ρ₁ / 2) (μ / 8), hρ₁pos])
  -- ## the conclusion
  refine ⟨y₂, ?_, ?_⟩
  · have hsplit : ‖y₂‖ ≤ ‖x₀‖ + ‖y₀ - x₀‖ + ‖y₁ - y₀‖ + ‖y₂ - y₁‖ := by
      have h1 : ‖y₂‖ ≤ ‖x₀ + (y₀ - x₀) + (y₁ - y₀)‖ + ‖y₂ - y₁‖ := by
        have h := norm_add_le (x₀ + (y₀ - x₀) + (y₁ - y₀)) (y₂ - y₁)
        have he : x₀ + (y₀ - x₀) + (y₁ - y₀) + (y₂ - y₁) = y₂ := by abel
        rwa [he] at h
      have h2 : ‖x₀ + (y₀ - x₀) + (y₁ - y₀)‖ ≤ ‖x₀‖ + ‖y₀ - x₀‖ + ‖y₁ - y₀‖ := by
        have h := norm_add_le (x₀ + (y₀ - x₀)) (y₁ - y₀)
        have h' := norm_add_le x₀ (y₀ - x₀)
        linarith
      linarith
    have h2b : ‖y₁ - y₀‖ < μ / 8 := lt_of_lt_of_le hy₁d (min_le_right _ _)
    have h3b : ‖y₂ - y₁‖ < μ / 8 := lt_of_lt_of_le hy₂d (min_le_right _ _)
    linarith [hsplit, hx₀n, hy₀d, hμρ]
  · intro k
    fin_cases k
    · exact hy₂A01.1
    · exact hy₂A01.2
    · exact hy₂A

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_sardNear : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **A finite family of open sets, each dense in a ball of radius `R` around `x₀`, has a common point
in every ball of radius `ε ≤ R` around `x₀`.**  The variant of `Work.Drive.exists_mem_all_of_isOpen_dense`
in which the density hypothesis is local around the base point (which is what one has for the block
sets `A_k`, whose density needs the half-space hypothesis `0 ≤ (blk k x) 0`). -/
private theorem exists_mem_all_near_of_isOpen_dense {m : ℕ} :
    ∀ (n : ℕ) (P : Fin n → Set (EuclideanSpace ℝ (Fin m)))
      (x₀ : EuclideanSpace ℝ (Fin m)) (R : ℝ), 0 < R →
      (∀ i, IsOpen (P i)) →
      (∀ i, ∀ x : EuclideanSpace ℝ (Fin m), ‖x - x₀‖ < R → ∀ ε : ℝ, 0 < ε →
        ∃ y, y ∈ P i ∧ ‖y - x‖ < ε) →
      ∀ ε : ℝ, 0 < ε → ε ≤ R → ∃ t, ‖t - x₀‖ < ε ∧ ∀ i, t ∈ P i := by
  intro n
  induction n with
  | zero =>
      intro P x₀ R _ _ _ ε hε _
      exact ⟨x₀, by simpa using hε, fun i => i.elim0⟩
  | succ n ih =>
      intro P x₀ R hR hopen hdense ε hε hεR
      obtain ⟨t, ht, htmem⟩ := ih (fun i : Fin n => P i.castSucc) x₀ R hR
        (fun i => hopen _) (fun i => hdense _) ε hε hεR
      have hneigh : (⋂ i : Fin n, P i.castSucc) ∈ 𝓝 t := by
        rw [Filter.iInter_mem]
        exact fun i => (hopen _).mem_nhds (htmem i)
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hneigh
      obtain ⟨s, hsmem, hs⟩ := hdense (Fin.last n) t (lt_of_lt_of_le ht hεR)
        (min δ (ε - ‖t - x₀‖)) (lt_min hδpos (by linarith))
      have hnorm : ‖s - x₀‖ ≤ ‖s - t‖ + ‖t - x₀‖ := by
        have h := norm_add_le (s - t) (t - x₀)
        rwa [show s - t + (t - x₀) = s - x₀ by abel] at h
      have hlt : ‖s - t‖ < ε - ‖t - x₀‖ := lt_of_lt_of_le hs (min_le_right _ _)
      refine ⟨s, by linarith, fun i => ?_⟩
      refine Fin.lastCases hsmem (fun j => ?_) i
      have hmem : s ∈ ⋂ i : Fin n, P i.castSucc := hδsub (by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le hs (min_le_left _ _))
      exact Set.mem_iInter.mp hmem j

/-- **The localized Sard at a base point**: the localized genericity of the design's rotated triple
with a finite family of open conditions dense at every point of the closed unit ball, *based at an
arbitrary point `m` of the unit ball*, and keeping a second finite family of open conditions holding at
`m`. -/
private lemma sardNear_local
    {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (u : Fin 3 → UnitAddCircle)
    {ι : Type} [Finite ι]
    (Pcond : ι → Set (EuclideanSpace ℝ (Fin 12)))
    (hPopen : ∀ i : ι, IsOpen (Pcond i))
    (hPdense : ∀ i : ι, ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ Pcond i ∧ ‖y - x‖ < δ)
    {κ : Type} [Finite κ] (A : κ → Set (EuclideanSpace ℝ (Fin 12)))
    (hAopen : ∀ k : κ, IsOpen (A k))
    (m : EuclideanSpace ℝ (Fin 12)) (hmA : ∀ k : κ, m ∈ A k) (hm1 : ‖m‖ < 1)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - m‖ < ε' ∧
      @Meet3Hyp CappingSpace _ cappingCharted isManifold_cappingCharted
        (sweepChartFam (fun j => rotPresentation Q (u j)) Ξ c t) ∧
      (∀ i : ι, t ∈ Pcond i) ∧ (∀ k : κ, t ∈ A k) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype κ := Fintype.ofFinite κ
  let P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace := fun j => rotPresentation Q (u j)
  have hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k) :=
    fun k => contMDiff_rotPresentation Q (u k) (contMDiff_diskPlane (Q := Q) hQ.1)
  have hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P k y = P k (seamInv2 y) :=
    fun k y hy => rotPresentation_seamInv Q hQ.2 (u k) y hy
  let G : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun t k x => sweepChartFam P Ξ c t k x
  have hGfun : ∀ t : EuclideanSpace ℝ (Fin 12),
      G t = sweepChartFam (fun j => rotPresentation Q (u j)) Ξ c t := fun t => rfl
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
  -- ## 1. a point `s` near `m` satisfying all the conditions
  have hAint : IsOpen (⋂ k : κ, A k) := isOpen_iInter_of_finite (fun k => hAopen k)
  obtain ⟨δA, hδApos, hδAsub⟩ :=
    Metric.isOpen_iff.mp hAint m (Set.mem_iInter.mpr hmA)
  set Rm : ℝ := (1 - ‖m‖) / 2 with hRmdef
  have hRmpos : 0 < Rm := by rw [hRmdef]; linarith
  set εs : ℝ := min (δA / 2) (min (ε' / 4) (Rm / 2)) with hεsdef
  have hεspos : 0 < εs := by
    rw [hεsdef]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hεs_le : εs ≤ Rm := by
    rw [hεsdef]
    have h1 : min (δA / 2) (min (ε' / 4) (Rm / 2)) ≤ Rm / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith [hRmpos]
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hdens' : ∀ i : ι, ∀ x : EuclideanSpace ℝ (Fin 12), ‖x - m‖ < Rm → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ Pcond i ∧ ‖y - x‖ < δ := by
    intro i x hx δ hδ
    refine hPdense i x ?_ δ hδ
    have h1 : ‖x‖ ≤ ‖m‖ + ‖x - m‖ := by
      have h := norm_add_le m (x - m)
      rwa [add_sub_cancel] at h
    rw [hRmdef] at hx
    linarith
  obtain ⟨s, hsε, hsPl⟩ := exists_mem_all_near_of_isOpen_dense (m := 12) (Fintype.card ι)
    (fun n => Pcond (eι.symm n)) m Rm hRmpos (fun n => hPopen _)
    (fun n x hx δ hδ => hdens' _ x hx δ hδ) εs hεspos hεs_le
  have hsP : ∀ i : ι, s ∈ Pcond i := fun i => by
    simpa only [Equiv.symm_apply_apply] using hsPl (eι i)
  have hsm : s ∈ Metric.ball m δA := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : εs ≤ δA / 2 := by rw [hεsdef]; exact min_le_left _ _
    linarith
  have hsA : ∀ k : κ, s ∈ A k := fun k => Set.mem_iInter.mp (hδAsub hsm) k
  have hsε' : ‖s - m‖ < ε' / 4 := by
    have h1 : εs ≤ ε' / 4 := by
      rw [hεsdef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  -- ## 2. the translated family and the localized Sard call at `s`
  have hOopen : IsOpen ((⋂ i : ι, Pcond i) ∩ (⋂ k : κ, A k)) :=
    (isOpen_iInter_of_finite (fun i => hPopen i)).inter hAint
  have hsO : s ∈ (⋂ i : ι, Pcond i) ∩ (⋂ k : κ, A k) :=
    ⟨Set.mem_iInter.mpr hsP, Set.mem_iInter.mpr hsA⟩
  obtain ⟨δO, hδOpos, hδOsub⟩ := Metric.isOpen_iff.mp hOopen s hsO
  let Gs : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun τ k x => G (s + τ) k x
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
      (hsm'.differentiableAt top_ne_zero_sardNear).hasFDerivAt
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
  obtain ⟨τ, hτ, hM⟩ := localSard (M := CappingSpace) (m := 12) Gs hGs_sm hGs_slice
    hGs_seam hGs_surj (min (δO / 2) (ε' / 2)) (lt_min (by linarith) (by linarith))
  -- ## 3. the conclusion
  have hτO : ‖τ‖ < δO := by
    have h1 : ‖τ‖ < min (δO / 2) (ε' / 2) := hτ
    linarith [min_le_left (δO / 2) (ε' / 2), hδOpos]
  have hτ' : ‖τ‖ < ε' / 2 := lt_of_lt_of_le hτ (min_le_right _ _)
  have hmemO : s + τ ∈ (⋂ i : ι, Pcond i) ∩ (⋂ k : κ, A k) :=
    hδOsub (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hτO)
  refine ⟨s + τ, ?_, ?_, ?_, ?_⟩
  · calc ‖s + τ - m‖ = ‖(s - m) + τ‖ := by congr 1; abel
      _ ≤ ‖s - m‖ + ‖τ‖ := norm_add_le _ _
      _ < ε' := by linarith
  · have hM' : Meet3Hyp CappingSpace (G (s + τ)) := by simpa only [Gs] using hM
    rwa [hGfun (s + τ)] at hM'
  · intro i
    exact Set.mem_iInter.mp hmemO.1 i
  · intro k
    exact Set.mem_iInter.mp hmemO.2 k

/-- The pair map `t ↦ (blk k t, blk j t)` is onto for `k ≠ j`. -/
private lemma pair_prod_surjective (k j : Fin 3) (hkj : k ≠ j) :
    Function.Surjective (((blk k).prod (blk j)) :
      EuclideanSpace ℝ (Fin 12) →L[ℝ]
        (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))) := by
  rintro ⟨x, y⟩
  refine ⟨blkSpan k x + blkSpan j y, ?_⟩
  have h1 : blk k (blkSpan k x + blkSpan j y) = x := by
    rw [map_add, blk_blkSpan k x, blk_blkSpan_of_ne (k := j) (j := k) hkj, add_zero]
  have h2 : blk j (blkSpan k x + blkSpan j y) = y := by
    rw [map_add, blk_blkSpan_of_ne (k := k) (j := j) (Ne.symm hkj) x, blk_blkSpan j y, zero_add]
  rw [ContinuousLinearMap.prod_apply]
  exact Prod.ext h1 h2

/-- **The `(E4)` producer of the `hdense` design**: one localized Sard call in the design's parameter
`t : ℝ¹²` producing a parameter at which the design's triple satisfies `DesignTripleAtN` **and** the
per-block transport `BlockT6AtN`, from the class-row family `R` (the one input that is not yet on disk:
the open-dense set of parameters at which the perturbed class triples are odd).

All the other inputs are on disk and proved:
* `Work.Drive.exists_meet3Hyp_rot_local_of_openDenseN` (`Drive/hdenseNodeOpens.lean`) — the localized
  Sard call for a finite family of open-dense conditions;
* `Work.Drive.exists_designGoodData` (`Drive/hdenseDesignData.lean`) — the twelve `GoodAt` conditions
  and the design's `Meet3Hyp` (use it as in `exists_designGoodData`'s own proof, with the `c''`/`w'`/`φ`
  family of `Drive/hdenseDesignData.lean`);
* `Work.Drive.isOpen_T6GenAtDBox_design` / `Work.Drive.dense_T6GenAtDBox_design` — the `A_k` sets (the
  density is stated with the extra hypothesis `0 ≤ (blk k x) 0`, which holds at `x = 0`; for the
  Sard call's *density at every* `x` with `‖x‖ ≤ 1`, first move `x` by `x ↦ (1-r) • x + blkSpan k (r • e₀)`
  (`blk k (blkSpan k w) = w`), which keeps `‖x‖ ≤ 1` and makes the coordinate nonnegative);
* `Work.Drive.BlockT6AtN_of_design` (`Drive/hdenseBlockT6.lean`) for `BlockT6AtN`, with the smallness
  producers `Work.Drive.disjoint_perturbed_blocks_of_small` (from `hdisjZc` and
  `designAngles_hu`-style membership of the differences) and `Work.Drive.level_blockChart_of_small`
  (from `hcbot` and `cblk i < c`), and `hcpos`/`hcdist` for the levels `![c/2, c/3, c/4]`.

**Proof (the assembly).**  Write `u := ![0, a, a + c']` and `cblk := ![c/2, c/3, c/4]`, and let
`A k` be the set of parameters at which the block-`k` transport bundle `T6GenAtDBox` holds.  Then:

1. `Work.Drive.threeBlock_dense_point` (its statement is proved **here**, as the private
   `threeBlocks_local`; the fleet also has a copy of the same statement in
   `Drive/threeBlock_dense_point.lean`) produces `s` of norm `< min (β/8) (1/4)`, `β` the budget below, lying in `A 0 ∩ A 1 ∩ A 2`.  The
   point is built by the *margined iteration*: start at the point with all three block coordinates `μ`
   (a small margin) and apply the three density facts `A_k` in turn; each move can lower a block
   coordinate by at most its radius, so the margin survives and every application is legitimate.  (The
   naive "move `x` to `(1-r) x + blkSpan k (r e₀)`" does *not* give the density at every `x` of the unit
   ball: it has displacement `~1`, so it cannot be used for an arbitrarily small `δ`.)
2. `Work.Drive.exists_meet3Hyp_and_cond_near_of_openDense` (its statement is proved **here**, as the
   private `sardNear_local`; the fleet also has a copy in
   `Drive/exists_meet3Hyp_and_cond_near_of_openDense.lean`) is the localized Sard call *based at `s`*: it produces `t` with `‖t - s‖ < β/4`,
   the design's `Meet3Hyp`, the twelve `GoodAt` conditions (`Pcond` below) **and** keeping `A 0, A 1,
   A 2` (which are open and contain `s`, so they persist in a neighbourhood).  This is the proof of
   `Work.Drive.exists_meet3Hyp_rot_local_of_openDenseN` with the search for the base point replaced by
   the input point `s`; the machinery (`localSard`, `richness_sweepChartFam`, the translated family
   `Gs`) is copied verbatim.
3. `‖t‖ < ‖s‖ + β/4 < β`, and `β := min ε' (min ρ₁ (min ρ₂ εl))`, where `ρ₁` is the separation radius
   of `disjoint_perturbed_blocks_of_small`, `ρ₂` the level-band radius of `level_blockChart_of_small`
   and `εl` the perturbation radius of `exists_eps_level_lt_pertChart`.  Then `DesignTripleAtN` is
   assembled from `Meet3Hyp` (step 2), the twelve `GoodAt`'s (step 2), the two level bands (from
   `‖t‖ < εl`, as in `exists_designGoodData`), the oddness of the class triple (from `t ∈ R`, the
   condition fed in as the extra member of `Pcond`) and the three `T6GenAtDBox` bundles (step 1/2);
   `BlockT6AtN` then follows from `BlockT6AtN_of_design` with the separation and level data.

The sole hypothesis of the whole call not available from the shelf is `R` (the class rows). -/
theorem exists_designTripleAtN_blockT6AtN_of_rows
    {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {c : ℝ}
    (hc : 0 < c) (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    (a c' : UnitAddCircle) (ha : a ∈ Work.Drive.Zc γ) (hc' : c' ∈ Work.Drive.Zc γ)
    (hac : a + c' ∈ Work.Drive.Zc γ)
    (R : Set (EuclideanSpace ℝ (Fin 12))) (hRopen : IsOpen R)
    (hRdense : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ R ∧ ‖y - x‖ < δ)
    (hRodd : ∀ t ∈ R, Odd (Work.Drive.classTripleSet
      (fun k z => Work.Drive.chartPert ((Work.Drive.blk k) t)
        (Work.Drive.rotPresentation Q ((![0, a, a + c'] : Fin 3 → UnitAddCircle) k) z))).ncard) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Work.Drive.DesignTripleAtN Q c (![c / 2, c / 3, c / 4] : Fin 3 → ℝ)
          (![0, a, a + c'] : Fin 3 → UnitAddCircle) t ∧
        Work.Drive.BlockT6AtN Q c (![c / 2, c / 3, c / 4] : Fin 3 → ℝ)
          (![0, a, a + c'] : Fin 3 → UnitAddCircle) t := by
  intro ε' hε'
  classical
  let cblk : Fin 3 → ℝ := ![c / 2, c / 3, c / 4]
  let u : Fin 3 → UnitAddCircle := ![0, a, a + c']
  have hcpos : ∀ k : Fin 3, 0 < cblk k := by
    intro k
    fin_cases k <;> simp [cblk] <;> linarith
  have hcdist : ∀ k k' : Fin 3, cblk k = cblk k' → k = k' := by
    intro k k' h
    fin_cases k <;> fin_cases k' <;> simp [cblk] at h ⊢ <;> linarith
  have hcblk_lt : ∀ i : Fin 3, cblk i < c := by
    intro i
    fin_cases i <;> simp [cblk] <;> linarith
  have hu : ∀ k j : Fin 3, k ≠ j → u j - u k ∈ Zc γ := by
    intro k j hkj
    fin_cases k <;> fin_cases j <;> simp_all [u] <;>
      first
        | (exact neg_mem_Zc ha)
        | (exact neg_mem_Zc hc')
        | (simpa only [neg_add_rev] using neg_mem_Zc hac)
  have hQd : IsChartData Q := IsChartData_of_isPlaneChart hQ
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  -- ## the three block sets, their openness and their (half-space) density
  have hAopen : ∀ k : Fin 3, IsOpen {t : EuclideanSpace ℝ (Fin 12) | T6GenAtDBox
      (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
      (cblk (k + 1)) (cblk (k + 2))} := fun k => isOpen_T6GenAtDBox_design hQd u cblk k
  have hlev_k : ∀ k : Fin 3, ∀ z : ℂ, ‖z‖ ≤ 1 → cblk (k + 2) < levelOf (Q z) := by
    intro k z hz
    have hmem : Q z ∈ chartDisk Q :=
      ⟨z, by rw [Metric.mem_closedBall, dist_zero_right]; exact hz, rfl⟩
    exact lt_trans (hcblk_lt (k + 2)) (hcbot _ hmem)
  have hAdense : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 12)), ‖x‖ ≤ 1 → 0 ≤ (blk k x) 0 →
      ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ {t : EuclideanSpace ℝ (Fin 12) | T6GenAtDBox
        (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
        (cblk (k + 1)) (cblk (k + 2))} ∧ ‖y - x‖ < δ := by
    intro k x hx hx0 δ hδ
    obtain ⟨y, hy, hyA⟩ := dense_T6GenAtDBox_design hQd u cblk k hcpos (hlev_k k) x hx hx0 δ hδ
    exact ⟨y, hyA, hy⟩
  -- ## the twelve `GoodAt` conditions, as open and everywhere dense conditions in `t`
  have hPairOpen : ∀ (k j : Fin 3), k ≠ j → ∀ (c'' : ℝ) (w : UnitAddCircle),
      IsOpen {t : EuclideanSpace ℝ (Fin 12) |
        GoodAt (fun s p => chartPert s p) Q c'' w (blk k t, blk j t)} := by
    intro k j hkj c'' w
    rw [show {t : EuclideanSpace ℝ (Fin 12) |
          GoodAt (fun s p => chartPert s p) Q c'' w (blk k t, blk j t)}
        = ((blk k).prod (blk j)) ⁻¹' {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt (fun s p => chartPert s p) Q c'' w q} from rfl]
    exact IsOpen.preimage ((blk k).prod (blk j)).continuous
      (goodPair_pertChart_isOpen hΞc hQ.1 c'' w)
  have hPairDense : ∀ (k j : Fin 3), k ≠ j → ∀ (c'' : ℝ) (w : UnitAddCircle),
      ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
        ∃ y, GoodAt (fun s p => chartPert s p) Q c'' w (blk k y, blk j y) ∧ ‖y - x‖ < δ := by
    intro k j hkj c'' w x _ δ hδ
    have hsurj : Function.Surjective (((blk k).prod (blk j)) :
        EuclideanSpace ℝ (Fin 12) →L[ℝ]
          (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))) :=
      pair_prod_surjective k j hkj
    have hDense : Dense {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
        GoodAt (fun s p => chartPert s p) Q c'' w q} := by
      rw [Metric.dense_iff]
      intro x r hr
      obtain ⟨dp, hdp, hg⟩ := goodPair_pertChart_exists_near (Ξ := fun s p => chartPert s p)
        (Q := Q) hΞc hQ.1 c'' w x.1 x.2 r hr
      refine ⟨(x.1 + dp, x.2), ⟨?_, hg⟩⟩
      have h1 : dist (x.1 + dp) x.1 = ‖dp‖ := by
        rw [dist_eq_norm]; congr 1; abel
      have h2 : dist x.2 x.2 = 0 := dist_self _
      have hd : dist ((x.1 + dp, x.2) :
          EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (x.1, x.2) = ‖dp‖ := by
        rw [Prod.dist_eq, h1, h2, max_eq_left (norm_nonneg dp)]
      rw [Metric.mem_ball, hd]
      exact hdp
    have hpre : Dense (((blk k).prod (blk j)) ⁻¹'
        {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt (fun s p => chartPert s p) Q c'' w q}) :=
      hDense.preimage (ContinuousLinearMap.isOpenMap _ hsurj)
    obtain ⟨y, hyball, hy⟩ := Metric.dense_iff.mp hpre x δ hδ
    refine ⟨y, ?_, ?_⟩
    · exact hy
    · rw [Metric.mem_ball, dist_eq_norm] at hyball
      exact hyball
  -- ## the thirteen open-dense conditions
  let ι : Type := ({q : Fin 3 × Fin 3 // q.1 ≠ q.2} × Fin 2) ⊕ Unit
  let Pcond : ι → Set (EuclideanSpace ℝ (Fin 12)) := fun i => match i with
    | Sum.inl ⟨⟨(k, j), _⟩, lvl⟩ =>
        {t | GoodAt (fun s p => chartPert s p) Q (if lvl = 0 then cblk j else c) (u j - u k)
          (blk k t, blk j t)}
    | Sum.inr _ => R
  have hPopen : ∀ i : ι, IsOpen (Pcond i) := by
    rintro (⟨⟨⟨k, j⟩, hkj⟩, lvl⟩ | _)
    · show IsOpen {t : EuclideanSpace ℝ (Fin 12) | GoodAt (fun s p => chartPert s p) Q
          (if lvl = 0 then cblk j else c) (u j - u k) (blk k t, blk j t)}
      split_ifs with hlvl
      · exact hPairOpen k j hkj (cblk j) (u j - u k)
      · exact hPairOpen k j hkj c (u j - u k)
    · exact hRopen
  have hPdense : ∀ i : ι, ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ Pcond i ∧ ‖y - x‖ < δ := by
    rintro (⟨⟨⟨k, j⟩, hkj⟩, lvl⟩ | _) x hx δ hδ
    · show ∃ y, y ∈ {t : EuclideanSpace ℝ (Fin 12) | GoodAt (fun s p => chartPert s p) Q
          (if lvl = 0 then cblk j else c) (u j - u k) (blk k t, blk j t)} ∧ ‖y - x‖ < δ
      split_ifs with hlvl
      · exact hPairDense k j hkj (cblk j) (u j - u k) x hx δ hδ
      · exact hPairDense k j hkj c (u j - u k) x hx δ hδ
    · exact hRdense x hx δ hδ
  -- ## the smallness radii of the design
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := disjoint_perturbed_blocks_of_small (γ := γ) (hγne := hγne) hQd hdisjZc u hu
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := level_blockChart_of_small hQ.1 hcbot u hcblk_lt
  obtain ⟨εl, hεlpos, hlvl⟩ := exists_eps_level_lt_pertChart hQ (fun s p => chartPert s p) hΞc c hcbot
  -- ## the budget
  let β : ℝ := min ε' (min ρ₁ (min ρ₂ εl))
  have hβpos : 0 < β := lt_min hε' (lt_min hρ₁pos (lt_min hρ₂pos hεlpos))
  have hβ_ε' : β ≤ ε' := min_le_left _ _
  have hβ_ρ₁ : β ≤ ρ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hβ_ρ₂ : β ≤ ρ₂ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hβ_εl : β ≤ εl := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- ## the three-block point `s`
  obtain ⟨s, hs_lt, hsA⟩ := threeBlocks_local (fun k => {t : EuclideanSpace ℝ (Fin 12) | T6GenAtDBox
      (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
      (cblk (k + 1)) (cblk (k + 2))}) hAopen hAdense (min (β / 8) (1 / 4))
      (lt_min (by linarith) (by norm_num))
  have hs_small : ‖s‖ < β / 8 := lt_of_lt_of_le hs_lt (min_le_left _ _)
  have hs1 : ‖s‖ < 1 := lt_of_lt_of_le hs_lt (le_trans (min_le_right _ _) (by norm_num))
  -- ## the localized Sard call at `s`
  obtain ⟨t, ht_dist, hM, hP, hA⟩ :=
    sardNear_local hQd (fun s p => chartPert s p) hΞc cblk hcpos hcdist u
      Pcond hPopen hPdense (fun k => {t : EuclideanSpace ℝ (Fin 12) | T6GenAtDBox
        (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
        (cblk (k + 1)) (cblk (k + 2))}) hAopen s hsA hs1 (β / 4) (by linarith)
  -- ## the smallness of the resulting parameter
  have ht_small : ‖t‖ < β := by
    have h1 : ‖t‖ ≤ ‖s‖ + ‖t - s‖ := by
      have := norm_add_le s (t - s)
      rwa [add_sub_cancel] at this
    linarith
  have htε' : ‖t‖ < ε' := lt_of_lt_of_le ht_small hβ_ε'
  have htρ₁ : ‖t‖ < ρ₁ := lt_of_lt_of_le ht_small hβ_ρ₁
  have htρ₂ : ‖t‖ < ρ₂ := lt_of_lt_of_le ht_small hβ_ρ₂
  have htεl : ‖t‖ < εl := lt_of_lt_of_le ht_small hβ_εl
  -- ## the design's goodness data at `t`
  have hM' : Meet3Hyp CappingSpace
      (sweepChartFam (fun j => rotPresentation Q (u j)) (fun s p => chartPert s p) cblk t) := hM
  have hGood_cblk : ∀ k j : Fin 3, k ≠ j →
      GoodAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) (blk k t, blk j t) := by
    intro k j hkj
    have h := hP (Sum.inl (⟨(k, j), hkj⟩, (0 : Fin 2)))
    simpa only [Pcond, Set.mem_ofPred_eq, ↓reduceIte] using h
  have hGood_c : ∀ k j : Fin 3, k ≠ j →
      GoodAt (fun s p => chartPert s p) Q c (u j - u k) (blk k t, blk j t) := by
    intro k j hkj
    have h := hP (Sum.inl (⟨(k, j), hkj⟩, (1 : Fin 2)))
    simpa only [Pcond, Set.mem_ofPred_eq,
      if_neg (show ¬ ((1 : Fin 2) = 0) from by decide)] using h
  have htR : t ∈ R := by
    have h := hP (Sum.inr ⟨⟩)
    simpa only [Pcond, Set.mem_ofPred_eq] using h
  have hblk_lt : ∀ k : Fin 3, ‖blk k t‖ < εl :=
    fun k => lt_of_le_of_lt (norm_blk_le k t) htεl
  have hband1 : ∀ k : Fin 3, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      c < levelOf (coreLoop (pertChart (fun s p => chartPert s p) Q (blk k t)) s) := by
    intro k s hs
    have hmem : Q (Complex.exp (Real.pi * (s : ℂ) * Complex.I)) ∈ chartDisk Q := by
      refine ⟨Complex.exp (Real.pi * (s : ℂ) * Complex.I), ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
      simp
    have h := hlvl (blk k t) (hblk_lt k) _ hmem
    simpa only [coreLoop, pertChart] using h
  have hband2 : ∀ k : Fin 3, ∀ (w : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)),
      y ∈ Submission.Drive.unitBox 1 →
      c ≤ levelOf (rotPresentation (pertChart (fun s p => chartPert s p) Q (blk k t)) w y) := by
    intro k w y hy
    have hmem : Q (sqDisk (foldBox y)) ∈ chartDisk Q := by
      refine ⟨sqDisk (foldBox y), ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_sqDisk_le_one (foldBox y) (foldBox_mem_unitBox y)
    have h := hlvl (blk k t) (hblk_lt k) _ hmem
    have h2 : levelOf (rotPresentation (pertChart (fun s p => chartPert s p) Q (blk k t)) w y)
        = levelOf (pertChart (fun s p => chartPert s p) Q (blk k t) (sqDisk (foldBox y))) := by
      rw [show rotPresentation (pertChart (fun s p => chartPert s p) Q (blk k t)) w y
          = rotCapping w (pertChart (fun s p => chartPert s p) Q (blk k t)
              (sqDisk (foldBox y))) from rfl, levelOf_rotCapping]
    rw [h2]
    exact le_of_lt h
  have hDG : DesignGoodData Q c cblk u t := ⟨hM', hGood_cblk, hGood_c, hband1, hband2⟩
  have hodd : Odd (classTripleSet
      (fun k z => chartPert (blk k t) (rotPresentation Q (u k) z))).ncard := by
    simpa only [u] using hRodd t htR
  have hgen : ∀ k : Fin 3, T6GenAtDBox
      (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
      (cblk (k + 1)) (cblk (k + 2)) := fun k => hA k
  -- ## the per-block transport
  have hsep : ∀ k j : Fin 3, k ≠ j →
      ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
        blockChart (fun s p => chartPert s p) Q u (fun i => blk i t) k z
          ≠ blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j y :=
    fun k j hkj z y hz => (hρ₁ t htρ₁).1 k j hkj z y hz
  have hsep' : ∀ k j : Fin 3, k ≠ j → ∀ y y' : EuclideanSpace ℝ (Fin 2),
      blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) k y
        ≠ blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j y' :=
    fun k j hkj y y' => (hρ₁ t htρ₁).2 k j hkj y y'
  have hlevmax : ∀ (k : Fin 3) (z : ℂ), ‖z‖ ≤ 1 →
      max (cblk (k + 1)) (cblk (k + 2))
        < levelOf (blockChart (fun s p => chartPert s p) Q u (fun i => blk i t) k z) :=
    fun k z hz => max_lt (hρ₂ t htρ₂ k z hz (k + 1)) (hρ₂ t htρ₂ k z hz (k + 2))
  have hBlock : BlockT6AtN Q c cblk u t :=
    BlockT6AtN_of_design hQd c u cblk hcpos t hM' hgen hsep hsep' hlevmax
  -- ## the conclusion
  refine ⟨t, htε', ?_, ?_⟩
  · exact ⟨hDG, hodd, hgen⟩
  · exact hBlock

end

end Work.Drive
