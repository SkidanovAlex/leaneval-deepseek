import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.EXT.formInFrame_symm
import Submission.Work.Diff.EXT.formFamSection_contMDiffAt_of_frameMat
import Submission.Work.Diff.EXT.FrameKit.formInFrame_frameMat
import Submission.Work.Diff.EXT.FrameKit.formInFrame_pos
import Submission.Work.Diff.EXT.FrameKit.frameMat_of_chartData
import Submission.Work.Diff.EXT.vonNBounded_formInFrame2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gluing local chart data of a one-sided metric family into a two-sided family at `t = 0`

This is the `t = 0` analogue of `Work.Diff.EXT.glue_local_metric_families` (which glues at an
arbitrary seam `T` from the left): here the family `G` is jointly smooth on the half interval
`[0,T)`, the local data `hV` extends its *chart matrices* past `t = 0` and is positive definite
two-sidedly and matches `G` from the right, and the conclusion is a family of metrics jointly
smooth on a two-sided neighbourhood of `0` agreeing with `G` on `[0, ε)`.

The construction is the same: a finite family of chart balls covering `M` with a subordinate
smooth partition of unity, and the form

`γ t x = ∑ i, χ i x • formInFrame i x (V i (t, (extChartAt I i) x))`,

whose matrix in the frame of the chart at `i` is `V i (t, ·)`; on the support of `χ i` this is the
matrix of `G t`, whence `γ t = (G t).inner` on `[0, δg)`, and each term is smooth by
`frameMat_of_chartData`; the section is then assembled by `formFamSection_contMDiffAt_of_frameMat`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- The slice of a jointly smooth family of forms at a fixed time is a smooth section of the
bundle of bilinear forms. -/
lemma twoSided_slice_joint {γ : FormFam (I := I) (M := M)} {O : Set ℝ}
    (h : FormFamJoint γ O) {t : ℝ} (ht : t ∈ O) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => formFamSection (I := I) γ (t, x)) := by
  have hf : ContMDiff I ((𝓘(ℝ, ℝ)).prod I) (⊤ : ℕ∞) (fun x : M => (t, x)) :=
    contMDiff_const.prodMk contMDiff_id
  have hmap : MapsTo (fun x : M => (t, x)) (univ : Set M) (O ×ˢ (univ : Set M)) :=
    fun x _ => ⟨ht, mem_univ x⟩
  have h2 := h.comp hf.contMDiffOn hmap
  rwa [contMDiffOn_univ] at h2

theorem twoSided_glue_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T))
    (hV : ∀ x₀ : M, ∃ δ > 0, ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧
        ∃ V : ℝ × E → Work.Diff.EXT.MatE (E := E),
          ContDiffOn ℝ (⊤ : ℕ∞) V ((Set.Ioo (-δ) δ) ×ˢ U) ∧
          (∀ t ∈ Set.Ico 0 δ, ∀ y ∈ U, V (t, y) = Work.Diff.EXT.chartMat G x₀ t y) ∧
          (∀ t ∈ Set.Ioo (-δ) δ, ∀ y ∈ U,
            (∀ i j, V (t, y) i j = V (t, y) j i) ∧
            ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
              0 < ∑ i, ∑ j, v i * v j * V (t, y) i j)) :
    ∃ ε > 0, ∃ K : ℝ → Submission.Diff.SMet I M,
      Submission.Diff.JointSmooth K (Set.Ioo (-ε) ε) ∧ ∀ t ∈ Set.Ico 0 ε, K t = G t := by
  classical
  rcases isEmpty_or_nonempty M with hMempty | hM
  · -- the empty manifold: the constant family `G` works
    refine ⟨1, one_pos, G, ?_, fun t _ => rfl⟩
    change ContMDiffOn ((𝓘(ℝ, ℝ)).prod I)
      (I.prod (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2 ((G p.1).inner p.2))
      (Set.Ioo (-1) 1 ×ˢ (univ : Set M))
    intro p _
    exact (hMempty.false p.2).elim
  · -- the interesting case
    -- ## Step 1: the local data
    choose δ hδpos U hUopen hUmem V hVsmooth hVeq hVspd using hV
    have hr : ∀ x : M, ∃ r : ℝ, 0 < r ∧ closedBall ((extChartAt I x) x) r ⊆ U x := by
      intro x
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp (hUopen x) ((extChartAt I x) x) (hUmem x)
      exact ⟨ρ / 2, by positivity, fun z hz => hρsub (Metric.closedBall_subset_ball (by linarith) hz)⟩
    choose r hrpos hrsub using hr
    -- ## Step 2: a finite cover by chart balls
    let W : M → Set M := fun x =>
      (chartAt H' x).source ∩ (extChartAt I x) ⁻¹' ball ((extChartAt I x) x) (r x / 2)
    have hWopen : ∀ x, IsOpen (W x) := fun x => isOpen_extChartAt_preimage (I := I) x Metric.isOpen_ball
    have hxW : ∀ x : M, x ∈ W x := fun x =>
      ⟨mem_chart_source H' x, Metric.mem_ball_self (by linarith [hrpos x])⟩
    obtain ⟨s, hs⟩ : ∃ s : Finset M, (univ : Set M) ⊆ ⋃ x ∈ s, W x := by
      obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWopen (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
      exact ⟨t, ht⟩
    have hsne : s.Nonempty := by
      obtain ⟨m⟩ := hM
      rcases mem_iUnion.mp (hs (mem_univ m)) with ⟨x, hx⟩
      rcases mem_iUnion.mp hx with ⟨hxs, _⟩
      exact ⟨x, hxs⟩
    -- ## Step 3: a uniform time radius
    obtain ⟨j₀, hj₀s, hj₀min⟩ : ∃ j ∈ s, ∀ i ∈ s, δ j ≤ δ i := s.exists_min_image δ hsne
    obtain ⟨δf, hδfpos, hδflt⟩ : ∃ δf : ℝ, 0 < δf ∧ ∀ i ∈ s, δf < δ i := by
      refine ⟨δ j₀ / 2, by have := hδpos j₀; positivity, fun i hi => ?_⟩
      have h1 := hj₀min i hi
      have h2 := hδpos j₀
      linarith
    set δg : ℝ := δf with hδgdef
    have hδgpos : 0 < δg := hδfpos
    have hδgf' : δg ≤ δf := le_refl _
    haveI : SigmaCompactSpace M :=
      SigmaCompactSpace.of_countable ({univ} : Set (Set M)) (Set.countable_singleton _)
        (fun t ht => by
          rw [Set.mem_singleton_iff.mp ht]
          exact isCompact_univ)
        (by simp)
    -- ## Step 4: the partition of unity
    let 𝒰 : M → Set M := fun i => if i ∈ s then W i else ∅
    have h𝒰of : ∀ i ∈ s, 𝒰 i = W i := fun i hi => by dsimp only [𝒰]; rw [if_pos hi]
    have h𝒰not : ∀ i ∉ s, 𝒰 i = ∅ := fun i hi => by dsimp only [𝒰]; rw [if_neg hi]
    have h𝒰open : ∀ i, IsOpen (𝒰 i) := by
      intro i
      by_cases hi : i ∈ s
      · rw [h𝒰of i hi]; exact hWopen i
      · rw [h𝒰not i hi]; exact isOpen_empty
    have hcover : (univ : Set M) ⊆ ⋃ i, 𝒰 i := by
      intro m hm
      rcases mem_iUnion.mp (hs hm) with ⟨x, hx⟩
      rcases mem_iUnion.mp hx with ⟨hxs, hmx⟩
      exact mem_iUnion.mpr ⟨x, by rw [h𝒰of x hxs]; exact hmx⟩
    obtain ⟨χ, hχ⟩ :=
      SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ 𝒰 h𝒰open hcover
    have hχsub : ∀ i, tsupport (χ i : M → ℝ) ⊆ 𝒰 i := hχ
    have hχzero : ∀ i ∉ s, ∀ y : M, (χ i : M → ℝ) y = 0 := by
      intro i hi y
      have h1 : tsupport (χ i : M → ℝ) ⊆ (∅ : Set M) := by
        rw [← h𝒰not i hi]; exact hχsub i
      by_contra hcon
      exact h1 (subset_closure (Function.mem_support.mpr hcon))
    have hsum1 : ∀ y : M, ∑ i ∈ s, (χ i : M → ℝ) y = 1 := by
      intro y
      have h1 : ∑ᶠ i : M, (χ i : M → ℝ) y = 1 := χ.sum_eq_one (mem_univ y)
      rw [finsum_eq_sum_of_support_subset (fun i : M => (χ i : M → ℝ) y) (s := s)
        (fun i hi => by
          by_contra hcon
          exact hi (hχzero i hcon y))] at h1
      exact h1
    -- ## Step 5: the chart-ball membership facts
    have hχW : ∀ i ∈ s, ∀ y : M, (χ i : M → ℝ) y ≠ 0 → y ∈ W i := by
      intro i hi y hy
      have h1 : y ∈ tsupport (χ i : M → ℝ) := subset_closure (Function.mem_support.mpr hy)
      have h2 := hχsub i h1
      rwa [h𝒰of i hi] at h2
    have hχbase : ∀ i ∈ s, ∀ y : M, (χ i : M → ℝ) y ≠ 0 →
        y ∈ (trivializationAt E (TangentSpace I) i).baseSet := by
      intro i hi y hy
      rw [TangentBundle.trivializationAt_baseSet]
      exact (hχW i hi y hy).1
    have hχU : ∀ i ∈ s, ∀ y : M, (χ i : M → ℝ) y ≠ 0 → (extChartAt I i) y ∈ U i := by
      intro i hi y hy
      have h1 : (extChartAt I i) y ∈ ball ((extChartAt I i) i) (r i / 2) := (hχW i hi y hy).2
      refine hrsub i (Metric.closedBall_subset_closedBall (by linarith [hrpos i])
        (Metric.ball_subset_closedBall h1))
    -- ## Step 6: the constructed family of forms
    let γ : FormFam (I := I) (M := M) := fun t y =>
      ∑ i ∈ s, (χ i : M → ℝ) y •
        formInFrame (I := I) i y (fun a b => V i (t, (extChartAt I i) y) a b)
    have hγ_apply : ∀ (t : ℝ) (y : M) (u v : TangentSpace I y), γ t y u v =
        ∑ i ∈ s, (χ i : M → ℝ) y * (formInFrame (I := I) i y
          (fun a b => V i (t, (extChartAt I i) y) a b) u v) := by
      intro t y u v
      simp only [γ, sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hhex : ∀ y : M, ∃ i ∈ s, (χ i : M → ℝ) y ≠ 0 := by
      intro y
      by_contra hcon
      push_neg at hcon
      have h1 := hsum1 y
      rw [Finset.sum_eq_zero (fun i hi => hcon i hi)] at h1
      exact zero_ne_one h1
    -- agreement with `G` on `[0, δg)`
    have hγ_agree : ∀ t ∈ Set.Ico 0 δg, ∀ y : M, γ t y = (G t).inner y := by
      intro t ht y
      have hterm : ∀ i ∈ s, (χ i : M → ℝ) y •
            formInFrame (I := I) i y (fun a b => V i (t, (extChartAt I i) y) a b)
          = (χ i : M → ℝ) y • (G t).inner y := by
        intro i hi
        by_cases hc : (χ i : M → ℝ) y = 0
        · ext u v
          rw [hc]
          simp only [smul_apply, smul_eq_mul, zero_mul]
        · have hchartU := hχU i hi y hc
          have hti : t ∈ Set.Ico 0 (δ i) :=
            ⟨ht.1, by linarith [ht.2, hδgf', hδflt i hi]⟩
          have hVeqi := hVeq i t hti ((extChartAt I i) y) hchartU
          have hleft : (extChartAt I i).symm ((extChartAt I i) y) = y :=
            (extChartAt I i).left_inv (by rw [extChartAt_source]; exact (hχW i hi y hc).1)
          have hmat : (fun a b => V i (t, (extChartAt I i) y) a b)
              = frameMat (I := I) i y ((G t).inner y) := by
            funext a b
            rw [hVeqi]
            simp only [chartMat, chartMatFun, frameMat]
            rw [hleft]
          rw [hmat, Work.Diff.EXT.FrameKit.formInFrame_frameMat (I := I) (x₀ := i) (x := y)
            (hχbase i hi y hc)]
      calc γ t y = ∑ i ∈ s, (χ i : M → ℝ) y • (G t).inner y := by
            simp only [γ]
            exact Finset.sum_congr rfl hterm
        _ = (∑ i ∈ s, (χ i : M → ℝ) y) • (G t).inner y := Finset.sum_smul.symm
        _ = (G t).inner y := by rw [hsum1 y, one_smul]
    -- symmetry
    have hγ_symm : ∀ t ∈ Set.Ioo (-δg) δg, ∀ (y : M) (u v : TangentSpace I y),
        γ t y u v = γ t y v u := by
      intro t ht y u v
      rw [hγ_apply, hγ_apply]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      by_cases hc : (χ i : M → ℝ) y = 0
      · rw [hc, zero_mul, zero_mul]
      · have hchartU := hχU i hi y hc
        have hti : t ∈ Set.Ioo (-δ i) (δ i) :=
          ⟨by linarith [hδgf', hδflt i hi, ht.1], by linarith [hδgf', hδflt i hi, ht.2]⟩
        have hsymm : ∀ a b, V i (t, (extChartAt I i) y) a b = V i (t, (extChartAt I i) y) b a :=
          (hVspd i t hti ((extChartAt I i) y) hchartU).1
        have hs := formInFrame_symm (I := I) (x₀ := i) (x := y)
          (A := fun a b => V i (t, (extChartAt I i) y) a b) hsymm
        rw [hs u v]
    -- positive definiteness
    have hγ_pos : ∀ t ∈ Set.Ioo (-δg) δg, ∀ y : M, ∀ u : TangentSpace I y,
        u ≠ 0 → 0 < γ t y u u := by
      intro t ht y u hu
      obtain ⟨i₀, hi₀, hc₀⟩ := hhex y
      have hti : t ∈ Set.Ioo (-δ i₀) (δ i₀) :=
        ⟨by linarith [hδgf', hδflt i₀ hi₀, ht.1], by linarith [hδgf', hδflt i₀ hi₀, ht.2]⟩
      have hspd := (hVspd i₀ t hti ((extChartAt I i₀) y) (hχU i₀ hi₀ y hc₀))
      have hpos₀ : 0 < (χ i₀ : M → ℝ) y *
          (formInFrame (I := I) i₀ y (fun a b => V i₀ (t, (extChartAt I i₀) y) a b) u u) :=
        mul_pos (lt_of_le_of_ne (χ.nonneg i₀ y) (Ne.symm hc₀))
          (Work.Diff.EXT.FrameKit.formInFrame_pos (I := I) (hχbase i₀ hi₀ y hc₀) hspd.2 hu)
      have hnn : ∀ i ∈ s, 0 ≤ (χ i : M → ℝ) y *
          (formInFrame (I := I) i y (fun a b => V i (t, (extChartAt I i) y) a b) u u) := by
        intro i hi
        by_cases hc : (χ i : M → ℝ) y = 0
        · rw [hc, zero_mul]
        · have hti' : t ∈ Set.Ioo (-δ i) (δ i) :=
            ⟨by linarith [hδgf', hδflt i hi, ht.1], by linarith [hδgf', hδflt i hi, ht.2]⟩
          exact mul_nonneg (χ.nonneg i y)
            (le_of_lt (Work.Diff.EXT.FrameKit.formInFrame_pos (I := I) (hχbase i hi y hc)
              ((hVspd i t hti' ((extChartAt I i) y) (hχU i hi y hc)).2) hu))
      rw [hγ_apply]
      exact lt_of_lt_of_le hpos₀ (Finset.single_le_sum hnn hi₀)
    -- von Neumann boundedness
    have hγ_vonN : ∀ t ∈ Set.Ioo (-δg) δg, ∀ y : M,
        Bornology.IsVonNBounded ℝ {u : TangentSpace I y | γ t y u u < 1} := by
      intro t ht y
      obtain ⟨i₀, hi₀, hc₀⟩ := hhex y
      have hti : t ∈ Set.Ioo (-δ i₀) (δ i₀) :=
        ⟨by linarith [hδgf', hδflt i₀ hi₀, ht.1], by linarith [hδgf', hδflt i₀ hi₀, ht.2]⟩
      have hspd := (hVspd i₀ t hti ((extChartAt I i₀) y) (hχU i₀ hi₀ y hc₀))
      have hcpos : 0 < (χ i₀ : M → ℝ) y := lt_of_le_of_ne (χ.nonneg i₀ y) (Ne.symm hc₀)
      refine Bornology.IsVonNBounded.subset ?_
        (vonNBounded_formInFrame2 (I := I) (x₀ := i₀) (x := y)
          (hχbase i₀ hi₀ y hc₀) (A := fun a b => V i₀ (t, (extChartAt I i₀) y) a b)
          hspd.2 (r := 1 / (χ i₀ : M → ℝ) y) (by positivity))
      intro u hu
      have hnn : ∀ i ∈ s, 0 ≤ (χ i : M → ℝ) y *
          (formInFrame (I := I) i y (fun a b => V i (t, (extChartAt I i) y) a b) u u) := by
        intro i hi
        by_cases hc : (χ i : M → ℝ) y = 0
        · rw [hc, zero_mul]
        · by_cases hu0 : u = 0
          · rw [hu0]; simp
          · have hti' : t ∈ Set.Ioo (-δ i) (δ i) :=
              ⟨by linarith [hδgf', hδflt i hi, ht.1], by linarith [hδgf', hδflt i hi, ht.2]⟩
            exact mul_nonneg (χ.nonneg i y)
              (le_of_lt (Work.Diff.EXT.FrameKit.formInFrame_pos (I := I) (hχbase i hi y hc)
                ((hVspd i t hti' ((extChartAt I i) y) (hχU i hi y hc)).2) hu0))
      have hu' : γ t y u u < 1 := by simpa using hu
      rw [hγ_apply t y u u] at hu'
      have h1 : (χ i₀ : M → ℝ) y *
          (formInFrame (I := I) i₀ y (fun a b => V i₀ (t, (extChartAt I i₀) y) a b) u u) < 1 :=
        lt_of_le_of_lt (Finset.single_le_sum hnn hi₀) hu'
      show formInFrame (I := I) i₀ y
        (fun a b => V i₀ (t, (extChartAt I i₀) y) a b) u u < 1 / (χ i₀ : M → ℝ) y
      rw [lt_div_iff₀ hcpos, mul_comm]
      exact h1
    -- ## Step 7: smoothness of the chart matrix of `γ`
    have hδgf'' : ∀ i ∈ s, δg < δ i := fun i hi => lt_of_le_of_lt hδgf' (hδflt i hi)
    have hmat_smooth : ∀ t ∈ Set.Ioo (-δg) δg, ∀ x : M,
        ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (modelWithCornersSelf ℝ (MatE (E := E))) (⊤ : ℕ∞)
          (fun p : ℝ × M => frameMat (I := I) x p.2 (γ p.1 p.2)) (t, x) := by
      intro t ht x
      -- the function is the sum of its terms
      have hsplit : (fun p : ℝ × M => frameMat (I := I) x p.2 (γ p.1 p.2))
          = fun p : ℝ × M => ∑ i ∈ s, (χ i : M → ℝ) p.2 •
              frameMat (I := I) x p.2
                (formInFrame (I := I) i p.2 (fun a b => V i (p.1, (extChartAt I i) p.2) a b)) := by
        funext p a b
        simp only [γ, frameMat, Finset.sum_apply, sum_apply, Pi.smul_apply, smul_apply, smul_eq_mul]
      rw [hsplit]
      have hconv : (fun p : ℝ × M => ∑ i ∈ s, (χ i : M → ℝ) p.2 • frameMat (I := I) x p.2
            (formInFrame (I := I) i p.2 (fun a b => V i (p.1, (extChartAt I i) p.2) a b)))
          = ∑ i ∈ s, (fun p : ℝ × M => (χ i : M → ℝ) p.2 • frameMat (I := I) x p.2
            (formInFrame (I := I) i p.2 (fun a b => V i (p.1, (extChartAt I i) p.2) a b))) :=
        funext fun p => (Finset.sum_apply p s
          (fun i (q : ℝ × M) => (χ i : M → ℝ) q.2 • frameMat (I := I) x q.2
            (formInFrame (I := I) i q.2 (fun a b => V i (q.1, (extChartAt I i) q.2) a b)))).symm
      rw [hconv]
      refine Finset.sum_induction (s := s)
        (f := fun i : M => fun p : ℝ × M => (χ i : M → ℝ) p.2 •
          frameMat (I := I) x p.2
            (formInFrame (I := I) i p.2 (fun a b => V i (p.1, (extChartAt I i) p.2) a b)))
        (p := fun F : ℝ × M → MatE (E := E) =>
          ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (modelWithCornersSelf ℝ (MatE (E := E))) (⊤ : ℕ∞) F (t, x))
        ?_ (contMDiffAt_const (c := (0 : MatE (E := E)))) (fun i hi => ?_)
      · exact fun f g hf hg => hf.add hg
      · -- smoothness of a single term
        by_cases hxχ : x ∈ tsupport (χ i : M → ℝ)
        · have hxsub : x ∈ W i := by
            have h1 : x ∈ 𝒰 i := hχsub i hxχ
            rwa [h𝒰of i hi] at h1
          have hxsrc : x ∈ (chartAt H' i).source := hxsub.1
          have hxU : (extChartAt I i) x ∈ U i := by
            have hxb : (extChartAt I i) x ∈ ball ((extChartAt I i) i) (r i / 2) := hxsub.2
            exact hrsub i (Metric.closedBall_subset_closedBall (by linarith [hrpos i])
              (Metric.ball_subset_closedBall hxb))
          have hmemU : (Set.Ioo (-δ i) (δ i)) ×ˢ U i ∈ 𝓝 (t, (extChartAt I i) x) := by
            rw [nhds_prod_eq]
            exact Filter.prod_mem_prod
              (isOpen_Ioo.mem_nhds ⟨by linarith [hδgf', hδflt i hi, ht.1],
                by linarith [hδgf', hδflt i hi, ht.2]⟩) ((hUopen i).mem_nhds hxU)
          have hWsm : ContDiffAt ℝ (⊤ : ℕ∞) (V i) (t, (extChartAt I i) x) :=
            (hVsmooth i).contDiffAt hmemU
          have hinner := Work.Diff.EXT.FrameKit.frameMat_of_chartData (I := I) (x₀ := i) (x := x)
            (W := V i) hxsrc hWsm
          have hχsm : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
              (fun p : ℝ × M => (χ i : M → ℝ) p.2) (t, x) :=
            ((χ i).contMDiff.contMDiffAt).comp (t, x) contMDiffAt_snd
          exact hχsm.smul hinner
        · -- the term vanishes near the point
          have hzero : ∀ᶠ p : ℝ × M in 𝓝 (t, x), (χ i : M → ℝ) p.2 = 0 := by
            have hopen : (tsupport (χ i : M → ℝ))ᶜ ∈ 𝓝 x :=
              (isClosed_tsupport _).isOpen_compl.mem_nhds hxχ
            have hprod : (univ : Set ℝ) ×ˢ (tsupport (χ i : M → ℝ))ᶜ ∈ 𝓝 (t, x) := by
              rw [nhds_prod_eq]
              exact Filter.prod_mem_prod Filter.univ_mem hopen
            filter_upwards [hprod] with p hp
            by_contra hcon
            exact hp.2 (subset_closure (Function.mem_support.mpr hcon))
          refine (contMDiffAt_const (c := (0 : MatE (E := E)))).congr_of_eventuallyEq ?_
          filter_upwards [hzero] with p hp
          rw [hp]
          funext a b
          simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_mul]
    -- ## Step 8: `γ` is jointly smooth
    have hγ_smooth : FormFamJoint γ (Set.Ioo (-δg) δg) := by
      rw [FormFamJoint]
      intro p hp
      rcases p with ⟨t, x⟩
      rw [Set.mem_prod] at hp
      exact (formFamSection_contMDiffAt_of_frameMat (I := I) (γ := γ) (τ := t) (x₀ := x)
        (hmat_smooth t hp.1 x)).contMDiffWithinAt
    -- ## Step 9: the family of metrics and the conclusion
    let H₁ : ℝ → Submission.Diff.SMet I M := fun t =>
      if t ∈ Set.Ico 0 δg then G t
      else if ht : t ∈ Set.Ioo (-δg) δg then
        { inner := γ t
          symm := hγ_symm t ht
          pos := hγ_pos t ht
          isVonNBounded := hγ_vonN t ht
          contMDiff := twoSided_slice_joint hγ_smooth ht }
      else G t
    have hH₁_inner : ∀ t ∈ Set.Ioo (-δg) δg, (H₁ t).inner = γ t := by
      intro t ht
      rcases lt_or_ge t 0 with htT | htT
      · -- `t < 0`: the constructed branch
        dsimp only [H₁]
        rw [if_neg (fun hc => absurd hc.1 (not_le.mpr htT)), dif_pos ht]
      · -- `0 ≤ t`: the branch agreeing with `G`
        have h1 : H₁ t = G t := by
          dsimp only [H₁]
          rw [if_pos ⟨htT, ht.2⟩]
        have h2 : γ t = (G t).inner := funext (hγ_agree t ⟨htT, ht.2⟩)
        rw [h1, h2]
    refine ⟨δg, hδgpos, H₁, ?_, ?_⟩
    · -- joint smoothness of `H₁` on the two-sided interval
      change FormFamJoint (I := I) (fun t x => (H₁ t).inner x) (Set.Ioo (-δg) δg)
      rw [FormFamJoint]
      intro p hp
      rcases p with ⟨t, x⟩
      rw [Set.mem_prod] at hp
      have ht : t ∈ Set.Ioo (-δg) δg := hp.1
      have hmem : (Set.Ioo (-δg) δg) ×ˢ (univ : Set M) ∈ 𝓝 (t, x) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod (isOpen_Ioo.mem_nhds ht) Filter.univ_mem
      have hev : formFamSection (I := I) (fun t x => (H₁ t).inner x)
          =ᶠ[𝓝 (t, x)] formFamSection (I := I) γ := by
        filter_upwards [hmem] with q hq
        rcases q with ⟨τ, z⟩
        rw [Set.mem_prod] at hq
        have hτ : τ ∈ Set.Ioo (-δg) δg := hq.1
        have hinner : (H₁ τ).inner = γ τ := by
          rcases lt_or_ge τ 0 with hτT | hτT
          · exact hH₁_inner τ hτ
          · have h1 : H₁ τ = G τ := by
              dsimp only [H₁]
              rw [if_pos ⟨hτT, hτ.2⟩]
            have h2 : γ τ = (G τ).inner := funext (hγ_agree τ ⟨hτT, hτ.2⟩)
            rw [h1, h2]
        simp only [formFamSection]
        rw [hinner]
      have hmain : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I)
          (I.prod (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))) (⊤ : ℕ∞)
          (formFamSection (I := I) γ) (t, x) :=
        hγ_smooth.contMDiffAt hmem
      exact (hmain.congr_of_eventuallyEq hev).contMDiffWithinAt
    · -- agreement on `[0, δg)`
      intro t ht
      dsimp only [H₁]
      rw [if_pos ht]

end Work.Diff.EXT
