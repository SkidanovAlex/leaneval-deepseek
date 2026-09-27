import Mathlib
import Submission.Work.Drive.trailStDef
import Submission.Work.Drive.trailStepCore
import Submission.Work.Drive.clipArcImage
import Submission.Work.Drive.rayBricks
import Submission.Work.Noncompact.CompressionTube.immersedLine
import Submission.Work.Noncompact.Routing.arcsRemovalIoc

namespace Work.Drive.trailStep

open Set Filter
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (Work.Noncompact.CompressionTube.MC n)
    Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- **The seed arc, trace form.**  This is `Work.Drive.stepSeed` with the hypothesis
`c.symm '' closedBall (c x) ρ ⊆ C` replaced by the *trace* hypothesis
`c.symm '' ((fun u => c x + u • v) '' Ioo a b) ⊆ C`.  The chart ball form is too strong for the
trail recursion: the chart ball of any radius containing the seed also contains the `-v` germ
ray, which lies on the *arriving* piece's terminal germ and is therefore removed from the region,
while the trace of the seed stays off that ray. -/
theorem stepSeedTrace {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    {x : M} (hxc : x ∈ c.source) {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    {a b e : ℝ} (ha : a < 0) (he : 0 < e) (heb : e < b)
    {φ : ℝ → ℝ} (hφcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφpos : ∀ t : ℝ, 0 < deriv φ t)
    (hφid : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) e → φ t = t)
    (hφrange : Set.range φ ⊆ Set.Ioo a b) (hφ1 : e < φ 1)
    (htgt : ∀ u : ℝ, u ∈ Set.Ioo a b → c x + u • v ∈ c.target)
    (hsegtgt : ∀ u : ℝ, |u| ≤ e → c x + u • v ∈ c.target)
    {C : Set M} (hCtr : c.symm '' ((fun u : ℝ => c x + u • v) '' Set.Ioo a b) ⊆ C) :
    ∃ A : ℝ → M, ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder A ∧ A 0 = x ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) A t)) ∧
      Set.InjOn A (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → A t ∈ C) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → A t = c.symm (c x + t • v)) ∧
      (∀ t : ℝ, e < t → t ≤ 1 → A t ∉ Work.Drive.chartSeg c x v e) := by
  classical
  obtain ⟨hAsm, hAimm⟩ :=
    Work.Routing.reparamChartLine_contMDiff_immersion (n := n) (M := M) hc hxc hv hφcd hφpos
      hφrange htgt
  have hinjsymm : Set.InjOn (⇑c.symm) c.target := by
    simpa [OpenPartialHomeomorph.symm_source] using c.symm.injOn
  have hmono : StrictMono φ := strictMono_of_deriv_pos hφpos
  refine ⟨fun t : ℝ => c.symm (c x + φ t • v), hAsm, ?_, hAimm, ?_, ?_, ?_, ?_⟩
  · show c.symm (c x + φ 0 • v) = x
    have hφ0 : φ 0 = 0 := hφid 0 ⟨le_rfl, he.le⟩
    rw [hφ0, zero_smul, add_zero, c.left_inv hxc]
  · -- injectivity on `[0,1]`
    intro s hs t ht hst
    have h1 : c x + φ s • v = c x + φ t • v :=
      hinjsymm (htgt (φ s) (hφrange ⟨s, rfl⟩)) (htgt (φ t) (hφrange ⟨t, rfl⟩)) hst
    have h2 : (φ s - φ t) • v = 0 := by rw [sub_smul, add_left_cancel h1, sub_self]
    have h3 : φ s = φ t := by
      rcases smul_eq_zero.mp h2 with h | h
      · linarith
      · exact absurd h hv
    exact hmono.injective h3
  · -- the image lies in `C`
    intro t _
    exact hCtr ⟨c x + φ t • v, ⟨φ t, hφrange ⟨t, rfl⟩, rfl⟩, rfl⟩
  · -- the germ row
    intro t ht0 hte
    show c.symm (c x + φ t • v) = c.symm (c x + t • v)
    rw [hφid t ⟨ht0, hte⟩]
  · -- the avoidance row
    intro t het _ hmem
    rw [Work.Drive.chartSeg] at hmem
    obtain ⟨z, ⟨s, hs, hsz⟩, hzA⟩ := hmem
    have harg_t : c x + φ t • v ∈ c.target := htgt (φ t) (hφrange ⟨t, rfl⟩)
    have harg_s : c x + s • v ∈ c.target := hsegtgt s (by rw [abs_le]; exact hs)
    have h2 : c.symm (c x + s • v) = c.symm z := congrArg (⇑c.symm) hsz
    have heq : c x + φ t • v = c x + s • v :=
      (hinjsymm harg_s harg_t (h2.trans hzA)).symm
    have hφs : φ t = s := by
      have h3 : (φ t - s) • v = 0 := by rw [sub_smul, add_left_cancel heq, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · linarith
      · exact absurd h hv
    have h4 : e < φ t := by
      have h5 : φ e < φ t := hmono het
      rwa [hφid e ⟨he.le, le_rfl⟩] at h5
    linarith [hs.2, hφs ▸ h4]

/-- One step of the trail recursion: from a state `S` produce the next state `S'`, keeping all of
`S`'s rows and adding the new piece, whose initial germ is the straight continuation of `S.P S.k`'s
terminal germ in the chart `S.c` along `S.w`. -/
theorem stepStCore {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) {ρ : ℝ → M} (hρ : Continuous ρ)
    (hρW : ∀ t : ℝ, 0 ≤ t → ρ t ∈ W)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K)
    (Kex : CompactExhaustion M)
    (S : Work.Drive.St (n := n) (M := M) W ρ Kex) :
    ∃ (S' : Work.Drive.St (n := n) (M := M) W ρ Kex) (ein : ℝ),
      S'.k = S.k + 1 ∧ (∀ j ≤ S.k, S'.P j = S.P j) ∧ 0 < ein ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ ein → S'.P (S.k + 1) t = S.c.symm (S.c S.x + t • S.w)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ ein → S.c S.x + t • S.w ∈ S.c.target) := by

  classical
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  set k : ℕ := S.k with hkdef
  have hvn : (0 : ℝ) < ‖S.w‖ := norm_pos_iff.mpr S.hw
  have hinjsymm : Set.InjOn (⇑S.c.symm) S.c.target := by
    simpa [OpenPartialHomeomorph.symm_source] using S.c.symm.injOn
  -- ## 1  the constants
  have hminpos : (0 : ℝ) < min S.r ‖S.w‖ := lt_min S.hr hvn
  set R : ℝ := min S.r ‖S.w‖ / 8 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact div_pos hminpos (by norm_num)
  have hRr : R ≤ S.r / 8 := by
    rw [hRdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hRw : R ≤ ‖S.w‖ / 8 := by
    rw [hRdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hRlt : R < S.r := by linarith [S.hr, hRr]
  have hRw8 : R / ‖S.w‖ ≤ 1 / 8 := by
    rw [div_le_iff₀ hvn]
    linarith [hRw]
  set E : ℝ := min S.e (R / ‖S.w‖) with hEdef
  have hRwpos : 0 < R / ‖S.w‖ := div_pos hRpos hvn
  have hEpos : 0 < E := lt_min S.he hRwpos
  have hEe : E ≤ S.e := min_le_left _ _
  have hER : E ≤ R / ‖S.w‖ := min_le_right _ _
  have hE1 : E ≤ 1 / 8 := le_trans hER hRw8
  have hElt : E < 1 := by linarith
  have hEw : E * ‖S.w‖ ≤ R := by
    calc E * ‖S.w‖ ≤ (R / ‖S.w‖) * ‖S.w‖ := mul_le_mul_of_nonneg_right hER hvn.le
      _ = R := by field_simp
  have hE3R : (3 * E) * ‖S.w‖ < S.r := by
    have h1 : (3 * E) * ‖S.w‖ = 3 * (E * ‖S.w‖) := by ring
    rw [h1]
    nlinarith [hEw, hRr, S.hr]
  have hrange_lt : ∀ u : ℝ, u ∈ Set.Ioo (-(R / ‖S.w‖)) (3 * E) → |u| < R / ‖S.w‖ + 3 * E := by
    intro u hu
    rw [abs_lt]
    constructor <;> linarith [hu.1, hu.2, hRwpos, hEpos]
  have htgt_aux : ∀ u : ℝ, u ∈ Set.Ioo (-(R / ‖S.w‖)) (3 * E) → S.c S.x + u • S.w ∈ S.c.target := by
    intro u hu
    refine S.hrtgt (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have h1 := hrange_lt u hu
    have h2 : (R / ‖S.w‖ + 3 * E) * ‖S.w‖ = R + 3 * (E * ‖S.w‖) := by
      field_simp
    have h3 : |u| * ‖S.w‖ < R + 3 * R := by
      have h4 : |u| * ‖S.w‖ < (R / ‖S.w‖ + 3 * E) * ‖S.w‖ :=
        mul_lt_mul_of_pos_right h1 hvn
      rw [h2] at h4
      nlinarith [h4, hEw]
    nlinarith [h3, hRr, hRpos]
  have hsegtgt_aux : ∀ u : ℝ, |u| ≤ E → S.c S.x + u • S.w ∈ S.c.target := by
    intro u hu
    refine S.hrtgt (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have h1 : |u| * ‖S.w‖ ≤ E * ‖S.w‖ := mul_le_mul_of_nonneg_right hu hvn.le
    linarith [h1, hEw, hRlt]
  -- ## 2  the region
  set D : Set M := S.c.symm '' Metric.ball (S.c S.x) R with hDdef
  have hDball : Metric.ball (S.c S.x) R ⊆ S.c.target :=
    fun z hz => S.hrtgt (Metric.ball_subset_ball hRlt.le hz)
  have hDopen : IsOpen D := S.c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hDball
  have hDsub : D ⊆ S.c.symm '' Metric.ball (S.c S.x) S.r :=
    Set.image_mono (Metric.ball_subset_ball hRlt.le)
  set F' : Set M := W \ (Kex (k + 2) ∪ (⋃ j ∈ Finset.range k, S.P j '' Set.Icc (0:ℝ) 1) ∪
      (S.P k '' Set.Icc (0:ℝ) 1 \ D)) with hF'def
  have hKold_cl : IsClosed (⋃ j ∈ Finset.range k, S.P j '' Set.Icc (0:ℝ) 1) := by
    refine (Finset.finite_toSet (Finset.range k)).isCompact_biUnion ?_ |>.isClosed
    intro j hj
    exact isCompact_Icc.image (S.hPsm j (Finset.mem_range.mp hj).le).continuous
  have hPk_cl : IsClosed (S.P k '' Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.image (S.hPsm k le_rfl).continuous |>.isClosed
  have hrem_cl : IsClosed (Kex (k + 2) ∪ (⋃ j ∈ Finset.range k, S.P j '' Set.Icc (0:ℝ) 1) ∪
      (S.P k '' Set.Icc (0:ℝ) 1 \ D)) :=
    ((Kex.isCompact (k + 2)).isClosed.union hKold_cl).union
      (hPk_cl.inter hDopen.isClosed_compl)
  have hF'o : IsOpen F' := by rw [hF'def]; exact hW.sdiff hrem_cl
  have hDF' : D ⊆ F' := by
    intro y hy
    rw [hF'def]
    refine ⟨S.hballW (hDsub hy), ?_⟩
    intro hcon
    rcases hcon with h | h
    · rcases h with hK | hJ
      · exact absurd (hDsub hy) (Set.disjoint_right.mp S.hballlev hK)
      · obtain ⟨j, hj, hjm⟩ := Set.mem_iUnion₂.mp hJ
        exact absurd (hDsub hy)
          (Set.disjoint_right.mp (S.hballold j (Finset.mem_range.mp hj)) hjm)
    · exact h.2 hy
  have hxF' : S.x ∈ F' := by
    rw [hF'def]
    refine ⟨S.hballW ⟨S.c S.x, Metric.mem_ball_self S.hr, S.c.left_inv S.hxc⟩, ?_⟩
    intro hcon
    rcases hcon with h | h
    · rcases h with hK | hJ
      · exact S.hxlev hK
      · obtain ⟨j, hj, hjm⟩ := Set.mem_iUnion₂.mp hJ
        have hj' : j < k := Finset.mem_range.mp hj
        exact absurd ⟨S.c S.x, Metric.mem_ball_self S.hr, S.c.left_inv S.hxc⟩
          (Set.disjoint_right.mp (S.hballold j hj') hjm)
    · exact h.2 ⟨S.c S.x, Metric.mem_ball_self hRpos, S.c.left_inv S.hxc⟩
  set C : Set M := connectedComponentIn F' S.x with hCdef
  have hCo : IsOpen C := hF'o.connectedComponentIn
  have hCpc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCW : C ⊆ W := (connectedComponentIn_subset F' S.x).trans (by
    rw [hF'def]; exact Set.sdiff_subset)
  have hxC : S.x ∈ C := mem_connectedComponentIn hxF'
  have hCF' : C ⊆ F' := connectedComponentIn_subset F' S.x
  -- ## 3  the trace of the incoming germ
  have htraceF' : ∀ u : ℝ, u ∈ Set.Ioo (-(R / ‖S.w‖)) (3 * E) →
      S.c.symm (S.c S.x + u • S.w) ∈ F' := by
    intro u hu
    have hrad : ‖u • S.w‖ < S.r := by
      rw [norm_smul, Real.norm_eq_abs]
      rcases le_or_gt 0 u with h | h
      · rw [abs_of_nonneg h]
        have h2 : u * ‖S.w‖ < (3 * E) * ‖S.w‖ := mul_lt_mul_of_pos_right hu.2 hvn
        linarith [h2, hE3R]
      · rw [abs_of_neg h]
        have h2 : -u * ‖S.w‖ < (R / ‖S.w‖) * ‖S.w‖ :=
          mul_lt_mul_of_pos_right (by linarith [hu.1]) hvn
        have h3 : (R / ‖S.w‖) * ‖S.w‖ = R := by field_simp
        linarith [h2, h3, hRlt]
    have hball : S.c.symm (S.c S.x + u • S.w) ∈ S.c.symm '' Metric.ball (S.c S.x) S.r :=
      ⟨S.c S.x + u • S.w, Metric.mem_ball.mpr (by rw [dist_eq_norm, add_sub_cancel_left]; exact hrad),
        rfl⟩
    rw [hF'def]
    refine ⟨S.hballW hball, ?_⟩
    intro hcon
    rcases hcon with h | h
    · rcases h with hK | hJ
      · exact Set.disjoint_left.mp S.hballlev hball hK
      · obtain ⟨j, hj, hjm⟩ := Set.mem_iUnion₂.mp hJ
        exact Set.disjoint_left.mp (S.hballold j (Finset.mem_range.mp hj)) hball hjm
    · obtain ⟨hPk, hD⟩ := h
      obtain ⟨u', hu'Icc, hu'z⟩ := hPk
      have hu'1 : 1 - S.e ≤ u' := S.hclamp u' hu'Icc (by rw [hu'z]; exact hball)
      have hcharttgt : S.c S.x + u • S.w ∈ S.c.target :=
        S.hrtgt (Metric.mem_ball.mpr (by rw [dist_eq_norm, add_sub_cancel_left]; exact hrad))
      have h1 : S.c S.x + (u' - 1) • S.w ∈ S.c.target := S.htgt u' hu'1 hu'Icc.2
      have h3 : u' - 1 = u := by
        have h4 : S.c S.x + (u' - 1) • S.w = S.c S.x + u • S.w :=
          hinjsymm h1 hcharttgt (by rw [← S.hger u' hu'1 hu'Icc.2, hu'z])
        have h5 : (u' - 1 - u) • S.w = 0 := by rw [sub_smul, add_left_cancel h4, sub_self]
        rcases smul_eq_zero.mp h5 with hh | hh
        · linarith
        · exact absurd hh S.hw
      have hu0 : u ≤ 0 := by rw [← h3]; linarith [hu'Icc.2]
      have hDmem : S.c.symm (S.c S.x + u • S.w) ∈ D := by
        rw [hDdef]
        refine ⟨S.c S.x + u • S.w, ?_, rfl⟩
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonpos hu0]
        have h6 : -u < R / ‖S.w‖ := by linarith [hu.1]
        have h7 : -u * ‖S.w‖ < (R / ‖S.w‖) * ‖S.w‖ := mul_lt_mul_of_pos_right h6 hvn
        rwa [show (R / ‖S.w‖) * ‖S.w‖ = R from by field_simp] at h7
      exact hD hDmem
  have hDF'trace : S.c.symm '' ((fun u : ℝ => S.c S.x + u • S.w) '' Set.Ioo (-(R / ‖S.w‖)) (3 * E))
      ⊆ F' := by
    rintro z ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    exact htraceF' u hu
  have hCtr : S.c.symm '' ((fun u : ℝ => S.c S.x + u • S.w) '' Set.Ioo (-(R / ‖S.w‖)) (3 * E))
      ⊆ C := by
    have h1 : IsPreconnected ((fun u : ℝ => S.c S.x + u • S.w) '' Set.Ioo (-(R / ‖S.w‖)) (3 * E)) :=
      isPreconnected_Ioo.image _ (by fun_prop)
    have h2 : IsPreconnected (S.c.symm '' ((fun u : ℝ => S.c S.x + u • S.w) ''
        Set.Ioo (-(R / ‖S.w‖)) (3 * E))) :=
      h1.image _ (S.c.continuousOn_symm.mono (fun z hz => by
        obtain ⟨u, hu, rfl⟩ := hz
        exact htgt_aux u hu))
    exact h2.subset_connectedComponentIn
      ⟨S.c S.x + 0 • S.w, ⟨0, ⟨by linarith [hRwpos], by linarith [hEpos]⟩, rfl⟩,
        by rw [zero_smul, add_zero]; exact S.c.left_inv S.hxc⟩
      hDF'trace
  -- ## 4  the obstacle and its arc
  set S0 : Set M := Work.Drive.chartSeg S.c S.x S.w E with hS0def
  set γ : ℝ → M := fun t : ℝ => S.c.symm (S.c S.x + Work.Drive.segParam E t • S.w) with hγdef
  have hγtgt : ∀ t : ℝ, S.c S.x + Work.Drive.segParam E t • S.w ∈ S.c.target := by
    intro t
    refine S.hrtgt (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have h1 : |Work.Drive.segParam E t| ≤ E := by
      rw [abs_le]; exact Work.Drive.segParam_mem hEpos.le t
    calc |Work.Drive.segParam E t| * ‖S.w‖ ≤ E * ‖S.w‖ := mul_le_mul_of_nonneg_right h1 hvn.le
      _ ≤ R := hEw
      _ < S.r := hRlt
  have hγcont : Continuous γ := by
    rw [hγdef]
    exact S.c.continuousOn_symm.comp_continuous
      (continuous_const.add ((Work.Drive.segParam_cont E).smul continuous_const)) hγtgt
  have hγimg : γ '' Set.Icc (0:ℝ) 1 = S0 := by
    rw [hγdef, hS0def, Work.Drive.chartSeg]
    ext z; constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨S.c S.x + Work.Drive.segParam E t • S.w,
        ⟨Work.Drive.segParam E t, Work.Drive.segParam_mem hEpos.le t, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨(s / E + 1) / 2, Work.Drive.segParam_pre_mem hEpos hs, ?_⟩
      show S.c.symm (S.c S.x + Work.Drive.segParam E ((s / E + 1) / 2) • S.w)
        = S.c.symm (S.c S.x + s • S.w)
      rw [Work.Drive.segParam_surj hEpos hs]
  have hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    have h1 : Work.Drive.segParam E s = Work.Drive.segParam E t := by
      have h2 : S.c S.x + Work.Drive.segParam E s • S.w = S.c S.x + Work.Drive.segParam E t • S.w :=
        hinjsymm (hγtgt s) (hγtgt t) (by simpa [hγdef] using hst)
      have h3 : (Work.Drive.segParam E s - Work.Drive.segParam E t) • S.w = 0 := by
        rw [sub_smul, add_left_cancel h2, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · linarith
      · exact absurd h S.hw
    rw [Work.Drive.segParam_id hs, Work.Drive.segParam_id ht] at h1
    have h4 : 2 * s - 1 - (2 * t - 1) = 0 := by
      have h5 : E * (2 * s - 1 - (2 * t - 1)) = 0 := by linarith
      exact (mul_eq_zero.mp h5).resolve_left (ne_of_gt hEpos)
    linarith
  have hS0closed : IsClosed S0 := by
    rw [← hγimg]; exact (isCompact_Icc.image hγcont).isClosed
  have hγIocF' : γ '' Set.Ioc (0:ℝ) 1 ⊆ F' := by
    rintro z ⟨t, ht, rfl⟩
    have ht01 : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have hsp : Work.Drive.segParam E t ∈ Set.Ioo (-(R / ‖S.w‖)) (3 * E) := by
      refine ⟨?_, ?_⟩
      · rw [Work.Drive.segParam_id ht01]; nlinarith [hEpos, ht.1, hER]
      · rw [Work.Drive.segParam_id ht01]; nlinarith [hEpos, ht.2]
    exact htraceF' _ hsp
  have hγIocC : γ '' Set.Ioc (0:ℝ) 1 ⊆ C := by
    have hpc : IsPreconnected (γ '' Set.Ioc (0:ℝ) 1) :=
      isPreconnected_Ioc.image γ hγcont.continuousOn
    refine hpc.subset_connectedComponentIn ⟨(1/2 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩ hγIocF'
    have h12 : Work.Drive.segParam E (1/2) = 0 := by
      rw [Work.Drive.segParam_id (show (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)]
      norm_num
    show S.c.symm (S.c S.x + Work.Drive.segParam E (1/2) • S.w) = S.x
    rw [h12, zero_smul, add_zero]
    exact S.c.left_inv S.hxc


  have hdanger : ∀ z : M, z ∈ C → z ∈ S.P k '' Set.Icc (0:ℝ) 1 →
      ∃ u : ℝ, u ≤ 0 ∧ z = S.c.symm (S.c S.x + u • S.w) ∧ |u| ≤ E := by
    intro z hzC hzK
    have hzF' : z ∈ F' := hCF' hzC
    have hzDmem : z ∈ D := by
      by_cases hmem : z ∈ D
      · exact hmem
      · exfalso
        rw [hF'def] at hzF'
        exact hzF'.2 (Or.inr ⟨hzK, hmem⟩)
    obtain ⟨z', z'ball, z'eq⟩ := hzDmem
    obtain ⟨u, huIcc, huz⟩ := hzK
    have hzball : z ∈ S.c.symm '' Metric.ball (S.c S.x) S.r :=
      ⟨z', Metric.ball_subset_ball hRlt.le z'ball, z'eq⟩
    have hu1 : 1 - S.e ≤ u := S.hclamp u huIcc (by rw [huz]; exact hzball)
    have hgtgt : S.c S.x + (u - 1) • S.w ∈ S.c.target := S.htgt u hu1 huIcc.2
    have hz'tgt : z' ∈ S.c.target := S.hrtgt (Metric.ball_subset_ball hRlt.le z'ball)
    have hzu : z = S.c.symm (S.c S.x + (u - 1) • S.w) := by
      rw [← huz]; exact S.hger u hu1 huIcc.2
    have hzeq : z' = S.c S.x + (u - 1) • S.w := by
      refine hinjsymm hz'tgt hgtgt ?_
      rw [z'eq, hzu]
    have hnorm : ‖(u - 1) • S.w‖ < R := by
      have h1 : ‖z' - S.c S.x‖ < R := by
        rw [Metric.mem_ball, dist_eq_norm] at z'ball; exact z'ball
      have h2 : z' - S.c S.x = (u - 1) • S.w := by rw [hzeq]; abel
      rwa [h2] at h1
    have hE1 : |u - 1| ≤ E := by
      have ha1 : |u - 1| ≤ S.e := by rw [abs_le]; constructor <;> linarith [hu1, huIcc.2]
      have ha2 : |u - 1| ≤ R / ‖S.w‖ := by
        rw [le_div_iff₀ hvn]
        rw [norm_smul, Real.norm_eq_abs] at hnorm
        exact hnorm.le
      exact le_min ha1 ha2
    exact ⟨u - 1, by have h := huIcc.2; linarith, hzu, hE1⟩
  have hdangerS0 : ∀ z : M, z ∈ C → z ∈ S.P k '' Set.Icc (0:ℝ) 1 → z ∈ S0 := by
    intro z hzC hzK
    obtain ⟨u, hu0, hzu, huE⟩ := hdanger z hzC hzK
    have hu1' : -E ≤ u := (abs_le.mp huE).1
    have hu2' : u ≤ E := (abs_le.mp huE).2
    rw [hS0def, Work.Drive.chartSeg]
    exact ⟨S.c S.x + u • S.w, ⟨u, ⟨hu1', hu2'⟩, rfl⟩, hzu.symm⟩
  -- ## 5  the far trail point
  have hS0cpt : IsCompact S0 := hγimg ▸ isCompact_Icc.image hγcont
  have hKcpt : IsCompact (S0 ∪ {S.x}) := hS0cpt.union isCompact_singleton
  obtain ⟨τK, hτKτ, _hτKmem, hτKmax⟩ :=
    Work.Drive.exists_lastVisit hρ hρesc hKcpt (t := S.τ) (by rw [S.hx]; exact Or.inr rfl)
  set T' : ℝ := max (max (τK + 1) (Work.Drive.escK Kex ρ hρesc (k + 3))) (S.τ + 1) with hT'def
  have hT'τK : τK < T' := by
    rw [hT'def]
    have h1 : τK + 1 ≤ max (τK + 1) (Work.Drive.escK Kex ρ hρesc (k + 3)) := le_max_left _ _
    have h2 : max (τK + 1) (Work.Drive.escK Kex ρ hρesc (k + 3)) ≤ T' := le_max_left _ _
    linarith
  have hT'esc : Work.Drive.escK Kex ρ hρesc (k + 3) ≤ T' := by
    rw [hT'def]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hT'τ : S.τ < T' := by
    rw [hT'def]
    have h := le_max_right (max (τK + 1) (Work.Drive.escK Kex ρ hρesc (k + 3))) (S.τ + 1)
    linarith
  have hyne : ρ T' ≠ S.x := fun hcon =>
    hτKmax T' hT'τK (Or.inr (by rw [Set.mem_singleton_iff]; exact hcon))
  have hyS0 : ρ T' ∉ S0 := fun hcon => hτKmax T' hT'τK (Or.inl hcon)
  have hT'ne : ∀ t : ℝ, T' ≤ t → ρ t ≠ S.x := by
    intro t ht hcon
    exact hτKmax t (lt_of_lt_of_le hT'τK ht) (Or.inr (by rw [Set.mem_singleton_iff]; exact hcon))
  have htrail : ∀ t ∈ Set.Icc S.τ T', ρ t ∈ F' := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ← S.hx]; exact hxF'
    · rw [hF'def]
      refine ⟨hρW t (le_trans S.hτ0 ht.1), ?_⟩
      intro hcon
      rcases hcon with hc | hc
      · rcases hc with hc | hc
        · exact (S.hlev t h) hc
        · obtain ⟨j, hj, hjm⟩ := Set.mem_iUnion₂.mp hc
          exact (Set.disjoint_left.mp (S.hclean j (Finset.mem_range.mp hj).le)) ⟨t, h, rfl⟩ hjm
      · exact (Set.disjoint_left.mp (S.hclean k le_rfl)) ⟨t, h, rfl⟩ hc.1
  have hpc : IsPreconnected (ρ '' Set.Icc S.τ T') := isPreconnected_Icc.image ρ hρ.continuousOn
  have hyC : ρ T' ∈ C := by
    have h1 : ρ T' ∈ connectedComponentIn F' (ρ S.τ) :=
      hpc.subset_connectedComponentIn ⟨S.τ, ⟨le_rfl, hT'τ.le⟩, rfl⟩
        (fun y hy => by obtain ⟨t, ht, rfl⟩ := hy; exact htrail t ht)
        ⟨T', ⟨hT'τ.le, le_rfl⟩, rfl⟩
    rwa [← S.hx] at h1
  -- ## 6  the seed
  obtain ⟨φ, hφcd, hφpos, hφid, hφrange, hφ1, -⟩ :=
    Work.Noncompact.CompressionTube.exists_smooth_reparam_gen (-(R / ‖S.w‖)) (3 * E) E 1
      (by linarith [hRwpos]) hEpos hElt le_rfl (by linarith [hEpos])
  obtain ⟨A, hAcd, hA0, hAimm, hAinj, hAC, hAgerm, hAavoid⟩ :=
    stepSeedTrace (n := n) (M := M) S.hc S.hxc S.hw
      (show -(R / ‖S.w‖) < 0 from by linarith [hRwpos]) hEpos (by linarith [hEpos])
      hφcd hφpos hφid hφrange (by linarith [hφ1.1]) htgt_aux hsegtgt_aux hCtr
  -- ## 7  the routing arc
  have hUpc : IsPreconnected (C \ S0) := by
    have h := Work.Noncompact.Routing.isPreconnected_sdiff_arc_Ioc (n := n) (M := M) hn hCo hCpc
      hγcont hγinj (fun t ht => hγIocC ⟨t, ht, rfl⟩)
    rwa [hγimg] at h
  obtain ⟨α, hα0, hα1, hαsm, hαimm, hαinj, hαC, hαgerm, hαav, _c₁, _w₁, _e₁, _he₁, _hw₁, _hc₁,
    _hqsrc₁, _hterm₁⟩ :=
    Work.Routing.rootedArcAvoidHalfOpen (n := n) (M := M) hn (W := C) (U := C \ S0) (S := S0)
      hCo (hCo.sdiff hS0closed) hUpc hS0closed (subset_refl _) Set.sdiff_subset
      (by rw [Set.disjoint_left]; intro z hz hzu; exact hzu.2 hz)
      S.hc S.hxc S.hw hEpos
      (fun t ht0 hte => hCtr ⟨S.c S.x + t • S.w,
        ⟨t, ⟨by linarith [hRwpos, ht0], by linarith [hEpos, hte]⟩, rfl⟩, rfl⟩)
      (by rw [Set.disjoint_left]
          intro z hzU hzRay
          refine hzU.2 ?_
          rw [hS0def, Work.Drive.chartSeg]
          exact Set.image_mono (Set.image_mono
            (Set.Icc_subset_Icc (by linarith [hEpos]) le_rfl)) hzRay)
      hElt hAcd hA0 hAgerm hAC hAimm hAinj hAavoid hyC hyS0
  -- ## 8  the last visit of the trail to the arc, and the clip
  have hαcpt : IsCompact (α '' Set.Icc (0:ℝ) 1) := isCompact_Icc.image hαsm.continuous
  have hyα : ρ T' ∈ α '' Set.Icc (0:ℝ) 1 := by
    rw [← hα1]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  obtain ⟨τ', hT'τ', hτ'α, hτ'max⟩ := Work.Drive.exists_lastVisit hρ hρesc hαcpt hyα
  set x' : M := ρ τ' with hx'def
  have hx'α : x' ∈ α '' Set.Icc (0:ℝ) 1 := hτ'α
  obtain ⟨s, hsIcc, hsx⟩ := hx'α
  have hτ'ne : ρ τ' ≠ S.x := hT'ne τ' hT'τ'
  have hs0 : 0 < s := by
    rcases lt_or_eq_of_le hsIcc.1 with h | h
    · exact h
    · exfalso
      have hxp : ρ τ' = S.x := by rw [← hx'def, ← hsx, ← h, hα0]
      exact hτ'ne hxp
  obtain ⟨Q, ein2, c₂, w₂, eout, hQ0, hQ1, hQsub, hQsm, hQimm, hQinj, hein2, hQgerm, hQtgt,
    heout0, hw₂, hc₂, hxs, hQterm, hQttgt⟩ :=
    Work.Drive.clipArcImage (n := n) (M := M) hn hαsm hαimm hαinj S.hc S.hw hEpos
      (fun t ht0 ht => by rw [hα0]; exact hαgerm t ht0 ht)
      (fun t ht0 ht => by rw [hα0]; exact hsegtgt_aux t (by rw [abs_of_nonneg ht0]; exact ht))
      hs0 hsIcc.2
  rw [hsx] at hxs hQterm hQttgt
  -- ## 9  the new terminal data and the small balls
  have hQ1' : Q 1 = x' := by rw [hQ1, hsx]
  obtain ⟨r₁, hr₁pos, hr₁tgt, hclamp₁⟩ :=
    Work.Drive.exists_clampBall hQsm.continuous hQ1' hQinj hxs heout0
  have hx'C : x' ∈ C := by rw [← hsx]; exact hαC s hsIcc
  have hx'W : x' ∈ W := hCW hx'C
  have hx'lev : x' ∉ Kex (k + 3) :=
    Work.Drive.escK_spec Kex ρ hρesc (k + 3) (le_trans hT'esc hT'τ')
  have hx'old : ∀ j : ℕ, j ≤ k → x' ∉ S.P j '' Set.Icc (0:ℝ) 1 := by
    intro j hj hmem
    exact (Set.disjoint_left.mp (S.hclean j hj)) ⟨τ', lt_of_lt_of_le hT'τ hT'τ', rfl⟩ hmem
  obtain ⟨r₂, hr₂pos, hr₂tgt, hr₂W, hr₂old⟩ :=
    Work.Drive.exists_chartBall_small (ι := Fin (k + 1))
      (T := fun j : Fin (k + 1) => S.P j '' Set.Icc (0:ℝ) 1)
      hxs (fun j => (isCompact_Icc.image (S.hPsm j (Nat.lt_succ_iff.mp j.isLt)).continuous).isClosed)
      (fun j => hx'old j (Nat.lt_succ_iff.mp j.isLt)) (U := W) hW hx'W
  obtain ⟨r₃, hr₃pos, hr₃tgt, hr₃W, hr₃lev⟩ :=
    Work.Drive.exists_chartBall_small (ι := Unit) (T := fun _ : Unit => Kex (k + 3))
      hxs (fun _ => (Kex.isCompact (k + 3)).isClosed) (fun _ => hx'lev)
      (U := W) hW hx'W
  -- ## 10  the separation of the new piece
  have hQC : Q '' Set.Icc (0:ℝ) 1 ⊆ C := by
    rintro z ⟨t, ht, hzt⟩
    obtain ⟨u, hu, huz⟩ := hQsub ⟨t, ht, hzt⟩
    rw [← huz]
    exact hαC u hu
  have hQlev : Disjoint (Q '' Set.Icc (0:ℝ) 1) (Kex (k + 2)) := by
    rw [Set.disjoint_left]
    intro z hzQ hzK
    have hzF' : z ∈ F' := hCF' (hQC hzQ)
    rw [hF'def] at hzF'
    exact hzF'.2 (Or.inl (Or.inl hzK))
  have hαmeet : α '' Set.Icc (0:ℝ) 1 ∩ S.P k '' Set.Icc (0:ℝ) 1 ⊆ {S.x} := by
    rintro z ⟨⟨t, ht, htz⟩, hzK⟩
    rw [← htz] at hzK ⊢
    rcases le_or_gt t E with hle | hlt
    · have hgerm := hαgerm t ht.1 hle
      obtain ⟨u, hu0, hzu, huE⟩ := hdanger (α t) (hαC t ht) hzK
      have h1 : S.c S.x + t • S.w ∈ S.c.target := hsegtgt_aux t (by rw [abs_of_nonneg ht.1]; exact hle)
      have h2 : S.c S.x + u • S.w ∈ S.c.target := hsegtgt_aux u huE
      have h3 : S.c S.x + t • S.w = S.c S.x + u • S.w :=
        hinjsymm h1 h2 (by rw [← hgerm, hzu])
      have h4 : t = u := by
        have h5 : (t - u) • S.w = 0 := by rw [sub_smul, add_left_cancel h3, sub_self]
        rcases smul_eq_zero.mp h5 with hh | hh
        · linarith
        · exact absurd hh S.hw
      have ht0 : t = 0 := by linarith [ht.1, hu0, h4]
      rw [ht0]; exact hα0
    · have hmem : α t ∈ S0 := hdangerS0 (α t) (hαC t ht) hzK
      exact absurd hmem (hαav t hlt ht.2)
  have hQmeet : Q '' Set.Icc (0:ℝ) 1 ∩ S.P k '' Set.Icc (0:ℝ) 1 ⊆ {S.x} := by
    rintro z ⟨h1, h2⟩
    exact hαmeet ⟨hQsub h1, h2⟩
  -- ## 11  the next state
  set P' : ℕ → ℝ → M := fun j : ℕ => if j ≤ k then S.P j else Q with hP'def
  have hP_old : ∀ j : ℕ, j ≤ k → P' j = S.P j := by
    intro j hj; rw [hP'def]; exact if_pos hj
  have hP_new : P' (k + 1) = Q := by rw [hP'def]; exact if_neg (by omega)
  have hPk1 : S.P k 1 = S.x := by
    rw [S.hger 1 (by linarith [S.he]) le_rfl]
    simp only [sub_self, zero_smul, add_zero]
    exact S.c.left_inv S.hxc
  have hQ0x : Q 0 = S.x := hQ0.trans hα0
  refine ⟨{
    k := k + 1
    P := P'
    x := x'
    τ := τ'
    c := c₂
    w := w₂
    e := eout
    r := min r₁ (min r₂ r₃)
    cIn := S.c
    wIn := S.w
    eIn := ein2
    hx := hx'def
    hτ0 := le_trans S.hτ0 (le_trans hT'τ.le hT'τ')
    hw := hw₂
    he := heout0
    hr := lt_min hr₁pos (lt_min hr₂pos hr₃pos)
    hrtgt := fun z hz => hr₁tgt (Metric.ball_subset_ball (min_le_left _ _) hz)
    hwIn := S.hw
    heIn := hein2
    hc := hc₂
    hcIn := S.hc
    hxc := hxs
    hger := fun t ht1 ht2 => by rw [hP_new]; exact hQterm t ht1 ht2
    htgt := fun t ht1 ht2 => hQttgt t ht1 ht2
    hgerIn := fun t ht0 hte => by rw [hP_new, hQgerm t ht0 hte, hQ0]
    hclamp := fun t ht hmem => by
      rw [hP_new] at hmem
      exact hclamp₁ t ht (Set.image_mono (Metric.ball_subset_ball (min_le_left _ _)) hmem)
    hballW := fun z hz => hr₂W (Set.image_mono (Metric.ball_subset_ball
      (le_trans (min_le_right _ _) (min_le_left _ _))) hz)
    hballlev := Set.disjoint_of_subset_left
      (Set.image_mono (Metric.ball_subset_ball
        (le_trans (min_le_right _ _) (min_le_right _ _)))) (hr₃lev ())
    hballold := fun j hj => by
      have hj' : j ≤ k := Nat.lt_succ_iff.mp hj
      have h1 : P' j = S.P j := hP_old j hj'
      have h2 := hr₂old ⟨j, hj⟩
      rw [h1]
      refine Set.disjoint_of_subset_left ?_ h2
      exact Set.image_mono (Metric.ball_subset_ball
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    hPsm := fun j hj => by
      rcases le_or_gt j k with h | h
      · rw [hP_old j h]; exact S.hPsm j h
      · have hj' : j = k + 1 := by omega
        rw [hj', hP_new]; exact hQsm
    hPimm := fun j hj t ht => by
      rcases le_or_gt j k with h | h
      · rw [hP_old j h]; exact S.hPimm j h t ht
      · have hj' : j = k + 1 := by omega
        rw [hj', hP_new]; exact hQimm t
    hPinj := fun j hj => by
      rcases le_or_gt j k with h | h
      · rw [hP_old j h]; exact S.hPinj j h
      · have hj' : j = k + 1 := by omega
        rw [hj', hP_new]; exact hQinj
    hPjun := fun j hj => by
      have hjle : j ≤ k := Nat.lt_succ_iff.mp hj
      rcases lt_or_eq_of_le hjle with h | h
      · rw [hP_old j h.le, hP_old (j + 1) (by omega)]
        exact S.hPjun j h
      · rw [h, hP_old k le_rfl, hP_new]
        show S.P k 1 = Q 0
        rw [hPk1, hQ0x]
    hPW := fun j hj => by
      rcases le_or_gt j k with h | h
      · rw [hP_old j h]; exact S.hPW j h
      · have hj' : j = k + 1 := by omega
        rw [hj', hP_new]
        exact fun z hz => hCW (hQC hz)
    hPlev := fun j hj1 hj2 => by
      rcases le_or_gt j k with h | h
      · rw [hP_old j h]; exact S.hPlev j hj1 h
      · have hj' : j = k + 1 := by omega
        rw [hj', hP_new]
        exact hQlev
    hPsep := fun j l hjl hl => by
      rcases le_or_gt l k with h | h
      · rw [hP_old j (by omega), hP_old l h]
        exact S.hPsep j l hjl h
      · have hl' : l = k + 1 := by omega
        have hjle : j ≤ k := by omega
        rw [hl', hP_new, hP_old j hjle]
        rcases lt_or_eq_of_le hjle with hjk | hjk
        · intro z hz
          exfalso
          have hzF' : z ∈ F' := hCF' (hQC hz.2)
          rw [hF'def] at hzF'
          exact hzF'.2 (Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjk, hz.1⟩)))
        · rw [hjk, hPk1]
          intro z hz
          exact hQmeet ⟨hz.2, hz.1⟩
    hclean := fun j hj => by
      rcases le_or_gt j k with h | h
      · rw [hP_old j h]
        refine Set.disjoint_of_subset_left ?_ (S.hclean j h)
        rintro z ⟨t, ht, rfl⟩
        exact ⟨t, by rw [Set.mem_Ioi] at ht ⊢; linarith [hT'τ, hT'τ', ht], rfl⟩
      · have hj' : j = k + 1 := by omega
        rw [hj', hP_new]
        rw [Set.disjoint_left]
        rintro z ⟨t, ht, rfl⟩ hzQ
        exact hτ'max t ht (hQsub hzQ)
    hlev := fun t ht =>
      Work.Drive.escK_spec Kex ρ hρesc (k + 3) (le_trans hT'esc (le_trans hT'τ' ht.le))
    hxlev := Work.Drive.escK_spec Kex ρ hρesc (k + 3) (le_trans hT'esc hT'τ')
    c₀ := S.c₀
    u₀ := S.u₀
    e₀ := S.e₀
    hP0 := by rw [hP_old 0 (Nat.zero_le k)]; exact S.hP0
    hc₀ := S.hc₀
    hu₀ := S.hu₀
    he₀ := S.he₀
    hρ0₀ := S.hρ0₀
    hgerm₀ := S.hgerm₀ }, min ein2 E, rfl, (fun j hj => hP_old j hj),
    lt_min hein2 hEpos,
    (by
      intro t ht0 hte
      change P' (k + 1) t = S.c.symm (S.c S.x + t • S.w)
      rw [hP_new, hQgerm t ht0 (le_trans hte (min_le_left _ _)), hα0]),
    (by intro t ht0 hte; exact hsegtgt_aux t (by rw [abs_of_nonneg ht0]; exact le_trans hte (min_le_right _ _)))⟩

end Work.Drive.trailStep
