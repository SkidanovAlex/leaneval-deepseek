import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.spike_removal
import Submission.Work.Noncompact.CompressionTube.ray_of_pieces_with_germs
import Submission.Work.Whitney.PathTools.joinedIn_sdiff_chartBall
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

/-- An open partial homeomorphism maps the points of `s` inside the preimage of `U` into `U`. -/
theorem image_subset_of_subset_preimage {α β : Type*} {f : α → β} {s t : Set α} {U : Set β}
    (h : s ∩ t ⊆ f ⁻¹' U) {r : Set α} (hr : r ⊆ s) (ht : r ⊆ t) : r ⊆ f ⁻¹' U :=
  fun x hx => h ⟨hr hx, ht hx⟩

/-- **Chart balls form a neighbourhood basis.**  For a chart `c` at `x` and any neighbourhood
`U` of `x`, some ball of the chart around `c x` has `c`-image inside `U`; moreover the image of the
*closed* ball of the same radius lies in `c.target`, hence is compact. -/
theorem exists_chartBall_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {x : M} (hx : x ∈ c.source) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (c x) ρ ⊆ c.target ∧
      c.symm '' Metric.ball (c x) ρ ⊆ U ∧ c.symm '' Metric.closedBall (c x) ρ ⊆ U := by
  classical
  have hcx : c.symm (c x) = x := c.left_inv hx
  have hcont : ContinuousAt (⇑c.symm) (c x) :=
    c.continuousOn_symm.continuousAt (c.open_target.mem_nhds (c.map_source hx))
  have hpre : c.symm ⁻¹' U ∈ 𝓝 (c x) :=
    hcont.preimage_mem_nhds (show U ∈ 𝓝 (c.symm (c x)) by rwa [hcx])
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hx))
  have hmin : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
  refine ⟨min ρ₀ ρ₁ / 2, by positivity, ?_, ?_, ?_⟩
  · have hlt : min ρ₀ ρ₁ / 2 < ρ₁ := lt_of_lt_of_le (by linarith [min_le_left ρ₀ ρ₁])
      (min_le_right ρ₀ ρ₁)
    exact (Metric.closedBall_subset_ball hlt).trans hρ₁sub
  · have hlt : min ρ₀ ρ₁ / 2 < ρ₀ := lt_of_lt_of_le (by linarith [min_le_right ρ₀ ρ₁])
      (min_le_left ρ₀ ρ₁)
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy]
    exact hρ₀sub (Metric.ball_subset_ball hlt.le hz)
  · have hlt : min ρ₀ ρ₁ / 2 < ρ₀ := lt_of_lt_of_le (by linarith [min_le_right ρ₀ ρ₁])
      (min_le_left ρ₀ ρ₁)
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy]
    exact hρ₀sub (Metric.closedBall_subset_ball hlt hz)

/-- **The trace of an arc near its endpoint is its terminal germ.**

`P` is continuous and injective on `[0,1]` with the terminal germ `t ↦ c.symm (c s + (t-1) • u)` at
`s = P 1` (`1-e ≤ t ≤ 1`).  Then for every open `C ∋ s` there is `ρ > 0` with the closed ball of
radius `ρ` around `c s` inside `C` (so its image is compact) and such that the points of `P '' [0,1]`
inside the *open* ball are exactly the points of the terminal germ. -/
theorem exists_trace_ball {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {P : ℝ → M} (hPc : Continuous P) (hPinj : Set.InjOn P (Set.Icc (0:ℝ) 1))
    {s : M} (hs : P 1 = s) (hsrc : s ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hgerm : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P t = c.symm (c s + (t - 1) • u))
    {C : Set M} (hC : IsOpen C) (hsC : s ∈ C) :
    ∃ ρ : ℝ, 0 < ρ ∧ c.symm '' Metric.closedBall (c s) ρ ⊆ C ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → P t ∈ c.symm '' Metric.ball (c s) ρ →
        t ∈ Set.Icc (1 - e) 1) := by
  classical
  have hKclosed : IsClosed (P '' Set.Icc (0:ℝ) (1 - e)) :=
    (isCompact_Icc.image hPc).isClosed
  have hsK : s ∉ P '' Set.Icc (0:ℝ) (1 - e) := by
    rintro ⟨t, ht, hts⟩
    have ht1 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, by linarith [ht.2, he]⟩
    have : t = 1 := hPinj ht1 ⟨by linarith, le_rfl⟩ (by rw [hts, hs])
    simp only [Set.mem_Icc] at ht
    linarith [ht.2, he, this]
  obtain ⟨ρ, hρ, _, hball, hclosed⟩ :=
    exists_chartBall_subset hsrc ((hKclosed.isOpen_compl.inter hC).mem_nhds ⟨hsK, hsC⟩)
  refine ⟨ρ, hρ, hclosed.trans Set.inter_subset_right, fun t ht hmem => ?_⟩
  by_contra hcon
  rw [Set.mem_Icc] at hcon
  push Not at hcon
  have hlt : t ≤ 1 - e := by
    by_contra h
    push Not at h
    exact absurd (hcon (le_of_lt h)) (not_lt.mpr ht.2)
  exact (hball hmem).1 ⟨t, ⟨ht.1, hlt⟩, rfl⟩

theorem isPathConnected_ball_sdiff_closedBall {n : ℕ} (hn : 2 ≤ n)
    {z : EuclideanSpace ℝ (Fin n)} {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ) :
    IsPathConnected (Metric.ball z ρ \ Metric.closedBall z r) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n)
  have hsphere : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isPathConnected_sphere hrank 0 zero_le_one
  have hIoo : IsPathConnected (Set.Ioo r ρ) :=
    (convex_Ioo r ρ).isPathConnected ⟨(r + ρ) / 2, by constructor <;> linarith⟩
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => z + p.2 • p.1) := by fun_prop
  have himg : (fun p : EuclideanSpace ℝ (Fin n) × ℝ => z + p.2 • p.1) ''
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ Set.Ioo r ρ)
      = Metric.ball z ρ \ Metric.closedBall z r := by
    ext x
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      have hp1' : ‖p.1‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hp1
      have hnorm : ‖p.2 • p.1‖ = p.2 := by
        rw [norm_smul, hp1', mul_one, Real.norm_eq_abs, abs_of_pos (lt_trans hr hp2.1)]
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]; exact hp2.2
      · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm]
        exact not_le.mpr hp2.1
    · rintro ⟨h1, h2⟩
      rw [Metric.mem_ball, dist_eq_norm] at h1
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      set w : EuclideanSpace ℝ (Fin n) := x - z with hw
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h2
        linarith
      have hnw : ‖w‖⁻¹ * ‖w‖ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)
      refine ⟨(‖w‖⁻¹ • w, ‖w‖), ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
        exact hnw
      · exact not_le.mp h2
      · exact h1
      · simp only
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw0), one_smul, hw]
        abel
  exact himg ▸ (hsphere.prod hIoo).image hcont

theorem isPreconnected_sdiff_chartClosedBall {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCpc : IsPreconnected C)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {s : M} (hsrc : s ∈ c.source)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ) (htgt : Metric.closedBall (c s) ρ ⊆ c.target)
    (hsub : c.symm '' Metric.closedBall (c s) ρ ⊆ C) :
    IsPreconnected (C \ c.symm '' Metric.closedBall (c s) r) := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  set B : Set M := c.symm '' Metric.closedBall (c s) r with hB
  set O : Set M := c.symm '' Metric.ball (c s) ρ with hO
  have hballρ : Metric.ball (c s) ρ ⊆ c.target :=
    (Metric.ball_subset_closedBall).trans htgt
  have hOopen : IsOpen O := c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballρ
  have hBclosed : IsClosed B := by
    refine IsCompact.isClosed ?_
    rw [hB]
    exact IsCompact.image_of_continuousOn (isCompact_closedBall (c s) r)
      (c.continuousOn_symm.mono ((Metric.closedBall_subset_closedBall hrρ.le).trans htgt))
  have hclO : closure B ⊆ O := by
    rw [hBclosed.closure_eq, hB, hO]
    exact Set.image_mono (Metric.closedBall_subset_ball hrρ)
  have hOpc : IsPathConnected (O \ B) := by
    have hEq : O \ B = c.symm '' (Metric.ball (c s) ρ \ Metric.closedBall (c s) r) := by
      rw [hO, hB]
      ext x
      constructor
      · rintro ⟨⟨y, hyρ, rfl⟩, hxB⟩
        exact ⟨y, ⟨hyρ, fun hyc => hxB ⟨y, hyc, rfl⟩⟩, rfl⟩
      · rintro ⟨y, ⟨hyρ, hyc⟩, rfl⟩
        exact ⟨⟨y, hyρ, rfl⟩, fun hmem => by
          obtain ⟨z, hz, hzy⟩ := hmem
          exact hyc (c.symm.injOn (htgt (Metric.closedBall_subset_closedBall hrρ.le hz))
            (hballρ hyρ) hzy ▸ hz)⟩
    rw [hEq]
    exact (isPathConnected_ball_sdiff_closedBall hn hr hrρ).image'
      (c.continuousOn_symm.mono (fun x hx => hballρ hx.1))
  have hOsub : O \ B ⊆ C \ B := fun x hx =>
    ⟨hsub (Set.image_mono Metric.ball_subset_closedBall hx.1), hx.2⟩
  rcases eq_empty_or_nonempty (C \ B) with hempty | ⟨u, hu⟩
  · rw [hempty]; exact isPreconnected_empty
  · have hW : IsPathConnected C :=
      (hC.isConnected_iff_isPathConnected).mp ⟨⟨u, hu.1⟩, hCpc⟩
    have hPC : IsPathConnected (C \ B) :=
      isPathConnected_iff.mpr ⟨⟨u, hu⟩, fun v hv w hw =>
        Work.Whitney.PathTools.joinedIn_sdiff_of_isOpen_of_closure_subset hW hOopen hclO hOpc
          hOsub hv hw⟩
    exact hPC.isConnected.isPreconnected

/-- **The stage region is preconnected.**

If `P`'s image meets `C` only inside the closed chart ball of radius `r` around `s`, then deleting
from `C` that ball together with the whole of `P '' Icc` leaves `C \ c.symm '' closedBall (c s) r`
(by the hypothesis for the `P`-part, and trivially for the ball), which is preconnected by
`isPreconnected_sdiff_chartClosedBall`. -/
theorem isPreconnected_sdiff_ball_and_trace {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCpc : IsPreconnected C)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {s : M} (hsrc : s ∈ c.source)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ) (htgt : Metric.closedBall (c s) ρ ⊆ c.target)
    (hsub : c.symm '' Metric.closedBall (c s) ρ ⊆ C)
    {P : ℝ → M} (htrace : P '' Set.Icc (0:ℝ) 1 ∩ C ⊆ c.symm '' Metric.closedBall (c s) r) :
    IsPreconnected (C \ (c.symm '' Metric.closedBall (c s) r ∪ P '' Set.Icc (0:ℝ) 1)) := by
  have hEq : C \ (c.symm '' Metric.closedBall (c s) r ∪ P '' Set.Icc (0:ℝ) 1)
      = C \ c.symm '' Metric.closedBall (c s) r := by
    ext x
    constructor
    · rintro ⟨hxC, hx⟩; exact ⟨hxC, fun hxb => hx (Or.inl hxb)⟩
    · rintro ⟨hxC, hxb⟩
      refine ⟨hxC, fun hx => hx.elim hxb (fun hxP => ?_)⟩
      exact hxb (htrace ⟨hxP, hxC⟩)
  rw [hEq]
  exact isPreconnected_sdiff_chartClosedBall hn hC hCpc hsrc hr hrρ htgt hsub

end

end Work.Noncompact.CompressionTube
