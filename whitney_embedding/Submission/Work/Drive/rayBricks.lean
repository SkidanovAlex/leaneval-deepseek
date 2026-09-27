import Mathlib
import Submission.Work.Drive.trailTools
import Submission.Work.Drive.stagePieceDrawnArcContained

/-!
# The routing bricks of `Work.Drive.rayPieceStep`

Split out of `rayPieceStep.lean` so that `Submission.Work.Drive.exists_routingTube_of_ray`
(which uses `Work.Drive.exists_lastVisit`) can be imported *by* `rayPieceStep.lean` without an
import cycle.  The four theorems keep their fully-qualified names.

* `exists_lastVisit` — the last visit of an escaping ray to a compact set.
* `trace_inter_clampBall` — the clamp row identifies the arriving trace inside the clamp ball with
  the terminal germ.
* `trace_inter_halfBall` — the half-ball gadget: on the side opposite the germ the trace meets the
  half-ball only in the junction.
* `clamp_radius_le_germ` — `hPgerm + hPtgt + hPclamp` force `ρout ≤ e‖u‖` for `e < 1`: every chart
  ball of radius `< ρout` is crossed by the germ at its boundary, so the "bad case" of the routing
  must be handled by an obstacle, never by a compact-set device.
-/

namespace Work.Drive

/-! ### Helper bricks for `rayPieceStep`

`Work.Drive.exists_lastVisit` — the last time a continuous ray which escapes every compact set
meets a given compact set `K`: after it the ray avoids `K` entirely.  This is the device that makes
the row `Disjoint (ρ '' Set.Ioi t') (Q '' Set.Icc 0 1)` available: if the new piece lies in `K`, its
image is disjoint from the whole future of the ray.

`Work.Drive.trace_inter_clampBall` — the clamp row `hPclamp` identifies the trace of the arriving
piece inside the clamp ball with (the image of) its terminal germ. -/

/-- **The last visit of an escaping ray to a compact set.** -/
theorem exists_lastVisit {M : Type*} [TopologicalSpace M] [T2Space M] {ρ : ℝ → M}
    (hρ : Continuous ρ)
    (hesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ s : ℝ, T ≤ s → ρ s ∉ K)
    {K : Set M} (hK : IsCompact K) {t : ℝ} (ht : ρ t ∈ K) :
    ∃ t' : ℝ, t ≤ t' ∧ ρ t' ∈ K ∧ ∀ s : ℝ, t' < s → ρ s ∉ K := by
  classical
  obtain ⟨T, hT⟩ := hesc K hK
  set S : Set ℝ := {s | t ≤ s ∧ ρ s ∈ K} with hSdef
  have hSne : S.Nonempty := ⟨t, le_rfl, ht⟩
  have hSsub : S ⊆ Set.Icc t T := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra h
    exact hT s (le_of_lt (not_le.mp h)) h2
  have hScl : IsClosed S := by
    have h1 : IsClosed ({s : ℝ | t ≤ s}) := isClosed_Ici
    have h2 : IsClosed (ρ ⁻¹' K) := hK.isClosed.preimage hρ
    rw [hSdef]
    exact h1.inter h2
  have hScomp : IsCompact S := isCompact_Icc.of_isClosed_subset hScl hSsub
  obtain ⟨t', ht'S, hmax⟩ := hScomp.exists_isMaxOn hSne continuous_id.continuousOn
  refine ⟨t', ht'S.1, ht'S.2, fun s hts hmem => ?_⟩
  have hmem' : s ∈ S := ⟨le_trans ht'S.1 hts.le, hmem⟩
  exact absurd (hmax hmem') (not_le.mpr hts)

/-- **The trace of the arriving piece inside the clamp ball is the terminal germ.** -/
theorem trace_inter_clampBall {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M} (hσc : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    {P : ℝ → M} (hPgerm : ∀ s : ℝ, 1 - e ≤ s → s ≤ 1 → P s = c.symm (c σ + (s - 1) • u))
    {ρout : ℝ} (hρout : 0 < ρout)
    (hPclamp : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
      P s ∈ c.symm '' Metric.ball (c σ) ρout → 1 - e ≤ s) :
    P '' Set.Icc (0:ℝ) 1 ∩ c.symm '' Metric.ball (c σ) ρout
      = c.symm '' ((fun s : ℝ => c σ + (s - 1) • u) '' Set.Icc (1 - e) 1)
        ∩ c.symm '' Metric.ball (c σ) ρout := by
  ext x
  constructor
  · rintro ⟨⟨s, hs, hxs⟩, hmem⟩
    refine ⟨?_, hmem⟩
    have hmem' : P s ∈ c.symm '' Metric.ball (c σ) ρout := by rw [hxs]; exact hmem
    refine ⟨(fun s : ℝ => c σ + (s - 1) • u) s, ⟨s, ⟨hPclamp s hs hmem', hs.2⟩, rfl⟩, ?_⟩
    show c.symm ((fun s : ℝ => c σ + (s - 1) • u) s) = x
    rw [← hxs, hPgerm s (hPclamp s hs hmem') hs.2]
  · rintro ⟨⟨y, ⟨s, hs, hys⟩, hyx⟩, hmem⟩
    have hs01 : s ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hs.1, he1, he], hs.2⟩
    refine ⟨⟨s, hs01, ?_⟩, hmem⟩
    rw [hPgerm s hs.1 hs.2]
    show c.symm ((fun s : ℝ => c σ + (s - 1) • u) s) = x
    rw [hys]
    exact hyx

/-- **The half-ball gadget.**  For a direction `w` with `⟪u, w⟫ > 0` the *half ball* around the
junction in direction `w` meets the trace of the arriving piece only in the junction itself: the
clamp row confines the trace inside the ball to the terminal germ, and the germ runs along `-u`,
i.e. on the other side of the flat face. -/
theorem trace_inter_halfBall {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M} (hσc : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    {P : ℝ → M} (hPgerm : ∀ s : ℝ, 1 - e ≤ s → s ≤ 1 → P s = c.symm (c σ + (s - 1) • u))
    (hPtgt : ∀ s : ℝ, 1 - e ≤ s → s ≤ 1 → c σ + (s - 1) • u ∈ c.target)
    (hP1 : P 1 = σ)
    {ρout : ℝ} (hρout : 0 < ρout)
    (hPclamp : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
      P s ∈ c.symm '' Metric.ball (c σ) ρout → 1 - e ≤ s)
    {r : ℝ} (hr : 0 < r) (hrtgt : Metric.closedBall (c σ) r ⊆ c.target) (hrρ : r < ρout)
    {w : EuclideanSpace ℝ (Fin n)} (hw : 0 < inner ℝ u w) :
    P '' Set.Icc (0:ℝ) 1
        ∩ c.symm '' (Metric.closedBall (c σ) r
            ∩ {z : EuclideanSpace ℝ (Fin n) | 0 ≤ inner ℝ (z - c σ) w})
      = {σ} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, ⟨z, ⟨hzball, hzhalf⟩, hzx⟩⟩
    have hztgt : z ∈ c.target := hrtgt hzball
    have hcz : c (c.symm z) = z := c.right_inv hztgt
    have hball : P s ∈ c.symm '' Metric.ball (c σ) ρout :=
      ⟨z, Metric.closedBall_subset_ball hrρ hzball, hzx⟩
    have hs1 : 1 - e ≤ s := hPclamp s hs hball
    have hkey : c (P s) = c σ + (s - 1) • u := by
      rw [hPgerm s hs1 hs.2]
      exact c.right_inv (hPtgt s hs1 hs.2)
    have hval : inner ℝ (c (P s) - c σ) w = (s - 1) * inner ℝ u w := by
      rw [hkey, add_sub_cancel_left, real_inner_smul_left]
    have hzval : 0 ≤ inner ℝ (c (P s) - c σ) w := by
      have hcz' : c (P s) = z := by rw [← hzx, hcz]
      rw [hcz']; exact hzhalf
    have hsge : 1 ≤ s := by nlinarith [hval, hzval, hw]
    have hseq : s = 1 := le_antisymm hs.2 hsge
    show P s = σ
    rw [hseq]; exact hP1
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    refine ⟨⟨1, ⟨by norm_num, le_rfl⟩, hP1⟩, ?_⟩
    refine ⟨c σ, ⟨Metric.mem_closedBall_self hr.le, ?_⟩, c.left_inv hσc⟩
    simp

/-- **The clamp ball never reaches beyond the terminal germ.**  If `e < 1` then the hypotheses
`hPgerm`, `hPtgt` and the clamp row `hPclamp` (together with continuity of `P`) force
`ρout ≤ e * ‖u‖`.  Consequently every chart ball of radius `< ρout` is crossed by the germ at its
boundary: the "bad case" of `rayPieceStep` (the ray leaving such a ball exactly on the germ) is
unavoidable and must be handled by an *obstacle*, not by a compact-set device. -/
theorem clamp_radius_le_germ {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M}
    {u : EuclideanSpace ℝ (Fin n)} {e : ℝ} (he : 0 < e) (he1 : e < 1)
    {P : ℝ → M} (hPc : Continuous P)
    (hPgerm : ∀ s : ℝ, 1 - e ≤ s → s ≤ 1 → P s = c.symm (c σ + (s - 1) • u))
    (hPtgt : ∀ s : ℝ, 1 - e ≤ s → s ≤ 1 → c σ + (s - 1) • u ∈ c.target)
    {ρout : ℝ} (hρout : 0 < ρout)
    (hPclamp : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 →
      P s ∈ c.symm '' Metric.ball (c σ) ρout → 1 - e ≤ s) :
    ρout ≤ e * ‖u‖ := by
  by_contra hcon
  push_neg at hcon
  have he1' : (1 : ℝ) - e ≤ 1 := by linarith
  have hP1e : P (1 - e) ∈ c.source := by
    rw [hPgerm (1 - e) le_rfl he1']
    exact c.map_target (hPtgt (1 - e) le_rfl he1')
  have hcAt : ContinuousAt c (P (1 - e)) :=
    c.continuousOn.continuousAt (c.open_source.mem_nhds hP1e)
  have hgcont : ContinuousAt (fun s : ℝ => ‖c (P s) - c σ‖) (1 - e) :=
    ((hcAt.comp hPc.continuousAt).sub continuousAt_const).norm
  have hgval : ‖c (P (1 - e)) - c σ‖ = e * ‖u‖ := by
    have h1 : c (P (1 - e)) = c σ + (1 - e - 1) • u := by
      rw [hPgerm (1 - e) le_rfl he1']
      exact c.right_inv (hPtgt (1 - e) le_rfl he1')
    have h2 : (1 - e - 1 : ℝ) = -e := by ring
    have h3 : c (P (1 - e)) - c σ = -((e : ℝ) • u) := by
      rw [h1, h2, add_sub_cancel_left, neg_smul]
    rw [h3, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos he]
  -- a neighbourhood of `1 - e` where `P` lands in `c.source` and the norm is `< ρout`
  have hopen : {s : ℝ | P s ∈ c.source} ∈ nhds (1 - e) :=
    hPc.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hP1e)
  have hlt : {s : ℝ | ‖c (P s) - c σ‖ < ρout} ∈ nhds (1 - e) :=
    hgcont.preimage_mem_nhds (isOpen_Iio.mem_nhds (by rw [hgval]; exact hcon))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hopen hlt)
  set s : ℝ := 1 - e - min δ (1 - e) / 2 with hsdef
  have heta : 0 < min δ (1 - e) := lt_min hδpos (by linarith)
  have hslt : s < 1 - e := by rw [hsdef]; linarith [heta]
  have hs01 : s ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · rw [hsdef]; have : min δ (1 - e) ≤ 1 - e := min_le_right _ _; linarith
    · rw [hsdef]; linarith [min_le_right δ (1 - e), heta]
  have hdist : dist s (1 - e) < δ := by
    rw [Real.dist_eq, hsdef, show 1 - e - min δ (1 - e) / 2 - (1 - e) = -(min δ (1 - e) / 2) from by ring,
      abs_neg, abs_of_pos (by linarith : (0:ℝ) < min δ (1 - e) / 2)]
    linarith [min_le_left δ (1 - e)]
  obtain ⟨hsrc, hsmall⟩ := hδ (Metric.mem_ball.mpr hdist)
  have hnotmem : P s ∉ c.symm '' Metric.ball (c σ) ρout := by
    intro hmem
    exact absurd (hPclamp s hs01 hmem) (by linarith)
  have hcout : c (P s) ∉ Metric.ball (c σ) ρout := by
    intro hmem
    exact hnotmem ⟨c (P s), hmem, c.left_inv hsrc⟩
  have hge : ρout ≤ ‖c (P s) - c σ‖ := by
    by_contra hlt'
    push_neg at hlt'
    exact hcout (by rw [Metric.mem_ball, dist_eq_norm]; exact hlt')
  exact absurd hge (not_le.mpr hsmall)

end Work.Drive
