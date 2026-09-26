import Mathlib
import Submission.Work.SphereJordan.ladder_trace
import Submission.Work.SphereJordan.part_defs
import Submission.Work.SphereJordan.path_algebra
import Submission.Work.Smooth.JordanSeparation.plApproxLoop
import Submission.Work.SphereJordan.lwalk_nullhomotopic
import Submission.Work.Smooth.JordanSeparation.lwalk_peel_base

/-!
# The lattice approximation of a loop in an open set

The main result is `Work.SphereJordan.exists_lwalk_freeHomotopic`: a loop in an open `U ⊆ ℂ` is
freely homotopic, inside `↥U`, to the realization `W.loopNat hval` of a closed lattice walk whose
trace lies in `U`.

The construction is the ladder of `ladder_macro.lean`/`ladder_walk.lean`: a partition `t` of the
unit interval, the even-lattice ladder `lad k = snap (γ (t k) / c)`, and the walk of blocks of
twelve unit steps; `ladder_trace.lean` shows the trace lies in `U`.  The homotopy compares, inside
the convex ball around `γ (t k)`, the restriction `γ.restr (t k) (t (k+1))` with the three-piece
path `e k · blk k · (e (k+1))⁻¹` of spokes and blocks, and then telescopes.
-/

namespace Work.SphereJordan

open Set Metric
open Work.Smooth.JordanSeparation

noncomputable section

/-! ## The blocks of the ladder walk -/

/-- The `k`-th block of the ladder walk: the join of its twelve edges (from the vertex `12 * k` to
the vertex `12 * (k + 1)`). -/
def blk {U : Set ℂ} (W : LWalk) (hval : ∀ t, W.path t ∈ U) (k : ℕ) :
    Path (W.ptMin hval (12 * k)) (W.ptMin hval (12 * (k + 1))) :=
  joinNat (p := fun j => W.ptMin hval (12 * k + j)) (fun j => W.edgeUNat hval (12 * k + j)) 12

/-- **The joining of the blocks.**  The join of all the edges of the walk is homotopic to the join
of its blocks. -/
theorem joinNat_blk {U : Set ℂ} (W : LWalk) (hval : ∀ t, W.path t ∈ U) (N : ℕ) :
    Path.Homotopic (joinNat (p := fun k => W.ptMin hval (12 * k)) (blk W hval) N)
      (joinNat (p := W.ptMin hval) (W.edgeUNat hval) (12 * N)) :=
  (joinNat_blockwise (p := W.ptMin hval) (W.edgeUNat hval) N).symm

/-- The spoke at the `k`-th ladder point: the straight segment from `γ (t k)` to the vertex
`12 * k`, inside the ball around `γ (t k)`. -/
def spoke {U : Set ℂ} {x : ℂ} {hx : x ∈ U} (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U))
    (W : LWalk) (hval : ∀ t, W.path t ∈ U) (t : ℕ → unitInterval) {δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    (hB : Metric.ball ((γ (t k) : ℂ)) δ ⊆ U)
    (htgt : ((W.ptMin hval (12 * k) : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ) :
    Path (γ (t k)) (W.ptMin hval (12 * k)) :=
  segIn (convex_ball _ _) hB (mem_ball_self hδ) htgt

theorem spoke_mem {U : Set ℂ} {x : ℂ} {hx : x ∈ U} (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U))
    (W : LWalk) (hval : ∀ t, W.path t ∈ U) (t : ℕ → unitInterval) {δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    (hB : Metric.ball ((γ (t k) : ℂ)) δ ⊆ U)
    (htgt : ((W.ptMin hval (12 * k) : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ) :
    ∀ s, (((spoke γ W hval t hδ k hB htgt) s : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ := by
  intro s
  rw [spoke, segIn_apply]
  exact (convex_ball _ _).segment_subset (mem_ball_self hδ) htgt
    (by rw [← Path.range_segment]; exact ⟨s, rfl⟩)


/-! ## The lattice approximation -/

set_option maxHeartbeats 8000000 in
theorem exists_lwalk_freeHomotopic {U : Set ℂ} (hUo : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) :
    ∃ (W : LWalk) (hval : ∀ t, W.path t ∈ U), FreeHomotopic γ (W.loopNat hval) := by
  classical
  obtain ⟨δ, hδpos, hball⟩ := exists_ball_subset_of_path hUo hx γ
  -- the mesh
  set c : ℝ := δ / 100 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hc2 : 2 * c < δ := by rw [hcdef]; linarith
  have hc16 : 16 * c < δ := by rw [hcdef]; linarith
  have hc17 : 17 * c < δ := by rw [hcdef]; linarith
  -- uniform continuity of the loop
  have hcont : Continuous (fun s : unitInterval => (γ s : ℂ)) :=
    continuous_subtype_val.comp γ.continuous
  have huc : UniformContinuous (fun s : unitInterval => (γ s : ℂ)) :=
    CompactSpace.uniformContinuous_of_continuous hcont
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨ε, hεpos, hε⟩ := huc c hc
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hεpos
  set N : ℕ := n + 1 with hNdef
  have hNpos : 0 < N := by omega
  have hNlt : 1 / (N : ℝ) < ε := by
    have hcast : ((N : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [hNdef]; push_cast; ring
    rw [hcast]; exact hn
  -- the partition
  let t : ℕ → unitInterval := part N
  have htN : t N = 1 := part_one hNpos
  have ht0 : t 0 = 0 := part_zero N
  have htmono : ∀ k ≤ N, dist (t k) (t (k + 1)) ≤ 1 / (N : ℝ) := fun k hk => part_dist_le hNpos hk
  have htge : ∀ k, N ≤ k → t k = 1 := fun k hk => part_of_le hNpos hk
  -- the loop closes at the two ends
  have hloop : ((γ (t N) : ℂ)) = ((γ (t 0) : ℂ)) := by
    rw [htN, ht0]
    exact congrArg Subtype.val (γ.target.trans γ.source.symm)
  -- successive points of the partition have close images
  have hstep : ∀ k ≤ N, dist ((γ (t k) : ℂ)) ((γ (t (k + 1)) : ℂ)) ≤ c := by
    intro k hk
    have h1 : dist (t k) (t (k + 1)) < ε := lt_of_le_of_lt (htmono k hk) hNlt
    exact le_of_lt (hε h1)
  -- the ladder on the even lattice
  let lad : ℕ → ℤ × ℤ := fun k => snap ((γ (t k) : ℂ) / (c : ℂ))
  have hlad : ∀ k, lad k = snap ((γ (t k) : ℂ) / (c : ℂ)) := fun k => rfl
  -- the displacements are small and even
  have hdisp : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6 := by
    intro k hk
    have hz : ‖(γ (t (k + 1)) : ℂ) / (c : ℂ) - (γ (t k) : ℂ) / (c : ℂ)‖ ≤ 1 := by
      rw [← sub_div, norm_div, show ‖(c : ℂ)‖ = c from by simp [abs_of_pos hc]]
      rw [div_le_one hc]
      have h2 := hstep k hk
      rw [dist_comm, dist_eq_norm] at h2
      exact h2
    obtain ⟨h1, h2⟩ := snap_diff_le (lad := lad) hlad hz
    exact ⟨by linarith, by linarith⟩
  have hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0 := fun k _ => (snap_diff_parity hlad k).1
  have hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0 := fun k _ => (snap_diff_parity hlad k).2
  have hclosed : lad N = lad 0 := by
    rw [hlad N, hlad 0, hloop]
  -- the walk
  let W : LWalk := ladderWalk N c hc lad hdisp hp1 hp2 hclosed
  have hval : ∀ s, W.path s ∈ U :=
    ladderWalk_trace hc hc16 (t := t) (g := fun s => (γ s : ℂ)) (lad := lad)
      (fun k _ => rfl) (fun k hk => hstep k hk) (fun k _ => hball (t k))
      (hq := hdisp) (hp1 := hp1) (hp2 := hp2) (hclosed := hclosed)
  -- the vertices of the walk are close to the ladder points
  have hpt_le : ∀ m, m ≤ 12 * N → ‖W.pt m - (γ (t ((bo m).1)) : ℂ)‖ ≤ 15 * c :=
    fun m hm => ladderWalk_pt_le (lad := lad) (N := N) (g := fun s => (γ s : ℂ)) (t := t) hc
      (hlad := fun k _ => rfl) (hq := hdisp) (hp1 := hp1) (hp2 := hp2) (hclosed := hclosed) hm
  have hpt_succ_le : ∀ m, m < 12 * N → ‖W.pt (m + 1) - (γ (t ((bo m).1)) : ℂ)‖ ≤ 16 * c :=
    fun m hm => ladderWalk_pt_succ_le (lad := lad) (N := N) (g := fun s => (γ s : ℂ)) (t := t)
      hc (hlad := fun k _ => rfl) (hgstep := fun k hk => hstep k hk) (hq := hdisp) (hp1 := hp1)
      (hp2 := hp2) (hclosed := hclosed) hm
  -- the vertices of one block lie in one ball
  have hpt_ball : ∀ k < N, ∀ m, 12 * k ≤ m → m ≤ 12 * (k + 1) →
      ‖W.pt m - (γ (t k) : ℂ)‖ ≤ 16 * c := by
    intro k hk m hm1 hm2
    have hb1 : (bo m).1 ≤ k + 1 := by rw [bo_eq_div]; omega
    have hb2 : k ≤ (bo m).1 := by rw [bo_eq_div]; omega
    have h15 : ‖W.pt m - (γ (t ((bo m).1)) : ℂ)‖ ≤ 15 * c := hpt_le m (by omega)
    have hc' : ‖(γ (t ((bo m).1)) : ℂ) - (γ (t k) : ℂ)‖ ≤ c := by
      have hcases : (bo m).1 = k ∨ (bo m).1 = k + 1 := by omega
      rcases hcases with h | h
      · rw [h, sub_self, norm_zero]; linarith
      · rw [h, ← dist_eq_norm, dist_comm]
        exact hstep k (le_of_lt hk)
    have htri : ‖W.pt m - (γ (t k) : ℂ)‖
        ≤ ‖W.pt m - (γ (t ((bo m).1)) : ℂ)‖ + ‖(γ (t ((bo m).1)) : ℂ) - (γ (t k) : ℂ)‖ := by
      have h := norm_add_le (W.pt m - (γ (t ((bo m).1)) : ℂ))
        ((γ (t ((bo m).1)) : ℂ) - (γ (t k) : ℂ))
      rwa [show W.pt m - (γ (t ((bo m).1)) : ℂ) + ((γ (t ((bo m).1)) : ℂ) - (γ (t k) : ℂ))
        = W.pt m - (γ (t k) : ℂ) from by ring] at h
    linarith
  -- the spokes
  have hmid : ∀ k, ((W.ptMin hval (12 * k) : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ := by
    intro k
    rw [Metric.mem_ball, dist_eq_norm]
    by_cases hk : k ≤ N
    · have h1 : ((W.ptMin hval (12 * k) : ↥U) : ℂ) = c * gpt (lad k) := by
        rw [ptMin_val_of_le W hval (by rw [show W.n = 12 * N from rfl]; omega : 12 * k ≤ W.n)]
        exact ladderWalk_pt_block hk
      rw [h1]
      have h2 := norm_pt_lad_le (g := fun s => (γ s : ℂ)) (t := t) (k := k) hc (hlad k)
      linarith
    · have hmin : min (12 * k) W.n = W.n := by
        rw [show W.n = 12 * N from rfl, Nat.min_eq_right]
        omega
      have h1 : ((W.ptMin hval (12 * k) : ↥U) : ℂ) = c * gpt (lad N) := by
        rw [LWalk.ptMin_apply, hmin, show W.n = 12 * N from rfl]
        exact ladderWalk_pt_block (le_refl N)
      rw [h1]
      have h2 : ‖c * gpt (lad N) - (γ (t N) : ℂ)‖ ≤ 2 * c :=
        norm_pt_lad_le (g := fun s => (γ s : ℂ)) (t := t) (k := N) hc (hlad N)
      have h3 : (γ (t k) : ℂ) = (γ (t N) : ℂ) :=
        congrArg (fun s => (γ s : ℂ)) ((htge k (Nat.le_of_not_le hk)).trans htN.symm)
      rw [h3]
      linarith [hc2]
  let e : ∀ k, Path (γ (t k)) (W.ptMin hval (12 * k)) :=
    fun k => spoke γ W hval t hδpos k (hball (t k)) (hmid k)
  have emem : ∀ k, ∀ s, ((e k s : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ :=
    fun k s => spoke_mem γ W hval t hδpos k (hball (t k)) (hmid k) s

  have hedge_mem : ∀ k < N, ∀ j < 12, ∀ u, ((W.edgeUNat hval (12 * k + j) u : ↥U) : ℂ)
      ∈ Metric.ball ((γ (t k) : ℂ)) δ := by
    intro k hk j hj u
    have hm1 : 12 * k + j < W.n := by rw [show W.n = 12 * N from rfl]; omega
    rw [show ((W.edgeUNat hval (12 * k + j) u : ↥U) : ℂ) = W.edge (12 * k + j) u from by
      rw [LWalk.edgeUNat_apply, dif_pos hm1]]
    have hseg : Path.segment (W.pt (12 * k + j)) (W.pt (12 * k + j + 1)) u
        ∈ Metric.ball ((γ (t k) : ℂ)) (17 * c) :=
      (convex_ball _ _).segment_subset
        (by rw [Metric.mem_ball, dist_eq_norm]
            have h := hpt_ball k hk (12 * k + j) (by omega) (by omega)
            linarith)
        (by rw [Metric.mem_ball, dist_eq_norm]
            have h := hpt_ball k hk (12 * k + j + 1) (by omega) (by omega)
            linarith)
        (by rw [← Path.range_segment]; exact ⟨u, rfl⟩)
    rw [Metric.mem_ball, dist_eq_norm] at hseg
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hseg (le_of_lt hc17)
  have hblk_mem : ∀ k < N, ∀ s, ((blk W hval k s : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ := by
    intro k hk s
    have hgen : ∀ j ≤ 12, ∀ u, (((joinNat (p := fun j => W.ptMin hval (12 * k + j))
        (fun j => W.edgeUNat hval (12 * k + j)) j) u : ↥U) : ℂ)
        ∈ Metric.ball ((γ (t k) : ℂ)) δ := by
      intro j
      induction j with
      | zero =>
        intro _ u
        change (((joinNat (p := fun j => W.ptMin hval (12 * k + j))
          (fun j => W.edgeUNat hval (12 * k + j)) 0) u : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ
        simpa [joinNat, Nat.add_zero] using hmid k
      | succ j ih =>
        intro hj u
        change ((((joinNat (p := fun j => W.ptMin hval (12 * k + j))
          (fun j => W.edgeUNat hval (12 * k + j)) j).trans
          (W.edgeUNat hval (12 * k + j))) u : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ
        rw [Path.trans_apply]
        by_cases h : (u : ℝ) ≤ 1 / 2
        · rw [dif_pos h]; exact ih (by omega) _
        · rw [dif_neg h]; exact hedge_mem k hk j (by omega) _
    exact hgen 12 (le_refl 12) s
  -- the three-piece family
  let F : ∀ k, Path (γ (t k)) (γ (t (k + 1))) :=
    fun k => (e k).trans ((blk W hval k).trans ((e (k + 1)).symm))
  have emem2 : ∀ k, ∀ s, ‖((e k s : ↥U) : ℂ) - (γ (t k) : ℂ)‖ ≤ 3 * c := by
    intro k s
    have hmid2 : ‖((W.ptMin hval (12 * k) : ↥U) : ℂ) - (γ (t k) : ℂ)‖ ≤ 2 * c := by
      by_cases hk : k ≤ N
      · rw [ptMin_val_of_le W hval (by rw [show W.n = 12 * N from rfl]; omega)]
        rw [ladderWalk_pt_block hk]
        exact norm_pt_lad_le (g := fun s => (γ s : ℂ)) (t := t) (k := k) hc (hlad k)
      · rw [show ((W.ptMin hval (12 * k) : ↥U) : ℂ) = c * gpt (lad N) from by
          rw [LWalk.ptMin_apply]
          have hmin : min (12 * k) W.n = W.n := by
            rw [show W.n = 12 * N from rfl, Nat.min_eq_right]; omega
          rw [hmin, show W.n = 12 * N from rfl]
          exact ladderWalk_pt_block (le_refl N)]
        have h2 : ‖c * gpt (lad N) - (γ (t N) : ℂ)‖ ≤ 2 * c :=
          norm_pt_lad_le (g := fun s => (γ s : ℂ)) (t := t) (k := N) hc (hlad N)
        have h3 : (γ (t k) : ℂ) = (γ (t N) : ℂ) :=
          congrArg (fun s => (γ s : ℂ)) ((htge k (Nat.le_of_not_le hk)).trans htN.symm)
        rw [h3]
        exact h2
    dsimp only [e]
    rw [spoke, segIn_apply]
    have hseg : Path.segment (γ (t k) : ℂ) ((W.ptMin hval (12 * k) : ↥U) : ℂ) s
        ∈ Metric.ball ((γ (t k) : ℂ)) (3 * c) :=
      (convex_ball _ _).segment_subset (mem_ball_self (by linarith [hc]))
        (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hmid2 (by linarith [hc]))
        (by rw [← Path.range_segment]; exact ⟨s, rfl⟩)
    rw [Metric.mem_ball, dist_eq_norm] at hseg
    exact le_of_lt hseg
  have hFmem : ∀ k < N, ∀ s, ((F k s : ↥U) : ℂ) ∈ Metric.ball ((γ (t k) : ℂ)) δ := by
    intro k hk s
    have hmem : (F k) s ∈ Set.range (F k) := ⟨s, rfl⟩
    rw [show F k = (e k).trans ((blk W hval k).trans ((e (k + 1)).symm)) from rfl,
      Path.trans_range] at hmem
    rcases hmem with hmem | hmem
    · obtain ⟨u, hu⟩ := hmem
      rw [← hu]
      exact emem k u
    · rw [Path.trans_range] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨u, hu⟩ := hmem
        rw [← hu]
        exact hblk_mem k hk u
      · obtain ⟨u, hu⟩ := hmem
        rw [← hu, Path.symm_apply]
        simp only [Function.comp_apply]
        rw [Metric.mem_ball, dist_eq_norm]
        have h5 := emem2 (k + 1) (unitInterval.symm u)
        have h6 : ‖(γ (t (k + 1)) : ℂ) - (γ (t k) : ℂ)‖ ≤ c := by
          rw [← dist_eq_norm, dist_comm]
          exact hstep k (le_of_lt hk)
        have htri : ‖(((e (k + 1)) (unitInterval.symm u) : ↥U) : ℂ) - (γ (t k) : ℂ)‖
            ≤ ‖(((e (k + 1)) (unitInterval.symm u) : ↥U) : ℂ) - (γ (t (k + 1)) : ℂ)‖
              + ‖(γ (t (k + 1)) : ℂ) - (γ (t k) : ℂ)‖ := by
          have h := norm_add_le ((((e (k + 1)) (unitInterval.symm u) : ↥U) : ℂ) - (γ (t (k + 1)) : ℂ))
            ((γ (t (k + 1)) : ℂ) - (γ (t k) : ℂ))
          rwa [show (((e (k + 1)) (unitInterval.symm u) : ↥U) : ℂ) - (γ (t (k + 1)) : ℂ)
            + ((γ (t (k + 1)) : ℂ) - (γ (t k) : ℂ))
            = (((e (k + 1)) (unitInterval.symm u) : ↥U) : ℂ) - (γ (t k) : ℂ) from by ring] at h
        linarith [h5, h6, htri, hc16, hc, hδpos]
  -- per-block homotopy
  have hblock : ∀ k < N, Path.Homotopic (γ.restr (t k) (t (k + 1))) (F k) := by
    intro k hk
    refine homotopic_of_convex_subset (convex_ball _ _)
      ⟨(γ (t k) : ℂ), mem_ball_self hδpos⟩ (hball (t k)) _ _ ?_ ?_
    · -- the values of the restriction of γ
      intro s
      rw [Metric.mem_ball, dist_eq_norm, Path.restr_apply]
      have h1 : dist (t k) (Path.affine (t k) (t (k + 1)) s) ≤ 1 / (N : ℝ) :=
        part_affine_dist hNpos hk s
      have h4 : dist (t k) (Path.affine (t k) (t (k + 1)) s) < ε :=
        lt_of_le_of_lt h1 hNlt
      have h5 := hε h4
      have h5' : ‖(γ (Path.affine (t k) (t (k + 1)) s) : ℂ) - (γ (t k) : ℂ)‖ ≤ c := by
        rw [← dist_eq_norm, dist_comm]
        exact le_of_lt h5
      linarith
    · intro s
      rw [Metric.mem_ball, dist_eq_norm]
      have h6 := hFmem k hk s
      rw [Metric.mem_ball, dist_eq_norm] at h6
      exact h6
  -- the join over the blocks
  have hjoin : Path.Homotopic (joinRestr γ t N) (joinNat F N) := by
    rw [joinRestr_eq_joinNat]
    exact joinNat_congr_lt N (fun k hk => hblock k hk)
  -- telescoping
  have htele : Path.Homotopic (joinNat F N)
      ((e 0).trans ((joinNat (p := fun k => W.ptMin hval (12 * k)) (blk W hval) N).trans
        ((e N).symm))) :=
    joinNat_conj e (blk W hval) N
  -- flattening
  have hflat : Path.Homotopic (joinNat (p := fun k => W.ptMin hval (12 * k)) (blk W hval) N)
      (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) :=
    joinNat_blk W hval N
  -- the loop realization
  have hloopNat : Path.Homotopic (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n)
      (Path.cast (W.loopNat hval) rfl (W.ptMin_zero_eq_last hval).symm) := by
    have heq : Path.cast (W.loopNat hval) rfl (W.ptMin_zero_eq_last hval).symm
        = joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n := by
      rw [LWalk.loopNat_eq_joinNat]
      ext t
      rfl
    rw [heq]
  -- the endpoints
  have hx0 : (⟨x, hx⟩ : ↥U) = γ (t 0) := by
    rw [ht0]; exact γ.source.symm
  have hxN : (⟨x, hx⟩ : ↥U) = γ (t N) := by
    rw [htN]; exact γ.target.symm
  -- the chain
  have hchain : Path.Homotopic γ
      (Path.cast ((e 0).trans (((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n)).trans
        ((e N).symm))) hx0 hxN) := by
    have hγ : Path.Homotopic γ (Path.cast (joinRestr γ t N) hx0 hxN) := by
      have heq : Path.cast (γ.restr (t 0) (t N)) hx0 hxN = γ := by
        ext s
        rw [Path.cast_coe, Path.restr_apply, ht0, htN]
        simp only [Path.cast_coe, Path.restr_apply, ht0, htN, affine_zero_one]
      have h1 : Path.Homotopic (Path.cast (γ.restr (t 0) (t N)) hx0 hxN)
          (Path.cast (joinRestr γ t N) hx0 hxN) :=
        Path.Homotopic.pathCast (homotopic_restr_joinRestr γ t N) hx0 hxN
      rwa [heq] at h1
    refine hγ.trans ?_
    refine Path.Homotopic.pathCast ?_ hx0 hxN
    exact hjoin.trans (htele.trans (Path.Homotopic.hcomp (Path.Homotopic.refl _)
      (Path.Homotopic.hcomp hflat (Path.Homotopic.refl _))))
  -- the cast decomposition
  have hcast : Path.cast ((e 0).trans ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans
        ((e N).symm))) hx0 hxN
      = (Path.cast (e 0) hx0 rfl).trans ((Path.cast (joinNat (p := W.ptMin hval)
          (W.edgeUNat hval) W.n) rfl rfl).trans (Path.cast ((e N).symm) rfl hxN)) := by
    rw [cast_trans (e 0) ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans ((e N).symm))
      hx0 hxN]
    rw [cast_trans (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) ((e N).symm) rfl hxN]
    rfl
  -- the conjugating path
  let a : Path (⟨x, hx⟩ : ↥U) (W.ptMin hval 0) := Path.cast (e 0) hx0 rfl
  have ha : ((a : Path (⟨x, hx⟩ : ↥U) (W.ptMin hval 0)) = Path.cast (e 0) hx0 rfl) := rfl
  have hcast0 : Path.cast (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) rfl rfl
      = joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n := Path.cast_rfl_rfl _
  -- the last spoke, based at `W.ptMin hval 0`
  have hb : W.ptMin hval 0 = W.ptMin hval (12 * N) := by
    rw [show (12 : ℕ) * N = W.n from rfl]
    exact W.ptMin_zero_eq_last hval
  let Z : Path (W.ptMin hval (12 * N)) (⟨x, hx⟩ : ↥U) :=
    Path.cast ((e N).symm) rfl hxN
  let X : Path (W.ptMin hval (12 * N)) (W.ptMin hval 0) :=
    Path.cast (Path.refl (W.ptMin hval (12 * N))) rfl hb
  -- (Q1): Z is homotopic to X · a⁻¹
  have hQ1 : Path.Homotopic Z (X.trans a.symm) := by
    refine homotopic_of_convex_subset (convex_ball _ _)
      ⟨(γ (t N) : ℂ), mem_ball_self hδpos⟩ (hball (t N)) _ _ ?_ ?_
    · intro s
      rw [Metric.mem_ball, dist_eq_norm]
      have h := emem N (unitInterval.symm s)
      rw [Metric.mem_ball, dist_eq_norm] at h
      have h1 : ((Z s : ↥U) : ℂ) = ((e N) (unitInterval.symm s) : ↥U) := by
        show ((Path.cast ((e N).symm) rfl hxN s : ↥U) : ℂ) = _
        rw [Path.cast_coe]
        rfl
      rw [h1]
      exact h
    · -- the values of `X · a.symm`
      intro s
      have hmem : (X.trans a.symm) s ∈ Set.range (X.trans a.symm) := ⟨s, rfl⟩
      rw [Path.trans_range] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨u, hu⟩ := hmem
        rw [← hu, Metric.mem_ball, dist_eq_norm]
        have hX : ∀ v : unitInterval, ((X v : ↥U) : ℂ) = (W.ptMin hval (12 * N) : ↥U) := by
          intro v
          show ((Path.cast (Path.refl (W.ptMin hval (12 * N))) rfl hb v : ↥U) : ℂ) = _
          rw [Path.cast_coe]
          rfl
        rw [hX u]
        have h2 : ((W.ptMin hval (12 * N) : ↥U) : ℂ) = c * gpt (lad N) := by
          rw [ptMin_val_of_le W hval (by rw [show W.n = 12 * N from rfl])]
          exact ladderWalk_pt_block (le_refl N)
        rw [h2]
        have h3 : ‖c * gpt (lad N) - (γ (t N) : ℂ)‖ ≤ 2 * c :=
          norm_pt_lad_le (g := fun s => (γ s : ℂ)) (t := t) (k := N) hc (hlad N)
        linarith [h3, hc2]
      · obtain ⟨u, hu⟩ := hmem
        rw [← hu, Path.symm_apply, Function.comp_apply, Metric.mem_ball, dist_eq_norm]
        have h5 := emem 0 (unitInterval.symm u)
        rw [Metric.mem_ball, dist_eq_norm] at h5
        have h6 : (γ (t 0) : ℂ) = (γ (t N) : ℂ) := hloop.symm
        rw [h6] at h5
        exact h5
  -- (Q2)
  have hQ2 : Path.Homotopic
      ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans X)
      (Path.cast (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) rfl hb) := by
    have hmain : Path.Homotopic
        ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans (Path.refl (W.ptMin hval (12 * N))))
        (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) := Path.Homotopic.trans_refl _
    have hXeq : Path.cast ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans
        (Path.refl (W.ptMin hval (12 * N)))) rfl hb
        = (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans X := by
      rw [cast_trans (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n)
        (Path.refl (W.ptMin hval (12 * N))) rfl hb, Path.cast_rfl_rfl]
      rfl
    rw [← hXeq]
    exact Path.Homotopic.pathCast hmain rfl hb
  -- (Q3): the cast of the loop realization
  have hQ3 : Path.Homotopic (Path.cast (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) rfl hb)
      (W.loopNat hval) := by
    have heq : Path.cast (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) rfl hb
        = W.loopNat hval := by
      rw [LWalk.loopNat_eq_joinNat]
      ext t
      rfl
    rw [heq]
  -- assemble the conjugation
  have hconj : Path.Homotopic γ (a.trans ((W.loopNat hval).trans a.symm)) := by
    refine hchain.trans ?_
    have step : Path.Homotopic
        ((a.trans ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans Z)))
        (a.trans ((W.loopNat hval).trans a.symm)) := by
      refine Path.Homotopic.hcomp (Path.Homotopic.refl _) ?_
      have h1 : Path.Homotopic
          ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans Z)
          ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans (X.trans a.symm)) :=
        Path.Homotopic.hcomp (Path.Homotopic.refl _) hQ1
      have h2 : Path.Homotopic
          ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans (X.trans a.symm))
          (((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans X).trans a.symm) :=
        (Path.Homotopic.trans_assoc _ _ _).symm
      have h3 : Path.Homotopic
          (((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).trans X).trans a.symm)
          ((Path.cast (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n) rfl hb).trans a.symm) :=
        Path.Homotopic.hcomp hQ2 (Path.Homotopic.refl _)
      exact h1.trans (h2.trans (h3.trans (Path.Homotopic.hcomp hQ3 (Path.Homotopic.refl _))))
    rw [hcast]
    exact step
  exact ⟨W, hval, freeHomotopic_of_conj γ (W.loopNat hval) hconj⟩

end

end Work.SphereJordan
