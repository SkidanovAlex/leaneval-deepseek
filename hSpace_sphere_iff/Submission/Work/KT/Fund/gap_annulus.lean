import Mathlib

namespace Work.KT.Fund

/-- **Gap around the unit circle.**

Let `X` be a compact Hausdorff space, `b` a square matrix of continuous complex-valued
functions on `X`, such that for every `x` and every `z` on the unit circle the matrix
`z • 1 + b(x)` is invertible.  Then invertibility persists on a whole annulus
`1 - ε ≤ ‖z‖ ≤ 1 + ε` around the unit circle, with `ε` uniform in `x`.

The proof is the usual ``compactness of the bad set'' argument.  Write
`g(x,z) = det (z • 1 + b(x))`; this is continuous.  The bad set `Z = {g = 0}` is closed,
and `X × {‖z‖ = 1}` is mapped into its complement by hypothesis.  Intersecting with the
compact annulus `T = {1/2 ≤ ‖z‖ ≤ 3/2}` and using Cantor's intersection theorem for the
decreasing family `Z ∩ T ∩ {|‖z‖-1| ≤ 1/(k+1)}` yields an index `k` for which the
intersection is empty, which is the required uniform gap. -/
theorem gap_annulus (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (b : Matrix (Fin n) (Fin n) C(X, ℂ))
    (hb : ∀ (x : X) (z : ℂ), ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f x))) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ (x : X) (z : ℂ), 1 - ε ≤ ‖z‖ → ‖z‖ ≤ 1 + ε →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f x)) := by
  classical
  -- the matrix-valued function whose invertibility we study
  set F : X × ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun p => p.2 • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f p.1) with hFdef
  have hFcont : Continuous F := by
    rw [hFdef]
    refine Continuous.add ?_ ?_
    · exact continuous_snd.smul continuous_const
    · apply continuous_matrix
      intro i j
      simp only [Matrix.map_apply]
      exact (b i j).continuous.comp continuous_fst
  have hg : Continuous (fun p : X × ℂ => (F p).det) := hFcont.matrix_det
  -- the bad locus
  set Z : Set (X × ℂ) := {p | (F p).det = 0} with hZdef
  have hZcl : IsClosed Z := by
    rw [hZdef]; exact isClosed_eq hg continuous_const
  -- a compact bounded annulus
  set T : Set (X × ℂ) := {p | (1 / 2 : ℝ) ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ (3 / 2 : ℝ)} with hTdef
  have hTcl : IsClosed T := by
    rw [hTdef]
    have hc : Continuous (fun p : X × ℂ => ‖p.2‖) := continuous_norm.comp continuous_snd
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  have hTcomp : IsCompact T := by
    refine (isCompact_univ.prod (isCompact_closedBall (0 : ℂ) (3 / 2 : ℝ))).of_isClosed_subset
      hTcl ?_
    intro p hp
    rw [hTdef] at hp
    exact ⟨trivial, by rw [Metric.mem_closedBall, dist_zero_right]; exact hp.2⟩
  -- the decreasing family of bad points in shrinking annuli
  set t : ℕ → Set (X × ℂ) :=
    fun k => Z ∩ T ∩ {p : X × ℂ | |‖p.2‖ - 1| ≤ 1 / ((k : ℝ) + 1)} with htdef
  have htcl : ∀ k, IsClosed (t k) := by
    intro k
    have hk : t k = Z ∩ T ∩ {p : X × ℂ | |‖p.2‖ - 1| ≤ 1 / ((k : ℝ) + 1)} := by
      simp only [htdef]
    rw [hk]
    refine (hZcl.inter hTcl).inter ?_
    have hc : Continuous (fun p : X × ℂ => |‖p.2‖ - 1|) :=
      ((continuous_norm.comp continuous_snd).sub continuous_const).abs
    exact isClosed_le hc continuous_const
  have htsub : ∀ i, t (i + 1) ⊆ t i := by
    intro i p hp
    simp only [htdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hp ⊢
    refine ⟨hp.1, le_trans hp.2 ?_⟩
    rw [Nat.cast_add, Nat.cast_one]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have ht0 : IsCompact (t 0) := by
    refine hTcomp.of_isClosed_subset (htcl 0) ?_
    intro p hp
    simp only [htdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hp
    exact hp.1.2
  -- the whole intersection would be a point on the unit circle at which `F` is singular
  have hdisj : ¬ (⋂ k, t k).Nonempty := by
    rintro ⟨p, hp⟩
    have hbnd : ∀ k : ℕ, |‖p.2‖ - 1| ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      have h := Set.mem_iInter.mp hp k
      simp only [htdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at h
      exact h.2
    have hnorm : ‖p.2‖ = 1 := by
      have hzero : |‖p.2‖ - 1| ≤ 0 := by
        refine le_of_forall_pos_le_add (fun ε hε => ?_)
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        calc |‖p.2‖ - 1| ≤ 1 / ((k : ℝ) + 1) := hbnd k
          _ ≤ ε := le_of_lt hk
          _ = 0 + ε := by ring
      have : ‖p.2‖ - 1 = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
      linarith
    have hunit : IsUnit (F p) := by
      have h1 : IsUnit (p.2 • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f p.1)) :=
        hb p.1 p.2 hnorm
      simpa only [hFdef] using h1
    have hdet0 : (F p).det = 0 := by
      have h := Set.mem_iInter.mp hp 0
      simp only [htdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at h
      exact h.1.1
    have hunitdet : IsUnit ((F p).det) := (Matrix.isUnit_iff_isUnit_det (F p)).mp hunit
    exact (isUnit_iff_ne_zero.mp hunitdet) hdet0
  -- some member of the family is already empty: the uniform gap
  have hsome : ∃ k, t k = ∅ := by
    by_contra hcon
    push Not at hcon
    exact hdisj (IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      t htsub hcon ht0 htcl)
  obtain ⟨k, hk⟩ := hsome
  refine ⟨min (1 / 2 : ℝ) (1 / ((k : ℝ) + 1)), lt_min (by norm_num) (by positivity),
    lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
  intro x z hzl hzr
  have hε1 : min (1 / 2 : ℝ) (1 / ((k : ℝ) + 1)) ≤ 1 / 2 := min_le_left _ _
  have hε2 : min (1 / 2 : ℝ) (1 / ((k : ℝ) + 1)) ≤ 1 / ((k : ℝ) + 1) := min_le_right _ _
  have hzg : (1 / 2 : ℝ) ≤ ‖z‖ := by linarith
  have hzl2 : ‖z‖ ≤ (3 / 2 : ℝ) := by linarith
  have hzT : (x, z) ∈ T := by
    rw [hTdef]; exact ⟨hzg, hzl2⟩
  have hzabs : |‖z‖ - 1| ≤ 1 / ((k : ℝ) + 1) := by
    have h1 : |‖z‖ - 1| ≤ min (1 / 2 : ℝ) (1 / ((k : ℝ) + 1)) := by
      rw [abs_le]; constructor <;> linarith
    exact le_trans h1 hε2
  have hnotZ : (x, z) ∉ Z := by
    intro hZ
    have hmem : (x, z) ∈ t k := by
      have h2 : (x, z) ∈ Z ∩ T ∩ {p : X × ℂ | |‖p.2‖ - 1| ≤ 1 / ((k : ℝ) + 1)} :=
        ⟨⟨hZ, hzT⟩, hzabs⟩
      simpa only [htdef] using h2
    rw [hk] at hmem
    exact Set.notMem_empty _ hmem
  have hdet : (F (x, z)).det ≠ 0 := hnotZ
  show IsUnit (F (x, z))
  exact (Matrix.isUnit_iff_isUnit_det (F (x, z))).mpr (isUnit_iff_ne_zero.mpr hdet)

end Work.KT.Fund
