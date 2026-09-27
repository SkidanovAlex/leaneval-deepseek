import Mathlib
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.KT.Fund.isUnit_matrix_forall

namespace Work.Idx

noncomputable section

/-- **Uniform gap of a continuous function over the unit circle.**

If `f : X × ℂ → ℂ` is continuous on a compact Hausdorff space `X` and vanishes nowhere on the
cylinder `X × {‖z‖ = 1}` over the unit circle, then it vanishes nowhere on a whole annulus
`X × {z | 1 - ε ≤ ‖z‖ ≤ 1 + ε}` around it, with a single `ε > 0` working for all `x ∈ X`.

Proof: the bad set `Z = {f = 0}` is closed.  If no `ε` worked, the sets
`t k = Z ∩ {1/2 ≤ ‖z‖ ≤ 3/2} ∩ {|‖z‖ - 1| ≤ 1/(k+1)}` would be a decreasing sequence of nonempty
compact sets, hence (Cantor) would have a common point `p`; then `f p = 0` and `‖p.2‖ = 1`,
contradicting the hypothesis. -/
theorem continuous_annulus_gap {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (f : X × ℂ → ℂ) (hf : Continuous f) (h : ∀ x z, ‖z‖ = 1 → f (x, z) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x z, 1 - ε ≤ ‖z‖ → ‖z‖ ≤ 1 + ε → f (x, z) ≠ 0 := by
  classical
  -- the bad locus
  set Z : Set (X × ℂ) := {p | f p = 0} with hZdef
  have hZcl : IsClosed Z := by rw [hZdef]; exact isClosed_eq hf continuous_const
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
  -- the whole intersection would be a point on the unit circle at which `f` vanishes
  have hdisj : ¬ (⋂ k, t k).Nonempty := by
    rintro ⟨p, hp⟩
    have hbnd : ∀ k : ℕ, |‖p.2‖ - 1| ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      have h1 := Set.mem_iInter.mp hp k
      simp only [htdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at h1
      exact h1.2
    have hnorm : ‖p.2‖ = 1 := by
      have hzero : |‖p.2‖ - 1| ≤ 0 := by
        refine le_of_forall_pos_le_add (fun ε hε => ?_)
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        calc |‖p.2‖ - 1| ≤ 1 / ((k : ℝ) + 1) := hbnd k
          _ ≤ ε := le_of_lt hk
          _ = 0 + ε := by ring
      have : ‖p.2‖ - 1 = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
      linarith
    have hf0 : f p = 0 := by
      have h1 := Set.mem_iInter.mp hp 0
      simp only [htdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at h1
      exact h1.1.1
    exact h p.1 p.2 hnorm hf0
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
  have hε2 : min (1 / 2 : ℝ) (1 / ((k : ℝ) + 1)) ≤ 1 / ((k : ℝ) + 1) := min_le_right _ _
  have hzg : (1 / 2 : ℝ) ≤ ‖z‖ := by linarith [min_le_left (1 / 2 : ℝ) (1 / ((k : ℝ) + 1))]
  have hzl2 : ‖z‖ ≤ (3 / 2 : ℝ) := by linarith [min_le_left (1 / 2 : ℝ) (1 / ((k : ℝ) + 1))]
  have hzT : (x, z) ∈ T := by rw [hTdef]; exact ⟨hzg, hzl2⟩
  have hzabs : |‖z‖ - 1| ≤ 1 / ((k : ℝ) + 1) := by
    have h1 : |‖z‖ - 1| ≤ min (1 / 2 : ℝ) (1 / ((k : ℝ) + 1)) := by
      rw [abs_le]; constructor <;> linarith
    exact le_trans h1 hε2
  intro hf0
  have hmem : (x, z) ∈ t k := by
    have h2 : (x, z) ∈ Z ∩ T ∩ {p : X × ℂ | |‖p.2‖ - 1| ≤ 1 / ((k : ℝ) + 1)} :=
      ⟨⟨by rw [hZdef]; exact hf0, hzT⟩, hzabs⟩
    simpa only [htdef] using h2
  rw [hk] at hmem
  exact Set.notMem_empty _ hmem

/-- **The spectral gap of a matrix pencil.** If the pencil `z ↦ z • A + B` over `C(X, ℂ)` is
invertible at every point of the unit circle, then it is invertible on a whole annulus
`1 - ε ≤ ‖z‖ ≤ 1 + ε` around it (`ε` uniform in `x`).  This is the pencil analogue of
`Work.KT.Fund.gap_annulus`.

Route: `IsUnit (z • A + B)` for matrices over `C(X, ℂ)` is equivalent to `det (z•A + B)` vanishing
nowhere (`Matrix.isUnit_iff_isUnit_det`, `ContinuousMap.isUnit_iff_forall_ne_zero`,
`Work.KT.Fund.isUnit_matrix_forall`), and `(x,z) ↦ det (z • A(x) + B(x))` is continuous; on the
compact `X × S¹` the continuous function `‖resolvent‖ = ‖(z•A+B)⁻¹‖` is bounded, and closeness of
`w` to `z` plus the Neumann series makes the pencil invertible for `|w - z|` small; compactness of
`S¹` gives the uniform `ε`.  Either this route, or the `Work.KT.Fund.gap_annulus` route (closed
zero set, compactness of `X × {1 - ε ≤ ‖z‖ ≤ 1 + ε}`, Cantor's intersection theorem) works. -/
theorem pen_annulus (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {N : ℕ} (A B : Matrix (Fin N) (Fin N) C(X, ℂ))
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ z : ℂ, 1 - ε ≤ ‖z‖ → ‖z‖ ≤ 1 + ε → IsUnit (z • A + B) := by
  classical
  -- the pencil evaluated pointwise
  have hmap : ∀ (z : ℂ) (x : X),
      (z • A + B).map (fun g : C(X, ℂ) => g x) =
        z • (A.map (fun g : C(X, ℂ) => g x)) + B.map (fun g : C(X, ℂ) => g x) := by
    intro z x
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
    rw [ContinuousMap.add_apply, ContinuousMap.smul_apply]
  -- the continuous family of pointwise determinants
  set G : X × ℂ → Matrix (Fin N) (Fin N) ℂ := fun p =>
    p.2 • (A.map (fun g : C(X, ℂ) => g p.1)) + B.map (fun g : C(X, ℂ) => g p.1) with hGdef
  have hGcont : Continuous G := by
    rw [hGdef]
    apply continuous_matrix
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
    fun_prop
  have hGdet : Continuous (fun p : X × ℂ => (G p).det) := hGcont.matrix_det
  have hGeq : ∀ (z : ℂ) (x : X),
      G (x, z) = (z • A + B).map (fun g : C(X, ℂ) => g x) := by
    intro z x
    rw [hGdef]
    exact (hmap z x).symm
  have hne : ∀ x z, ‖z‖ = 1 → (G (x, z)).det ≠ 0 := by
    intro x z hz
    have h1 : IsUnit ((z • A + B).map (fun g : C(X, ℂ) => g x)) :=
      (Work.KT.Fund.isUnit_matrix_forall N (z • A + B)).mp (hunit z hz) x
    have h2 : IsUnit (((z • A + B).map (fun g : C(X, ℂ) => g x))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp h1
    rw [← hGeq z x] at h2
    exact isUnit_iff_ne_zero.mp h2
  obtain ⟨ε, hε0, hε1, hε⟩ :=
    continuous_annulus_gap (fun p : X × ℂ => (G p).det) hGdet hne
  refine ⟨ε, hε0, hε1, ?_⟩
  intro z hzl hzr
  refine (Work.KT.Fund.isUnit_matrix_forall N (z • A + B)).mpr ?_
  intro x
  have h0 : (G (x, z)).det ≠ 0 := hε x z hzl hzr
  rw [hGeq z x] at h0
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h0)

end

end Work.Idx
