import Mathlib

namespace Work.RedProj

open Set Metric

/-- Auxiliary: the point `i / (n+1)` of the unit interval, capped so that it is
always a well defined element of `[0,1]`.  It is used to subdivide a path. -/
noncomputable def up (n i : ℕ) : unitInterval :=
  ⟨(min i (n+1) : ℝ) / (n+1), by
    have h : (0:ℝ) < (n+1) := by positivity
    constructor
    · positivity
    · rw [div_le_one h]; exact_mod_cast min_le_right i (n+1)⟩

/-- A continuous map from the unit interval into `ℂ` can be subdivided into
finitely many pieces each of diameter at most `ε`. -/
lemma subdivision {γ : unitInterval → ℂ} (hγ : Continuous γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ i < n+1, dist (γ (up n i)) (γ (up n (i+1))) ≤ ε := by
  have hunif : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous hγ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp hunif ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  refine ⟨n, ?_⟩
  intro i hi
  apply le_of_lt
  apply hδ
  rw [Subtype.dist_eq]
  simp only [up]
  have hm1 : min (i:ℝ) ((n:ℝ)+1) = (i:ℝ) := min_eq_left (by exact_mod_cast Nat.le_of_lt hi)
  have hm2 : min ((i+1:ℕ):ℝ) ((n:ℝ)+1) = ((i+1:ℕ):ℝ) :=
    min_eq_left (by exact_mod_cast Nat.succ_le_of_lt hi)
  rw [hm1, hm2, Real.dist_eq]
  have hkey : (i:ℝ)/((n:ℝ)+1) - ((i+1:ℕ):ℝ)/((n:ℝ)+1) = -(1/((n:ℝ)+1)) := by
    push_cast; rw [← sub_div]; ring
  rw [hkey, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1/((n:ℝ)+1))]
  simpa using hn

/-- **Chain lemma for open preconnected subsets of `ℂ`.**

If `W` is open and preconnected in `ℂ`, then any two of its points can be joined
by a finite chain of points inside `W` which is `ε`-fine (consecutive points at
distance at most `ε`) and at distance larger than `5 ε` from the complement of
`W`, for some `0 < ε ≤ η`. -/
theorem chain_of_isPreconnected {W : Set ℂ} (hWo : IsOpen W) (hWc : IsPreconnected W)
    {a z : ℂ} (ha : a ∈ W) (hz : z ∈ W) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ η ∧ ∃ N : ℕ, ∃ p : ℕ → ℂ,
      p 0 = a ∧ p N = z ∧
      (∀ i ≤ N, Metric.ball (p i) (5 * ε) ⊆ W) ∧
      (∀ i < N, ‖p (i + 1) - p i‖ ≤ ε) := by
  -- `W` is an open preconnected subset of the locally path-connected space `ℂ`,
  -- hence path connected.
  have hWconn : IsConnected W := ⟨⟨a, ha⟩, hWc⟩
  have hWpath : IsPathConnected W := (hWo.isConnected_iff_isPathConnected).mp hWconn
  obtain ⟨γ, hγ⟩ := hWpath.joinedIn a ha z hz
  -- The image of the path is a compact subset of the open set `W`; therefore some
  -- thickening of it is still contained in `W`.
  have hKcpt : IsCompact (range γ) := isCompact_range γ.continuous
  have hKW : range γ ⊆ W := by rintro _ ⟨t, rfl⟩; exact hγ t
  obtain ⟨δT, hδTpos, hδTsub⟩ := hKcpt.exists_thickening_subset_open hWo hKW
  set ε : ℝ := min η (δT/10) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hη (by linarith)
  have hεη : ε ≤ η := by rw [hεdef]; exact min_le_left _ _
  have h5ε : 5 * ε ≤ δT := by
    rw [hεdef]; have := min_le_right η (δT/10); linarith
  -- Subdivide the path into pieces of diameter at most `ε`.
  obtain ⟨n, hn⟩ := subdivision γ.continuous hεpos
  refine ⟨ε, hεpos, hεη, n+1, (fun i => γ (up n i)), ?_, ?_, ?_, ?_⟩
  · show γ (up n 0) = a
    rw [show up n 0 = (0 : unitInterval) from by
        apply Subtype.ext; simp only [up]; push_cast
        rw [min_eq_left (by positivity : (0:ℝ) ≤ (↑n + 1))]; simp]
    exact Path.source γ
  · show γ (up n (n+1)) = z
    rw [show up n (n+1) = (1 : unitInterval) from by
        apply Subtype.ext; simp only [up]; push_cast
        rw [min_self, div_self (by positivity : ((n:ℝ)+1) ≠ 0)]]
    exact Path.target γ
  · intro i hi
    calc ball (γ (up n i)) (5 * ε) ⊆ thickening (5 * ε) (range γ) := by
          rw [Metric.thickening_eq_biUnion_ball]
          intro y hy
          exact mem_iUnion₂.mpr ⟨γ (up n i), ⟨up n i, rfl⟩, hy⟩
      _ ⊆ thickening δT (range γ) := thickening_mono h5ε _
      _ ⊆ W := hδTsub
  · intro i hi
    have hs := hn i hi
    rw [dist_comm] at hs
    rwa [dist_eq_norm] at hs

end Work.RedProj
