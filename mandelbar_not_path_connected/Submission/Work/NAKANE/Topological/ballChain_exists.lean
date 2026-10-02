import Mathlib
import Submission.Work.NAKANE.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.Topological

/-- **Ball-chain refinement of a path in an open set.**

Let `γ : C(I, ℂ)` be a path in the open set `S ⊆ ℂ`, and let `η > 0` be a "margin" such that the
`η`-neighbourhood of `γ '' I` is contained in `S` (the hypothesis `hthick`, in the form
`∀ z, (∃ t, ‖z - γ t‖ < η) → z ∈ S`).  Then there are `m : ℕ`, centres `ctr 0, …, ctr m` *on the
path* and positive radii `rad i ≤ η / 4` such that consecutive balls overlap and all balls lie in
`S`, and `ctr 0 = γ 0`, `ctr m = γ 1`.

This is the combinatorial input of the propagation argument for the joint continuity of the
critical Böttcher coordinate: the chain is a connected spine of small balls from the base point to
the far point, and the smallness plus the margin makes each ball lie in `critDomain c` for all
parameters `c` in a neighbourhood (a uniform gap argument).

Proof sketch: `γ` is uniformly continuous on the compact `I`, so there are `0 = t 0 < … < t m = 1`
with `‖γ (t i) - γ (t (i+1))‖ < η/4`; take `ctr i := γ (t i)` and `rad i := η/4`.  The midpoint
`γ ((t i + t (i+1))/2)` lies in both consecutive balls, giving the overlap; each ball is contained
in `ball (γ (t i)) (η/2) ⊆ S` by `hthick`. -/
theorem ballChain_exists {S : Set ℂ} (hS : IsOpen S) {γ : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hγ : ∀ t, γ t ∈ S) {η : ℝ} (hη : 0 < η) (hthick : ∀ z : ℂ, (∃ t, ‖z - γ t‖ < η) → z ∈ S) :
    ∃ m : ℕ, ∃ ctr : ℕ → ℂ, ∃ rad : ℕ → ℝ,
      (∀ i ≤ m, 0 < rad i) ∧ (∀ i ≤ m, rad i ≤ η / 4) ∧
      (∀ i ≤ m, ∃ t, ctr i = γ t) ∧
      ctr 0 = γ 0 ∧ ctr m = γ 1 ∧
      (∀ i ≤ m, Metric.ball (ctr i) (rad i) ⊆ S) ∧
      (∀ i < m, (Metric.ball (ctr i) (rad i) ∩ Metric.ball (ctr (i + 1)) (rad (i + 1))).Nonempty) := by
  -- `I = [0,1]` is compact, so the path `γ` is uniformly continuous on it.
  haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have huc : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc (η/4) (by positivity)
  -- A mesh `M` of the unit interval so that consecutive nodes are `< δ` apart.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  let M : ℕ := n + 1
  have hMpos : (0:ℝ) < (M:ℝ) := by
    change (0:ℝ) < ((n+1 : ℕ) : ℝ)
    push_cast
    positivity
  have hMne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
  have hstep : 1/(M:ℝ) < δ := by
    change 1/((n+1 : ℕ) : ℝ) < δ
    push_cast
    exact hn
  -- The nodes `s i = min (i/M) 1` of the mesh, as points of `I`.
  let s : ℕ → Set.Icc (0:ℝ) 1 := fun i =>
    ⟨min ((i:ℝ)/(M:ℝ)) 1,
      ⟨le_min (div_nonneg (Nat.cast_nonneg i) (le_of_lt hMpos)) zero_le_one, min_le_right _ _⟩⟩
  let ctr : ℕ → ℂ := fun i => γ (s i)
  let rad : ℕ → ℝ := fun _ => η/4
  have hsval : ∀ i ≤ M, ((s i : Set.Icc (0:ℝ) 1) : ℝ) = (i:ℝ)/(M:ℝ) := by
    intro i hi
    change min ((i:ℝ)/(M:ℝ)) 1 = (i:ℝ)/(M:ℝ)
    rw [min_eq_left_iff, div_le_one hMpos]
    exact_mod_cast hi
  have hs0 : s 0 = (0 : Set.Icc (0:ℝ) 1) := by
    apply Subtype.ext
    rw [hsval 0 (Nat.zero_le M)]
    simp
  have hsM : s M = (1 : Set.Icc (0:ℝ) 1) := by
    apply Subtype.ext
    rw [hsval M le_rfl, div_self hMne]
    simp
  refine ⟨M, ctr, rad, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _
    change (0:ℝ) < η/4
    positivity
  · intro i _
    change η/4 ≤ η/4
    exact le_refl _
  · intro i _
    exact ⟨s i, rfl⟩
  · show γ (s 0) = γ 0
    rw [hs0]
  · show γ (s M) = γ 1
    rw [hsM]
  · -- every ball lies in `S`: it is contained in the `η`-neighbourhood of the path
    intro i _
    intro z hz
    rw [Metric.mem_ball] at hz
    apply hthick z
    refine ⟨s i, ?_⟩
    have hz' : dist z (γ (s i)) < η/4 := hz
    rw [dist_eq_norm] at hz'
    linarith
  · -- consecutive balls overlap: the next centre lies in the previous ball
    intro i hi
    have hle : ((s i : Set.Icc (0:ℝ) 1) : ℝ) ≤ ((s (i+1) : Set.Icc (0:ℝ) 1) : ℝ) := by
      rw [hsval i (le_of_lt hi), hsval (i+1) (by omega)]
      apply div_le_div_of_nonneg_right _ (le_of_lt hMpos)
      push_cast
      linarith
    have hd : dist (s (i+1)) (s i) = 1/(M:ℝ) := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle),
        hsval (i+1) (by omega), hsval i (le_of_lt hi)]
      push_cast
      field_simp
      ring
    refine ⟨γ (s (i+1)), ?_, ?_⟩
    · rw [Metric.mem_ball]
      change dist (γ (s (i+1))) (γ (s i)) < η/4
      apply hδ
      rw [hd]
      exact hstep
    · rw [Metric.mem_ball]
      change dist (γ (s (i+1))) (γ (s (i+1))) < η/4
      rw [dist_self]
      positivity

end Work.NAKANE.Topological
