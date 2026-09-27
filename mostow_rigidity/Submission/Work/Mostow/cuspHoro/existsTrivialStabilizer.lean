import Mathlib

/-!
# A point with trivial stabilizer for a countable group of isometries of ℝᵐ

Given a countable group `G` acting faithfully by isometries on the Euclidean space
`EuclideanSpace ℝ (Fin m)`, there is a point `x₀` whose stabiliser is trivial.

The proof is the classical Baire category argument: for `g ≠ 1` the fixed point set
`{x | ρ g x = x}` is closed and has empty interior.  Emptiness of the interior follows from
`eq_one_of_fixes_ball`: an isometric self-equivalence of a Euclidean space that fixes an open
ball pointwise is the identity (Mazur–Ulam: an isometry is affine, so we compare its linear part
with the identity on the ball, which spans).  Hence the union of the fixed sets over `g ≠ 1` is
a countable union of nowhere dense sets, and a Baire space is not such a union.

Note: countability is essential — e.g. the full orthogonal group `O(m)` (`m ≥ 2`) acts on
`ℝᵐ` with every point fixed by some nontrivial element, and it is uncountable.
-/

namespace Work.Mostow.cuspHoro

open Set

/-- An isometric self-equivalence of `EuclideanSpace ℝ (Fin m)` that fixes an open ball
pointwise is the identity.

Proof: by the Mazur–Ulam theorem `e` is affine, `e x = L x + e 0` with `L` linear isometric.
If the ball `B(p, r)` is fixed pointwise, then for `y ∈ B(p, r)` we have
`L (y - p) = e y - e p = y - p`, so `L` fixes the open ball of radius `r` around `0`; since the
ball spans (any vector is a nonzero multiple of a small vector), `L = 1`.  Then `e x = x + e 0`
for all `x`, and `e p = p` gives `e 0 = 0`, so `e = 1`. -/
theorem eq_one_of_fixes_ball {m : ℕ}
    (e : EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin m)) (r : ℝ) (hr : 0 < r)
    (h : ∀ y, dist y p < r → e y = y) : e = 1 := by
  set b := EuclideanSpace.basisFun (Fin m) ℝ with hb
  have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.norm_eq_one i
  set t : ℝ := r / 2 with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have htlt : t < r := by rw [ht]; linarith
  have hdist_lt : ∀ i, dist (p + t • b i) p < r := by
    intro i
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hb1 i, mul_one, Real.norm_eq_abs,
      abs_of_pos htpos]
    exact htlt
  have hfix : ∀ i, e (p + t • b i) = p + t • b i := fun i => h _ (hdist_lt i)
  have hp : e p = p := h p (by simpa using hr)
  -- key step: `e` fixes every point
  have key : ∀ x : EuclideanSpace ℝ (Fin m), e x = x := by
    intro x
    -- the two closed ball conditions
    have hlin : ∀ i, inner ℝ (e x) (p + t • b i) - inner ℝ (e x) p
        = inner ℝ x (p + t • b i) - inner ℝ x p := by
      intro i
      have h1 : ‖e x - (p + t • b i)‖ ^ 2 = ‖x - (p + t • b i)‖ ^ 2 := by
        have hd : dist (e x) (p + t • b i) = dist x (p + t • b i) := by
          have hh := e.dist_eq x (p + t • b i)
          simpa only [hfix i] using hh
        rw [← dist_eq_norm, ← dist_eq_norm, hd]
      have h2 : ‖e x - p‖ ^ 2 = ‖x - p‖ ^ 2 := by
        have hd : dist (e x) p = dist x p := by
          have hh := e.dist_eq x p
          simpa only [hp] using hh
        rw [← dist_eq_norm, ← dist_eq_norm, hd]
      rw [norm_sub_sq_real, norm_sub_sq_real] at h1
      rw [norm_sub_sq_real, norm_sub_sq_real] at h2
      linarith
    have hzero : ∀ i, inner ℝ (e x - x) (b i) = 0 := by
      intro i
      have hsub : inner ℝ (e x - x) ((p + t • b i) - p) = 0 := by
        have hh := hlin i
        simp only [inner_sub_left, inner_sub_right] at hh ⊢
        linarith
      rw [add_sub_cancel_left, inner_smul_right] at hsub
      exact (mul_eq_zero.mp hsub).resolve_left (ne_of_gt htpos)
    have hzero' : e x - x = 0 := by
      rw [← OrthonormalBasis.sum_repr' b (e x - x)]
      apply Finset.sum_eq_zero
      intro i _
      rw [inner_eq_zero_symm.mpr (hzero i), zero_smul]
    exact sub_eq_zero.mp hzero'
  exact IsometryEquiv.ext key

/-- For `g ≠ 1`, the fixed point set of `ρ g` has empty interior. -/
private theorem interior_fixed_eq_empty {m : ℕ} {G : Type*} [Group G]
    (ρ : G →* (EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)))
    (hinj : ∀ g : G, ρ g = 1 → g = 1) {g : G} (hg : g ≠ 1) :
    interior {x : EuclideanSpace ℝ (Fin m) | ρ g x = x} = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, hε, hball⟩ := hx
  have heq : ρ g = 1 := eq_one_of_fixes_ball (ρ g) x ε hε fun y hy => hball hy
  exact hg (hinj g heq)

theorem existsTrivialStabilizer {m : ℕ} {G : Type*} [Group G] [Countable G]
    (ρ : G →* (EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)))
    (hinj : ∀ g : G, ρ g = 1 → g = 1) :
    ∃ x₀ : EuclideanSpace ℝ (Fin m), ∀ g : G, g ≠ 1 → ρ g x₀ ≠ x₀ := by
  classical
  by_contra hcon
  push Not at hcon
  -- fixed point sets of nontrivial elements
  have hclosed : ∀ g ∈ {g : G | g ≠ 1},
      IsClosed {x : EuclideanSpace ℝ (Fin m) | ρ g x = x} :=
    fun g _ => isClosed_eq (ρ g).continuous continuous_id
  have hnowhere : ∀ g ∈ {g : G | g ≠ 1},
      IsNowhereDense {x : EuclideanSpace ℝ (Fin m) | ρ g x = x} := by
    intro g hg
    rw [IsClosed.isNowhereDense_iff (hclosed g hg)]
    exact interior_fixed_eq_empty ρ hinj hg
  have hcov : (⋃ g ∈ {g : G | g ≠ 1}, {x : EuclideanSpace ℝ (Fin m) | ρ g x = x}) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨g, hg, hgx⟩ := hcon x
    exact mem_iUnion.mpr ⟨g, mem_iUnion.mpr ⟨hg, hgx⟩⟩
  have hcount : ({g : G | g ≠ 1} : Set G).Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  have hmeagre : IsMeagre (univ : Set (EuclideanSpace ℝ (Fin m))) := by
    rw [← hcov]
    exact isMeagre_biUnion hcount fun g hg => (hnowhere g hg).isMeagre
  exact (not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty) hmeagre

end Work.Mostow.cuspHoro

