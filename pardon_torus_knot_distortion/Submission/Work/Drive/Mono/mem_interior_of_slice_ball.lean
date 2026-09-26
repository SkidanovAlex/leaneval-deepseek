import Mathlib

/-!
# A point of a convex set whose slice-collar lies in the set is interior

Let `K ⊆ ℝ³` be convex, `f` a nonzero continuous linear functional, `t ∈ ℝ`, and
`u ∈ interior K` with `f u = t`.  If `z` lies on the same level set `f = t` and some
relative (slice) ball around `z` inside the plane `{f = t}` is contained in `K`, then
`z ∈ interior K`.

The proof is the supporting-hyperplane argument.  If `z` were not interior, the point
`z` and the open convex set `interior K` could be separated by a nonzero functional `φ`
with `φ a < φ z` for all `a ∈ interior K`; since `interior K` is dense in the convex set
`K`, this gives `φ ≤ φ z` on `K`.  The slice hypothesis then forces `φ` to vanish on the
2-plane `ker f ⊆ ℝ³` (both `z + s` and `z - s` lie in `K` for small `s ∈ ker f`), so
`φ = (φ g) • f` for any `g` with `f g = 1`.  Evaluating at `u` and at `z` gives
`φ u = φ z`, contradicting `φ u < φ z`.
-/

open Set

namespace Work.Drive.Mono

theorem mem_interior_of_slice_ball {K : Set (EuclideanSpace ℝ (Fin 3))} (hKc : Convex ℝ K)
    {f : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ} (hf : f ≠ 0) {t : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} (huf : f u = t) (hu : u ∈ interior K)
    {z : EuclideanSpace ℝ (Fin 3)} (hzf : f z = t)
    (hball : ∃ ε : ℝ, 0 < ε ∧ ∀ v : EuclideanSpace ℝ (Fin 3), f v = t → ‖v - z‖ < ε → v ∈ K) :
    z ∈ interior K := by
  -- assume for a contradiction that `z` is not interior
  by_contra hz
  -- separate `z` from the open convex set `interior K`
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hKc.interior isOpen_interior hz
  -- `φ ≤ φ z` on the whole of `K`
  have hle : ∀ y ∈ K, φ y ≤ φ z := by
    intro y hy
    have hsub : interior K ⊆ {x | φ x ≤ φ z} := fun a ha => (hφ a ha).le
    have hclosed : IsClosed {x | φ x ≤ φ z} := isClosed_le φ.continuous continuous_const
    have hcl_sub : closure (interior K) ⊆ {x | φ x ≤ φ z} := closure_minimal hsub hclosed
    rw [hKc.closure_interior_eq_closure_of_nonempty_interior ⟨u, hu⟩] at hcl_sub
    exact hcl_sub (subset_closure hy)
  obtain ⟨ε, hε, hball'⟩ := hball
  -- on `ker f` the value of `φ` is at most `0`
  have hkey : ∀ s : EuclideanSpace ℝ (Fin 3), f s = 0 → φ s ≤ 0 := by
    intro s hs
    rcases eq_or_ne s 0 with rfl | hsne
    · simp
    · have hsnorm : 0 < ‖s‖ := norm_pos_iff.mpr hsne
      set μ : ℝ := ε / (2 * ‖s‖) with hμ
      have hμpos : 0 < μ := by
        rw [hμ]; exact div_pos hε (mul_pos (by norm_num) hsnorm)
      have hnorm : ‖μ • s‖ < ε := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
        have hcalc : μ * ‖s‖ = ε / 2 := by rw [hμ]; field_simp
        rw [hcalc]; linarith
      have hmem : z + μ • s ∈ K := by
        refine hball' (z + μ • s) ?_ ?_
        · simp only [map_add, map_smul, smul_eq_mul, hzf, hs, mul_zero, add_zero]
        · rw [add_sub_cancel_left]; exact hnorm
      have h := hle (z + μ • s) hmem
      simp only [map_add, map_smul, smul_eq_mul] at h
      have h2 : μ * φ s ≤ 0 := by linarith
      exact nonpos_of_mul_nonpos_right h2 hμpos
  -- hence `φ` vanishes identically on `ker f`
  have hker : ∀ s : EuclideanSpace ℝ (Fin 3), f s = 0 → φ s = 0 := by
    intro s hs
    have h1 := hkey s hs
    have h2 := hkey (-s) (by simp [hs])
    simp only [map_neg, neg_nonpos] at h2
    linarith
  -- `f` is nonzero, so choose `g` with `f g = 1` and conclude `φ = (φ g) • f`
  have hx : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext h)
  obtain ⟨x₀, hx₀⟩ := hx
  set g : EuclideanSpace ℝ (Fin 3) := (f x₀)⁻¹ • x₀ with hg
  have hfg : f g = 1 := by
    simp only [hg, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hx₀
  have hφeq : φ = (φ g) • f := by
    ext x
    have h0 : f (x - (f x) • g) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hfg, mul_one, sub_self]
    have h := hker (x - (f x) • g) h0
    simp only [map_sub, map_smul, smul_eq_mul] at h
    simp only [smul_apply, smul_eq_mul]
    linarith
  -- but then `φ u = φ z`, contradicting `φ u < φ z`
  have huz : φ u = φ z := by
    rw [hφeq]
    simp only [smul_apply, smul_eq_mul, huf, hzf]
  have := hφ u hu
  linarith

end Work.Drive.Mono
