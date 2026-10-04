import Mathlib
import Submission.Work.Diff.EXT.FlatPre

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter
open scoped Topology

namespace Work.Diff.EXT

/-- If `γ` is `C^1` on an open set `u` and its iterated derivatives all vanish at the points of the
hyperplane `{t = T}` lying in `u`, then its Heaviside cut `stepFun T γ` is continuous on `u`. -/
theorem continuousOn_stepFun
    {n : ℕ} {T : ℝ} {u : Set (ℝ × (Fin n → ℝ))}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ × (Fin n → ℝ) → F}
    (hu : IsOpen u) (hγ : ContDiffOn ℝ 1 γ u)
    (hflat : ∀ p ∈ u, p.1 = T → ∀ j : ℕ, iteratedFDeriv ℝ j γ p = 0) :
    ContinuousOn (stepFun T γ) u := by
  -- The openness of `u` is not needed for this statement; nothing below uses it.
  have _ := hu
  -- Split the ambient space into the closed half space `A = {t ≤ T}` and the open half space
  -- `C = {T < t}`.  On `u ∩ A` the cut vanishes identically, on `u ∩ C` it agrees with `γ`, and
  -- `u = (u ∩ A) ∪ (u ∩ C)`, so `𝓝[u] x` is the supremum of the two restrictions.
  set A : Set (ℝ × (Fin n → ℝ)) := {q | q.1 ≤ T} with hA
  set C : Set (ℝ × (Fin n → ℝ)) := {q | T < q.1} with hC
  have hmemA : ∀ q, q ∈ A ↔ q.1 ≤ T := fun q => by simp [hA]
  have hmemC : ∀ q, q ∈ C ↔ T < q.1 := fun q => by simp [hC]
  have hAclosed : IsClosed A := by
    rw [hA]; exact isClosed_le continuous_fst continuous_const
  have hCcl : IsClosed {q : ℝ × (Fin n → ℝ) | T ≤ q.1} :=
    isClosed_le continuous_const continuous_fst
  have hCsub : C ⊆ {q : ℝ × (Fin n → ℝ) | T ≤ q.1} :=
    fun q hq => le_of_lt ((hmemC q).1 hq)
  have hAcupC : A ∪ C = Set.univ := by
    ext q
    exact iff_true_intro ((le_or_gt q.1 T).elim (fun h => Or.inl ((hmemA q).2 h))
      (fun h => Or.inr ((hmemC q).2 h)))
  have hu_union : u = (u ∩ A) ∪ (u ∩ C) := by
    rw [← Set.inter_union_distrib_left, hAcupC, Set.inter_univ]
  intro x hx
  change Tendsto (stepFun T γ) (𝓝[u] x) (𝓝 (stepFun T γ x))
  rw [hu_union, nhdsWithin_union, tendsto_sup]
  constructor
  · -- `f` is eventually `0` along `u ∩ A`; either `x ∈ A`, and then `f x = 0`, or `x ∉ A`
    -- and then `x` is not even in the closure of `u ∩ A`, so any limit works.
    by_cases hxA : x ∈ A
    · have hfx : stepFun T γ x = 0 := by
        simp only [stepFun_apply]; exact ite_eq_left ((hmemA x).1 hxA)
      rw [hfx]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      refine eventually_of_mem self_mem_nhdsWithin ?_
      intro y hy
      exact (ite_eq_left ((hmemA y).1 hy.2)).symm
    · refine continuousWithinAt_of_notMem_closure ?_
      intro hc
      exact hxA (closure_minimal Set.inter_subset_right hAclosed hc)
  · -- On `u ∩ C` the cut agrees with `γ`.  Off the hyperplane `{t = T}` the limit is then
    -- `𝓝 (f x) = 𝓝 (γ x)`; on the hyperplane we use flatness (`j = 0`) to see `γ x = 0 = f x`;
    -- for `x.1 < T` the point `x` is not in the closure of `u ∩ C` and any limit works.
    by_cases hxt : T < x.1
    · have hfx : stepFun T γ x = γ x := by
        simp only [stepFun_apply]; exact ite_eq_right (not_le.mpr hxt)
      refine ContinuousWithinAt.congr ((hγ.continuousOn x hx).mono Set.inter_subset_left) ?_ hfx
      intro y hy
      simp only [stepFun_apply]; exact ite_eq_right (not_le.mpr hy.2)
    · by_cases hxT : x.1 = T
      · have hfx : stepFun T γ x = 0 := by
          simp only [stepFun_apply]; exact ite_eq_left (le_of_eq hxT)
        have hγx : γ x = 0 := by
          have h0 := hflat x hx hxT 0
          have h1 := iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := γ) (x := x) (fun i : Fin 0 => i.elim0)
          rw [h0] at h1
          simpa using h1.symm
        refine ContinuousWithinAt.congr ((hγ.continuousOn x hx).mono Set.inter_subset_left) ?_ ?_
        · intro y hy
          simp only [stepFun_apply]; exact ite_eq_right (not_le.mpr hy.2)
        · rw [hfx, hγx]
      · have hxlt : x.1 < T := lt_of_le_of_ne (not_lt.mp hxt) hxT
        refine continuousWithinAt_of_notMem_closure ?_
        intro hc
        have hcl := closure_minimal (Set.Subset.trans Set.inter_subset_right hCsub) hCcl hc
        have hcl' : T ≤ x.1 := hcl
        linarith

end Work.Diff.EXT
