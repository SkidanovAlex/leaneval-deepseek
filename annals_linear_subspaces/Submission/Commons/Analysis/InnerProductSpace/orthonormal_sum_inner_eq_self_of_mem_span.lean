import Mathlib.Analysis.InnerProductSpace.Orthonormal

namespace Commons.Analysis.InnerProductSpace

lemma orthonormal_sum_inner_eq_self_of_mem_span {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : ι → E) (hu : Orthonormal ℝ u)
    {v : E} (hv : v ∈ Submodule.span ℝ (Set.range u)) :
    (Finset.univ.sum (fun i : ι => inner ℝ (u i) v • u i)) = v := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := u) (x := v)).mp hv
  calc
    (Finset.univ.sum (fun i : ι => inner ℝ (u i) v • u i))
        = Finset.univ.sum (fun i : ι => c i • u i) := by
          rw [← hc]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hu.inner_right_fintype c i]
    _ = v := hc

end Commons.Analysis.InnerProductSpace