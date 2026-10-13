import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.Pinning

theorem leftLimitOfBoundedDeriv {φ ψ : ℝ → ℝ} {x d M : ℝ} (hd : 0 < d) (hM : 0 ≤ M)
    (hder : ∀ z ∈ Set.Ioo (x - d) x, HasDerivAt φ (ψ z) z)
    (hbdd : ∀ z ∈ Set.Ioo (x - d) x, |ψ z| ≤ M) :
    ∃ G : ℝ, Filter.Tendsto φ (nhdsWithin x (Set.Iio x)) (nhds G) := by
  -- On `Ioo (x - d) x` the function `φ` is `M`-Lipschitz (mean value inequality).
  have hle : ∀ a b, a ∈ Set.Ioo (x - d) x → b ∈ Set.Ioo (x - d) x → a ≤ b →
      |φ a - φ b| ≤ M * |a - b| := by
    intro a b ha hb hab
    have hSz : ∀ z ∈ Set.Icc a b, z ∈ Set.Ioo (x - d) x := fun z hz =>
      ⟨lt_of_lt_of_le ha.1 hz.1, lt_of_le_of_lt hz.2 hb.2⟩
    have hIz : ∀ z ∈ Set.Ico a b, z ∈ Set.Ioo (x - d) x := fun z hz =>
      hSz z ⟨hz.1, le_of_lt hz.2⟩
    have hdiff : DifferentiableOn ℝ φ (Set.Icc a b) := fun z hz =>
      ((hder z (hSz z hz)).differentiableAt).differentiableWithinAt
    have hder' : ∀ z ∈ Set.Ico a b, HasDerivWithinAt φ (ψ z) (Set.Ici z) z := fun z hz =>
      (hder z (hIz z hz)).hasDerivWithinAt
    have hbound : ∀ z ∈ Set.Ico a b, ‖ψ z‖ ≤ M := fun z hz => by
      rw [Real.norm_eq_abs]; exact hbdd z (hIz z hz)
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment hdiff.continuousOn hder' hbound b
        (Set.right_mem_Icc.mpr hab)
    rw [Real.norm_eq_abs] at h
    have h1 : |φ a - φ b| = |φ b - φ a| := abs_sub_comm (φ a) (φ b)
    have h2 : |a - b| = b - a := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    rw [h1, h2]
    exact h
  have hlip : ∀ a b, a ∈ Set.Ioo (x - d) x → b ∈ Set.Ioo (x - d) x →
      |φ a - φ b| ≤ M * |a - b| := by
    intro a b ha hb
    rcases le_total a b with hab | hba
    · exact hle a b ha hb hab
    · have h := hle b a hb ha hba
      rw [abs_sub_comm (φ b) (φ a), abs_sub_comm b a] at h
      exact h
  -- Hence the map filter of `𝓝[<] x` under `φ` is Cauchy; in the complete space `ℝ` a
  -- Cauchy filter converges, which is the limit from the left.
  have hcauchy : Cauchy (Filter.map φ (nhdsWithin x (Set.Iio x))) := by
    rw [Metric.cauchy_iff]
    refine ⟨?_, ?_⟩
    · exact Filter.map_neBot
    · intro ε hε
      have hM1 : (0 : ℝ) < M + 1 := by linarith
      have hδpos : 0 < min d (ε / (M + 1)) := lt_min hd (div_pos hε hM1)
      refine ⟨φ '' Set.Ioo (x - min d (ε / (M + 1))) x, ?_, ?_⟩
      · rw [Filter.mem_map]
        refine Filter.mem_of_superset
          (Ioo_mem_nhdsLT (by linarith [hδpos] : x - min d (ε / (M + 1)) < x)) ?_
        intro z hz
        exact ⟨z, hz, rfl⟩
      · intro u hu v hv
        rcases hu with ⟨a, ha, rfl⟩
        rcases hv with ⟨b, hb, rfl⟩
        have hdδ : min d (ε / (M + 1)) ≤ d := min_le_left _ _
        have hδε : min d (ε / (M + 1)) ≤ ε / (M + 1) := min_le_right _ _
        have ha' : a ∈ Set.Ioo (x - d) x := ⟨lt_of_le_of_lt (by linarith [hdδ]) ha.1, ha.2⟩
        have hb' : b ∈ Set.Ioo (x - d) x := ⟨lt_of_le_of_lt (by linarith [hdδ]) hb.1, hb.2⟩
        have habs : |a - b| < min d (ε / (M + 1)) := by
          rw [abs_sub_lt_iff]
          constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
        have h1 : |φ a - φ b| ≤ M * |a - b| := hlip a b ha' hb'
        have h2 : M * |a - b| < ε := by
          calc M * |a - b| ≤ M * min d (ε / (M + 1)) :=
                mul_le_mul_of_nonneg_left (le_of_lt habs) hM
            _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hδε hM
            _ < ε := by
                rw [← mul_div_assoc, div_lt_iff₀ hM1]
                nlinarith
        rw [Real.dist_eq]
        linarith
  exact (cauchy_map_iff_exists_tendsto (l := nhdsWithin x (Set.Iio x)) (f := φ)).mp hcauchy

end Work.FTS_EllLimOK.Pinning
