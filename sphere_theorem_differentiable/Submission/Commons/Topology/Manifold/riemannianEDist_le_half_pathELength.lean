import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.Manifold

open scoped Manifold ContDiff Bundle Topology ENNReal

/-- **The half-length bound**: every point of a closed `C¹` curve is at Riemannian distance at most
half the length of the curve from the base point. -/
theorem riemannianEDist_le_half_pathELength
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [instE : ∀ x : M, ENorm (TangentSpace I x)]
    [instEm : ∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    {γ : ℝ → M}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc (0 : ℝ) 1))
    (hloop : γ 1 = γ 0) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Manifold.riemannianEDist I (γ 0) (γ s) ≤ Manifold.pathELength I γ 0 1 / 2 := by
  -- The point `γ s` can be reached from `γ 0` by following the curve forward on `[0, s]` ...
  have h0s : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1 : Manifold.riemannianEDist I (γ 0) (γ s) ≤ Manifold.pathELength I γ 0 s :=
    Manifold.riemannianEDist_le_pathELength (hγ.mono (Set.Icc_subset_Icc le_rfl hs1)) rfl rfl h0s
  -- ... and also by following it backward on `[s, 1]`, using that the curve is closed.
  have h2 : Manifold.riemannianEDist I (γ 0) (γ s) ≤ Manifold.pathELength I γ s 1 := by
    rw [Manifold.riemannianEDist_comm]
    exact Manifold.riemannianEDist_le_pathELength (hγ.mono (Set.Icc_subset_Icc h0s le_rfl)) rfl hloop hs1
  -- Hence twice the distance is at most the total length of the two pieces.
  have hsum : Manifold.pathELength I γ 0 s + Manifold.pathELength I γ s 1
      = Manifold.pathELength I γ 0 1 :=
    Manifold.pathELength_add h0s hs1
  have h3 : 2 * Manifold.riemannianEDist I (γ 0) (γ s) ≤ Manifold.pathELength I γ 0 1 := by
    rw [← hsum, two_mul]
    exact add_le_add h1 h2
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  simpa [mul_comm] using h3

end Commons.Topology.Manifold