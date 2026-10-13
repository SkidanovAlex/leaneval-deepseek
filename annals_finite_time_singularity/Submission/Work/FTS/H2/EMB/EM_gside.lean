import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STEasyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.EMB

theorem EM_gside {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hg : Work.Spaces.SmoothNbhd g)
    (hHk : Work.Spaces.HkMem α 4 g) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {i j c d : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hd : d ≤ 3) (hdc : d + 1 + c ≤ 4) :
    Real.sin (2 * θ) * |Work.Spaces.mixed c d (Work.Spaces.pth g) z θ|
        * |Work.Spaces.mixed j i g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ 187 * ((d + 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (Set.mem_Ioi.mp hz).le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hstrp : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hzI hθI
  have hSnn : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_Iθ hθI
  have hsig := Work.FTS.H2.sigma_z_bound g hg d hd c z θ hstrp hθ
  have hBz : Work.FTS.H2.Bz d ≤ 187 := Work.FTS.H2.Bz_le d
  have hHInn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hpairnn : 0 ≤ |Work.Spaces.mixed j i g z θ|
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hSnn _))
  have hterm : ∀ m ∈ Finset.Icc 1 (d + 1),
      |Work.Spaces.mixed c m g z θ|
        * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmc : m + c ≤ 4 := by
      have h2 := (Finset.mem_Icc.mp hm).2; omega
    have h := Work.FTS.H2.gam_pair_le (α := α) (g := g) hα hHk hzI hθI
      (m₁ := m) (j₁ := c) (m₂ := i) (j₂ := j) hm1 hmc hi hij
    rwa [mul_assoc] at h
  have hsum : (∑ m ∈ Finset.Icc 1 (d + 1), |Work.Spaces.mixed c m g z θ|)
        * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      ≤ ((d + 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α 4 g z θ := by
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    rw [Nat.card_Icc, nsmul_eq_mul]
    simp
  calc Real.sin (2 * θ) * |Work.Spaces.mixed c d (Work.Spaces.pth g) z θ|
        * |Work.Spaces.mixed j i g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (Real.sin (2 * θ) * |Work.Spaces.mixed c d (Work.Spaces.pth g) z θ|)
        * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
    _ ≤ (Work.FTS.H2.Bz d * ∑ m ∈ Finset.Icc 1 (d + 1), |Work.Spaces.mixed c m g z θ|)
        * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
        mul_le_mul_of_nonneg_right hsig hpairnn
    _ = Work.FTS.H2.Bz d * ((∑ m ∈ Finset.Icc 1 (d + 1), |Work.Spaces.mixed c m g z θ|)
        * (|Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) := by ring
    _ ≤ Work.FTS.H2.Bz d * (((d + 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α 4 g z θ) :=
        mul_le_mul_of_nonneg_left hsum (Work.FTS.H2.Bz_nonneg d)
    _ ≤ 187 * (((d + 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α 4 g z θ) :=
        mul_le_mul_of_nonneg_right hBz (mul_nonneg (Nat.cast_nonneg _) hHInn)
    _ = 187 * ((d + 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α 4 g z θ := by ring

end Work.FTS.H2.EMB
