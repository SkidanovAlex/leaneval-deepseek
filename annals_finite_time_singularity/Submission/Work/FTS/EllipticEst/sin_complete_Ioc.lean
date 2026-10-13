import Mathlib.Analysis.Fourier.AddCircle
import Submission.Work.FTS.EllipticEst.SinCompleteAux
import Submission.Work.FTS.EllipticEst.sinOdd_fourierCoeffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

theorem sin_complete_Ioc {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MeasureTheory.MemLp F 2 (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) L)))
    (h : ∀ n : ℕ, 0 < n → ∫ θ in (0:ℝ)..L, F θ * Real.sin (n * Real.pi * θ / L) = 0) :
    F =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) L)] 0 := by
  have hmem2 : MeasureTheory.MemLp (sinOdd F) 2
      (MeasureTheory.volume.restrict (Set.Ioc (-L) L)) := sinOdd_memLp hL hmem
  have hint := sinInt_eq_zero hL h
  have hcoeff : ∀ n : ℤ, fourierCoeffOn (show (-L) < L by linarith) (sinOdd F) n = 0 := by
    intro n
    rw [sinOdd_fourierCoeffOn hL hmem2 n, hint n, mul_zero]
  have hcoeff0 : ∀ i : ℤ,
      ‖fourierCoeffOn (show (-L) < L by linarith) (sinOdd F) i‖ ^ 2 = 0 :=
    fun i => by rw [hcoeff i, norm_zero]; norm_num
  have hP := hasSum_sq_fourierCoeffOn (show (-L) < L by linarith) hmem2
  have hP0 : HasSum (fun _ : ℤ => (0:ℝ))
      ((L - -L)⁻¹ • ∫ x in (-L)..L, ‖sinOdd F x‖ ^ 2) := by
    simpa only [hcoeff0] using hP
  have hval : ((L - -L)⁻¹ • ∫ x in (-L)..L, ‖sinOdd F x‖ ^ 2) = 0 := by
    simpa using hP0.tsum_eq.symm
  have hInt : ∫ x in (-L)..L, ‖sinOdd F x‖ ^ 2 = 0 := by
    rw [smul_eq_mul] at hval
    exact (mul_eq_zero.mp hval).resolve_left (inv_ne_zero (by linarith : L - -L ≠ 0))
  exact sinOdd_ae_eq_zero hL hmem2 hInt

end Work.FTS.EllipticEst
