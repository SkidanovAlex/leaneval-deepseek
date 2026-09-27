import Mathlib
import Submission.Work.KT.Fund.gap_annulus
import Submission.Work.KT.Fund.isUnit_matrix_forall
import Submission.Work.KT.Fund.circleIntegral_inv_sub_eq_zero
import Submission.Work.KT.Fund.SpectralAux
import Submission.Work.KT.Fund.SpectralBasic
import Submission.Work.KT.Fund.spectral_bY
import Submission.Work.KT.Fund.spectral_Yb
import Submission.Work.KT.Fund.TwoRadiusAlt
import Submission.Work.KT.Fund.spectral_unit_d
import Submission.Work.KT.Fund.spectral_unit_z

namespace Work.KT.Fund

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- The "inside" spectral projection, continuously in the parameter: for `b` a matrix over `C(X, ℂ)` (`X` compact Hausdorff) with `z • 1 + b x` invertible for every `z` on the unit circle, there is an idempotent matrix `E` over `C(X, ℂ)` commuting with `b` such that `E b` has all eigenvalues inside the open unit disc (witnessed by `z • 1 + t • (E b) x` being invertible for all `t ∈ [0,1]` and `‖z‖ = 1`), and such that `b` restricted to the complement of `E` is invertible (witnessed by `(1 - E) b + E` being invertible).  Suggested route: `E_k := b^k (1 + b^k)⁻¹` is well defined (no eigenvalue of `b x` on the unit circle is a `k`-th root of `-1`); by compactness of `X` there is a uniform annulus around the unit circle free of eigenvalues, so `E_k` converges uniformly to an idempotent `E`, for which the stated properties follow. -/
theorem spectral_split (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b : Matrix (Fin n) (Fin n) C(X, ℂ))
    (hb : ∀ (x : X) (z : ℂ), ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f x))) :
    ∃ E : Matrix (Fin n) (Fin n) C(X, ℂ),
      E * E = E ∧ E * b = b * E ∧
      (∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
        IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + t • ((E * b).map (fun f => f x)))) ∧
      (∀ x : X, IsUnit (((1 - E) * b + E).map (fun f => f x))) := by
  classical
  letI : NormedRing (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  have hCS : CompleteSpace (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  obtain ⟨ε, hε0, hε1, hgap⟩ := gap_annulus X n b hb
  set ρ : ℝ := 1 - ε / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρlt : ρ < 1 := by rw [hρdef]; linarith
  have hρle : ρ ≤ 1 := le_of_lt hρlt
  -- the invertibility of the resolvent on the annulus `ρ ≤ ‖z‖ ≤ 1`
  have hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - b) := by
    intro z hz1 hz2
    rw [isUnit_matrix_forall n]
    intro x
    have h1 : 1 - ε ≤ ‖(-z)‖ := by rw [norm_neg]; linarith
    have h2 : ‖(-z)‖ ≤ 1 + ε := by rw [norm_neg]; linarith
    have hgapx := hgap x (-z) h1 h2
    have hglob : z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - b
        = -((-z) • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + b) := by
      rw [neg_add, neg_smul, neg_neg, sub_eq_add_neg]
    have hφ : ((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix) (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - b)
        = -(((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
            ((-z) • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + b)) := by
      rw [hglob, map_neg]
    have hφ' : ((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
          ((-z) • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + b)
        = (-z) • (1 : Matrix (Fin n) (Fin n) ℂ) + b.map (fun f => f x) := by
      rw [map_add, map_smul, map_one]
      rfl
    have h1' : IsUnit (((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
        ((-z) • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + b)) := by
      rw [hφ']
      exact hgapx
    change IsUnit (((ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix)
      (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) - b))
    rw [hφ]
    exact h1'.neg
  -- the four algebraic facts
  have hbY := @spectral_bY _ _ _ hCS b ρ hρpos hρlt hunit
  have hYb := @spectral_Yb _ _ _ hCS b ρ hρpos hρlt hunit
  have htwo := @twoRadius_alt _ _ _ hCS b ρ hρpos hρlt hunit
  have hidem : Proj b ρ * Proj b ρ = Proj b ρ :=
    @spectral_idem _ _ _ hCS b ρ hρpos hρle hunit htwo
  have hcomm : b * Proj b ρ = Proj b ρ * b :=
    @spectral_comm _ _ _ hCS b ρ hρpos
      (fun z hz => hunit z (by rw [hz]) (by rw [hz]; exact hρle))
  have huz := @spectral_unit_z _ _ _ hCS b ρ hρpos hρlt hunit hidem hcomm
  have hud := @spectral_unit_d _ _ _ hCS b ρ hρpos hρlt hunit hbY hYb hidem
  refine ⟨Proj b ρ, hidem, hcomm.symm, ?_, ?_⟩
  · intro x t z ht0 ht1 hz
    have hu := huz z t hz ht0 ht1
    have hu' : IsUnit ((z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + t • (Proj b ρ * b)).map
        (fun f => f x)) := (isUnit_matrix_forall n _).mp hu x
    have hone : ((1 : Matrix (Fin n) (Fin n) C(X, ℂ)).map (fun f => f x))
        = (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, h]
    have hm : (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) + t • (Proj b ρ * b)).map
          (fun f => f x)
        = z • (1 : Matrix (Fin n) (Fin n) ℂ) + t • ((Proj b ρ * b).map (fun f => f x)) := by
      rw [Matrix.map_add _ (fun a b => rfl) _ _,
        Matrix.map_smul _ z (fun a => by simp [Algebra.smul_def]) _,
        hone,
        Matrix.map_smul _ t (fun a => by simp [Algebra.smul_def]) _]
    rwa [hm] at hu'
  · intro x
    have hu' : IsUnit (((1 - Proj b ρ) * b + Proj b ρ).map (fun f => f x)) :=
      (isUnit_matrix_forall n _).mp hud x
    exact hu'

end

end Work.KT.Fund
