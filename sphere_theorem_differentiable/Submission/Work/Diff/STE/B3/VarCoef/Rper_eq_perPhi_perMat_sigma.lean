import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.RperFold.periodization_mul_eq_mul_periodization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Rper = perPhi · perMat` with the **σ**-ball cut-off hypothesis

This is the σ-ball variant of `Work.Diff.STE.B3.Rper_eq_perPhi_perMat`: the cut-off `η` is assumed
to be `1` only on the ball of radius `D.σ l` (rather than on the whole ball of radius `1/4`).  This
is exactly the hypothesis that the proof uses, because the localised weight `ψ l` is supported in
the *open* ball of radius `σ l` (`Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero`).

The argument is unchanged: the localised component factorises pointwise as
`D.R l h a b = (ψ l · √dens l) · (η · mat l h a b)`, the first factor is supported in the closed
ball of radius `1/4` (since `2 σ l ≤ 1/4`), the second in the open centred cube (`hηt`), and a
lattice orbit of a point can meet the closed `1/4`-ball in at most one point which is also the
unique point of the orbit lying in the open cube; hence both periodisation sums collapse to the
same single term and the periodisation of the product is the product of the periodisations
(`Work.Diff.STE.B3.RperFold.periodization_mul_eq_mul_periodization`).
-/

namespace Work.Diff.STE.B3.VarCoef

theorem Rper_eq_perPhi_perMat_sigma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper l h a b
      = fun z => Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z
          * Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h a b z := by
  funext z
  -- The two factors of the localised component `D.R l h a b = (ψ l √dens l) · mat l h a b`,
  -- and `η · mat l h a b`, as `ℂ`-valued functions.
  set f : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun w => ((D.psi l w * Real.sqrt (D.dens l w) : ℝ) : ℂ) with hf_def
  set g : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun w => ((η w * D.mat l h a b w : ℝ) : ℂ) with hg_def
  -- The weight is supported in the ball of radius `1/4`.
  have hf_supp : Function.support f ⊆
      Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (1 / 4) := by
    intro w hw
    rw [Function.mem_support] at hw
    have hψ : D.psi l w ≠ 0 := by
      intro h0
      exact hw (by simp only [hf_def, h0, zero_mul, Complex.ofReal_zero])
    have h1 : ‖w‖ < D.σ l := Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hψ
    have h2 : 2 * D.σ l ≤ 1 / 4 := D.hσ2 l
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith
  -- The cut-off chart matrix is supported in the open centred cube.
  have hg_supp : Function.support g ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro w hw
    rw [Function.mem_support] at hw
    have hη : η w ≠ 0 := by
      intro h0
      exact hw (by simp only [hg_def, h0, zero_mul, Complex.ofReal_zero])
    exact hηt (subset_closure (Function.mem_support.mpr hη))
  -- On the support of the weight, `η = 1`, so the two chart matrices agree there; hence
  -- `D.R = f · g` pointwise.
  have hpt : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      ((D.R l h a b w : ℝ) : ℂ) = f w * g w := by
    intro w
    have hfw : f w = ((D.psi l w * Real.sqrt (D.dens l w) : ℝ) : ℂ) := by
      simp only [hf_def]
    have hgw : g w = ((η w * D.mat l h a b w : ℝ) : ℂ) := by
      simp only [hg_def]
    have hreal : D.R l h a b w
        = D.psi l w * Real.sqrt (D.dens l w) * (η w * D.mat l h a b w) := by
      rw [Work.Diff.STE.B3Data.R]
      by_cases hψ : D.psi l w = 0
      · rw [hψ]; ring
      · have hη : η w = 1 :=
          hη1 w (le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hψ))
        rw [hη]; ring
    rw [hfw, hgw, ← Complex.ofReal_mul, ← hreal]
  have hL : D.Rper l h a b z = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
      f (z + Work.Diff.STE.iVec m) * g (z + Work.Diff.STE.iVec m) := by
    rw [Work.Diff.STE.B3Data.Rper]
    exact tsum_congr (fun m => hpt (z + Work.Diff.STE.iVec m))
  have hP : Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z
      = ∑' m : Fin (Module.finrank ℝ E) → ℤ, f (z + Work.Diff.STE.iVec m) := by
    simp only [Work.Diff.STE.B3.perPhi, hf_def]
  have hM : Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h a b z
      = ∑' m : Fin (Module.finrank ℝ E) → ℤ, g (z + Work.Diff.STE.iVec m) := by
    simp only [Work.Diff.STE.B3.perMat, hg_def]
  rw [hL, hP, hM]
  exact Work.Diff.STE.B3.RperFold.periodization_mul_eq_mul_periodization f g hf_supp hg_supp z

end Work.Diff.STE.B3.VarCoef
