import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.RperFold.periodization_mul_eq_mul_periodization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open scoped BigOperators

/-!
# `Rper = perPhi · perMat`: the periodised component factors through its two periodised factors

The localised component of Layer B3 is the pointwise product

`D.R l h a b = (ψ l · √(dens l)) · mat l h a b`,

and `perPhi D l`, `perMat D η l h a b` are the periodisations of its two factors, the weight
`ψ l · √(dens l)` and the cut-off chart matrix `η · mat l h a b`.  This file proves that the
*periodisation* of the product is the product of the periodisations,

`D.Rper l h a b = perPhi D l · perMat D η l h a b`,

under the two hypotheses on the cut-off `η` which make the periodisation well behaved: `η = 1` on
the ball of radius `1/4` around the origin and `tsupport η ⊆ (-1/2,1/2)^n`.

The reason this holds is that at every point `z` of the torus at most **one** lattice translate
`z + m` can contribute, and it is the same one for both factors:

* the weight `ψ l` vanishes off the open centred cube and, more precisely, off the ball of radius
  `σ l ≤ 1/8` (because `ψ l = χ l · ζ l ∘ pt l` and the support of `ζ l` lies in the `σ l`-ball);
  so a translate that contributes to `perPhi` lies in the closed ball of radius `1/4`, which is
  contained coordinatewise in the open centred cube;
* two lattice translates of one point cannot both lie in the open centred cube;
* on the ball of radius `1/4` the cut-off is `1`, so the two factors `mat` and `η · mat` agree on
  the support of the weight.

The lattice content is isolated in the general lemma
`Work.Diff.STE.B3.RperFold.periodization_mul_eq_mul_periodization` (imported below).
-/

theorem Rper_eq_perPhi_perMat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 1 / 4 → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (l : ι₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
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
    have h1 : ‖w‖ < D.σ l := norm_lt_sigma_of_psi_ne_zero D hψ
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
  have hpt : ∀ w : Fin (Module.finrank ℝ E) → ℝ, ((D.R l h a b w : ℝ) : ℂ) = f w * g w := by
    intro w
    have hfw : f w = ((D.psi l w * Real.sqrt (D.dens l w) : ℝ) : ℂ) := by
      simp only [hf_def]
    have hgw : g w = ((η w * D.mat l h a b w : ℝ) : ℂ) := by
      simp only [hg_def]
    have hreal : D.R l h a b w
        = D.psi l w * Real.sqrt (D.dens l w) * (η w * D.mat l h a b w) := by
      rw [B3Data.R]
      by_cases hψ : D.psi l w = 0
      · rw [hψ]; ring
      · have hη : η w = 1 := hη1 w (le_of_lt (by
          have h1 : ‖w‖ < D.σ l := norm_lt_sigma_of_psi_ne_zero D hψ
          have h2 : 2 * D.σ l ≤ 1 / 4 := D.hσ2 l
          linarith))
        rw [hη]; ring
    rw [hfw, hgw, ← Complex.ofReal_mul, ← hreal]
  have hL : D.Rper l h a b z = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
      f (z + Work.Diff.STE.iVec m) * g (z + Work.Diff.STE.iVec m) := by
    rw [B3Data.Rper]
    exact tsum_congr (fun m => hpt (z + Work.Diff.STE.iVec m))
  have hP : Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z
      = ∑' m : Fin (Module.finrank ℝ E) → ℤ, f (z + Work.Diff.STE.iVec m) := by
    simp only [Work.Diff.STE.B3.perPhi, hf_def]
  have hM : Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h a b z
      = ∑' m : Fin (Module.finrank ℝ E) → ℤ, g (z + Work.Diff.STE.iVec m) := by
    simp only [Work.Diff.STE.B3.perMat, hg_def]
  rw [hL, hP, hM]
  exact Work.Diff.STE.B3.RperFold.periodization_mul_eq_mul_periodization f g hf_supp hg_supp z

end Work.Diff.STE.B3
