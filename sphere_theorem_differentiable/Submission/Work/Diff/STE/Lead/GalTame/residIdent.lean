import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.residGn.BoxDefs
import Submission.Work.Diff.STE.B3.transport_tame_assemble
import Submission.Work.Diff.STE.B3.Rres_eq_residualLow
import Submission.Work.Diff.STE.B3.transport_tame_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead.GalTame

theorem residIdent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) (cl ch : ℝ) (hcl : 0 < cl) (hch : cl < ch)
    (hwin : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
      cl ≤ (Matrix.of (fun i k : Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ∧
      (Matrix.of (fun i k : Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ≤ ch)
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ 2 * D.σ j)
    (af bf : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.B3.tmPsi (I := I) (M := M) D j cl ch hcl hch z
        (fun c d => D.mat j h c d z) (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) af bf
      = Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z af bf := by
  classical
  have hσ : 0 < D.σ j := D.hσ j
  have hσ3 : 3 * D.σ j ≤ 1 / 2 := by linarith [D.hσ2 j]
  -- **Step 1.** On the `2σ j`-ball the clamped inverse `tmGKi` of the nominal coordinate chart
  -- matrix is the honest inverse `tmGfi` of the chart matrix of `h`: the two matrices agree
  -- (`tmGK_eq_Gf`) and the determinant lies in the clamping window `[cl, ch]` by `hwin`, so
  -- `tmInv` is the honest inverse there.
  have hmem : ∀ (w : Fin (Module.finrank ℝ E) → ℝ), ‖w‖ ≤ 2 * D.σ j →
      ∀ c d : Fin (Module.finrank ℝ E),
      Work.Diff.STE.B3.tmGKi (I := I) (M := M) D j cl ch hcl hch w
        (fun p q => D.mat j h p q w) c d
      = Work.Diff.STE.B3.tmGfi (I := I) (M := M) D h j w c d := by
    intro w hw c d
    have h1 := Work.Diff.STE.B3.tmGK_eq_Gf (I := I) (M := M) D h j w
      (D.htarget j w hw) (Work.Diff.STE.B3.det_Ff_ne_zero (I := I) (M := M) D j hw)
    have h2 : Work.Diff.STE.B3.tmInv cl ch hcl hch
          (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j w))
        = (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j w))⁻¹ := by
      rw [Work.Diff.STE.B3.tmInv,
        Work.Diff.STE.B3.tms_beta_one cl ch
          (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j w)).det hcl hch
          (hwin w hw).1 (hwin w hw).2]
      simp only [one_smul, sub_self, zero_smul, add_zero]
    unfold Work.Diff.STE.B3.tmGKi Work.Diff.STE.B3.tmGfi
    rw [show (fun p q : Fin (Module.finrank ℝ E) => D.mat j h p q w)
        = Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w from rfl, h1, h2]
  -- **Step 2.** The cut-off `φ`: `C^∞`, `1` on the closed `2σ j`-ball, supported in the open
  -- `3σ j`-ball (so `3σ j ≤ 1/2` makes the periodisation in `tmA` a single translate there).
  obtain ⟨φ, hφsm, hφ1, hφsupp⟩ :
      ∃ φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
        (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j → φ z = 1) ∧
        Function.support φ ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (3 * D.σ j) := by
    let ρ : ContDiffBump (0 : Fin (Module.finrank ℝ E) → ℝ) :=
      ⟨2 * D.σ j, 3 * D.σ j, by linarith [hσ], by linarith [hσ]⟩
    have hρrOut : ρ.rOut = 3 * D.σ j := rfl
    have hρrIn : ρ.rIn = 2 * D.σ j := rfl
    refine ⟨ρ, ρ.contDiff, ?_, ?_⟩
    · intro w hw
      exact ρ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right, hρrIn]; exact hw)
    · intro w hw
      have h2 : w ∈ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) ρ.rOut := by
        rw [← ρ.support_eq]; exact hw
      rw [Metric.mem_ball, dist_zero_right] at h2
      rw [Metric.mem_ball, dist_zero_right]
      exact h2
  -- **Step 3.** The transport identity with the coefficient `tmA φ cl (tmGfi D h j)`.
  have hid := Work.Diff.STE.B3.tm_identity_clause (I := I) (M := M) D hLC h hsym hpos hsmooth
    j af bf φ hφsm hφ1 (3 * D.σ j) hσ3 hφsupp (by linarith [hσ]) cl cl ch hcl hch hmem z hz
  -- **Step 4.** The residual in lower-order form.
  have hres := Work.Diff.STE.B3.Rres_eq_residualLow (I := I) (M := M) D hLC h hsym hpos hsmooth
    j hz af bf
  -- **Step 5.** On the ball, `tmA φ cl γ = γ` for `γ = tmGfi`.
  have hcoe : ∀ p q : Fin (Module.finrank ℝ E),
      Work.Diff.STE.B3.tmA φ cl (Work.Diff.STE.B3.tmGfi (I := I) (M := M) D h j) z p q
        = Work.Diff.STE.B3.tmGfi (I := I) (M := M) D h j z p q := by
    intro p q
    exact Work.Diff.STE.B3.tmA_eq_of_one (n := Module.finrank ℝ E) (R := 3 * D.σ j)
      (ρ := 2 * D.σ j) φ (Work.Diff.STE.B3.tmGfi (I := I) (M := M) D h j) hσ3
      (by linarith [hσ]) hφsupp hφ1 hz p q
  have hsumA : (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        Work.Diff.STE.B3.tmA φ cl (Work.Diff.STE.B3.tmGfi (I := I) (M := M) D h j) z p q
          * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z)
      = ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.STE.B3.tmGfi (I := I) (M := M) D h j z p q
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hcoe p q]
  have hGf_inv : ∀ p q : Fin (Module.finrank ℝ E),
      ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
        = Work.Diff.STE.B3.tmGfi (I := I) (M := M) D h j z p q := by
    intro p q
    simp only [Work.Diff.STE.B3.tmGfi]
  have hsumB : (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
          * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z)
      = ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.STE.B3.tmGfi (I := I) (M := M) D h j z p q
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hGf_inv p q]
  have hphi : φ z = 1 := hφ1 z hz
  -- **Step 6.** `Rres` with the coefficient `(Gf)⁻¹` equals `tmPsi` on the ball.
  have hkey : Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
      (fun z p q => ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)
      z af bf
      = Work.Diff.STE.B3.tmPsi (I := I) (M := M) D j cl ch hcl hch z
          (fun c d => D.mat j h c d z)
          (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) af bf := by
    simp only [Work.Diff.STE.B3.Rres]
    rw [hid af bf, hsumA, hsumB, hphi, one_mul]
    ring
  rw [← hkey, hres]

end Work.Diff.STE.Lead.GalTame
