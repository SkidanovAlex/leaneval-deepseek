import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.B3.mat_eq_inv_zeta_sum
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.goodSet_smooth_noT2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false

/-! ### The pointwise reconstruction identity, in the `[I.Boundaryless]`-free form

`Submission/Work/Diff/STE/B3/mat_eq_inv_zeta_sum.lean` proves this identity as
`mat_eq_inv_zeta_sum_aux`, but that lemma is `private` (hence not importable) and its public
corollary `mat_eq_inv_zeta_sum` carries an unused `[I.Boundaryless]` instance.  The target of this
file is stated without `[I.Boundaryless]`, so the identity is reproduced here verbatim. -/

/-- Elementary algebra: if `(A * B⁻¹) * S = A ^ 2 * M` with `A ≠ 0` and `B ≠ 0`, then
`A⁻¹ * B⁻¹ * S = M`.  This is the cancellation of the weight `ζ_j p` and of the square root of the
volume density `√(dens_j)` in the pointwise reconstruction identity. -/
private lemma inv_mul_inv_mul_eq_of_mul_inv_mul_eq {A B S M : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (h : (A * B⁻¹) * S = A ^ 2 * M) :
    A⁻¹ * B⁻¹ * S = M := by
  have h1 : S = A * B * M := by
    have h2 : (A * B⁻¹) * (A * B * M) = A ^ 2 * M := by
      field_simp
    exact mul_left_cancel₀ (mul_ne_zero hA (inv_ne_zero hB)) (h.trans h2.symm)
  rw [h1]
  calc A⁻¹ * B⁻¹ * (A * B * M) = (A⁻¹ * A) * (B⁻¹ * B) * M := by ring
    _ = M := by rw [inv_mul_cancel₀ hA, inv_mul_cancel₀ hB]; ring

/-- **Pointwise inversion of the reconstruction identity**, without `[I.Boundaryless]`.  At a point
`p` where the weight `ζ_j` of the chart `j` does not vanish, the value of the bilinear form `h` on
two tangent vectors `X`, `Y` is the (weighted) double sum of the localised components `R_j h`
against the coefficients of `X`, `Y` in the frame `e_j`. -/
private lemma mat_eq_inv_zeta_sum_aux'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (p : M) (X Y : TangentSpace I p)
    (hζ : D.ζ j p ≠ 0) :
    h p X Y
      = (D.ζ j p)⁻¹
        * (Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p)))⁻¹
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₀.inner p X (D.e j a p) * g₀.inner p Y (D.e j b p)
              * D.R j h a b (Work.Diff.STE.coord (I := I) (D.x₀ j) p) := by
  obtain ⟨hsrc, hlt⟩ := D.hζsupp j p hζ
  have h2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ j) p‖ ≤ 2 * D.σ j := by
    have hσ := D.hσ j; linarith
  -- the frame `e_j` is `g₀`-orthonormal at `p`
  have hON : Submission.Diff.IsONFrame g₀ p (fun a => D.e j a p) := by
    have h0 := D.heON j (Work.Diff.STE.coord (I := I) (D.x₀ j) p) h2
    rwa [D.symm_flatToE_coord j hsrc] at h0
  -- the density is positive at the flat coordinate of `p`
  have htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) (Work.Diff.STE.coord (I := I) (D.x₀ j) p)
      ∈ (extChartAt I (D.x₀ j)).target := D.htarget j _ h2
  have hdens : 0 < D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p) :=
    dens_pos_of_mem_target D j htgt
  have hB : Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p)) ≠ 0 :=
    (Real.sqrt_pos.mpr hdens).ne'
  -- the cut-off is `1` on the σ-ball, where `ζ_j` lives
  have hchi : D.χ j (Work.Diff.STE.coord (I := I) (D.x₀ j) p) = 1 :=
    D.hχ1 j _ (le_of_lt hlt)
  -- evaluate the reconstruction of the localised component: this is `ζ_j ^ 2 * h`
  have hR := Rstar_R_eq_zeta_sq_free D h j p X Y
  -- and expand the reconstruction in the frame of chart `j`
  have hRa : ((D.Rstar j (fun (a b : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ) => D.R j h a b z) p) X) Y
      = (D.ζ j p * D.χ j (Work.Diff.STE.coord (I := I) (D.x₀ j) p)
          * (Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p)))⁻¹)
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            D.R j h a b (Work.Diff.STE.coord (I := I) (D.x₀ j) p)
              * ((g₀.inner p) X) (D.e j a p) * ((g₀.inner p) Y) (D.e j b p) := by
    simpa only using Rstar_apply D j (fun a b z => D.R j h a b z) p X Y
  have hcomb := hRa.symm.trans hR
  simp only [hchi, mul_one] at hcomb
  -- cancel the weight `ζ_j p` and the square root of the density
  have hkey := inv_mul_inv_mul_eq_of_mul_inv_mul_eq hζ hB hcomb
  rw [← hkey]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-- **The chart matrix `D.mat l h` is `C^∞` on the "good set" of the pair `(l,l)`.**

The hypothesis `hsm` says that the localised components `D.R j h a' b' = ψ_j · √dens_j · D.mat j h a' b'`
are globally `C^∞`; this only immediately gives smoothness of `D.mat l h` where `ψ_l ≠ 0`.  The
claim is that on the larger set `goodSet D l l = {z | flatToE (x₀ l) z ∈ interior target_l}` one
still has smoothness: at any such `z` pick `j` with `ζ_j (pt_l z) ≠ 0` (exists by `hζsq`);
then `work.Diff.STE.B3.mat_eq_inv_zeta_sum` (or its `private` auxiliary form, which does not need
`[I.Boundaryless]`) expresses `D.mat l h a b` near `z` as
`(ζ_j (pt_l ·))⁻¹ (√dens_j (coord_j (pt_l ·)))⁻¹ Σ_{a'b'} ⟪e_l a, e_j a'⟫⟪e_l b, e_j b'⟫ ·
D.R j h a' b' (coord_j (pt_l ·))`,
all of whose factors are `C^∞` near `z` (by `hζsupp` + `hζsm`, `dens_pos_of_mem_target`,
`hsm`, `pt_contMDiffAt_of_mem_interior`, `ONF.pairing`).

This is the last remaining piece of the proof of `Work.Diff.STE.B3.VarCoef.R_Qk_chartExpr`: there
the chain-rule inner function is `Σ_{c',d'} ci · D.mat l h c' d'` with `ci` supported in `goodSet`,
and the chain rule needs that inner function to be globally `C^∞`. -/
theorem contDiffOn_mat_of_goodSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (hsm : ∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R j h a' b')) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ => D.mat l h a b z)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D l l) := by
  intro z hz
  have hz' : Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ interior ((extChartAt I (D.x₀ l)).target) ∧
      D.pt l z ∈ (extChartAt I (D.x₀ l)).source ∧
      (extChartAt I (D.x₀ l)) (D.pt l z) ∈ interior ((extChartAt I (D.x₀ l)).target) := hz
  obtain ⟨hz1, hz2, hz3⟩ := hz'
  -- pick a chart `j` whose weight does not vanish at `pt l z`
  obtain ⟨j, hj⟩ : ∃ j : ι₀, D.ζ j (D.pt l z) ≠ 0 := by
    have h1 := D.hζsq (D.pt l z)
    have h2 : ∑ i : ι₀, (D.ζ i (D.pt l z)) ^ 2 ≠ 0 := by rw [h1]; exact one_ne_zero
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    exact ⟨i, fun h0 => hi (by rw [h0]; ring)⟩
  -- `hζsupp` puts `pt l z` in the source of chart `j`, with small flat coordinate
  have hsrcj : D.pt l z ∈ (extChartAt I (D.x₀ j)).source := (D.hζsupp j (D.pt l z) hj).1
  have hltj : ‖Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l z)‖ < D.σ j :=
    (D.hζsupp j (D.pt l z) hj).2
  have hintj : Work.Diff.STE.flatToE (I := I) (D.x₀ j)
      (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l z))
        ∈ interior ((extChartAt I (D.x₀ j)).target) :=
    Work.Diff.STE.D.flatToE_mem_interior_target (I := I) D j _ (le_of_lt hltj)
  -- hence `z` lies in the good set of the pair `(j,l)`
  have hzjl : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D j l := by
    refine ⟨hz1, hsrcj, ?_⟩
    rw [← Work.Diff.STE.B3.noT2_flatToE_coord (I := I) (M := M) D j hsrcj]
    exact hintj
  -- the smoothness of the ingredients
  have hζc : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ j (D.pt l w)) z :=
    Work.Diff.STE.B3.noT2_contDiffAt_zeta_pt (I := I) (M := M) D j l hzjl
  have hζinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (D.ζ j (D.pt l w))⁻¹) z := hζc.inv hj
  have hT : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w)) z :=
    Work.Diff.STE.B3.noT2_tMapFun_contDiffAt (I := I) (M := M) D j l hzjl
  have hdenj_at : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens j)
      (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l z)) :=
    Work.Diff.STE.D.dens_interior_contDiffAt (I := I) D j _ hintj
  have hdenjpos : 0 < D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l z)) :=
    Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D j (interior_subset hintj)
  have hdenscomp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w))) z :=
    ContDiffAt.comp (x := z)
      (f := fun w => Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w))
      (g := D.dens j) hdenj_at hT
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w)))) z :=
    ContDiffAt.comp (x := z)
      (f := fun w => D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w)))
      (g := Real.sqrt) (Real.contDiffAt_sqrt hdenjpos.ne') hdenscomp
  have hsqrtinv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w))))⁻¹) z :=
    hsqrt.inv (Real.sqrt_pos.mpr hdenjpos).ne'
  have hpair1 : ∀ a' : Fin (Module.finrank ℝ E), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e j a' (D.pt l w))) z :=
    fun a' => Work.Diff.STE.B3.noT2_contDiffAt_pairing_pt (I := I) (M := M) D j l l a a' hzjl
  have hpair2 : ∀ b' : Fin (Module.finrank ℝ E), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e j b' (D.pt l w))) z :=
    fun b' => Work.Diff.STE.B3.noT2_contDiffAt_pairing_pt (I := I) (M := M) D j l l b b' hzjl
  have hR : ∀ a' b' : Fin (Module.finrank ℝ E), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => D.R j h a' b' (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w))) z :=
    fun a' b' => ((hsm j a' b').contDiffAt).comp z hT
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e j a' (D.pt l w)) *
        g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e j b' (D.pt l w)) *
        D.R j h a' b' (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w))) z := by
    apply ContDiffAt.sum
    intro a' _
    apply ContDiffAt.sum
    intro b' _
    exact ((hpair1 a').mul (hpair2 b')).mul (hR a' b')
  -- the smooth model function
  let F : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun w =>
    (D.ζ j (D.pt l w))⁻¹ * (Real.sqrt (D.dens j
        (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w))))⁻¹ *
      (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e j a' (D.pt l w)) *
        g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e j b' (D.pt l w)) *
        D.R j h a' b' (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w)))
  have hFsm : ContDiffAt ℝ (⊤ : ℕ∞) F z := by
    show ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (D.ζ j (D.pt l w))⁻¹
      * (Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w))))⁻¹
      * (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e j a' (D.pt l w)) *
        g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e j b' (D.pt l w)) *
        D.R j h a' b' (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt l w)))) z
    exact (hζinv.mul hsqrtinv).mul hsum
  -- on a neighbourhood of `z` the two functions agree
  have hζev : ∀ᶠ w in nhds z, D.ζ j (D.pt l w) ≠ 0 := hζc.continuousAt.eventually_ne hj
  have hkeyev : (fun w : Fin (Module.finrank ℝ E) → ℝ => D.mat l h a b w) =ᶠ[nhds z] F := by
    filter_upwards [hζev] with w hw
    exact mat_eq_inv_zeta_sum_aux' D h j (D.pt l w) (D.e l a (D.pt l w))
      (D.e l b (D.pt l w)) hw
  exact (hFsm.congr_of_eventuallyEq hkeyev).contDiffWithinAt

end Work.Diff.STE.B3.VarCoef
