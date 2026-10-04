import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.ChartCE
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.D.dens_interior_contDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness and periodicity of the periodised chart weight `perPhiR`

`perPhiR D l` is the periodisation of the chart weight `φ_l = ψ_l · √(dens_l)`,

`perPhiR D l z = ∑' m, ψ_l (z + m) · √(dens_l (z + m))`.

The proof of smoothness does **not** need the chart target to be open (which would require
`[I.Boundaryless]`), only `htarget`: since the closed coordinate ball of radius `2 * σ l` is mapped
by `flatToE` into the chart target, its image — an open set, as `flatToE` is an affine
bijection — is contained in the *interior* of the target.  Hence every flat coordinate of norm
`< 2 * σ l` (in particular every flat coordinate of norm `≤ σ l`) lies in the interior of the
target.

On the other hand the weight `ψ_l` vanishes off the coordinate ball of radius `σ l`
(`Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero`), so its topological support is contained in the
ball of radius `σ l` and hence in the interior of the target; there `ψ_l` and `√dens_l` are both
`C^∞` (`Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero`,
`Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior`, `Work.Diff.STE.D.dens_interior_contDiffAt`,
`Work.Diff.STE.B3.dens_pos_of_mem_target`).  The product is therefore `C^∞` on the open set
"interior of the target" and vanishes identically off the (closed) topological support of `ψ_l`;
gluing these two open pieces gives global smoothness of `ψ_l · √dens_l`, and since that function is
supported in the open unit cube the periodisation is smooth and `1`-periodic
(`Work.Diff.STE.periodization_contDiff_periodic`).
-/

namespace Work.Diff.STE.B3.VarCoef

open scoped Manifold ContDiff Topology BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **Flat coordinates of norm `< 2 σ` lie in the interior of the chart target.**  The image of the
closed coordinate ball of radius `2 σ` under the affine map `flatToE` is contained in the chart
target (`B3Data.htarget`), and the image of the corresponding *open* ball is open (as `flatToE` is
an affine bijection) and contained in it, hence contained in the interior. -/
lemma flatToE_mem_interior_target_of_norm_lt
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ < 2 * D.σ l) :
    Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ interior ((extChartAt I (D.x₀ l)).target) := by
  haveI : IsManifold I (⊤ : ℕ∞) M := IsManifold.of_le (le_refl _)
  -- the closed coordinate ball of radius `2 σ l` is mapped into the target
  have hclosed : Work.Diff.STE.coordBall (I := I) (M := M) (D.x₀ l) (2 * D.σ l) ⊆
      (extChartAt I (D.x₀ l)).target := by
    intro v hv
    have hv' : Work.Diff.STE.flatToE (I := I) (D.x₀ l)
        ((Module.finBasis ℝ E).equivFun v
          - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ l)) (D.x₀ l))) = v := by
      simp only [Work.Diff.STE.flatToE, add_sub_cancel, LinearEquiv.symm_apply_apply]
    rw [← hv']
    refine D.htarget l _ ?_
    exact hv
  -- the point itself lies in the corresponding open ball
  have hmem : Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
      Work.Diff.STE.coordBallOpen (I := I) (M := M) (D.x₀ l) (2 * D.σ l) := by
    have hcoord : (Module.finBasis ℝ E).equivFun (Work.Diff.STE.flatToE (I := I) (D.x₀ l) z)
        = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ l)) (D.x₀ l)) + z := by
      simp only [Work.Diff.STE.flatToE]
      rw [LinearEquiv.apply_symm_apply]
    show ‖(Module.finBasis ℝ E).equivFun (Work.Diff.STE.flatToE (I := I) (D.x₀ l) z)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ l)) (D.x₀ l))‖ < 2 * D.σ l
    rw [hcoord, add_sub_cancel_left]
    exact hz
  have hopen : IsOpen (Work.Diff.STE.coordBallOpen (I := I) (M := M) (D.x₀ l) (2 * D.σ l)) :=
    Work.Diff.STE.isOpen_coordBallOpen (I := I) (D.x₀ l) (2 * D.σ l)
  have hsub : Work.Diff.STE.coordBallOpen (I := I) (M := M) (D.x₀ l) (2 * D.σ l) ⊆
      (extChartAt I (D.x₀ l)).target := by
    intro v hv
    have hv' : ‖(Module.finBasis ℝ E).equivFun v
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ l)) (D.x₀ l))‖ < 2 * D.σ l := hv
    exact hclosed (le_of_lt hv')
  exact (interior_maximal hsub hopen) hmem

theorem perPhiR_smooth_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀)
    (hint : ∀ z : Fin (Module.finrank ℝ E) → ℝ, D.psi l z ≠ 0 →
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target)) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
      ∧ Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l) := by
  classical
  haveI : IsManifold I (⊤ : ℕ∞) M := IsManifold.of_le (le_refl _)
  -- the `ℂ`-valued weight-and-density function whose periodisation is `perPhi`
  set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun z => ((D.psi l z * Real.sqrt (D.dens l z) : ℝ) : ℂ) with hF
  -- the open set on which both factors are smooth
  set W : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    {z | Work.Diff.STE.flatToE (I := I) (D.x₀ l) z
      ∈ interior ((extChartAt I (D.x₀ l)).target)} with hW
  have hWopen : IsOpen W :=
    isOpen_interior.preimage
      (Work.Diff.STE.B3.flatToE_contDiff (I := I) (M := M) (D.x₀ l)).continuous
  -- `ψ l` vanishes off the coordinate ball of radius `σ l`
  have hsupp_ball : Function.support (D.psi l) ⊆
      Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ l) := by
    intro z hz
    rw [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) (M := M) D hz)
  have hFsup_ball : Function.support F ⊆
      Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ l) := by
    intro z hz
    rw [Function.mem_support] at hz
    exact hsupp_ball (Function.mem_support.mpr fun h0 =>
      hz (by rw [hF]; simp only [h0, zero_mul, Complex.ofReal_zero]))
  -- hence the topological support of `F` is inside `W`
  have htsupW : tsupport F ⊆ W := by
    intro z hz
    rw [hW]
    have hzball : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ l) :=
      closure_minimal hFsup_ball Metric.isClosed_closedBall hz
    rw [Metric.mem_closedBall, dist_zero_right] at hzball
    exact flatToE_mem_interior_target_of_norm_lt D l (by have := D.hσ l; linarith)
  -- smoothness on `W`
  have hFW : ContDiffOn ℝ (⊤ : ℕ∞) F W := by
    rw [hWopen.contDiffOn_iff]
    intro z hz
    have hζpt : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => D.ζ l (D.pt l z)) z :=
      contMDiffAt_iff_contDiffAt.mp
        ((D.hζsm l).contMDiffAt.comp z
          (Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) (M := M) D l z hz))
    have hψ : ContDiffAt ℝ (⊤ : ℕ∞) (D.psi l) z := by
      change ContDiffAt ℝ (⊤ : ℕ∞) (fun x => D.χ l x * D.ζ l (D.pt l x)) z
      exact (D.hχsm l).contDiffAt.mul hζpt
    have hdens : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens l) z :=
      Work.Diff.STE.D.dens_interior_contDiffAt (I := I) (M := M) D l z hz
    have hpos : D.dens l z ≠ 0 :=
      (Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) (M := M) D l
        (interior_subset hz)).ne'
    have hsq : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Real.sqrt (D.dens l z)) z :=
      (Real.contDiffAt_sqrt hpos).comp z hdens
    have hlift : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => ((D.psi l z * Real.sqrt (D.dens l z) : ℝ) : ℂ)) z := by
      have := ((Complex.ofRealCLM.contDiff (𝕜 := ℝ)
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt).comp z (hψ.mul hsq)
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using this
    rwa [hF]
  -- `F` vanishes off the topological support of `ψ l`
  have hFc : ContDiffOn ℝ (⊤ : ℕ∞) F (tsupport F)ᶜ := by
    refine ContDiffOn.congr (f := fun _ => (0 : ℂ)) contDiffOn_const ?_
    intro z hz
    show F z = (fun _ => (0 : ℂ)) z
    exact image_eq_zero_of_notMem_tsupport hz
  -- glue the two open pieces
  have hcover : W ∪ (tsupport F)ᶜ = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ W
    · exact Or.inl hz
    · exact Or.inr fun hmem => hz (htsupW hmem)
  have hFsm : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_of_contDiffOn_union_of_isOpen hFW hFc hcover hWopen
      (isClosed_tsupport F).isOpen_compl
  -- `F` is supported in the open unit cube
  have hFsupp : Function.support F ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    rw [Function.mem_support] at hz
    refine Work.Diff.STE.B3Data.psi_supp (I := I) (M := M) D l (Function.mem_support.mpr ?_)
    intro h0
    exact hz (by rw [hF]; simp only [h0, zero_mul, Complex.ofReal_zero])
  -- the periodisation of `F` is smooth and periodic
  obtain ⟨hcdF, hperF, -⟩ := Work.Diff.STE.periodization_contDiff_periodic F hFsm hFsupp
  -- it is `perPhi`
  have hperPhi : Work.Diff.STE.B3.perPhi (I := I) (M := M) D l
      = fun x => ∑' m : Fin (Module.finrank ℝ E) → ℤ, F (x + Work.Diff.STE.iVec m) := by
    funext x
    simp only [Work.Diff.STE.B3.perPhi, hF]
  have hcdPhi : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.perPhi (I := I) (M := M) D l) := by
    rw [hperPhi]
    exact hcdF
  have hperPhi1 : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.perPhi (I := I) (M := M) D l) := by
    rw [hperPhi]
    exact hperF
  -- `perPhiR` is the real part of `perPhi`
  have hRperPhiR : Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l
      = fun z => (Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z).re := by
    funext z
    have h := congrFun
      (Work.Diff.STE.B3.VarCoef.perPhi_eq_ofReal_perPhiR (I := I) (M := M) D l) z
    rw [h, Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun z => (Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z).re) := by
      have := Complex.reCLM.contDiff.comp hcdPhi
      simpa only [Function.comp_def, Complex.reCLM_apply] using this
    rwa [hRperPhiR]
  · have h1 : Work.Diff.STE.Periodic1
        (fun z => (Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z).re) := by
      intro i z
      exact congrArg Complex.re (hperPhi1 i z)
    rwa [hRperPhiR]

end

end Work.Diff.STE.B3.VarCoef
