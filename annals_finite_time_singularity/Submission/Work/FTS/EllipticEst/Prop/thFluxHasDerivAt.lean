import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology

/-- `∂_z` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pz_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hne : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by simp
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn hne).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `∂_θ` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pth_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hne : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by simp
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn hne).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The angular slice of `∂_z G` is differentiable, with derivative the corresponding
mixed partial `∂_θ ∂_z G`. -/
theorem hasDerivAt_pz_slice {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz G)) (z, θ)) :
    HasDerivAt (fun θ' => Work.Spaces.pz G z θ') (Work.Spaces.pth (Work.Spaces.pz G) z θ) θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  have hh := h.hasFDerivAt.comp_hasDerivAt θ hcurve
  rw [← Work.Spaces.pth_eq_fderiv h] at hh
  simpa only [Function.comp_def, Function.uncurry] using hh

theorem thFluxHasDerivAt (q : ℝ) (v : ℝ → ℝ → ℝ)
    (hv : ContDiffOn ℝ 3 (Function.uncurry v) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' : ℝ => (Work.Spaces.Dz v z θ') * (Work.Spaces.Dz (Work.Spaces.pth v) z θ')
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ')) ^ q) θ
      = (Work.Spaces.Dz (Work.Spaces.pth v) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ q
        + (Work.Spaces.Dz v z θ) * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth v)) z θ)
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ q
        + (Work.Spaces.Dz v z θ) * (Work.Spaces.Dz (Work.Spaces.pth v) z θ)
            * (Work.Spaces.w z) ^ 2 * deriv (fun t : ℝ => (Real.sin (2 * t)) ^ q) θ := by
  set U : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) with hUdef
  have hU : IsOpen U := by rw [hUdef]; exact isOpen_Ioi.prod isOpen_Ioo
  have hmem : (z, θ) ∈ U := by rw [hUdef]; exact ⟨hz, hθ⟩
  -- finite-order smoothness of the partial derivatives
  have hpz2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz v)) U :=
    contDiffOn_uncurry_pz_fin hU (n := 2) hv
  have hpth2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth v)) U :=
    contDiffOn_uncurry_pth_fin hU (n := 2) hv
  have hpzpth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth v))) U :=
    contDiffOn_uncurry_pz_fin hU (n := 1) hpth2
  -- Clairaut: `∂_z ∂_θ = ∂_θ ∂_z` for `v` and for `∂_θ v`
  have hvdiff2 : ContDiffAt ℝ 2 (Function.uncurry v) (z, θ) :=
    (hv.contDiffAt (hU.mem_nhds hmem)).of_le (by norm_num)
  have hpthdiff2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth v)) (z, θ) :=
    hpth2.contDiffAt (hU.mem_nhds hmem)
  have hcl1 : Work.Spaces.pz (Work.Spaces.pth v) z θ
      = Work.Spaces.pth (Work.Spaces.pz v) z θ := Work.Spaces.pz_pth_comm hvdiff2
  have hcl2 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth v)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth v)) z θ :=
    Work.Spaces.pz_pth_comm hpthdiff2
  -- the two derivative factors
  have hA : HasDerivAt (fun θ' : ℝ => Work.Spaces.Dz v z θ')
      (Work.Spaces.Dz (Work.Spaces.pth v) z θ) θ := by
    have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz v)) (z, θ) :=
      (hpz2.contDiffAt (hU.mem_nhds hmem)).differentiableAt (by norm_num)
    have h := (hasDerivAt_pz_slice hd).const_mul z
    rw [← hcl1] at h
    exact h
  have hB : HasDerivAt (fun θ' : ℝ => Work.Spaces.Dz (Work.Spaces.pth v) z θ')
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth v)) z θ) θ := by
    have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth v))) (z, θ) :=
      (hpzpth1.contDiffAt (hU.mem_nhds hmem)).differentiableAt (by norm_num)
    have h := (hasDerivAt_pz_slice hd).const_mul z
    rw [← hcl2] at h
    exact h
  -- the angular factor `sin(2θ)^q`
  have hpos : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hs2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ hs2
  have hrpow : HasDerivAt (fun x : ℝ => x ^ q) (q * (Real.sin (2 * θ)) ^ (q - 1))
      (Real.sin (2 * θ)) :=
    Real.hasDerivAt_rpow_const (Or.inl hpos)
  have hS : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ q)
      (deriv (fun θ' : ℝ => (Real.sin (2 * θ')) ^ q) θ) θ := by
    simpa only [Function.comp_def] using (hrpow.comp θ hsin).differentiableAt.hasDerivAt
  -- the product rule
  have hchain := ((hA.mul hB).mul (hasDerivAt_const θ ((Work.Spaces.w z) ^ 2))).mul hS
  have hfun : (fun θ' : ℝ => (Work.Spaces.Dz v z θ')
        * (Work.Spaces.Dz (Work.Spaces.pth v) z θ')
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ')) ^ q)
      = ((fun θ' : ℝ => Work.Spaces.Dz v z θ')
          * (fun θ' : ℝ => Work.Spaces.Dz (Work.Spaces.pth v) z θ')
          * (fun _ : ℝ => (Work.Spaces.w z) ^ 2))
          * (fun θ' : ℝ => (Real.sin (2 * θ')) ^ q) := by
    funext y
    simp only [Pi.mul_apply]
  rw [hfun, hchain.deriv]
  simp only [Pi.mul_apply]
  ring

end Work.FTS.EllipticEst.Prop
