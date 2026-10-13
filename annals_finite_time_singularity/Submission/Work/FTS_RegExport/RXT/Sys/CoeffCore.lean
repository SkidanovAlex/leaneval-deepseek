import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.C2Final
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS.StrongEps.mixed_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.CoeffCore` — local helpers for `coeff_jets`

* `mixed` of a constant function, and scalar homogeneity of `mixed`;
* the derivative of the angular coefficient `c2m`;
* the `C²`-smoothness on the open quadrant of every *piece* of the three transport
  coefficients (the same assembly as `RXT.coeff_C2_assembly`, but exposing the pieces);
* the `Θ`-split `Uop α Φ = Uop α Φ̃ + Uop α (Θ α F_τ)` on the open quadrant.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR ΦR μR)
open Work.FTS_RegExport.RXT (v2_PhiT v2_SlotR v2_SlotV v2_SlotU)
open Work.FTS.Regularity (pExp)
open Work.Construction (L12 FK Ftau Theta Uop Vop Rop c2m Fstar)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## §1 `mixed` of constants and constant multiples -/

/-- `D_z`-iterates of a constant function. -/
theorem DzIter_const_fun (c : ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun _ _ : ℝ => c) = fun _ _ => if j = 0 then c else 0 := by
  induction j with
  | zero => simp
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        funext z θ
        simp [Work.Spaces.Dz, Work.Spaces.pz]
      · have hn0 : n ≠ 0 := by omega
        have hz : (fun _ _ : ℝ => (if n = 0 then c else 0)) = fun _ _ => (0 : ℝ) := by
          funext z θ; simp [hn0]
        rw [hz]
        funext z θ
        simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- `D_θ`-iterates of a constant function. -/
theorem DthIter_const_fun (c : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => c) = fun _ _ => if i = 0 then c else 0 := by
  induction i with
  | zero => simp
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]
      · have hn0 : n ≠ 0 := by omega
        have hz : (fun _ _ : ℝ => (if n = 0 then c else 0)) = fun _ _ => (0 : ℝ) := by
          funext z θ; simp [hn0]
        rw [hz]
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- The `mixed`-jets of a constant function are bounded by the constant. -/
theorem abs_mixed_const_le (c : ℝ) (j i : ℕ) (z θ : ℝ) :
    |Work.Spaces.mixed j i (fun _ _ : ℝ => c) z θ| ≤ |c| := by
  rw [Work.Spaces.mixed, DthIter_const_fun c i,
    DzIter_const_fun (if i = 0 then c else 0) j]
  by_cases hj : j = 0 <;> by_cases hi : i = 0 <;> simp [hj, hi]

/-- Scalar homogeneity of the mixed operator. -/
theorem coeff_mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  funext z θ
  simp only [Work.Spaces.mixed, Work.FTS.StrongEps.DthIter_const_mul c f i,
    Work.FTS.StrongEps.DzIter_const_mul c _ j]

/-- A constant multiple of a `mixed`-jet is bounded by `|c|` times a bound of the jet. -/
theorem abs_mixed_const_mul_le' {c M : ℝ} {f : ℝ → ℝ → ℝ} {j i : ℕ} {z θ : ℝ}
    (h : |Work.Spaces.mixed j i f z θ| ≤ M) :
    |Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ| ≤ |c| * M := by
  rw [coeff_mixed_const_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

/-- The nonnegative-`c` form of `abs_mixed_const_mul_le'`. -/
theorem abs_mixed_const_mul_le {c M : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ → ℝ} {j i : ℕ} {z θ : ℝ}
    (h : |Work.Spaces.mixed j i f z θ| ≤ M) :
    |Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ| ≤ c * M := by
  have := abs_mixed_const_mul_le' (c := c) h
  rwa [abs_of_nonneg hc] at this

/-- Additivity of the mixed operator in the *lambda* form (for `rw`). -/
theorem mixed_add_lam {f h : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 (Function.uncurry f) Q0)
    (hh : ContDiffOn ℝ 2 (Function.uncurry h) Q0)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hzθ : (z, θ) ∈ Q0) :
    Work.Spaces.mixed j i (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i h z θ :=
  mixed_add_pt hf hh hji hzθ

/-- A Lipschitz-type pointwise bound on a set gives continuity there. -/
theorem continuousOn_of_abs_sub_le {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) {s : Set ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ C * |x - y|) : ContinuousOn f s := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨ε / (C + 1), by positivity, ?_⟩
  intro y hy hxy
  have h2 : |y - x| < ε / (C + 1) := by
    have hxy' : dist y x < ε / (C + 1) := hxy
    rw [Real.dist_eq] at hxy'
    simpa [abs_sub_comm] using hxy'
  have h1 : |f y - f x| ≤ C * |y - x| := h y hy x hx
  have h3 : C * |y - x| ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (le_of_lt h2) hC
  have h4 : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ hC1]
    nlinarith
  have hgoal : dist (f y) (f x) < ε := by
    rw [Real.dist_eq]
    linarith
  simpa using hgoal

/-- The derivative of the angular coefficient `c2m` is bounded by `4`. -/
theorem abs_deriv_c2m_le (θ : ℝ) : |deriv c2m θ| ≤ 4 := by
  have hderiv1 : deriv (fun θ : ℝ => Real.cos (2 * θ)) θ = -2 * Real.sin (2 * θ) := by
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) θ).const_mul (2 : ℝ)
    have hcomp : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-(Real.sin (2 * θ) * 2)) θ := by
      simpa [Function.comp_def] using (Real.hasDerivAt_cos (2 * θ)).comp θ hlin
    rw [hcomp.deriv]
    ring
  have hderiv2 : deriv (fun θ : ℝ => Real.sin θ ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
    have hcomp : HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2)
        (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
    rw [hcomp.deriv]
    norm_num
  have h1 : DifferentiableAt ℝ (fun θ : ℝ => Real.cos (2 * θ)) θ := by fun_prop
  have h2 : DifferentiableAt ℝ (fun θ : ℝ => Real.sin θ ^ 2) θ := by fun_prop
  have h4 : deriv c2m θ = -3 * Real.sin (2 * θ) := by
    rw [show (c2m : ℝ → ℝ) = ((fun θ : ℝ => Real.cos (2 * θ))
      - (fun θ : ℝ => Real.sin θ ^ 2)) from by funext θ'; rfl]
    rw [deriv_sub h1 h2, hderiv1, hderiv2, Real.sin_two_mul]
    ring
  rw [h4, abs_mul, show |(-3 : ℝ)| = 3 by norm_num]
  have h5 : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  nlinarith [abs_nonneg (Real.sin (2 * θ))]

/-! ## §3 The `Θ`-split of `Uop` -/

/-- On the open quadrant, `Uop α Φ` splits along `Φ = Φ̃ + Θ`. -/
theorem uop_split_theta {g : Fam} {τ z θ : ℝ} (hzθ : (z, θ) ∈ Q0)
    (hPsi : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0)
    (hTheta : ContDiffOn ℝ 3 (Function.uncurry (Theta (pExp α)
      (Ftau (pExp α) (GR α g) τ))) Q0) :
    Uop (pExp α) (slice (ΦR α Φs E g) τ) z θ
      = Uop (pExp α) (v2_PhiT α Φs E g τ) z θ
        + Uop (pExp α) (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ := by
  have hfun : slice (ΦR α Φs E g) τ = fun z θ => v2_PhiT α Φs E g τ z θ
      + Theta (pExp α) (Ftau (pExp α) (GR α g) τ) z θ := by
    funext z' θ'
    simp only [Work.FTS.Galerkin.slice, v2_PhiT, Work.Construction.PhiTil]
    ring
  have hd1 : DifferentiableAt ℝ (fun z' => v2_PhiT α Φs E g τ z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hPsi.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt
        (by norm_num))
  have hd2 : DifferentiableAt ℝ (fun z' => Theta (pExp α)
      (Ftau (pExp α) (GR α g) τ) z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hTheta.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt
        (by norm_num))
  rw [hfun]
  simp only [Uop, Work.Spaces.pz]
  rw [show (fun z' : ℝ => (fun z θ => v2_PhiT α Φs E g τ z θ
        + Theta (pExp α) (Ftau (pExp α) (GR α g) τ) z θ) z' θ)
      = (fun z' => v2_PhiT α Φs E g τ z' θ)
        + (fun z' => Theta (pExp α) (Ftau (pExp α) (GR α g) τ) z' θ) from rfl,
    deriv_add hd1 hd2]
  ring

end Work.FTS_RegExport.RXT.Sys
