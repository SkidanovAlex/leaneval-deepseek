/-
Copyright: Work.MRMT (mandelbar) subproject.

# A quasiregular solution of the Beltrami equation with decay at infinity vanishes

`Work.MRMT.QC.eq_zero_of_beltrami_of_decay`: if `h : ℂ → ℂ` is continuous, lies in
`W^{1,2}_{loc}(ℂ)`, satisfies `∂̄h = μ ∂h` a.e. with `‖μ‖ ≤ k < 1` a.e., and decays like
`C/‖z‖` at infinity, then `h = 0`.

The mathematical content is the Liouville theorem for quasiregular maps: a *bounded*
quasiregular map of the plane is constant, and `h → 0` at infinity pins the constant.

The proof here is a direct `L²`-energy argument that avoids the Ahlfors–Bers existence
theory.  Writing `gz = ∂h`, `gz̄ = ∂̄h` for the weak Wirtinger derivatives supplied by
`HasW12LocOn`, one tests `h` against a family of smooth cut-offs `ψₙ` which are `1` on
`B(0,Rₙ)` (`Rₙ = n+1`) and supported in `B(0,2Rₙ)`:

* the **energy identity** `∫‖∂u‖² = ∫‖∂̄u‖²` (`integral_norm_dz_eq_integral_norm_dzbar`)
  for the compactly supported `u = ψₙ h`;
* the weak **Leibniz rule** (`isDzDeriv_mul_and_isDbarDeriv_mul_of_contDiff_infty`) which
  identifies the weak derivatives of `ψₙ h` and lets the a.e. Beltrami equation be used;
* the resulting **a priori bound** `∫‖∂u‖² ≤ (∫e²)/(1-k)²`
  (`l2_bound_of_energy`) for the error term `e = ‖h‖(‖∂̄ψ‖ + k‖∂ψ‖)`, whose `L²` norm is
  `O(1/Rₙ)` by the decay hypothesis.

Consequently `∫_{B(0,Rₙ)}‖gz‖² → 0`, so `gz = 0` a.e.; then `gz̄ = μ gz = 0` a.e., so `h`
has vanishing weak `∂̄`, and Weyl's lemma (`differentiableOn_of_isDbarDerivOn_zero`) makes
`h` entire.  Liouville's theorem (`Differentiable.eq_const_of_tendsto_cocompact`) plus the
decay at infinity gives `h = 0`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.QC.CompHolo.Basic
import Submission.Work.MRMT.QC.WirtingerCalc
import Submission.Work.MRMT.QC.differentiableOn_of_isDbarDerivOn_zero
import Submission.Work.MRMT.QC.isDzDeriv_mul_and_isDbarDeriv_mul
import Submission.Work.MRMT.QC.l2_bound_of_energy
import Submission.Work.MRMT.QC.integral_norm_dz_eq_integral_norm_dzbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal ContDiff

namespace Work.MRMT.QC

/-! ## The cut-off family `ψₙ` -/

/-- The standard bump function on `ℂ`, `1` on `closedBall 0 1`, supported in `closedBall 0 2`. -/
def bumpC : ContDiffBump (0 : ℂ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The complex-valued version of `bumpC`. -/
def chiC : ℂ → ℂ := fun z => (bumpC z : ℂ)

/-- The outer radius `Rₙ = n + 1`. -/
def Rn (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The scaling factor `Rₙ⁻¹` (as a complex number). -/
def cC (n : ℕ) : ℂ := ((Rn n : ℝ)⁻¹ : ℂ)

/-- The cut-off `ψₙ(z) = χ(z/Rₙ)`. -/
def psiC (n : ℕ) : ℂ → ℂ := fun z => chiC (cC n * z)

theorem Rn_pos (n : ℕ) : 0 < Rn n := by unfold Rn; positivity

theorem norm_cC (n : ℕ) : ‖cC n‖ = (Rn n)⁻¹ := by
  unfold cC
  rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Rn_pos n).le)]

theorem cC_ne_zero (n : ℕ) : cC n ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_cC]; exact inv_ne_zero (ne_of_gt (Rn_pos n))

theorem chiC_one (w : ℂ) (h : ‖w‖ ≤ 1) : chiC w = 1 := by
  have hmem : w ∈ Metric.closedBall (0 : ℂ) bumpC.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]; simpa [bumpC] using h
  unfold chiC
  rw [ContDiffBump.one_of_mem_closedBall (f := bumpC) hmem]
  norm_num

theorem chiC_zero (w : ℂ) (h : 2 ≤ ‖w‖) : chiC w = 0 := by
  have hmem : bumpC.rOut ≤ dist w (0 : ℂ) := by
    rw [dist_zero_right]; simpa [bumpC] using h
  unfold chiC
  rw [ContDiffBump.zero_of_le_dist (f := bumpC) hmem]
  norm_num

theorem chiC_contDiff : ContDiff ℝ ∞ chiC := by
  unfold chiC
  have hcd : ContDiff ℝ ∞ (bumpC : ℂ → ℝ) := ContDiffBump.contDiff bumpC
  have := (Complex.ofRealCLM.contDiff).comp hcd
  simpa [Function.comp_def] using this

theorem chiC_cs : HasCompactSupport chiC := by
  unfold chiC
  have := (ContDiffBump.hasCompactSupport bumpC).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  simpa [Function.comp_def] using this

theorem psiC_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiC n) := by
  unfold psiC
  exact chiC_contDiff.comp (ContDiff.const_smul (cC n) contDiff_id)

theorem psiC_cs (n : ℕ) : HasCompactSupport (psiC n) := by
  unfold psiC
  exact chiC_cs.comp_smul (c := cC n) (cC_ne_zero n)

theorem psiC_one (n : ℕ) (z : ℂ) (h : ‖z‖ ≤ Rn n) : psiC n z = 1 := by
  unfold psiC
  apply chiC_one
  rw [norm_mul, norm_cC, inv_mul_le_one₀ (Rn_pos n)]
  exact h

theorem psiC_zero (n : ℕ) (z : ℂ) (h : 2 * Rn n ≤ ‖z‖) : psiC n z = 0 := by
  unfold psiC
  apply chiC_zero
  rw [norm_mul, norm_cC, inv_mul_eq_div, le_div_iff₀ (Rn_pos n)]
  linarith

theorem chiC_eventuallyEq_one (w : ℂ) (h : ‖w‖ < 1) : chiC =ᶠ[𝓝 w] (fun _ => (1 : ℂ)) := by
  have hmem : Metric.ball (0 : ℂ) (1 : ℝ) ∈ 𝓝 w :=
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using h)
  refine mem_of_superset hmem ?_
  intro x hx
  exact chiC_one x (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hx))

theorem chiC_dz_zero (w : ℂ) (h : ‖w‖ < 1) : Work.MRMT.dz chiC w = 0 := by
  have hf : fderiv ℝ chiC w = 0 := by
    rw [(chiC_eventuallyEq_one w h).fderiv_eq]; simp
  simp only [Work.MRMT.dz, hf]; simp

theorem chiC_dzbar_zero (w : ℂ) (h : ‖w‖ < 1) : Work.MRMT.dzbar chiC w = 0 := by
  have hf : fderiv ℝ chiC w = 0 := by
    rw [(chiC_eventuallyEq_one w h).fderiv_eq]; simp
  simp only [Work.MRMT.dzbar, hf]; simp

/-! ## The chain rule for `ψₙ` and its consequences -/

theorem deriv_const_mul_cC (n : ℕ) (z : ℂ) :
    deriv (fun w : ℂ => cC n * w) z = cC n := by
  have hd : HasDerivAt (fun w : ℂ => cC n * w) (cC n) z := by
    simpa using (hasDerivAt_id z).const_mul (cC n)
  exact hd.deriv

theorem psiC_dz (n : ℕ) (z : ℂ) :
    Work.MRMT.dz (psiC n) z = cC n * Work.MRMT.dz chiC (cC n * z) := by
  have hgd : DifferentiableAt ℝ chiC (cC n * z) :=
    (chiC_contDiff.differentiable (by simp)).differentiableAt
  have hfd : DifferentiableAt ℂ (fun w : ℂ => cC n * w) z := by fun_prop
  have h := Work.MRMT.QC.dz_comp_holo (g := chiC) (f := fun w : ℂ => cC n * w) hgd hfd
  have hcomp : psiC n = chiC ∘ (fun w : ℂ => cC n * w) := rfl
  rw [hcomp, h, deriv_const_mul_cC]

theorem psiC_dzbar (n : ℕ) (z : ℂ) :
    Work.MRMT.dzbar (psiC n) z = star (cC n) * Work.MRMT.dzbar chiC (cC n * z) := by
  have hgd : DifferentiableAt ℝ chiC (cC n * z) :=
    (chiC_contDiff.differentiable (by simp)).differentiableAt
  have hfd : DifferentiableAt ℂ (fun w : ℂ => cC n * w) z := by fun_prop
  have h := Work.MRMT.QC.dzbar_comp_holo (g := chiC) (f := fun w : ℂ => cC n * w) hgd hfd
  have hcomp : psiC n = chiC ∘ (fun w : ℂ => cC n * w) := rfl
  rw [hcomp, h, deriv_const_mul_cC]

theorem psiC_dz_zero (n : ℕ) (z : ℂ) (h : ‖z‖ < Rn n) : Work.MRMT.dz (psiC n) z = 0 := by
  rw [psiC_dz]
  have h1 : ‖cC n * z‖ < 1 := by
    rw [norm_mul, norm_cC, inv_mul_lt_one₀ (Rn_pos n)]; exact h
  rw [chiC_dz_zero _ h1, mul_zero]

theorem psiC_dzbar_zero (n : ℕ) (z : ℂ) (h : ‖z‖ < Rn n) : Work.MRMT.dzbar (psiC n) z = 0 := by
  rw [psiC_dzbar]
  have h1 : ‖cC n * z‖ < 1 := by
    rw [norm_mul, norm_cC, inv_mul_lt_one₀ (Rn_pos n)]; exact h
  rw [chiC_dzbar_zero _ h1, mul_zero]

/-- `∂χ` has compact support (it vanishes where `χ` is locally constant and where `χ` vanishes). -/
theorem chiC_dz_cs : HasCompactSupport (Work.MRMT.dz chiC) := by
  have h := (chiC_cs.fderiv ℝ).comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (L 1 - Complex.I * L Complex.I) / 2) (by simp)
  have hfun : (fun x : ℂ => ((fderiv ℝ chiC x) 1 - Complex.I * (fderiv ℝ chiC x) Complex.I) / 2)
      = Work.MRMT.dz chiC := by funext x; simp only [Work.MRMT.dz]
  rw [Function.comp_def] at h
  rwa [hfun] at h

/-- `∂̄χ` has compact support. -/
theorem chiC_dzbar_cs : HasCompactSupport (Work.MRMT.dzbar chiC) := by
  have h := (chiC_cs.fderiv ℝ).comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (L 1 + Complex.I * L Complex.I) / 2) (by simp)
  have hfun : (fun x : ℂ => ((fderiv ℝ chiC x) 1 + Complex.I * (fderiv ℝ chiC x) Complex.I) / 2)
      = Work.MRMT.dzbar chiC := by funext x; simp only [Work.MRMT.dzbar]
  rw [Function.comp_def] at h
  rwa [hfun] at h

/-- Pointwise bound for `∂` on a normed space. -/
theorem norm_dz_le_fderiv (g : ℂ → ℂ) (z : ℂ) :
    ‖Work.MRMT.dz g z‖ ≤ ‖fderiv ℝ g z‖ := by
  have h1 : ‖fderiv ℝ g z 1‖ ≤ ‖fderiv ℝ g z‖ := by
    simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ g z) (1 : ℂ)
  have hI : ‖fderiv ℝ g z Complex.I‖ ≤ ‖fderiv ℝ g z‖ := by
    have := ContinuousLinearMap.le_opNorm (fderiv ℝ g z) Complex.I
    simpa using this
  have h2 : ‖(fderiv ℝ g z) 1 - Complex.I * (fderiv ℝ g z) Complex.I‖ ≤ 2 * ‖fderiv ℝ g z‖ := by
    calc ‖(fderiv ℝ g z) 1 - Complex.I * (fderiv ℝ g z) Complex.I‖
        ≤ ‖(fderiv ℝ g z) 1‖ + ‖Complex.I * (fderiv ℝ g z) Complex.I‖ := norm_sub_le _ _
      _ = ‖(fderiv ℝ g z) 1‖ + ‖(fderiv ℝ g z) Complex.I‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖fderiv ℝ g z‖ + ‖fderiv ℝ g z‖ := add_le_add h1 hI
      _ = 2 * ‖fderiv ℝ g z‖ := by ring
  rw [Work.MRMT.dz, norm_div]
  have h3 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h3]
  linarith

theorem norm_dzbar_le_fderiv (g : ℂ → ℂ) (z : ℂ) :
    ‖Work.MRMT.dzbar g z‖ ≤ ‖fderiv ℝ g z‖ := by
  have h1 : ‖fderiv ℝ g z 1‖ ≤ ‖fderiv ℝ g z‖ := by
    simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ g z) (1 : ℂ)
  have hI : ‖fderiv ℝ g z Complex.I‖ ≤ ‖fderiv ℝ g z‖ := by
    have := ContinuousLinearMap.le_opNorm (fderiv ℝ g z) Complex.I
    simpa using this
  have h2 : ‖(fderiv ℝ g z) 1 + Complex.I * (fderiv ℝ g z) Complex.I‖ ≤ 2 * ‖fderiv ℝ g z‖ := by
    calc ‖(fderiv ℝ g z) 1 + Complex.I * (fderiv ℝ g z) Complex.I‖
        ≤ ‖(fderiv ℝ g z) 1‖ + ‖Complex.I * (fderiv ℝ g z) Complex.I‖ := norm_add_le _ _
      _ = ‖(fderiv ℝ g z) 1‖ + ‖(fderiv ℝ g z) Complex.I‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖fderiv ℝ g z‖ + ‖fderiv ℝ g z‖ := add_le_add h1 hI
      _ = 2 * ‖fderiv ℝ g z‖ := by ring
  rw [Work.MRMT.dzbar, norm_div]
  have h3 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h3]
  linarith

/-- Derivative bound for `ψₙ = χ(·/Rₙ)`. -/
theorem psiC_dz_bound (n : ℕ) {M : ℝ} (hM : ∀ w : ℂ, ‖fderiv ℝ chiC w‖ ≤ M) (z : ℂ) :
    ‖Work.MRMT.dz (psiC n) z‖ ≤ M / Rn n ∧
    ‖Work.MRMT.dzbar (psiC n) z‖ ≤ M / Rn n := by
  have hdz : ‖Work.MRMT.dz (psiC n) z‖ = (Rn n)⁻¹ * ‖Work.MRMT.dz chiC (cC n * z)‖ := by
    rw [psiC_dz, norm_mul, norm_cC]
  have hdzb : ‖Work.MRMT.dzbar (psiC n) z‖ = (Rn n)⁻¹ * ‖Work.MRMT.dzbar chiC (cC n * z)‖ := by
    rw [psiC_dzbar, norm_mul, norm_star, norm_cC]
  have hb1 : ‖Work.MRMT.dz chiC (cC n * z)‖ ≤ M :=
    le_trans (norm_dz_le_fderiv chiC _) (hM _)
  have hb2 : ‖Work.MRMT.dzbar chiC (cC n * z)‖ ≤ M :=
    le_trans (norm_dzbar_le_fderiv chiC _) (hM _)
  constructor
  · rw [hdz, div_eq_mul_inv, mul_comm (M) ((Rn n)⁻¹)]
    exact mul_le_mul_of_nonneg_left hb1 (le_of_lt (inv_pos.mpr (Rn_pos n)))
  · rw [hdzb, div_eq_mul_inv, mul_comm (M) ((Rn n)⁻¹)]
    exact mul_le_mul_of_nonneg_left hb2 (le_of_lt (inv_pos.mpr (Rn_pos n)))

/-! ## The `L²` estimate for the error term -/

/-- The error term `eₙ` of the cut-off argument. -/
def eC (h : ℂ → ℂ) (k : ℝ) (n : ℕ) : ℂ → ℝ :=
  fun z => ‖h z‖ * (‖Work.MRMT.dzbar (psiC n) z‖ + k * ‖Work.MRMT.dz (psiC n) z‖)

theorem psiC_dz_scaled (n : ℕ) (w : ℂ) :
    Work.MRMT.dz (psiC n) (Rn n • w) = cC n * Work.MRMT.dz chiC w := by
  rw [psiC_dz]
  have hne : (Rn n : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (Rn_pos n)
  have harg : cC n * (Rn n • w) = w := by
    rw [cC, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (ne_of_gt (Rn_pos n)), Complex.ofReal_one, one_mul]
  rw [harg]

theorem psiC_dzbar_scaled (n : ℕ) (w : ℂ) :
    Work.MRMT.dzbar (psiC n) (Rn n • w) = star (cC n) * Work.MRMT.dzbar chiC w := by
  rw [psiC_dzbar]
  have hne : (Rn n : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (Rn_pos n)
  have harg : cC n * (Rn n • w) = w := by
    rw [cC, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (ne_of_gt (Rn_pos n)), Complex.ofReal_one, one_mul]
  rw [harg]

theorem eC_scaled (h : ℂ → ℂ) (k : ℝ) (n : ℕ) (w : ℂ) :
    eC h k n (Rn n • w)
      = (Rn n)⁻¹ * (‖h (Rn n • w)‖ * (‖Work.MRMT.dzbar chiC w‖ + k * ‖Work.MRMT.dz chiC w‖)) := by
  unfold eC
  rw [psiC_dzbar_scaled, psiC_dz_scaled]
  simp only [norm_mul, norm_star, norm_cC]
  ring

/-- The substitution `z = Rₙ w` in the error integral. -/
theorem integral_eC_sq_eq (h : ℂ → ℂ) (k : ℝ) (n : ℕ) :
    (∫ z, (eC h k n z)^2)
      = ∫ w, (‖h (Rn n • w)‖ * (‖Work.MRMT.dzbar chiC w‖ + k * ‖Work.MRMT.dz chiC w‖))^2 := by
  have hne : (Rn n : ℝ) ≠ 0 := ne_of_gt (Rn_pos n)
  have hsub := MeasureTheory.Measure.integral_comp_smul (volume : Measure ℂ)
    (fun z => (eC h k n z)^2) (Rn n)
  rw [Complex.finrank_real_complex] at hsub
  simp only [smul_eq_mul] at hsub
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))] at hsub
  have hpt : ∀ w, (‖h (Rn n • w)‖ * (‖Work.MRMT.dzbar chiC w‖ + k * ‖Work.MRMT.dz chiC w‖))^2
      = (Rn n)^2 * (eC h k n (Rn n • w))^2 := by
    intro w
    set G : ℝ := ‖h (Rn n • w)‖ * (‖Work.MRMT.dzbar chiC w‖ + k * ‖Work.MRMT.dz chiC w‖) with hG
    rw [eC_scaled]
    have h2 : (Rn n)^2 * ((Rn n)⁻¹ * G)^2 = G^2 := by
      rw [← mul_pow]
      rw [show Rn n * ((Rn n)⁻¹ * G) = G by
        rw [← mul_assoc, mul_comm (Rn n) ((Rn n)⁻¹), inv_mul_cancel₀ hne, one_mul]]
    rw [h2]
  have h1 : (∫ z, (eC h k n z)^2) = (Rn n)^2 * (∫ w, (eC h k n (Rn n • w))^2) := by
    rw [hsub]; field_simp
  rw [h1, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun w => (hpt w).symm)

/-- Pointwise bound on the substituted integrand, using the decay of `h`. -/
theorem eC_bound (h : ℂ → ℂ) {k C R : ℝ} (hk0 : 0 ≤ k) (hC : 0 ≤ C)
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ C / ‖z‖) (n : ℕ) (hn : R ≤ Rn n) (w : ℂ) :
    (‖h (Rn n • w)‖ * (‖Work.MRMT.dzbar chiC w‖ + k * ‖Work.MRMT.dz chiC w‖))^2
      ≤ (C / Rn n)^2 * (‖Work.MRMT.dzbar chiC w‖ + k * ‖Work.MRMT.dz chiC w‖)^2 := by
  set A : ℝ := ‖Work.MRMT.dzbar chiC w‖ + k * ‖Work.MRMT.dz chiC w‖ with hA
  by_cases hw : ‖w‖ < 1
  · rw [chiC_dz_zero w hw, chiC_dzbar_zero w hw] at hA
    rw [hA]; simp
  · push_neg at hw
    have hb : ‖h (Rn n • w)‖ ≤ C / Rn n := by
      have h1 := hdec (Rn n • w) (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Rn_pos n).le]
        nlinarith [hw, hn, Rn_pos n])
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Rn_pos n).le] at h1
      refine le_trans h1 ?_
      rw [div_le_div_iff₀ (mul_pos (Rn_pos n) (by linarith)) (Rn_pos n)]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (le_of_lt (Rn_pos n)) hw) hC
    have h3 : ‖h (Rn n • w)‖^2 ≤ (C / Rn n)^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have h4 : (‖h (Rn n • w)‖ * A)^2 ≤ (C / Rn n)^2 * A^2 := by
      calc (‖h (Rn n • w)‖ * A)^2 = ‖h (Rn n • w)‖^2 * A^2 := by ring
        _ ≤ (C / Rn n)^2 * A^2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg A)
    rw [hA] at h4
    rwa [hA]

/-- `∫ eₙ² → 0` along the family of cut-offs. -/
theorem tendsto_integral_eC_sq {h : ℂ → ℂ} (hh : Continuous h) {k C R : ℝ} (hk0 : 0 ≤ k)
    (hC : 0 ≤ C) (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ C / ‖z‖) :
    Tendsto (fun n : ℕ => ∫ z, (eC h k n z)^2) atTop (𝓝 0) := by
  set A : ℂ → ℝ := fun w => ‖Work.MRMT.dzbar chiC w‖ + k * ‖Work.MRMT.dz chiC w‖ with hA
  have hAc : Continuous A := by
    rw [hA]
    exact (Work.MRMT.QC.continuous_dzbar_of_contDiff (by simp) chiC_contDiff).norm.add
      (continuous_const.mul
        (Work.MRMT.QC.continuous_dz_of_contDiff (by simp) chiC_contDiff).norm)
  have hAs : HasCompactSupport A := by
    rw [hA]
    exact chiC_dzbar_cs.norm.add (chiC_dz_cs.norm.mul_left (f := fun _ : ℂ => k))
  have hApow : HasCompactSupport (fun w => (A w)^2) := by
    have := hAs.mul_right (f' := A)
    convert this using 1
    funext w; rw [Pi.mul_apply, sq]
  have hAint : Integrable (fun w => (A w)^2) :=
    (hAc.pow 2).integrable_of_hasCompactSupport hApow
  set K : ℝ := ∫ w, (A w)^2 with hK
  have hK0 : 0 ≤ K := integral_nonneg (fun w => sq_nonneg _)
  have hbdd : ∀ᶠ n : ℕ in atTop, ∫ z, (eC h k n z)^2 ≤ (C / Rn n)^2 * K := by
    filter_upwards [eventually_ge_atTop ⌈max R 0⌉₊] with n hn
    have hn' : R ≤ Rn n := by
      have h1 : R ≤ (max R 0 : ℝ) := le_max_left _ _
      have h4 : (max R 0 : ℝ) ≤ ((⌈max R 0⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈max R 0⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h3 : (n : ℝ) ≤ Rn n := by unfold Rn; linarith
      linarith
    have hGeo : Integrable (fun w => (‖h (Rn n • w)‖ * A w)^2) := by
      have hcont : Continuous (fun w : ℂ => ‖h (Rn n • w)‖ * A w) :=
        ((hh.comp (continuous_const_smul (Rn n))).norm).mul hAc
      have hGpow : HasCompactSupport (fun w => (‖h (Rn n • w)‖ * A w)^2) := by
        have hbase : HasCompactSupport (fun w => ‖h (Rn n • w)‖ * A w) := hAs.mul_left
        have := hbase.mul_right (f' := fun w => ‖h (Rn n • w)‖ * A w)
        convert this using 1
        funext w; rw [Pi.mul_apply, sq]
      exact (hcont.pow 2).integrable_of_hasCompactSupport hGpow
    have hmaj : Integrable (fun w => (C / Rn n)^2 * (A w)^2) := hAint.const_mul _
    have hle : ∀ w, (‖h (Rn n • w)‖ * A w)^2 ≤ (C / Rn n)^2 * (A w)^2 := by
      intro w; rw [hA]; exact eC_bound h hk0 hC hdec n hn' w
    calc ∫ z, (eC h k n z)^2
        = ∫ w, (‖h (Rn n • w)‖ * A w)^2 := by rw [integral_eC_sq_eq, hA]
      _ ≤ ∫ w, (C / Rn n)^2 * (A w)^2 := integral_mono_ae hGeo hmaj (Eventually.of_forall hle)
      _ = (C / Rn n)^2 * K := by rw [integral_const_mul, hK]
  have hR0 : Tendsto (fun n : ℕ => (C / Rn n)^2 * K) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (C : ℝ) / Rn n) atTop (𝓝 0) := by
      have h2 : (fun n : ℕ => (C : ℝ) / Rn n) = fun n : ℕ => C * (1 / ((n : ℝ) + 1)) := by
        funext n; rw [Rn]; ring
      rw [h2]
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    simpa using (h1.pow 2).mul_const K
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR0
    (Eventually.of_forall fun n => integral_nonneg fun z => sq_nonneg _) hbdd


/-! ## Support and auxiliary facts for the cut-off family -/

theorem chiC_fderiv_bound : ∃ M : ℝ, ∀ w : ℂ, ‖fderiv ℝ chiC w‖ ≤ M := by
  have hcs : HasCompactSupport (fderiv ℝ chiC) := chiC_cs.fderiv ℝ
  have hcont : Continuous (fderiv ℝ chiC) := chiC_contDiff.continuous_fderiv (by simp)
  have hbdd : Bornology.IsBounded (Set.range (fderiv ℝ chiC)) := by
    have himg : IsCompact ((fderiv ℝ chiC) '' tsupport (fderiv ℝ chiC)) := hcs.image hcont
    have hsub : Set.range (fderiv ℝ chiC) ⊆
        (fderiv ℝ chiC) '' tsupport (fderiv ℝ chiC) ∪ {0} := by
      intro L hL
      obtain ⟨w, rfl⟩ := hL
      by_cases hw : fderiv ℝ chiC w = 0
      · exact Or.inr hw
      · exact Or.inl ⟨w, subset_tsupport _ (by simpa [Function.mem_support] using hw), rfl⟩
    exact (himg.isBounded.union Bornology.isBounded_singleton).subset hsub
  rw [isBounded_iff_forall_norm_le] at hbdd
  obtain ⟨M, hM⟩ := hbdd
  exact ⟨M, fun w => hM _ (Set.mem_range_self w)⟩

theorem psiC_norm_le_one (n : ℕ) (z : ℂ) : ‖psiC n z‖ ≤ 1 := by
  have h1 : 0 ≤ bumpC (cC n * z) := bumpC.nonneg
  have h2 : bumpC (cC n * z) ≤ 1 := bumpC.le_one
  unfold psiC chiC
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, h2⟩

theorem chiC_eventuallyEq_zero (w : ℂ) (h : 2 < ‖w‖) : chiC =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := by
  have hr : 0 < (‖w‖ - 2) / 2 := by linarith
  have hmem : Metric.ball w ((‖w‖ - 2) / 2) ∈ 𝓝 w := Metric.ball_mem_nhds w hr
  refine mem_of_superset hmem ?_
  intro x hx
  rw [Metric.mem_ball] at hx
  exact chiC_zero x (by
    have h1 : ‖w‖ ≤ ‖x‖ + dist x w := by
      have := dist_triangle w x 0
      rw [dist_zero_right, dist_zero_right, dist_comm w x] at this
      linarith
    linarith)

theorem chiC_dz_zero_of_gt (w : ℂ) (h : 2 < ‖w‖) : Work.MRMT.dz chiC w = 0 := by
  have hf : fderiv ℝ chiC w = 0 := by
    rw [(chiC_eventuallyEq_zero w h).fderiv_eq]; simp
  simp only [Work.MRMT.dz, hf]; simp

theorem chiC_dzbar_zero_of_gt (w : ℂ) (h : 2 < ‖w‖) : Work.MRMT.dzbar chiC w = 0 := by
  have hf : fderiv ℝ chiC w = 0 := by
    rw [(chiC_eventuallyEq_zero w h).fderiv_eq]; simp
  simp only [Work.MRMT.dzbar, hf]; simp

theorem psiC_support_subset (n : ℕ) :
    Function.support (psiC n) ⊆ Metric.closedBall (0 : ℂ) (2 * Rn n) := by
  intro z hz
  simp only [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hc
  push_neg at hc
  exact hz (psiC_zero n z (le_of_lt hc))

theorem psiC_dz_zero_of_gt (n : ℕ) (z : ℂ) (h : 2 * Rn n < ‖z‖) : Work.MRMT.dz (psiC n) z = 0 := by
  rw [psiC_dz]
  have h1 : 2 < ‖cC n * z‖ := by
    rw [norm_mul, norm_cC, inv_mul_eq_div, lt_div_iff₀ (Rn_pos n)]
    linarith
  rw [chiC_dz_zero_of_gt _ h1, mul_zero]

theorem psiC_dzbar_zero_of_gt (n : ℕ) (z : ℂ) (h : 2 * Rn n < ‖z‖) :
    Work.MRMT.dzbar (psiC n) z = 0 := by
  rw [psiC_dzbar]
  have h1 : 2 < ‖cC n * z‖ := by
    rw [norm_mul, norm_cC, inv_mul_eq_div, lt_div_iff₀ (Rn_pos n)]
    linarith
  rw [chiC_dzbar_zero_of_gt _ h1, mul_zero]

theorem psiC_dz_support (n : ℕ) :
    Function.support (fun z => Work.MRMT.dz (psiC n) z) ⊆ Metric.closedBall (0 : ℂ) (2 * Rn n) := by
  intro z hz
  simp only [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hc
  push_neg at hc
  exact hz (psiC_dz_zero_of_gt n z hc)


/-! ## The weak derivatives of `ψₙ h` and their `L²` membership -/

/-- `p = ∂(ψₙ h)`. -/
def pC (h gz : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => psiC n z * gz z + h z * Work.MRMT.dz (psiC n) z

/-- `q = ∂̄(ψₙ h)`. -/
def qC (h gzbar : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => psiC n z * gzbar z + h z * Work.MRMT.dzbar (psiC n) z

theorem memL2Loc_integrableOn {f : ℂ → ℂ} (h : MemL2Loc f) {K : Set ℂ} (hK : IsCompact K) :
    IntegrableOn (fun z => ‖f z‖^2) K (volume : Measure ℂ) := by
  simpa using h K hK

theorem memLp_two_of_integrableOn {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AEStronglyMeasurable f (volume : Measure ℂ))
    (hK : IntegrableOn (fun z => ‖f z‖^2) K (volume : Measure ℂ))
    (hsupp : Function.support f ⊆ K) : MemLp f 2 (volume : Measure ℂ) := by
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hf]
  have hsupp' : Function.support (fun z => ‖f z‖^2) ⊆ K := by
    intro z hz
    simp only [Function.mem_support] at hz
    refine hsupp ?_
    simp only [Function.mem_support]
    intro h0; exact hz (by rw [h0]; simp)
  exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset (s := K) hsupp').mp hK

/-- `IntegrableOn` of `‖f‖²` from a two-term domination by `L²_loc` functions. -/
theorem integrableOn_sq_of_bound {f g₁ g₂ : ℂ → ℂ} {K : Set ℂ} {a b : ℝ}
    (hK : IsCompact K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : AEStronglyMeasurable f (volume : Measure ℂ))
    (h1 : MemL2Loc g₁) (h2 : MemL2Loc g₂)
    (hbd : ∀ z, ‖f z‖ ≤ a * ‖g₁ z‖ + b * ‖g₂ z‖) :
    IntegrableOn (fun z => ‖f z‖^2) K (volume : Measure ℂ) := by
  set G : ℂ → ℝ := fun z => 2 * (a^2 * ‖g₁ z‖^2 + b^2 * ‖g₂ z‖^2) with hG
  have hGint : Integrable G ((volume : Measure ℂ).restrict K) := by
    rw [hG]
    exact (((memL2Loc_integrableOn h1 hK).const_mul (a^2)).add
      ((memL2Loc_integrableOn h2 hK).const_mul (b^2))).const_mul 2
  have hle : (volume : Measure ℂ).restrict K ≤ (volume : Measure ℂ) := Measure.restrict_le_self
  have hfK : AEStronglyMeasurable (fun z => ‖f z‖^2) ((volume : Measure ℂ).restrict K) :=
    ((hf.mono_measure hle).norm.pow 2)
  have hbdd : ∀ᵐ z ∂((volume : Measure ℂ).restrict K),
      ‖(fun z => ‖f z‖^2) z‖ ≤ G z := by
    refine ae_of_all _ (fun z => ?_)
    have h1' : ‖f z‖^2 ≤ (a * ‖g₁ z‖ + b * ‖g₂ z‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hbd z) 2
    have h2' : (a * ‖g₁ z‖ + b * ‖g₂ z‖)^2 ≤ G z := by
      rw [hG]; nlinarith [sq_nonneg (a * ‖g₁ z‖ - b * ‖g₂ z‖)]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    linarith
  exact hGint.mono' hfK hbdd

theorem memLp_pC {h gz : ℂ → ℂ} {n : ℕ} (hh : AEStronglyMeasurable h (volume : Measure ℂ))
    (hg : AEStronglyMeasurable gz (volume : Measure ℂ)) (hgzl : MemL2Loc gz)
    (hl : MemL2Loc h) {M : ℝ} (hM : ∀ w : ℂ, ‖fderiv ℝ chiC w‖ ≤ M) :
    MemLp (pC h gz n) 2 (volume : Measure ℂ) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (2 * Rn n + 1)) := isCompact_closedBall _ _
  have hmeas : AEStronglyMeasurable (pC h gz n) (volume : Measure ℂ) := by
    unfold pC
    exact ((psiC_contDiff n).continuous.aestronglyMeasurable.mul hg).add
      (hh.mul ((Work.MRMT.QC.continuous_dz_of_contDiff (by simp) (psiC_contDiff n)).aestronglyMeasurable))
  have hbd : ∀ z, ‖pC h gz n z‖ ≤ 1 * ‖gz z‖ + (M / Rn n) * ‖h z‖ := by
    intro z
    have h1 : ‖Work.MRMT.dz (psiC n) z‖ ≤ M / Rn n := (psiC_dz_bound n hM z).1
    have h2 : ‖h z‖ * ‖Work.MRMT.dz (psiC n) z‖ ≤ ‖h z‖ * (M / Rn n) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    calc ‖pC h gz n z‖
        = ‖psiC n z * gz z + h z * Work.MRMT.dz (psiC n) z‖ := rfl
      _ ≤ ‖psiC n z * gz z‖ + ‖h z * Work.MRMT.dz (psiC n) z‖ := norm_add_le _ _
      _ = ‖psiC n z‖ * ‖gz z‖ + ‖h z‖ * ‖Work.MRMT.dz (psiC n) z‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖gz z‖ + ‖h z‖ * (M / Rn n) :=
          add_le_add (mul_le_mul_of_nonneg_right (psiC_norm_le_one n z) (norm_nonneg _)) h2
      _ = 1 * ‖gz z‖ + (M / Rn n) * ‖h z‖ := by ring
  have hInt : IntegrableOn (fun z => ‖pC h gz n z‖^2) (Metric.closedBall (0:ℂ) (2*Rn n+1)) volume :=
    integrableOn_sq_of_bound hK zero_le_one (div_nonneg hM0 (le_of_lt (Rn_pos n)))
      hmeas hgzl hl hbd
  have hsupp : Function.support (pC h gz n) ⊆ Metric.closedBall (0:ℂ) (2*Rn n+1) := by
    intro z hz
    simp only [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hc
    push_neg at hc
    apply hz
    have hzc : 2 * Rn n < ‖z‖ := by linarith
    unfold pC
    rw [psiC_zero n z (le_of_lt (by linarith)), psiC_dz_zero_of_gt n z hzc]
    ring
  exact memLp_two_of_integrableOn hmeas hInt hsupp

theorem memLp_qC {h gzbar : ℂ → ℂ} {n : ℕ} (hh : AEStronglyMeasurable h (volume : Measure ℂ))
    (hg : AEStronglyMeasurable gzbar (volume : Measure ℂ)) (hgzl : MemL2Loc gzbar)
    (hl : MemL2Loc h) {M : ℝ} (hM : ∀ w : ℂ, ‖fderiv ℝ chiC w‖ ≤ M) :
    MemLp (qC h gzbar n) 2 (volume : Measure ℂ) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (2 * Rn n + 1)) := isCompact_closedBall _ _
  have hmeas : AEStronglyMeasurable (qC h gzbar n) (volume : Measure ℂ) := by
    unfold qC
    exact ((psiC_contDiff n).continuous.aestronglyMeasurable.mul hg).add
      (hh.mul ((Work.MRMT.QC.continuous_dzbar_of_contDiff (by simp) (psiC_contDiff n)).aestronglyMeasurable))
  have hbd : ∀ z, ‖qC h gzbar n z‖ ≤ 1 * ‖gzbar z‖ + (M / Rn n) * ‖h z‖ := by
    intro z
    have h1 : ‖Work.MRMT.dzbar (psiC n) z‖ ≤ M / Rn n := (psiC_dz_bound n hM z).2
    have h2 : ‖h z‖ * ‖Work.MRMT.dzbar (psiC n) z‖ ≤ ‖h z‖ * (M / Rn n) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    calc ‖qC h gzbar n z‖
        = ‖psiC n z * gzbar z + h z * Work.MRMT.dzbar (psiC n) z‖ := rfl
      _ ≤ ‖psiC n z * gzbar z‖ + ‖h z * Work.MRMT.dzbar (psiC n) z‖ := norm_add_le _ _
      _ = ‖psiC n z‖ * ‖gzbar z‖ + ‖h z‖ * ‖Work.MRMT.dzbar (psiC n) z‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖gzbar z‖ + ‖h z‖ * (M / Rn n) :=
          add_le_add (mul_le_mul_of_nonneg_right (psiC_norm_le_one n z) (norm_nonneg _)) h2
      _ = 1 * ‖gzbar z‖ + (M / Rn n) * ‖h z‖ := by ring
  have hInt : IntegrableOn (fun z => ‖qC h gzbar n z‖^2) (Metric.closedBall (0:ℂ) (2*Rn n+1)) volume :=
    integrableOn_sq_of_bound hK zero_le_one (div_nonneg hM0 (le_of_lt (Rn_pos n)))
      hmeas hgzl hl hbd
  have hsupp : Function.support (qC h gzbar n) ⊆ Metric.closedBall (0:ℂ) (2*Rn n+1) := by
    intro z hz
    simp only [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hc
    push_neg at hc
    apply hz
    have hzc : 2 * Rn n < ‖z‖ := by linarith
    unfold qC
    rw [psiC_zero n z (le_of_lt (by linarith)), psiC_dzbar_zero_of_gt n z hzc]
    ring
  exact memLp_two_of_integrableOn hmeas hInt hsupp

theorem memLp_eC {h : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) {n : ℕ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w : ℂ, ‖fderiv ℝ chiC w‖ ≤ M) (hh : AEStronglyMeasurable h (volume : Measure ℂ))
    (hl : MemL2Loc h) : MemLp (eC h k n) 2 (volume : Measure ℂ) := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (2 * Rn n + 1)) := isCompact_closedBall _ _
  have hmeas : AEStronglyMeasurable (eC h k n) (volume : Measure ℂ) := by
    have h1 : Continuous (fun z => ‖Work.MRMT.dz (psiC n) z‖) :=
      (Work.MRMT.QC.continuous_dz_of_contDiff (by simp) (psiC_contDiff n)).norm
    have h2 : Continuous (fun z => ‖Work.MRMT.dzbar (psiC n) z‖) :=
      (Work.MRMT.QC.continuous_dzbar_of_contDiff (by simp) (psiC_contDiff n)).norm
    unfold eC
    exact hh.norm.mul (h2.aestronglyMeasurable.add (continuous_const.mul h1).aestronglyMeasurable)
  rw [MeasureTheory.memLp_two_iff_integrable_sq hmeas]
  have hhK : IntegrableOn (fun z => ‖h z‖^2) (Metric.closedBall (0:ℂ) (2*Rn n+1)) volume :=
    memL2Loc_integrableOn hl hK
  have hdom : Integrable ((Metric.closedBall (0:ℂ) (2*Rn n+1)).indicator
      (fun z => (M * (1 + k) / Rn n)^2 * ‖h z‖^2)) :=
    (integrable_indicator_iff hK.isClosed.measurableSet).mpr (hhK.const_mul _)
  refine hdom.mono' ((hmeas.pow 2)) ?_
  refine ae_of_all _ (fun z => ?_)
  have hbd : ‖eC h k n z‖ ≤ M * (1 + k) / Rn n * ‖h z‖ := by
    have h1 : ‖Work.MRMT.dz (psiC n) z‖ ≤ M / Rn n := (psiC_dz_bound n hM z).1
    have h2 : ‖Work.MRMT.dzbar (psiC n) z‖ ≤ M / Rn n := (psiC_dz_bound n hM z).2
    unfold eC
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (mul_nonneg hk0 (norm_nonneg _))))]
    calc ‖h z‖ * (‖Work.MRMT.dzbar (psiC n) z‖ + k * ‖Work.MRMT.dz (psiC n) z‖)
        ≤ ‖h z‖ * (M / Rn n + k * (M / Rn n)) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add h2 (mul_le_mul_of_nonneg_left h1 hk0)) (norm_nonneg _)
      _ = M * (1 + k) / Rn n * ‖h z‖ := by ring
  have htarget : ‖(fun z => eC h k n z ^ 2) z‖ ≤
      ((Metric.closedBall (0:ℂ) (2*Rn n+1)).indicator (fun z => (M * (1 + k) / Rn n)^2 * ‖h z‖^2)) z := by
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) (2 * Rn n + 1)
    · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (sq_nonneg _)]
      have h3 : (M * (1 + k) / Rn n) ^ 2 * ‖h z‖^2 = (M * (1 + k) / Rn n * ‖h z‖)^2 := by ring
      rw [h3]
      simpa only [Real.norm_eq_abs, sq_abs] using
        pow_le_pow_left₀ (norm_nonneg (eC h k n z)) hbd 2
    · have hz0 : eC h k n z = 0 := by
        unfold eC
        have hzc : 2 * Rn n < ‖z‖ := by
          have h1 : 2 * Rn n + 1 < ‖z‖ := not_le.mp (by
            simpa [Metric.mem_closedBall, dist_zero_right] using hz)
          linarith
        rw [psiC_dz_zero_of_gt n z hzc, psiC_dzbar_zero_of_gt n z hzc]
        simp
      rw [Set.indicator_of_notMem hz]
      simp [hz0]
  exact htarget



theorem aesm_pC {h gz : ℂ → ℂ} {n : ℕ} (hh : AEStronglyMeasurable h (volume : Measure ℂ))
    (hg : AEStronglyMeasurable gz (volume : Measure ℂ)) :
    AEStronglyMeasurable (pC h gz n) (volume : Measure ℂ) := by
  unfold pC
  exact ((psiC_contDiff n).continuous.aestronglyMeasurable.mul hg).add
    (hh.mul ((Work.MRMT.QC.continuous_dz_of_contDiff (by simp)
      (psiC_contDiff n)).aestronglyMeasurable))

theorem aesm_qC {h gz : ℂ → ℂ} {n : ℕ} (hh : AEStronglyMeasurable h (volume : Measure ℂ))
    (hg : AEStronglyMeasurable gz (volume : Measure ℂ)) :
    AEStronglyMeasurable (qC h gz n) (volume : Measure ℂ) := by
  unfold qC
  exact ((psiC_contDiff n).continuous.aestronglyMeasurable.mul hg).add
    (hh.mul ((Work.MRMT.QC.continuous_dzbar_of_contDiff (by simp)
      (psiC_contDiff n)).aestronglyMeasurable))

/-- **The main theorem.** -/
theorem eq_zero_of_beltrami_of_decay {h : ℂ → ℂ} {μ : ℂ → ℂ} {k : ℝ}
    (hf : Continuous h) (hW : Work.MRMT.HasW12LocOn h Set.univ) (hk : k < 1)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hrel : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Work.MRMT.dzbar h z = μ z * Work.MRMT.dz h z)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ C / ‖z‖) :
    h = 0 := by
  have hk0 : 0 ≤ k := by
    have h1 := (MeasureTheory.ae_iff (p := fun z => ‖μ z‖ ≤ k) (μ := (volume : Measure ℂ))).mp hb
    by_contra hc
    push_neg at hc
    have h2 : {z : ℂ | ¬ ‖μ z‖ ≤ k} = Set.univ := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact fun hle => absurd hle (not_le.mpr (lt_of_lt_of_le hc (norm_nonneg _)))
    rw [h2] at h1
    simpa using h1
  obtain ⟨hl2, hgz, hgzbar, hdzl, hdbl, hgzl, hgzbl, hgzae, hgzbar_ae⟩ := hW
  have hdz : Work.MRMT.IsDzDeriv h hgz := by
    obtain ⟨a, b, c⟩ := hdzl
    refine ⟨?_, ?_, fun φ => c φ (Set.subset_univ _)⟩
    · exact (locallyIntegrableOn_univ).mp a
    · exact (locallyIntegrableOn_univ).mp b
  have hdb : Work.MRMT.IsDbarDeriv h hgzbar := by
    obtain ⟨a, b, c⟩ := hdbl
    refine ⟨?_, ?_, fun φ => c φ (Set.subset_univ _)⟩
    · exact (locallyIntegrableOn_univ).mp a
    · exact (locallyIntegrableOn_univ).mp b
  have hrel' : hgzbar =ᵐ[(volume : Measure ℂ)] (fun z => μ z * hgz z) := by
    filter_upwards [hgzae, hgzbar_ae, hrel] with z h1 h2 h3
    rw [h2, h3, ← h1]
  obtain ⟨M, hM⟩ := chiC_fderiv_bound
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  obtain ⟨C, R, hdecC⟩ := hdec
  have hC0 : 0 ≤ C := by
    have hge : R ≤ ‖(((max R 1 + 1 : ℝ) : ℂ))‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [le_max_left R 1]
    have h1 := hdecC _ hge
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have h2 : 0 ≤ C / (max R 1 + 1) := le_trans (norm_nonneg _) h1
    have hden : (0:ℝ) < max R 1 + 1 := by linarith [le_max_right R 1]
    have h3 : 0 ≤ C / (max R 1 + 1) * (max R 1 + 1) := mul_nonneg h2 hden.le
    rwa [div_mul_cancel₀ C hden.ne'] at h3
  have hAESMh : AEStronglyMeasurable h (volume : Measure ℂ) := hf.aestronglyMeasurable
  have hAESMgz : AEStronglyMeasurable hgz (volume : Measure ℂ) := hdz.2.1.aestronglyMeasurable
  have hAESMgzb : AEStronglyMeasurable hgzbar (volume : Measure ℂ) := hdb.2.1.aestronglyMeasurable
  have hstep : ∀ n : ℕ, ∫ z in Metric.ball 0 (Rn n), ‖hgz z‖^2 ≤
      (∫ z, (eC h k n z)^2) / (1 - k)^2 := by
    intro n
    obtain ⟨hpz, hpb⟩ := isDzDeriv_mul_and_isDbarDeriv_mul_of_contDiff_infty
      (ψ := psiC n) (psiC_contDiff n) (psiC_cs n) hdz hdb
    have hpn : MemLp (pC h hgz n) 2 (volume : Measure ℂ) := memLp_pC hAESMh hAESMgz hgzl hl2 hM
    have hqn : MemLp (qC h hgzbar n) 2 (volume : Measure ℂ) :=
      memLp_qC hAESMh hAESMgzb hgzbl hl2 hM
    have hen : MemLp (eC h k n) 2 (volume : Measure ℂ) := memLp_eC hk0 hM0 hM hAESMh hl2
    have henn : ∀ᵐ z ∂(volume : Measure ℂ), 0 ≤ eC h k n z :=
      Eventually.of_forall (fun z => by unfold eC; positivity)
    have hpint : Integrable (fun z => ‖pC h hgz n z‖^2) (volume : Measure ℂ) :=
      (MeasureTheory.memLp_two_iff_integrable_sq_norm (aesm_pC hAESMh hAESMgz)).mp hpn
    have hbd : ∀ᵐ z ∂(volume : Measure ℂ),
        ‖qC h hgzbar n z‖ ≤ k * ‖pC h hgz n z‖ + eC h k n z := by
      filter_upwards [hrel', hb] with z h1 h2
      have h3 : qC h hgzbar n z = μ z * pC h hgz n z +
          h z * (Work.MRMT.dzbar (psiC n) z - μ z * Work.MRMT.dz (psiC n) z) := by
        unfold qC pC; rw [h1]; ring
      rw [h3]
      have h4 : ‖Work.MRMT.dzbar (psiC n) z - μ z * Work.MRMT.dz (psiC n) z‖
          ≤ ‖Work.MRMT.dzbar (psiC n) z‖ + k * ‖Work.MRMT.dz (psiC n) z‖ := by
        calc ‖Work.MRMT.dzbar (psiC n) z - μ z * Work.MRMT.dz (psiC n) z‖
            ≤ ‖Work.MRMT.dzbar (psiC n) z‖ + ‖μ z * Work.MRMT.dz (psiC n) z‖ := norm_sub_le _ _
          _ = ‖Work.MRMT.dzbar (psiC n) z‖ + ‖μ z‖ * ‖Work.MRMT.dz (psiC n) z‖ := by rw [norm_mul]
          _ ≤ ‖Work.MRMT.dzbar (psiC n) z‖ + k * ‖Work.MRMT.dz (psiC n) z‖ :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      calc ‖μ z * pC h hgz n z +
              h z * (Work.MRMT.dzbar (psiC n) z - μ z * Work.MRMT.dz (psiC n) z)‖
          ≤ ‖μ z * pC h hgz n z‖
              + ‖h z * (Work.MRMT.dzbar (psiC n) z - μ z * Work.MRMT.dz (psiC n) z)‖ :=
            norm_add_le _ _
        _ = ‖μ z‖ * ‖pC h hgz n z‖
              + ‖h z‖ * ‖Work.MRMT.dzbar (psiC n) z - μ z * Work.MRMT.dz (psiC n) z‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ k * ‖pC h hgz n z‖ + ‖h z‖ *
              (‖Work.MRMT.dzbar (psiC n) z‖ + k * ‖Work.MRMT.dz (psiC n) z‖) :=
            add_le_add (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
        _ = k * ‖pC h hgz n z‖ + eC h k n z := rfl
    have henergy : ∫ z, ‖pC h hgz n z‖^2 = ∫ z, ‖qC h hgzbar n z‖^2 :=
      integral_norm_dz_eq_integral_norm_dzbar
        (hus := (psiC_cs n).mul_right (f' := h)) hpz hpb hpn hqn
    have hbound := l2_bound_of_energy hk0 hk hpn hqn hen henn henergy hbd
    calc ∫ z in Metric.ball 0 (Rn n), ‖hgz z‖^2
        = ∫ z in Metric.ball 0 (Rn n), ‖pC h hgz n z‖^2 := by
          refine setIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
          rw [Metric.mem_ball, dist_zero_right] at hz
          unfold pC
          rw [psiC_one n z (le_of_lt hz), psiC_dz_zero n z hz]
          simp
      _ ≤ ∫ z, ‖pC h hgz n z‖^2 :=
          setIntegral_le_integral hpint (Eventually.of_forall fun z => sq_nonneg _)
      _ ≤ (∫ z, (eC h k n z)^2) / (1 - k)^2 := hbound
  have hest : Tendsto (fun n : ℕ => (∫ z, (eC h k n z)^2)) atTop (𝓝 0) :=
    tendsto_integral_eC_sq hf hk0 hC0 hdecC
  have hlim : ∀ m : ℕ, ∫ z in Metric.ball 0 (Rn m), ‖hgz z‖^2 ≤ 0 := by
    intro m
    have h1 : Tendsto (fun n : ℕ => (∫ z, (eC h k n z)^2) / (1 - k)^2) atTop (𝓝 0) := by
      simpa using hest.div_const ((1 - k)^2)
    refine ge_of_tendsto h1 ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    calc ∫ z in Metric.ball 0 (Rn m), ‖hgz z‖^2
        ≤ ∫ z in Metric.ball 0 (Rn n), ‖hgz z‖^2 := by
          refine setIntegral_mono_set
            ((memL2Loc_integrableOn hgzl (isCompact_closedBall 0 (Rn n))).mono_set
              Metric.ball_subset_closedBall)
            (Eventually.of_forall fun z => sq_nonneg _)
            (Eventually.of_forall fun z hz => ?_)
          simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
          have h2 : Rn m ≤ Rn n := by
            have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
            unfold Rn; linarith
          linarith
      _ ≤ (∫ z, (eC h k n z)^2) / (1 - k)^2 := hstep n
  have hgz_ae : hgz =ᵐ[(volume : Measure ℂ)] (fun _ => (0 : ℂ)) := by
    have hnull : ∀ m : ℕ,
        (volume : Measure ℂ) (Metric.ball 0 (Rn m) ∩ {z : ℂ | hgz z ≠ 0}) = 0 := by
      intro m
      have h1 : ∫ z in Metric.ball 0 (Rn m), ‖hgz z‖^2 = 0 :=
        le_antisymm (hlim m) (integral_nonneg fun z => sq_nonneg _)
      have h2 : IntegrableOn (fun z => ‖hgz z‖^2) (Metric.ball 0 (Rn m)) volume :=
        (memL2Loc_integrableOn hgzl (isCompact_closedBall 0 (Rn m))).mono_set
          Metric.ball_subset_closedBall
      have h3 := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun z => sq_nonneg _) h2).mp h1
      have h5 := (MeasureTheory.ae_iff
        (p := fun z => z ∈ Metric.ball 0 (Rn m) → ‖hgz z‖^2 = 0) (μ := volume)).mp
        ((MeasureTheory.ae_restrict_iff' measurableSet_ball).mp h3)
      have hset : Metric.ball 0 (Rn m) ∩ {z : ℂ | hgz z ≠ 0}
          = {z : ℂ | ¬ (z ∈ Metric.ball 0 (Rn m) → ‖hgz z‖^2 = 0)} := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, not_imp]
        constructor
        · rintro ⟨hz, hz'⟩
          exact ⟨hz, fun h0 => hz' (by simpa [pow_two, mul_self_eq_zero, norm_eq_zero] using h0)⟩
        · rintro ⟨hz, hz'⟩
          exact ⟨hz, fun h0 => hz' (by rw [h0]; simp)⟩
      rw [hset]; exact h5
    change ∀ᵐ z ∂(volume : Measure ℂ), hgz z = 0
    rw [MeasureTheory.ae_iff]
    have hcover : {z : ℂ | ¬ hgz z = 0}
        = ⋃ m, (Metric.ball 0 (Rn m) ∩ {z : ℂ | hgz z ≠ 0}) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hz
        obtain ⟨m, hm⟩ := exists_nat_gt ‖z‖
        refine ⟨m, ?_, hz⟩
        rw [Metric.mem_ball, dist_zero_right]
        have h2 : (m : ℝ) ≤ Rn m := by unfold Rn; push_cast; linarith
        linarith
      · rintro ⟨m, _, hz⟩; exact hz
    rw [hcover]
    exact MeasureTheory.measure_iUnion_null hnull
  have hgzbar_ae0 : hgzbar =ᵐ[(volume : Measure ℂ)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hrel', hgz_ae] with z h1 h2
    rw [h2] at h1
    simpa using h1
  have hdb0 : Work.MRMT.IsDbarDeriv h (fun _ => 0) := by
    refine ⟨hdb.1, MeasureTheory.locallyIntegrable_zero, fun φ => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hdb.2.2 φ
    refine ⟨h1, by simp, ?_⟩
    have h4 : ∫ z, hgzbar z * (φ : ℂ → ℂ) z = 0 := by
      have he : (fun z => hgzbar z * (φ : ℂ → ℂ) z)
          =ᵐ[(volume : Measure ℂ)] (fun _ => (0 : ℂ)) := by
        filter_upwards [hgzbar_ae0] with z hz
        rw [hz]; simp
      rw [integral_congr_ae he]; simp
    rw [h3, h4]; simp
  have hdbOn : Work.MRMT.IsDbarDerivOn h (fun _ => 0) Set.univ := by
    obtain ⟨a, b, c⟩ := hdb0
    refine ⟨?_, ?_, fun φ _ => c φ⟩
    · exact (locallyIntegrableOn_univ).mpr a
    · exact MeasureTheory.locallyIntegrable_zero.locallyIntegrableOn Set.univ
  have hdiff : Differentiable ℂ h := by
    have := differentiableOn_of_isDbarDerivOn_zero isOpen_univ hf.continuousOn hdbOn
    rwa [differentiableOn_univ] at this
  have htend : Tendsto h (cocompact ℂ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.hasBasis_cocompact.eventually_iff]
    refine ⟨Metric.closedBall 0 (max R (C / ε) + 1), isCompact_closedBall _ _, ?_⟩
    intro z hz
    have hz_gt : max R (C / ε) + 1 < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hzpos : 0 < ‖z‖ := by
      linarith [hε, div_nonneg hC0 hε.le, le_max_right R (C / ε)]
    rw [dist_zero_right]
    calc ‖h z‖ ≤ C / ‖z‖ := hdecC z (by linarith [le_max_left R (C / ε)])
      _ < ε := by
          rw [div_lt_iff₀ hzpos]
          have := (div_lt_iff₀ hε).mp (by linarith [le_max_right R (C / ε)] : C / ε < ‖z‖)
          linarith
  exact funext fun z => hdiff.apply_eq_of_tendsto_cocompact z htend

end Work.MRMT.QC
