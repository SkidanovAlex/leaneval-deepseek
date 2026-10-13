/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/DiffAux/JepsSubPointwise.lean`

The pointwise half of the mollifier-approximation estimate

  `|J_ε f - f|_{ℋ^k} ≤ C ε |f|_{ℋ^{k+1}}`.

The difference `J_ε g - g` is the average over the shift parameter `p` of the *increment*
`g(shift p) - g`, which by the fundamental theorem of calculus along the log-coordinate shift path
`t ↦ (z e^{-t p₁}, arctan (tan θ e^{-t p₂}))` is the `t`-integral of the directional derivative
`-(p₁ D_z g + (p₂/2) D_θ g)`.  Cauchy–Schwarz in the probability density `Jker ρ ε` then gives

  `(W z θ · (J_ε g - g)(z,θ))²
     ≤ 2 ε² e^{4cε} ∫_p Jker ρ ε p ∫_0^1 bracket g W z θ p t dt dp`,

where `bracket g W z θ p t = (W(s) D_z g(s))² + (1/4) (W(s) D_θ g(s))²` at the shifted point `s`,
and `W` is a weight with shift ratio `≤ e^{c(|p₁|+|p₂|)}`.  The factor `ε²` comes from
`|p₁|, |p₂| ≤ ε` on the support of the kernel and from `|t| ≤ 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le
import Submission.Work.FTS.StrongEps.DiffAux.Defs
import Submission.Work.FTS.StrongEps.DiffAux.shiftPath_sub
import Submission.Work.FTS.StrongEps.DiffAux.Jeps_sub_eq_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

open Work.FTS.StrongEps (Quad zShift thShift Jker Jeps)

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {g W : ℝ → ℝ → ℝ}

/-! ## The shift path -/

/-- The point reached from `(z,θ)` after the fraction `t` of the log-coordinate shift by `p`:
`(z e^{-t p₁}, arctan (tan θ e^{-t p₂}))`. -/
def shiftPt (z θ : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (zShift z (t * p.1), thShift θ (t * p.2))

theorem shiftPt_mem_Quad {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ)
    (t : ℝ) : shiftPt z θ p t ∈ Quad :=
  ⟨zShift_pos hz, thShift_mem hθ⟩

theorem continuous_shiftPt (z θ : ℝ) :
    Continuous fun q : (ℝ × ℝ) × ℝ => shiftPt z θ q.1 q.2 := by
  refine Continuous.prodMk ?_ ?_
  · show Continuous fun q : (ℝ × ℝ) × ℝ => z * Real.exp (-(q.2 * q.1.1))
    fun_prop
  · show Continuous fun q : (ℝ × ℝ) × ℝ =>
      Real.arctan (Real.tan θ * Real.exp (-(q.2 * q.1.2)))
    fun_prop

theorem continuous_shiftPt_slice (z θ : ℝ) (p : ℝ × ℝ) :
    Continuous fun t : ℝ => shiftPt z θ p t := by
  refine Continuous.prodMk ?_ ?_
  · show Continuous fun t : ℝ => z * Real.exp (-(t * p.1))
    fun_prop
  · show Continuous fun t : ℝ => Real.arctan (Real.tan θ * Real.exp (-(t * p.2)))
    fun_prop

/-- The composed slice `t ↦ A (shiftPt z θ p t)` is continuous for `A` continuous on `Quad`. -/
theorem continuous_shiftPt_comp {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) :
    Continuous fun t : ℝ => A (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
  hA.comp_continuous (continuous_shiftPt_slice z θ p) (fun t => shiftPt_mem_Quad hz hθ p t)

/-- The composed function `(p,t) ↦ A (shiftPt z θ p t)` is continuous for `A` continuous on
`Quad`. -/
theorem continuous_shiftPt_comp_joint {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Continuous fun q : (ℝ × ℝ) × ℝ =>
      A (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
  hA.comp_continuous (continuous_shiftPt z θ) (fun q => shiftPt_mem_Quad hz hθ q.1 q.2)

/-! ## The two integrands -/

/-- The directional derivative of the shift path: `-(p₁ D_z g + (p₂/2) D_θ g)`. -/
def pathDeriv (g : ℝ → ℝ → ℝ) (z θ : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℝ :=
  -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
    + p.2 / 2 * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)))

/-- The bracket of the difference estimate at the shifted point. -/
def bracket (g W : ℝ → ℝ → ℝ) (z θ : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℝ :=
  (W (zShift z (t * p.1)) (thShift θ (t * p.2))
      * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2
    + 1 / 4 * (W (zShift z (t * p.1)) (thShift θ (t * p.2))
      * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2

theorem bracket_nonneg (g W : ℝ → ℝ → ℝ) (z θ : ℝ) (p : ℝ × ℝ) (t : ℝ) :
    0 ≤ bracket g W z θ p t := by
  rw [bracket]; positivity

theorem continuous_pathDeriv_joint {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) :
    Continuous fun q : (ℝ × ℝ) × ℝ => pathDeriv g z θ q.1 q.2 := by
  have h1 : Continuous fun q : (ℝ × ℝ) × ℝ =>
      Work.Spaces.Dz g (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
    continuous_shiftPt_comp_joint hDz hz hθ
  have h2 : Continuous fun q : (ℝ × ℝ) × ℝ =>
      Work.Spaces.Dth g (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
    continuous_shiftPt_comp_joint hDth hz hθ
  have h3 : Continuous fun q : (ℝ × ℝ) × ℝ =>
      q.1.1 * Work.Spaces.Dz g (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
    continuous_fst.fst.mul h1
  have h4 : Continuous fun q : (ℝ × ℝ) × ℝ =>
      q.1.2 / 2 * Work.Spaces.Dth g (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
    (continuous_fst.snd.div_const 2).mul h2
  exact (h3.add h4).neg

theorem continuous_pathDeriv_slice {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) (p : ℝ × ℝ) :
    Continuous fun t : ℝ => pathDeriv g z θ p t := by
  have h1 : Continuous fun t : ℝ =>
      Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
    continuous_shiftPt_comp hDz hz hθ p
  have h2 : Continuous fun t : ℝ =>
      Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
    continuous_shiftPt_comp hDth hz hθ p
  have h3 : Continuous fun t : ℝ =>
      p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
    continuous_const.mul h1
  have h4 : Continuous fun t : ℝ =>
      p.2 / 2 * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
    (continuous_const.div_const 2).mul h2
  exact (h3.add h4).neg

theorem continuous_bracket_slice {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) (p : ℝ × ℝ) :
    Continuous fun t : ℝ => bracket g W z θ p t := by
  have h1 := continuous_shiftPt_comp (A := fun u v => W u v * Work.Spaces.Dz g u v)
    (hWc.mul hDz) hz hθ p
  have h2 := continuous_shiftPt_comp (A := fun u v => W u v * Work.Spaces.Dth g u v)
    (hWc.mul hDth) hz hθ p
  have h := (h1.pow 2).add
    ((continuous_const : Continuous fun _ : ℝ => (1 / 4 : ℝ)).mul (h2.pow 2))
  refine h.congr fun t => ?_
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, bracket]

theorem continuous_bracket_joint {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) :
    Continuous fun q : (ℝ × ℝ) × ℝ => bracket g W z θ q.1 q.2 := by
  have h1 := continuous_shiftPt_comp_joint (A := fun u v => W u v * Work.Spaces.Dz g u v)
    (hWc.mul hDz) hz hθ
  have h2 := continuous_shiftPt_comp_joint (A := fun u v => W u v * Work.Spaces.Dth g u v)
    (hWc.mul hDth) hz hθ
  have h := (h1.pow 2).add
    ((continuous_const : Continuous fun _ : (ℝ × ℝ) × ℝ => (1 / 4 : ℝ)).mul (h2.pow 2))
  refine h.congr fun q => ?_
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, bracket]

/-! ## Cauchy–Schwarz for the unit interval -/

theorem sq_intervalIntegral_le {X : ℝ → ℝ} (hX : ContinuousOn X (Set.Icc 0 1)) :
    (∫ t in (0 : ℝ)..1, X t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (X t) ^ 2 := by
  set m : ℝ := ∫ t in (0 : ℝ)..1, X t with hm
  have hX' : ContinuousOn X (Set.uIcc (0 : ℝ) 1) := by
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hXint : IntervalIntegrable X volume 0 1 := hX'.intervalIntegrable
  have hX2' : ContinuousOn (fun t => X t ^ 2) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hX.pow 2
  have hX2int : IntervalIntegrable (fun t => X t ^ 2) volume 0 1 := hX2'.intervalIntegrable
  have h2m : IntervalIntegrable (fun t => 2 * m * X t) volume 0 1 := hXint.const_mul (2 * m)
  have hconst : IntervalIntegrable (fun _ : ℝ => m ^ 2) volume 0 1 := intervalIntegrable_const
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, (X t - m) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
  have hcongr : (∫ t in (0 : ℝ)..1, (X t - m) ^ 2)
      = ∫ t in (0 : ℝ)..1, (X t ^ 2 - 2 * m * X t + m ^ 2) :=
    intervalIntegral.integral_congr (fun t _ => by ring)
  have hcalc : (∫ t in (0 : ℝ)..1, (X t ^ 2 - 2 * m * X t + m ^ 2))
      = (∫ t in (0 : ℝ)..1, X t ^ 2) - m ^ 2 := by
    rw [intervalIntegral.integral_add (hX2int.sub h2m) hconst,
      intervalIntegral.integral_sub hX2int h2m,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hm]
    simp only [smul_eq_mul]
    ring
  linarith [hnn, hcongr, hcalc]

/-! ## Continuity of the parametric integrals -/

/-- **Continuity of the parametric interval integral on a ball.**  If `F` is jointly continuous and
bounded by `C` on `closedBall 0 ε × [0,1]`, then `p ↦ ∫_0^1 F p t dt` is continuous on that
ball. -/
theorem continuous_integral_pathDeriv {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) :
    Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t := by
  have hcont := continuous_pathDeriv_joint hz hθ hDz hDth
  have h1 : Continuous fun p : ℝ × ℝ => ∫ t in Set.Icc (0 : ℝ) 1, pathDeriv g z θ p t :=
    continuous_parametric_integral_of_continuous (μ := volume) hcont isCompact_Icc
  refine h1.congr fun p => ?_
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact (MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := 1))).symm

theorem continuous_integral_bracket {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) :
    Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
  have hcont := continuous_bracket_joint hz hθ hWc hDz hDth
  have h1 : Continuous fun p : ℝ × ℝ => ∫ t in Set.Icc (0 : ℝ) 1, bracket g W z θ p t :=
    continuous_parametric_integral_of_continuous (μ := volume) hcont isCompact_Icc
  refine h1.congr fun p => ?_
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact (MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := 1))).symm

/-! ## The pointwise estimate -/

theorem Jeps_sub_sq_le (hρ : IsMollKernel ρ) (hε : 0 < ε) {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad)
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWnn : 0 ≤ W z θ)
    (hW : ∀ q : ℝ × ℝ, W z θ ≤ Real.exp (c * (|q.1| + |q.2|))
      * W (zShift z q.1) (thShift θ q.2)) :
    (W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2
      ≤ 2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ p : ℝ × ℝ, Jker ρ ε p
          * ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
  have hAcont : Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t :=
    continuous_integral_pathDeriv hz hθ hDz hDth
  have hbcont : Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, bracket g W z θ p t :=
    continuous_integral_bracket hz hθ hWc hDz hDth
  -- the mass-one identity and the fundamental theorem of calculus
  have hsub := Jeps_sub_eq_integral ρ hρ hε (hg 0).continuousOn hz hθ
  have hWsub : W z θ * (Jeps ρ ε g z θ - g z θ)
      = ∫ p : ℝ × ℝ, Jker ρ ε p
          * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) := by
    rw [hsub, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    show W z θ * (Jker ρ ε p * (g (zShift z p.1) (thShift θ p.2) - g z θ))
      = Jker ρ ε p * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t)
    rw [shiftPath_sub hg hz hθ p]
    rw [show (∫ t in (0 : ℝ)..1,
          (-(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
            + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)))))
        = ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t from by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [pathDeriv]]
    ring
  -- Cauchy–Schwarz in the kernel
  have hCS := Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le ρ hρ hε
    (fun p : ℝ × ℝ => W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t)
    ((hAcont.const_mul (W z θ)).continuousOn)
  -- the pointwise bound in `p`
  have hpoint : ∀ p : ℝ × ℝ, Jker ρ ε p
        * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2
      ≤ Jker ρ ε p * (2 * ε ^ 2 * Real.exp (4 * c * ε)
          * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) := by
    intro p
    by_cases hp : Jker ρ ε p = 0
    · rw [hp, zero_mul, zero_mul]
    · have hb := Jker_ne_zero_support hρ hε hp
      have hp1 : |p.1| ≤ ε := by
        have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
        rw [sq_le_sq] at h1
        rwa [abs_of_nonneg hε.le] at h1
      have hp2 : |p.2| ≤ ε := by
        have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
        rw [sq_le_sq] at h2
        rwa [abs_of_nonneg hε.le] at h2
      have htcs := sq_intervalIntegral_le (continuous_pathDeriv_slice hz hθ hDz hDth p).continuousOn
      have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          (W z θ) ^ 2 * (pathDeriv g z θ p t) ^ 2
            ≤ 2 * ε ^ 2 * Real.exp (4 * c * ε) * bracket g W z θ p t := by
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have htabs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
        have hWsn : 0 ≤ W (zShift z (t * p.1)) (thShift θ (t * p.2)) := by
          have hsh := hW (t * p.1, t * p.2)
          have hpos : 0 < Real.exp (c * (|t * p.1| + |t * p.2|)) := Real.exp_pos _
          nlinarith [hsh, hWnn, hpos]
        have hexp : Real.exp (c * (|t * p.1| + |t * p.2|)) ≤ Real.exp (2 * c * ε) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : |t * p.1| ≤ ε := by
            rw [abs_mul]
            exact (mul_le_mul htabs hp1 (abs_nonneg _) (by norm_num)).trans_eq (one_mul ε)
          have h2 : |t * p.2| ≤ ε := by
            rw [abs_mul]
            exact (mul_le_mul htabs hp2 (abs_nonneg _) (by norm_num)).trans_eq (one_mul ε)
          nlinarith
        have hWsq : (W z θ) ^ 2 ≤ Real.exp (4 * c * ε)
            * (W (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2 := by
          have h1 : W z θ ≤ Real.exp (2 * c * ε)
              * W (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
            (hW (t * p.1, t * p.2)).trans
              (mul_le_mul_of_nonneg_right hexp hWsn)
          have h2 := pow_le_pow_left₀ hWnn h1 2
          rw [mul_pow] at h2
          have hexp4 : Real.exp (2 * c * ε) ^ 2 = Real.exp (4 * c * ε) := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          rwa [hexp4] at h2
        have hpd : (pathDeriv g z θ p t) ^ 2 ≤ 2 * ε ^ 2
            * ((Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2
              + 1 / 4 * (Work.Spaces.Dth g (zShift z (t * p.1))
                  (thShift θ (t * p.2))) ^ 2) := by
          set X := Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2)) with hX
          set Y := Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) with hY
          have h1 : (p.1 * X + p.2 / 2 * Y) ^ 2 ≤ 2 * p.1 ^ 2 * X ^ 2
              + 2 * (p.2 / 2) ^ 2 * Y ^ 2 := by
            nlinarith [sq_nonneg (p.1 * X - p.2 / 2 * Y)]
          have h2 : p.1 ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hp1 2
          have h3 : p.2 ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hp2 2
          have h4 : 2 * p.1 ^ 2 * X ^ 2 + 2 * (p.2 / 2) ^ 2 * Y ^ 2
              ≤ 2 * ε ^ 2 * (X ^ 2 + 1 / 4 * Y ^ 2) := by
            nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg ε]
          rw [pathDeriv]
          calc (-(p.1 * X + p.2 / 2 * Y)) ^ 2 = (p.1 * X + p.2 / 2 * Y) ^ 2 := by ring
            _ ≤ 2 * p.1 ^ 2 * X ^ 2 + 2 * (p.2 / 2) ^ 2 * Y ^ 2 := h1
            _ ≤ 2 * ε ^ 2 * (X ^ 2 + 1 / 4 * Y ^ 2) := h4
        calc (W z θ) ^ 2 * (pathDeriv g z θ p t) ^ 2
            ≤ (Real.exp (4 * c * ε) * (W (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2)
              * (2 * ε ^ 2 * ((Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2
                + 1 / 4 * (Work.Spaces.Dth g (zShift z (t * p.1))
                    (thShift θ (t * p.2))) ^ 2)) :=
              mul_le_mul hWsq hpd (sq_nonneg _) (by positivity)
            _ = 2 * ε ^ 2 * Real.exp (4 * c * ε) * bracket g W z θ p t := by
              rw [bracket]; ring
      have hWnnsq : (0 : ℝ) ≤ (W z θ) ^ 2 := sq_nonneg _
      have hmain : (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2
          ≤ 2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
       calc (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2
          = (W z θ) ^ 2 * (∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2 := by ring
        _ ≤ (W z θ) ^ 2 * ∫ t in (0 : ℝ)..1, (pathDeriv g z θ p t) ^ 2 :=
            mul_le_mul_of_nonneg_left htcs hWnnsq
        _ = ∫ t in (0 : ℝ)..1, (W z θ) ^ 2 * (pathDeriv g z θ p t) ^ 2 := by
            rw [intervalIntegral.integral_const_mul]
        _ ≤ ∫ t in (0 : ℝ)..1, 2 * ε ^ 2 * Real.exp (4 * c * ε) * bracket g W z θ p t := by
            rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
              intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
            refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc
              (fun t ht => hpt t (Set.Ioc_subset_Icc_self ht))
            · exact (((continuous_pathDeriv_slice hz hθ hDz hDth p).pow 2).continuousOn
                |>.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self |>.const_mul _
            · exact (((continuous_bracket_slice hz hθ hWc hDz hDth p).continuousOn
                |>.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
                |>.const_mul _)
        _ = 2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
            rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hmain (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p)
  -- the two integrals are integrable
  have hint1 : Integrable (fun p : ℝ × ℝ => Jker ρ ε p
      * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2) :=
    Work.FTS.StrongEps.HkSqAux.integrable_Jker_mul ρ hρ hε
      (((hAcont.const_mul (W z θ)).continuousOn).pow 2)
  have hint2 : Integrable (fun p : ℝ × ℝ => Jker ρ ε p
      * (2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ t in (0 : ℝ)..1, bracket g W z θ p t)) :=
    Work.FTS.StrongEps.HkSqAux.integrable_Jker_mul ρ hρ hε (hbcont.const_mul _).continuousOn
  calc (W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2
      = (∫ p : ℝ × ℝ, Jker ρ ε p
          * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t)) ^ 2 := by rw [hWsub]
    _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p
          * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2 := hCS
    _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p
          * (2 * ε ^ 2 * Real.exp (4 * c * ε)
            * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) :=
        MeasureTheory.integral_mono hint1 hint2 hpoint
    _ = 2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ p : ℝ × ℝ, Jker ρ ε p
          * ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring

/-! ## The `ℝ≥0∞` form -/

theorem ofReal_intervalIntegral {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hnn : ∀ t, 0 ≤ f t) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, f t)
      = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (f t) := by
  have hint : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume := hf.integrableOn_compact isCompact_Icc
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (hint.mono_set Set.Ioc_subset_Icc_self) (Eventually.of_forall hnn)]
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := 1))]

/-- **The `ℝ≥0∞` pointwise bound.** -/
theorem ofReal_Jeps_sub_sq_le (hρ : IsMollKernel ρ) (hε : 0 < ε) {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad)
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hWnn : 0 ≤ W z θ)
    (hW : ∀ q : ℝ × ℝ, W z θ ≤ Real.exp (c * (|q.1| + |q.2|))
      * W (zShift z q.1) (thShift θ q.2)) :
    ENNReal.ofReal ((W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2)
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bracket g W z θ p t) := by
  have hreal := Jeps_sub_sq_le hρ hε hc hg hWc hDz hDth hz hθ hWnn hW
  have hbcont : Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, bracket g W z θ p t :=
    continuous_integral_bracket hz hθ hWc hDz hDth
  have hint : Integrable (fun p : ℝ × ℝ => Jker ρ ε p
      * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) :=
    Work.FTS.StrongEps.HkSqAux.integrable_Jker_mul ρ hρ hε hbcont.continuousOn
  have hnnG : ∀ p : ℝ × ℝ, 0 ≤ ∫ t in (0 : ℝ)..1, bracket g W z θ p t := fun p =>
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => bracket_nonneg g W z θ p t)
  have hconv : ENNReal.ofReal (∫ p : ℝ × ℝ, Jker ρ ε p
        * ∫ t in (0 : ℝ)..1, bracket g W z θ p t)
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
          * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bracket g W z θ p t) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun p =>
        mul_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p) (hnnG p))]
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_mul (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p)]
    congr 1
    exact ofReal_intervalIntegral ((continuous_bracket_slice hz hθ hWc hDz hDth p).continuousOn)
      (fun t => bracket_nonneg g W z θ p t)
  calc ENNReal.ofReal ((W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2)
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε)
          * ∫ p : ℝ × ℝ, Jker ρ ε p * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * ENNReal.ofReal (∫ p : ℝ × ℝ, Jker ρ ε p
              * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
              * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bracket g W z θ p t)) := by
        rw [hconv]

end Work.FTS.StrongEps.DiffAux
