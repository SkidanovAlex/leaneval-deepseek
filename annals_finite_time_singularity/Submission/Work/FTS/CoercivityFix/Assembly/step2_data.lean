import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Step
import Submission.Work.FTS.CoercivityFix.StepCoer.step_coer
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge
import Submission.Work.FTS.CoercivityFix.Assembly.RegQ_dth_ge
import Submission.Work.FTS.CoercivityFix.Assembly.coer_clause_succ
import Submission.Work.FTS.CoercivityFix.Assembly.exists_not_normSub_lt
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-- **The one-sided norm comparison of the `D_z`-slot**: the squared `ℋⁿ`-norm of `D_z f`
is dominated by the squared `ℋ^{n+1}`-norm of `f`.  The pointwise comparison of the
integrands is `QuadPorts.HkIntegrand_Dz_le_succ` (the index shift `D_z^i(D_z f) = D_z^{i+1} f`,
`D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` — the same weight on both sides, so *no* hypothesis
on `α` is needed), and the transfer to the iterated integrals is the elementary monotonicity
of the integral in the integrand. -/
theorem HkSq_Dz_le_succ (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (n + 1) f z θ
  exact MeasureTheory.ae_restrict_of_forall_mem hmesz fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
      (h.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hmesθ fun θ hθ =>
        Work.FTS.CoercivityFix.QuadPorts.HkIntegrand_Dz_le_succ α n hsm z θ hz hθ)

/-- **The Cauchy–Schwarz clause of the step, at level `n+1`.**  From the level-`n`
Cauchy–Schwarz bound of `IP` and the three one-sided norm comparisons
(`HkNorm α n f ≤ HkNorm α (n+1) f`, `HkNorm α n (D_θ f) ≤ HkNorm α (n+1) f`,
`HkNorm α n (D_z f) ≤ HkNorm α (n+1) f`) one obtains the level-`(n+1)` bound for
`HkIPStep c₁ c₂ IP = IP + c₁ IP(D_θ·, D_θ·) + c₂ IP(D_z·, D_z·)`, with the constant
`3 * max 1 (max c₁ c₂) * CC`: three slots, each costing the factor `max 1 (max c₁ c₂)`.

The third comparison `HkNorm α n (D_z f) ≤ HkNorm α (n+1) f` is the index shift
`D_z^i(D_z f) = D_z^{i+1} f` (no hypothesis on `α`); the second is the same statement for
`D_θ`, which holds exactly in the range `α ≥ -1/10` (`HkSq_Dth_le_ge`).  `hregdth` is the
corresponding port of the regularity class, supplied by `RegQ_dth_ge`. -/
theorem cs_clause_succ (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) (n : ℕ)
    {IP : Fn → Fn → ℝ} {CC : ℝ}
    (hcs : ∀ f g : Fn, RegQ α n f → RegQ α n g →
      |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g)
    (hCC : 0 ≤ CC)
    (hregdth : ∀ f : Fn, RegQ α (n + 1) f → RegQ α n (Work.Spaces.Dth f))
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∀ f g : Fn, RegQ α (n + 1) f → RegQ α (n + 1) g →
      |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
        ≤ 3 * max 1 (max c₁ c₂) * CC * Work.Spaces.HkNorm α (n + 1) f
            * Work.Spaces.HkNorm α (n + 1) g := by
  intro f g hf hg
  -- the level-`n` memberships of the three slots
  have hfn : RegQ α n f := Work.FTS.GalerkinFix.RegQ.regQ_mono hf (Nat.le_succ n)
  have hgn : RegQ α n g := Work.FTS.GalerkinFix.RegQ.regQ_mono hg (Nat.le_succ n)
  have hdfn : RegQ α n (Work.Spaces.Dth f) := hregdth f hf
  have hdgn : RegQ α n (Work.Spaces.Dth g) := hregdth g hg
  have hdzn : RegQ α n (Work.Spaces.Dz f) := Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hf
  have hdzn' : RegQ α n (Work.Spaces.Dz g) := Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hg
  -- Cauchy–Schwarz at level `n`
  have e0 := hcs f g hfn hgn
  have e1 := hcs (Work.Spaces.Dth f) (Work.Spaces.Dth g) hdfn hdgn
  have e2 := hcs (Work.Spaces.Dz f) (Work.Spaces.Dz g) hdzn hdzn'
  have hfmem : Work.Spaces.HkMem α (n + 1) f := hf.2.1
  have hgmem : Work.Spaces.HkMem α (n + 1) g := hg.2.1
  -- the three one-sided norm comparisons
  have n0f : Work.Spaces.HkNorm α n f ≤ Work.Spaces.HkNorm α (n + 1) f :=
    Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hfmem)
  have n0g : Work.Spaces.HkNorm α n g ≤ Work.Spaces.HkNorm α (n + 1) g :=
    Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hgmem)
  have n1f : Work.Spaces.HkNorm α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkNorm α (n + 1) f :=
    Real.sqrt_le_sqrt (HkSq_Dth_le_ge α hα n hfmem)
  have n1g : Work.Spaces.HkNorm α n (Work.Spaces.Dth g) ≤ Work.Spaces.HkNorm α (n + 1) g :=
    Real.sqrt_le_sqrt (HkSq_Dth_le_ge α hα n hgmem)
  have n2f : Work.Spaces.HkNorm α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkNorm α (n + 1) f :=
    Real.sqrt_le_sqrt (HkSq_Dz_le_succ α n hf.1 hfmem)
  have n2g : Work.Spaces.HkNorm α n (Work.Spaces.Dz g) ≤ Work.Spaces.HkNorm α (n + 1) g :=
    Real.sqrt_le_sqrt (HkSq_Dz_le_succ α n hg.1 hgmem)
  have hF : 0 ≤ Work.Spaces.HkNorm α (n + 1) f := Real.sqrt_nonneg _
  have hG : 0 ≤ Work.Spaces.HkNorm α (n + 1) g := Real.sqrt_nonneg _
  have b0 : |IP f g|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := e0
      _ = CC * (Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n0f n0g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have b1 : |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth g) := e1
      _ = CC * (Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth g)) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n1f n1g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have b2 : |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz g) := e2
      _ = CC * (Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz g)) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n2f n2g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have key : |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
      ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := by
    have h1 : Work.Coercivity.HkIPStep c₁ c₂ IP f g
        = IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
          + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g) := rfl
    have main : |IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
          + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ |IP f g| + c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
          + c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := by
      have t1 := abs_add_le (IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
        (c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g))
      have t2 := abs_add_le (IP f g) (c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
      have E1 : |c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
          = c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)| := by
        rw [abs_mul, abs_of_pos hc₁]
      have E2 : |c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
          = c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := by
        rw [abs_mul, abs_of_pos hc₂]
      linarith
    have A1 := mul_le_mul_of_nonneg_left b1 hc₁.le
    have A2 := mul_le_mul_of_nonneg_left b2 hc₂.le
    rw [h1]
    calc |IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
            + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ |IP f g| + c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
            + c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := main
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
            + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
            + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f
                * Work.Spaces.HkNorm α (n + 1) g) := by linarith [b0, A1, A2]
  have hcoef : 1 + c₁ + c₂ ≤ 3 * max 1 (max c₁ c₂) := by
    have h1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
    have h2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hmax : 0 ≤ max 1 (max c₁ c₂) := le_trans zero_le_one (le_max_left _ _)
  have hpos : (0 : ℝ) ≤ 1 + c₁ + c₂ := by linarith
  have hfin : CC * (1 + c₁ + c₂) ≤ 3 * max 1 (max c₁ c₂) * CC := by
    nlinarith [hcoef, hCC, hmax, hpos]
  calc |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
      ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := key
    _ = (CC * (1 + c₁ + c₂))
          * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := by
        ring
    _ ≤ (3 * max 1 (max c₁ c₂) * CC)
          * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
        mul_le_mul_of_nonneg_right hfin (mul_nonneg hF hG)
    _ = 3 * max 1 (max c₁ c₂) * CC * Work.Spaces.HkNorm α (n + 1) f
          * Work.Spaces.HkNorm α (n + 1) g := by
        ring

/-- **`StepReg2 α n` is unsatisfiable for `α < -1/10`.**  Its `normSub` field would give
`HkSq α n (D_θ f) ≤ HkSq α (n+1) f` for every `f ∈ RegQ α (n+2)`, which is refuted by the
explicit family `f = z²e^{-z} · Λ((θ-θ₀)/δ)` of `exists_not_normSub_lt`. -/
theorem not_stepReg2_of_lt (α : ℝ) (hα : α < -(1 / 10 : ℝ)) (n : ℕ) :
    ¬ Work.FTS.CoercivityFix.Assembly.StepReg2 α n := by
  intro hr
  obtain ⟨f, hf, hlt⟩ := exists_not_normSub_lt α hα n
  exact absurd (hr.normSub f hf).2.1 (not_le.mpr hlt)

theorem step2_data (α : ℝ) (n : ℕ) {IP : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {cc CC κ c₁ c₂ D : ℝ}
    (hdata : Work.FTS.CoercivityFix.Assembly.CoerData2 α n IP cc CC)
    (hκ : 0 ≤ κ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hsmall : Work.FTS.CoercivityFix.StepSmall cc CC κ c₁ c₂)
    (hr : Work.FTS.CoercivityFix.Assembly.StepReg2 α n)
    (hc : Work.FTS.CoercivityFix.Assembly.Comm2 α n IP)
    (hE2 : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.RegQ α (n + 1) f →
      Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ κ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hnormD : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.RegQ α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ D * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f))) :
    Work.FTS.CoercivityFix.Assembly.CoerData2 α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP)
      (cc * min 1 (min c₁ c₂) / (2 * D)) (3 * max 1 (max c₁ c₂) * CC) := by
  by_cases hα : -(1 / 10 : ℝ) ≤ α
  · -- the honest range `α ≥ -1/10`: the `ℋⁿ`-norm comparison of the `D_θ`-slot is available
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the coercivity constant is positive
      have hmin : 0 < min 1 (min c₁ c₂) := lt_min one_pos (lt_min hc₁ hc₂)
      exact div_pos (mul_pos hdata.hcc hmin) (by positivity)
    · -- the Cauchy–Schwarz constant is positive
      exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_left _ _)))
        hdata.hCC
    · -- Cauchy–Schwarz: the three slots, each bounded through the level-`(n+1)` norm of `f`
      exact cs_clause_succ α hα n hdata.cs (le_of_lt hdata.hCC)
        (fun f hf => RegQ_dth_ge α hα hf) hc₁ hc₂
    · -- coercivity of `Lhat`: the paper's arithmetic, with the `RegQ`-ports of `hr`
      exact coer_clause_succ α n hdata hκ hc₁ hc₂ hD hsmall hr hc hE2 hnormD
  · -- `α < -1/10`: the hypothesis `hr` is contradictory (`StepReg2` fails there)
    exact absurd hr (not_stepReg2_of_lt α (not_le.mp hα) n)

end Work.FTS.CoercivityFix.Assembly
