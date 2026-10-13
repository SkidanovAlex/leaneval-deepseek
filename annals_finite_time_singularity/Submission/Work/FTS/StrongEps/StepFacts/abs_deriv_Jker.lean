import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# The two partial derivatives of the rescaled kernel `Jker ρ ε`

This file collects the elementary calculus of the kernel `Jker ρ ε p = ε⁻¹^2 • ρ (p/ε)`:

* the two scaling identities `∂₁ (Jker ρ ε) = ε⁻¹ • Jker (|∂₁ρ|) ε` (and likewise for `∂₂`),
  which express the fact that differentiating the rescaled kernel is the same as rescaling the
  kernel of the derivative (with the absolute value taken on the kernel side, since all the
  later estimates only ever see `|∂₁ρ|`);
* the continuity of the two partial derivatives of a smooth `ρ` (they are the Fréchet
  derivative applied to the two unit vectors `(1,0)`, `(0,1)`);
* the support of the two partial derivatives of `ρ`: since `ρ` is supported in the closed unit
  ball and is smooth, its partial derivatives vanish off that ball as well.

The proofs rest on the elementary slice-calculus of `ℝ × ℝ` (`deriv_slice_fst_eq`,
`deriv_slice_snd_eq`) and on the chain rule in one variable.
-/

/-! ## The slice calculus of `ℝ × ℝ` -/

/-- The derivative of the first-coordinate slice of a function on `ℝ × ℝ` is the Fréchet
derivative at the point, evaluated at the unit vector `(1, 0)`. -/
private lemma deriv_slice_fst_eq {f : ℝ × ℝ → ℝ} {x y : ℝ} (hf : DifferentiableAt ℝ f (x, y)) :
    deriv (fun s : ℝ => f (s, y)) x = fderiv ℝ f (x, y) (1, 0) := by
  have hγ : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) x := by
    simpa using (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y).hasDerivAt
  have h := hf.hasFDerivAt.comp_hasDerivAt x hγ
  simpa [Function.comp_def] using h.deriv

/-- The derivative of the second-coordinate slice of a function on `ℝ × ℝ` is the Fréchet
derivative at the point, evaluated at the unit vector `(0, 1)`. -/
private lemma deriv_slice_snd_eq {f : ℝ × ℝ → ℝ} {x y : ℝ} (hf : DifferentiableAt ℝ f (x, y)) :
    deriv (fun t : ℝ => f (x, t)) y = fderiv ℝ f (x, y) (0, 1) := by
  have hγ : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y := by
    simpa using (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y).hasDerivAt
  have h := hf.hasFDerivAt.comp_hasDerivAt y hγ
  simpa [Function.comp_def] using h.deriv

/-- The first-coordinate slice of a `C¹` function on `ℝ × ℝ` is `C¹`. -/
private lemma contDiff_slice_fst₁ {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (y : ℝ) :
    ContDiff ℝ 1 (fun x : ℝ => f (x, y)) :=
  hf.comp (contDiff_id.prodMk (contDiff_const (c := y)))

/-- The second-coordinate slice of a `C¹` function on `ℝ × ℝ` is `C¹`. -/
private lemma contDiff_slice_snd₁ {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => f (x, t)) :=
  hf.comp ((contDiff_const (c := x)).prodMk contDiff_id)

/-- For a `C¹` function on `ℝ × ℝ`, the pointwise first-coordinate slice derivative is
continuous. -/
private lemma continuous_deriv_slice_fst {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s : ℝ => f (s, p.2)) p.1) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ f p (1, 0)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h1.congr (fun p => (deriv_slice_fst_eq (x := p.1) (y := p.2)
    hf.differentiable_one.differentiableAt).symm)

/-- For a `C¹` function on `ℝ × ℝ`, the pointwise second-coordinate slice derivative is
continuous. -/
private lemma continuous_deriv_slice_snd {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × ℝ => deriv (fun t : ℝ => f (p.1, t)) p.2) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ f p (0, 1)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h1.congr (fun p => (deriv_slice_snd_eq (x := p.1) (y := p.2)
    hf.differentiable_one.differentiableAt).symm)

/-! ## The chain rule for the rescaled kernel -/

/-- **The first scaling identity, in non-absolute-value form**: differentiating
`ε⁻¹^2 * σ (ε⁻¹·, ε⁻¹ p₂)` in the first variable produces the extra factor `ε⁻¹`. -/
private lemma deriv_Jker_fst (σ : ℝ × ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (ε : ℝ) (p : ℝ × ℝ) :
    deriv (fun s : ℝ => ε⁻¹ ^ 2 * σ (ε⁻¹ * s, ε⁻¹ * p.2)) p.1
      = ε⁻¹ ^ 2 * (ε⁻¹ * deriv (fun u : ℝ => σ (u, ε⁻¹ * p.2)) (ε⁻¹ * p.1)) := by
  have hsm : ContDiff ℝ 1 (fun u : ℝ => σ (u, ε⁻¹ * p.2)) := contDiff_slice_fst₁ hσ _
  have houter : HasDerivAt (fun u : ℝ => σ (u, ε⁻¹ * p.2))
      (deriv (fun u : ℝ => σ (u, ε⁻¹ * p.2)) (ε⁻¹ * p.1)) (ε⁻¹ * p.1) :=
    hsm.differentiable_one.differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun s : ℝ => ε⁻¹ * s) ε⁻¹ p.1 := by
    simpa using (hasDerivAt_id p.1).const_mul ε⁻¹
  have hcomp : HasDerivAt (fun s : ℝ => σ (ε⁻¹ * s, ε⁻¹ * p.2))
      (deriv (fun u : ℝ => σ (u, ε⁻¹ * p.2)) (ε⁻¹ * p.1) * ε⁻¹) p.1 := by
    simpa [Function.comp_def] using houter.comp p.1 hinner
  rw [(hcomp.const_mul (ε⁻¹ ^ 2)).deriv]
  ring

/-- **The second scaling identity, in non-absolute-value form**. -/
private lemma deriv_Jker_snd (σ : ℝ × ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (ε : ℝ) (p : ℝ × ℝ) :
    deriv (fun t : ℝ => ε⁻¹ ^ 2 * σ (ε⁻¹ * p.1, ε⁻¹ * t)) p.2
      = ε⁻¹ ^ 2 * (ε⁻¹ * deriv (fun u : ℝ => σ (ε⁻¹ * p.1, u)) (ε⁻¹ * p.2)) := by
  have hsm : ContDiff ℝ 1 (fun u : ℝ => σ (ε⁻¹ * p.1, u)) := contDiff_slice_snd₁ hσ _
  have houter : HasDerivAt (fun u : ℝ => σ (ε⁻¹ * p.1, u))
      (deriv (fun u : ℝ => σ (ε⁻¹ * p.1, u)) (ε⁻¹ * p.2)) (ε⁻¹ * p.2) :=
    hsm.differentiable_one.differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun t : ℝ => ε⁻¹ * t) ε⁻¹ p.2 := by
    simpa using (hasDerivAt_id p.2).const_mul ε⁻¹
  have hcomp : HasDerivAt (fun t : ℝ => σ (ε⁻¹ * p.1, ε⁻¹ * t))
      (deriv (fun u : ℝ => σ (ε⁻¹ * p.1, u)) (ε⁻¹ * p.2) * ε⁻¹) p.2 := by
    simpa [Function.comp_def] using houter.comp p.2 hinner
  rw [(hcomp.const_mul (ε⁻¹ ^ 2)).deriv]
  ring

-- context: namespace Work.FTS.StrongEps.StepFacts. `Jker ρ ε p = ε⁻¹^2 * ρ (ε⁻¹ • p)`; `IsSmoothKernel ρ` = `∀n, ContDiff ℝ n ρ` plus continuous/supported-in-closed-unit-ball/nonneg/mass-one. The conclusion is a six-fold conjunction (scaling identities for the two partial derivatives, joint continuity of the two partials of ρ, and support of the two partials).
theorem abs_deriv_Jker (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
        = ε⁻¹ * Work.FTS.StrongEps.Jker
            (fun q : ℝ × ℝ => |deriv (fun s : ℝ => ρ (s, q.2)) q.1|) ε p)
    ∧ (∀ p : ℝ × ℝ, |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
        = ε⁻¹ * Work.FTS.StrongEps.Jker
            (fun q : ℝ × ℝ => |deriv (fun t : ℝ => ρ (q.1, t)) q.2|) ε p)
    ∧ Continuous (fun q : ℝ × ℝ => deriv (fun s : ℝ => ρ (s, q.2)) q.1)
    ∧ Continuous (fun q : ℝ × ℝ => deriv (fun t : ℝ => ρ (q.1, t)) q.2)
    ∧ (∀ p : ℝ × ℝ, deriv (fun s : ℝ => ρ (s, p.2)) p.1 ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1)
    ∧ (∀ p : ℝ × ℝ, deriv (fun t : ℝ => ρ (p.1, t)) p.2 ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1) := by
  have hsmooth : ContDiff ℝ 1 ρ := hρ.smooth 1
  -- the two scaling identities
  have hsc1 : ∀ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      = ε⁻¹ * Work.FTS.StrongEps.Jker
          (fun q : ℝ × ℝ => |deriv (fun s : ℝ => ρ (s, q.2)) q.1|) ε p := by
    intro p
    simp only [Work.FTS.StrongEps.Jker, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [deriv_Jker_fst ρ hsmooth ε p]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹)]
    ring
  have hsc2 : ∀ p : ℝ × ℝ, |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
      = ε⁻¹ * Work.FTS.StrongEps.Jker
          (fun q : ℝ × ℝ => |deriv (fun t : ℝ => ρ (q.1, t)) q.2|) ε p := by
    intro p
    simp only [Work.FTS.StrongEps.Jker, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [deriv_Jker_snd ρ hsmooth ε p]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹ ^ 2), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε⁻¹)]
    ring
  -- the two partial derivatives are continuous
  have hcont1 : Continuous (fun q : ℝ × ℝ => deriv (fun s : ℝ => ρ (s, q.2)) q.1) :=
    continuous_deriv_slice_fst hsmooth
  have hcont2 : Continuous (fun q : ℝ × ℝ => deriv (fun t : ℝ => ρ (q.1, t)) q.2) :=
    continuous_deriv_slice_snd hsmooth
  -- both partial derivatives vanish off the closed unit ball
  have htsupport : tsupport ρ ⊆ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ 1} :=
    closure_minimal (fun q hq => hρ.moll.support q hq)
      (isClosed_le (by continuity) continuous_const)
  have hsupp1 : ∀ p : ℝ × ℝ, deriv (fun s : ℝ => ρ (s, p.2)) p.1 ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
    intro p hp
    by_contra hcon
    have hlt : 1 < p.1 ^ 2 + p.2 ^ 2 := not_le.mp hcon
    have hpnot : p ∉ tsupport ρ := fun h => absurd (htsupport h) (not_le.mpr hlt)
    have hev : ρ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hpnot
    have hcont : Tendsto (fun s : ℝ => (s, p.2)) (𝓝 p.1) (𝓝 p) :=
      (continuous_id.prodMk continuous_const).tendsto p.1
    have hslice : (fun s : ℝ => ρ (s, p.2)) =ᶠ[𝓝 p.1] (fun _ : ℝ => (0 : ℝ)) :=
      hcont.eventually hev
    exact hp (by rw [hslice.deriv_eq]; simp)
  have hsupp2 : ∀ p : ℝ × ℝ, deriv (fun t : ℝ => ρ (p.1, t)) p.2 ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
    intro p hp
    by_contra hcon
    have hlt : 1 < p.1 ^ 2 + p.2 ^ 2 := not_le.mp hcon
    have hpnot : p ∉ tsupport ρ := fun h => absurd (htsupport h) (not_le.mpr hlt)
    have hev : ρ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hpnot
    have hcont : Tendsto (fun t : ℝ => (p.1, t)) (𝓝 p.2) (𝓝 p) :=
      (continuous_const.prodMk continuous_id).tendsto p.2
    have hslice : (fun t : ℝ => ρ (p.1, t)) =ᶠ[𝓝 p.2] (fun _ : ℝ => (0 : ℝ)) :=
      hcont.eventually hev
    exact hp (by rw [hslice.deriv_eq]; simp)
  exact ⟨hsc1, hsc2, hcont1, hcont2, hsupp1, hsupp2⟩

end

end Work.FTS.StrongEps.StepFacts
