/-
# `Work.FTS.CoercivityFix.Assembly.WitDefs` — the witness of the non-vacuity lemma

The target `Work.FTS.CoercivityFix.Assembly.exists_coerAdm_pos` asks for a *non-zero*
element of the coercivity class with a *positive* `𝓗⁴`-functional:

  `∀ α > 0, ∃ f, Work.FTS.Nonlin.CoerAdm α f ∧ 0 < Work.Spaces.HkSq α 4 f`.

Since `CoerAdm α f = RegQ α 5 f ∧ VanishTheta f ∧ (axis) ∧ L₁₂(f)(0) = 0`, a witness has to
satisfy five conditions simultaneously.  The one that constrains the shape of the datum is
`L₁₂(f)(0) = 0`: for a *separable* datum `f z θ = ρ(z)·Γ(θ)` (`Γ = Work.Spaces.Gam α`) one has

  `L₁₂(f)(0) = (∫_{s>0} ρ(s)/s ds) · c(α)`,   `c(α) = ∫_θ K(θ)Γ(θ) dθ > 0`,

so it is enough to make the *radial* factor have zero logarithmic mean,
`∫_0^∞ ρ(s)/s ds = 0`.  The cheapest way to get that together with *bounded* `D_z`-jets (which
is what `HkMem` needs) is to take a derivative of a compactly supported bump:

  `ρ := z ∂_z(bumpZ) = D_z(bumpZ)`,

because `∫_0^∞ ∂_z(bumpZ) = bumpZ(∞) − bumpZ(0) = 0` (fundamental theorem of calculus, the bump
being compactly supported), while at the same time

  `D_z^j ρ = D_z^{j+1} bumpZ`

is bounded for every `j` by the delivered `Work.FTS.LocData.exists_bound_T1_iterate_bumpZ`.
The angular factor is the paper's own `Γ(θ) = (sin θ · cos²θ)^{α/3}`, so that the delivered
separable majorant `Work.FTS.LocDataExt.HkIntegrand_sepGam_le` applies verbatim and (for every
`α > 0`, with no smallness restriction) the `𝓗⁵`-membership follows.

This module only fixes the witness and its elementary properties (smoothness, vanishing,
separability of the `D`-iterates); the estimates about it live in the sibling modules.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.BumpZ_contDiff
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.contDiff_deriv
import Submission.Work.FTS.LocData.SmoothQuad_hLoc
import Submission.Work.FTS.LocData.DzIter_bumpZ_bound
import Submission.Work.FTS.LocData.hLoc_vanishing

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-- **The radial factor of the witness**: `ρ(z) = z ∂_z(bumpZ)(z) = D_z(bumpZ)(z)`, the
`D_z`-derivative of the compactly supported bump `bumpZ = χ(4· − 5)` of
`Work.FTS.LocData`.

* its support is contained in `[3/4, 7/4]` (the support of `bumpZ`), so it vanishes on a
  neighbourhood of `z = 0` and at infinity;
* `ρ(z)/z = ∂_z(bumpZ)(z)`, hence `∫_0^∞ ρ(s)/s ds = 0` — this is what makes the witness
  `L₁₂`-orthogonal;
* `D_z^j ρ = D_z^{j+1} bumpZ` is bounded for every `j` (the jets of a smooth compactly
  supported bump), which is the radial input of the separable `𝓗^k`-majorant. -/
noncomputable def radW (z : ℝ) : ℝ := z * deriv Work.FTS.LocData.bumpZ z

/-- **The witness** of the non-vacuity lemma: `f(z,θ) = ρ(z)·Γ(θ)`, with `ρ = radW` and
`Γ(θ) = (sinθ cos²θ)^{α/3}` the paper's angular factor. -/
noncomputable def witF (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => radW z * Work.Spaces.Gam α θ

@[simp] theorem radW_apply (z : ℝ) : radW z = z * deriv Work.FTS.LocData.bumpZ z := rfl

@[simp] theorem witF_apply (α z θ : ℝ) : witF α z θ = radW z * Work.Spaces.Gam α θ := rfl

theorem radW_eq_T1 : radW = Work.FTS.LocData.T1 Work.FTS.LocData.bumpZ := rfl

/-! ## The `D_z`-iterates of the radial factor -/

/-- `D_z`-iterating a `D_z`-derivative: `D_z^j (D_z f) = D_z^{j+1} f`. -/
theorem DzIter_Dz (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz f) = Work.Spaces.DzIter (j + 1) f := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      rfl

/-- The `θ`-dummy version of the radial factor *is* `D_z(bumpZ)`. -/
theorem radW_eq_Dz :
    (fun z _ : ℝ => radW z) = Work.Spaces.Dz (fun z _ => Work.FTS.LocData.bumpZ z) := by
  funext z θ
  simp only [radW, Work.Spaces.Dz, Work.Spaces.pz]

/-- **Every `D_z`-iterate of the radial factor is a `D_z`-iterate of the bump**:
`D_z^j ρ = D_z^{j+1} bumpZ`.  Consequently the delivered bounds on the jets of `bumpZ` give the
jets of `ρ`. -/
theorem DzIter_radW (j : ℕ) :
    Work.Spaces.DzIter j (fun z _ : ℝ => radW z)
      = Work.Spaces.DzIter (j + 1) (fun z _ => Work.FTS.LocData.bumpZ z) := by
  rw [radW_eq_Dz, DzIter_Dz]

/-! ## Elementary properties of the witness -/

/-- The radial factor vanishes off the support of the bump. -/
theorem radW_eq_zero_of_notMem {z : ℝ} (hz : z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4)) :
    radW z = 0 := by
  rw [radW, Work.FTS.LocData.deriv_eq_zero_of_eq_zero_off_closed isClosed_Icc
    (fun z' hz' => Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc z' hz') hz, mul_zero]

/-- The radial factor is `C^∞` on `ℝ`. -/
theorem radW_contDiff : ContDiff ℝ Work.Stability.smoothOrder radW := by
  have h := Work.FTS.LocData.T1_contDiff Work.FTS.LocData.BumpZ_contDiff
  simpa only [radW_eq_T1] using h

/-- The radial factor is continuous. -/
theorem radW_continuous : Continuous radW := radW_contDiff.continuous

/-- A function of `z` alone is `SmoothQuad`. -/
theorem smoothQuad_radW : Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => radW z) :=
  Work.FTS.LocData.smoothQuad_of_fst radW_contDiff

/-- **The witness is `C^∞` on the open quadrant** (genuine smoothness, not analyticity). -/
theorem smoothQuad_witF (α : ℝ) : Work.FTS.LocData.SmoothQuad (witF α) := by
  change Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => radW z * Work.Spaces.Gam α θ)
  exact Work.FTS.LocData.smoothQuad_mul smoothQuad_radW
    (Work.FTS.LocData.smoothQuad_of_snd (Work.FTS.LocData.contDiffOn_Gam_Ioo α))

/-- The witness vanishes at the two angular endpoints. -/
theorem vanishTheta_witF (α : ℝ) (hα : 0 < α) : Work.Spaces.VanishTheta (witF α) := by
  constructor
  · intro z
    rw [witF_apply, Work.Spaces.Gam_zero_left α (ne_of_gt hα), mul_zero]
  · intro z
    rw [witF_apply, Work.Spaces.Gam_zero_right α (ne_of_gt hα), mul_zero]

/-- `radW` vanishes on a neighbourhood of `0`, so all its derivatives vanish there. -/
theorem radW_eventually_zero_at_zero : ∀ᶠ z in 𝓝 (0 : ℝ), radW z = 0 := by
  filter_upwards [isOpen_lt continuous_id continuous_const |>.mem_nhds
    (by norm_num : (0 : ℝ) < 3 / 4)] with z hz
  exact radW_eq_zero_of_notMem (fun h => absurd h.1 (not_le.mpr hz))

/-- **The radial factor is not identically zero.**  Otherwise `∂_z(bumpZ)` would vanish
everywhere, contradicting `∫_{3/4}^{3/2} ∂_z(bumpZ) = bumpZ(3/2) − bumpZ(3/4) = 1`. -/
theorem radW_ne_zero_exists : ∃ z : ℝ, radW z ≠ 0 := by
  by_contra h
  push_neg at h
  have hd : deriv Work.FTS.LocData.bumpZ = fun _ : ℝ => (0 : ℝ) := by
    funext z
    rcases eq_or_ne z 0 with rfl | hz
    · exact Work.FTS.LocData.deriv_eq_zero_of_eq_zero_off_closed isClosed_Icc
        (fun z' hz' => Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc z' hz') (by norm_num)
    · have h1 := h z
      rw [radW, mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 hz
      · exact h1
  have hdiff : ∀ x ∈ Set.uIcc (3 / 4 : ℝ) (3 / 2), DifferentiableAt ℝ Work.FTS.LocData.bumpZ x :=
    fun x _ => (Work.FTS.LocData.BumpZ_contDiff.differentiable (by simp)).differentiableAt
  have hint := intervalIntegral.integral_deriv_eq_sub' Work.FTS.LocData.bumpZ hd hdiff
    (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => (0 : ℝ))
      (Set.uIcc (3 / 4 : ℝ) (3 / 2)))
  have hzero : (∫ y in (3 / 4 : ℝ)..(3 / 2), (0 : ℝ)) = 0 := by simp
  rw [hzero] at hint
  have h1 : Work.FTS.LocData.bumpZ (3 / 2) = 1 := by
    rw [Work.FTS.LocData.bumpZ_apply]
    exact Work.Stability.chi_eq_one (by norm_num)
  have h2 : Work.FTS.LocData.bumpZ (3 / 4) = 0 := by
    rw [Work.FTS.LocData.bumpZ_apply]
    exact Work.Stability.chi_eq_zero (by norm_num)
  rw [h1, h2] at hint
  norm_num at hint

/-- **On a whole interval around some point the radial factor does not vanish** (continuity plus
`radW_ne_zero_exists`; the interval lies inside `(0,∞)` because `radW` vanishes off the support
of the bump). -/
theorem exists_radW_ne_zero_interval :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ z ∈ Set.Ioo a b, radW z ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := radW_ne_zero_exists
  have hzmem : z₀ ∈ Set.Icc (3 / 4 : ℝ) (7 / 4) := by
    by_contra hcon
    exact hz₀ (radW_eq_zero_of_notMem hcon)
  have hopen : IsOpen (radW ⁻¹' ({0}ᶜ : Set ℝ)) :=
    isOpen_compl_singleton.preimage radW_continuous
  have hmem : z₀ ∈ radW ⁻¹' ({0}ᶜ : Set ℝ) := by
    simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  have hz1 : (3 : ℝ) / 4 ≤ z₀ := hzmem.1
  refine ⟨max (z₀ - ε) (3 / 4), z₀ + ε, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (le_max_right (z₀ - ε) (3 / 4))
  · exact max_lt (by linarith) (by linarith)
  · intro z hz
    have h1 : z₀ - ε < z := lt_of_le_of_lt (le_max_left (z₀ - ε) (3 / 4)) hz.1
    have h2 : z < z₀ + ε := hz.2
    have hdist : dist z z₀ < ε := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have := hball (Metric.mem_ball.mpr hdist)
    simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using this

/-- The witness vanishes on the axis, together with its first `z`-derivative. -/
theorem axis_witF (α : ℝ) : ∀ θ ∈ Work.Spaces.Iθ,
    witF α 0 θ = 0 ∧ Work.Spaces.pz (witF α) 0 θ = 0 := by
  intro θ _
  constructor
  · rw [witF_apply, radW]
    ring
  · rw [Work.Spaces.pz]
    have hev : (fun z' : ℝ => witF α z' θ) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [radW_eventually_zero_at_zero] with z hz
      rw [witF_apply, hz, zero_mul]
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

end Work.FTS.CoercivityFix.Assembly
