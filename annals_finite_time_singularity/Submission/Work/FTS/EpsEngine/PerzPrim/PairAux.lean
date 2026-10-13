/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/PerzPrim/PairAux.lean` — the pointwise pair estimates for the
# per-`z` angular energy of a sum

Three auxiliaries for `Work.FTS.EpsEngine.perz_iter_feps_le`:

* `aesm_slice_HkIntegrand_of_smoothOpen` — for `f` smooth on the open quadrant and `z ∈ Iz`, the
  angular slice `θ ↦ HkIntegrand α k f z θ` is a.e. strongly measurable on `Iθ` (continuity on
  `(0,π/2)`, together with `HkIntegrand α k f 0 θ = 0` at `z = 0`);

* `HkIntegrand_le_add_of_smoothOpen` — the *reverse* triangle inequality for the pair
  `(f, g) → f + g`: on `Iz × Iθ`,
  `HkIntegrand α k f ≤ 2 · HkIntegrand α k (f+g) + 2 · HkIntegrand α k g`.
  (The slots of the pair are additive on `Q0`, and `(x - y)² ≤ 2x² + 2y²`; it is
  `HkIntegrand_add_le_open` applied to the pair `(f+g, -g)`.)

* `integral_HkIntegrand_add_le` — the **junk-robust** per-`z` angular-energy bound for a sum:
  given that the *summand* `g` has an integrable angular energy at `z` with integral `≤ b`, and
  that the *other* summand `f` has angular-energy integral `≤ B` (as a Bochner integral — no
  integrability assumed!), the sum `f + g` satisfies
  `∫_θ HkIntegrand α k (f+g) z θ ≤ 2 B + 2 b`.
  The proof splits on the integrability of `θ ↦ HkIntegrand α k f z θ`: in the honest case
  `Integrable.mono'` + `integral_mono_ae` apply to the pointwise inequality of
  `HkIntegrand_add_le_open`; in the junk case the reverse inequality above shows that the *sum*
  is also non-integrable, so both Bochner integrals are the junk value `0`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.PerzPrim

set_option autoImplicit false

/-- For `f` smooth on the open quadrant and `z ∈ Iz`, the angular slice of the level-`k`
`ℋ`-integrand is a.e. strongly measurable on `Iθ`. -/
lemma aesm_slice_HkIntegrand_of_smoothOpen {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ => (0 : ℝ) from
      funext fun θ => Work.Spaces.HkIntegrand_zero_z α k f θ]
    exact aestronglyMeasurable_const
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (hf.continuousOn_HkIntegrand α k) hzpos

/-- **The reverse triangle inequality for the `ℋ^k`-integrand.**  With `f`, `g` smooth on the
open quadrant, on `Iz × Iθ`,
`HkIntegrand α k f ≤ 2 · HkIntegrand α k (f+g) + 2 · HkIntegrand α k g`.
Obtained from `HkIntegrand_add_le_open` applied to the pair `(f+g, -g)`. -/
lemma HkIntegrand_le_add_of_smoothOpen {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k f z θ ≤
      2 * Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hfg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hf hg
  have hng : Work.FTS.EllipticEst.SmoothOpen (-g) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun x : ℝ × ℝ => -g x.1 x.2)
      Work.FTS.EllipticEst.Q0
    exact hg.neg
  have h := Work.FTS.EllipticEst.HkIntegrand_add_le_open α k
    (f := fun z θ => f z θ + g z θ) (g := -g) hfg hng hz hθ
  rw [Work.FTS.EllipticEst.HkIntegrand_neg α k g,
    show (fun z θ => (f z θ + g z θ) + (-g) z θ) = f from by ext z θ; simp] at h
  exact h

/-- **The junk-robust per-`z` angular-energy bound for a sum.**  If the angular energy of `g` is
integrable at `z` with integral `≤ b`, and the Bochner integral of the angular energy of `f` is
`≤ B` (no integrability of `f` assumed), then the angular energy of `f + g` has Bochner integral
`≤ 2 B + 2 b`. -/
theorem integral_HkIntegrand_add_le {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {B b : ℝ}
    (hB : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) ≤ B) (hB0 : 0 ≤ B)
    (hbint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k g z θ) Work.Spaces.Iθ)
    (hb : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) ≤ b) (hb0 : 0 ≤ b) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      ≤ 2 * B + 2 * b := by
  set a : ℝ → ℝ := fun θ => Work.Spaces.HkIntegrand α k f z θ with ha
  set bb : ℝ → ℝ := fun θ => Work.Spaces.HkIntegrand α k g z θ with hbb
  set ff : ℝ → ℝ := fun θ => Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ with hff
  have hfg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hf hg
  have hAESMa : MeasureTheory.AEStronglyMeasurable a
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_slice_HkIntegrand_of_smoothOpen hf hz
  have hAESMf : MeasureTheory.AEStronglyMeasurable ff
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_slice_HkIntegrand_of_smoothOpen hfg hz
  have hfw : ∀ θ ∈ Work.Spaces.Iθ, ff θ ≤ 2 * a θ + 2 * bb θ := fun θ hθ =>
    Work.FTS.EllipticEst.HkIntegrand_add_le_open α k hf hg hz hθ
  have hrev : ∀ θ ∈ Work.Spaces.Iθ, a θ ≤ 2 * ff θ + 2 * bb θ := fun θ hθ =>
    HkIntegrand_le_add_of_smoothOpen hf hg hz hθ
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ff θ ≤ 2 * a θ + 2 * bb θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hfw θ hθ
  have hae_rev : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖a θ‖ ≤ 2 * ff θ + 2 * bb θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hrev θ hθ
  have hae_fwd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖ff θ‖ ≤ 2 * a θ + 2 * bb θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k _ z θ)]
    exact hfw θ hθ
  by_cases hA : MeasureTheory.Integrable a (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · have h2ab : MeasureTheory.Integrable (fun θ => 2 * a θ + 2 * bb θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hA.const_mul 2).add (hbint.const_mul 2)
    have hffint : MeasureTheory.Integrable ff (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      h2ab.mono' hAESMf hae_fwd
    have hmain := MeasureTheory.integral_mono_ae hffint h2ab hae
    rw [MeasureTheory.integral_add (hA.const_mul 2) (hbint.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmain
    linarith
  · have hnotff : ¬ MeasureTheory.Integrable ff
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      intro hffint
      have h2fb : MeasureTheory.Integrable (fun θ => 2 * ff θ + 2 * bb θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hffint.const_mul 2).add (hbint.const_mul 2)
      exact hA (h2fb.mono' hAESMa hae_rev)
    rw [MeasureTheory.integral_undef hnotff]
    linarith

end Work.FTS.EpsEngine.PerzPrim
