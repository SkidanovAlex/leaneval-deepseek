/-
Copyright: work module for the Elgindi finite-time singularity project.

# The triangle inequality for the weighted `ℋ^k`-norm

`Work.Spaces.HkNorm α k f = √(HkSq α k f)`, where

`HkSq α k f = ∫_{z ∈ [0,∞)} ∫_{θ ∈ [0,π/2]} HkIntegrand α k f z θ`

and `HkIntegrand α k f z θ` is the sum of the squares of the *slots*
`D_z^i f · w(z)/sin(2θ)^{η/2}` (`0 ≤ i ≤ k`) and `D_z^jD_θ^i f · Wt α z θ`
(`1 ≤ i`, `i + j ≤ k`).  Since the slots are linear in `f` wherever the iterated operators
are additive, `HkSq` is the squared norm of an `ℓ²`-valued `L²`-function and the honest
triangle inequality `HkNorm (f+g) ≤ HkNorm f + HkNorm g` holds — *with constant `1`*, not just
with the constant `√2` obtained from the elementary `(a+b)² ≤ 2a² + 2b²` (the sibling
`Work.FTS.EllipticEst.HkNorm_add_le`).

The argument has three layers.

* **Pointwise square-root bound.**  On the open quadrant the slot vectors add, so the
  Euclidean inequality `√(∑(xᵢ+yᵢ)²) ≤ √(∑xᵢ²) + √(∑yᵢ²)` gives
  `√(HkIntegrand (f+g)) ≤ √(HkIntegrand f) + √(HkIntegrand g)`; on the two boundary lines
  `z = 0` and `sin(2θ) = 0` both sides vanish because the weights `w 0` and `Wt α z θ` do.
  This is the companion lemma `HkIntegrand_sqrt_add_le` of this directory.
* **`L¹`/`L²` bookkeeping.**  Writing `a := √(HkIntegrand f)`, `b := √(HkIntegrand g)`, the
  pointwise bound gives `HkIntegrand (f+g) ≤ (a+b)²`.  Integrating in `θ` and then in `z` (both
  steps are `integral_mono_of_nonneg`, which needs integrability only of the *larger*
  function) and applying the elementary `L²`-Minkowski inequality
  `∫ (a+b)² ≤ (√∫a² + √∫b²)²` (the companion lemma `integral_sq_add_le`) once per variable
  yields `HkSq (f+g) ≤ (√(HkSq f) + √(HkSq g))²`.
* **Square roots.**  Taking square roots gives the statement.

The hypotheses are exactly those of the statement: `C^n` on the open quadrant for every `n`,
and the two `HkMem` certificates.  Nothing is assumed about `f + g`; the estimates above only
ever integrate a function *dominated* by `2 HkIntegrand f + 2 HkIntegrand g`, so the
integrability of the whole is inherited.

**A note on the `π` of the statement.**  The delivered skeleton of this file contained the
smoothness hypothesis `ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))`
*without* `open scoped Real`; there the token `π` is not the notation for `Real.pi` but is
auto-bound as a free variable of the theorem (the elaborated type is
`∀ {π : ℝ} (α : ℝ) (k : ℕ) …, … Set.Ioo 0 (π / 2) → …`), so the statement would ask the
triangle inequality for the smoothness box `(0, π/2)` with an *arbitrary* `π` while the
conclusion does not mention `π` at all.  That free-`π` version is false: for `π ≤ 0` the box is
empty, both smoothness hypotheses become vacuous, and the claim would be the triangle
inequality for *arbitrary* `HkMem` data — which fails, because `HkMem` constrains only the raw
iterated-`deriv` slots, and a function that is nowhere differentiable (hence has all its slots
`= 0` by Mathlib's totalised `deriv`) but is `L²` against the weights is `HkMem` with a tiny
norm, while adding a genuinely smooth, rapidly oscillating function produces a large
`HkNorm` of the sum.  The statement is therefore meant with the genuine `π = Real.pi` — as in
the sibling `Work.FTS.EllipticEst.HkNorm_add_le` and `Work.FTS.EllipticEst.HkNormAddSelf` — and
this is what `open scoped Real` (present below, before the theorem) makes of it.  The text of
the statement is unchanged from the skeleton, only the scope of `π` is fixed.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS.StrongEps.EpsE4Thr.integral_sq_add_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkIntegrand_sqrt_add_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The iterated `L²`-Minkowski step

For nonnegative `a`, `b` with the honest slicewise/integrated `L²` certificates, and any
nonnegative `c` dominated pointwise by `(a+b)²` on the domain,

`∫_z ∫_θ c ≤ (√(∫_z ∫_θ a²) + √(∫_z ∫_θ b²))²`

whenever the iterated integral of `c` is the honest one.  The proof applies the
one-dimensional `L²`-Minkowski inequality `integral_sq_add_le` in the variable `θ` (slicewise)
and then in the variable `z`, so that only the *angular* slices of `a`, `b` and the two
`z`-integrals `z ↦ ∫_θ a²`, `z ↦ ∫_θ b²` have to be measurable — the joint measurability of
`(a+b)²` is never needed. -/
theorem iterated_sq_integral_add_le {a b c : ℝ → ℝ → ℝ}
    (han : ∀ z θ, 0 ≤ a z θ) (hbn : ∀ z θ, 0 ≤ b z θ)
    (hsa : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => a z θ) (volume.restrict Work.Spaces.Iθ))
    (hsb : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => b z θ) (volume.restrict Work.Spaces.Iθ))
    (h2a : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => a z θ ^ 2) (volume.restrict Work.Spaces.Iθ))
    (h2b : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => b z θ ^ 2) (volume.restrict Work.Spaces.Iθ))
    (hAa : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
      (volume.restrict Work.Spaces.Iz))
    (hAb : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, b z θ ^ 2)
      (volume.restrict Work.Spaces.Iz))
    (hIa : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
      (volume.restrict Work.Spaces.Iz))
    (hIb : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, b z θ ^ 2)
      (volume.restrict Work.Spaces.Iz))
    (hc : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, c z θ ≤ (a z θ + b z θ) ^ 2)
    (hcn : ∀ z θ, 0 ≤ c z θ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, c z θ)
      ≤ (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
          + Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 := by
  -- the angular slice of `(a+b)²` is integrable, being dominated by `2a² + 2b²`
  have hint_θ : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => (a z θ + b z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    refine Integrable.mono' (((h2a z hz).const_mul 2).add ((h2b z hz).const_mul 2))
      (((hsa z hz).add (hsb z hz)).pow 2) (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    linarith [add_sq_le (a := a z θ) (b := b z θ)]
  -- slicewise: `∫_θ c ≤ (√∫_θ a² + √∫_θ b²)²`
  have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, c z θ)
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
          + Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, c z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (a z θ + b z θ) ^ 2 :=
      integral_mono_of_nonneg (Eventually.of_forall (fun θ => hcn z θ)) (hint_θ z hz)
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hc z hz θ hθ))
    have h2 := integral_sq_add_le (μ := volume.restrict Work.Spaces.Iθ)
      (a := fun θ => a z θ) (b := fun θ => b z θ)
      (han z) (hbn z) (hsa z hz) (hsb z hz) (h2a z hz) (h2b z hz)
    linarith
  -- the `z`-integrand `(√∫_θ a² + √∫_θ b²)²` is integrable, being dominated by
  -- `2 ∫_θ a² + 2 ∫_θ b²`
  have hRHSint : Integrable (fun z => (Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
      + Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine Integrable.mono' ((hIa.const_mul 2).add (hIb.const_mul 2)) ?_
      (Eventually.of_forall fun z => ?_)
    · exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hAa).add
        (Real.continuous_sqrt.comp_aestronglyMeasurable hAb)).pow 2
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      have e1 : Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2) ^ 2
          = ∫ θ in Work.Spaces.Iθ, a z θ ^ 2 :=
        Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _)
      have e2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2) ^ 2
          = ∫ θ in Work.Spaces.Iθ, b z θ ^ 2 :=
        Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _)
      linarith [add_sq_le (a := Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2))
        (b := Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2))]
  -- integrate the slicewise bound in `z`
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, c z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          (Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
            + Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ => hcn z θ) hRHSint
      (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
  have hIa' : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
    hIa.congr (Eventually.of_forall fun z =>
      (Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _)).symm)
  have hIb' : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
    hIb.congr (Eventually.of_forall fun z =>
      (Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _)).symm)
  -- `L²`-Minkowski in the variable `z`
  have hz2 := integral_sq_add_le (μ := volume.restrict Work.Spaces.Iz)
    (a := fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2))
    (b := fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2))
    (fun z => Real.sqrt_nonneg _) (fun z => Real.sqrt_nonneg _)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hAa)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hAb) hIa' hIb'
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, c z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          (Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
            + Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 := houter
    _ ≤ (Real.sqrt (∫ z in Work.Spaces.Iz,
            Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2) ^ 2)
          + Real.sqrt (∫ z in Work.Spaces.Iz,
              Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2) ^ 2)) ^ 2 := hz2
    _ = (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
          + Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 := by
        have e1 : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2) ^ 2)
            = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, a z θ ^ 2 :=
          integral_congr_ae (Eventually.of_forall fun z =>
            Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _))
        have e2 : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2) ^ 2)
            = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, b z θ ^ 2 :=
          integral_congr_ae (Eventually.of_forall fun z =>
            Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _))
        rw [e1, e2]

/-! ## The triangle inequality -/

theorem HkNorm_triangle (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g := by
  -- the angular slices of `√(HkIntegrand ·)` are a.e. strongly measurable
  have hsa : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k f z θ))
        (volume.restrict Work.Spaces.Iθ) := fun z hz =>
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Work.FTS.StrongEps.aesm_slice_HkIntegrand_of_contDiffOn α k f (hf k) z hz)
  have hsb : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k g z θ))
        (volume.restrict Work.Spaces.Iθ) := fun z hz =>
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Work.FTS.StrongEps.aesm_slice_HkIntegrand_of_contDiffOn α k g (hg k) z hz)
  -- their squares are integrable on each angular slice (`HkMem`)
  have h2a : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := fun z hz =>
    (hmf.1 z hz).congr (Eventually.of_forall fun θ =>
      (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)).symm)
  have h2b : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := fun z hz =>
    (hmg.1 z hz).congr (Eventually.of_forall fun θ =>
      (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm)
  -- the `z`-integrated squares are a.e. strongly measurable ...
  have hAa : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    refine (Work.FTS.StrongEps.aesm_integral_HkIntegrand_of_contDiffOn α k f (hf k)).congr
      (Eventually.of_forall fun z => ?_)
    exact integral_congr_ae (Eventually.of_forall fun θ =>
      (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)).symm)
  have hAb : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    refine (Work.FTS.StrongEps.aesm_integral_HkIntegrand_of_contDiffOn α k g (hg k)).congr
      (Eventually.of_forall fun z => ?_)
    exact integral_congr_ae (Eventually.of_forall fun θ =>
      (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm)
  -- ... and integrable (`HkMem` again)
  have hIa : Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
    hmf.2.congr (Eventually.of_forall fun z => integral_congr_ae
      (Eventually.of_forall fun θ =>
        (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)).symm))
  have hIb : Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
    hmg.2.congr (Eventually.of_forall fun z => integral_congr_ae
      (Eventually.of_forall fun θ =>
        (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm))
  -- the pointwise bound `HkIntegrand (f+g) ≤ (√(HkIntegrand f) + √(HkIntegrand g))²`
  have hc : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ (Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
            + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ)) ^ 2 := by
    intro z hz θ hθ
    have h1 := HkIntegrand_sqrt_add_le α k hf hg z hz θ hθ
    have h2 : Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ) ^ 2
        ≤ (Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
            + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ)) ^ 2 := by
      nlinarith [h1, Real.sqrt_nonneg (Work.Spaces.HkIntegrand α k
        (fun z θ => f z θ + g z θ) z θ)]
    rwa [Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k _ z θ)] at h2
  have hcore := iterated_sq_integral_add_le
    (a := fun z θ => Real.sqrt (Work.Spaces.HkIntegrand α k f z θ))
    (b := fun z θ => Real.sqrt (Work.Spaces.HkIntegrand α k g z θ))
    (c := fun z θ => Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
    (fun z θ => Real.sqrt_nonneg _) (fun z θ => Real.sqrt_nonneg _)
    hsa hsb h2a h2b hAa hAb hIa hIb hc
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
  -- identify the two integrals with `HkSq`
  have hSqf : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ^ 2) = Work.Spaces.HkSq α k f := by
    rw [Work.Spaces.HkSq]
    exact integral_congr_ae (Eventually.of_forall fun z => integral_congr_ae
      (Eventually.of_forall fun θ => Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)))
  have hSqg : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) ^ 2) = Work.Spaces.HkSq α k g := by
    rw [Work.Spaces.HkSq]
    exact integral_congr_ae (Eventually.of_forall fun z => integral_congr_ae
      (Eventually.of_forall fun θ => Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k g z θ)))
  rw [hSqf, hSqg] at hcore
  -- take square roots
  have hgoal : Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      = Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ) := rfl
  rw [hgoal]
  refine (Real.sqrt_le_sqrt hcore).trans (le_of_eq ?_)
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt (Work.Spaces.HkSq α k f)
      + Real.sqrt (Work.Spaces.HkSq α k g))]
  rfl

end Work.FTS.StrongEps.EpsE4Thr
