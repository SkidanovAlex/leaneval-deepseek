/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `∀ᵐ θ` Plancherel identities for `NiceFlat` data and the shifted operator `∂_t - b`

`Work.FTS.EllSol.Shift2Flat.niceRangePlanch`: for `NiceFlat u` and every real `b`, for almost
every angle `θ ∈ Iθ` the three shifted Plancherel identities hold:

* `∫_ξ ((2πξ)² + b²)‖Φ_ξ(θ)‖² = ∫_t (∂_t u(t,θ) - b·u(t,θ))²` (and the left-hand integrand is
  integrable), where `Φ_ξ(θ) = slice u ξ θ` is the `t`-Fourier slice of `u`;
* `∫_ξ ((2πξ)² + b²)²‖Φ_ξ(θ)‖² = ∫_t (∂_t²u(t,θ) - 2b·∂_t u(t,θ) + b²u(t,θ))²`;
* the same first-order identity with `u` replaced by `∂_θu` (the right-hand side being
  `∫_t (∂_θ∂_t u(t,θ) - b·∂_θu(t,θ))²`, the two mixed partials agreeing by Clairaut).

The multiplier identities behind the statement are
`𝓕((∂_t - b)h)(ξ) = (2πiξ - b)·𝓕h(ξ)`, `|2πiξ - b|² = (2πξ)² + b²`, and
`|(2πiξ - b)²|² = ((2πξ)² + b²)²`; the two `t`-integral identities themselves are the
one-dimensional Plancherel lemma `FlatFT.shiftPlancherel1` (proved in the sibling module),
applied at each interior angle `θ` to the slice
`h_θ = fun t => (u t θ : ℂ)`, which is `C²` (resp. `C¹` for `∂_θu`) with compact support by
`NiceFlat`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv
import Submission.Work.FTS.EllSol.FlatFT.flatNiceSlices
import Submission.Work.FTS.EllSol.FlatFT.pz_contDiffOn_succ
import Submission.Work.FTS.EllSol.FlatFT.shiftPlancherel1
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

open Work.FTS.EllSol.FlatFT (slice slice1 NiceFlat niceFlat_slice_contDiff
  niceFlat_hasCompactSupport niceFlat_hasCompactSupport_pth niceFlat_slice_pth_contDiff
  contDiff_ofReal_comp deriv_ofReal_comp)

namespace Work.FTS.EllSol.Shift2Flat

set_option maxHeartbeats 1000000

/-! ## Elementary facts about the a.e. angle and about complex norms -/

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`. -/
theorem nrp_ae_mem_Ioo :
    ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
  filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)]
    with θ h hmem
  exact h.mpr hmem

/-- `‖(x:ℂ) - b (y:ℂ)‖² = (x - b y)²` for real `x y b`. -/
theorem nrp_normSq_sub (x y b : ℝ) :
    ‖(x : ℂ) - b * (y : ℂ)‖ ^ 2 = (x - b * y) ^ 2 := by
  have h : (x : ℂ) - b * (y : ℂ) = ((x - b * y : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-- `‖(x:ℂ) - 2b(y:ℂ) + b²(z:ℂ)‖² = (x - 2by + b²z)²` for real `x y z b`. -/
theorem nrp_normSq_sub2 (x y z b : ℝ) :
    ‖(x : ℂ) - 2 * b * (y : ℂ) + b ^ 2 * (z : ℂ)‖ ^ 2 = (x - 2 * b * y + b ^ 2 * z) ^ 2 := by
  have h : (x : ℂ) - 2 * b * (y : ℂ) + b ^ 2 * (z : ℂ)
      = ((x - 2 * b * y + b ^ 2 * z : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-! ## The slice data of a `NiceFlat` datum, as a complex-valued function of `t` -/

/-- The `t`-derivative of the coerced slice of `u` is the coerced slice of `∂_t u`. -/
theorem nrp_deriv_slice {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t : ℝ => (u t θ : ℂ)) = fun t : ℝ => (Work.Spaces.pz u t θ : ℂ) := by
  funext t
  have hs2 := niceFlat_slice_contDiff hg hθ (n := 2) (by norm_num)
  rw [deriv_ofReal_comp (ContDiff.differentiable hs2 (by norm_num)).differentiableAt]
  rfl

/-- The `t`-slice of `∂_t u` is `C¹`. -/
theorem nrp_slice_pz_contDiff {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiff ℝ 1 (fun t : ℝ => Work.Spaces.pz u t θ) := by
  have hV : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (isOpen_univ : IsOpen (Set.univ : Set ℝ)).prod isOpen_Ioo
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz u))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllSol.FlatFT.pz_contDiffOn_succ hV hg.1
  have h := h1.comp (t := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      (f := fun t : ℝ => (t, θ)) (s := Set.univ)
    ((show ContDiff ℝ 1 (fun t : ℝ => (t, θ)) from by fun_prop).contDiffOn (s := Set.univ))
    (fun t _ => ⟨trivial, hθ⟩)
  exact contDiffOn_univ.1 (by simpa [Function.comp_def, Function.uncurry] using h)

/-- The second `t`-derivative of the coerced slice of `u` is the coerced slice of `∂_t²u`. -/
theorem nrp_deriv2_slice {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun t : ℝ => (u t θ : ℂ)))
      = fun t : ℝ => (Work.Spaces.pz (Work.Spaces.pz u) t θ : ℂ) := by
  have hpz := nrp_slice_pz_contDiff hg hθ
  have h2 : deriv (fun t : ℝ => (Work.Spaces.pz u t θ : ℂ))
      = fun t : ℝ => (Work.Spaces.pz (Work.Spaces.pz u) t θ : ℂ) := by
    funext t
    rw [deriv_ofReal_comp (ContDiff.differentiable hpz (by norm_num)).differentiableAt]
    rfl
  rw [nrp_deriv_slice hg hθ]
  exact h2

/-- The `t`-derivative of the coerced slice of `∂_θu` is the coerced slice of `∂_t∂_θu`. -/
theorem nrp_deriv_pth_slice {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t : ℝ => (Work.Spaces.pth u t θ : ℂ))
      = fun t : ℝ => (Work.Spaces.pz (Work.Spaces.pth u) t θ : ℂ) := by
  funext t
  have hs1 := niceFlat_slice_pth_contDiff hg hθ (n := 1) (by norm_num)
  rw [deriv_ofReal_comp (ContDiff.differentiable hs1 (by norm_num)).differentiableAt]
  rfl

/-- Clairaut on the open strip, at an interior angle. -/
theorem nrp_pz_pth_comm {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (t : ℝ) :
    Work.Spaces.pz (Work.Spaces.pth u) t θ = Work.Spaces.pth (Work.Spaces.pz u) t θ := by
  refine Work.Spaces.pz_pth_comm (hg.1.contDiffAt ?_)
  exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hθ⟩


/-! ## The second-order shifted Plancherel identity, from the first-order one applied twice

The sibling module `FlatFT.shiftPlancherel1` gives the first-order identity.  Applying it to the
shifted profile `t ↦ ∂_t h t - b·h t` — which is again `C¹` with compact support when `h` is
`C²` with compact support — and using `𝓕(∂_t h - b·h)(ξ) = (2πiξ - b)·𝓕h(ξ)` pointwise yields the
second-order identity (the multiplier `(2πiξ)² - 2b(2πiξ) + b²` of `h'' - 2bh' + b²h` being the
square of `2πiξ - b`).  Keeping the derivation here makes this module depend only on the
first-order sibling.
-/

/-- The squared modulus of the shifted Fourier multiplier `2πIξ - b`:
`‖(2πIξ - b)F‖² = ((2πξ)² + b²)·‖F‖²`. -/
theorem nrp_norm_sq_mul_shift (F : ℂ) (b ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ - (b : ℂ)) * F‖ ^ 2
      = ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖F‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (2 * Real.pi * Complex.I * ξ - (b : ℂ)).re = -b := by simp
  have him : (2 * Real.pi * Complex.I * ξ - (b : ℂ)).im = 2 * Real.pi * ξ := by simp
  rw [hre, him]
  ring

/-- Linearity of the `t`-Fourier slice for a difference with a constant multiple,
`slice1 (f - c·g) ξ = slice1 f ξ - c·slice1 g ξ`; all the integrals involved converge absolutely
because the exponential factor has modulus one and `f`, `g` are continuous with compact
support. -/
theorem nrp_slice1_sub_const_mul (f g : ℝ → ℂ) (c : ℂ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (hg : Continuous g) (hgs : HasCompactSupport g) (ξ : ℝ) :
    slice1 (fun t => f t - c * g t) ξ = slice1 f ξ - c * slice1 g ξ := by
  set κ : ℝ → ℂ := fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)) with hκ
  have hκc : Continuous κ := by rw [hκ]; fun_prop
  have hfs' : HasCompactSupport (fun t => f t * κ t) :=
    hfs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have hgs' : HasCompactSupport (fun t => g t * κ t) :=
    hgs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have h1 : Integrable (fun t => f t * κ t) :=
    (hf.mul hκc).integrable_of_hasCompactSupport hfs'
  have h2 : Integrable (fun t => g t * κ t) :=
    (hg.mul hκc).integrable_of_hasCompactSupport hgs'
  have h3 : Integrable (fun t => c * (g t * κ t)) := h2.const_mul c
  calc slice1 (fun t => f t - c * g t) ξ
      = ∫ t, (f t - c * g t) * κ t := rfl
    _ = ∫ t, (f t * κ t - c * (g t * κ t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        ring
    _ = (∫ t, f t * κ t) - ∫ t, c * (g t * κ t) := integral_sub h1 h3
    _ = (∫ t, f t * κ t) - c * ∫ t, g t * κ t := by rw [integral_const_mul]
    _ = slice1 f ξ - c * slice1 g ξ := rfl

/-- The pointwise multiplier identity for the shifted profile `∂_t h - b·h`. -/
theorem nrp_key {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (b ξ : ℝ) :
    ‖slice1 (fun t => deriv h t - b * h t) ξ‖ ^ 2
      = ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2 := by
  rw [nrp_slice1_sub_const_mul (deriv h) h (b : ℂ) hh.continuous_deriv_one hs.deriv
    hh.continuous hs ξ, Work.FTS.EllSol.FlatFT.slice1_deriv h hh hs ξ, ← sub_mul,
    nrp_norm_sq_mul_shift]

/-- **Second-order shifted Plancherel**, obtained from `FlatFT.shiftPlancherel1` applied to `h`
and to `∂_t h - b·h`. -/
theorem nrp_shiftPlancherel2 {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) (hs : HasCompactSupport h)
    (b : ℝ) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice1 h ξ‖ ^ 2) ∧
      (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice1 h ξ‖ ^ 2
        = ∫ t : ℝ, ‖deriv (deriv h) t - 2 * b * deriv h t + b ^ 2 * h t‖ ^ 2) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hdc : ContDiff ℝ 1 (deriv h) := hh.deriv'
  have hcd' : ContDiff ℝ 1 (fun t : ℝ => deriv h t - b * h t) :=
    hdc.sub ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (b : ℂ))).mul hh1)
  have hb : HasCompactSupport (fun t : ℝ => (b : ℂ) * h t) :=
    hs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have hs' : HasCompactSupport (fun t : ℝ => deriv h t - b * h t) := hs.deriv.sub hb
  obtain ⟨hint', heq'⟩ := Work.FTS.EllSol.FlatFT.shiftPlancherel1
    (h := fun t : ℝ => deriv h t - b * h t) hcd' hs' b
  have hpt : ∀ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2)
      * ‖slice1 (fun t : ℝ => deriv h t - b * h t) ξ‖ ^ 2
      = (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice1 h ξ‖ ^ 2 := by
    intro ξ
    rw [nrp_key hh1 hs b ξ]
    ring
  refine ⟨hint'.congr (Filter.Eventually.of_forall hpt), ?_⟩
  have hderiv' : deriv (fun t : ℝ => deriv h t - b * h t)
      = fun t : ℝ => deriv (deriv h) t - b * deriv h t := by
    funext t
    have h1 : HasDerivAt (fun t : ℝ => deriv h t) (deriv (deriv h) t) t :=
      (hdc.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => (b : ℂ) * h t) ((b : ℂ) * deriv h t) t :=
      ((hh1.differentiable (by norm_num)).differentiableAt.hasDerivAt).const_mul (b : ℂ)
    exact (h1.sub h2).deriv
  calc (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice1 h ξ‖ ^ 2)
      = ∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2)
          * ‖slice1 (fun t : ℝ => deriv h t - b * h t) ξ‖ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun ξ => (hpt ξ).symm)
    _ = ∫ t : ℝ, ‖deriv (fun t : ℝ => deriv h t - b * h t) t
          - b * ((fun t : ℝ => deriv h t - b * h t) t)‖ ^ 2 := heq'
    _ = ∫ t : ℝ, ‖deriv (deriv h) t - 2 * b * deriv h t + b ^ 2 * h t‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        have h1 : deriv (fun t : ℝ => deriv h t - b * h t) t
            = deriv (deriv h) t - b * deriv h t := by
          rw [hderiv']
        rw [h1, show (deriv (deriv h) t - b * deriv h t) - b * (deriv h t - b * h t)
            = deriv (deriv h) t - 2 * b * deriv h t + b ^ 2 * h t from by ring]

/-! ## The three Plancherel identities at an interior angle -/

/-- The first-order shifted Plancherel identity at a fixed interior angle. -/
theorem nrp_conj1 {b : ℝ} {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice u ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pz u t θ - b * u t θ) ^ 2 := by
  have hs2 := niceFlat_slice_contDiff hg hθ (n := 2) (by norm_num)
  have hcd : ContDiff ℝ 1 (fun t : ℝ => (u t θ : ℂ)) :=
    contDiff_ofReal_comp (hs2.of_le (by norm_num))
  have hsupp := niceFlat_hasCompactSupport hg θ
  have hderiv := nrp_deriv_slice hg hθ
  obtain ⟨hint, heq⟩ := Work.FTS.EllSol.FlatFT.shiftPlancherel1 hcd hsupp b
  refine ⟨hint, ?_⟩
  calc (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice u ξ θ‖ ^ 2)
      = ∫ t : ℝ,
          ‖deriv (fun t : ℝ => (u t θ : ℂ)) t - b * ((fun t : ℝ => (u t θ : ℂ)) t)‖ ^ 2 :=
        heq
    _ = ∫ t : ℝ, ‖(Work.Spaces.pz u t θ : ℂ) - b * (u t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hderiv]
    _ = ∫ t : ℝ, (Work.Spaces.pz u t θ - b * u t θ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        exact nrp_normSq_sub _ _ _

/-- The second-order shifted Plancherel identity at a fixed interior angle. -/
theorem nrp_conj2 {b : ℝ} {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice u ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ
            + b ^ 2 * u t θ) ^ 2 := by
  have hs2 := niceFlat_slice_contDiff hg hθ (n := 2) (by norm_num)
  have hcd : ContDiff ℝ 2 (fun t : ℝ => (u t θ : ℂ)) := contDiff_ofReal_comp hs2
  have hsupp := niceFlat_hasCompactSupport hg θ
  have hd1 := nrp_deriv_slice hg hθ
  have hd2 := nrp_deriv2_slice hg hθ
  obtain ⟨hint, heq⟩ := nrp_shiftPlancherel2 hcd hsupp b
  refine ⟨hint, ?_⟩
  calc (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖slice u ξ θ‖ ^ 2)
      = ∫ t : ℝ, ‖deriv (deriv (fun t : ℝ => (u t θ : ℂ))) t
          - 2 * b * deriv (fun t : ℝ => (u t θ : ℂ)) t
          + b ^ 2 * ((fun t : ℝ => (u t θ : ℂ)) t)‖ ^ 2 :=
        heq
    _ = ∫ t : ℝ, ‖(Work.Spaces.pz (Work.Spaces.pz u) t θ : ℂ)
          - 2 * b * (Work.Spaces.pz u t θ : ℂ) + b ^ 2 * (u t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hd2, hd1]
    _ = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ
          + b ^ 2 * u t θ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        exact nrp_normSq_sub2 _ _ _ _

/-- The first-order shifted Plancherel identity for `∂_θu` at a fixed interior angle. -/
theorem nrp_conj3 {b : ℝ} {u : ℝ → ℝ → ℝ} (hg : NiceFlat u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice (Work.Spaces.pth u) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice (Work.Spaces.pth u) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pz u) t θ
            - b * Work.Spaces.pth u t θ) ^ 2 := by
  have hs1 := niceFlat_slice_pth_contDiff hg hθ (n := 1) (by norm_num)
  have hcd : ContDiff ℝ 1 (fun t : ℝ => (Work.Spaces.pth u t θ : ℂ)) :=
    contDiff_ofReal_comp hs1
  have hsupp := niceFlat_hasCompactSupport_pth hg θ
  have hderiv := nrp_deriv_pth_slice hg hθ
  obtain ⟨hint, heq⟩ := Work.FTS.EllSol.FlatFT.shiftPlancherel1 hcd hsupp b
  refine ⟨hint, ?_⟩
  calc (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice (Work.Spaces.pth u) ξ θ‖ ^ 2)
      = ∫ t : ℝ, ‖deriv (fun t : ℝ => (Work.Spaces.pth u t θ : ℂ)) t
          - b * ((fun t : ℝ => (Work.Spaces.pth u t θ : ℂ)) t)‖ ^ 2 :=
        heq
    _ = ∫ t : ℝ, ‖(Work.Spaces.pz (Work.Spaces.pth u) t θ : ℂ)
          - b * (Work.Spaces.pth u t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hderiv]
    _ = ∫ t : ℝ, ‖(Work.Spaces.pth (Work.Spaces.pz u) t θ : ℂ)
          - b * (Work.Spaces.pth u t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [nrp_pz_pth_comm hg hθ t]
    _ = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pz u) t θ
          - b * Work.Spaces.pth u t θ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        exact nrp_normSq_sub _ _ _

theorem niceRangePlanch {b : ℝ} {u : ℝ → ℝ → ℝ} (hg : Work.FTS.EllSol.FlatFT.NiceFlat u) :
    (∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) ∧
        (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pz u t θ - b * u t θ) ^ 2)
    ∧ (∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable (fun ξ : ℝ => (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) ∧
        (∫ ξ : ℝ, (((2 * Real.pi * ξ) ^ 2 + b ^ 2)) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ + b ^ 2 * u t θ) ^ 2)
    ∧ (∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth u) ξ θ‖ ^ 2) ∧
        (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth u) ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pz u) t θ - b * Work.Spaces.pth u t θ) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [nrp_ae_mem_Ioo] with θ hθ
    exact nrp_conj1 hg hθ
  · filter_upwards [nrp_ae_mem_Ioo] with θ hθ
    exact nrp_conj2 hg hθ
  · filter_upwards [nrp_ae_mem_Ioo] with θ hθ
    exact nrp_conj3 hg hθ

end Work.FTS.EllSol.Shift2Flat
