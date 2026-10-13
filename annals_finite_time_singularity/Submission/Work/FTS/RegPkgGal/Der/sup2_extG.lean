/-
# `Work.FTS.RegPkgGal.Der.sup2_extG` — the second `z`-derivative of the extension `g̃`

This file bounds `∂_z² g̃` uniformly on the strip `0 < z`, `θ ∈ Iθ`, `τ ∈ [0,S]`, where
`g̃ = Work.FTS.RegPkgGal.extG g` is the extension of design §4 (`= 0` for `z ≤ 0`, the first
order Taylor jet in `τ` for `τ < 0`, `g` itself for `τ ≥ 0`).

**Route.**  For `τ ∈ [0,S]` and `z > 0`, the slice `z' ↦ g̃ z' θ τ` agrees with the slice
`z' ↦ g z' θ τ` on the *open* half line `Ioi 0`, and `∂_z` is local
(`Work.Spaces.pz_congr_of_isOpen`), so

  `∂_z²(g̃-slice)(z,θ) = ∂_z²(g-slice)(z,θ)`   for every `z > 0`,

which transfers all the bounds of the `g`-slice to the extension.  Three regimes:

* `θ = 0` and `θ = π/2`: the slice `z' ↦ g̃ z' θ τ` is *identically zero* — for `z' ≤ 0` by the
  definition of `extG`, for `z' > 0` by the angular vanishing hypothesis `hvan` — so both
  `∂_z`-derivatives vanish.
* `0 < z ≤ 2`: the hypothesis `hq2` is exactly the bound on `∂_z² g`.
* `z > 2`: here `hq2` is not available, and the bound comes from the `ℋ⁴`-norm `hHkn` through the
  interior `L^∞`–`ℋ⁴` trade-off (Elgindi's Corollary `SecondDerivativesBounded` in the interior
  class, `Work.FTS.H2.mixed_supAbsO_le`, packaged as the pointwise statement
  `mixed_le_ten_sqrt_gam` below).  The bridge from `D_z²` to `∂_z²` is the elementary identity
  `D_z²F = D_zF + z²∂_z²F` (`DzIter_two_eq_add`): both `D_zF` and `D_z²F` are `D`-derivatives of
  order `≤ 2`, hence bounded by `10/√(γ-1)·|F|_{ℋ⁴}`, and `z² > 4` gives
  `|∂_z²F| ≤ 2·(10/√(γ-1)|F|_{ℋ⁴})/4 ≤ 10/√(γ-1)|F|_{ℋ⁴}`.

The conclusion is therefore `M₂ = max Q₂ (10/√(γ-1)·C₀)` with the exponent `α` of the paper
replaced everywhere by `pExp α = 3α` (that is the exponent of the `ℋ⁴`-norm of the profiles);
`hα13 : α ≤ 1/3` is used exactly to place `pExp α` in the admissible range `(0,1]`.

The statement of `sup2_extG` is *unchanged* from the requested one; only the missing
`open scoped Real` (without which the bare `π` of the statement is not `Real.pi`) and the import
of the pointwise trade-off `Work.FTS.H2.HQ.LinfQpt` are added.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.R8
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.HQ.LinfQpt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The support, the calculus and the pointwise trade-off -/

/-- **Congruence of `∂_z²` between the extension slice and the slice of `g`.**  For `τ ≥ 0` the
two functions `z' ↦ extG g z' θ τ` and `z' ↦ g z' θ τ` agree on the open half line `Ioi 0`
(`extG_of_pos`), and `pz` is a local operator, so their second `z`-derivatives agree at every
`z > 0`. -/
private lemma pz_pz_extG_eq {g : Work.FTS.RegPkgGal.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z) :
    Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hagree : EqOn (Function.uncurry (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
      (Function.uncurry (fun z θ => g z θ τ)) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rintro ⟨z', θ'⟩ ⟨hz', -⟩
    exact Work.FTS.RegPkgGal.extG_of_pos hz' hτ
  have h1 : EqOn (Function.uncurry (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)))
      (Function.uncurry (Work.Spaces.pz (fun z θ => g z θ τ)))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    intro y hy
    exact Work.Spaces.pz_congr_of_isOpen hV hagree hy
  exact Work.Spaces.pz_congr_of_isOpen hV h1 ⟨hz, trivial⟩

/-- **The bridge `D_z² = D_z + z²∂_z²`.**  If the `z`-slice of `pz F` is differentiable at `z`,
then `D_z²F = D_zF + z²∂_z²F` at `(z,θ)`.  (This is the `n = 2` case of the expansion of
`D_z = z∂_z` in terms of `z^k∂_z^k`, with Stirling coefficients `S(2,1) = S(2,2) = 1`; only the
product rule is needed, so no smoothness of higher order is required.) -/
private lemma DzIter_two_eq_add (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z) :
    Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
  have hdmul : deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
    have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id' z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz F z' θ)
        (Work.Spaces.pz (Work.Spaces.pz F) z θ) z := hd.hasDerivAt
    have h3 : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz F z' θ)
        (1 * Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ) z :=
      (h1.mul h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext z'; rfl))
    simpa only [one_mul] using h3.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = z * Work.Spaces.pz F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ
  rw [hdmul]
  ring

/-- The `z`-slice of `pz F` is differentiable at every interior point `z > -1` of a `SmoothQuad`
function `F` (at an angle `θ ∈ (0,π/2)`): the slice of `F` is `C^∞` on `Ioi (-1)`, hence so is
its derivative. -/
private lemma differentiableAt_pz_slice {F : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad F) {z θ : ℝ} (hz : z ∈ Set.Ioi (-1))
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z := by
  have hsl : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => F z θ) (Set.Ioi (-1)) :=
    hsq.curry_z hθ
  have hd : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (deriv (fun z => F z θ)) (Set.Ioi (-1)) :=
    hsl.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
  exact (hd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- **The interior `L^∞`–`ℋ⁴` trade-off, pointwise form, for every mixed slot of order `≤ 2`.**
For `f` in the interior class `Work.FTS.Nonlin.RegQ α 4` (`= SmoothQuad f ∧ HkMem α 4 f ∧
BdryTraces α 4 f`) and `a + b ≤ 2`,

  `|D_z^b D_θ^a f(z,θ)| ≤ 10/√(γ-1)·|f|_{ℋ⁴}`   for `z > 0`, `0 < θ < π/2`.

This is the `(b,a) = (0,0)` statement `Work.FTS.Nonlinear.Pieces.rl1Tools.abs_le_ten_sqrt_gam`
of the tree, generalized to every slot of order `≤ 2`: the *pointwise* bound
`Work.FTS.H2.HQ.LinfQpt` (with the two one-dimensional Hardy inequalities `HardyThetaO` and
`hardyZ_open` supplied) gives such a bound with an *unknown* positive constant, which is enough
to know that `supAbsO` is not the junk value attached to an unbounded set; `le_supAbsO` then
turns the pointwise bound into the statement `le supAbsO`, and `Work.FTS.H2.mixed_supAbsO_le`
supplies the explicit constant `10`. -/
theorem mixed_le_ten_sqrt_gam {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.Nonlin.RegQ α 4 f) (b a : ℕ) (hab : a + b ≤ 2) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, _hCpos, hL⟩ := Work.FTS.H2.HQ.LinfQpt
  -- the two one-dimensional Hardy inequalities, in the shapes `LinfQpt` asks them for
  have hAng : ∀ (u : ℝ → ℝ → ℝ) (z : ℝ), Work.FTS.LocData.SmoothQuad u →
      z ∈ Set.Ioi (-1) → Tendsto (fun θ => u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      IntegrableOn (fun σ => (Work.Spaces.pth u z σ) ^ 2
        * Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), u z θ ^ 2
        ≤ 100 / (Work.Spaces.gam α - 1) * ∫ σ in Work.Spaces.Iθ,
            Work.Spaces.pth u z σ ^ 2 * Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α) :=
    fun u z hu hz h0 hint => Work.FTS.H2.HardyThetaO α hα hα1 u z hu hz h0 hint
  have hRad : ∀ (v : ℝ → ℝ), ContDiffOn ℝ 1 v (Set.Ioi 0) → Tendsto v atTop (nhds 0) →
      IntegrableOn (fun s => (s * deriv v s) ^ 2 * Work.Spaces.w s ^ 2) Work.Spaces.Iz →
      ∀ z ∈ Set.Ioi 0, v z ^ 2
        ≤ ∫ s in Work.Spaces.Iz, (s * deriv v s) ^ 2 * Work.Spaces.w s ^ 2 :=
    fun v hcd hdec hint => Work.FTS.H2.hardyZ_open hcd hdec hint
  -- a uniform (but numerically unknown) bound on the open quadrant
  have hglobal : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |Work.Spaces.mixed b a f z' θ'| ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.Nonlin.Xn α f := by
    intro z' θ' hz' hθ' hθ''
    exact hL α f b a hα hα1 hab hreg hAng hRad z' hz' θ' hθ' hθ''
  intro z hz θ hθ0 hθ1
  have hsup : |Work.Spaces.mixed b a f z θ| ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed b a f) :=
    Work.FTS.H2.le_supAbsO hz hθ0 hθ1 hglobal
  have hsupb : Work.FTS.H2.supAbsO (Work.Spaces.mixed b a f)
      ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f :=
    Work.FTS.H2.mixed_supAbsO_le α f hα hα1 hreg.1 hreg.2.1 hreg.2.2 b a hab
  exact le_trans hsup hsupb

/-! ## The target -/

theorem sup2_extG {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hS : 0 < S)
    (hRQ : ∀ τ ∈ Set.Icc 0 S, Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 4
      (Work.FTS.Regularity.gSlice g τ))
    (hHkn : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ ∈ Set.Icc 0 S,
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (Work.FTS.Regularity.gSlice g τ) ≤ C₀)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0)
    (hq2 : ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 < z → z ≤ 2 →
      |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ| ≤ Q₂) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ| ≤ M₂ := by
  obtain ⟨Q₂, hQ₂nn, hQ₂bd⟩ := hq2
  obtain ⟨C₀, hC₀nn, hC₀bd⟩ := hHkn
  -- the exponent of the `ℋ⁴`-norm is `pExp α = 3α ∈ (0,1]`, and the constant of the trade-off
  have hα' : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hα1' : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hcoef_nn : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨max Q₂ (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀),
    le_trans hQ₂nn (le_max_left _ _), ?_⟩
  intro τ hτ z θ hz hθI
  -- the extension slice agrees with the `g`-slice on `Ioi 0`, so `∂_z²` agrees too
  have hcongr : Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ := pz_pz_extG_eq hτ.1 hz
  rcases lt_or_eq_of_le hθI.1 with hθpos | hθzero
  · rcases lt_or_eq_of_le hθI.2 with hθlt | hθtop
    · -- the interior angle: `hq2` for `z ≤ 2`, the `ℋ⁴`-norm for `z > 2`
      rw [hcongr]
      rcases le_or_gt z 2 with hz2 | hz2
      · exact le_trans (hQ₂bd τ hτ θ hθI z hz hz2) (le_max_left _ _)
      · have hsq : Work.FTS.LocData.SmoothQuad (Work.FTS.Regularity.gSlice g τ) := (hRQ τ hτ).1
        have hb2 := mixed_le_ten_sqrt_gam hα' hα1' (hRQ τ hτ) 2 0 (by norm_num) z hz θ hθpos hθlt
        have hb1 := mixed_le_ten_sqrt_gam hα' hα1' (hRQ τ hτ) 1 0 (by norm_num) z hz θ hθpos hθlt
        have hbd2 : |Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ|
            ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ :=
          le_trans hb2 (mul_le_mul_of_nonneg_left (hC₀bd τ hτ) hcoef_nn)
        have hbd1 : |Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ|
            ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ :=
          le_trans hb1 (mul_le_mul_of_nonneg_left (hC₀bd τ hτ) hcoef_nn)
        -- the identity `D_z² = D_z + z²∂_z²`
        have hdiff : DifferentiableAt ℝ
            (fun z' => Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z' θ) z :=
          differentiableAt_pz_slice hsq (by simp only [Set.mem_Ioi]; linarith) ⟨hθpos, hθlt⟩
        have hid := DzIter_two_eq_add (Work.FTS.Regularity.gSlice g τ) hdiff
        have hmul : z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ
            = Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ
              - Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ := by
          rw [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_right]
          linarith [hid]
        have hΔ : |Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ
              - Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ|
            ≤ 2 * (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) := by
          calc |Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ
                - Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ|
              = |Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ
                  + (-Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ)| := by ring_nf
            _ ≤ |Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ|
                  + |-Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ| :=
                abs_add_le _ _
            _ = |Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ|
                  + |Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ| := by rw [abs_neg]
            _ ≤ (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀)
                  + (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) :=
                add_le_add hbd2 hbd1
            _ = 2 * (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) := by
                ring
        have hzsq : (4 : ℝ) ≤ z ^ 2 := by nlinarith
        have hBnn : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ :=
          mul_nonneg hcoef_nn hC₀nn
        have hfinal : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
            ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ := by
          have h1 : z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
              ≤ 2 * (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) := by
            rw [← abs_of_pos (by positivity : (0 : ℝ) < z ^ 2), ← abs_mul, hmul]
            exact hΔ
          have h2 : 4 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
              ≤ z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ| :=
            mul_le_mul_of_nonneg_right hzsq (abs_nonneg _)
          nlinarith [le_trans h2 h1, hBnn, abs_nonneg (Work.Spaces.pz (Work.Spaces.pz
            (Work.FTS.Regularity.gSlice g τ)) z θ)]
        exact le_trans hfinal (le_max_right _ _)
    · -- the angle `θ = π/2`: the extension slice is identically zero in `z`
      have hzero : (fun z' : ℝ => Work.FTS.RegPkgGal.extG g z' θ τ) = fun _ => (0 : ℝ) := by
        funext z'
        rcases le_or_gt z' 0 with hz' | hz'
        · exact Work.FTS.RegPkgGal.extG_of_nonpos hz'
        · rw [Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1, hθtop]
          exact (hvan τ hτ z' hz'.le).2
      have hpz0 : ∀ z' : ℝ,
          Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ = 0 := by
        intro z'
        show deriv (fun z'' => Work.FTS.RegPkgGal.extG g z'' θ τ) z' = 0
        rw [hzero, deriv_const]
      have hpp : Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
          = 0 := by
        show deriv (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ) z
          = 0
        rw [show (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ)
            = fun _ => (0 : ℝ) from funext hpz0, deriv_const]
      rw [hpp, abs_zero]
      exact le_trans hQ₂nn (le_max_left _ _)
  · -- the angle `θ = 0`: the extension slice is identically zero in `z`
    have hθ0 : θ = 0 := hθzero.symm
    have hzero : (fun z' : ℝ => Work.FTS.RegPkgGal.extG g z' θ τ) = fun _ => (0 : ℝ) := by
      funext z'
      rcases le_or_gt z' 0 with hz' | hz'
      · exact Work.FTS.RegPkgGal.extG_of_nonpos hz'
      · rw [Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1, hθ0]
        exact (hvan τ hτ z' hz'.le).1
    have hpz0 : ∀ z' : ℝ,
        Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ = 0 := by
      intro z'
      show deriv (fun z'' => Work.FTS.RegPkgGal.extG g z'' θ τ) z' = 0
      rw [hzero, deriv_const]
    have hpp : Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
        = 0 := by
      show deriv (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ) z
        = 0
      rw [show (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ)
          = fun _ => (0 : ℝ) from funext hpz0, deriv_const]
    rw [hpp, abs_zero]
    exact le_trans hQ₂nn (le_max_left _ _)

end Work.FTS.RegPkgGal.Der
