import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.H2W.LocC.LzeroQuantSelf
import Submission.Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3LocReduction
import Submission.Work.FTS.EllipticEst.H2W.SliceMassExternal
import Submission.Work.FTS.EllipticEst.H2W.sliceSourceMassBound_of_external
import Submission.Work.FTS.EllipticEst.H2W.SliceB.pzSecGrowthLoc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W.pzIterBoxIntegrable` — slice and box integrability of the first four `z`-slices

Target: for a datum `(F, Ψ)` of the weak class `Work.FTS.EllipticEst.WeakPos2 α F Ψ`
(`0 < α ≤ 1/4`), for almost every `z₀ > 0` there is `ε > 0` with `ε < z₀` such that

* for every `j ≤ 3` and every `z` in `(z₀ - ε, z₀ + ε)` the angular slice
  `θ ↦ ∂_z^jΨ(z,θ)·sinθcos²θ` is integrable on `Iθ = [0, π/2]`;
* for every `j ≤ 3` the function `(s,θ) ↦ |∂_z^jΨ(s,θ)|·sinθcos²θ` is integrable on the
  product `(z₀ - ε, z₀ + ε] × Iθ`.

## What is proved here, and what is delegated

### STATUS (this stretch): the target is the chapter's bottleneck node, and its conclusion is
### available from any of the *documented* inputs below

The target's statement is **not** derivable from `WeakPos2` by any argument available in the
tree: `WeakPos2` carries no honesty for the left-hand-side slots of `Ψ` (`∂_z^jΨ·sinθcos²θ`,
`j ≤ 3` *are* the quantities the target asserts to be honest), the source-tower
`Lzero1(∂_z^mΨ) = ∂_z^mF + α²z²∂_z^{m+2}Ψ + …` has no base case because `HkMem α 2 F` stops at
level `2`, and all of the chapter's weak-class estimates are inequalities between *totalised*
(junk-tolerant) integrals.  The detailed analysis, the precedents (the verdict recorded for the
whole node family is *"mis-stated: the hypothesis list is too weak"*, never *"mathematically
false"*), the source theorem's own hypotheses (the paper's `prop:L2` uses *the unique `L²`
solution* and `R²Ψ → 0` at `R = 0`) and the dead ends are in
`Submission/Work/FTS/EllipticEst/H2W/NOTES_pzIterBoxIntegrable_state2.md` and
`.../WeakPureAux/NOTES_cascade.md`.

What IS available (all proved in this file or in the tree, all axiom-clean) is the target's
conclusion from each of the following inputs, on top of `WeakPos2 α F Ψ`:

| input | consumer lemma |
|---|---|
| `HkMem α 0 (∂_θθ(∂_z^jΨ))`, `j ≤ 3` | `H2W/pzIterBoxIntegrable_of_slots` |
| locally uniform bound on `∫_θ (∂_θ(pzIter m Ψ)(z,·))² sin(2θ)^{-η}`, `m ≤ 3` | `pzIterBoxIntegrable_of_locGradBound` |
| locally uniform bound on `∫_θ (∂_θθ(pzIter m Ψ)(z,·))² sin(2θ)^{-η}`, `m ≤ 3` | `pzIterBoxIntegrable_of_locSecBound` |
| locally uniform pole bound `|∂_z^jΨ| ≤ C(θ⁻¹+(π/2-θ)⁻¹)` | `pzIterBoxIntegrable_of_poleBoundDatum` |
| `SliceSourceMassBound Ψ` | `pzIterBoxIntegrable_of_sourceMass` |
| `SliceMassExternal α F Ψ` (ψ-mass form of the paper's `R²Ψ → 0`) | `pzIterBoxIntegrable_of_externalMass` |
| unweighted `L²`-honesty of `∂_θθ(∂_z^jΨ)`, `j ≤ 3` (per `z` and on the box) | `pzIterBoxIntegrable_of_secDerivSq` (module `H2W/pzIterBoxIntegrableOfSecDerivSq`) |
| the single slot `HkMem α 3 (pthIter 2 Ψ)` | `pzIterBoxIntegrable_of_hkMem3` (same module) |

### The reductions proved in this file

Four reductions are proved, of strictly decreasing strength in their input (the first is the
sharpest and is the one the project should consume):

* **`pzIterBoxIntegrable_of_growth`** — from the *locally uniform angular growth (pole) bound*
  `|∂_z^jΨ(z,θ)| ≤ C·(θ⁻¹ + (π/2-θ)⁻¹)` on a neighbourhood of a.e. `z₀` (with a single `C`).  The
  elementary bound `(θ⁻¹ + (π/2-θ)⁻¹)·sinθcos²θ ≤ 1 + π/2` turns the growth bound into the
  *uniform* bound `|∂_z^jΨ·sinθcos²θ| ≤ C(1+π/2)` on the whole box, the box has finite measure, so
  `Integrable.of_bound` gives both conclusions.
* **`pzIterBoxIntegrable_of_locBound`** — from the strictly weaker input that the *`θ`-integrals*
  `∫⁻_θ |∂_z^jΨ(z,θ)|·|sinθcos²θ|` (`j ≤ 3`) are *locally uniformly bounded* on a neighbourhood of
  a.e. `z₀`.  This is the weakest local-uniformity statement that implies the target: the pole
  bound gives it (integrating `C(θ⁻¹+(π/2-θ)⁻¹)` against `sinθcos²θ` gives `C(1+π/2)`), while the
  *`θ`-pointwise* information is discarded.  The pointwise conjunct comes from `M < ⊤` via
  `hasFiniteIntegral_iff_norm`; the box conjunct from Tonelli (`lintegral_prod`) and the finiteness
  of the measure of the box.
* **`pzIterBoxIntegrable_of_sourceMass`** — from a locally uniform bound on the **source mass**
  `∫_{Iθ} (sinθcos²θ·|Lzero1(∂_z^mΨ)(z,·)| + |∂_z^mΨ(z,π/4)| + |∂_θ∂_z^mΨ(z,π/4)|)`, `m ≤ 3` (the
  project's `SliceSourceMassBound` shape).  This is proved through the new node
  `poleBound_of_sourceMass`, which applies the *proved quantitative* one-variable theorem
  `H2W.LocC.lzeroGrowthQuantL1Self` (`H2W/LocC/LzeroQuantSelf.lean`, axiom-clean) slice by slice —
  the universal constant is what makes the pole bound uniform in `z`.
* **`integrableOn_abs_mul_sinCos2_of_sq_secondDeriv`** (the *bridge*) — a `C²` function on
  `(0,π/2)` with square-integrable second derivative is bounded, hence `sinθcos²θ`-integrable.
  This is the link from the *left-hand-side honesty slots* of the paper's elliptic estimates
  (`HkMem α 0 (∂_θθ·)`, `HkMem α 0 (z²∂_zz·)`) to the slice honesty.

The intended assembly of the target is then the delegated node
`H2W/pzIterBoxIntegrable_of_slots` (`Submission/.../H2W/pzIterBoxIntegrable_of_slots.lean`):

  `HkMem α 0 (∂_θθ(∂_z^jΨ))` for every `j ≤ 3`  **⟹**  the target,

via the bridge.  Indeed `HkMem α 0 g` has a *pointwise-in-`z`* first conjunct, so for every
`z > 0` one has `∫_θ (∂_θθ(∂_z^jΨ)(z,θ))² dθ < ∞` (drop the weight `w²/sin^η ≥ 1`), the bridge
gives `∫_θ |∂_z^jΨ(z,θ)|·sinθcos²θ dθ < ∞` for *every* `z > 0` (so the first conjunct of the
target holds on the whole neighbourhood), and the box conjunct follows from Tonelli together
with the bound `|u θ| ≤ |u(π/4)| + (π/2)(|u'(π/4)| + ∫_θ|u''|)` that the bridge produces:
`|∂_z^jΨ(s,π/4)|` and `|∂_θ∂_z^jΨ(s,π/4)|` are continuous in `s` (hence locally integrable), and
`∫_θ|∂_θ²∂_z^jΨ(s,θ)|dθ ≤ √Q(s)·√(∫sin^η)/w(s)` with `Q(s) = HkIntegrand α 0 (∂_θ²∂_z^jΨ) s`
globally `L¹` by the second conjunct of `HkMem`, so that Cauchy–Schwarz on a finite `s`-interval
makes `s ↦ ∫_θ|∂_z^jΨ(s,θ)|·sinθcos²θ dθ` locally integrable.  (This corrects an earlier remark
of this module: the local uniformity needed for the box conjunct *is* supplied by the
`HkMem`-honesty of the `θθ`-slots, because `HkMem` controls the global `z`-integral; what is
*not* sufficient is a merely a.e.-in-`z` growth bound — see below.)

## Why a local uniformity is needed at all, and where it comes from

`∫_θ |f(θ)|·sinθcos²θ` is finite for any `f` with `|f(θ)| = O((π/2-θ)^(-3+δ))`, so the purely
*a.e.-in-`z`* bound `|∂_z^jΨ(z,θ)| ≤ C(z)(θ⁻¹ + (π/2-θ)⁻¹)` — the shape of the project's
`SliceGrowth` — gives the pointwise slice integrability for a.e. `z`, but *not* the box
statement: the constant `C(z)` may be finite a.e. and yet have infinite integral on every
neighbourhood of a.e. `z₀` (`1/|z - z₀|` is the model example: finite everywhere, l.s.c., but not
locally integrable), and then the box integral of `|∂_z^jΨ|·sinθcos²θ` need not be finite.  Even
more, a *lower semicontinuous, everywhere finite* function can be locally unbounded
(`f z = 1/|z|` for `z ≠ 0`, `f 0 = 0`), so the *closedness* of the set `{z : the slice of ∂_z^jΨ
is not integrable}` (which does follow from Fatou) only yields the *pointwise* conjunct, not the
box conjunct.  Hence the target genuinely needs a locally uniform input; what the analysis above
adds is that the *global `z`-integral* half of `HkMem` supplies it, so the honest slots
`HkMem α 0 (∂_θθ(∂_z^jΨ))` (the left-hand-side honesty of the paper's elliptic estimates) are
enough, and the two reductions below isolate the weakest *self-contained* local-uniformity
inputs (the pole bound, and the local boundedness of the `θ`-integrals).
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary facts about the angular profile `sinθcos²θ` -/

/-- `sinθcos²θ` vanishes at `θ = 0`. -/
private theorem sinCos2_zero_left : Work.Elliptic.sinCos2 0 = 0 := by
  simp [Work.Elliptic.sinCos2]

/-- `sinθcos²θ` vanishes at `θ = π/2`. -/
private theorem sinCos2_zero_right : Work.Elliptic.sinCos2 (Real.pi / 2) = 0 := by
  simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]

/-- `sinθcos²θ` is nonnegative on `(0,π/2)`. -/
private theorem sinCos2_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  have h1 : 0 ≤ Real.sin θ :=
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).le
  have h2 : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).le
  rw [Work.Elliptic.sinCos2]
  positivity

/-- `θ ↦ sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2_fts : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- **The comparison function is bounded against `sinθcos²θ`.**

`(θ⁻¹ + (π/2-θ)⁻¹)·sinθcos²θ ≤ 1 + π/2` on `(0,π/2)`: the first summand is
`θ⁻¹sinθ·cos²θ ≤ 1` (since `sinθ ≤ θ` and `cos²θ ≤ 1`), and the second is
`(π/2-θ)⁻¹cos²θ·sinθ ≤ π/2`, because `cosθ = sin(π/2-θ) ≤ π/2-θ`.  Consequently a growth bound
`|f θ| ≤ C(θ⁻¹ + (π/2-θ)⁻¹)` gives the *uniform* bound `|f θ·sinθcos²θ| ≤ C(1+π/2)`, which is
what makes the box integrability immediate on a box of finite measure. -/
private theorem rho_mul_sinCos2_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) * Work.Elliptic.sinCos2 θ ≤ 1 + Real.pi / 2 := by
  obtain ⟨h0, h1⟩ := hθ
  have hτ : 0 < Real.pi / 2 - θ := by linarith
  have hcos_nn : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩).le
  have h1' : θ⁻¹ * Real.sin θ ≤ 1 := by
    rw [inv_mul_le_iff₀ h0]
    simpa using Real.sin_le h0.le
  have hcos : Real.cos θ ≤ Real.pi / 2 - θ := by
    have h : Real.sin (Real.pi / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
    rw [← h]
    exact Real.sin_le hτ.le
  have hA : θ⁻¹ * Work.Elliptic.sinCos2 θ ≤ 1 := by
    show θ⁻¹ * (Real.sin θ * Real.cos θ ^ 2) ≤ 1
    calc θ⁻¹ * (Real.sin θ * Real.cos θ ^ 2)
        = (θ⁻¹ * Real.sin θ) * Real.cos θ ^ 2 := by ring
      _ ≤ 1 * 1 :=
          mul_le_mul h1' (Real.cos_sq_le_one θ) (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  have hstep : (Real.pi / 2 - θ)⁻¹ * Real.cos θ ^ 2 ≤ Real.pi / 2 - θ := by
    have h2' : Real.cos θ ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 := pow_le_pow_left₀ hcos_nn hcos 2
    calc (Real.pi / 2 - θ)⁻¹ * Real.cos θ ^ 2
        ≤ (Real.pi / 2 - θ)⁻¹ * (Real.pi / 2 - θ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2' (by positivity)
      _ = Real.pi / 2 - θ := by
          rw [sq, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hτ), one_mul]
  have hB : (Real.pi / 2 - θ)⁻¹ * Work.Elliptic.sinCos2 θ ≤ Real.pi / 2 := by
    show (Real.pi / 2 - θ)⁻¹ * (Real.sin θ * Real.cos θ ^ 2) ≤ Real.pi / 2
    rw [show (Real.pi / 2 - θ)⁻¹ * (Real.sin θ * Real.cos θ ^ 2)
        = Real.sin θ * ((Real.pi / 2 - θ)⁻¹ * Real.cos θ ^ 2) from by ring]
    calc Real.sin θ * ((Real.pi / 2 - θ)⁻¹ * Real.cos θ ^ 2)
        ≤ 1 * (Real.pi / 2 - θ) :=
          mul_le_mul (Real.sin_le_one θ) hstep (by positivity) zero_le_one
      _ ≤ Real.pi / 2 := by linarith
  show (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) * (Real.sin θ * Real.cos θ ^ 2) ≤ 1 + Real.pi / 2
  calc (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) * (Real.sin θ * Real.cos θ ^ 2)
      = θ⁻¹ * (Real.sin θ * Real.cos θ ^ 2)
        + (Real.pi / 2 - θ)⁻¹ * (Real.sin θ * Real.cos θ ^ 2) := by ring
    _ ≤ 1 + Real.pi / 2 := add_le_add hA hB

/-! ## Two integrability criteria (bounded functions on finite-measure sets) -/

/-- The angular interval `Iθ = [0, π/2]` has finite Lebesgue measure. -/
private theorem volume_Iθ_lt_top_fts : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- A function on `Iθ` bounded by a constant is integrable on `Iθ`, which has finite measure. -/
private theorem integrableOn_of_bound_Iθ {f : ℝ → ℝ} {K : ℝ}
    (hae : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ))
    (hb : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ K) :
    IntegrableOn f Work.Spaces.Iθ := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_Iθ_lt_top_fts⟩
  rw [IntegrableOn]
  refine MeasureTheory.Integrable.of_bound hae K ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs]
  exact hb θ hθ

/-- A function on the box `(a,b] × Iθ`, bounded by a constant, is integrable there: the box has
finite measure. -/
private theorem integrable_box_of_bound {f : ℝ × ℝ → ℝ} {a b K : ℝ}
    (hae : AEStronglyMeasurable f
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)))
    (hb : ∀ p ∈ Set.Ioc a b ×ˢ Work.Spaces.Iθ, |f p| ≤ K) :
    Integrable f ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hfin : ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) Set.univ
      ≠ ⊤ := by
    rw [Measure.prod_apply MeasurableSet.univ]
    simp only [Set.preimage_univ]
    rw [lintegral_const, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      Real.volume_Ioc, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    ⟨lt_top_iff_ne_top.mpr hfin⟩
  have hmem : ∀ᵐ p ∂((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)),
      p ∈ Set.Ioc a b ×ˢ Work.Spaces.Iθ := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Icc)
  refine MeasureTheory.Integrable.of_bound hae K ?_
  filter_upwards [hmem] with p hp
  rw [Real.norm_eq_abs]
  exact hb p hp

/-! ## The elementary bridge: `L²`-control of `∂_θ²u` implies `sinθcos²θ`-honesty

The following lemma is the *link* between the left-hand-side honesty slots of the paper's
elliptic estimates (`HkMem α 0 (∂_θθu)`, `HkMem α 0 (z²∂_zzu)`) and the `sinθcos²θ`-integrability
of the angular slices: a `C²` function on the open interval whose second derivative is
square-integrable is *bounded*, by two applications of the one-dimensional fundamental theorem
of calculus (each losing the factor `π/2`, from Cauchy–Schwarz on the integral of `|u''|`). -/

/-- **The bridge.**  A `C²` function on `(0,π/2)` with square-integrable second derivative has
`sinθcos²θ`-integrable absolute value: it is in fact bounded, by
`|u θ| ≤ |u(π/4)| + (π/2)(|u'(π/4)| + ∫_{Iθ}|u''|)`. -/
theorem integrableOn_abs_mul_sinCos2_of_sq_secondDeriv {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun θ' => deriv u θ') θ) ^ 2)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_Iθ_lt_top_fts⟩
  have hquarter : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have h0d : ContDiffOn ℝ 0 (deriv (fun θ' => deriv u θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
  have hcont2 : ContinuousOn (fun θ : ℝ => deriv (fun θ' => deriv u θ') θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h0d.continuousOn
  have haesm : AEStronglyMeasurable (fun θ : ℝ => deriv (fun θ' => deriv u θ') θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have h3 : AEStronglyMeasurable (fun θ : ℝ => deriv (fun θ' => deriv u θ') θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hcont2.aestronglyMeasurable measurableSet_Ioo
    rw [Work.Spaces.Iθ, (Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))).symm]
    exact h3
  have h2abs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun θ' => deriv u θ') θ|) Work.Spaces.Iθ := by
    have hg : MeasureTheory.IntegrableOn
        (fun θ : ℝ => ((deriv (fun θ' => deriv u θ') θ) ^ 2 + 1) / 2) Work.Spaces.Iθ := by
      have h1' : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
        integrable_const 1
      have hsum := (h2.const_mul (1 / 2 : ℝ)).add (h1'.const_mul (1 / 2 : ℝ))
      refine hsum.congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Pi.add_apply]; ring
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · refine haesm.norm.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show ‖deriv (fun θ' => deriv u θ') θ‖ = |deriv (fun θ' => deriv u θ') θ|
      rw [Real.norm_eq_abs]
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_abs]
      nlinarith [sq_nonneg (|deriv (fun θ' => deriv u θ') θ| - 1),
        sq_abs (deriv (fun θ' => deriv u θ') θ)]
  have h2int : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun θ' => deriv u θ') θ)
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' h2abs haesm (by
      filter_upwards with θ
      simpa using le_abs_self (deriv (fun θ' => deriv u θ') θ))
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, |deriv (fun θ' => deriv u θ') θ| with hA
  have hAnn : 0 ≤ A := integral_nonneg (fun θ => abs_nonneg _)
  have hAint : IntervalIntegrable (fun θ : ℝ => |deriv (fun θ' => deriv u θ') θ|)
      volume (0 : ℝ) (Real.pi / 2) :=
    (h2abs.mono_set (s := uIcc (0 : ℝ) (Real.pi / 2)) (by
      intro x hx
      rw [uIcc_of_le (by linarith [Real.pi_pos])] at hx
      exact ⟨hx.1, hx.2⟩)).intervalIntegrable
  have hsub_int : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      ∫ θ in a..b, |deriv (fun θ' => deriv u θ') θ| ≤ A := by
    intro a b ha hab hb
    have hA' : A = ∫ θ in (0 : ℝ)..(Real.pi / 2), |deriv (fun θ' => deriv u θ') θ| := by
      rw [hA, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), Work.Spaces.Iθ]
      exact MeasureTheory.integral_Icc_eq_integral_Ioc' (μ := volume)
        (x := (0 : ℝ)) (y := Real.pi / 2)
        (f := fun θ => |deriv (fun θ' => deriv u θ') θ|) (by simp)
    rw [hA']
    exact intervalIntegral.integral_mono_interval ha hab hb
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hAint
  have hftc1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u x - deriv u (Real.pi / 4)| ≤ A := by
    intro x hx
    have hsub : uIcc (Real.pi / 4) x ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      (convex_Ioo (0 : ℝ) (Real.pi / 2)).ordConnected.uIcc_subset hquarter hx
    have hsubI : uIcc (Real.pi / 4) x ⊆ Work.Spaces.Iθ := fun y hy =>
      ⟨(hsub hy).1.le, (hsub hy).2.le⟩
    have hderiv : ∀ y ∈ uIcc (Real.pi / 4) x,
        HasDerivAt (deriv u) (deriv (fun θ' => deriv u θ') y) y := by
      intro y hy
      exact (((h1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds (hsub hy)))).hasDerivAt
    have hint : IntervalIntegrable (fun θ => deriv (fun θ' => deriv u θ') θ) volume
        (Real.pi / 4) x := (h2int.mono_set hsubI).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rcases le_total (Real.pi / 4) x with hle | hle
    · have hf := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
          (f := fun θ => deriv (fun θ' => deriv u θ') θ) hle
      rw [hftc] at hf
      exact hf.trans (hsub_int (Real.pi / 4) x (by linarith [Real.pi_pos]) hle (le_of_lt hx.2))
    · have hftc' : ∫ θ in x..(Real.pi / 4), deriv (fun θ' => deriv u θ') θ
            = deriv u (Real.pi / 4) - deriv u x := by
        rw [intervalIntegral.integral_symm, hftc]; ring
      have hf := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
          (f := fun θ => deriv (fun θ' => deriv u θ') θ) hle
      rw [hftc', abs_sub_comm] at hf
      exact hf.trans (hsub_int x (Real.pi / 4) (le_of_lt hx.1) hle (by linarith [Real.pi_pos]))
  have hderiv_le : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u x| ≤ |deriv u (Real.pi / 4)| + A := by
    intro x hx
    have h := hftc1 x hx
    have h2' : |deriv u x| ≤ |deriv u x - deriv u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := by
      have h3 := abs_sub_le (deriv u x) (deriv u (Real.pi / 4)) 0
      simp only [sub_zero] at h3
      linarith
    linarith
  have hftc2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u x - u (Real.pi / 4)| ≤ (Real.pi / 2) * (|deriv u (Real.pi / 4)| + A) := by
    intro x hx
    have hsub : uIcc (Real.pi / 4) x ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      (convex_Ioo (0 : ℝ) (Real.pi / 2)).ordConnected.uIcc_subset hquarter hx
    have hderiv : ∀ y ∈ uIcc (Real.pi / 4) x, HasDerivAt u (deriv u y) y := by
      intro y hy
      exact (((hu.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds (hsub hy)))).hasDerivAt
    have hint : IntervalIntegrable (deriv u) volume (Real.pi / 4) x :=
      (h1.continuousOn.mono hsub).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rcases le_total (Real.pi / 4) x with hle | hle
    · have h1' : |u x - u (Real.pi / 4)| ≤ ∫ θ in (Real.pi / 4)..x, |deriv u θ| := by
        have hf := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
          (f := deriv u) hle
        rw [hftc] at hf
        exact hf
      have h2' : ∫ θ in (Real.pi / 4)..x, |deriv u θ| ≤
          ∫ θ in (Real.pi / 4)..x, (|deriv u (Real.pi / 4)| + A) := by
        refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
        · exact (h1.continuousOn.abs.mono hsub).intervalIntegrable
        · exact intervalIntegrable_const
        · intro y hy
          exact hderiv_le y (hsub (by rw [uIcc_of_le hle]; exact hy))
      have h3' : ∫ θ in (Real.pi / 4)..x, (|deriv u (Real.pi / 4)| + A)
          = (|deriv u (Real.pi / 4)| + A) * (x - Real.pi / 4) := by
        rw [intervalIntegral.integral_const]; ring
      have h4' : (|deriv u (Real.pi / 4)| + A) * (x - Real.pi / 4)
          ≤ (Real.pi / 2) * (|deriv u (Real.pi / 4)| + A) := by
        have hx' : x - Real.pi / 4 ≤ Real.pi / 2 := by linarith [hx.2]
        nlinarith [abs_nonneg (deriv u (Real.pi / 4)), hAnn]
      linarith
    · have hsub' : uIcc x (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        (convex_Ioo (0 : ℝ) (Real.pi / 2)).ordConnected.uIcc_subset hx hquarter
      have h1' : |u x - u (Real.pi / 4)| = |∫ θ in x..(Real.pi / 4), deriv u θ| := by
        have hftc' : ∫ θ in x..(Real.pi / 4), deriv u θ = u (Real.pi / 4) - u x := by
          rw [intervalIntegral.integral_symm, hftc]; ring
        rw [hftc', abs_sub_comm]
      have h2' : |∫ θ in x..(Real.pi / 4), deriv u θ| ≤
          ∫ θ in x..(Real.pi / 4), |deriv u θ| :=
        intervalIntegral.abs_integral_le_integral_abs (μ := volume) hle
      have h3' : ∫ θ in x..(Real.pi / 4), |deriv u θ| ≤
          ∫ θ in x..(Real.pi / 4), (|deriv u (Real.pi / 4)| + A) := by
        refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
        · exact (h1.continuousOn.abs.mono hsub').intervalIntegrable
        · exact intervalIntegrable_const
        · intro y hy
          exact hderiv_le y (hsub' (by rw [uIcc_of_le hle]; exact hy))
      have h4' : ∫ θ in x..(Real.pi / 4), (|deriv u (Real.pi / 4)| + A)
          = (|deriv u (Real.pi / 4)| + A) * (Real.pi / 4 - x) := by
        rw [intervalIntegral.integral_const]; ring
      have h5' : (|deriv u (Real.pi / 4)| + A) * (Real.pi / 4 - x)
          ≤ (Real.pi / 2) * (|deriv u (Real.pi / 4)| + A) := by
        have hx' : Real.pi / 4 - x ≤ Real.pi / 2 := by linarith [hx.1]
        nlinarith [abs_nonneg (deriv u (Real.pi / 4)), hAnn]
      linarith
  set C : ℝ := |u (Real.pi / 4)|
    + (Real.pi / 2) * (|deriv u (Real.pi / 4)| + A) with hC
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hub : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ C := by
    intro θ hθ
    have h := hftc2 θ hθ
    have h2' : |u θ| ≤ |u θ - u (Real.pi / 4)| + |u (Real.pi / 4)| := by
      have h3 := abs_sub_le (u θ) (u (Real.pi / 4)) 0
      simp only [sub_zero] at h3
      linarith
    rw [hC]; linarith
  refine MeasureTheory.Integrable.mono' (g := fun θ : ℝ => C * Work.Elliptic.sinCos2 θ)
    ?_ ?_ ?_
  · exact (continuous_sinCos2_fts.continuousOn.integrableOn_compact
      isCompact_Icc).const_mul C
  · have hcont : ContinuousOn (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hu.continuousOn.abs).mul continuous_sinCos2_fts.continuousOn
    have h3 : AEStronglyMeasurable (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rw [Work.Spaces.Iθ, (Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))).symm]
    exact h3
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs]
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, sinCos2_zero_left, mul_zero, abs_zero, mul_zero]
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · rw [h2, sinCos2_zero_right, mul_zero, abs_zero, mul_zero]
      · rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Ioo ⟨h, h2⟩))]
        exact mul_le_mul_of_nonneg_right (hub θ ⟨h, h2⟩) (sinCos2_nonneg_Ioo ⟨h, h2⟩)

/-! ## The reduction: the growth bound implies the box statement -/

/-- **The box statement from the locally uniform angular growth bound.**

If, for a.e. `z₀ > 0`, there is a neighbourhood `(z₀-ε, z₀+ε)` of `z₀` (with `ε < z₀`) on which
a *single* constant `C` dominates all four slices `∂_z^jΨ`, `j ≤ 3`, by `C(θ⁻¹ + (π/2-θ)⁻¹)`,
then the conclusion of `pzIterBoxIntegrable` holds at a.e. `z₀`.

The growth bound combined with `rho_mul_sinCos2_le` bounds `|∂_z^jΨ·sinθcos²θ|` by the constant
`C(1+π/2)` on the whole box; the box has finite measure, so that constant is integrable, and
together with the a.e. strong measurability of the slices (continuity on the open quadrant, the
exceptional set `θ ∈ {0, π/2}` being null) `Integrable.of_bound` gives both conclusions. -/
theorem pzIterBoxIntegrable_of_growth
    (hcore : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
            ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.Spaces.pzIter j Ψ z θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
          (∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
            MeasureTheory.IntegrableOn
              (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
              Work.Spaces.Iθ) ∧
          (∀ j : ℕ, j ≤ 3 → MeasureTheory.Integrable
              (Function.uncurry (fun s θ : ℝ =>
                |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
              ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - ε) (z₀ + ε))).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  intro α F Ψ hα hα4 hcl
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hcl.2.2.2.2.2.2.1
  filter_upwards [hcore α F Ψ hα hα4 hcl,
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z₀ hz hzmem
  obtain ⟨ε₁, hε₁pos, hε₁z, C, hC, hbound⟩ := hz
  have hz₀ : 0 < z₀ := hzmem
  -- shrink the neighbourhood so that `ε < z₀` and `ε < ε₁` (the box then stays in `z > 0`)
  set e : ℝ := min ε₁ z₀ / 2 with he
  have hepos : 0 < e := by rw [he]; positivity
  have hez : e < z₀ := by
    rw [he]
    have h : min ε₁ z₀ ≤ z₀ := min_le_right _ _
    linarith
  have heε₁ : e < ε₁ := by
    rw [he]
    have h : min ε₁ z₀ ≤ ε₁ := min_le_left _ _
    linarith
  have hsub : Set.Ioo (z₀ - e) (z₀ + e) ⊆ Set.Ioo (z₀ - ε₁) (z₀ + ε₁) := by
    intro z hz'
    exact ⟨by linarith [hz'.1, heε₁], by linarith [hz'.2, heε₁]⟩
  refine ⟨e, hepos, hez, ?_, ?_⟩
  · -- the pointwise slices
    intro j hj z hz'
    have hzpos : 0 < z := by linarith [hz'.1, hez]
    have hzin : z ∈ Set.Ioo (z₀ - ε₁) (z₀ + ε₁) := hsub hz'
    have hcont : ContinuousOn
        (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (((hS.pzIter j).curry_θ hzpos).continuousOn).mul
        continuous_sinCos2_fts.continuousOn
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      rw [Work.Spaces.Iθ,
        Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm]
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    refine integrableOn_of_bound_Iθ (K := C * (1 + Real.pi / 2)) haesm (fun θ hθ => ?_)
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
      · have hg := hbound j hj z hzin θ ⟨hθ0, hθ1⟩
        have hψnn : 0 ≤ Work.Elliptic.sinCos2 θ := sinCos2_nonneg_Ioo ⟨hθ0, hθ1⟩
        rw [abs_mul, abs_of_nonneg hψnn]
        calc |Work.Spaces.pzIter j Ψ z θ| * Work.Elliptic.sinCos2 θ
            ≤ (C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)) * Work.Elliptic.sinCos2 θ :=
              mul_le_mul_of_nonneg_right hg hψnn
          _ = C * ((θ⁻¹ + (Real.pi / 2 - θ)⁻¹) * Work.Elliptic.sinCos2 θ) := by ring
          _ ≤ C * (1 + Real.pi / 2) :=
              mul_le_mul_of_nonneg_left (rho_mul_sinCos2_le ⟨hθ0, hθ1⟩) hC
      · rw [hθ1, sinCos2_zero_right, mul_zero, abs_zero]
        exact mul_nonneg hC (by linarith [Real.pi_pos])
    · rw [← hθ0, sinCos2_zero_left, mul_zero, abs_zero]
      exact mul_nonneg hC (by linarith [Real.pi_pos])
  · -- the box integrability
    intro j hj
    have hcont : ContinuousOn
        (Function.uncurry (fun s θ : ℝ =>
          |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (((hS.pzIter j).continuousOn.abs).mul
        (continuous_sinCos2_fts.comp continuous_snd).continuousOn)
    have ha : 0 ≤ z₀ - e := by linarith [hez]
    have haesm := Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont
      (a := z₀ - e) (b := z₀ + e) ha
    refine integrable_box_of_bound (K := C * (1 + Real.pi / 2)) haesm (fun p hp => ?_)
    obtain ⟨hp1, hp2⟩ := hp
    have hpin : p.1 ∈ Set.Ioo (z₀ - ε₁) (z₀ + ε₁) := by
      exact ⟨by linarith [hp1.1, heε₁], by linarith [hp1.2, heε₁]⟩
    rcases lt_or_eq_of_le hp2.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hp2.2 with hθ1 | hθ1
      · have hg := hbound j hj p.1 hpin p.2 ⟨hθ0, hθ1⟩
        have hψnn : 0 ≤ Work.Elliptic.sinCos2 p.2 := sinCos2_nonneg_Ioo ⟨hθ0, hθ1⟩
        show |Function.uncurry (fun s θ : ℝ =>
            |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ) p|
          ≤ C * (1 + Real.pi / 2)
        rw [show Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ) p
            = |Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2 from rfl]
        rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) hψnn)]
        calc |Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2
            ≤ (C * (p.2⁻¹ + (Real.pi / 2 - p.2)⁻¹)) * Work.Elliptic.sinCos2 p.2 :=
              mul_le_mul_of_nonneg_right hg hψnn
          _ = C * ((p.2⁻¹ + (Real.pi / 2 - p.2)⁻¹) * Work.Elliptic.sinCos2 p.2) := by ring
          _ ≤ C * (1 + Real.pi / 2) :=
              mul_le_mul_of_nonneg_left (rho_mul_sinCos2_le ⟨hθ0, hθ1⟩) hC
      · rw [show Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ) p
            = |Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2 from rfl,
          hθ1, sinCos2_zero_right, mul_zero, abs_zero]
        exact mul_nonneg hC (by linarith [Real.pi_pos])
    · rw [show Function.uncurry (fun s θ : ℝ =>
            |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ) p
          = |Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2 from rfl,
        ← hθ0, sinCos2_zero_left, mul_zero, abs_zero]
      exact mul_nonneg hC (by linarith [Real.pi_pos])

/-! ## The reduction: a locally uniform `L¹_θ`-bound on the slices

This is the *weakest* local-uniformity input that implies the target: not the pointwise-in-`θ`
pole bound of `pzIterBoxIntegrable_of_growth`, but only the local *boundedness in `z` of the
`θ`-integral* of the slices.  The first lemma below records that the pole bound implies it
(so the reduction of this section strictly generalises the previous one). -/

/-- **The locally uniform pole bound implies the locally uniform `L¹_θ`-bound.**  Integrating
`C(θ⁻¹ + (π/2-θ)⁻¹)` against `sinθcos²θ ≤ 1` gives `C(1+π/2)`, so the input of
`pzIterBoxIntegrable_of_locBound` is implied by that of `pzIterBoxIntegrable_of_growth`. -/
theorem locBound_of_poleBound {Ψ : ℝ → ℝ → ℝ}
    (h : ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.Spaces.pzIter j Ψ z θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
        ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (|Work.Spaces.pzIter j Ψ z θ|
              * |Work.Elliptic.sinCos2 θ|) ≤ M := by
  filter_upwards [h] with z₀ hz
  obtain ⟨ε, hε, hεz, C, hC, hb⟩ := hz
  refine ⟨ε, hε, hεz, ENNReal.ofReal (C * (1 + Real.pi / 2) * (Real.pi / 2)),
    ENNReal.ofReal_ne_top, ?_⟩
  intro j hj z hz'
  have hCnn : 0 ≤ C * (1 + Real.pi / 2) := by positivity
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ| ≤ C * (1 + Real.pi / 2) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, sinCos2_zero_left, abs_zero, mul_zero]; exact hCnn
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · rw [h2, sinCos2_zero_right, abs_zero, mul_zero]; exact hCnn
      · have hb' := hb j hj z hz' θ ⟨h0, h2⟩
        have hψnn := sinCos2_nonneg_Ioo ⟨h0, h2⟩
        rw [abs_of_nonneg hψnn]
        calc |Work.Spaces.pzIter j Ψ z θ| * Work.Elliptic.sinCos2 θ
            ≤ (C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)) * Work.Elliptic.sinCos2 θ :=
              mul_le_mul_of_nonneg_right hb' hψnn
          _ = C * ((θ⁻¹ + (Real.pi / 2 - θ)⁻¹) * Work.Elliptic.sinCos2 θ) := by ring
          _ ≤ C * (1 + Real.pi / 2) :=
              mul_le_mul_of_nonneg_left (rho_mul_sinCos2_le ⟨h0, h2⟩) hC
  calc ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (|Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|)
      ≤ ∫⁻ _θ in Work.Spaces.Iθ, ENNReal.ofReal (C * (1 + Real.pi / 2)) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact ENNReal.ofReal_le_ofReal (hpt θ hθ)
    _ = ENNReal.ofReal (C * (1 + Real.pi / 2) * (Real.pi / 2)) := by
        rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Work.Spaces.Iθ,
          Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul hCnn]

/-- **The reduction from a locally uniform `L¹_θ`-bound.**

If, for a.e. `z₀ > 0`, there is a neighbourhood `(z₀-ε, z₀+ε)` (with `ε < z₀`) and a *finite*
constant `M` with `∫⁻_θ ofReal(|∂_z^jΨ(z,θ)|·|sinθcos²θ|) ≤ M` for `j ≤ 3` and `z` in the
neighbourhood, then the conclusion of `pzIterBoxIntegrable` holds at a.e. `z₀`.  The pointwise
integrability comes from `M < ⊤` (via `hasFiniteIntegral_iff_norm`), the box integrability from
Tonelli (`lintegral_prod`) and the finiteness of the measure of the box.  (The absolute value of
the angular weight is immaterial — it is nonnegative on `Iθ` — but it makes the passage from the
`lintegral` bound to the stated `Integrable` statements pointwise.) -/
theorem pzIterBoxIntegrable_of_locBound
    (hcore : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
          ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
            ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (|Work.Spaces.pzIter j Ψ z θ|
                * |Work.Elliptic.sinCos2 θ|) ≤ M) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
          (∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
            MeasureTheory.IntegrableOn
              (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
              Work.Spaces.Iθ) ∧
          (∀ j : ℕ, j ≤ 3 → MeasureTheory.Integrable
              (Function.uncurry (fun s θ : ℝ =>
                |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
              ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - ε) (z₀ + ε))).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  intro α F Ψ hα hα4 hcl
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hcl.2.2.2.2.2.2.1
  filter_upwards [hcore α F Ψ hα hα4 hcl,
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z₀ hz hzmem
  obtain ⟨ε₁, hε₁pos, hε₁z, M, hMtop, hbound⟩ := hz
  have hz₀ : 0 < z₀ := hzmem
  set e : ℝ := min ε₁ z₀ / 2 with he
  have hepos : 0 < e := by rw [he]; positivity
  have hez : e < z₀ := by
    rw [he]
    have h : min ε₁ z₀ ≤ z₀ := min_le_right _ _
    linarith
  have heε₁ : e < ε₁ := by
    rw [he]
    have h : min ε₁ z₀ ≤ ε₁ := min_le_left _ _
    linarith
  have hsub : Set.Ioo (z₀ - e) (z₀ + e) ⊆ Set.Ioo (z₀ - ε₁) (z₀ + ε₁) := by
    intro z hz'
    exact ⟨by linarith [hz'.1, heε₁], by linarith [hz'.2, heε₁]⟩
  refine ⟨e, hepos, hez, ?_, ?_⟩
  · -- the pointwise slices
    intro j hj z hz'
    have hzpos : 0 < z := by linarith [hz'.1, hez]
    have hb := hbound j hj z (hsub hz')
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => |Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|)
        (volume.restrict Work.Spaces.Iθ) := by
      have hcont : ContinuousOn
          (fun θ : ℝ => |Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|)
          (Set.Ioo 0 (Real.pi / 2)) :=
        (((hS.pzIter j).curry_θ hzpos).continuousOn.abs).mul
          (continuous_sinCos2_fts.continuousOn.abs)
      have h3 : AEStronglyMeasurable
          (fun θ : ℝ => |Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|)
          (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
        hcont.aestronglyMeasurable measurableSet_Ioo
      rw [Work.Spaces.Iθ, (Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))).symm]
      exact h3
    have hlt : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (|Work.Spaces.pzIter j Ψ z θ|
          * |Work.Elliptic.sinCos2 θ|)) < ⊤ :=
      lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hMtop)
    have hfin : MeasureTheory.HasFiniteIntegral
        (fun θ : ℝ => |Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|)
        (volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.hasFiniteIntegral_iff_norm]
      have hcongr : (fun θ : ℝ => ENNReal.ofReal
            ‖|Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|‖)
          = fun θ : ℝ => ENNReal.ofReal (|Work.Spaces.pzIter j Ψ z θ|
              * |Work.Elliptic.sinCos2 θ|) := by
        funext θ
        show ENNReal.ofReal ‖|Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|‖ = _
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      rw [hcongr]
      exact hlt
    have habs : MeasureTheory.IntegrableOn
        (fun θ : ℝ => |Work.Spaces.pzIter j Ψ z θ| * |Work.Elliptic.sinCos2 θ|)
        Work.Spaces.Iθ := ⟨haesm, hfin⟩
    refine MeasureTheory.Integrable.mono' habs ?_ ?_
    · have hcont : ContinuousOn
          (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        (((hS.pzIter j).curry_θ hzpos).continuousOn).mul
          continuous_sinCos2_fts.continuousOn
      have h3 : AEStronglyMeasurable
          (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
          (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
        hcont.aestronglyMeasurable measurableSet_Ioo
      rw [Work.Spaces.Iθ, (Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))).symm]
      exact h3
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_mul]
  · -- the box
    intro j hj
    have ha : 0 ≤ z₀ - e := by linarith [hez]
    have hcont : ContinuousOn
        (Function.uncurry (fun s θ : ℝ =>
          |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (((hS.pzIter j).continuousOn.abs).mul
        (continuous_sinCos2_fts.comp continuous_snd).continuousOn)
    have haesm := Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont
      (a := z₀ - e) (b := z₀ + e) ha
    refine ⟨haesm, ?_⟩
    have hfin : MeasureTheory.HasFiniteIntegral
        (Function.uncurry (fun s θ : ℝ =>
          |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - e) (z₀ + e))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.hasFiniteIntegral_iff_norm]
      set μ := MeasureTheory.volume.restrict (Set.Ioc (z₀ - e) (z₀ + e)) with hμ
      set ν := MeasureTheory.volume.restrict Work.Spaces.Iθ with hν
      have hcongr : (fun p : ℝ × ℝ => ENNReal.ofReal
            ‖(Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ)) p‖)
          = fun p : ℝ × ℝ => ENNReal.ofReal (|Work.Spaces.pzIter j Ψ p.1 p.2|
              * |Work.Elliptic.sinCos2 p.2|) := by
        funext p
        show ENNReal.ofReal ‖|Work.Spaces.pzIter j Ψ p.1 p.2|
            * Work.Elliptic.sinCos2 p.2‖ = _
        rw [Real.norm_eq_abs, abs_mul, abs_abs]
      rw [hcongr]
      have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
          (|Work.Spaces.pzIter j Ψ p.1 p.2| * |Work.Elliptic.sinCos2 p.2|))
          (μ.prod ν) :=
        ((haesm.norm.congr (Filter.Eventually.of_forall (fun p => by
          show ‖|Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2‖
            = |Work.Spaces.pzIter j Ψ p.1 p.2| * |Work.Elliptic.sinCos2 p.2|
          rw [Real.norm_eq_abs, abs_mul, abs_abs]))).aemeasurable).ennreal_ofReal
      rw [MeasureTheory.lintegral_prod _ hmeas]
      have hstep : ∀ᵐ s ∂μ, (∫⁻ θ, ENNReal.ofReal
            (|Work.Spaces.pzIter j Ψ s θ| * |Work.Elliptic.sinCos2 θ|) ∂ν) ≤ M := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hs1 : z₀ - ε₁ < s := lt_trans (by linarith [heε₁]) hs.1
        have hs2 : s < z₀ + ε₁ := lt_of_le_of_lt hs.2 (by linarith [heε₁])
        exact hbound j hj s ⟨hs1, hs2⟩
      have h1 : ∫⁻ s, (∫⁻ θ, ENNReal.ofReal
            (|Work.Spaces.pzIter j Ψ s θ| * |Work.Elliptic.sinCos2 θ|) ∂ν) ∂μ
          ≤ ∫⁻ _s, M ∂μ :=
        MeasureTheory.lintegral_mono_ae hstep
      refine lt_of_le_of_lt h1 ?_
      rw [MeasureTheory.lintegral_const, hμ, Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hMtop) ENNReal.ofReal_lt_top
    exact hfin

/-! ## The pole bound from a locally uniform source-mass bound

The chapter's bottleneck in `L¹`-mass form is the locally uniform bound on the *source mass*
`∫_{Iθ} sinθcos²θ·|Lzero1(∂_z^mΨ)(z,·)|`, together with the (free, by continuity) bound on the
`π/4`-data of the slices.  The two lemmas below show that this input is *sufficient*: the proved
quantitative one-variable theorem `LocC.lzeroGrowthQuantL1Self`
(`Submission/Work/FTS/EllipticEst/H2W/LocC/LzeroQuantSelf.lean`, axiom-clean) bounds every slice by
`C·(mass + data at π/4)·(θ⁻¹ + (π/2-θ)⁻¹)` with a *universal* `C`, so a single uniform bound on
the mass and the data gives the pole bound with a single constant.  Consequently the target
reduces to the source-mass bound (`pzIterBoxIntegrable_of_sourceMass`). -/

/-- **The locally uniform pole bound from a locally uniform source-mass bound.**

The three hypotheses are the ingredients of the `SliceSourceMassBound` shape of
`Submission/Work/FTS/EllipticEst/H2W/pzIterSliceGrowth3LocReduction.lean`, split so that each has
its own `ε` and its own constant: for a.e. `z₀` there is a neighbourhood on which, for every
`m ≤ 3`, (i) the θ-source `θ ↦ sinθcos²θ·|Lzero1(∂_z^mΨ)(z,·)|` is integrable on `Iθ`, (ii) its
integral is at most `K`, and (iii) the `π/4`-data `|∂_z^mΨ| + |∂_θ∂_z^mΨ|` is at most `K'`.  The
conclusion is the input of `pzIterBoxIntegrable_of_growth`. -/
theorem poleBound_of_sourceMass {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hInt : ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
        ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 *
              |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
            Work.Spaces.Iθ)
    (hMass : ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
        ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
          (∫ θ in Work.Spaces.Iθ,
                (Real.sin θ * Real.cos θ ^ 2 *
                    |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|
                  + |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
                  + |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)|))
            ≤ K) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.Spaces.pzIter j Ψ z θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.H2W.LocC.lzeroGrowthQuantL1Self
  filter_upwards [hInt, hMass, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z₀ hInt' hMass' hz
  obtain ⟨ε₁, hε₁pos, hε₁z, hI⟩ := hInt'
  obtain ⟨ε₃, hε₃pos, hε₃z, Km, hKmnn, hMi⟩ := hMass'
  set e : ℝ := min ε₁ (min ε₃ z₀) / 2 with he
  have hepos : 0 < e := by
    rw [he]
    have h1 : 0 < min ε₁ (min ε₃ z₀) := lt_min hε₁pos (lt_min hε₃pos hz)
    linarith
  have hez : e < z₀ := by
    rw [he]
    have h : min ε₁ (min ε₃ z₀) ≤ min ε₃ z₀ := min_le_right _ _
    have h2 : min ε₃ z₀ ≤ z₀ := min_le_right _ _
    linarith
  have heε₁ : e < ε₁ := by
    rw [he]
    have h : min ε₁ (min ε₃ z₀) ≤ ε₁ := min_le_left _ _
    linarith
  have heε₃ : e < ε₃ := by
    rw [he]
    have h : min ε₁ (min ε₃ z₀) ≤ min ε₃ z₀ := min_le_right _ _
    have h2 : min ε₃ z₀ ≤ ε₃ := min_le_left _ _
    linarith
  refine ⟨e, hepos, hez, C * Km, mul_nonneg hCpos.le hKmnn, ?_⟩
  intro j hj z hz' θ hθ
  have hzpos : 0 < z := by linarith [hz'.1, hez]
  have hz₁ : z ∈ Set.Ioo (z₀ - ε₁) (z₀ + ε₁) :=
    ⟨by linarith [hz'.1, heε₁], by linarith [hz'.2, heε₁]⟩
  have hz₃ : z ∈ Set.Ioo (z₀ - ε₃) (z₀ + ε₃) :=
    ⟨by linarith [hz'.1, heε₃], by linarith [hz'.2, heε₃]⟩
  have hint := hI z hz₁ j hj
  have hu : ∀ n : ℕ, ContDiffOn ℝ n
      (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun n =>
    (hsm.pzIter j).curry_θ hzpos |>.of_le (by simp [Work.Stability.smoothOrder])
  have hslice := hC (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') hu hint θ hθ
  have hbr : (∫ s in Work.Spaces.Iθ, Real.sin s * Real.cos s ^ 2 *
        |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') s|
      + |Work.Spaces.pzIter j Ψ z (Real.pi / 4)|
      + |deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') (Real.pi / 4)|) ≤ Km :=
    hMi z hz₃ j hj
  have hρ : 0 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ :=
    add_nonneg (inv_nonneg.mpr hθ.1.le) (inv_nonneg.mpr (by linarith [hθ.2]))
  calc |Work.Spaces.pzIter j Ψ z θ|
      ≤ C * (∫ s in Work.Spaces.Iθ, Real.sin s * Real.cos s ^ 2 *
              |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') s|
            + |Work.Spaces.pzIter j Ψ z (Real.pi / 4)|
            + |deriv (fun θ' : ℝ => Work.Spaces.pzIter j Ψ z θ') (Real.pi / 4)|)
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := hslice
    _ ≤ C * Km * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbr hCpos.le) hρ

/-- **The target from a locally uniform source-mass bound** (the hypotheses as in
`poleBound_of_sourceMass`). -/
theorem pzIterBoxIntegrable_of_sourceMass
    (hcore : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      (∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
          ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
            MeasureTheory.IntegrableOn
              (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 *
                |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|)
              Work.Spaces.Iθ) ∧
      (∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
          ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε), ∀ m : ℕ, m ≤ 3 →
            (∫ θ in Work.Spaces.Iθ,
                  (Real.sin θ * Real.cos θ ^ 2 *
                      |Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') θ|
                    + |Work.Spaces.pzIter m Ψ z (Real.pi / 4)|
                    + |deriv (fun θ' : ℝ => Work.Spaces.pzIter m Ψ z θ') (Real.pi / 4)|))
              ≤ K)) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
          (∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
            MeasureTheory.IntegrableOn
              (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
              Work.Spaces.Iθ) ∧
          (∀ j : ℕ, j ≤ 3 → MeasureTheory.Integrable
              (Function.uncurry (fun s θ : ℝ =>
                |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
              ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - ε) (z₀ + ε))).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  intro α F Ψ hα hα4 hcl
  exact pzIterBoxIntegrable_of_growth
    (fun α' F' Ψ' hα' hα4' h' =>
      poleBound_of_sourceMass
        (Work.FTS.EllipticEst.smoothOpen_of_forall h'.2.2.2.2.2.2.1)
        (hcore α' F' Ψ' hα' hα4' h').1 (hcore α' F' Ψ' hα' hα4' h').2)
    α F Ψ hα hα4 hcl

/-! ## The per-datum form of the reduction, and the paper's missing hypothesis

`WeakPos2` is the *weak* class (see `PropH2Base.lean`): the equation on the open quadrant, the
Dirichlet data as *values*, the decay `z → ∞`, the two moment conditions, `C^∞` on the open
quadrant, and the honesty of the **source** only (`HkMem α 2 F`).  It carries **no** honesty for
the left-hand-side slots of `Ψ`, and those are exactly the quantities the target asserts to be
honest.  The paper's Proposition `prop:L2` does not work in this class either: it concerns *the
unique `L²` solution* of `(PolarBSL)` with `R²Ψ → 0` at `R = 0`, and its Step 1 uses precisely
that condition to conclude `Ψ_★ ≡ 0`.

The two lemmas below record the conditional forms of the target that *are* usable:

* `pzIterBoxIntegrable_of_poleBoundDatum` — the target's conclusion for a *fixed* datum from a
  locally uniform pole bound for that datum (the conclusion of the tree's
  `pzIterSliceGrowth3Loc` chain, in its `pzIterSliceGrowth3Loc_of_massBound` /
  `pzIterSliceGrowth3LocC` reductions);
* `pzIterBoxIntegrable_of_externalMass` — the target's conclusion from the paper's missing
  hypothesis `SliceMassExternal α F Ψ` (the ψ-weighted slice-mass form of the paper's
  `R²Ψ → 0` at `R = 0`, `H2W/SliceMassExternal.lean`), through the proved tree lemmas
  `sliceSourceMassBound_of_external` and `pzIterSliceGrowth3Loc_of_massBound`. -/

/-- **The target's conclusion for a fixed datum from a locally uniform pole bound for that
datum.**  The uniformity in `z` on the neighbourhood is what the box conjunct needs; the
pointwise conjunct uses the same bound at each `z` of the neighbourhood. -/
theorem pzIterBoxIntegrable_of_poleBoundDatum {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hcl : Work.FTS.EllipticEst.WeakPos2 α F Ψ)
    (hpole : ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.Spaces.pzIter j Ψ z θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
        (∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ) ∧
        (∀ j : ℕ, j ≤ 3 → MeasureTheory.Integrable
            (Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
            ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - ε) (z₀ + ε))).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hcl.2.2.2.2.2.2.1
  filter_upwards [hpole, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z₀ hz hzmem
  obtain ⟨ε₁, hε₁pos, hε₁z, C, hC, hbound⟩ := hz
  have hz₀ : 0 < z₀ := hzmem
  set e : ℝ := min ε₁ z₀ / 2 with he
  have hepos : 0 < e := by rw [he]; positivity
  have hez : e < z₀ := by
    rw [he]
    have h : min ε₁ z₀ ≤ z₀ := min_le_right _ _
    linarith
  have heε₁ : e < ε₁ := by
    rw [he]
    have h : min ε₁ z₀ ≤ ε₁ := min_le_left _ _
    linarith
  have hsub : Set.Ioo (z₀ - e) (z₀ + e) ⊆ Set.Ioo (z₀ - ε₁) (z₀ + ε₁) := by
    intro z hz'
    exact ⟨by linarith [hz'.1, heε₁], by linarith [hz'.2, heε₁]⟩
  refine ⟨e, hepos, hez, ?_, ?_⟩
  · -- the pointwise slices
    intro j hj z hz'
    have hzpos : 0 < z := by linarith [hz'.1, hez]
    have hzin : z ∈ Set.Ioo (z₀ - ε₁) (z₀ + ε₁) := hsub hz'
    have hcont : ContinuousOn
        (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (((hS.pzIter j).curry_θ hzpos).continuousOn).mul
        continuous_sinCos2_fts.continuousOn
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      rw [Work.Spaces.Iθ,
        Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm]
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    refine integrableOn_of_bound_Iθ (K := C * (1 + Real.pi / 2)) haesm (fun θ hθ => ?_)
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
      · have hg := hbound j hj z hzin θ ⟨hθ0, hθ1⟩
        have hψnn : 0 ≤ Work.Elliptic.sinCos2 θ := sinCos2_nonneg_Ioo ⟨hθ0, hθ1⟩
        rw [abs_mul, abs_of_nonneg hψnn]
        calc |Work.Spaces.pzIter j Ψ z θ| * Work.Elliptic.sinCos2 θ
            ≤ (C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)) * Work.Elliptic.sinCos2 θ :=
              mul_le_mul_of_nonneg_right hg hψnn
          _ = C * ((θ⁻¹ + (Real.pi / 2 - θ)⁻¹) * Work.Elliptic.sinCos2 θ) := by ring
          _ ≤ C * (1 + Real.pi / 2) :=
              mul_le_mul_of_nonneg_left (rho_mul_sinCos2_le ⟨hθ0, hθ1⟩) hC
      · rw [hθ1, sinCos2_zero_right, mul_zero, abs_zero]
        exact mul_nonneg hC (by linarith [Real.pi_pos])
    · rw [← hθ0, sinCos2_zero_left, mul_zero, abs_zero]
      exact mul_nonneg hC (by linarith [Real.pi_pos])
  · -- the box integrability
    intro j hj
    have hcont : ContinuousOn
        (Function.uncurry (fun s θ : ℝ =>
          |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (((hS.pzIter j).continuousOn.abs).mul
        (continuous_sinCos2_fts.comp continuous_snd).continuousOn)
    have ha : 0 ≤ z₀ - e := by linarith [hez]
    have haesm := Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont
      (a := z₀ - e) (b := z₀ + e) ha
    refine integrable_box_of_bound (K := C * (1 + Real.pi / 2)) haesm (fun p hp => ?_)
    obtain ⟨hp1, hp2⟩ := hp
    have hpin : p.1 ∈ Set.Ioo (z₀ - ε₁) (z₀ + ε₁) :=
      ⟨by linarith [hp1.1, heε₁], by linarith [hp1.2, heε₁]⟩
    rcases lt_or_eq_of_le hp2.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hp2.2 with hθ1 | hθ1
      · have hg := hbound j hj p.1 hpin p.2 ⟨hθ0, hθ1⟩
        have hψnn : 0 ≤ Work.Elliptic.sinCos2 p.2 := sinCos2_nonneg_Ioo ⟨hθ0, hθ1⟩
        show |Function.uncurry (fun s θ : ℝ =>
            |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ) p|
          ≤ C * (1 + Real.pi / 2)
        rw [show Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ) p
            = |Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2 from rfl]
        rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) hψnn)]
        calc |Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2
            ≤ (C * (p.2⁻¹ + (Real.pi / 2 - p.2)⁻¹)) * Work.Elliptic.sinCos2 p.2 :=
              mul_le_mul_of_nonneg_right hg hψnn
          _ = C * ((p.2⁻¹ + (Real.pi / 2 - p.2)⁻¹) * Work.Elliptic.sinCos2 p.2) := by ring
          _ ≤ C * (1 + Real.pi / 2) :=
              mul_le_mul_of_nonneg_left (rho_mul_sinCos2_le ⟨hθ0, hθ1⟩) hC
      · rw [show Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ) p
            = |Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2 from rfl,
          hθ1, sinCos2_zero_right, mul_zero, abs_zero]
        exact mul_nonneg hC (by linarith [Real.pi_pos])
    · rw [show Function.uncurry (fun s θ : ℝ =>
            |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ) p
          = |Work.Spaces.pzIter j Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2 from rfl,
        ← hθ0, sinCos2_zero_left, mul_zero, abs_zero]
      exact mul_nonneg hC (by linarith [Real.pi_pos])

/-- **The target's conclusion from the paper's missing hypothesis.**

`WeakPos2` does not control the left-hand-side slots of `Ψ`; the paper's own setting does, and
the ψ-mass form of that control is `SliceMassExternal α F Ψ` (`H2W/SliceMassExternal.lean`, the
form in which the paper's `R²Ψ → 0` at `R = 0` enters the tree's honesty chain).  With it, the
tree's proved chain

  `SliceMassExternal α F Ψ  →  SliceSourceMassBound Ψ  →  (locally uniform pole bound)`

ends in the target's conclusion. -/
theorem pzIterBoxIntegrable_of_externalMass {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hcl : Work.FTS.EllipticEst.WeakPos2 α F Ψ)
    (hM : Work.FTS.EllipticEst.H2W.SliceMassExternal α F Ψ) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
        (∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ) ∧
        (∀ j : ℕ, j ≤ 3 → MeasureTheory.Integrable
            (Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
            ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - ε) (z₀ + ε))).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
  pzIterBoxIntegrable_of_poleBoundDatum hcl
    (Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3Loc_of_massBound hcl
      (Work.FTS.EllipticEst.H2W.sliceSourceMassBound_of_external α F Ψ hα hα4 hcl hM))

/-! ### The two weakest sufficient inputs available in the tree

The tree's `H2W/SliceB/pzSecGrowthLoc.lean` reduces the locally uniform pole bound to a locally
uniform bound on the *honest angular slots* of the four slices `pzIter m Ψ` (`m ≤ 3`): the second
derivative slot (`LocSecBound`) or even just the first (`LocGradBound`).  Composed with
`pzIterBoxIntegrable_of_poleBoundDatum` this gives the target's conclusion from those inputs. -/

/-- **The target's conclusion from the locally uniform honest second angular slot.** -/
theorem pzIterBoxIntegrable_of_locSecBound {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hcl : Work.FTS.EllipticEst.WeakPos2 α F Ψ)
    (hs : Work.FTS.EllipticEst.H2W.SliceB.LocSecBound Ψ) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
        (∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ) ∧
        (∀ j : ℕ, j ≤ 3 → MeasureTheory.Integrable
            (Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
            ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - ε) (z₀ + ε))).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
  pzIterBoxIntegrable_of_poleBoundDatum hcl
    (Work.FTS.EllipticEst.H2W.SliceB.pzIterSliceGrowth3Loc_of_locSecBound hcl hs)

/-- **The target's conclusion from the locally uniform honest first angular slot** (the weakest
sufficient input currently on disk: `∫_θ (∂_θ(pzIter m Ψ)(z,·))² sin(2θ)^{-η} ≤ C` for `m ≤ 3`,
locally uniformly in `z`). -/
theorem pzIterBoxIntegrable_of_locGradBound {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hcl : Work.FTS.EllipticEst.WeakPos2 α F Ψ)
    (hs : Work.FTS.EllipticEst.H2W.SliceB.LocGradBound Ψ) :
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
        (∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ) ∧
        (∀ j : ℕ, j ≤ 3 → MeasureTheory.Integrable
            (Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
            ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - ε) (z₀ + ε))).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
  pzIterBoxIntegrable_of_poleBoundDatum hcl
    (Work.FTS.EllipticEst.H2W.SliceB.pzIterSliceGrowth3Loc_of_locGradBound hcl hs)

/-! ## The target -/

theorem pzIterBoxIntegrable : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos2 α F Ψ →
    ∀ᵐ z₀ ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∃ ε : ℝ, 0 < ε ∧ ε < z₀ ∧
        (∀ j : ℕ, j ≤ 3 → ∀ z ∈ Set.Ioo (z₀ - ε) (z₀ + ε),
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter j Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ) ∧
        (∀ j : ℕ, j ≤ 3 → MeasureTheory.Integrable
            (Function.uncurry (fun s θ : ℝ =>
              |Work.Spaces.pzIter j Ψ s θ| * Work.Elliptic.sinCos2 θ))
            ((MeasureTheory.volume.restrict (Set.Ioc (z₀ - ε) (z₀ + ε))).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  sorry

end

end Work.FTS.EllipticEst.H2W
