import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPB.B2.chordSurf_injective
import Submission.Work.RPB.B5.chordSurf_rhoChart_full
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.chart_C12
import Submission.Work.RPB.B5.contDiff_signedArea
import Submission.Work.RPB.B5.deriv_signedArea_general
import Submission.Work.RPB.B4.periodic_reduce
import Submission.Work.RPB.B4.periodic_deriv
import Submission.Work.RPB.B5.chord_linear_bound
import Submission.Work.RPB.B5.pos_min_of_compact
import Submission.Work.RPB.B5.chartJets_chartLev_slice
import Submission.Work.RPB.B5.chartJets_oneSided
import Submission.Work.RPB.B5.iteratedDeriv_eq_of_eqOn_Ioo_right
import Submission.Work.RPB.B5.area_normalised
import Submission.Work.RPB.B5.signedArea_scale_shift
import Submission.Work.RPV.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.levelPt_omega

/-!
# B5: existence of the collar, without level-data input (`collar_exists_noL`)

Given the `ρ = r²`-chart `W` of the chord annulus of the curve isotopy `CI` (`W τ t (r ^ 2) =
chordSurf CI.c a τ t r` for `0 < r ≤ π/2`) and a level inversion `ρh` with
`K₀ (W τ t (ρh τ t σ)) + 1 = -σ`, this file constructs a collar family `(Γc, Ac)` on the levels
`σ ≥ 0` with the ten properties of the statement.

Notation used throughout (with `P τ σ t = W τ t (ρh τ t σ)`):

* `N τ σ t = uproj (P τ σ t)` (the reduced coordinate) and `A τ σ t = (P τ σ t).1.2` (the phase);
  then `levelPt (N τ σ t) σ (A τ σ t) = P τ σ t` (this is `levelPt_uproj_level`).
* `Def` is the *flux defect* of the level family: `Def = ω_ℂ(∂_σ N, ∂_t N) - ∂_t A`.
  It vanishes identically on the annulus side (where the chart is the chord surface, which is
  Lagrangian) and vanishes to order `≥ 9` at `σ = 0`, because the chart's Lagrangian defect is a
  `C^11` function of `ρ` vanishing on `(0, π²/4)`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## 1. Elementary algebra of the level chart -/

/-- A point on the level `K₀ = -1 - σ` is recovered from its reduced coordinate `uproj` and its
phase `q₂`. -/
theorem levelPt_uproj_level (x : Work.RPV.PS) (σ : ℝ) (h : Work.RPV.K0 x + 1 = -σ) :
    Work.RPV.levelPt (Work.RPV.uproj x) σ x.1.2 = x := by
  have hexp : Complex.exp (-(x.1.2 : ℂ) * Complex.I)
        * (Complex.exp (x.1.2 * Complex.I) * (x.2.1 + x.1.1 * Complex.I))
      = x.2.1 + x.1.1 * Complex.I := by
    rw [← mul_assoc, ← Complex.exp_add]
    have h0 : -(x.1.2 : ℂ) * Complex.I + x.1.2 * Complex.I = 0 := by ring
    rw [h0, Complex.exp_zero, one_mul]
  have hnorm : ‖Work.RPV.uproj x‖ ^ 2 = x.2.1 ^ 2 + x.1.1 ^ 2 := by
    rw [Work.RPV.uproj, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, Complex.add_im, Complex.mul_im, add_zero, zero_add]
    ring
  have hp2 : ‖Work.RPV.uproj x‖ ^ 2 / 2 - σ - 1 = x.2.2 := by
    rw [hnorm, Work.RPV.K0] at *
    linarith
  have hkey : Complex.exp (-(x.1.2 : ℂ) * Complex.I) * Work.RPV.uproj x
      = x.2.1 + x.1.1 * Complex.I := hexp
  unfold Work.RPV.levelPt
  rw [hkey, hp2]
  ext1 <;> simp

/-- The level family point of `P τ σ t = W τ t (ρh τ t σ)`. -/
theorem levelPt_W_rho (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) {τ σ t : ℝ}
    (h : Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ) :
    Work.RPV.levelPt (Work.RPV.uproj (W τ t (ρh τ t σ))) σ ((W τ t (ρh τ t σ)).1.2)
      = W τ t (ρh τ t σ) :=
  levelPt_uproj_level _ σ h

/-! ## 2. Flat calculus: functions whose jets vanish at a point -/

/-- If `f` is `C^n` at `x₀` and vanishes on a left neighbourhood of `x₀`, then all its jets of
order `≤ n` vanish at `x₀`.  (Consequence of `chartJets_oneSided`.) -/
theorem iteratedDeriv_eq_zero_of_eqOn_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x₀ δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hf : ContDiffAt ℝ n f x₀)
    (h : ∀ x ∈ Set.Ioo (x₀ - δ) x₀, f x = 0) {k : ℕ} (hk : k ≤ n) :
    iteratedDeriv k f x₀ = 0 := by
  have h0 : ContDiffAt ℝ n (fun _ : ℝ => (0 : E)) x₀ := contDiffAt_const
  have hk' := chartJets_oneSided hδ hf h0 h hk
  rw [hk']; simp

/-- If `f` is `C^n` at `x₀` and vanishes on a right neighbourhood of `x₀`, then all its jets of
order `≤ n` vanish at `x₀`.  (Consequence of `iteratedDeriv_eq_of_eqOn_Ioo_right`.) -/
theorem iteratedDeriv_eq_zero_of_eqOn_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x₀ δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hf : ContDiffAt ℝ n f x₀)
    (h : ∀ x ∈ Set.Ioo x₀ (x₀ + δ), f x = 0) {k : ℕ} (hk : k ≤ n) :
    iteratedDeriv k f x₀ = 0 := by
  have h0 : ContDiffAt ℝ n (fun _ : ℝ => (0 : E)) x₀ := contDiffAt_const
  have hk' := iteratedDeriv_eq_of_eqOn_Ioo_right hδ hf h0 h hk
  rw [hk']; simp

/-! ## 3. The cutoffs and the construction

The collar is built from the following data: a scale `δ > 0`, the integer `k` of the `τ = 0`
chord phase, and the given chart `W` and level inversion `ρh`.
-/

/-- The smooth transition function: `0` on `(-∞,0]`, `1` on `[1,∞)`. -/
def stp (x : ℝ) : ℝ := Real.smoothTransition x

theorem stp_contDiff : ContDiff ℝ ∞ stp := Real.smoothTransition.contDiff

theorem stp_zero {x : ℝ} (h : x ≤ 0) : stp x = 0 := Real.smoothTransition.zero_of_nonpos h

theorem stp_one {x : ℝ} (h : 1 ≤ x) : stp x = 1 := Real.smoothTransition.one_of_one_le h

theorem stp_nonneg (x : ℝ) : 0 ≤ stp x := Real.smoothTransition.nonneg x

theorem stp_le_one (x : ℝ) : stp x ≤ 1 := Real.smoothTransition.le_one x

/-- The phase offset: `0` for `σ ≤ δ` and `-(π/2 + 2πk)` for `σ ≥ 2δ`. -/
def phc (δ : ℝ) (k : ℤ) (σ : ℝ) : ℝ :=
  (-(Real.pi/2) - 2*Real.pi*k) * stp ((σ - δ)/δ)

/-- The chord parameter of the far family: `1` for `σ ≤ δ`, `0` for `σ ≥ 2δ`. -/
def rpf (δ : ℝ) (σ : ℝ) : ℝ := 1 - stp ((σ - δ)/δ)

/-- The blend cutoff between the chart part and the far circles: `0` for `σ ≤ δ/2`, `1` for
`σ ≥ δ`. -/
def blf (δ : ℝ) (σ : ℝ) : ℝ := stp ((σ - δ/2)/(δ/2))

/-- The bump switching on the `τ = 0` correction: `1` for `τ ≤ 0`, `0` for `τ ≥ δ`. -/
def bbmp (δ : ℝ) (τ : ℝ) : ℝ := 1 - stp (τ/δ)

/-- The radius of the far circles. -/
def rd (σ : ℝ) : ℝ := Real.sqrt (2 + 2*σ)

/-- The diagonal real-linear map `(x,y) ↦ (x, g·y)` of `ℂ ≅ ℝ²`; its determinant is `g`, so it
reverses orientation when `g < 0`. -/
def diagM (g : ℝ) (z : ℂ) : ℂ := (z.re : ℂ) + ((g * z.im : ℝ) : ℂ) * Complex.I

/-- The level used by the negative-side family: `σ` for `σ ≥ -δ/2`, `-δ/4` for `σ ≤ -δ`.  It takes
values in `[-δ/4, ∞)` and stays inside the range where the chart area law is available. -/
def lvf (δ : ℝ) (σ : ℝ) : ℝ := -δ/4 + (σ + δ/4) * stp ((σ + δ)/(δ/2))

/-- The chart point on the level `σ`. -/
def PP (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (τ σ t : ℝ) : Work.RPV.PS :=
  W τ t (ρh τ t σ)

/-- The reduced coordinate of the chart point. -/
def NN (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (τ σ t : ℝ) : ℂ :=
  Work.RPV.uproj (PP W ρh τ σ t)

/-- The phase of the chart point. -/
def AA (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (τ σ t : ℝ) : ℝ :=
  (PP W ρh τ σ t).1.2

/-- The `τ = 0` target circle. -/
def targ (δ : ℝ) (k : ℤ) (σ t : ℝ) : ℂ :=
  (rd σ : ℂ) * Complex.exp ((t + phc δ k σ) * Complex.I)

/-- The near shape: the chart reduced coordinate, corrected near `τ = 0` so that the `τ = 0` slice
is exactly the circle family `targ`. -/
def nsh (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ)
    (τ σ t : ℝ) : ℂ :=
  NN W ρh τ σ t + bbmp δ τ * (targ δ k σ t - NN W ρh 0 σ t)

/-- The far shape: the rescaled curve family carried by `CI.c`. -/
def fsh (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℂ :=
  (rd σ : ℂ) * CI.c (rpf δ σ * τ) (t + phc δ k σ)

/-- The glued shape (before the area normalisation). -/
def sh0 (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℂ :=
  (1 - blf δ σ) * nsh W ρh δ k τ σ t + blf δ σ * fsh CI δ k τ σ t

/-- The signed area of the glued shape. -/
def arS (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ : ℝ) : ℝ :=
  Work.RPB.signedArea (sh0 CI W ρh δ k τ σ)

/-- The area normalisation factor. -/
def lam (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi*(1+σ)/arS CI W ρh δ k τ σ)

/-- The collar family on the levels `σ ≥ 0`. -/
def cpos (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℂ :=
  (lam CI W ρh δ k τ σ : ℂ) * sh0 CI W ρh δ k τ σ t

/-- The collar family on the levels `σ ≤ 0`: the diagonal image of the level family at the level
`lvf δ σ`, normalised so that the signed area is exactly `2π(1+σ)`. -/
def cneg (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (τ σ t : ℝ) : ℂ :=
  diagM ((1+σ)/(1 + lvf δ σ)) (NN W ρh τ (lvf δ σ) t)

/-- The collar curve family. -/
def GAM (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℂ :=
  if σ ≤ 0 then cneg W ρh δ τ σ t else cpos CI W ρh δ k τ σ t

/-- The `σ`-jets of the phase of the chart point at `t = 0`. -/
def cj (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) (j : ℕ) : ℝ :=
  iteratedDeriv j (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) 0

/-- The bump of the jet interpolation. -/
def jbump (δ : ℝ) (σ : ℝ) : ℝ := 1 - stp (σ/δ)

/-- The constant of integration of the phase.  Its `σ`-jets at `σ = 0` are those of `σ ↦ AA τ σ 0`
(so that the jet condition of the statement holds), it equals `φ + π/2 + 2πk` on the `τ = 0`
slice (so that the `τ = 0` slice lies in the zero section) and it vanishes for `σ ≥ 2δ` (so that
the phase is `t` at the far end). -/
def A0 (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) (τ σ : ℝ) : ℝ :=
  (phc δ k σ + Real.pi/2 + 2*Real.pi*k) +
    ∑ j ∈ Finset.range 9,
      (cj W ρh τ j - cj W ρh 0 j) * (σ^j / (Nat.factorial j : ℝ)) * jbump δ σ

/-- The phase of the collar, defined by the flux integral. -/
def AcF (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℝ :=
  A0 W ρh δ k τ σ +
    ∫ u in (0:ℝ)..t,
      Work.RPV.ωC (deriv (fun s => GAM CI W ρh δ k τ s u) σ)
        (deriv (fun s => GAM CI W ρh δ k τ σ s) u)

/-! ## 3'. The smooth phase constant

`A0` above is a *truncated Taylor polynomial* in `σ` whose coefficients are the `σ`-jets
`cj W ρh τ j` of the chart phase at `σ = 0`.  Those coefficients are only as regular in `τ` as
the `(12 - j)`-th derivative of the chart data, so `A0` itself is not `C⁸` in `τ`; the phase
`AcF = A0 + ∫ ω_ℂ(∂_σΓc, ∂_tΓc)` therefore fails to be `C⁸` jointly in `(τ, σ, t)`, which the
collar statement requires.

`A0s` avoids the truncation: it *is* the chart phase itself, cut off away from `σ = 0` by the
conjugate of the blend cutoff, so it is as regular in `τ` as the chart data, while having exactly
the same `σ`-jets at `σ = 0` as `A0` (the cutoff is identically `1` near `0`).  All the other
properties asked of `A0` are preserved: it vanishes for `σ ≥ 2δ` and reduces to
`phc δ k σ + π/2 + 2πk` on the `τ = 0` slice. -/

/-- The smooth phase constant: the chart phase `σ ↦ (W τ 0 (ρh τ 0 σ)).1.2`, corrected by the
`τ = 0` chart phase, cut off away from `σ = 0` (where the cutoff `1 - blf δ` is identically `1`). -/
def A0s (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) (τ σ : ℝ) : ℝ :=
  phc δ k σ + Real.pi/2 + 2*Real.pi*k +
    ((W τ 0 (ρh τ 0 σ)).1.2 - (W 0 0 (ρh 0 0 σ)).1.2) * (1 - blf δ σ)

/-- A *symmetric* cutoff in the level: `1` for `|σ| ≤ δ/2`, `0` for `|σ| ≥ δ`.  (The square `σ²`
makes it smooth across `σ = 0`.) -/
def ctf (δ σ : ℝ) : ℝ := 1 - stp (2 * ((σ/δ)^2 - 1/4))

/-- The phase constant actually used by the collar: `A0s` near `σ = 0`, smoothly interpolated (on
*both* sides) to the constant `phc δ k σ + π/2 + 2πk` away from the `τ = 0` region.

`A0s` itself only has a one-sided cutoff (`1 - blf δ`, which is `1` for all `σ ≤ δ/2`), so it is
evaluated at levels `ρh τ 0 σ` that the hypotheses do not control when `σ ≤ -1`; the symmetric
cutoff `ctf` has support in `|σ| ≤ δ < 1`, so the chart phase is only ever needed on the range
where it is known to be `C¹²`.  The interpolation is the identity near `σ = 0`, so `A0i` has the
same `σ`-jets at `0` as `A0s` (hence as `A0`), it vanishes for `σ ≥ 2δ` and it reduces to
`phc δ k σ + π/2 + 2πk` on the `τ = 0` slice. -/
def A0i (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) (τ σ : ℝ) : ℝ :=
  A0s W ρh δ k τ σ * ctf δ σ
    + (phc δ k σ + Real.pi/2 + 2*Real.pi*k) * (1 - ctf δ σ)

/-- The collar phase built on the smooth constant `A0i`: the flux primitive of the collar curve
family.  It differs from `AcF` by `A0i - A0`, a function whose `σ`-jets at `σ = 0` all vanish, so
the two phases have the same one-sided `σ`-jets at `0` (whence the same induced level points to all
orders at `σ = 0`). -/
def AcS (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℝ :=
  A0i W ρh δ k τ σ +
    ∫ u in (0:ℝ)..t,
      Work.RPV.ωC (deriv (fun s => GAM CI W ρh δ k τ s u) σ)
        (deriv (fun s => GAM CI W ρh δ k τ σ s) u)

end Work.RPB.B5
