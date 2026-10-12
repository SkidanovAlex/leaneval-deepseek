import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import ChallengeDeps
import Submission.CubicChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, brick B2 — the renormalized kernel calculus (kernel identities)

This module formalizes the Fournais--Solovej *renormalized kernel identities*
(eq:DefU, eq:w2int, lem:LocPotential of `final_v2.tex`, lines ~817--895 and
~975--985): with the cubic bump `χ` of `Submission.CubicChi`,
`g := v(1−ω)` (`ω` the scattering solution; only the abstract properties
below are used), the scaled kernels

    χ_ℓ(x) := χ(x/ℓ),   (χ⋆χ)_ℓ(x) := (χ⋆χ)(x/ℓ),
    W₁(x)  := g(x) / (χ⋆χ)_ℓ(x),     w₁(x,y) := χ_ℓ(x)W₁(x−y)χ_ℓ(y),
    W₂(x)  := h(x) / (χ⋆χ)_ℓ(x),     w₂(x,y) := χ_ℓ(x)W₂(x−y)χ_ℓ(y)   (h := g(1+ω))

satisfy the *box identities*

    (1/2)ℓ⁻⁶ ∬_{ℝ³×ℝ³} w₁(x,y) dxdy  = (1/2)ℓ⁻³ ∫g  = 4πaℓ⁻³            (eq:DefU)
    (1/2)ℓ⁻⁶ ∬ w₂(x,y) dxdy           = (1/2)ℓ⁻³ ∫g(1+ω)                (eq:w2int)

and the *reconstruction identity* (lem:LocPotential; `w_u` = cell-`u`
translate `w(x−ℓu, y−ℓu)`; here `chiU ℓ u x := χ((x−ℓu)/ℓ)`)

    ∫_{ℝ³} w_u(x,y) du = h(x−y)      (h := v or g)

used in the localization formula.  In Lean there is no vector division
`x/ℓ`; the scaling is `(ℓ⁻¹) • x` (`chiScale ℓ x := χ((ℓ⁻¹)•x)`).  All
kernels are defined as total functions (division by zero returns `0`); the
identity lemmas carry the hypothesis that the denominator is nonzero (on the
support of the numerator this is guaranteed once `ℓ·r₀ ≥ R` with `r₀` from
`CubicChi.half_lower_ball_of_continuousAt_one`, P4: `(χ⋆χ) ≥ 1/2` on
`ball 0 r₀`).

## Proof routes (given to the child)

* `chiU_chiU_integral`: substitute `u ↦ w := (ℓ⁻¹)•x − u` in the `u`-integral
  (a translation + negation of `ℝ³`, measure-preserving; use
  `MeasureTheory.measurePreserving_neg`/`MeasurePreserving.add_right` +
  `MeasurePreserving.integral_comp`), obtaining
  `∫_w χ(w)·χ(w + (ℓ⁻¹)•(y−x)) dw`; then apply evenness of `χ`
  (`chi_even`) to rewrite as `∫_w χ(w)·χ((ℓ⁻¹)•(x−y) − w) dw`, which is
  exactly `conv3 chi chi ((ℓ⁻¹)•(x−y))` by the definition of `conv3`
  (need `MeasureTheory.integral_comp`/congr along the way).

* `wScaled_integral`: for fixed `x,y` the `u`-integrand is the constant
  `wScaled ℓ h (x−y)` times `chiU ℓ u x · chiU ℓ u y`; pull the constant out
  (integral_mul_const / integral_const_mul), then `chiU_chiU_integral` and
  the field law `(a/c)·c = a` for `c ≠ 0`.

* `kernel_double_integral`: write `J(x) := ∫_y χ_ℓ(y)·(g(x−y)/C_ℓ(x−y)) dy`;
  substitute `z = x−y` (i.e. `y = x−z`, measure-preserving) to get
  `J(x) = ∫_z χ_ℓ(x−z)·(g(z)/C_ℓ(z)) dz`; hence the double integral is
  `∫_x∫_z χ_ℓ(x)·χ_ℓ(x−z)·(g(z)/C_ℓ(z)) dz dx`.  Apply Fubini/Tonelli
  (justify integrability with Cauchy--Schwarz `∫_x χ_ℓ(x)χ_ℓ(x−z) dx ≤ ℓ³`,
  from `∫χ² = 1`), and use the inner integral
  `∫_x χ_ℓ(x)χ_ℓ(x−z) dx = ℓ³·C_ℓ(z)` (substitute `x = ℓs`, use evenness:
  `∫_s χ(s)χ(s − z/ℓ) ds = (χ⋆χ)(z/ℓ)`, with the volume factor `ℓ³` from
  `dx = ℓ³ ds` — a single-variable scaling substitution on `ℝ³`, e.g.
  via the linear equivalence `s ↦ ℓ•s` and `MeasureTheory.map_linearMap_...`
  or the volume-factor lemma used elsewhere in the corpus).  Pointwise
  `C_ℓ(z)·(g(z)/C_ℓ(z)) = g(z)` for all `z`: if `C_ℓ(z) ≠ 0` the field law;
  if `C_ℓ(z) = 0` then `g(z) = 0` (contrapositive of `hgsupp` together with
  `hRℓ`, `hC`).  Then `∫_z ℓ³·g(z) = ℓ³·∫g`.

* `eq_DefU_norm`: divide `kernel_double_integral` by `(1/2)ℓ⁻⁶`-normalization:
  `(1/2)·ℓ^(-6:ℤ)·(ℓ^3·∫g) = (1/2)·ℓ^(-3:ℤ)·∫g` by zpow algebra
  (`ℓ^(-6:ℤ) = ℓ^(-3:ℤ)·ℓ^(-3:ℤ)`-style, `zpow_add`, `zpow_neg`, hℓ).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real Convolution

namespace Submission.BoseGases

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The scaled bump `χ(x/ℓ)` — in Lean `χ((ℓ⁻¹) • x)`. -/
noncomputable def chiScale (ℓ : ℝ) (x : ℝ³) : ℝ := chi ((ℓ⁻¹) • x)

/-- The scaled convolution `(χ⋆χ)(x/ℓ)` — in Lean `conv3 chi chi ((ℓ⁻¹) • x)`. -/
noncomputable def convScale (ℓ : ℝ) (x : ℝ³) : ℝ := conv3 chi chi ((ℓ⁻¹) • x)

/-- The cell-`u` translate of the bump: `χ((x − ℓu)/ℓ) = χ((ℓ⁻¹)•x − u)`. -/
noncomputable def chiU (ℓ : ℝ) (u : ℝ³) (x : ℝ³) : ℝ := chi ((ℓ⁻¹) • x - u)

/-- The renormalized kernel `W(x) := h(x) / (χ⋆χ)(x/ℓ)` for a numerator
`h : ℝ³ → ℝ` (total function: division by zero is `0`). -/
noncomputable def wScaled (ℓ : ℝ) (h : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  h x / convScale ℓ x

/-- The localized two-body kernel `w(x,y) := χ_ℓ(x)·W(x−y)·χ_ℓ(y)` for the
numerator `h`. -/
noncomputable def wPair (ℓ : ℝ) (h : ℝ³ → ℝ) (x : ℝ³) (y : ℝ³) : ℝ :=
  chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ y

-- ======================================================================
-- elementary measure-preserving substitutions on ℝ³
-- ======================================================================

/-- Negation preserves the Lebesgue integral on `ℝ³`. -/
lemma integral_comp_neg (g : ℝ³ → ℝ) : (∫ y : ℝ³, g (-y)) = ∫ y : ℝ³, g y := by
  let e : ℝ³ ≃ᵐ ℝ³ := MeasurableEquiv.neg ℝ³
  have hmp : MeasurePreserving (⇑e) volume volume := by
    simpa [e, MeasurableEquiv.neg_apply] using
      (Measure.measurePreserving_neg (volume : Measure ℝ³))
  simpa [e, MeasurableEquiv.neg_apply] using (hmp.integral_comp' (f := e) (g := g))

/-- Translation preserves the Lebesgue integral on `ℝ³`. -/
lemma integral_comp_add_left (g : ℝ³ → ℝ) (c : ℝ³) : (∫ y : ℝ³, g (c + y)) = ∫ y : ℝ³, g y := by
  let e : ℝ³ ≃ᵐ ℝ³ := MeasurableEquiv.addLeft c
  have hmp : MeasurePreserving (⇑e) volume volume := by
    change MeasurePreserving (fun x : ℝ³ => c + x) volume volume
    exact measurePreserving_add_left volume c
  simpa [e] using (hmp.integral_comp' (f := e) (g := g))

-- The substitution `u ↦ c - u` preserves the Lebesgue integral on `ℝ³`. -/
lemma integral_comp_sub_left (g : ℝ³ → ℝ) (c : ℝ³) : (∫ y : ℝ³, g (c - y)) = ∫ y : ℝ³, g y := by
  calc
    (∫ y : ℝ³, g (c - y)) = ∫ y : ℝ³, (fun v : ℝ³ => g (c + v)) (-y) := by
      apply integral_congr_ae
      exact ae_of_all _ (by intro y; rfl)
    _ = ∫ v : ℝ³, g (c + v) := integral_comp_neg (fun v : ℝ³ => g (c + v))
    _ = ∫ y : ℝ³, g y := integral_comp_add_left g c
/-- `χ⋆χ` is even (from evenness of `χ`). -/
lemma conv3chi_even (x : ℝ³) : conv3 chi chi (-x) = conv3 chi chi x := by
  unfold conv3
  let g : ℝ³ → ℝ := fun z : ℝ³ => chi (-z) * chi (-x + z)
  calc
    (∫ y : ℝ³, chi y * chi (-x - y)) = ∫ z : ℝ³, g z := by
      have h := integral_comp_neg (g := g)
      -- h : ∫ z, g (-z) = ∫ z, g z ; note g (-y) = chi y * chi (-x - y)
      rw [← h]
      apply integral_congr_ae
      exact ae_of_all _ (by intro y; dsimp [g]; congr 1; abel)
    _ = ∫ y : ℝ³, chi y * chi (x - y) := by
      apply integral_congr_ae
      exact ae_of_all _ (by intro z; dsimp [g]; rw [chi_even z]; congr 1; rw [← chi_even (x - z)]; congr 1; abel)
    _ = ∫ y : ℝ³, chi y * chi (x - y) := rfl
/-- `χ_ℓ` is even. -/
lemma chiScale_even (ℓ : ℝ) (x : ℝ³) : chiScale ℓ (-x) = chiScale ℓ x := by
  unfold chiScale
  rw [smul_neg]
  exact chi_even ((ℓ⁻¹) • x)

/-- `χ_ℓ` is smooth (for `ℓ ≠ 0`). -/
lemma chiScale_contDiff {ℓ : ℝ} (hℓ : ℓ ≠ 0) : ContDiff ℝ ∞ (chiScale ℓ) := by
  unfold chiScale
  exact chi_contDiff.comp
    (ContinuousLinearMap.contDiff ((ℓ⁻¹) • ContinuousLinearMap.id ℝ ℝ³))

lemma chiScale_hasCompactSupport {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    HasCompactSupport (chiScale ℓ) := by
  unfold chiScale
  let φ : ℝ³ ≃ₜ ℝ³ := Homeomorph.smulOfNeZero (ℓ⁻¹) (inv_ne_zero hℓ)
  convert chi_hasCompactSupport.comp_homeomorph φ using 1
  ext x
  simp [φ, Homeomorph.smulOfNeZero]

/-- The cell-`u` bump is smooth in `(u,x)`. -/
lemma chiU_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (fun p : ℝ³ × ℝ³ => chiU ℓ p.1 p.2) := by
  unfold chiU
  have hlin : ContDiff ℝ ∞ (fun p : ℝ³ × ℝ³ => (ℓ⁻¹) • p.2 - p.1) := by
    let proj1 : (ℝ³ × ℝ³) →L[ℝ] ℝ³ := ContinuousLinearMap.fst ℝ ℝ³ ℝ³
    let proj2 : (ℝ³ × ℝ³) →L[ℝ] ℝ³ := ContinuousLinearMap.snd ℝ ℝ³ ℝ³
    let L : ℝ³ →L[ℝ] ℝ³ := (ℓ⁻¹) • ContinuousLinearMap.id ℝ ℝ³
    let T : (ℝ³ × ℝ³) →L[ℝ] ℝ³ := L.comp proj2 - proj1
    have hT : (fun p : ℝ³ × ℝ³ => (ℓ⁻¹) • p.2 - p.1) = ⇑T := by
      funext p
      simp [T, proj1, proj2, L]
    rw [hT]
    exact T.contDiff
  exact chi_contDiff.comp hlin

/-- `∫_u χ(a−u)·χ(b−u) du = (χ⋆χ)(a−b)` (a pure affine-translation identity). -/
lemma integral_chi_conv (a b : ℝ³) :
    (∫ u : ℝ³, chi (a - u) * chi (b - u)) = conv3 chi chi (a - b) := by
  calc
    (∫ u : ℝ³, chi (a - u) * chi (b - u))
        = ∫ w : ℝ³, chi (a - (a - w)) * chi (b - (a - w)) := by
          symm
          exact integral_comp_sub_left (g := fun u : ℝ³ => chi (a - u) * chi (b - u)) a
    _ = ∫ w : ℝ³, chi w * chi (w - (a - b)) := by
      apply integral_congr_ae
      exact ae_of_all _ (by
        intro w
        dsimp
        have hw1 : a - (a - w) = w := by abel
        have hw2 : b - (a - w) = w - (a - b) := by abel
        rw [hw1, hw2])
    _ = ∫ w : ℝ³, chi w * chi ((a - b) - w) := by
      apply integral_congr_ae
      exact ae_of_all _ (by
        intro w
        dsimp
        have hw : w - (a - b) = -((a - b) - w) := by abel
        rw [hw]
        rw [chi_even ((a - b) - w)])
    _ = conv3 chi chi (a - b) := by
      unfold conv3
      rfl

/-- `∫_u χ_u(x)·χ_u(y) du = (χ⋆χ)((x−y)/ℓ) = convScale ℓ (x−y)` — the
identity `eq:transInv`/convolution normalization underlying eq:DefU. -/
theorem chiU_chiU_integral (ℓ : ℝ) (hℓ : ℓ ≠ 0) (x y : ℝ³) :
    (∫ u : ℝ³, chiU ℓ u x * chiU ℓ u y) = convScale ℓ (x - y) := by
  let a : ℝ³ := (ℓ⁻¹) • x
  let b : ℝ³ := (ℓ⁻¹) • y
  calc
    (∫ u : ℝ³, chiU ℓ u x * chiU ℓ u y) = ∫ u : ℝ³, chi (a - u) * chi (b - u) := by
      apply integral_congr_ae
      exact ae_of_all _ (by intro u; dsimp [chiU, a, b])
    _ = conv3 chi chi (a - b) := integral_chi_conv a b
    _ = convScale ℓ (x - y) := by
      dsimp [convScale, a, b]
      congr 1
      rw [smul_sub]

/-- The reconstruction identity (lem:LocPotential, two-body part):
`∫_u w_u(x,y) du = h(x−y)` pointwise, wherever the denominator
`convScale ℓ (x−y) ≠ 0`. -/
theorem wScaled_integral (h : ℝ³ → ℝ) (ℓ : ℝ) (hℓ : ℓ ≠ 0) (x y : ℝ³)
    (hC : convScale ℓ (x - y) ≠ 0) :
    (∫ u : ℝ³, chiU ℓ u x * wScaled ℓ h (x - y) * chiU ℓ u y) = h (x - y) := by
  let c : ℝ := h (x - y) / convScale ℓ (x - y)
  have hsc : wScaled ℓ h (x - y) = c := by
    dsimp [c, wScaled]
  calc
    (∫ u : ℝ³, chiU ℓ u x * wScaled ℓ h (x - y) * chiU ℓ u y)
        = ∫ u : ℝ³, c * (chiU ℓ u x * chiU ℓ u y) := by
      apply integral_congr_ae
      exact ae_of_all _ (by intro u; dsimp; rw [hsc]; ring)
    _ = c * (∫ u : ℝ³, chiU ℓ u x * chiU ℓ u y) := by
      rw [integral_const_mul]
    _ = c * convScale ℓ (x - y) := by
      rw [chiU_chiU_integral ℓ hℓ x y]
    _ = h (x - y) := by
      dsimp [c]
      field_simp [hC]

-- ======================================================================
-- scaling substitutions and their volume factors (on ℝ³)
-- ======================================================================

/-- `Measure.map (x ↦ ℓ•x)` rescales the volume on `ℝ³` by `|ℓ³|⁻¹`. -/
lemma map_smul_volume (ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    Measure.map (fun x : ℝ³ => ℓ • x) volume =
      ENNReal.ofReal (|(ℓ ^ (Module.finrank ℝ ℝ³))⁻¹|) • (volume : Measure ℝ³) :=
  Measure.map_addHaar_smul (μ := (volume : Measure ℝ³)) (r := ℓ) hℓ

/-- `Measure.map (x ↦ ℓ•x)` rescales the volume on `ℝ³` by `ℓ⁻³` (positive case). -/
lemma map_smul_volume3 (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Measure.map (fun x : ℝ³ => ℓ • x) volume =
      ENNReal.ofReal ((ℓ ^ 3)⁻¹) • (volume : Measure ℝ³) := by
  have hfr : Module.finrank ℝ ℝ³ = 3 := by norm_num
  simpa [hfr, abs_of_nonneg (le_of_lt (inv_pos.mpr (pow_pos hℓ 3)))] using
    map_smul_volume ℓ (ne_of_gt hℓ)

/-- Substituting `s ↦ ℓ•s` in an integral over `ℝ³` brings a factor `ℓ⁻³`. -/
lemma integral_comp_smul_left (g : ℝ³ → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ s : ℝ³, g (ℓ • s)) = (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, g x) := by
  let φ : ℝ³ ≃ₜ ℝ³ := Homeomorph.smulOfNeZero ℓ (ne_of_gt hℓ)
  have hfun : (fun x : ℝ³ => ℓ • x) = ⇑φ := by
    funext x
    simp [φ, Homeomorph.smulOfNeZero]
  have hemb : MeasurableEmbedding (fun x : ℝ³ => ℓ • x) := by
    have hemb0 : MeasurableEmbedding ⇑φ := (Homeomorph.measurableEmbedding φ)
    simpa [← hfun] using hemb0
  have hint := hemb.integral_map (μ := (volume : Measure ℝ³)) (g := g)
  calc
    (∫ s : ℝ³, g (ℓ • s)) = ∫ y : ℝ³, g y ∂(Measure.map (fun x : ℝ³ => ℓ • x) volume) := hint.symm
    _ = ∫ y : ℝ³, g y ∂(ENNReal.ofReal ((ℓ ^ 3)⁻¹) • (volume : Measure ℝ³)) := by
        rw [map_smul_volume3 ℓ hℓ]
    _ = (ENNReal.ofReal ((ℓ ^ 3)⁻¹)).toReal • (∫ x : ℝ³, g x) := by
        rw [integral_smul_measure]
    _ = (ℓ ^ 3)⁻¹ * (∫ x : ℝ³, g x) := by
        have hnn : 0 ≤ (ℓ ^ 3)⁻¹ := le_of_lt (inv_pos.mpr (pow_pos hℓ 3))
        simp [ENNReal.toReal_ofReal hnn]

/-- Substituting `x = ℓ•s` in an integral over `ℝ³` brings a factor `ℓ³`. -/
lemma integral_comp_smul_right (g : ℝ³ → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x : ℝ³, g x) = ℓ ^ 3 * (∫ s : ℝ³, g (ℓ • s)) := by
  have h := integral_comp_smul_left (g := g) hℓ
  -- (∫ s, g (ℓ•s)) = (ℓ^3)⁻¹ * ∫g
  calc
    (∫ x : ℝ³, g x) = ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * (∫ x : ℝ³, g x)) := by
        field_simp [ne_of_gt (pow_pos hℓ 3)]
    _ = ℓ ^ 3 * (∫ s : ℝ³, g (ℓ • s)) := by rw [h]

/-- `χ_ℓ(ℓ•s) = χ(s)`. -/
lemma chiScale_apply_smul {ℓ : ℝ} (hℓ : ℓ ≠ 0) (s : ℝ³) : chiScale ℓ (ℓ • s) = chi s := by
  dsimp [chiScale]
  congr 1
  rw [smul_smul]
  simp [hℓ]

/-- `χ_ℓ(ℓ•s − z) = χ(s − (ℓ⁻¹)•z)`. -/
lemma chiScale_apply_smul_sub {ℓ : ℝ} (hℓ : ℓ ≠ 0) (s z : ℝ³) :
    chiScale ℓ (ℓ • s - z) = chi (s - (ℓ⁻¹) • z) := by
  dsimp [chiScale]
  congr 1
  rw [smul_sub, smul_smul]
  simp [hℓ]

/-- `χ_ℓ` is nonnegative. -/
lemma chiScale_nonneg (ℓ : ℝ) (x : ℝ³) : 0 ≤ chiScale ℓ x := by
  exact chi_nonneg ((ℓ⁻¹) • x)

/-- `χ_ℓ(x) ≠ 0` forces `‖x‖ ≤ ℓ/2` (for `0 < ℓ`). -/
lemma chiScale_support_le {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℝ³} (hx : chiScale ℓ x ≠ 0) :
    ‖x‖ ≤ ℓ / 2 := by
  have h1 : ¬ 1 / 2 < ‖(ℓ⁻¹) • x‖ := by
    intro hb
    exact hx (chi_eq_zero_of_norm_gt ((ℓ⁻¹) • x) hb)
  have hle : ‖(ℓ⁻¹) • x‖ ≤ 1 / 2 := le_of_not_gt h1
  have hnorm : ‖(ℓ⁻¹) • x‖ = (ℓ⁻¹) * ‖x‖ := by
    rw [norm_smul]
    congr 1
    exact abs_of_nonneg (le_of_lt (inv_pos.mpr hℓ))
  rw [hnorm] at hle
  have hℓi : 0 < (ℓ⁻¹) := inv_pos.mpr hℓ
  calc
    ‖x‖ = (ℓ * (ℓ⁻¹)) * ‖x‖ := by field_simp [ne_of_gt hℓ]
    _ = ℓ * ((ℓ⁻¹) * ‖x‖) := by ring
    _ ≤ ℓ * (1 / 2) := by
      exact mul_le_mul_of_nonneg_left hle (le_of_lt hℓ)
    _ = ℓ / 2 := by ring

/-- `∫ₛ χ(s)·χ(s−w) ds = (χ⋆χ)(w)` (uses evenness of `χ`). -/
lemma integral_chi_mul_chi_sub (w : ℝ³) :
    (∫ s : ℝ³, chi s * chi (s - w)) = conv3 chi chi w := by
  calc
    (∫ s : ℝ³, chi s * chi (s - w)) = ∫ s : ℝ³, chi s * chi (w - s) := by
      apply integral_congr_ae
      exact ae_of_all _ (by
        intro s
        dsimp
        have hneg : s - w = -(w - s) := by abel
        rw [hneg]
        rw [chi_even (w - s)])
    _ = conv3 chi chi w := by
      unfold conv3
      rfl

/-- `∫ₓ χ_ℓ(x)·χ_ℓ(x−z) dx = ℓ³·(χ⋆χ)_ℓ(z)` — the volume-factor identity. -/
lemma integral_pair_scale {ℓ : ℝ} (hℓ : 0 < ℓ) (z : ℝ³) :
    (∫ x : ℝ³, chiScale ℓ x * chiScale ℓ (x - z)) = ℓ ^ 3 * convScale ℓ z := by
  let g : ℝ³ → ℝ := fun s : ℝ³ => chiScale ℓ s * chiScale ℓ (s - z)
  have hg : (fun s : ℝ³ => g (ℓ • s)) = fun s : ℝ³ => chi s * chi (s - (ℓ⁻¹) • z) := by
    funext s
    dsimp [g]
    rw [chiScale_apply_smul (ne_of_gt hℓ) s, chiScale_apply_smul_sub (ne_of_gt hℓ) s z]
  have hsc := integral_comp_smul_right (g := g) hℓ
  calc
    (∫ x : ℝ³, chiScale ℓ x * chiScale ℓ (x - z)) = ℓ ^ 3 * (∫ s : ℝ³, g (ℓ • s)) := hsc
    _ = ℓ ^ 3 * (∫ s : ℝ³, chi s * chi (s - (ℓ⁻¹) • z)) := by rw [hg]
    _ = ℓ ^ 3 * conv3 chi chi ((ℓ⁻¹) • z) := by
      rw [integral_chi_mul_chi_sub ((ℓ⁻¹) • z)]
    _ = ℓ ^ 3 * convScale ℓ z := by rw [convScale]

/-- `χ⋆χ` is pointwise nonnegative. -/
lemma conv3chi_nonneg (x : ℝ³) : 0 ≤ conv3 chi chi x := by
  unfold conv3
  apply integral_nonneg
  intro y
  exact mul_nonneg (chi_nonneg y) (chi_nonneg (x - y))

/-- `convScale` is pointwise nonnegative. -/
lemma convScale_nonneg (ℓ : ℝ) (x : ℝ³) : 0 ≤ convScale ℓ x := by
  dsimp [convScale]
  exact conv3chi_nonneg ((ℓ⁻¹) • x)

/-- `convScale` is pointwise nonnegative (in `z`). -/
lemma convScale_nonneg' (ℓ : ℝ) : 0 ≤ convScale ℓ := fun z => convScale_nonneg ℓ z


/-- `χ_ℓ` is continuous. -/
lemma chiScale_continuous (ℓ : ℝ) : Continuous (chiScale ℓ) := by
  change Continuous (fun x : ℝ³ => chi ((ℓ⁻¹) • x))
  exact chi_contDiff.continuous.comp
    (ContinuousLinearMap.contDiff (n := ∞) ((ℓ⁻¹) • ContinuousLinearMap.id ℝ ℝ³)).continuous

/-- `convScale ℓ` is continuous. -/
lemma convScale_continuous (ℓ : ℝ) : Continuous (convScale ℓ) := by
  change Continuous (fun x : ℝ³ => conv3 chi chi ((ℓ⁻¹) • x))
  exact conv_contDiff.continuous.comp
    (ContinuousLinearMap.contDiff (n := ∞) ((ℓ⁻¹) • ContinuousLinearMap.id ℝ ℝ³)).continuous

/-- `χ ≤ (∫χ²)⁻¹/²` pointwise. -/
lemma chi_le_sqrt_inv (x : ℝ³) : chi x ≤ (Real.sqrt chiNormSq)⁻¹ := by
  have hpos : 0 < Real.sqrt chiNormSq := Real.sqrt_pos.mpr chiNormSq_pos
  calc
    chi x = chiBase x / Real.sqrt chiNormSq := by rfl
    _ ≤ 1 / Real.sqrt chiNormSq := by
        exact div_le_div_of_nonneg_right (chiBase_le_one x) (le_of_lt hpos)
    _ = (Real.sqrt chiNormSq)⁻¹ := by rw [one_div]

/-- `|χ_ℓ| ≤ (∫χ²)⁻¹/²` pointwise. -/
lemma abs_chiScale_le (ℓ : ℝ) (x : ℝ³) : |chiScale ℓ x| ≤ (Real.sqrt chiNormSq)⁻¹ := by
  have hnn : 0 ≤ chiScale ℓ x := chiScale_nonneg ℓ x
  rw [abs_of_nonneg hnn]
  dsimp [chiScale]
  exact chi_le_sqrt_inv ((ℓ⁻¹) • x)

/-- The quotient numerator `h / (χ⋆χ)_ℓ` (total-function division). -/
noncomputable def kRat (h : ℝ³ → ℝ) (ℓ : ℝ) (z : ℝ³) : ℝ := h z / convScale ℓ z

/-- Away from the support of `h` the denominator `(χ⋆χ)_ℓ` is bounded below by `1/2`. -/
lemma convScale_ge_half_of_hnz {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hhsupp : ∀ x : ℝ³, R ≤ ‖x‖ → h x = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) {z : ℝ³} (hz : h z ≠ 0) :
    1 / 2 ≤ convScale ℓ z := by
  have hnR : ¬ R ≤ ‖z‖ := by
    intro hRz
    exact hz (hhsupp z hRz)
  have hzR : ‖z‖ ≤ R := le_of_lt (lt_of_not_ge hnR)
  have hℓi : 0 ≤ (ℓ⁻¹) := le_of_lt (inv_pos.mpr hℓ)
  have hwle : ‖(ℓ⁻¹) • z‖ ≤ r₀ := by
    have h1 : ‖(ℓ⁻¹) • z‖ ≤ (ℓ⁻¹) * R := by
      rw [norm_smul, Real.norm_of_nonneg hℓi]
      exact mul_le_mul_of_nonneg_left hzR hℓi
    have h2 : (ℓ⁻¹) * R ≤ r₀ := by
      calc
        (ℓ⁻¹) * R ≤ (ℓ⁻¹) * (ℓ * r₀) := mul_le_mul_of_nonneg_left hRℓ hℓi
        _ = r₀ := by field_simp [ne_of_gt hℓ]
    exact le_trans h1 h2
  have hc : 1 / 2 ≤ conv3 chi chi ((ℓ⁻¹) • z) := hC ((ℓ⁻¹) • z) hwle
  dsimp [convScale]
  exact hc

/-- Pointwise `K(z)·(χ⋆χ)_ℓ(z) = h(z)`. -/
lemma kRat_mul_convScale {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hhsupp : ∀ x : ℝ³, R ≤ ‖x‖ → h x = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (z : ℝ³) :
    kRat h ℓ z * convScale ℓ z = h z := by
  dsimp [kRat]
  by_cases hz : h z = 0
  · simp [hz]
  · have hhalf : 1 / 2 ≤ convScale ℓ z := convScale_ge_half_of_hnz hℓ hhsupp hRℓ hC hz
    have hpos : 0 < convScale ℓ z := lt_of_lt_of_le (by norm_num) hhalf
    field_simp [ne_of_gt hpos]

/-- Pointwise `|K(z)| ≤ 2·|h(z)|`. -/
lemma abs_kRat_le {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hhsupp : ∀ x : ℝ³, R ≤ ‖x‖ → h x = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (z : ℝ³) :
    |kRat h ℓ z| ≤ 2 * |h z| := by
  dsimp [kRat]
  by_cases hz : h z = 0
  · simp [hz]
  · have hhalf : 1 / 2 ≤ convScale ℓ z := convScale_ge_half_of_hnz hℓ hhsupp hRℓ hC hz
    have hpos : 0 < convScale ℓ z := lt_of_lt_of_le (by norm_num) hhalf
    have hcinv : (convScale ℓ z)⁻¹ ≤ 2 := by
      calc
        (convScale ℓ z)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
          have h := one_div_le_one_div_of_le (a := (1 / 2 : ℝ)) (b := convScale ℓ z)
            (by norm_num) hhalf
          simpa [one_div] using h
        _ = 2 := by norm_num
    calc
      |h z / convScale ℓ z| = |h z| * (convScale ℓ z)⁻¹ := by
        rw [abs_div, abs_of_nonneg (le_of_lt hpos), div_eq_mul_inv]
      _ ≤ |h z| * 2 := mul_le_mul_of_nonneg_left hcinv (abs_nonneg (h z))
      _ = 2 * |h z| := by ring

/-- For fixed `z`: `∫ₓ χ_ℓ(x)·χ_ℓ(x−z)·K(z) dx = ℓ³·h(z)`. -/
lemma integral_kernel_inner {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hhsupp : ∀ x : ℝ³, R ≤ ‖x‖ → h x = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (z : ℝ³) :
    (∫ x : ℝ³, chiScale ℓ x * chiScale ℓ (x - z) * kRat h ℓ z) = ℓ ^ 3 * h z := by
  calc
    (∫ x : ℝ³, chiScale ℓ x * chiScale ℓ (x - z) * kRat h ℓ z)
        = kRat h ℓ z * (∫ x : ℝ³, chiScale ℓ x * chiScale ℓ (x - z)) := by
      have hre : (fun x : ℝ³ => chiScale ℓ x * chiScale ℓ (x - z) * kRat h ℓ z)
               = fun x : ℝ³ => kRat h ℓ z * (chiScale ℓ x * chiScale ℓ (x - z)) := by
        funext x
        ring
      rw [hre, integral_const_mul]
    _ = kRat h ℓ z * (ℓ ^ 3 * convScale ℓ z) := by rw [integral_pair_scale hℓ z]
    _ = ℓ ^ 3 * (kRat h ℓ z * convScale ℓ z) := by ring
    _ = ℓ ^ 3 * h z := by rw [kRat_mul_convScale hℓ hhsupp hRℓ hC z]

/-- The product-space integrand `(x,z) ↦ χ_ℓ(x)χ_ℓ(x−z)K(z)` is AE strongly measurable. -/
lemma kernel_AEStronglyMeasurable (h : ℝ³ → ℝ) (hh : Integrable h) (ℓ : ℝ) :
    AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1 * chiScale ℓ (p.1 - p.2) * kRat h ℓ p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  let μ : Measure ℝ³ := volume
  have hcont1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1) :=
    (chiScale_continuous ℓ).comp continuous_fst
  have hcont2 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ (p.1 - p.2)) := by
    exact (chiScale_continuous ℓ).comp (continuous_fst.sub continuous_snd)
  have hAE1 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1) (μ.prod μ) :=
    hcont1.aestronglyMeasurable (μ := μ.prod μ)
  have hAE2 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => chiScale ℓ (p.1 - p.2)) (μ.prod μ) :=
    hcont2.aestronglyMeasurable (μ := μ.prod μ)
  have hAE0 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1 * chiScale ℓ (p.1 - p.2))
      (μ.prod μ) :=
    hAE1.mul hAE2
  have hinvmeas : Measurable (fun z : ℝ³ => (convScale ℓ z)⁻¹) := by
    have hinv : Measurable fun t : ℝ => t⁻¹ := by fun_prop
    exact hinv.comp (convScale_continuous ℓ).measurable
  have hAEh : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => h p.2) (μ.prod μ) := by
    simpa [μ] using (hh.aestronglyMeasurable.comp_snd (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³)))
  have hAEinv : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => (convScale ℓ p.2)⁻¹) (μ.prod μ) := by
    simpa [μ] using (hinvmeas.aestronglyMeasurable.comp_snd (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³)))
  have hAEk : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => kRat h ℓ p.2) (μ.prod μ) := by
    have hEq : (fun p : ℝ³ × ℝ³ => kRat h ℓ p.2)
             = fun p : ℝ³ × ℝ³ => h p.2 * (convScale ℓ p.2)⁻¹ := by
      funext p
      dsimp [kRat]
      rw [div_eq_mul_inv]
    rw [hEq]
    exact hAEh.mul hAEinv
  have hF : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1 * chiScale ℓ (p.1 - p.2) * kRat h ℓ p.2)
      (μ.prod μ) :=
    hAE0.mul hAEk
  simpa [μ] using hF

/-- The product-space kernel `(x,z) ↦ χ_ℓ(x)χ_ℓ(x−z)K(z)` is integrable. -/
lemma kernel_integrable_prod {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ) (hh : Integrable h)
    (hhsupp : ∀ x : ℝ³, R ≤ ‖x‖ → h x = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) :
    Integrable (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1 * chiScale ℓ (p.1 - p.2) * kRat h ℓ p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  let μ : Measure ℝ³ := volume
  let S : ℝ := (Real.sqrt chiNormSq)⁻¹
  have hsup : ∀ x : ℝ³, |chiScale ℓ x| ≤ S := by
    intro x
    dsimp [S]
    exact abs_chiScale_le ℓ x
  have hkbound : ∀ z : ℝ³, |kRat h ℓ z| ≤ 2 * |h z| :=
    abs_kRat_le hℓ hhsupp hRℓ hC
  have hSpos : 0 < S := by
    dsimp [S]
    exact inv_pos.mpr (Real.sqrt_pos.mpr chiNormSq_pos)
  have hdom : ∀ p : ℝ³ × ℝ³,
      |chiScale ℓ p.1 * chiScale ℓ (p.1 - p.2) * kRat h ℓ p.2|
        ≤ ((2 * S) * chiScale ℓ p.1) * |h p.2| := by
    intro p
    calc
      |chiScale ℓ p.1 * chiScale ℓ (p.1 - p.2) * kRat h ℓ p.2|
          = |chiScale ℓ p.1 * chiScale ℓ (p.1 - p.2)| * |kRat h ℓ p.2| := by rw [abs_mul]
      _ = (|chiScale ℓ p.1| * |chiScale ℓ (p.1 - p.2)|) * |kRat h ℓ p.2| := by rw [abs_mul]
      _ = (chiScale ℓ p.1 * |chiScale ℓ (p.1 - p.2)|) * |kRat h ℓ p.2| := by
          rw [abs_of_nonneg (chiScale_nonneg ℓ p.1)]
      _ ≤ (chiScale ℓ p.1 * S) * |kRat h ℓ p.2| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hsup (p.1 - p.2)) (chiScale_nonneg ℓ p.1))
            (abs_nonneg (kRat h ℓ p.2))
      _ ≤ (chiScale ℓ p.1 * S) * (2 * |h p.2|) := by
          exact mul_le_mul_of_nonneg_left (hkbound p.2)
            (mul_nonneg (chiScale_nonneg ℓ p.1) (le_of_lt hSpos))
      _ ≤ ((2 * S) * chiScale ℓ p.1) * |h p.2| := by
          have heq : (chiScale ℓ p.1 * S) * (2 * |h p.2|)
                    = ((2 * S) * chiScale ℓ p.1) * |h p.2| := by ring
          rw [heq]
  have hfg : Integrable
      (fun p : ℝ³ × ℝ³ => ((2 * S) * chiScale ℓ p.1) * |h p.2|) (μ.prod μ) := by
    have hχint : Integrable (chiScale ℓ) μ := by
      exact Continuous.integrable_of_hasCompactSupport (chiScale_continuous ℓ)
        (chiScale_hasCompactSupport (ne_of_gt hℓ))
    have hf : Integrable (fun x : ℝ³ => (2 * S) * chiScale ℓ x) μ := hχint.const_mul (2 * S)
    have hg : Integrable (fun z : ℝ³ => |h z|) μ := hh.abs
    exact hf.mul_prod hg
  refine Integrable.mono hfg (kernel_AEStronglyMeasurable h hh ℓ) ?_
  filter_upwards with p
  simpa [abs_of_pos hSpos, abs_of_nonneg (chiScale_nonneg ℓ p.1), mul_assoc, mul_left_comm, mul_comm]
    using hdom p

/-- The box identity for a general integrable numerator `h` (eq:DefU /
eq:w2int in raw form): for `0 < ℓ` with `(χ⋆χ) ≥ 1/2` on `ball 0 r₀` and
`R ≤ ℓ·r₀`, and `h` integrable with support inside `ball 0 R`,

    ∫_x ∫_y χ_ℓ(x)·χ_ℓ(y)·(h(x−y)/(χ⋆χ)_ℓ(x−y)) dxdy = ℓ³·∫h.  -/
theorem kernel_double_integral (h : ℝ³ → ℝ) {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hh : MeasureTheory.Integrable h)
    (hhsupp : ∀ x : ℝ³, R ≤ ‖x‖ → h x = 0)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) :
    (∫ x : ℝ³, ∫ y : ℝ³,
        chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y))) =
      ℓ ^ 3 * (∫ z : ℝ³, h z) := by
  let K : ℝ³ → ℝ := fun z => h z / convScale ℓ z
  have hsub : ∀ x : ℝ³,
      (∫ y : ℝ³, chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)))
        = ∫ z : ℝ³, chiScale ℓ x * chiScale ℓ (x - z) * K z := by
    intro x
    let M : ℝ³ → ℝ := fun y => chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y))
    calc
      (∫ y : ℝ³, chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)))
          = ∫ y : ℝ³, M y := by rfl
      _ = ∫ z : ℝ³, M (x - z) := (integral_comp_sub_left (g := M) x).symm
      _ = ∫ z : ℝ³, chiScale ℓ x * chiScale ℓ (x - z) * K z := by
          apply integral_congr_ae
          exact ae_of_all _ (by
            intro z
            dsimp [M, K]
            rw [show x - (x - z) = z by abel])
  calc
    (∫ x : ℝ³, ∫ y : ℝ³,
        chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)))
        = ∫ x : ℝ³, (∫ z : ℝ³, chiScale ℓ x * chiScale ℓ (x - z) * K z) := by
            apply integral_congr_ae
            exact ae_of_all _ (by intro x; dsimp; exact hsub x)
    _ = ∫ z : ℝ³, (∫ x : ℝ³, chiScale ℓ x * chiScale ℓ (x - z) * K z) := by
            have hInt : Integrable
                (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1 * chiScale ℓ (p.1 - p.2) * K p.2)
                ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
              have h := kernel_integrable_prod (h := h) hℓ hh hhsupp hRℓ hC
              simpa [K, kRat] using h
            have hswap := MeasureTheory.integral_integral_swap
              (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
              (f := fun x z : ℝ³ => chiScale ℓ x * chiScale ℓ (x - z) * K z) hInt
            simpa [Function.uncurry] using hswap
    _ = ∫ z : ℝ³, ℓ ^ 3 * h z := by
            apply integral_congr_ae
            exact ae_of_all _ (by
              intro z
              dsimp
              have hz := integral_kernel_inner (h := h) hℓ hhsupp hRℓ hC z
              simpa [K, kRat] using hz)
    _ = ℓ ^ 3 * (∫ z : ℝ³, h z) := by
            rw [integral_const_mul]

/-- **eq:DefU** — the FS-normalized form:
`(1/2)ℓ⁻⁶∬w₁ = (1/2)ℓ⁻³∫h` (with `h` playing the role of `g := v(1−ω)`;
the last equality `(1/2)ℓ⁻³∫g = 4πaℓ⁻³` needs `∫g = 8πa`, a scattering fact
used at instantiation time, not here). -/
theorem eq_DefU_norm (h : ℝ³ → ℝ) {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hh : MeasureTheory.Integrable h)
    (hhsupp : ∀ x : ℝ³, R ≤ ‖x‖ → h x = 0)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) :
    (1 / 2) * ℓ ^ (-6 : ℤ) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y))) =
      (1 / 2) * ℓ ^ (-3 : ℤ) * (∫ z : ℝ³, h z) := by
  have hmain := kernel_double_integral h hℓ hh hhsupp hr₀ hRℓ hC
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hcoef : ℓ ^ (-6 : ℤ) * ℓ ^ 3 = ℓ ^ (-3 : ℤ) := by
    change ℓ ^ (-6 : ℤ) * ℓ ^ (3 : ℤ) = ℓ ^ (-3 : ℤ)
    rw [← zpow_add₀ hℓne]
    norm_num
  calc
    (1 / 2) * ℓ ^ (-6 : ℤ) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)))
        = (1 / 2) * ℓ ^ (-6 : ℤ) * (ℓ ^ 3 * (∫ z : ℝ³, h z)) := by rw [hmain]
    _ = (1 / 2) * (ℓ ^ (-6 : ℤ) * ℓ ^ 3) * (∫ z : ℝ³, h z) := by ring
    _ = (1 / 2) * (ℓ ^ (-3 : ℤ)) * (∫ z : ℝ³, h z) := by rw [hcoef]
    _ = (1 / 2) * ℓ ^ (-3 : ℤ) * (∫ z : ℝ³, h z) := by ring

end BoseGases

end Submission
