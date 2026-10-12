import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.ConvChiBound
import Submission.ScatKernelChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# NewtonCoulomb — the x-space Coulomb-energy dictionary (corpus form of FS eq:I2-integral)

The Fournais--Solovej box analysis needs, at several points (the proof of
`eq:I2-integral` / `eq:I2-integral-2` used inside the Bogoliubov
diagonalization and in `thm:Control3Q`), estimates comparing quantities
built from the *renormalized* kernel `W₁ := g₀/(χ⋆χ)(·/ℓ)` with the same
quantities built from the bare kernel `g₀ = v(1−w₀)`, where the difference
is controlled by `δ := 2C(R/ℓ)²` (the sandwich of `ConvChiBound.wScaled_sandwich`,
FS eq:W1-g).

In x-space (the corpus's Fourier-free route; see NOTES.md Session 28) the
Fourier-mode quantity `(2π)⁻³∫ W₁̂(k)²/(2k²) dk` is identified with the
Coulomb double integral `J(W₁) := (1/8π)∫∫ W₁(x)W₁(y)/‖x−y‖ dx dy` via the
Newton-kernel identity `(2π)⁻³∫e^{ik·z}/k² dk = 1/(4π‖z‖)`, so that the FS
estimates become the *pure x-space* statements proved here:

  |J(W₁) − J(g₀)| ≤ δ(2+δ)·J(g₀),    J(g₀) = ∫g₀·w₀,     (eq:I2-integral)
  J(W₁−g₀)      ≤ δ²·J(g₀)                                (eq:I2-integral-2)

where `J(f) := (1/8π)∫∫f(x)f(y)(‖x−y‖:ℝ)⁻¹` and
`W₁ := wScaled ℓ (g0 v h)`, `g₀ := g0 v h := v(1−w₀)` for the chosen
radial scattering solution `w₀ := Classical.choose h` of the radial `v`
with `tsupport v ⊆ ball 0 R`.

Because `g₀` is only known to be non-negative *a.e.* (not pointwise: it is
`v·(1−w₀)` with `0 ≤ w₀ ≤ 1` a.e.), the sandwich is first proved per-point
(`wScaled_sandwich_at`, requiring only `0 ≤ g x` at the point) and then
lifted to an a.e. statement (`wScaled_sandwich_ae`); the integral estimates
then follow from a.e. bounds and the a.e. non-negativity of the factors,
via monotonicity of the non-negative-kernel double integral (lintegral /
ae reasoning, as in `ScatGIntegrals`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real

namespace Submission.BoseGases

set_option autoImplicit false

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The Coulomb kernel `‖x−y‖⁻¹` (with real division, so that it is `0` on
the diagonal and `≥ 0` everywhere). -/
def coulK (x y : ℝ³) : ℝ := (‖x - y‖ : ℝ)⁻¹

/-- **Per-point sandwich of the renormalized kernel** (eq:W1-g at a point):
given only `0 ≤ g x` at the point `x` (rather than globally), the conclusion
of `ConvChiBound.wScaled_sandwich` holds at `x`.  Copy the body of
`wScaled_sandwich` with the global hypothesis `hg : 0 ≤ g` replaced by
`hgx : 0 ≤ g x` (the body only ever uses `hg x`). -/
theorem wScaled_sandwich_at {g : ℝ³ → ℝ} {ℓ R r₁ C : ℝ} (hℓ : 0 < ℓ)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0) (hR : 0 ≤ R)
    (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) {x : ℝ³} (hgx : 0 ≤ g x) :
    g x ≤ wScaled ℓ g x ∧ wScaled ℓ g x ≤ g x * (1 + 2 * C * (R / ℓ) ^ 2) := by
  by_cases hx0 : g x = 0
  · simp [wScaled, hx0]
  · have hgpos : 0 < g x := lt_of_le_of_ne hgx (Ne.symm hx0)
    have hxRlt : ‖x‖ < R := by
      by_contra hn
      have hRle : R ≤ ‖x‖ := le_of_not_gt hn
      exact (hgpos.ne' (hgsupp x hRle))
    let y : ℝ³ := (ℓ⁻¹) • x
    let u : ℝ := C * (R / ℓ) ^ 2
    have hℓi : 0 < (ℓ⁻¹) := inv_pos.mpr hℓ
    have hu0 : 0 ≤ u := by
      dsimp [u]
      exact mul_nonneg hC (sq_nonneg (R / ℓ))
    have hcondU : u ≤ 1 / 2 := by
      simpa [u] using hcond
    have hyRlt : ‖y‖ < R / ℓ := by
      dsimp [y]
      calc
        ‖(ℓ⁻¹) • x‖ = (ℓ⁻¹) * ‖x‖ := norm_smul_of_nonneg (ℓ⁻¹) (le_of_lt hℓi) x
        _ < (ℓ⁻¹) * R := mul_lt_mul_of_pos_left hxRlt hℓi
        _ = R / ℓ := by ring
    have hyle : ‖y‖ ≤ r₁ := by
      exact le_of_lt (lt_of_lt_of_le hyRlt hreg)
    have hT' := hT y hyle
    have hbnd : C * ‖y‖ ^ 2 ≤ u := by
      dsimp [u]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg y) (le_of_lt hyRlt) 2) hC
    have hCu : |conv3 chi chi y - 1| ≤ u := le_trans hT' hbnd
    have hCu' := (abs_le.mp hCu)
    have hcge : 1 - u ≤ conv3 chi chi y := by linarith
    have hcup : conv3 chi chi y ≤ 1 + u := by linarith
    have hcpos : 0 < conv3 chi chi y := by
      have hcone : 0 < 1 - u := by linarith
      exact lt_of_lt_of_le hcone hcge
    have hconvle1 : convScale ℓ x ≤ 1 := by
      dsimp [convScale, y]
      exact conv3chi_le_one ((ℓ⁻¹) • x)
    have hconvge : 1 - u ≤ convScale ℓ x := by
      dsimp [convScale, y]
      exact hcge
    have hconvpos : 0 < convScale ℓ x := by
      dsimp [convScale, y]
      exact hcpos
    -- left inequality: `g x ≤ g x / C_ℓ(x)`
    have hleft : g x ≤ wScaled ℓ g x := by
      dsimp [wScaled]
      rw [le_div_iff₀ hconvpos]
      have hprod : 0 ≤ g x * (1 - convScale ℓ x) :=
        mul_nonneg hgx (sub_nonneg.mpr hconvle1)
      nlinarith
    -- right inequality: `g x / C_ℓ(x) ≤ g x (1 + 2u)`, using `1 ≤ (1+2u)C_ℓ(x)`
    have h1p2u : 0 ≤ 1 + 2 * u := by nlinarith
    have hprodpos : 0 ≤ u * (1 - 2 * u) :=
      mul_nonneg hu0 (sub_nonneg.mpr (by linarith))
    have hpoly1 : 1 ≤ (1 - u) * (1 + 2 * u) := by
      nlinarith [hprodpos]
    have hstep : (1 - u) * (1 + 2 * u) ≤ convScale ℓ x * (1 + 2 * u) := by
      exact mul_le_mul_of_nonneg_right hconvge h1p2u
    have hcbig : 1 ≤ (1 + 2 * u) * convScale ℓ x := by
      calc
        1 ≤ convScale ℓ x * (1 + 2 * u) := le_trans hpoly1 hstep
        _ = (1 + 2 * u) * convScale ℓ x := by ring
    have hright : wScaled ℓ g x ≤ g x * (1 + 2 * u) := by
      dsimp [wScaled]
      rw [div_le_iff₀ hconvpos]
      have hprod2 : 0 ≤ g x * ((1 + 2 * u) * convScale ℓ x - 1) :=
        mul_nonneg hgx (sub_nonneg.mpr hcbig)
      nlinarith
    constructor
    · exact hleft
    · dsimp [u] at hright
      convert hright using 1
      ring


/-- **A.e. sandwich** of the renormalized kernel for an a.e.-non-negative
`g` supported in `ball 0 R`. -/
theorem wScaled_sandwich_ae {g : ℝ³ → ℝ} {ℓ R r₁ C : ℝ} (hℓ : 0 < ℓ)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hg : ∀ᵐ x : ℝ³, 0 ≤ g x) (hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0)
    (hR : 0 ≤ R) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    ∀ᵐ x : ℝ³, g x ≤ wScaled ℓ g x ∧ wScaled ℓ g x ≤ g x * (1 + 2 * C * (R / ℓ) ^ 2) := by
  filter_upwards [hg] with x hgx
  exact wScaled_sandwich_at (g := g) (ℓ := ℓ) (R := R) (r₁ := r₁) (C := C) hℓ hC hr₁ hT
    hgsupp hR hreg hcond hgx

/-- **A.e. sandwich for the chosen `g₀`**: with `δ := 2C(R/ℓ)²` we have
`0 ≤ wScaled ℓ g₀ − g₀ ≤ δ·g₀` a.e. on ℝ³. -/
theorem wScaled_g0_ae_bounds {v : ℝ³ → ℝ} {R ℓ r₁ C : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    ∀ᵐ x : ℝ³,
      0 ≤ wScaled ℓ (g0 v h) x - g0 v h x ∧
        wScaled ℓ (g0 v h) x - g0 v h x ≤ (2 * C * (R / ℓ) ^ 2) * g0 v h x := by
  let g : ℝ³ → ℝ := g0 v h
  have hg0_nonneg : ∀ᵐ x : ℝ³, 0 ≤ g x := by
    simpa [g] using (g0_nonneg_ae (v := v) (R := R) hR hv_nonneg hvrad hv_supp h)
  have hg0supp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0 := by
    intro x hx
    simpa [g] using (g0_zero_of_norm_ge (v := v) (R := R) hv_supp hx h)
  have hsand := wScaled_sandwich_ae (g := g) (ℓ := ℓ) (R := R) (r₁ := r₁) (C := C) hℓ hC
    hr₁ hT hg0_nonneg hg0supp (le_of_lt hR) hreg hcond
  filter_upwards [hsand] with x hx
  constructor
  · linarith
  · nlinarith

/-- The Coulomb potential `x ↦ ∫_y f(y)·‖x−y‖⁻¹`. -/
noncomputable def coulPot (f : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  ∫ y : ℝ³, f y * (‖x - y‖ : ℝ)⁻¹

/-- `coulPot f x ≥ 0` pointwise in `x` whenever `f ≥ 0` a.e. -/
lemma coulPot_nonneg {f : ℝ³ → ℝ} (hf : ∀ᵐ y : ℝ³, 0 ≤ f y) (x : ℝ³) :
    0 ≤ coulPot f x := by
  dsimp [coulPot]
  exact MeasureTheory.integral_nonneg_of_ae (μ := volume) (f := fun y : ℝ³ => f y * (‖x - y‖ : ℝ)⁻¹)
    (by
      filter_upwards [hf] with y hy
      exact mul_nonneg hy (inv_nonneg.mpr (norm_nonneg (x - y))))

/-- The kernel `‖x−y‖⁻¹` is non-negative pointwise. -/
lemma coulK_nonneg (x y : ℝ³) : 0 ≤ (‖x - y‖ : ℝ)⁻¹ := by
  exact inv_nonneg.mpr (norm_nonneg (x - y))

/-- For each fixed `x`, the inner `y`-integral equals `f₁ x` times the Coulomb
potential of `f₂`, so the double integral collapses to a single `x`-integral. -/
lemma double_integral_eq_coulPot (f₁ f₂ : ℝ³ → ℝ) :
    (∫ x : ℝ³, ∫ y : ℝ³, f₁ x * f₂ y * (‖x - y‖ : ℝ)⁻¹) = ∫ x : ℝ³, f₁ x * coulPot f₂ x := by
  apply MeasureTheory.integral_congr_ae
  refine ae_of_all _ ?_
  intro x
  calc
    (∫ y : ℝ³, f₁ x * f₂ y * (‖x - y‖ : ℝ)⁻¹)
        = ∫ y : ℝ³, f₁ x * (f₂ y * (‖x - y‖ : ℝ)⁻¹) := by
            apply MeasureTheory.integral_congr_ae
            refine ae_of_all _ ?_
            intro y
            ring
    _ = f₁ x * (∫ y : ℝ³, f₂ y * (‖x - y‖ : ℝ)⁻¹) := by
            rw [MeasureTheory.integral_const_mul]
    _ = f₁ x * coulPot f₂ x := by rfl

/-- For a.e. `x ∈ ball 0 M` the slice `y ↦ |p(y)|·‖x−y‖⁻¹` is integrable
(`p ∈ L¹`, `p = 0` outside `closedBall 0 R`).  Wrapper around
`NewtonRep.kernel_abs_slice_integrable_ae`. -/
lemma coulPot_abs_slice_integrable_ae_ball {p : ℝ³ → ℝ} {R M : ℝ}
    (hp : MeasureTheory.Integrable p) (hpsupp : ∀ y : ℝ³, R ≤ ‖y‖ → p y = 0)
    (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : ℝ³) M)),
      MeasureTheory.Integrable (fun y : ℝ³ => |p y| * (‖x - y‖ : ℝ)⁻¹) := by
  have hslice := kernel_abs_slice_integrable_ae (g := p) (R := R) (M := M) hp hpsupp hR hM
  simpa [nPotKernel] using hslice

/-- For `2R ≤ ‖x‖` the slice `y ↦ |p(y)|·‖x−y‖⁻¹` is integrable (dominated by
`(2/‖x‖)·|p|`). -/
lemma coulPot_abs_slice_integrable_of_norm_ge {p : ℝ³ → ℝ} {R : ℝ}
    (hp : MeasureTheory.Integrable p) (hpsupp : ∀ y : ℝ³, R ≤ ‖y‖ → p y = 0)
    {x : ℝ³} (hx0 : 0 < ‖x‖) (hxR : 2 * R ≤ ‖x‖) :
    MeasureTheory.Integrable (fun y : ℝ³ => |p y| * (‖x - y‖ : ℝ)⁻¹) := by
  have hgabs : MeasureTheory.Integrable (fun y : ℝ³ => |p y|) := by
    refine MeasureTheory.Integrable.congr hp.norm ?_
    filter_upwards with y
    change ‖(p y : ℝ)‖ = |p y|
    rw [Real.norm_eq_abs]
  have hD : MeasureTheory.Integrable (fun y : ℝ³ => |p y| * (2 / ‖x‖)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgabs.const_mul (2 / ‖x‖)
  have hAEs : AEStronglyMeasurable (fun y : ℝ³ => |p y| * (‖x - y‖ : ℝ)⁻¹) := by
    have hgabsA : AEStronglyMeasurable (fun y : ℝ³ => |p y|) := by
      apply MeasureTheory.AEStronglyMeasurable.congr (hp.aestronglyMeasurable.norm)
      filter_upwards with y
      change ‖(p y : ℝ)‖ = |p y|
      rw [Real.norm_eq_abs]
    have hk : AEStronglyMeasurable (fun y : ℝ³ => (‖x - y‖ : ℝ)⁻¹) := by
      have hm : Measurable (fun y : ℝ³ => (‖x - y‖ : ℝ)⁻¹) := by
        refine Measurable.inv ?_
        exact measurable_norm.comp ((measurable_const : Measurable fun _ : ℝ³ => x).sub measurable_id)
      exact hm.stronglyMeasurable.aestronglyMeasurable
    exact hgabsA.mul hk
  have hbnd : ∀ y : ℝ³, ‖(|p y| * (‖x - y‖ : ℝ)⁻¹ : ℝ)‖ ≤ |p y| * (2 / ‖x‖) := by
    intro y
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg (p y)) (inv_nonneg.mpr (norm_nonneg (x - y))))]
    by_cases hy : ‖y‖ ≤ R
    · have hxy : ‖x‖ / 2 ≤ ‖x - y‖ := by
        have h1 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by
          have hh' : ‖(x - y) + y‖ ≤ ‖x - y‖ + ‖y‖ := norm_add_le (x - y) y
          have hh'' : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa using hh'
          linarith
        have hyhalf : ‖y‖ ≤ ‖x‖ / 2 := by linarith
        linarith
      have hxy0 : 0 < ‖x - y‖ := lt_of_lt_of_le (by linarith) hxy
      have hxhalf : 0 < ‖x‖ / 2 := by linarith
      have hi0 : (‖x - y‖ : ℝ)⁻¹ ≤ (‖x‖ / 2 : ℝ)⁻¹ := (inv_le_inv₀ hxy0 hxhalf).2 hxy
      have hid : (‖x‖ / 2 : ℝ)⁻¹ = 2 / ‖x‖ := by
        field_simp [hx0.ne']
      calc
        |p y| * (‖x - y‖ : ℝ)⁻¹ ≤ |p y| * ((‖x‖ / 2 : ℝ)⁻¹) := by
          exact mul_le_mul_of_nonneg_left hi0 (abs_nonneg (p y))
        _ = |p y| * (2 / ‖x‖) := by rw [hid]
    · have hp0 : p y = 0 := hpsupp y (le_of_not_ge hy)
      have h0 : 0 ≤ 2 / ‖x‖ := by positivity
      simp [hp0, h0]
  exact MeasureTheory.Integrable.mono' hD hAEs (ae_of_all _ hbnd)

/-- For a.e. `x : ℝ³` the slice `y ↦ |p(y)|·‖x−y‖⁻¹` is integrable
(`p ∈ L¹`, `p = 0` outside `closedBall 0 R`, `R > 0`). -/
lemma coulPot_abs_slice_integrable_ae {p : ℝ³ → ℝ} {R : ℝ}
    (hp : MeasureTheory.Integrable p) (hpsupp : ∀ y : ℝ³, R ≤ ‖y‖ → p y = 0)
    (hR : 0 < R) :
    ∀ᵐ x : ℝ³,
      MeasureTheory.Integrable (fun y : ℝ³ => |p y| * (‖x - y‖ : ℝ)⁻¹) := by
  let P : ℝ³ → Prop := fun x : ℝ³ =>
    MeasureTheory.Integrable (fun y : ℝ³ => |p y| * (‖x - y‖ : ℝ)⁻¹)
  have h2R : 0 ≤ 2 * R := by positivity
  have hballm : MeasurableSet (ball (0 : ℝ³) (2 * R)) := isOpen_ball.measurableSet
  have hres : ∀ᵐ x ∂(volume.restrict (ball (0 : ℝ³) (2 * R))), P x := by
    simpa [P] using (coulPot_abs_slice_integrable_ae_ball hp hpsupp (le_of_lt hR) h2R)
  have hresg : ∀ᵐ x : ℝ³, x ∈ ball (0 : ℝ³) (2 * R) → P x := by
    simpa [P] using ((MeasureTheory.ae_restrict_iff' hballm).mp hres)
  filter_upwards [hresg] with x hx
  by_cases hb : x ∈ ball (0 : ℝ³) (2 * R)
  · exact hx hb
  · have hge : 2 * R ≤ ‖x‖ := by
      have hlt0 : ¬ ‖x‖ < 2 * R := by simpa [Metric.mem_ball, dist_eq_norm] using hb
      exact le_of_not_gt hlt0
    have hx0 : 0 < ‖x‖ := lt_of_lt_of_le (mul_pos (by norm_num) hR) hge
    simpa [P] using (coulPot_abs_slice_integrable_of_norm_ge hp hpsupp hx0 hge)

/-- A.e.-version of the "inner potential" bound: if `p ≤ c·g` a.e. (`p,g ≥ 0`
a.e., both supported in `closedBall 0 R`), then `coulPot p ≤ c·coulPot g` a.e.
-/
lemma coulPot_le_ae {p g : ℝ³ → ℝ} {c : ℝ} {R : ℝ} (hR : 0 < R)
    (hp : MeasureTheory.Integrable p) (hg : MeasureTheory.Integrable g)
    (hpsupp : ∀ y : ℝ³, R ≤ ‖y‖ → p y = 0) (hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0)
    (hp0 : ∀ᵐ y : ℝ³, 0 ≤ p y) (hg0 : ∀ᵐ y : ℝ³, 0 ≤ g y)
    (hple : ∀ᵐ y : ℝ³, p y ≤ c * g y) (hc : 0 ≤ c) :
    ∀ᵐ x : ℝ³, coulPot p x ≤ c * coulPot g x := by
  have hs_p : ∀ᵐ x : ℝ³,
      MeasureTheory.Integrable (fun y : ℝ³ => |p y| * (‖x - y‖ : ℝ)⁻¹) :=
    coulPot_abs_slice_integrable_ae hp hpsupp hR
  have hs_g : ∀ᵐ x : ℝ³,
      MeasureTheory.Integrable (fun y : ℝ³ => |g y| * (‖x - y‖ : ℝ)⁻¹) :=
    coulPot_abs_slice_integrable_ae hg hgsupp hR
  filter_upwards [hs_p, hs_g] with x hxp hxg
  have hI_p : MeasureTheory.Integrable (fun y : ℝ³ => p y * (‖x - y‖ : ℝ)⁻¹) := by
    refine MeasureTheory.Integrable.congr hxp ?_
    filter_upwards [hp0] with y hy
    rw [abs_of_nonneg hy]
  have hI_g : MeasureTheory.Integrable (fun y : ℝ³ => g y * (‖x - y‖ : ℝ)⁻¹) := by
    refine MeasureTheory.Integrable.congr hxg ?_
    filter_upwards [hg0] with y hy
    rw [abs_of_nonneg hy]
  have hI_gc : MeasureTheory.Integrable (fun y : ℝ³ => c * g y * (‖x - y‖ : ℝ)⁻¹) := by
    refine MeasureTheory.Integrable.congr (hxg.const_mul c) ?_
    filter_upwards [hg0] with y hy
    rw [abs_of_nonneg hy]
    ring
  have hle_y : ∀ᵐ y : ℝ³, p y * (‖x - y‖ : ℝ)⁻¹ ≤ c * g y * (‖x - y‖ : ℝ)⁻¹ := by
    filter_upwards [hple] with y hy
    exact mul_le_mul_of_nonneg_right hy (inv_nonneg.mpr (norm_nonneg (x - y)))
  have hineq : (∫ y : ℝ³, p y * (‖x - y‖ : ℝ)⁻¹) ≤ (∫ y : ℝ³, c * g y * (‖x - y‖ : ℝ)⁻¹) := by
    exact MeasureTheory.integral_mono_ae hI_p hI_gc hle_y
  dsimp [coulPot]
  calc
    (∫ y : ℝ³, p y * (‖x - y‖ : ℝ)⁻¹) ≤ (∫ y : ℝ³, c * g y * (‖x - y‖ : ℝ)⁻¹) := hineq
    _ = c * (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹) := by
        calc
          (∫ y : ℝ³, c * g y * (‖x - y‖ : ℝ)⁻¹)
              = ∫ y : ℝ³, c * (g y * (‖x - y‖ : ℝ)⁻¹) := by
                  apply MeasureTheory.integral_congr_ae
                  refine ae_of_all _ ?_
                  intro y
                  ring
          _ = c * (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹) := by
                  rw [MeasureTheory.integral_const_mul]

/-- `coulPot p` is AE-strongly measurable when `p ∈ L¹` vanishes outside
`closedBall 0 R` (it is `8π` times the locally-integrable Newton potential). -/
lemma coulPot_aestronglyMeasurable {p : ℝ³ → ℝ} {R : ℝ}
    (hp : MeasureTheory.Integrable p) (hpsupp : ∀ y : ℝ³, R ≤ ‖y‖ → p y = 0)
    (hR : 0 ≤ R) : AEStronglyMeasurable (coulPot p) := by
  have hNli : LocallyIntegrable (newtonPotential p) :=
    newtonPotential_locallyIntegrable (g := p) (R := R) hp hpsupp hR
  have hN : AEStronglyMeasurable (newtonPotential p) := hNli.aestronglyMeasurable
  refine AEStronglyMeasurable.congr (hN.const_mul (8 * π)) ?_
  filter_upwards with x
  have hc : (8 : ℝ) * π ≠ 0 := by positivity
  unfold coulPot newtonPotential nPotKernel
  rw [← mul_assoc, one_div, mul_inv_cancel₀ hc, one_mul]

/-- Non-negativity of a two-level iterated integral from a.e.-in-x / a.e.-in-y
non-negativity of the integrand. -/
lemma iter_integral_nonneg_of_ae {f : ℝ³ → ℝ³ → ℝ}
    (hf : ∀ᵐ x : ℝ³, ∀ᵐ y : ℝ³, 0 ≤ f x y) :
    0 ≤ (∫ x : ℝ³, ∫ y : ℝ³, f x y) := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [hf] with x hx
  exact MeasureTheory.integral_nonneg_of_ae hx

/-- **Rectangular double-integral bound**: for `0 ≤ A ≤ cA·g` and `0 ≤ B ≤ cB·g`
a.e. (all supported in `closedBall 0 R`, integrable), the Coulomb double
integral of `A(x)B(y)/‖x−y‖` is `≤ cA·cB` times that of `g(x)g(y)/‖x−y‖`. -/
lemma coulomb_rect_le {R : ℝ} (hR : 0 < R) {A B g : ℝ³ → ℝ} {cA cB : ℝ}
    (hAI : MeasureTheory.Integrable A) (hBI : MeasureTheory.Integrable B)
    (hgI : MeasureTheory.Integrable g)
    (hAsupp : ∀ x : ℝ³, R ≤ ‖x‖ → A x = 0) (hBsupp : ∀ x : ℝ³, R ≤ ‖x‖ → B x = 0)
    (hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0)
    (hA0 : ∀ᵐ x : ℝ³, 0 ≤ A x) (hB0 : ∀ᵐ x : ℝ³, 0 ≤ B x) (hg0 : ∀ᵐ x : ℝ³, 0 ≤ g x)
    (hAle : ∀ᵐ x : ℝ³, A x ≤ cA * g x) (hBle : ∀ᵐ x : ℝ³, B x ≤ cB * g x)
    (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hVgInt : MeasureTheory.Integrable (fun x : ℝ³ => g x * coulPot g x)) :
    (∫ x : ℝ³, ∫ y : ℝ³, A x * B y * (‖x - y‖ : ℝ)⁻¹) ≤
      (cA * cB) * (∫ x : ℝ³, ∫ y : ℝ³, g x * g y * (‖x - y‖ : ℝ)⁻¹) := by
  have hD : (∫ x : ℝ³, ∫ y : ℝ³, A x * B y * (‖x - y‖ : ℝ)⁻¹)
      = ∫ x : ℝ³, A x * coulPot B x := double_integral_eq_coulPot A B
  have hDg : (∫ x : ℝ³, ∫ y : ℝ³, g x * g y * (‖x - y‖ : ℝ)⁻¹)
      = ∫ x : ℝ³, g x * coulPot g x := double_integral_eq_coulPot g g
  have hVle : ∀ᵐ x : ℝ³, coulPot B x ≤ cB * coulPot g x :=
    coulPot_le_ae (p := B) (g := g) (c := cB) (R := R) hR hBI hgI hBsupp hgsupp hB0 hg0 hBle hcB
  have hVg0 : ∀ x : ℝ³, 0 ≤ coulPot g x := coulPot_nonneg hg0
  have hVB0 : ∀ x : ℝ³, 0 ≤ coulPot B x := coulPot_nonneg hB0
  have hOut : ∀ᵐ x : ℝ³, A x * coulPot B x ≤ (cA * cB) * (g x * coulPot g x) := by
    filter_upwards [hA0, hVle, hAle] with x hA0x hVlex hAlex
    calc
      A x * coulPot B x ≤ A x * (cB * coulPot g x) := by
        exact mul_le_mul_of_nonneg_left hVlex hA0x
      _ ≤ (cA * g x) * (cB * coulPot g x) := by
        exact mul_le_mul_of_nonneg_right hAlex (mul_nonneg hcB (hVg0 x))
      _ = (cA * cB) * (g x * coulPot g x) := by ring
  have hA : AEStronglyMeasurable A := hAI.aestronglyMeasurable
  have hVb_aesm : AEStronglyMeasurable (coulPot B) :=
    coulPot_aestronglyMeasurable hBI hBsupp (le_of_lt hR)
  have hOutAESM : AEStronglyMeasurable (fun x : ℝ³ => A x * coulPot B x) := hA.mul hVb_aesm
  have hM : MeasureTheory.Integrable (fun x : ℝ³ => (cA * cB) * (g x * coulPot g x)) :=
    hVgInt.const_mul (cA * cB)
  have hAVb : MeasureTheory.Integrable (fun x : ℝ³ => A x * coulPot B x) := by
    refine MeasureTheory.Integrable.mono' hM hOutAESM ?_
    have hOut0 : ∀ᵐ x : ℝ³, 0 ≤ A x * coulPot B x := by
      filter_upwards [hA0] with x hx
      exact mul_nonneg hx (hVB0 x)
    filter_upwards [hOut0, hOut] with x hx0 hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx
  rw [hD, hDg]
  calc
    (∫ x : ℝ³, A x * coulPot B x) ≤ (∫ x : ℝ³, (cA * cB) * (g x * coulPot g x)) := by
      exact MeasureTheory.integral_mono_ae hAVb hM hOut
    _ = (cA * cB) * (∫ x : ℝ³, g x * coulPot g x) := by
      rw [MeasureTheory.integral_const_mul]

/-- **Coulomb cross-term estimate** (eq:I2-integral, x-space, product form):
`0 ≤ (W₁−g₀)(x)(W₁+g₀)(y)` a.e. and the double integral is bounded by
`δ(2+δ)·∫∫g₀(x)g₀(y)K(x,y)` with `δ := 2C(R/ℓ)²`, `K(x,y) := ‖x−y‖⁻¹`. -/
theorem coulomb_g0_cross_le {v : ℝ³ → ℝ} {R ℓ r₁ C : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    (∫ x : ℝ³, ∫ y : ℝ³,
        (wScaled ℓ (g0 v h) x - g0 v h x) * (wScaled ℓ (g0 v h) y + g0 v h y) *
          (‖x - y‖ : ℝ)⁻¹) ≤
      (2 * C * (R / ℓ) ^ 2) * (2 + 2 * C * (R / ℓ) ^ 2) *
        (∫ x : ℝ³, ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹) := by
  let g : ℝ³ → ℝ := g0 v h
  let W : ℝ³ → ℝ := wScaled ℓ g
  let F : ℝ³ → ℝ := W - g
  let G : ℝ³ → ℝ := W + g
  let δ : ℝ := 2 * C * (R / ℓ) ^ 2
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial (Classical.choose h) := hspec.1
  have hw₀ : IsScatteringSolution (Classical.choose h) v := hspec.2
  -- g-facts
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using (g0_integrable hR hv_supp h)
  have hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0 := by
    intro x hx
    simpa [g] using (g0_zero_of_norm_ge hv_supp hx h)
  have hg0 : ∀ᵐ x : ℝ³, 0 ≤ g x := by
    simpa [g] using (g0_nonneg_ae hR hv_nonneg hvrad hv_supp h)
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    have h2C : 0 ≤ 2 * C := by positivity
    exact mul_nonneg h2C (sq_nonneg (R / ℓ))
  have h2δ0 : 0 ≤ 2 + δ := by linarith
  -- representation and hVgInt
  have hrep : ∀ᵐ x : ℝ³, (Classical.choose h) x = (1 / (8 * π)) * coulPot g x := by
    have h0 := scattering_newton_representation (v := v) (w := Classical.choose h) (R := R) hR hvrad hv_supp hrad₀ hw₀
    simpa [g, g0, coulPot] using h0
  have hVg_eq : (fun x : ℝ³ => g x * coulPot g x) =ᵐ[volume]
      (fun x : ℝ³ => 8 * π * (g x * (Classical.choose h) x)) := by
    filter_upwards [hrep] with x hx
    have hc : (8 : ℝ) * π ≠ 0 := by positivity
    have hVx : coulPot g x = (8 * π) * (Classical.choose h) x := by
      symm
      calc
        (8 * π) * (Classical.choose h) x = (8 * π) * ((1 / (8 * π)) * coulPot g x) := by rw [hx]
        _ = coulPot g x := by rw [← mul_assoc, one_div, mul_inv_cancel₀ hc, one_mul]
    calc
      g x * coulPot g x = g x * ((8 * π) * (Classical.choose h) x) := by rw [hVx]
      _ = 8 * π * (g x * (Classical.choose h) x) := by ring
  have hVgInt : MeasureTheory.Integrable (fun x : ℝ³ => g x * coulPot g x) := by
    have hgw0 : MeasureTheory.Integrable (fun x : ℝ³ => g x * (Classical.choose h) x) := by
      simpa [g] using (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
    have hmain : MeasureTheory.Integrable (fun x : ℝ³ => 8 * π * (g x * (Classical.choose h) x)) :=
      hgw0.const_mul (8 * π)
    exact MeasureTheory.Integrable.congr hmain hVg_eq.symm
  -- sandwich in W-terms
  have hsand := wScaled_sandwich_ae (g := g) (ℓ := ℓ) (R := R) (r₁ := r₁) (C := C) hℓ hC
    hr₁ hT hg0 hgsupp (le_of_lt hR) hreg hcond
  have hWge : ∀ᵐ x : ℝ³, g x ≤ W x := by
    filter_upwards [hsand] with x hx
    simpa [W] using hx.1
  have hWle : ∀ᵐ x : ℝ³, W x ≤ (1 + δ) * g x := by
    filter_upwards [hsand] with x hx
    have hx2 : W x ≤ g x * (1 + δ) := by
      dsimp [δ] at hx ⊢
      simpa [W] using hx.2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hx2
  -- F-facts
  have hFbounds : ∀ᵐ x : ℝ³, 0 ≤ F x ∧ F x ≤ δ * g x := by
    have hb := wScaled_g0_ae_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
    filter_upwards [hb] with x hx
    constructor
    · simpa [g, W, F, δ] using hx.1
    · simpa [g, W, F, δ] using hx.2
  have hF0 : ∀ᵐ x : ℝ³, 0 ≤ F x := by filter_upwards [hFbounds] with x hx; exact hx.1
  have hFle : ∀ᵐ x : ℝ³, F x ≤ δ * g x := by filter_upwards [hFbounds] with x hx; exact hx.2
  have hFsupp : ∀ x : ℝ³, R ≤ ‖x‖ → F x = 0 := by
    intro x hx
    have hgx : g x = 0 := hgsupp x hx
    simp [F, W, wScaled, hgx]
  have hconv_aesm : AEStronglyMeasurable (fun x : ℝ³ => (convScale ℓ x)⁻¹) := by
    have hmeas : Measurable (fun x : ℝ³ => (convScale ℓ x)⁻¹) := by
      refine Measurable.inv ?_
      have hc : Continuous (fun x : ℝ³ => convScale ℓ x) := by
        dsimp [convScale]
        exact (conv_contDiff.continuous).comp (continuous_id.const_smul (ℓ⁻¹))
      exact hc.measurable
    exact hmeas.stronglyMeasurable.aestronglyMeasurable
  have hW_aesm : AEStronglyMeasurable W := by
    have hg_aesm : AEStronglyMeasurable g := hgI.aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun x : ℝ³ => g x * (convScale ℓ x)⁻¹) :=
      hg_aesm.mul hconv_aesm
    refine AEStronglyMeasurable.congr hprod ?_
    filter_upwards with x
    simp [W, wScaled, div_eq_mul_inv]
  have hF_aesm : AEStronglyMeasurable F := by
    dsimp [F]
    exact hW_aesm.sub hgI.aestronglyMeasurable
  have hFI : MeasureTheory.Integrable F := by
    refine MeasureTheory.Integrable.mono' (hgI.const_mul δ) hF_aesm ?_
    filter_upwards [hF0, hFle] with x hF0x hFle
    rw [Real.norm_eq_abs, abs_of_nonneg hF0x]
    exact hFle
  -- G-facts
  have hW0 : ∀ᵐ x : ℝ³, 0 ≤ W x := by
    filter_upwards [hg0, hWge] with x hg0x hge
    exact le_trans hg0x hge
  have hG0 : ∀ᵐ x : ℝ³, 0 ≤ G x := by
    filter_upwards [hg0, hW0] with x hg0x hW0x
    dsimp [G]
    exact add_nonneg hW0x hg0x
  have hGle : ∀ᵐ x : ℝ³, G x ≤ (2 + δ) * g x := by
    filter_upwards [hWle] with x hWlex
    dsimp [G]
    calc
      W x + g x ≤ (1 + δ) * g x + g x := add_le_add_left hWlex (g x)
      _ = (2 + δ) * g x := by ring
  have hG_aesm : AEStronglyMeasurable G := by
    dsimp [G]
    exact hW_aesm.add hgI.aestronglyMeasurable
  have hGI : MeasureTheory.Integrable G := by
    refine MeasureTheory.Integrable.mono' (hgI.const_mul (2 + δ)) hG_aesm ?_
    filter_upwards [hG0, hGle] with x hG0x hGle
    rw [Real.norm_eq_abs, abs_of_nonneg hG0x]
    exact hGle
  have hGsupp : ∀ x : ℝ³, R ≤ ‖x‖ → G x = 0 := by
    intro x hx
    have hgx : g x = 0 := hgsupp x hx
    simp [G, W, wScaled, hgx]
  -- apply the rectangular bound
  have hmain := coulomb_rect_le (R := R) (A := F) (B := G) (g := g) (cA := δ) (cB := 2 + δ) hR
    hFI hGI hgI hFsupp hGsupp hgsupp hF0 hG0 hg0 hFle hGle hδ0 h2δ0 hVgInt
  simpa [g, W, F, G, δ] using hmain

/-- **Coulomb square estimate** (eq:I2-integral-2, x-space, product form):
`∫∫(W₁−g₀)(x)(W₁−g₀)(y)K(x,y) ≤ δ²·∫∫g₀(x)g₀(y)K(x,y)`, `δ := 2C(R/ℓ)²`. -/
theorem coulomb_g0_sq_le {v : ℝ³ → ℝ} {R ℓ r₁ C : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    (∫ x : ℝ³, ∫ y : ℝ³,
        (wScaled ℓ (g0 v h) x - g0 v h x) * (wScaled ℓ (g0 v h) y - g0 v h y) *
          (‖x - y‖ : ℝ)⁻¹) ≤
      (2 * C * (R / ℓ) ^ 2) ^ 2 *
        (∫ x : ℝ³, ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹) := by
  let g : ℝ³ → ℝ := g0 v h
  let W : ℝ³ → ℝ := wScaled ℓ g
  let F : ℝ³ → ℝ := W - g
  let δ : ℝ := 2 * C * (R / ℓ) ^ 2
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial (Classical.choose h) := hspec.1
  have hw₀ : IsScatteringSolution (Classical.choose h) v := hspec.2
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using (g0_integrable hR hv_supp h)
  have hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0 := by
    intro x hx
    simpa [g] using (g0_zero_of_norm_ge hv_supp hx h)
  have hg0 : ∀ᵐ x : ℝ³, 0 ≤ g x := by
    simpa [g] using (g0_nonneg_ae hR hv_nonneg hvrad hv_supp h)
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    have h2C : 0 ≤ 2 * C := by positivity
    exact mul_nonneg h2C (sq_nonneg (R / ℓ))
  have hrep : ∀ᵐ x : ℝ³, (Classical.choose h) x = (1 / (8 * π)) * coulPot g x := by
    have h0 := scattering_newton_representation (v := v) (w := Classical.choose h) (R := R) hR hvrad hv_supp hrad₀ hw₀
    simpa [g, g0, coulPot] using h0
  have hVg_eq : (fun x : ℝ³ => g x * coulPot g x) =ᵐ[volume]
      (fun x : ℝ³ => 8 * π * (g x * (Classical.choose h) x)) := by
    filter_upwards [hrep] with x hx
    have hc : (8 : ℝ) * π ≠ 0 := by positivity
    have hVx : coulPot g x = (8 * π) * (Classical.choose h) x := by
      symm
      calc
        (8 * π) * (Classical.choose h) x = (8 * π) * ((1 / (8 * π)) * coulPot g x) := by rw [hx]
        _ = coulPot g x := by rw [← mul_assoc, one_div, mul_inv_cancel₀ hc, one_mul]
    calc
      g x * coulPot g x = g x * ((8 * π) * (Classical.choose h) x) := by rw [hVx]
      _ = 8 * π * (g x * (Classical.choose h) x) := by ring
  have hVgInt : MeasureTheory.Integrable (fun x : ℝ³ => g x * coulPot g x) := by
    have hgw0 : MeasureTheory.Integrable (fun x : ℝ³ => g x * (Classical.choose h) x) := by
      simpa [g] using (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
    have hmain : MeasureTheory.Integrable (fun x : ℝ³ => 8 * π * (g x * (Classical.choose h) x)) :=
      hgw0.const_mul (8 * π)
    exact MeasureTheory.Integrable.congr hmain hVg_eq.symm
  have hF0 : ∀ᵐ x : ℝ³, 0 ≤ F x := by
    have hb := wScaled_g0_ae_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
    filter_upwards [hb] with x hx
    simpa [g, W, F, δ] using hx.1
  have hFle : ∀ᵐ x : ℝ³, F x ≤ δ * g x := by
    have hb := wScaled_g0_ae_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
    filter_upwards [hb] with x hx
    simpa [g, W, F, δ] using hx.2
  have hFsupp : ∀ x : ℝ³, R ≤ ‖x‖ → F x = 0 := by
    intro x hx
    have hgx : g x = 0 := hgsupp x hx
    simp [F, W, wScaled, hgx]
  have hconv_aesm : AEStronglyMeasurable (fun x : ℝ³ => (convScale ℓ x)⁻¹) := by
    have hmeas : Measurable (fun x : ℝ³ => (convScale ℓ x)⁻¹) := by
      refine Measurable.inv ?_
      have hc : Continuous (fun x : ℝ³ => convScale ℓ x) := by
        dsimp [convScale]
        exact (conv_contDiff.continuous).comp (continuous_id.const_smul (ℓ⁻¹))
      exact hc.measurable
    exact hmeas.stronglyMeasurable.aestronglyMeasurable
  have hW_aesm : AEStronglyMeasurable W := by
    have hg_aesm : AEStronglyMeasurable g := hgI.aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun x : ℝ³ => g x * (convScale ℓ x)⁻¹) :=
      hg_aesm.mul hconv_aesm
    refine AEStronglyMeasurable.congr hprod ?_
    filter_upwards with x
    simp [W, wScaled, div_eq_mul_inv]
  have hF_aesm : AEStronglyMeasurable F := by
    dsimp [F]
    exact hW_aesm.sub hgI.aestronglyMeasurable
  have hFI : MeasureTheory.Integrable F := by
    refine MeasureTheory.Integrable.mono' (hgI.const_mul δ) hF_aesm ?_
    filter_upwards [hF0, hFle] with x hF0x hFle
    rw [Real.norm_eq_abs, abs_of_nonneg hF0x]
    exact hFle
  have hcoef : δ * δ = (2 * C * (R / ℓ) ^ 2) ^ 2 := by
    dsimp [δ]
    ring
  have hmain := coulomb_rect_le (R := R) (A := F) (B := F) (g := g) (cA := δ) (cB := δ) hR
    hFI hFI hgI hFsupp hFsupp hgsupp hF0 hF0 hg0 hFle hFle hδ0 hδ0 hVgInt
  have hmain' : (∫ x : ℝ³, ∫ y : ℝ³, F x * F y * (‖x - y‖ : ℝ)⁻¹) ≤
      (2 * C * (R / ℓ) ^ 2) ^ 2 * (∫ x : ℝ³, ∫ y : ℝ³, g x * g y * (‖x - y‖ : ℝ)⁻¹) := by
    rw [← hcoef]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  simpa [g, W, F, δ] using hmain'

/-- **eq:I2-integral, x-space, J-form**: with
`J(f) := (1/8π)∫∫f(x)f(y)(‖x−y‖:ℝ)⁻¹` and `W₁ := wScaled ℓ (g0 v h)`:
`|J(W₁) − J(g₀)| ≤ δ(2+δ)·J(g₀)`, `δ := 2C(R/ℓ)²`.

Proof route: `W₁²−g₀² = (W₁−g₀)(W₁+g₀)` pointwise; use `coulomb_g0_cross_le`,
the non-negativity of the cross integrand, and `integral_add` (both of the
terms are integrable by the cross/square bounds and `chosen_newton_double_le`),
then multiply by `1/(8π)`. -/
theorem i2_integral_xspace {v : ℝ³ → ℝ} {R ℓ r₁ C : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    |(1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y * (‖x - y‖ : ℝ)⁻¹) -
      (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹)| ≤
      (2 * C * (R / ℓ) ^ 2) * (2 + 2 * C * (R / ℓ) ^ 2) *
        ((1 / (8 * π)) *
          (∫ x : ℝ³, ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹)) := by
  let g : ℝ³ → ℝ := g0 v h
  let W : ℝ³ → ℝ := wScaled ℓ g
  let δ : ℝ := 2 * C * (R / ℓ) ^ 2
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial (Classical.choose h) := hspec.1
  have hw₀ : IsScatteringSolution (Classical.choose h) v := hspec.2
  have hgI : MeasureTheory.Integrable g := by
    simpa [g] using (g0_integrable hR hv_supp h)
  have hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0 := by
    intro x hx
    simpa [g] using (g0_zero_of_norm_ge hv_supp hx h)
  have hg0 : ∀ᵐ x : ℝ³, 0 ≤ g x := by
    simpa [g] using (g0_nonneg_ae hR hv_nonneg hvrad hv_supp h)
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    have h2C : 0 ≤ 2 * C := by positivity
    exact mul_nonneg h2C (sq_nonneg (R / ℓ))
  have h1δ0 : 0 ≤ 1 + δ := by linarith
  have hrep : ∀ᵐ x : ℝ³, (Classical.choose h) x = (1 / (8 * π)) * coulPot g x := by
    have h0 := scattering_newton_representation (v := v) (w := Classical.choose h) (R := R) hR hvrad hv_supp hrad₀ hw₀
    simpa [g, g0, coulPot] using h0
  have hVg_eq : (fun x : ℝ³ => g x * coulPot g x) =ᵐ[volume]
      (fun x : ℝ³ => 8 * π * (g x * (Classical.choose h) x)) := by
    filter_upwards [hrep] with x hx
    have hc : (8 : ℝ) * π ≠ 0 := by positivity
    have hVx : coulPot g x = (8 * π) * (Classical.choose h) x := by
      symm
      calc
        (8 * π) * (Classical.choose h) x = (8 * π) * ((1 / (8 * π)) * coulPot g x) := by rw [hx]
        _ = coulPot g x := by rw [← mul_assoc, one_div, mul_inv_cancel₀ hc, one_mul]
    calc
      g x * coulPot g x = g x * ((8 * π) * (Classical.choose h) x) := by rw [hVx]
      _ = 8 * π * (g x * (Classical.choose h) x) := by ring
  have hVgInt : MeasureTheory.Integrable (fun x : ℝ³ => g x * coulPot g x) := by
    have hgw0 : MeasureTheory.Integrable (fun x : ℝ³ => g x * (Classical.choose h) x) := by
      simpa [g] using (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
    have hmain : MeasureTheory.Integrable (fun x : ℝ³ => 8 * π * (g x * (Classical.choose h) x)) :=
      hgw0.const_mul (8 * π)
    exact MeasureTheory.Integrable.congr hmain hVg_eq.symm
  have hsand := wScaled_sandwich_ae (g := g) (ℓ := ℓ) (R := R) (r₁ := r₁) (C := C) hℓ hC
    hr₁ hT hg0 hgsupp (le_of_lt hR) hreg hcond
  have hWge : ∀ᵐ x : ℝ³, g x ≤ W x := by
    filter_upwards [hsand] with x hx
    simpa [W] using hx.1
  have hWle : ∀ᵐ x : ℝ³, W x ≤ (1 + δ) * g x := by
    filter_upwards [hsand] with x hx
    have hx2 : wScaled ℓ g x ≤ g x * (1 + δ) := by
      simpa [δ] using hx.2
    simpa [W, mul_comm] using hx2
  have hW0 : ∀ᵐ x : ℝ³, 0 ≤ W x := by
    filter_upwards [hg0, hWge] with x hg0x hge
    exact le_trans hg0x hge
  have hWsupp : ∀ x : ℝ³, R ≤ ‖x‖ → W x = 0 := by
    intro x hx
    have hgx : g x = 0 := hgsupp x hx
    simp [W, wScaled, hgx]
  have hconv_aesm : AEStronglyMeasurable (fun x : ℝ³ => (convScale ℓ x)⁻¹) := by
    have hmeas : Measurable (fun x : ℝ³ => (convScale ℓ x)⁻¹) := by
      refine Measurable.inv ?_
      have hc : Continuous (fun x : ℝ³ => convScale ℓ x) := by
        dsimp [convScale]
        exact (conv_contDiff.continuous).comp (continuous_id.const_smul (ℓ⁻¹))
      exact hc.measurable
    exact hmeas.stronglyMeasurable.aestronglyMeasurable
  have hW_aesm : AEStronglyMeasurable W := by
    have hg_aesm : AEStronglyMeasurable g := hgI.aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun x : ℝ³ => g x * (convScale ℓ x)⁻¹) :=
      hg_aesm.mul hconv_aesm
    refine AEStronglyMeasurable.congr hprod ?_
    filter_upwards with x
    simp [W, wScaled, div_eq_mul_inv]
  have hWI : MeasureTheory.Integrable W := by
    refine MeasureTheory.Integrable.mono' (hgI.const_mul (1 + δ)) hW_aesm ?_
    filter_upwards [hW0, hWle, hg0] with x hW0x hWlex hg0x
    rw [Real.norm_eq_abs, abs_of_nonneg hW0x]
    exact hWlex
  -- inner potential inequalities
  have hVgVW : ∀ᵐ x : ℝ³, coulPot g x ≤ coulPot W x := by
    have h1 : ∀ᵐ y : ℝ³, g y ≤ (1 : ℝ) * W y := by
      filter_upwards [hWge] with y hy
      simpa using hy
    simpa using (coulPot_le_ae (p := g) (g := W) (c := 1) (R := R) hR hgI hWI hgsupp hWsupp hg0 hW0 h1 (by norm_num))
  have hVWVg : ∀ᵐ x : ℝ³, coulPot W x ≤ (1 + δ) * coulPot g x := by
    exact coulPot_le_ae (p := W) (g := g) (c := 1 + δ) (R := R) hR hWI hgI hWsupp hgsupp hW0 hg0 hWle h1δ0
  -- outer pointwise bounds
  have hOut1 : ∀ᵐ x : ℝ³, g x * coulPot g x ≤ W x * coulPot W x := by
    filter_upwards [hg0, hW0, hWge, hVgVW] with x hg0x hW0x hgex hVx
    calc
      g x * coulPot g x ≤ W x * coulPot g x := mul_le_mul_of_nonneg_right hgex (coulPot_nonneg hg0 x)
      _ ≤ W x * coulPot W x := mul_le_mul_of_nonneg_left hVx hW0x
  have hOut2 : ∀ᵐ x : ℝ³, W x * coulPot W x ≤ (1 + δ) ^ 2 * (g x * coulPot g x) := by
    filter_upwards [hg0, hW0, hWle, hVWVg] with x hg0x hW0x hWlex hVx
    calc
      W x * coulPot W x ≤ ((1 + δ) * g x) * coulPot W x := by
        exact mul_le_mul_of_nonneg_right hWlex (coulPot_nonneg hW0 x)
      _ ≤ ((1 + δ) * g x) * ((1 + δ) * coulPot g x) := by
        exact mul_le_mul_of_nonneg_left hVx (mul_nonneg h1δ0 hg0x)
      _ = (1 + δ) ^ 2 * (g x * coulPot g x) := by ring
  -- integrability of outer functions
  have hVW_aesm : AEStronglyMeasurable (coulPot W) :=
    coulPot_aestronglyMeasurable hWI hWsupp (le_of_lt hR)
  have hVg_aesm : AEStronglyMeasurable (coulPot g) :=
    coulPot_aestronglyMeasurable hgI hgsupp (le_of_lt hR)
  have hWVW_aesm : AEStronglyMeasurable (fun x : ℝ³ => W x * coulPot W x) := hW_aesm.mul hVW_aesm
  have hgVg_aesm : AEStronglyMeasurable (fun x : ℝ³ => g x * coulPot g x) := hgI.aestronglyMeasurable.mul hVg_aesm
  have hWVW : MeasureTheory.Integrable (fun x : ℝ³ => W x * coulPot W x) := by
    have hM : MeasureTheory.Integrable (fun x : ℝ³ => (1 + δ) ^ 2 * (g x * coulPot g x)) :=
      hVgInt.const_mul ((1 + δ) ^ 2)
    refine MeasureTheory.Integrable.mono' hM hWVW_aesm ?_
    have hout0 : ∀ᵐ x : ℝ³, 0 ≤ W x * coulPot W x := by
      filter_upwards [hW0] with x hx
      exact mul_nonneg hx (coulPot_nonneg hW0 x)
    filter_upwards [hout0, hOut2] with x hx0 hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx
  have hggV : MeasureTheory.Integrable (fun x : ℝ³ => g x * coulPot g x) := hVgInt
  -- integral-level: Dgg ≤ Dww ≤ (1+δ)^2 Dgg
  have hDgg : (∫ x : ℝ³, ∫ y : ℝ³, g x * g y * (‖x - y‖ : ℝ)⁻¹)
      = ∫ x : ℝ³, g x * coulPot g x := double_integral_eq_coulPot g g
  have hDww : (∫ x : ℝ³, ∫ y : ℝ³, W x * W y * (‖x - y‖ : ℝ)⁻¹)
      = ∫ x : ℝ³, W x * coulPot W x := double_integral_eq_coulPot W W
  have hgg_le_ww : (∫ x : ℝ³, g x * coulPot g x) ≤ (∫ x : ℝ³, W x * coulPot W x) := by
    exact MeasureTheory.integral_mono_ae hggV hWVW hOut1
  have hww_le : (∫ x : ℝ³, W x * coulPot W x) ≤ (1 + δ) ^ 2 * (∫ x : ℝ³, g x * coulPot g x) := by
    have hM : MeasureTheory.Integrable (fun x : ℝ³ => (1 + δ) ^ 2 * (g x * coulPot g x)) :=
      hVgInt.const_mul ((1 + δ) ^ 2)
    have hle : (∫ x : ℝ³, W x * coulPot W x) ≤ (∫ x : ℝ³, (1 + δ) ^ 2 * (g x * coulPot g x)) := by
      exact MeasureTheory.integral_mono_ae hWVW hM hOut2
    calc
      (∫ x : ℝ³, W x * coulPot W x) ≤ (∫ x : ℝ³, (1 + δ) ^ 2 * (g x * coulPot g x)) := hle
      _ = (1 + δ) ^ 2 * (∫ x : ℝ³, g x * coulPot g x) := by
        rw [MeasureTheory.integral_const_mul]
  -- assemble
  let Dgg : ℝ := ∫ x : ℝ³, ∫ y : ℝ³, g x * g y * (‖x - y‖ : ℝ)⁻¹
  let Dww : ℝ := ∫ x : ℝ³, ∫ y : ℝ³, W x * W y * (‖x - y‖ : ℝ)⁻¹
  have hDgg0 : 0 ≤ (1 / (8 * π)) * Dgg := by
    exact mul_nonneg (by positivity) (by
      have h0 : 0 ≤ (∫ x : ℝ³, g x * coulPot g x) := by
        exact MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [hg0] with x hx
          exact mul_nonneg hx (coulPot_nonneg hg0 x))
      simpa [Dgg, hDgg] using h0)
  have h1 : Dgg ≤ Dww := by
    dsimp [Dgg, Dww]
    rw [hDgg, hDww]
    exact hgg_le_ww
  have h2 : Dww ≤ (1 + δ) ^ 2 * Dgg := by
    dsimp [Dgg, Dww]
    rw [hDgg, hDww]
    exact hww_le
  have hXmY0 : 0 ≤ (1 / (8 * π)) * Dww - (1 / (8 * π)) * Dgg := by
    have hle : (1 / (8 * π)) * Dgg ≤ (1 / (8 * π)) * Dww := by
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hbound : (1 / (8 * π)) * Dww - (1 / (8 * π)) * Dgg ≤
      δ * (2 + δ) * ((1 / (8 * π)) * Dgg) := by
    have hmain : Dww - Dgg ≤ δ * (2 + δ) * Dgg := by
      have h2' : Dww - Dgg ≤ ((1 + δ) ^ 2 - 1) * Dgg := by
        nlinarith
      calc
        Dww - Dgg ≤ ((1 + δ) ^ 2 - 1) * Dgg := h2'
        _ = δ * (2 + δ) * Dgg := by
          dsimp [δ]
          ring
    have hpi : 0 < (1 / (8 * π)) := by positivity
    have hmult := (mul_le_mul_of_nonneg_left hmain (le_of_lt hpi))
    -- hmult : (1/(8π))·(Dww − Dgg) ≤ (1/(8π))·(δ(2+δ)·Dgg)
    nlinarith [hmult]
  rw [abs_of_nonneg hXmY0]
  dsimp [Dgg, Dww, W, g]
  exact hbound

/-- **eq:I2-integral in `∫g₀w₀`-terms** (the corpus form of the FS statement
`|(2π)⁻³∫Ŵ₁²/(2k²)dk − ĝω(0)| ≤ C(R/ℓ)²ĝω(0)`): use
`ScatGChosen.chosen_newton_double_eq` (`∫∫g₀g₀K = 8π∫g₀w₀`) and the bounds
`0 ≤ ∫g₀w₀` to rewrite `J(g₀) = ∫g₀·w₀`. -/
theorem i2_integral_xspace_fs {v : ℝ³ → ℝ} {R ℓ r₁ C : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    |(1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          wScaled ℓ (g0 v h) x * wScaled ℓ (g0 v h) y * (‖x - y‖ : ℝ)⁻¹) -
      (∫ x : ℝ³, g0 v h x * Classical.choose h x)| ≤
      (2 * C * (R / ℓ) ^ 2) * (2 + 2 * C * (R / ℓ) ^ 2) *
        (∫ x : ℝ³, g0 v h x * Classical.choose h x) := by
  have hD0 : (∫ x : ℝ³, ∫ y : ℝ³,
        g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹) =
      (∫ x : ℝ³, ∫ y : ℝ³,
        (v x * (1 - Classical.choose h x)) * (v y * (1 - Classical.choose h y)) *
          (‖x - y‖ : ℝ)⁻¹) := by
    apply MeasureTheory.integral_congr_ae
    refine ae_of_all _ ?_
    intro x
    apply MeasureTheory.integral_congr_ae
    refine ae_of_all _ ?_
    intro y
    simp [g0]
  have hI0 : (∫ x : ℝ³, g0 v h x * Classical.choose h x) =
      (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * Classical.choose h x) := by
    apply MeasureTheory.integral_congr_ae
    refine ae_of_all _ ?_
    intro x
    simp [g0]
  have hJ : (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹) =
      (∫ x : ℝ³, g0 v h x * Classical.choose h x) := by
    rw [hD0, hI0]
    have h0 := chosen_newton_double_eq (v := v) (R := R) hR hvrad hv_supp h
    have hc : (8 : ℝ) * π ≠ 0 := by positivity
    calc
      (1 / (8 * π)) * (∫ x : ℝ³, ∫ y : ℝ³,
          (v x * (1 - Classical.choose h x)) * (v y * (1 - Classical.choose h y)) *
            (‖x - y‖ : ℝ)⁻¹)
          = (1 / (8 * π)) * (8 * π * (∫ x : ℝ³,
              (v x * (1 - Classical.choose h x)) * Classical.choose h x)) := by
              rw [h0]
      _ = (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * Classical.choose h x) := by
              rw [← mul_assoc]
              rw [one_div]
              rw [inv_mul_cancel₀ hc]
              rw [one_mul]
  have hx := i2_integral_xspace (v := v) (R := R) (ℓ := ℓ) (r₁ := r₁) (C := C) hR hv_nonneg hvrad
    hv_supp h hC hr₁ hT hℓ hreg hcond
  rw [hJ] at hx
  exact hx

/-- **eq:I2-integral-2 in `∫g₀w₀`-terms**: `J(W₁−g₀) ≤ δ²·∫g₀·w₀`. -/
theorem i2_integral2_xspace {v : ℝ³ → ℝ} {R ℓ r₁ C : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          (wScaled ℓ (g0 v h) x - g0 v h x) * (wScaled ℓ (g0 v h) y - g0 v h y) *
            (‖x - y‖ : ℝ)⁻¹) ≤
      (2 * C * (R / ℓ) ^ 2) ^ 2 * (∫ x : ℝ³, g0 v h x * Classical.choose h x) := by
  have hJ : (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹) =
      (∫ x : ℝ³, g0 v h x * Classical.choose h x) := by
    have hD0 : (∫ x : ℝ³, ∫ y : ℝ³,
          g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹) =
        (∫ x : ℝ³, ∫ y : ℝ³,
          (v x * (1 - Classical.choose h x)) * (v y * (1 - Classical.choose h y)) *
            (‖x - y‖ : ℝ)⁻¹) := by
      apply MeasureTheory.integral_congr_ae
      refine ae_of_all _ ?_
      intro x
      apply MeasureTheory.integral_congr_ae
      refine ae_of_all _ ?_
      intro y
      simp [g0]
    have hI0 : (∫ x : ℝ³, g0 v h x * Classical.choose h x) =
        (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * Classical.choose h x) := by
      apply MeasureTheory.integral_congr_ae
      refine ae_of_all _ ?_
      intro x
      simp [g0]
    rw [hD0, hI0]
    have h0 := chosen_newton_double_eq (v := v) (R := R) hR hvrad hv_supp h
    have hc : (8 : ℝ) * π ≠ 0 := by positivity
    calc
      (1 / (8 * π)) * (∫ x : ℝ³, ∫ y : ℝ³,
          (v x * (1 - Classical.choose h x)) * (v y * (1 - Classical.choose h y)) *
            (‖x - y‖ : ℝ)⁻¹)
          = (1 / (8 * π)) * (8 * π * (∫ x : ℝ³,
              (v x * (1 - Classical.choose h x)) * Classical.choose h x)) := by
              rw [h0]
      _ = (∫ x : ℝ³, (v x * (1 - Classical.choose h x)) * Classical.choose h x) := by
              rw [← mul_assoc]
              rw [one_div]
              rw [inv_mul_cancel₀ hc]
              rw [one_mul]
  have hsq := coulomb_g0_sq_le (v := v) (R := R) (ℓ := ℓ) (r₁ := r₁) (C := C) hR hv_nonneg hvrad
    hv_supp h hC hr₁ hT hℓ hreg hcond
  have hpi : 0 ≤ 1 / (8 * π) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hsq hpi
  calc
    (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          (wScaled ℓ (g0 v h) x - g0 v h x) * (wScaled ℓ (g0 v h) y - g0 v h y) *
            (‖x - y‖ : ℝ)⁻¹)
        ≤ (1 / (8 * π)) * ((2 * C * (R / ℓ) ^ 2) ^ 2 *
            (∫ x : ℝ³, ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹)) := h1
    _ = (2 * C * (R / ℓ) ^ 2) ^ 2 * ((1 / (8 * π)) *
            (∫ x : ℝ³, ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹)) := by ring
    _ = (2 * C * (R / ℓ) ^ 2) ^ 2 * (∫ x : ℝ³, g0 v h x * Classical.choose h x) := by
            rw [hJ]

end BoseGases

end Submission
