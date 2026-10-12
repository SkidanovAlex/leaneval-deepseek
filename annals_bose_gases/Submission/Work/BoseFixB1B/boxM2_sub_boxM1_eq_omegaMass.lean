import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1B.ae_integrable_fibre_wPairC
import Submission.Work.BoseFixB1B.exists_pos_le_conv3Small_of_polydisc
import Submission.Work.BoseFixB1B.integral_add_of_le_of_const_mul_le
import Submission.Work.BoseFixB1B.integral_prod_eq_iterated_of_ae_fibre_integrable
import Submission.Work.BoseFixB1S.boxM1Info
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass`

The **`ω`-mass identity** for the sliding-box localised kernels of FS `eq:HBU`:

    boxM2 |B(u)| B(u) w_{2,B(u)}  −  boxM1 ℓ B(u) w_{1,B(u)}
      = ∫_{(x,y) ∈ B(u)×B(u)}, ω₀(x−y)·w_{1,B(u)}(x,y) ,

with `ω₀ := Classical.choose h` the chosen scattering solution, `w_{1,B(u)} = wSmall1Pair h M ℓ d u`
and `w_{2,B(u)} = wSmallPair M ℓ d u (g₂ v h)`, `g₂ = g₀(1+ω₀)`, `g₀ = v(1−ω₀)`.

## The mathematics

The pointwise identity `w_{2,B} = w_{1,B} + ω₀·w_{1,B}` (from `g₂ = g₀ + g₀ω₀`, i.e. FS
`lm:w2>w1`) turns the difference of the two box integrals into the integral of `ω₀·w_{1,B}`
— *provided* the Bochner integrals may be split.  That splitting is the whole content here,
because the localised kernels carry the two renormalisation denominators
`(χ_M⋆χ_M)(·/(ℓd))` and `(χ⋆χ)(·/ℓ)` and need **not** be integrable over the box; for a
non-integrable function the Bochner integral is `0` by convention, so a careless proof gives
`0 − 0 = 0` while the right-hand side is non-zero.

The hypotheses available here (no diluteness: `ℓ, d > 0` are arbitrary) supply exactly the
input that rules this out.  The chosen scattering solution is the Newton potential of
`g₀ = v(1−ω₀)`, hence on the support of `v`

    0 < c := a v/(2 R₀) ≤ ω₀(z)      for a.e. `z` with `‖z‖ < R₀`   (`w0_ge_const_on_ball`),

and since `w_{1,B}(x,y) ≠ 0` forces `g₀(x−y) ≠ 0`, hence `‖x−y‖ < R₀`, the three integrands
`F := w_{1,B}`, `H := ω₀·F`, `G := w_{2,B}` satisfy, pointwise a.e.,

    c·F ≤ H ≤ F ≤ G = F + H .

With this sandwich the identity holds in *both* regimes: if `F` is integrable then so are
`H` and `G`, and additivity of the Bochner integral applies; if `F` is not integrable then
`F`, `G`, `H` are all non-integrable and all three integrals vanish by the `0`-convention.
`integral_add_of_le_of_const_mul_le` packages this dichotomy in one dimension.

## The Fubini-type steps

`boxM1` is an *iterated* integral while `boxM2` and the right-hand side are *product-measure*
integrals, so the three have to be compared in a common shape:
`integral_prod_eq_iterated_of_ae_fibre_integrable` does this as soon as the fibres are a.e.
integrable.  The a.e. fibre integrability of `wSmall1Pair` is not a diluteness statement: the
dangerous denominator `(χ_M⋆χ_M)((x−y)/(ℓd))` vanishes only at the faces `|(x−y)_j| = ℓd` of
the small box, where the `y`-cutoff `χ_M((ℓd)⁻¹ y − u)` vanishes; quantitatively, on the
support of that cutoff, `(χ_M⋆χ_M)((ℓd)⁻¹(x−y)) ≥ c(x) > 0` with `c(x) > 0` for a.e. `x`
(`exists_pos_le_conv3Small_of_polydisc`).  The remaining `ℓ`-scale denominator is controlled
a.e. in `x` by the *exact* cancellation `∫_x χ_ℓ(x)χ_ℓ(x−z)dx = ℓ³(χ⋆χ)(z/ℓ)` exploited in
`Work.BoseFixB2.Pot.lintegral_wPairC_le` (a joint bound with no diluteness hypothesis)
together with Tonelli (`ae_integrable_fibre_wPairC`).

Everything is assembled with the support collapse of the kernels off `B(u)×B(u)`
(`Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox`).
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The localised one-body kernel (numerator `g₀ = v(1−ω₀)`), uncurried — the integrand of
the target's right-hand side. -/
noncomputable def omF {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) : E3 × E3 → ℝ :=
  fun p => Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) p.1 p.2

/-- The localised two-body kernel (numerator `g₂ = g₀(1+ω₀)`), uncurried — the integrand of
`boxM2`. -/
noncomputable def omG {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) : E3 × E3 → ℝ :=
  fun p => Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2

/-- The `ω₀`-weighted one-body kernel, uncurried — the integrand of the target's right-hand
side. -/
noncomputable def omH {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) : E3 × E3 → ℝ :=
  fun p => Classical.choose h (p.1 - p.2) * omF h M ℓ d u p

@[simp] lemma omF_apply {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) (x y : E3) :
    omF h M ℓ d u (x, y) = Submission.BoseGases.wSmallPair M ℓ d u
      (Submission.BoseGases.g0 v h) x y := rfl

@[simp] lemma omG_apply {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) (x y : E3) :
    omG h M ℓ d u (x, y) = Submission.BoseGases.wSmallPair M ℓ d u
      (Submission.BoseGases.g2 v h) x y := rfl

@[simp] lemma omH_apply {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) (x y : E3) :
    omH h M ℓ d u (x, y)
      = Classical.choose h (x - y) * Submission.BoseGases.wSmallPair M ℓ d u
          (Submission.BoseGases.g0 v h) x y := rfl

/-- **The pointwise `ω`-identity for the localised kernels**: `w_{2,B} = w_{1,B} + ω₀ w_{1,B}`,
i.e. the `g₂ = g₀ + g₀ω₀` factorisation of the numerators. -/
theorem omG_eq_omF_add_omH {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) (p : E3 × E3) :
    omG h M ℓ d u p = omF h M ℓ d u p + omH h M ℓ d u p := by
  obtain ⟨x, y⟩ := p
  simp only [omG_apply, omF_apply, omH_apply, Submission.BoseGases.wSmallPair,
    Submission.BoseGases.wSmallScaled, Submission.BoseGases.g0, Submission.BoseGases.g2]
  ring

/-- **Pointwise positivity of the `g₀`-kernel forces smallness of `x − y`.**  If the localised
one-body kernel does not vanish at `(x,y)` then its numerator `g₀(x−y)` does not vanish, hence
`v(x−y) ≠ 0` and `‖x−y‖ < R₀` (the support of `v` is contained in the *open* ball). -/
lemma norm_sub_lt_of_omF_ne_zero {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0)
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) {x y : E3}
    (hxy : omF h M ℓ d u (x, y) ≠ 0) : ‖x - y‖ < R0 := by
  have hfac : omF h M ℓ d u (x, y)
      = Submission.BoseGases.chiSmallB M ℓ d u x *
        ((Submission.BoseGases.g0 v h (x - y)
            / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
          / Submission.BoseGases.convScale ℓ (x - y))
        * Submission.BoseGases.chiSmallB M ℓ d u y := rfl
  have hmid : ((Submission.BoseGases.g0 v h (x - y)
        / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
      / Submission.BoseGases.convScale ℓ (x - y)) ≠ 0 := by
    intro h0
    exact hxy (by rw [hfac, h0]; ring)
  have hq : (Submission.BoseGases.g0 v h (x - y)
      / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)) ≠ 0 := by
    intro h0
    exact hmid (by rw [h0, zero_div])
  have hg0 : Submission.BoseGases.g0 v h (x - y) ≠ 0 := by
    intro h0
    exact hq (by rw [h0, zero_div])
  have hvne : v (x - y) ≠ 0 := by
    intro h0
    exact hg0 (by simp only [Submission.BoseGases.g0, h0, zero_mul])
  have hmem : x - y ∈ tsupport v := subset_closure (Function.mem_support.mpr hvne)
  have := hv_supp hmem
  simpa [Metric.mem_ball, dist_eq_norm] using this

/-- **Pointwise fibre domination of the localised one-body kernel, with a per-`x` constant.**

For a fixed `x`: if the `(ℓd)`-scale renormalisation denominator `(χ_M⋆χ_M)((ℓd)⁻¹(x−y))` is
bounded below by `c > 0` on the support of the `y`-cutoff `χ_M((ℓd)⁻¹y − u)`, then the
localised one-body kernel is dominated by the `ℓ`-scale kernel
`χ_ℓ(y)·|g₀(x−y)|/(χ⋆χ)_ℓ(x−y)` with the constant `chiSmallDecay M ^ 2 / c`. -/
lemma abs_omF_le_fibre {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u x : E3) {c : ℝ} (hc : 0 < c)
    (hx : |Submission.BoseGases.chiSmallB M ℓ d u x|
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
    (hden : ∀ y : E3, Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u) ≠ 0 →
      c ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
    (y : E3) :
    |omF h M ℓ d u (x, y)| ≤
      (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          * Submission.BoseGases.chiSmallDecay M / c) *
        (Submission.BoseGases.chiScale ℓ y *
          (|Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y))) := by
  set X : ℝ := Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u) with hXdef
  set C : ℝ := Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) with hCdef
  set D : ℝ := Submission.BoseGases.convScale ℓ (x - y) with hDdef
  have hX0 : 0 ≤ X := Submission.BoseGases.chiSmall_nonneg M _
  have hC0 : 0 ≤ C := Work.BoseFixB1.convScaleSmall_nonneg M (ℓ * d) (x - y)
  have hD0 : 0 ≤ D := Submission.BoseGases.convScale_nonneg ℓ (x - y)
  have hdec0 : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hχy0 : 0 ≤ Submission.BoseGases.chiScale ℓ y := Submission.BoseGases.chiScale_nonneg ℓ y
  have hXle : X ≤ Submission.BoseGases.chiSmallDecay M := by
    have hh := Submission.BoseGases.chiSmall_decay_coord_le_decay (M := M) hM ((ℓ * d)⁻¹ • y - u)
    rw [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hh
    rwa [hXdef]
  -- the kernel as an explicit product
  have hval : |omF h M ℓ d u (x, y)|
      = |Submission.BoseGases.chiSmallB M ℓ d u x| * (Submission.BoseGases.chiScale ℓ y * X)
        * (|Submission.BoseGases.g0 v h (x - y)| / C / D) := by
    have h1 : omF h M ℓ d u (x, y)
        = Submission.BoseGases.chiSmallB M ℓ d u x
          * (Submission.BoseGases.chiScale ℓ y * X)
          * (Submission.BoseGases.g0 v h (x - y) / C / D) := by
      simp only [omF_apply, Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled,
        Submission.BoseGases.chiSmallB, hXdef, hCdef, hDdef]
      ring
    rw [h1, abs_mul, abs_mul, abs_mul, abs_div, abs_div]
    rw [abs_of_nonneg hC0, abs_of_nonneg hD0, abs_of_nonneg hχy0, abs_of_nonneg hX0]
  -- the coefficient bound
  have hcoef : |Submission.BoseGases.chiSmallB M ℓ d u x| * X / (C * D)
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
        * Submission.BoseGases.chiSmallDecay M / (c * D) := by
    by_cases hX : X = 0
    · rw [hX, mul_zero, zero_div]
      exact div_nonneg (mul_nonneg (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg hdec0) hdec0)
        (mul_nonneg hc.le hD0)
    · have hCX : c ≤ C := hden y (by rwa [← hXdef])
      have hnum : |Submission.BoseGases.chiSmallB M ℓ d u x| * X
          ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
            * Submission.BoseGases.chiSmallDecay M :=
        calc |Submission.BoseGases.chiSmallB M ℓ d u x| * X
            ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) * X :=
              mul_le_mul_of_nonneg_right hx hX0
          _ ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                * Submission.BoseGases.chiSmallDecay M :=
              mul_le_mul_of_nonneg_left hXle (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg hdec0)
      by_cases hDz : D = 0
      · rw [hDz, mul_zero, mul_zero, div_zero, div_zero]
      · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDz)
        calc |Submission.BoseGases.chiSmallB M ℓ d u x| * X / (C * D)
            ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                * Submission.BoseGases.chiSmallDecay M / (C * D) :=
              div_le_div_of_nonneg_right hnum (mul_nonneg hC0 hD0)
          _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                * Submission.BoseGases.chiSmallDecay M / (c * D) :=
              div_le_div_of_nonneg_left
                (mul_nonneg (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg hdec0) hdec0)
                (mul_pos hc hDpos) (mul_le_mul_of_nonneg_right hCX hD0)
  rw [hval]
  have hid : |Submission.BoseGases.chiSmallB M ℓ d u x| * (Submission.BoseGases.chiScale ℓ y * X)
        * (|Submission.BoseGases.g0 v h (x - y)| / C / D)
      = (Submission.BoseGases.chiScale ℓ y * |Submission.BoseGases.g0 v h (x - y)|)
        * (|Submission.BoseGases.chiSmallB M ℓ d u x| * X / (C * D)) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hid]
  refine le_trans (mul_le_mul_of_nonneg_left hcoef (mul_nonneg hχy0 (abs_nonneg _))) ?_
  exact le_of_eq (by ring)

/-- **The scattering solution is bounded below on the support of `v`.**  The chosen scattering
solution is the Newton potential of `g₀ = v(1−ω₀)`; on `{‖z‖ < R₀}` the Newton kernel is at
least `(2R₀)⁻¹` on the support of `g₀`, whence

    ω₀(z) ≥ (8π)⁻¹·(2R₀)⁻¹·∫g₀ = (8π)⁻¹·(2R₀)⁻¹·8π·a v = a v/(2R₀)

for a.e. `‖z‖ < R₀`. -/
theorem w0_ge_const_on_ball_aux {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      ‖z‖ < R0 → _root_.BoseGases.a v / (2 * R0) ≤ Classical.choose h z := by
  classical
  set w0 : E3 → ℝ := Classical.choose h with hw0
  have hspec := Classical.choose_spec h
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0nn : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      0 ≤ Submission.BoseGases.g0 v h y :=
    Submission.BoseGases.g0_nonneg_ae (R := R0) hR0 hv hvrad hv_supp h
  have hgsupp : ∀ y : E3, R0 ≤ ‖y‖ → Submission.BoseGases.g0 v h y = 0 :=
    fun y hy => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hy h
  have hg0int_eq : (∫ y : E3, Submission.BoseGases.g0 v h y) = 8 * π * _root_.BoseGases.a v :=
    Submission.BoseGases.chosen_scattering_integral h
  -- Newton representation, a.e.
  have hnewt : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      w0 z = (1 / (8 * π)) * ∫ y : E3, Submission.BoseGases.g0 v h y * ‖z - y‖⁻¹ := by
    have hh := Submission.BoseGases.scattering_newton_representation (w := w0) (v := v)
      hR0 hvrad hv_supp hspec.1 hspec.2
    filter_upwards [hh] with z hz
    rw [hz]
    simp only [Submission.BoseGases.g0, hw0]
  -- a.e. fibre integrability of the signed Newton integrand
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      ‖z‖ < R0 → MeasureTheory.Integrable
        (fun y : E3 => Submission.BoseGases.g0 v h y * ‖z - y‖⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    have h1 := Submission.BoseGases.kernel_abs_slice_integrable_ae
      (g := Submission.BoseGases.g0 v h) (R := R0) (M := R0) hg0int hgsupp hR0.le hR0.le
    have h1' : ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Metric.ball (0 : E3) R0))
        {x : E3 | ¬ MeasureTheory.Integrable
          (fun y : E3 => (|Submission.BoseGases.g0 v h y|
            * Submission.BoseGases.nPotKernel x y : ℝ))
          (MeasureTheory.volume : MeasureTheory.Measure E3)} = 0 :=
      MeasureTheory.ae_iff.mp h1
    refine MeasureTheory.ae_iff.mpr ?_
    set P : E3 → Prop := fun z => MeasureTheory.Integrable
      (fun y : E3 => Submission.BoseGases.g0 v h y * ‖z - y‖⁻¹)
      (MeasureTheory.volume : MeasureTheory.Measure E3) with hPdef
    have hsub : {z : E3 | ¬ (‖z‖ < R0 → P z)}
        ⊆ {x : E3 | ¬ MeasureTheory.Integrable
          (fun y : E3 => (|Submission.BoseGases.g0 v h y|
            * Submission.BoseGases.nPotKernel x y : ℝ))
          (MeasureTheory.volume : MeasureTheory.Measure E3)} := by
      intro z hz hU
      refine hz (fun _ => ?_)
      have hcongr : (fun y : E3 => (|Submission.BoseGases.g0 v h y|
            * Submission.BoseGases.nPotKernel z y : ℝ))
          =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure E3)]
          (fun y : E3 => Submission.BoseGases.g0 v h y * ‖z - y‖⁻¹) := by
        filter_upwards [hg0nn] with y hy
        rw [abs_of_nonneg hy]
        rfl
      have hUsigned : MeasureTheory.Integrable
          (fun y : E3 => Submission.BoseGases.g0 v h y * ‖z - y‖⁻¹)
          (MeasureTheory.volume : MeasureTheory.Measure E3) := hU.congr hcongr
      simpa [hPdef] using hUsigned
    have hvol_eq : (MeasureTheory.volume : MeasureTheory.Measure E3) {z : E3 | ¬ (‖z‖ < R0 → P z)}
        = ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Metric.ball (0 : E3) R0)) {z : E3 | ¬ (‖z‖ < R0 → P z)} := by
      have h := MeasureTheory.Measure.restrict_apply'
        (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
        (s := Metric.ball (0 : E3) R0) (t := {z : E3 | ¬ (‖z‖ < R0 → P z)})
        Metric.isOpen_ball.measurableSet
      rw [h]
      congr 1
      ext z
      constructor
      · intro hz
        refine ⟨hz, ?_⟩
        have hzR : ‖z‖ < R0 := by
          by_contra hc
          exact hz (fun h => absurd h hc)
        simpa [Metric.mem_ball, dist_eq_norm] using hzR
      · intro hz
        exact hz.1
    rw [hvol_eq]
    exact measure_mono_null hsub h1'
  filter_upwards [hnewt, hslice] with z hz hzi hzR
  rw [hz]
  have hzi' : MeasureTheory.Integrable (fun y : E3 => Submission.BoseGases.g0 v h y * ‖z - y‖⁻¹)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := hzi hzR
  have hz_ne : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure E3), y ≠ z := by
    rw [MeasureTheory.ae_iff]
    rw [show {y : E3 | ¬ y ≠ z} = {z} by ext y; simp]
    exact measure_singleton z
  have hcmp : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      Submission.BoseGases.g0 v h y * ((2 * R0)⁻¹) ≤ Submission.BoseGases.g0 v h y * ‖z - y‖⁻¹ := by
    filter_upwards [hg0nn, hz_ne] with y hy hyz
    by_cases h0 : Submission.BoseGases.g0 v h y = 0
    · rw [h0, zero_mul, zero_mul]
    · have hmem : ‖y‖ < R0 := by
        by_contra hc
        exact h0 (hgsupp y (le_of_not_gt hc))
      have hle : ‖z - y‖ ≤ 2 * R0 := by
        calc ‖z - y‖ ≤ ‖z‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ R0 + R0 := by linarith
          _ = 2 * R0 := by ring
      exact mul_le_mul_of_nonneg_left
        (inv_anti₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hyz.symm)) hle) hy
  have hle1 : (∫ y : E3, Submission.BoseGases.g0 v h y * ((2 * R0)⁻¹))
      = (2 * R0)⁻¹ * (8 * π * _root_.BoseGases.a v) := by
    rw [MeasureTheory.integral_mul_const, hg0int_eq]
    ring
  have hle2 : (2 * R0)⁻¹ * (8 * π * _root_.BoseGases.a v)
      ≤ ∫ y : E3, Submission.BoseGases.g0 v h y * ‖z - y‖⁻¹ := by
    rw [← hle1]
    exact MeasureTheory.integral_mono_ae (hg0int.mul_const _) hzi' hcmp
  have hstep : _root_.BoseGases.a v / (2 * R0)
      = (1 / (8 * π)) * ((2 * R0)⁻¹ * (8 * π * _root_.BoseGases.a v)) := by
    field_simp
  rw [hstep]
  exact mul_le_mul_of_nonneg_left hle2 (by positivity)

/-- **The a.e. sandwich of the three localised integrands.**  With `c := a v/(2R₀)`:

* `0 ≤ F`, `0 ≤ H`, `H ≤ F`, `c·F ≤ H` (the last one from the scattering-solution lower
  bound `c ≤ ω₀` on the support of `v`), all a.e. for `volume ⊗ volume`;
* `G = F + H` everywhere. -/
theorem ae_om_bounds {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3) :
    (∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)), 0 ≤ omF h M ℓ d u p)
      ∧ (∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)), 0 ≤ omH h M ℓ d u p)
      ∧ (∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)), omH h M ℓ d u p ≤ omF h M ℓ d u p)
      ∧ (∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)),
          (_root_.BoseGases.a v / (2 * R0)) * omF h M ℓ d u p ≤ omH h M ℓ d u p) := by
  have hqmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3))
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant _ _
  have hg0nn : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae (R := R0) hR0 hv hvrad hv_supp h
  have hwb := Submission.BoseGases.scattering_bounds_ae (w := Classical.choose h) hR0 hv hvrad
    hv_supp (Classical.choose_spec h).1 (Classical.choose_spec h).2
  have hwlow : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      ‖z‖ < R0 → _root_.BoseGases.a v / (2 * R0) ≤ Classical.choose h z :=
    w0_ge_const_on_ball_aux hv_supp hR0 hv hvrad h
  have hz0 : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
      (MeasureTheory.volume : MeasureTheory.Measure E3)),
      0 ≤ Submission.BoseGases.g0 v h (p.1 - p.2) := hqmp.ae hg0nn
  have hz1 : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
      (MeasureTheory.volume : MeasureTheory.Measure E3)),
      Classical.choose h (p.1 - p.2) ≤ 1 := hqmp.ae hwb.2
  have hzlow0 : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
      (MeasureTheory.volume : MeasureTheory.Measure E3)),
      0 ≤ Classical.choose h (p.1 - p.2) := hqmp.ae hwb.1
  have hzlow : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
      (MeasureTheory.volume : MeasureTheory.Measure E3)),
      ‖p.1 - p.2‖ < R0 → _root_.BoseGases.a v / (2 * R0) ≤ Classical.choose h (p.1 - p.2) :=
    hqmp.ae hwlow
  have hcle : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
      (MeasureTheory.volume : MeasureTheory.Measure E3)),
      omF h M ℓ d u p ≠ 0 →
        _root_.BoseGases.a v / (2 * R0) ≤ Classical.choose h (p.1 - p.2) := by
    filter_upwards [hzlow] with p hplow hpne
    exact hplow (norm_sub_lt_of_omF_ne_zero hv_supp h M ℓ d u hpne)
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hz0] with p hp
    exact wSmallPair_nonneg_of_nonneg hp
  · filter_upwards [hz0, hzlow0] with p hp hw0
    have h1 : 0 ≤ omF h M ℓ d u p := wSmallPair_nonneg_of_nonneg hp
    exact mul_nonneg hw0 h1
  · filter_upwards [hz0, hz1] with p hp hw1
    have h1 : 0 ≤ omF h M ℓ d u p := wSmallPair_nonneg_of_nonneg hp
    have h2 : Classical.choose h (p.1 - p.2) * omF h M ℓ d u p ≤ 1 * omF h M ℓ d u p :=
      mul_le_mul_of_nonneg_right hw1 h1
    change Classical.choose h (p.1 - p.2) * omF h M ℓ d u p ≤ omF h M ℓ d u p
    simpa using h2
  · filter_upwards [hz0, hcle] with p hp hc
    by_cases h0 : omF h M ℓ d u p = 0
    · change (_root_.BoseGases.a v / (2 * R0)) * omF h M ℓ d u p
        ≤ Classical.choose h (p.1 - p.2) * omF h M ℓ d u p
      rw [h0, mul_zero, mul_zero]
    · have h1 : 0 ≤ omF h M ℓ d u p := wSmallPair_nonneg_of_nonneg hp
      have h2 : (_root_.BoseGases.a v / (2 * R0)) * omF h M ℓ d u p
          ≤ Classical.choose h (p.1 - p.2) * omF h M ℓ d u p :=
        mul_le_mul_of_nonneg_right (hc h0) h1
      change (_root_.BoseGases.a v / (2 * R0)) * omF h M ℓ d u p
        ≤ Classical.choose h (p.1 - p.2) * omF h M ℓ d u p
      exact h2

/-- **Coordinate strictness of the `M`-th power cosine bump.**  Where the (normalised)
product bump `chiSmall M` does not vanish, every coordinate lies strictly inside `[-1/2,1/2]`. -/
lemma abs_coord_lt_half_of_chiSmall_ne_zero {M : ℕ} (hM : 1 ≤ M) {z : E3}
    (hz : Submission.BoseGases.chiSmall M z ≠ 0) (j : Fin 3) : |z.ofLp j| < 1 / 2 := by
  have hbase : Submission.BoseGases.chiSmallBase M z ≠ 0 := by
    intro h0
    refine hz ?_
    rw [Submission.BoseGases.chiSmall, h0, zero_div]
  have hfac := Submission.BoseGases.chiSmallBase_factors_ne_zero hM hbase
  have hζ : Submission.BoseGases.zeta1d (z.ofLp j) ≠ 0 := by
    fin_cases j
    · exact hfac.1
    · exact hfac.2.1
    · exact hfac.2.2
  have hle := Submission.BoseGases.zeta1d_ne_zero_abs_le hζ
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have ht : z.ofLp j = 1 / 2 ∨ z.ofLp j = -1 / 2 := by
      by_cases h0 : 0 ≤ z.ofLp j
      · left
        rw [abs_of_nonneg h0] at heq
        exact heq
      · right
        rw [abs_of_neg (lt_of_not_ge h0)] at heq
        linarith
    have hz0 : Submission.BoseGases.zeta1d (z.ofLp j) = 0 := by
      rw [Submission.BoseGases.zeta1d_of_abs_le (le_of_eq heq)]
      rcases ht with ht | ht
      · rw [ht, show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two]
      · rw [ht, show Real.pi * (-1 / 2) = -(Real.pi / 2) by ring, Real.cos_neg,
          Real.cos_pi_div_two]
    exact hζ hz0

/-- **A.e. fibre integrability of the localised one-body kernel** (no diluteness hypothesis).

For almost every `x ∈ B(u)`, the `y`-fibre `y ↦ wSmall1Pair h M ℓ d u x y` is integrable over
`B(u)`.  The `(ℓd)`-scale renormalisation denominator is paid by the per-`x` polydisc bound
`exists_pos_le_conv3Small_of_polydisc` (the `y`-cutoff forces `(ℓd)⁻¹(x−y)` into the polydisc
`{|z_j| ≤ |a_x_j| + 1/2}` with `|a_x_j| < 1/2`), the `ℓ`-scale one by the a.e. fibre bound
`ae_integrable_fibre_wPairC`, and the two are combined in `abs_omF_le_fibre`. -/
theorem ae_integrable_omF_fibre {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : E3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
        (Submission.BoseGases.dlBox ℓ d u)),
      MeasureTheory.Integrable (fun y => omF h M ℓ d u (x, y))
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.dlBox ℓ d u)) := by
  classical
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set νA : MeasureTheory.Measure E3 := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict A
    with hνdef
  have hD3a : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      Submission.BoseGases.chiScale ℓ x ≠ 0 →
      MeasureTheory.Integrable
        (fun y : E3 => Submission.BoseGases.chiScale ℓ y *
          (|Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y)))
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    ae_integrable_fibre_wPairC hv_supp hR0 hv hvrad h ℓ hℓ
  have hmain : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      MeasureTheory.Integrable (fun y => omF h M ℓ d u (x, y)) νA := by
    filter_upwards [hD3a] with x hx
    by_cases hχ : Submission.BoseGases.chiSmallB M ℓ d u x = 0
    · have hzero : (fun y : E3 => omF h M ℓ d u (x, y)) = fun _ => (0 : ℝ) := by
        funext y
        simp only [omF_apply, Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
        rw [hχ]
        ring
      rw [hzero]
      exact MeasureTheory.integrable_zero E3 ℝ νA
    · have hχs : Submission.BoseGases.chiScale ℓ x ≠ 0 := by
        intro h0
        exact hχ (by rw [Submission.BoseGases.chiSmallB, h0, zero_mul])
      have hχax : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) ≠ 0 := by
        intro h0
        exact hχ (by rw [Submission.BoseGases.chiSmallB, h0, mul_zero])
      have hax : ∀ j : Fin 3, |((ℓ * d)⁻¹ • x - u).ofLp j| < 1 / 2 :=
        fun j => abs_coord_lt_half_of_chiSmall_ne_zero hM hχax j
      set ρ : ℝ := max (|((ℓ * d)⁻¹ • x - u).ofLp 0| + 1 / 2)
        (max (|((ℓ * d)⁻¹ • x - u).ofLp 1| + 1 / 2)
          (|((ℓ * d)⁻¹ • x - u).ofLp 2| + 1 / 2)) with hρdef
      have hρ1 : ρ < 1 := by
        rw [hρdef]
        exact max_lt (by linarith [hax 0]) (max_lt (by linarith [hax 1]) (by linarith [hax 2]))
      obtain ⟨c, hcpos, hc⟩ := exists_pos_le_conv3Small_of_polydisc (M := M) hM hρ1
      set ψ : E3 → ℝ := fun y => Submission.BoseGases.chiScale ℓ y *
        (|Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y))
        with hψdef
      have hψint : MeasureTheory.Integrable ψ (MeasureTheory.volume : MeasureTheory.Measure E3) :=
        hx hχs
      have hψintA : MeasureTheory.Integrable ψ νA :=
        hψint.mono_measure MeasureTheory.Measure.restrict_le_self
      have hden : ∀ y : E3, Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u) ≠ 0 →
          c ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) := by
        intro y hy
        have hyb : ∀ j : Fin 3, |((ℓ * d)⁻¹ • y - u).ofLp j| < 1 / 2 :=
          fun j => abs_coord_lt_half_of_chiSmall_ne_zero hM hy j
        have hcoord : ∀ j : Fin 3, |((ℓ * d)⁻¹ • (x - y)).ofLp j| ≤ ρ := by
          intro j
          have hsplit : ((ℓ * d)⁻¹ • (x - y)).ofLp j
              = ((ℓ * d)⁻¹ • x - u).ofLp j - ((ℓ * d)⁻¹ • y - u).ofLp j := by
            simp only [PiLp.smul_apply, PiLp.sub_apply]
            ring
          rw [hsplit]
          calc |((ℓ * d)⁻¹ • x - u).ofLp j - ((ℓ * d)⁻¹ • y - u).ofLp j|
              ≤ |((ℓ * d)⁻¹ • x - u).ofLp j| + |((ℓ * d)⁻¹ • y - u).ofLp j| := by
                calc |((ℓ * d)⁻¹ • x - u).ofLp j - ((ℓ * d)⁻¹ • y - u).ofLp j|
                    = |((ℓ * d)⁻¹ • x - u).ofLp j
                        + -(((ℓ * d)⁻¹ • y - u).ofLp j)| := by rw [sub_eq_add_neg]
                  _ ≤ |((ℓ * d)⁻¹ • x - u).ofLp j|
                        + |-(((ℓ * d)⁻¹ • y - u).ofLp j)| := abs_add_le _ _
                  _ = |((ℓ * d)⁻¹ • x - u).ofLp j| + |((ℓ * d)⁻¹ • y - u).ofLp j| := by
                      rw [abs_neg]
            _ ≤ |((ℓ * d)⁻¹ • x - u).ofLp j| + 1 / 2 := by linarith [hyb j]
            _ ≤ ρ := by
                rw [hρdef]
                fin_cases j
                · exact le_max_left _ _
                · exact le_trans (le_max_left _ _) (le_max_right _ _)
                · exact le_trans (le_max_right _ _) (le_max_right _ _)
        have hconv := hc ((ℓ * d)⁻¹ • (x - y)) hcoord
        simpa only [Submission.BoseGases.convScaleSmall] using hconv
      have hxle : |Submission.BoseGases.chiSmallB M ℓ d u x|
          ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
        refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le hM u x) ?_
        refine mul_le_mul_of_nonneg_left ?_ Submission.BoseGases.chiSupAbs_nonneg
        have hh := Submission.BoseGases.chiSmall_decay_coord_le_decay (M := M) hM
          ((ℓ * d)⁻¹ • x - u)
        rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hh
      refine MeasureTheory.Integrable.mono'
        (hψintA.const_mul (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
            * Submission.BoseGases.chiSmallDecay M / c)) ?_ ?_
      · exact (((Work.BoseFixB1B.aemeasurable_wSmallPair_fibre
          (f := Submission.BoseGases.g0 v h)
          (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable hM
          (ℓ := ℓ) (d := d) u x)).aestronglyMeasurable).mono_measure
          MeasureTheory.Measure.restrict_le_self
      · filter_upwards with y
        have h1 := abs_omF_le_fibre (h := h) (hM := hM) (ℓ := ℓ) (d := d) (u := u) (x := x)
          (c := c) hcpos hxle hden y
        rw [Real.norm_eq_abs]
        exact h1
  exact (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_le_self : νA ≤ MeasureTheory.volume))
    hmain

theorem boxM2_sub_boxM1_eq_omegaMass {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
    = ∫ p in (Submission.BoseGases.dlBox ℓ d u) ×ˢ (Submission.BoseGases.dlBox ℓ d u),
        Classical.choose h (p.1 - p.2)
          * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 := by
  classical
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set νA : MeasureTheory.Measure E3 := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict A
    with hνdef
  have hAmeas : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  -- ### the vanishing of the localised kernels off `A × A`
  have hvanF : ∀ x y : E3, (x ∉ A ∨ y ∉ A) → Submission.BoseGases.wSmallPair M ℓ d u
      (Submission.BoseGases.g0 v h) x y = 0 :=
    fun x y hxy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  have hvanG : ∀ x y : E3, (x ∉ A ∨ y ∉ A) → Submission.BoseGases.wSmallPair M ℓ d u
      (Submission.BoseGases.g2 v h) x y = 0 :=
    fun x y hxy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  have hvanF' : ∀ x y : E3, (x ∉ A ∨ y ∉ A) → omF h M ℓ d u (x, y) = 0 :=
    fun x y hxy => hvanF x y hxy
  -- ### `boxM2`, `boxM1` and the right-hand side in a common shape
  have hbox2 : Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
      (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      = ∫ p in A ×ˢ A, omG h M ℓ d u p := rfl
  have hbox1 : Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      = ∫ x in A, ∫ y in A, omF h M ℓ d u (x, y) := by
    have h1 : Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        = ∫ x : E3, ∫ y : E3, omF h M ℓ d u (x, y) := by
      change Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h))
        = ∫ x : E3, ∫ y : E3, omF h M ℓ d u (x, y)
      rw [Work.BoseFixB1S.boxM1_eq_nested u hvanF]
      rfl
    rw [h1]
    have hout : (∫ x : E3, ∫ y : E3, omF h M ℓ d u (x, y))
        = ∫ x in A, ∫ y : E3, omF h M ℓ d u (x, y) :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := A) (f := fun x : E3 => ∫ y : E3, omF h M ℓ d u (x, y))
        (fun x hx => by
          have hzero : (fun y : E3 => omF h M ℓ d u (x, y)) = fun _ => (0 : ℝ) := by
            funext y
            exact hvanF' x y (Or.inl hx)
          rw [hzero, MeasureTheory.integral_zero])).symm
    rw [hout]
    refine MeasureTheory.setIntegral_congr_fun hAmeas (fun x _ => ?_)
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hvanF' x y (Or.inr hy))).symm
  have hrhs : (∫ p in A ×ˢ A, Classical.choose h (p.1 - p.2)
        * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      = ∫ p in A ×ˢ A, omH h M ℓ d u p :=
    MeasureTheory.setIntegral_congr_fun (hAmeas.prod hAmeas) (fun p _ => rfl)
  have hbox2' : Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) A
      (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      = ∫ p, omG h M ℓ d u p ∂(νA.prod νA) := by
    rw [hbox2]
    change (∫ p, omG h M ℓ d u p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)).restrict (A ×ˢ A))
      = ∫ p, omG h M ℓ d u p ∂(νA.prod νA)
    rw [← MeasureTheory.Measure.prod_restrict (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) A A]
  have hrhs' : (∫ p in A ×ˢ A, Classical.choose h (p.1 - p.2)
        * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      = ∫ p, omH h M ℓ d u p ∂(νA.prod νA) := by
    rw [hrhs]
    change (∫ p, omH h M ℓ d u p ∂((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)).restrict (A ×ˢ A))
      = ∫ p, omH h M ℓ d u p ∂(νA.prod νA)
    rw [← MeasureTheory.Measure.prod_restrict (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) A A]
  rw [hbox2', hbox1, hrhs']
  show (∫ p, omG h M ℓ d u p ∂(νA.prod νA)) - (∫ x, ∫ y, omF h M ℓ d u (x, y) ∂νA ∂νA)
      = ∫ p, omH h M ℓ d u p ∂(νA.prod νA)
  -- ### the a.e. sandwich of the three integrands (from the ω₀ lower bound)
  obtain ⟨hFnn0, hHnn0, hHF0, hcF0⟩ := ae_om_bounds hv_supp hR0 hv hvrad h hM ℓ d u
  have hle : νA.prod νA ≤ (MeasureTheory.volume : MeasureTheory.Measure E3).prod
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    rw [hνdef]
    exact MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self
      MeasureTheory.Measure.restrict_le_self
  have hFnn : ∀ᵐ p ∂(νA.prod νA), 0 ≤ omF h M ℓ d u p := (MeasureTheory.ae_mono hle) hFnn0
  have hHnn : ∀ᵐ p ∂(νA.prod νA), 0 ≤ omH h M ℓ d u p := (MeasureTheory.ae_mono hle) hHnn0
  have hHF : ∀ᵐ p ∂(νA.prod νA), omH h M ℓ d u p ≤ omF h M ℓ d u p :=
    (MeasureTheory.ae_mono hle) hHF0
  have hcF : ∀ᵐ p ∂(νA.prod νA),
      (_root_.BoseGases.a v / (2 * R0)) * omF h M ℓ d u p ≤ omH h M ℓ d u p :=
    (MeasureTheory.ae_mono hle) hcF0
  have hGnn : ∀ᵐ p ∂(νA.prod νA), 0 ≤ omG h M ℓ d u p := by
    filter_upwards [hFnn, hHnn] with p h1 h2
    rw [omG_eq_omF_add_omH h M ℓ d u p]
    exact add_nonneg h1 h2
  -- the fibre versions
  have hFnnf : ∀ᵐ x ∂νA, ∀ᵐ y ∂νA, 0 ≤ omF h M ℓ d u (x, y) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hFnn
  have hHnnf : ∀ᵐ x ∂νA, ∀ᵐ y ∂νA, 0 ≤ omH h M ℓ d u (x, y) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hHnn
  have hHFf : ∀ᵐ x ∂νA, ∀ᵐ y ∂νA, omH h M ℓ d u (x, y) ≤ omF h M ℓ d u (x, y) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hHF
  have hcFf : ∀ᵐ x ∂νA, ∀ᵐ y ∂νA,
      (_root_.BoseGases.a v / (2 * R0)) * omF h M ℓ d u (x, y) ≤ omH h M ℓ d u (x, y) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hcF
  -- ### a.e. measurability of the ingredients
  have hg0aem : AEMeasurable (Submission.BoseGases.g0 v h)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
  have hw0aesm : MeasureTheory.AEStronglyMeasurable (Classical.choose h)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    (Classical.choose_spec h).2.lhs_integrable.aestronglyMeasurable
  have hg2aem : AEMeasurable (Submission.BoseGases.g2 v h)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    have hv' : AEMeasurable v (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      hv1.aestronglyMeasurable.aemeasurable
    have hw : AEMeasurable (Classical.choose h) (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      hw0aesm.aemeasurable
    rw [show Submission.BoseGases.g2 v h
        = fun x => (v x * (1 - Classical.choose h x)) * (1 + Classical.choose h x) from rfl]
    exact (hv'.mul (aemeasurable_const.sub hw)).mul (aemeasurable_const.add hw)
  have hqmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3))
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant _ _
  have hFaesm0 : MeasureTheory.AEStronglyMeasurable (fun p => omF h M ℓ d u p)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) :=
    Work.BoseFixB1.aesm_wSmallPair_prod_full u hg0aem
  have hGaesm0 : MeasureTheory.AEStronglyMeasurable (fun p => omG h M ℓ d u p)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) :=
    Work.BoseFixB1.aesm_wSmallPair_prod_full u hg2aem
  have hHaesm0 : MeasureTheory.AEStronglyMeasurable (fun p => omH h M ℓ d u p)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) :=
    (hw0aesm.comp_quasiMeasurePreserving hqmp).mul hFaesm0
  have hFaesm : MeasureTheory.AEStronglyMeasurable (fun p => omF h M ℓ d u p) (νA.prod νA) :=
    hFaesm0.mono_measure hle
  have hGaesm : MeasureTheory.AEStronglyMeasurable (fun p => omG h M ℓ d u p) (νA.prod νA) :=
    hGaesm0.mono_measure hle
  have hHaesm : MeasureTheory.AEStronglyMeasurable (fun p => omH h M ℓ d u p) (νA.prod νA) :=
    hHaesm0.mono_measure hle
  -- ### the a.e. fibre integrability
  have hFfibint : ∀ᵐ x ∂νA, MeasureTheory.Integrable (fun y => omF h M ℓ d u (x, y)) νA :=
    ae_integrable_omF_fibre hv_supp hR0 hv hvrad h hM hℓ hd u
  have hHfibint : ∀ᵐ x ∂νA, MeasureTheory.Integrable (fun y => omH h M ℓ d u (x, y)) νA := by
    filter_upwards [hFfibint, hHnnf, hHFf] with x hFx hHnnx hHFx
    have hνAle : νA ≤ (MeasureTheory.volume : MeasureTheory.Measure E3) := by
      rw [hνdef]
      exact MeasureTheory.Measure.restrict_le_self
    have hAESM : MeasureTheory.AEStronglyMeasurable (fun y => omH h M ℓ d u (x, y)) νA :=
      (((hw0aesm.comp_quasiMeasurePreserving
        (MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant _ x)).mul
        ((Work.BoseFixB1B.aemeasurable_wSmallPair_fibre hg0aem hM (ℓ := ℓ) (d := d) u
          x).aestronglyMeasurable)).mono_measure hνAle)
    refine MeasureTheory.Integrable.mono' hFx hAESM ?_
    filter_upwards [hHnnx, hHFx] with y h1 h2
    rw [Real.norm_of_nonneg h1]
    exact h2
  have hGfibint : ∀ᵐ x ∂νA, MeasureTheory.Integrable (fun y => omG h M ℓ d u (x, y)) νA := by
    filter_upwards [hFfibint, hHfibint] with x hFx hHx
    rw [show (fun y => omG h M ℓ d u (x, y))
        = fun y => omF h M ℓ d u (x, y) + omH h M ℓ d u (x, y) from
      funext (fun y => omG_eq_omF_add_omH h M ℓ d u (x, y))]
    exact hFx.add hHx
  -- ### the two Fubini-type identifications
  have hIG : ∫ p, omG h M ℓ d u p ∂(νA.prod νA) = ∫ x, ∫ y, omG h M ℓ d u (x, y) ∂νA ∂νA :=
    integral_prod_eq_iterated_of_ae_fibre_integrable hGaesm hGnn hGfibint
  have hIH : ∫ p, omH h M ℓ d u p ∂(νA.prod νA) = ∫ x, ∫ y, omH h M ℓ d u (x, y) ∂νA ∂νA :=
    integral_prod_eq_iterated_of_ae_fibre_integrable hHaesm hHnn hHfibint
  -- ### the outer-level additivity
  have hFAESM : MeasureTheory.AEStronglyMeasurable
      (fun x => ∫ y, omF h M ℓ d u (x, y) ∂νA) νA :=
    hFaesm.integral_prod_right'
  have hHAESM : MeasureTheory.AEStronglyMeasurable
      (fun x => ∫ y, omH h M ℓ d u (x, y) ∂νA) νA :=
    hHaesm.integral_prod_right'
  have hFnnO : 0 ≤ᵐ[νA] (fun x => ∫ y, omF h M ℓ d u (x, y) ∂νA) := by
    filter_upwards [hFnnf] with x hx
    exact MeasureTheory.integral_nonneg_of_ae hx
  have hHFO : (fun x => ∫ y, omH h M ℓ d u (x, y) ∂νA)
      ≤ᵐ[νA] (fun x => ∫ y, omF h M ℓ d u (x, y) ∂νA) := by
    filter_upwards [hFfibint, hHfibint, hHFf] with x hFx hHx hHFx
    exact MeasureTheory.integral_mono_ae hHx hFx hHFx
  have hcFO : ∀ᵐ x ∂νA,
      (_root_.BoseGases.a v / (2 * R0)) * (∫ y, omF h M ℓ d u (x, y) ∂νA)
        ≤ ∫ y, omH h M ℓ d u (x, y) ∂νA := by
    filter_upwards [hFfibint, hHfibint, hcFf] with x hFx hHx hcFx
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono_ae (hFx.const_mul _) hHx hcFx
  by_cases hc : 0 < _root_.BoseGases.a v / (2 * R0)
  · -- ### the generic case: split both nested integrals with the sandwich lemma
    have hfib : ∀ᵐ x ∂νA, (∫ y, omG h M ℓ d u (x, y) ∂νA)
        = (∫ y, omF h M ℓ d u (x, y) ∂νA) + (∫ y, omH h M ℓ d u (x, y) ∂νA) := by
      filter_upwards [hFfibint, hHfibint, hFnnf, hHFf, hcFf] with x hFx hHx hFnnx hHFx hcFx
      have hνAle : νA ≤ (MeasureTheory.volume : MeasureTheory.Measure E3) := by
        rw [hνdef]
        exact MeasureTheory.Measure.restrict_le_self
      have hFxA : MeasureTheory.AEStronglyMeasurable (fun y => omF h M ℓ d u (x, y)) νA :=
        ((Work.BoseFixB1B.aemeasurable_wSmallPair_fibre hg0aem hM (ℓ := ℓ) (d := d) u
          x).aestronglyMeasurable).mono_measure hνAle
      have hHxA : MeasureTheory.AEStronglyMeasurable (fun y => omH h M ℓ d u (x, y)) νA :=
        (((hw0aesm.comp_quasiMeasurePreserving
          (MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant _ x)).mul
          ((Work.BoseFixB1B.aemeasurable_wSmallPair_fibre hg0aem hM (ℓ := ℓ) (d := d) u
            x).aestronglyMeasurable)).mono_measure hνAle)
      have hstep := integral_add_of_le_of_const_mul_le (μ := νA)
        (f := fun y => omF h M ℓ d u (x, y)) (h := fun y => omH h M ℓ d u (x, y))
        hc hFxA hHxA hFnnx hHFx hcFx
      rw [← hstep]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y =>
        omG_eq_omF_add_omH h M ℓ d u (x, y)))
    have houter := integral_add_of_le_of_const_mul_le (μ := νA)
      (f := fun x => ∫ y, omF h M ℓ d u (x, y) ∂νA)
      (h := fun x => ∫ y, omH h M ℓ d u (x, y) ∂νA) hc hFAESM hHAESM hFnnO hHFO hcFO
    show (∫ p, omG h M ℓ d u p ∂(νA.prod νA)) - (∫ x, ∫ y, omF h M ℓ d u (x, y) ∂νA ∂νA)
      = ∫ p, omH h M ℓ d u p ∂(νA.prod νA)
    rw [hIG, hIH, MeasureTheory.integral_congr_ae hfib, houter]
    ring
  · -- ### the degenerate case `a v = 0`: all three integrands vanish a.e.
    have hnn : 0 ≤ _root_.BoseGases.a v :=
      (Submission.BoseGases.av_bounds_weak (v := v) hR0 hv hvrad hv_supp h).1
    have hquot0 : _root_.BoseGases.a v / (2 * R0) = 0 := by
      refine le_antisymm (le_of_not_gt hc) ?_
      exact div_nonneg hnn (by linarith)
    have hav0 : _root_.BoseGases.a v = 0 := by
      rcases (div_eq_zero_iff.mp hquot0) with h | h
      · exact h
      · exact absurd h (by linarith : (2 * R0 : ℝ) ≠ 0)
    have hg0ae0 : Submission.BoseGases.g0 v h =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure E3)] 0 := by
      refine (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Submission.BoseGases.g0_nonneg_ae (R := R0) hR0 hv hvrad hv_supp h)
        (Submission.BoseGases.g0_integrable hR0 hv_supp h)).mp ?_
      change (∫ x : E3, v x * (1 - Classical.choose h x)) = 0
      rw [Submission.BoseGases.chosen_scattering_integral h, hav0, mul_zero]
    have hFae0 : (fun p : E3 × E3 => omF h M ℓ d u p) =ᵐ[
        (MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)] 0 := by
      filter_upwards [hqmp.ae hg0ae0] with p hp
      have hp' : Submission.BoseGases.g0 v h (p.1 - p.2) = 0 := by simpa using hp
      show Submission.BoseGases.chiSmallB M ℓ d u p.1
          * ((Submission.BoseGases.g0 v h (p.1 - p.2)
              / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
            / Submission.BoseGases.convScale ℓ (p.1 - p.2))
          * Submission.BoseGases.chiSmallB M ℓ d u p.2 = 0
      rw [hp']
      ring
    have hGae0 : (fun p : E3 × E3 => omG h M ℓ d u p) =ᵐ[
        (MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)] 0 := by
      filter_upwards [hFae0] with p hp
      have hp' : omF h M ℓ d u p = 0 := by simpa using hp
      have hp'' : omH h M ℓ d u p = 0 := by
        show Classical.choose h (p.1 - p.2) * omF h M ℓ d u p = 0
        rw [hp', mul_zero]
      rw [omG_eq_omF_add_omH h M ℓ d u p, hp', hp'', add_zero, Pi.zero_apply]
    have hHae0 : (fun p : E3 × E3 => omH h M ℓ d u p) =ᵐ[
        (MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)] 0 := by
      filter_upwards [hFae0] with p hp
      have hp' : omF h M ℓ d u p = 0 := by simpa using hp
      show Classical.choose h (p.1 - p.2) * omF h M ℓ d u p = 0
      rw [hp', mul_zero]
    have hFaeA : (fun p : E3 × E3 => omF h M ℓ d u p) =ᵐ[νA.prod νA] 0 :=
      (MeasureTheory.ae_mono hle) hFae0
    have hGaeA : (fun p : E3 × E3 => omG h M ℓ d u p) =ᵐ[νA.prod νA] 0 :=
      (MeasureTheory.ae_mono hle) hGae0
    have hHaeA : (fun p : E3 × E3 => omH h M ℓ d u p) =ᵐ[νA.prod νA] 0 :=
      (MeasureTheory.ae_mono hle) hHae0
    have hFfib0 : ∀ᵐ x ∂νA, (fun y => omF h M ℓ d u (x, y)) =ᵐ[νA] 0 :=
      MeasureTheory.Measure.ae_ae_eq_curry_of_prod hFaeA
    have hIG0 : ∫ p, omG h M ℓ d u p ∂(νA.prod νA) = 0 :=
      MeasureTheory.integral_eq_zero_of_ae hGaeA
    have hIH0 : ∫ p, omH h M ℓ d u p ∂(νA.prod νA) = 0 :=
      MeasureTheory.integral_eq_zero_of_ae hHaeA
    have hIF0 : (∫ x, ∫ y, omF h M ℓ d u (x, y) ∂νA ∂νA) = 0 := by
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hFfib0] with x hx
      exact MeasureTheory.integral_eq_zero_of_ae hx
    show (∫ p, omG h M ℓ d u p ∂(νA.prod νA)) - (∫ x, ∫ y, omF h M ℓ d u (x, y) ∂νA ∂νA)
      = ∫ p, omH h M ℓ d u p ∂(νA.prod νA)
    rw [hIG0, hIF0, hIH0]
    ring

end Work.BoseFixB1B
