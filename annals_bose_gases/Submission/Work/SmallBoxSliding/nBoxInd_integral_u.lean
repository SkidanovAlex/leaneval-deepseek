import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.boxInd_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The particle-number identity of the indicator-box sliding layer

FS `eq:appsliding`'s particle-number telescoping in the **exact** continuum
form of `Indicator.lean` (item (iv) of that file's header):

    ∫_u (∫_x ρ x · 1_{B(u)}(x) dx) du = ∫_{acube ℓ} ρ  ,

i.e. summing the `B(u)`-mass of a density `ρ` over all positions `u` of the
small box `B(u) = dlBox ℓ d u` recovers the mass of `ρ` over the big box
`acube ℓ`.  This is the exact analogue of `nBox_integral_u` (the
`χ_{B(u)}²`-weighted version), and it is the indicator-layer input to the
sliding-sum bookkeeping.

The mathematical content is the *tube* computation: for fixed `x` the set of
positions `u` with `x ∈ B(u)` is the cube `(ℓd)•u ∈ x - acube(ℓd)`, whose
`u`-volume is `1` (`(ℓd)⁻¹ • acube (ℓd) = acube 1`, `|acube 1| = 1`), so

    ∫_u 1_{B(u)}(x) du = 1_{x ∈ acube ℓ}      (`boxInd_integral_u_aux`),

which is `boxInd_integral_u` restated with the helper proved in place (the
colleague's file `boxInd_integral_u` is not used here, so this module is
self-contained).  The target then follows from Fubini in the orientation of
the hypothesis (`integrable_swap_iff` + `integral_integral_symm` +
`integral_prod`) and the identification `ρ x · 1_{x ∈ acube ℓ} = 1_{acube ℓ} ρ x`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-! ## Three elementary ingredients -/

/-- Membership in the centred cube `acube ℓ` by absolute values. -/
lemma mem_acube_iff_abs (ℓ : ℝ) (y : ℝ³) :
    y ∈ acube ℓ ↔ ∀ k : Fin 3, |y k| ≤ ℓ / 2 := by
  simp only [mem_acube_iff, Set.mem_Icc, abs_le, neg_div]

/-- **Scaling of the centred cube**: for `c > 0`, the cube of side `c` scaled
by `c` is the unit cube, `c • acube c = acube 1` on points. -/
lemma smul_mem_acube_iff {c : ℝ} (hc : 0 < c) (z : ℝ³) :
    c • z ∈ acube c ↔ z ∈ acube 1 := by
  rw [mem_acube_iff_abs, mem_acube_iff_abs]
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
  constructor
  · intro h k
    have hk := h k
    have h2 : c * |z k| ≤ c * (1 / 2) := by linarith
    exact le_of_mul_le_mul_left h2 hc
  · intro h k
    have hk := h k
    have h2 : c * |z k| ≤ c * (1 / 2) := mul_le_mul_of_nonneg_left hk (le_of_lt hc)
    linarith

/-- **Reflection invariance** of the Lebesgue integral on `ℝ³`:
`∫ u, F (c - u) = ∫ u, F u` (the map `u ↦ c - u` is a measure-preserving
involution of `(ℝ³, volume)`). -/
lemma integral_comp_sub_eq_self {F : ℝ³ → ℝ} (c : ℝ³) :
    (∫ u : ℝ³, F (c - u)) = ∫ u : ℝ³, F u := by
  have h1 : (∫ u : ℝ³, F (c - u)) = ∫ u : ℝ³, (fun v => F (-v)) (u - c) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [neg_sub]
  rw [h1, MeasureTheory.integral_sub_right_eq_self (μ := volume) (fun v => F (-v)) c,
      MeasureTheory.integral_neg_eq_self (μ := volume) F]

/-! ## The box indicator as a product of two cube indicators -/

/-- The box indicator factorises into the two cube indicators of its
definition, `1_{B(u)}(x) = 1_{acube ℓ}(x) · 1_{acube (ℓd)}(x - (ℓd)•u)`. -/
lemma boxInd_eq_mul {ℓ d : ℝ} (u x : ℝ³) :
    boxInd ℓ d u x = (acube ℓ).indicator (fun _ => (1 : ℝ)) x
      * (acube (ℓ * d)).indicator (fun _ => (1 : ℝ)) (x - (ℓ * d) • u) := by
  simp only [boxInd, dlBox]
  by_cases hx : x ∈ acube ℓ
  · by_cases hy : x - (ℓ * d) • u ∈ acube (ℓ * d)
    · rw [Set.indicator_of_mem (show x ∈ acube ℓ ∩ {y : ℝ³ | y - (ℓ * d) • u ∈ acube (ℓ * d)}
          from ⟨hx, hy⟩),
          Set.indicator_of_mem hx, Set.indicator_of_mem hy, mul_one]
    · rw [Set.indicator_of_notMem (show x ∉ acube ℓ ∩ {y : ℝ³ | y - (ℓ * d) • u ∈ acube (ℓ * d)}
          from fun h => hy h.2),
          Set.indicator_of_mem hx, Set.indicator_of_notMem hy, mul_zero]
  · rw [Set.indicator_of_notMem (show x ∉ acube ℓ ∩ {y : ℝ³ | y - (ℓ * d) • u ∈ acube (ℓ * d)}
        from fun h => hx h.1),
        Set.indicator_of_notMem hx, zero_mul]

/-! ## The per-point tube integral -/

/-- **The tube identity**: for a point `x`, the set of positions `u` of the
small box for which `x ∈ B(u)` has measure `1` if `x` lies in the big box and
is empty otherwise:

    `∫_u 1_{B(u)}(x) du = 1_{acube ℓ}(x)`.

(Substituting `y := (ℓd)•u` turns the `u`-integral into the volume of
`(ℓd)⁻¹ • acube (ℓd) = acube 1`, of volume `1`.)  This is
`boxInd_integral_u` with the proof carried out here, so that this module does
not depend on the (currently unproved) collegial file of that name. -/
lemma boxInd_integral_u_aux {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (x : ℝ³) :
    (∫ u : ℝ³, boxInd ℓ d u x) = (acube ℓ).indicator (fun _ => (1 : ℝ)) x := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hne : ℓ * d ≠ 0 := ne_of_gt hld
  simp only [boxInd_eq_mul]
  by_cases hx : x ∈ acube ℓ
  · -- `x` in the big box: pull out the constant and integrate over the `u`-tube
    have hpt2 : ∀ u : ℝ³, (acube ℓ).indicator (fun _ => (1 : ℝ)) x
        * (acube (ℓ * d)).indicator (fun _ => (1 : ℝ)) (x - (ℓ * d) • u)
        = (acube (ℓ * d)).indicator (fun _ => (1 : ℝ)) (x - (ℓ * d) • u) := by
      intro u; rw [Set.indicator_of_mem hx, one_mul]
    simp_rw [hpt2]
    simp only [Set.indicator_of_mem hx]
    -- rewrite `x - (ℓd)•u = (ℓd) • ((ℓd)⁻¹•x - u)`
    have hsmul : ∀ u : ℝ³, x - (ℓ * d) • u = (ℓ * d) • ((ℓ * d)⁻¹ • x - u) := by
      intro u
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]
    simp_rw [hsmul]
    -- scale the cube of side `ℓd` back to the unit cube
    have hind : ∀ z : ℝ³, (acube (ℓ * d)).indicator (fun _ => (1 : ℝ)) ((ℓ * d) • z)
        = (acube 1).indicator (fun _ => (1 : ℝ)) z := by
      intro z
      by_cases hz : z ∈ acube 1
      · rw [Set.indicator_of_mem ((smul_mem_acube_iff hld z).mpr hz), Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem (fun hzz => hz ((smul_mem_acube_iff hld z).mp hzz)),
            Set.indicator_of_notMem hz]
    simp_rw [hind]
    -- translation invariance + the unit cube has volume one
    rw [integral_comp_sub_eq_self ((ℓ * d)⁻¹ • x),
      MeasureTheory.integral_indicator_const (1 : ℝ) (acube_measurable 1), Measure.real_def,
      acube_volume 1 zero_le_one, one_pow, ENNReal.toReal_ofReal zero_le_one, one_smul]
  · -- `x` outside the big box: the integrand vanishes identically
    simp only [Set.indicator_of_notMem hx, zero_mul, integral_zero]

/-! ## The particle-number identity -/

theorem nBoxInd_integral_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ρ p.1 * Work.SmallBoxSliding.boxInd ℓ d p.2 p.1)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), ∫ x : EuclideanSpace ℝ (Fin 3),
        ρ x * Work.SmallBoxSliding.boxInd ℓ d u x)
      = ∫ x in Submission.BoseGases.acube ℓ, ρ x := by
  -- integrability in the Fubini orientation needed below
  have hswap : MeasureTheory.Integrable
      (fun p : ℝ³ × ℝ³ => ρ p.2 * boxInd ℓ d p.1 p.2) (volume.prod volume) :=
    (MeasureTheory.integrable_swap_iff (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³))).mp hint
  calc (∫ u : ℝ³, ∫ x : ℝ³, ρ x * boxInd ℓ d u x)
      = ∫ z : ℝ³ × ℝ³, ρ z.1 * boxInd ℓ d z.2 z.1 :=
        MeasureTheory.integral_integral_symm (f := fun u x => ρ x * boxInd ℓ d u x) hswap
    _ = ∫ x : ℝ³, ∫ u : ℝ³, ρ x * boxInd ℓ d u x :=
        MeasureTheory.integral_prod _ hint
    -- the `u`-integral of the inner integrand is the big-box indicator
    _ = ∫ x : ℝ³, ρ x * (acube ℓ).indicator (fun _ => (1 : ℝ)) x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [MeasureTheory.integral_const_mul, boxInd_integral_u_aux hℓ hd x]
    -- and `ρ · 1_{acube ℓ} = 1_{acube ℓ} ρ`
    _ = ∫ x in acube ℓ, ρ x := by
        rw [← MeasureTheory.integral_indicator (acube_measurable ℓ)]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ acube ℓ
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

end Work.SmallBoxSliding
