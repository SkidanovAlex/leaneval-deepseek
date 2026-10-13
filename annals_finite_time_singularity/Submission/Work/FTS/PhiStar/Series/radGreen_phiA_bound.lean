/-
# `radGreen_phiA_bound` — the `O(1/(z(m+1)²))` bound on the radial Green's function of `𝒜φ`

`Work.FTS.PhiStar.Radial.radGreen α m c` is the decaying-at-`∞` solution of the mode-`m` Euler
equation with source `c` (`Submission/Work/FTS/PhiStar/Radial/Defs.lean`):

  `radGreen α m c z = 1/(α(4m+5)) · ( z^{s⁻}·∫_0^z c t·t^{s⁺-1} dt
                                      + z^{s⁺}·∫_{Ioi z} c t·t^{-s⁺-1} dt )`

with `s⁻ = -(2m+5)/α` and `s⁺ = 2m/α`.  Here we bound it for the *specific* source
`c = 𝒜φ = VocabO.phiA α`, whose only structural input is the pointwise bound
`|𝒜φ α t| ≤ 24/t` for every `t > 0` (a consequence of the two regimes
`Deleg.phiA_abs_le_small` (`|𝒜φ| ≤ 20t` for `0 < t ≤ 1`) and `Deleg.phiA_abs_le_large`
(`|𝒜φ| ≤ 24/t` for `t ≥ 1`)).

The estimate obtained is, for every `z > 0`, `0 < α ≤ 1` and `m ≥ 1`,

  `|radGreen α m (𝒜φ α) z| ≤ 24 / (z·(m+1)²)`,

uniformly in `α ∈ (0,1]`.  It implies both conjuncts of the target statement with the same
constant `C = 24`:

* `24/(z(m+1)²) ≤ 24·(1+1/z)·(m+1)^{-2}` since `1/z ≤ 1 + 1/z`;
* `24/(z(m+1)²) ≤ 24/(z(m+1))` since `m + 1 ≥ 1`.

## The proof

Put `p = (2m+5)/α`, `q = 2m/α`, `K = 1/(α(4m+5))`.  Since `|c t| ≤ M/t` with `M = 24`:

* `|∫_0^z c t·t^{p-1} dt| ≤ ∫_0^z M·t^{p-2} dt = M·z^{p-1}/(p-1)`, hence the head piece is
  `≤ K·M/(p-1) = M/(z·(4m+5)·(2m+5-α))`;
* `|∫_{Ioi z} c t·t^{-q-1} dt| ≤ ∫_{Ioi z} M·t^{-q-2} dt = M·z^{-q-1}/(q+1)`, hence the tail
  piece is `≤ K·M/(q+1) = M/(z·(4m+5)·(2m+α))`;
* `1/(2m+5-α) + 1/(2m+α) ≤ 1/m` and `m(4m+5) ≥ (m+1)²` finish the job.

The two elementary integrals are Mathlib's `integral_rpow` and `integral_Ioi_rpow_of_lt`; the
comparison of an integral with its `M`-fold majorant uses the pointwise a.e. form of
`norm_integral_le_of_norm_le`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.Series.Deleg.phiAPointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary integral computations -/

/-- `∫_0^z t^{p-2} dt = z^{p-1}/(p-1)` for `p ≥ 3`, `z > 0`. -/
theorem rpowInt_zero_to_z_sub_two {p z : ℝ} (hp : 3 ≤ p) (hz : 0 < z) :
    ∫ t in (0 : ℝ)..z, t ^ (p - 2) = z ^ (p - 1) / (p - 1) := by
  have h := integral_rpow (a := (0 : ℝ)) (b := z) (r := p - 2)
    (Or.inl (by linarith : (-1 : ℝ) < p - 2))
  rw [show p - 2 + 1 = p - 1 by ring, Real.zero_rpow (by linarith : p - 1 ≠ 0)] at h
  simpa using h

/-- `∫_{Ioi z} t^{-q-2} dt = z^{-q-1}/(q+1)` for `q > 0`, `z > 0`. -/
theorem rpowInt_Ioi_neg_two {q z : ℝ} (hq : 0 < q) (hz : 0 < z) :
    ∫ t in Set.Ioi z, t ^ (-q - 2) = z ^ (-q - 1) / (q + 1) := by
  have h := integral_Ioi_rpow_of_lt (a := -q - 2) (c := z) (by linarith) hz
  rw [show -q - 2 + 1 = -q - 1 by ring] at h
  rw [h]
  have h1 : (-q - 1 : ℝ) ≠ 0 := by linarith
  have h2 : (q + 1 : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-! ## Comparison of an integral with a pointwise majorant -/

/-- **Interval-integral comparison.**  If `|f| ≤ g` on `Ioc a b` and `g` is interval integrable,
then `|∫_a^b f| ≤ ∫_a^b g`. -/
theorem abs_intervalIntegral_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ioc a b, |f t| ≤ g t) (hg : IntervalIntegrable g volume a b) :
    |∫ t in a..b, f t| ≤ ∫ t in a..b, g t := by
  have h' : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b → ‖f t‖ ≤ g t :=
    Eventually.of_forall fun t ht => by simpa [Real.norm_eq_abs] using h t ht
  have h2 := intervalIntegral.norm_integral_le_of_norm_le hab h' hg
  simpa [Real.norm_eq_abs] using h2

/-- **Set-integral comparison on a tail `Ioi z`.**  If `|f| ≤ g` on `Ioi z` and `g` is integrable
there, then `|∫_{Ioi z} f| ≤ ∫_{Ioi z} g`. -/
theorem abs_setIntegral_Ioi_le {f g : ℝ → ℝ} {z : ℝ}
    (h : ∀ t ∈ Set.Ioi z, |f t| ≤ g t) (hg : IntegrableOn g (Set.Ioi z) volume) :
    |∫ t in Set.Ioi z, f t| ≤ ∫ t in Set.Ioi z, g t := by
  have h' : ∀ᵐ t ∂(volume.restrict (Set.Ioi z)), ‖f t‖ ≤ g t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun t ht => by simpa [Real.norm_eq_abs] using h t ht
  have h2 := MeasureTheory.norm_integral_le_of_norm_le hg h'
  simpa [Real.norm_eq_abs] using h2

/-! ## A rational identity used for the normalising factor -/

private lemma one_div_mul_one_div (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    1 / (a * b) * (1 / c) = 1 / (b * (a * c)) := by
  field_simp

/-! ## The Green-function estimate -/

/-- **The mode-`m` radial Green's function of a source with `1/t` decay.**  If `|c t| ≤ M/t` for
every `t > 0`, then for `0 < α ≤ 1` and `m ≥ 1`

  `|radGreen α m c z| ≤ M / (z·(m+1)²)`   for every `z > 0`.

(The estimate is uniform in `α`: the `α`-dependence of the two indicial exponents cancels against
the normalising factor `1/(α(4m+5))`.) -/
private lemma radGreen_le_of_inv_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) {c : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ t : ℝ, 0 < t → |c t| ≤ M / t) {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ M / (z * ((m : ℝ) + 1) ^ 2) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp3 : (3 : ℝ) ≤ (2 * (m : ℝ) + 5) / α := by
    rw [le_div_iff₀ hα]
    nlinarith
  set p : ℝ := (2 * (m : ℝ) + 5) / α with hp
  set q : ℝ := 2 * (m : ℝ) / α with hq
  have hp3' : (3 : ℝ) ≤ p := hp ▸ hp3
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hq0 : (0 : ℝ) < q := by
    rw [hq]
    positivity
  have hKpos : (0 : ℝ) < 1 / (α * (4 * (m : ℝ) + 5)) := by positivity
  -- integrability of the two majorants
  have hInt1 : IntervalIntegrable (fun t : ℝ => M * t ^ (p - 2)) volume (0 : ℝ) z := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const (fun t _ => Or.inr (by linarith : (0 : ℝ) ≤ p - 2)))
  have hInt2 : IntegrableOn (fun t : ℝ => M * t ^ (-q - 2)) (Set.Ioi z) volume := by
    have h := integrableOn_Ioi_rpow_of_lt (a := -q - 2) (c := z) (by linarith) hz
    exact h.const_mul M
  -- pointwise comparison of the integrands with the majorants
  have hpoint1 : ∀ t ∈ Set.Ioc (0 : ℝ) z, |c t * t ^ (p - 1)| ≤ M * t ^ (p - 2) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hpown : (0 : ℝ) ≤ t ^ (p - 1) := Real.rpow_nonneg ht0.le _
    rw [abs_mul, abs_of_nonneg hpown]
    calc |c t| * t ^ (p - 1)
        ≤ (M / t) * t ^ (p - 1) := mul_le_mul_of_nonneg_right (hc t ht0) hpown
      _ = M * (t ^ (-1 : ℝ) * t ^ (p - 1)) := by
            rw [div_eq_mul_inv, Real.rpow_neg_one]; ring
      _ = M * t ^ ((-1 : ℝ) + (p - 1)) := by rw [Real.rpow_add ht0]
      _ = M * t ^ (p - 2) := by rw [show (-1 : ℝ) + (p - 1) = p - 2 by ring]
  have hpoint2 : ∀ t ∈ Set.Ioi z, |c t * t ^ (-q - 1)| ≤ M * t ^ (-q - 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hz ht
    have hpown : (0 : ℝ) ≤ t ^ (-q - 1) := Real.rpow_nonneg ht0.le _
    rw [abs_mul, abs_of_nonneg hpown]
    calc |c t| * t ^ (-q - 1)
        ≤ (M / t) * t ^ (-q - 1) := mul_le_mul_of_nonneg_right (hc t ht0) hpown
      _ = M * (t ^ (-1 : ℝ) * t ^ (-q - 1)) := by
            rw [div_eq_mul_inv, Real.rpow_neg_one]; ring
      _ = M * t ^ ((-1 : ℝ) + (-q - 1)) := by rw [Real.rpow_add ht0]
      _ = M * t ^ (-q - 2) := by rw [show (-1 : ℝ) + (-q - 1) = -q - 2 by ring]
  -- the two integral bounds
  have hA : |∫ t in (0 : ℝ)..z, c t * t ^ (p - 1)| ≤ M * (z ^ (p - 1) / (p - 1)) := by
    have h := abs_intervalIntegral_le (f := fun t => c t * t ^ (p - 1))
      (g := fun t => M * t ^ (p - 2)) hz.le hpoint1 hInt1
    rwa [intervalIntegral.integral_const_mul, rpowInt_zero_to_z_sub_two hp3' hz] at h
  have hB : |∫ t in Set.Ioi z, c t * t ^ (-q - 1)| ≤ M * (z ^ (-q - 1) / (q + 1)) := by
    have h := abs_setIntegral_Ioi_le (f := fun t => c t * t ^ (-q - 1))
      (g := fun t => M * t ^ (-q - 2)) hpoint2 hInt2
    rwa [MeasureTheory.integral_const_mul, rpowInt_Ioi_neg_two hq0 hz] at h
  -- the definitional unfolding
  have hunfold : Work.FTS.PhiStar.Radial.radGreen α m c z
      = 1 / (α * (4 * (m : ℝ) + 5)) *
        (z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))
          + z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1))) := by
    have e1 : -(2 * (m : ℝ) + 5) / α = -p := by rw [hp]; ring
    have e2 : (2 * (m : ℝ) + 5) / α - 1 = p - 1 := by rw [hp]
    have e3 : 2 * (m : ℝ) / α = q := by rw [hq]
    have e4 : -(2 * (m : ℝ) / α) - 1 = -q - 1 := by rw [hq]
    unfold Work.FTS.PhiStar.Radial.radGreen
    rw [e1, e2, e3, e4]
  have hznp : (0 : ℝ) ≤ z ^ (-p) := Real.rpow_nonneg hz.le _
  have hzq : (0 : ℝ) ≤ z ^ q := Real.rpow_nonneg hz.le _
  -- triangle inequality + the two estimates
  have htri : |z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))
        + z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1))|
      ≤ z ^ (-p) * (M * (z ^ (p - 1) / (p - 1)))
        + z ^ q * (M * (z ^ (-q - 1) / (q + 1))) := by
    have h1 : |z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))|
        ≤ z ^ (-p) * (M * (z ^ (p - 1) / (p - 1))) := by
      rw [abs_mul, abs_of_nonneg hznp]
      exact mul_le_mul_of_nonneg_left hA hznp
    have h2 : |z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1))|
        ≤ z ^ q * (M * (z ^ (-q - 1) / (q + 1))) := by
      rw [abs_mul, abs_of_nonneg hzq]
      exact mul_le_mul_of_nonneg_left hB hzq
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  -- `z`-power clearing
  have hzpow1 : z ^ (-p) * z ^ (p - 1) = z ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hz, show -p + (p - 1) = (-1 : ℝ) by ring]
  have hzpow2 : z ^ q * z ^ (-q - 1) = z ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hz, show q + (-q - 1) = (-1 : ℝ) by ring]
  have hstepH : z ^ (-p) * (M * (z ^ (p - 1) / (p - 1))) = (M / z) * (1 / (p - 1)) := by
    rw [show z ^ (-p) * (M * (z ^ (p - 1) / (p - 1)))
        = M * (z ^ (-p) * z ^ (p - 1)) / (p - 1) by ring, hzpow1, Real.rpow_neg_one]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hstepT : z ^ q * (M * (z ^ (-q - 1) / (q + 1))) = (M / z) * (1 / (q + 1)) := by
    rw [show z ^ q * (M * (z ^ (-q - 1) / (q + 1)))
        = M * (z ^ q * z ^ (-q - 1)) / (q + 1) by ring, hzpow2, Real.rpow_neg_one]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  -- the normalising factor times the two indicial reciprocals
  have hp1eq : α * (p - 1) = 2 * (m : ℝ) + 5 - α := by
    rw [hp]
    field_simp
  have hq1eq : α * (q + 1) = 2 * (m : ℝ) + α := by
    rw [hq]
    field_simp
  have hcoefH : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / (p - 1))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α)) := by
    rw [one_div_mul_one_div α (4 * (m : ℝ) + 5) (p - 1) (ne_of_gt hα) (by positivity)
      (ne_of_gt hp1)]
    rw [hp1eq]
  have hcoefT : 1 / (α * (4 * (m : ℝ) + 5)) * (1 / (q + 1))
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α)) := by
    rw [one_div_mul_one_div α (4 * (m : ℝ) + 5) (q + 1) (ne_of_gt hα) (by positivity)
      (by positivity)]
    rw [hq1eq]
  have hS : 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α))
      + 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α))
      ≤ 1 / ((4 * (m : ℝ) + 5) * (m : ℝ)) := by
    have h5 : (2 : ℝ) * (m : ℝ) ≤ 2 * (m : ℝ) + 5 - α := by linarith
    have h1 : 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α))
        ≤ 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have h2 : 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α))
        ≤ 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) * (m : ℝ) ≤ 2 * (m : ℝ) + α)
        (by positivity)
    have h3 : 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ)))
        + 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) = 1 / ((4 * (m : ℝ) + 5) * (m : ℝ)) := by
      field_simp
      ring
    linarith [h1, h2, h3.le]
  have hmge : ((m : ℝ) + 1) ^ 2 ≤ (4 * (m : ℝ) + 5) * (m : ℝ) := by nlinarith [hmR]
  have hMz : (0 : ℝ) ≤ M / z := div_nonneg hM hz.le
  have hdiv : M / z * (1 / ((4 * (m : ℝ) + 5) * (m : ℝ)))
      = M / (z * ((4 * (m : ℝ) + 5) * (m : ℝ))) := by
    field_simp
  have hXY : z * ((m : ℝ) + 1) ^ 2 ≤ z * ((4 * (m : ℝ) + 5) * (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hmge hz.le
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
      = |(1 / (α * (4 * (m : ℝ) + 5))) *
          (z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))
            + z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1)))| := by rw [hunfold]
    _ = 1 / (α * (4 * (m : ℝ) + 5)) *
          |z ^ (-p) * (∫ t in (0 : ℝ)..z, c t * t ^ (p - 1))
            + z ^ q * (∫ t in Set.Ioi z, c t * t ^ (-q - 1))| := by
          rw [abs_mul, abs_of_pos hKpos]
    _ ≤ 1 / (α * (4 * (m : ℝ) + 5)) *
          (z ^ (-p) * (M * (z ^ (p - 1) / (p - 1)))
            + z ^ q * (M * (z ^ (-q - 1) / (q + 1)))) :=
          mul_le_mul_of_nonneg_left htri hKpos.le
    _ = 1 / (α * (4 * (m : ℝ) + 5))
          * ((M / z) * (1 / (p - 1)) + (M / z) * (1 / (q + 1))) := by
          rw [hstepH, hstepT]
    _ = M / z * (1 / (α * (4 * (m : ℝ) + 5)) * (1 / (p - 1))
          + 1 / (α * (4 * (m : ℝ) + 5)) * (1 / (q + 1))) := by ring
    _ = M / z * (1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5 - α))
          + 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + α))) := by rw [hcoefH, hcoefT]
    _ ≤ M / z * (1 / ((4 * (m : ℝ) + 5) * (m : ℝ))) := mul_le_mul_of_nonneg_left hS hMz
    _ = M / (z * ((4 * (m : ℝ) + 5) * (m : ℝ))) := hdiv
    _ ≤ M / (z * ((m : ℝ) + 1) ^ 2) :=
          div_le_div_of_nonneg_left hM (by positivity) hXY

/-! ## The source bound for `𝒜φ` -/

/-- `|𝒜φ(α,t)| = |phiA α t| ≤ 24/t` for every `t > 0` and `0 < α ≤ 1`. -/
private lemma phiA_abs_le_inv (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 < t) :
    |Work.FTS.VocabO.phiA α t| ≤ 24 / t := by
  by_cases h1 : t ≤ 1
  · have h := Work.FTS.PhiStar.Series.Deleg.phiA_abs_le_small hα hα1 ht h1
    rw [le_div_iff₀ ht]
    nlinarith [h, ht, h1]
  · have h2 : 1 ≤ t := by linarith
    exact Work.FTS.PhiStar.Series.Deleg.phiA_abs_le_large hα hα1 h2

/-! ## The target -/

theorem radGreen_phiA_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (m : ℕ), 1 ≤ m →
      (∀ z : ℝ, 0 < z →
        |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
          ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ, 1 ≤ z →
        |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
          ≤ C / (z * ((m : ℝ) + 1))) := by
  refine ⟨24, by norm_num, ?_⟩
  intro α hα hα1 m hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hgen : ∀ z : ℝ, 0 < z →
      |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ 24 / (z * ((m : ℝ) + 1) ^ 2) := by
    intro z hz
    exact radGreen_le_of_inv_bound hα hα1 hm (M := 24) (by norm_num)
      (fun t ht => phiA_abs_le_inv α t hα hα1 ht) hz
  have hpow : ((m : ℝ) + 1) ^ (-(2 : ℝ)) = 1 / ((m : ℝ) + 1) ^ 2 := by
    have h2 : ((m : ℝ) + 1) ^ (2 : ℝ) = ((m : ℝ) + 1) ^ 2 := Real.rpow_natCast _ 2
    rw [one_div, ← h2, ← Real.rpow_neg (le_of_lt hm1)]
  constructor
  · intro z hz
    have h := hgen z hz
    rw [hpow]
    have hle : 1 / z ≤ 1 + 1 / z := by linarith
    have hcoef : (0 : ℝ) ≤ 24 / ((m : ℝ) + 1) ^ 2 := by positivity
    calc |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ 24 / (z * ((m : ℝ) + 1) ^ 2) := h
      _ = 24 / ((m : ℝ) + 1) ^ 2 * (1 / z) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, one_div, mul_inv]
            ring
      _ ≤ 24 / ((m : ℝ) + 1) ^ 2 * (1 + 1 / z) := mul_le_mul_of_nonneg_left hle hcoef
      _ = 24 * (1 + 1 / z) * (1 / ((m : ℝ) + 1) ^ 2) := by ring
  · intro z hz1
    have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
    have h := hgen z hz
    have hXY : z * ((m : ℝ) + 1) ≤ z * ((m : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [hm1]) hz.le
    calc |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ 24 / (z * ((m : ℝ) + 1) ^ 2) := h
      _ ≤ 24 / (z * ((m : ℝ) + 1)) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hXY

end Work.FTS.PhiStar.Series
