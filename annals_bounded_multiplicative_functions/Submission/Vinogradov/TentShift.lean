/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.LocalisedDecoupling
import Submission.Commons.Analysis.Convolution.itent_comparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shifting the plate tent by an element of the polar plate

GLYZ Lemma 3.8 (`Submission/Work/Vino/paper/1912.txt`, (3.11) and the line following it) uses
the fact that the bump `ϕ_{I'}` adapted to the polar plate `𝒰_{I'}^o` is essentially constant
on the translate ball `B_H(z, δ^{-b'l})`, because that ball is contained in a fixed multiple of
the polar plate.  In our framework the relevant sub-step is:

  `sup_{x ∈ B_H(z,r)} (|f_{I'}|^{p_k-p_l} ∗ ϕ_{I'})(x) ≲ (|f_{I'}|^{p_k-p_l} ∗ ϕ_{I'})(z)`,

and since `(|g| ∗ ϕ)(x) = ∫ ‖g y‖ ϕ(x-y) dy`, it is *enough* to know the pointwise comparison
`ϕ(w + h) ≤ C ϕ(w)` for every `h` in (a multiple of) the polar plate.  This module proves that
comparison, for the canonical gauge bump `platePhi` of a plate:

* `gauge_neg`, `gauge_add_le` — the sup-gauge on `E k` is a seminorm;
* `max_one_le_mul_max_one_of_abs_sub_le` — the elementary numerical step
  `|u - v| ≤ ρ, ρ ≥ 0 ⟹ max 1 u ≤ (1 + ρ) max 1 v`;
* `gauge_plateGaugeLin_le` — if `|⟪h, γ^{(i+1)}(c)⟫| ≤ ρ δ^{-(i+1)}` for all `i` then
  `gauge (plateGaugeLin k δ c h) ≤ ρ` (in particular every element of `polarPlate k δ c`
  has gauge `≤ 1`);
* `phiPlate_shift_le` — `phiPlate k hk δ c A Cφ (x + h) ≤ (1 + ρ)^A phiPlate k hk δ c A Cφ x`
  whenever `gauge (plateGaugeLin k δ c h) ≤ ρ` and `ρ ≥ 0`, `A > 0`, `Cφ ≥ 0`;
* `platePhi_shift_le` — the same for the canonical `ℝ≥0∞`-valued tent of a plate.

This is the "sup comparison" ingredient of Lemma 3.8; the companion direction
(`phiPlate_shift_ge`) is the same statement with `x` and `x + h` exchanged.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Submission.Vinogradov

/-! ## 1. The sup-gauge is a seminorm -/

lemma gauge_neg (k : ℕ) (hk : 1 ≤ k) (u : E k) : gauge k hk (-u) = gauge k hk u := by
  rw [gauge, gauge]
  refine Finset.sup'_congr _ rfl (fun i _ => ?_)
  simp

lemma gauge_add_le (k : ℕ) (hk : 1 ≤ k) (u v : E k) :
    gauge k hk (u + v) ≤ gauge k hk u + gauge k hk v := by
  rw [gauge]
  refine Finset.sup'_le _ _ (fun i _ => ?_)
  have h1 : |(u + v).ofLp i| = |u.ofLp i + v.ofLp i| := by simp
  rw [h1]
  calc |u.ofLp i + v.ofLp i| ≤ |u.ofLp i| + |v.ofLp i| := abs_add_le _ _
    _ ≤ gauge k hk u + gauge k hk v := add_le_add (le_gauge k hk u i) (le_gauge k hk v i)

lemma gauge_sub_le (k : ℕ) (hk : 1 ≤ k) (u v : E k) :
    gauge k hk (u - v) ≤ gauge k hk u + gauge k hk v := by
  rw [sub_eq_add_neg]
  exact le_trans (gauge_add_le k hk u (-v)) (by rw [gauge_neg])

/-! ## 2. The elementary numerical steps -/

/-- If `u` and `v` are within `ρ ≥ 0` of each other then `max 1 u ≤ (1 + ρ) max 1 v`. -/
lemma max_one_le_mul_max_one_of_abs_sub_le {ρ u v : ℝ} (hρ : 0 ≤ ρ) (h : |u - v| ≤ ρ) :
    max 1 u ≤ (1 + ρ) * max 1 v := by
  have huv : u ≤ v + ρ := by
    have := (abs_le.mp h).2; linarith
  rcases le_total 1 v with hv | hv
  · have h1 : v + ρ ≤ (1 + ρ) * v := by nlinarith
    have h2 : max 1 (v + ρ) = v + ρ := max_eq_right (by linarith)
    calc max 1 u ≤ max 1 (v + ρ) := max_le_max le_rfl huv
      _ = v + ρ := h2
      _ ≤ (1 + ρ) * v := h1
      _ ≤ (1 + ρ) * max 1 v :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  · have h3 : u ≤ 1 + ρ := by linarith
    have h4 : max 1 u ≤ 1 + ρ := max_le (by linarith) h3
    have h5 : max 1 v = 1 := max_eq_left hv
    rwa [h5, mul_one]

/-- Numerical conversion: `a ≤ (1 + ρ) b`, `a, b > 0`, `A > 0`, `ρ ≥ 0` give
`b ^ (-A) ≤ (1 + ρ) ^ A * a ^ (-A)`. -/
lemma rpow_neg_le_mul_rpow_neg {A ρ a b : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ) (ha : 0 < a)
    (hb : 0 < b) (h : a ≤ (1 + ρ) * b) : b ^ (-A) ≤ (1 + ρ) ^ A * a ^ (-A) := by
  have h1 : (1 + ρ) > 0 := by linarith
  have haA : 0 < a ^ A := Real.rpow_pos_of_pos ha A
  have hbA : 0 < b ^ A := Real.rpow_pos_of_pos hb A
  have hba : a ^ A ≤ ((1 + ρ) * b) ^ A := Real.rpow_le_rpow (le_of_lt ha) h (le_of_lt hA)
  rw [Real.mul_rpow (le_of_lt h1) (le_of_lt hb)] at hba
  rw [Real.rpow_neg (le_of_lt hb), Real.rpow_neg (le_of_lt ha), inv_eq_one_div,
    ← div_eq_mul_inv]
  rw [div_le_div_iff₀ hbA haA]
  simpa using hba

/-! ## 3. The gauge of an element of the polar plate -/

/-- If `|⟪h, γ^{(i+1)}(c)⟫| ≤ ρ δ^{-(i+1)}` for all `i` then `h` has gauge at most `ρ` in the
gauge coordinates of the polar plate of `plate k δ c`. -/
lemma gauge_plateGaugeLin_le {k : ℕ} (hk : 1 ≤ k) {δ c ρ : ℝ} (hδ : 0 < δ) {h : E k}
    (hh : ∀ i : Fin k, |⟪h, gammaDeriv k (i.val + 1) c⟫| ≤ ρ * (δ ^ (i.val + 1))⁻¹) :
    gauge k hk (plateGaugeLin k δ c h) ≤ ρ := by
  rw [gauge]
  refine Finset.sup'_le _ _ (fun i _ => ?_)
  rw [plateGaugeLin_apply]
  have h1 : |δ ^ (i.val + 1) * ⟪h, gammaDeriv k (i.val + 1) c⟫|
      = δ ^ (i.val + 1) * |⟪h, gammaDeriv k (i.val + 1) c⟫| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hδ.le _)]
  rw [h1]
  calc δ ^ (i.val + 1) * |⟪h, gammaDeriv k (i.val + 1) c⟫|
      ≤ δ ^ (i.val + 1) * (ρ * (δ ^ (i.val + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left (hh i) (pow_nonneg hδ.le _)
    _ = ρ := by
        have : δ ^ (i.val + 1) * (ρ * (δ ^ (i.val + 1))⁻¹)
            = ρ * (δ ^ (i.val + 1) * (δ ^ (i.val + 1))⁻¹) := by ring
        rw [this, mul_inv_cancel₀ (ne_of_gt (pow_pos hδ _)), mul_one]

/-- Every element of the polar plate has gauge at most `1` in the gauge coordinates. -/
lemma gauge_plateGaugeLin_le_one {k : ℕ} (hk : 1 ≤ k) {δ c : ℝ} (hδ : 0 < δ) {h : E k}
    (hh : h ∈ polarPlate k δ c) : gauge k hk (plateGaugeLin k δ c h) ≤ 1 := by
  refine gauge_plateGaugeLin_le hk hδ (ρ := 1) (fun i => ?_)
  rw [one_mul]
  exact (mem_polarPlate_iff k δ c h).mp hh i

/-! ## 4. The shift comparison for the plate tent -/

/-- **The plate tent is comparable under shifts by `ρ · polarPlate`.** -/
lemma phiPlate_shift_le (k : ℕ) (hk : 1 ≤ k) (δ c A Cφ : ℝ) {ρ : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ)
    (hCφ : 0 ≤ Cφ) {x h : E k} (hh : gauge k hk (plateGaugeLin k δ c h) ≤ ρ) :
    phiPlate k hk δ c A Cφ (x + h) ≤ (1 + ρ) ^ A * phiPlate k hk δ c A Cφ x := by
  rw [phiPlate, phiPlate]
  set B := plateGaugeLin k δ c with hB
  set m : ℝ := max 1 (gauge k hk (B x)) with hm
  set m' : ℝ := max 1 (gauge k hk (B (x + h))) with hm'
  have hmpos : 0 < m := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hm'pos : 0 < m' := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hBadd : B (x + h) = B x + B h := map_add B x h
  have hgb : gauge k hk (B (x + h)) ≤ gauge k hk (B x) + ρ := by
    rw [hBadd]
    exact le_trans (gauge_add_le k hk _ _) (add_le_add le_rfl hh)
  have hgle : gauge k hk (B x) ≤ gauge k hk (B (x + h)) + ρ := by
    have h1 : B x = B (x + h) + (-(B h)) := by rw [hBadd]; abel
    rw [h1]
    refine le_trans (gauge_add_le k hk _ _) ?_
    rw [gauge_neg]
    exact add_le_add le_rfl hh
  have hsub : |gauge k hk (B x) - gauge k hk (B (x + h))| ≤ ρ :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hmle : m ≤ (1 + ρ) * m' := by
    rw [hm, hm']
    exact max_one_le_mul_max_one_of_abs_sub_le hρ hsub
  have hkey : m' ^ (-A) ≤ (1 + ρ) ^ A * m ^ (-A) :=
    rpow_neg_le_mul_rpow_neg hA hρ hmpos hm'pos hmle
  rw [hm', hm] at hkey
  calc Cφ * |LinearMap.det B| * m' ^ (-A)
      ≤ Cφ * |LinearMap.det B| * ((1 + ρ) ^ A * m ^ (-A)) :=
        mul_le_mul_of_nonneg_left hkey (mul_nonneg hCφ (abs_nonneg _))
    _ = (1 + ρ) ^ A * (Cφ * |LinearMap.det B| * m ^ (-A)) := by ring

/-- The reverse shift comparison (exchange `x` and `x + h`). -/
lemma phiPlate_shift_ge (k : ℕ) (hk : 1 ≤ k) (δ c A Cφ : ℝ) {ρ : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ)
    (hCφ : 0 ≤ Cφ) {x h : E k} (hh : gauge k hk (plateGaugeLin k δ c h) ≤ ρ) :
    phiPlate k hk δ c A Cφ x ≤ (1 + ρ) ^ A * phiPlate k hk δ c A Cφ (x + h) := by
  have hh' : gauge k hk (plateGaugeLin k δ c (-h)) ≤ ρ := by rw [map_neg, gauge_neg]; exact hh
  have h := phiPlate_shift_le k hk δ c A Cφ hA hρ hCφ (x := x + h) (h := -h) hh'
  simpa only [add_assoc, add_neg_cancel, add_zero] using h

/-- **The canonical tent of a plate is comparable under shifts by the polar plate.** -/
lemma platePhi_shift_le (k : ℕ) (hk : 1 ≤ k) (δ c : ℝ) {x h : E k}
    (hh : gauge k hk (plateGaugeLin k δ c h) ≤ 1) :
    platePhi k hk δ c (x + h)
      ≤ ENNReal.ofReal (2 ^ gaugeExp k) * platePhi k hk δ c x := by
  have h1 : platePhi k hk δ c (x + h)
      = ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) (x + h)) := rfl
  have h2 : platePhi k hk δ c x
      = ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x) := rfl
  rw [h1, h2]
  have hApos : (0:ℝ) < gaugeExp k := lt_of_le_of_lt (by positivity) (gaugeExp_gt hk)
  have hle := phiPlate_shift_le k hk δ c (gaugeExp k) (gaugeAmp k hk) (ρ := 1)
    hApos zero_le_one (gaugeAmp_pos k hk).le (x := x) (h := h) hh
  have hofR : ENNReal.ofReal ((1 + 1 : ℝ) ^ gaugeExp k) = ENNReal.ofReal (2 ^ gaugeExp k) := by
    norm_num
  calc ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) (x + h))
      ≤ ENNReal.ofReal ((1 + 1) ^ gaugeExp k
          * phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((1 + 1) ^ gaugeExp k)
          * ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal (2 ^ gaugeExp k)
          * ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x) := by rw [hofR]

end Submission.Vinogradov
