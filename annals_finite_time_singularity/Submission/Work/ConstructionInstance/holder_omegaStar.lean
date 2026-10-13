/-
# `Holder ⟨β, _⟩ (omegaStar β)` for `0 < β ≤ 1`

The model field `omegaStar β x = (Γ(θ x) · F_*(ρ(x)^{3β})) • e_θ(x)` of the construction
(`Submission/Work/ConstructionInstance/Defs.lean`) is `β`-Hölder on `ℝ³`.

## The argument

`AuxOmegaStar.lean` introduces the *non-negative amplitude*
`A0 β x = 2 |x₂|^β r(x)^{2β} / (1 + ρ(x)^{3β})²` (`r` the distance to the axis, `ρ = ‖x‖`) and
the sign factor `cSign β (x₂)` (`1` for `x₂ ≥ 0`, `cos (βπ)` for `x₂ < 0`) produced by
`Real.rpow` at the negative base `sin θ cos²θ`; `Aom β x = cSign β (x₂) · A0 β x` is the true
amplitude, so that (`omegaStar_eq_Aom`)

  `omegaStar β x = Aom β x • e_θ(x)`.

Decomposing `Aom β x • e_θ x - Aom β y • e_θ y` as `Aom β x • (e_θ x - e_θ y)
+ (Aom β x - Aom β y) • e_θ y` the estimate reduces to the three inputs

* `A0_holder` : `A0` is `β`-Hölder (with `|cSign| ≤ 1` this handles the amplitude difference);
* `eTheta_dist_le` : `‖e_θ x - e_θ y‖ ≤ √2 ‖x - y‖ / min (r x) (r y)` (the geometric input);
* the vanishing bounds `A0 β x ≤ 2 r(x)^{2β}` and `A0 β x ≤ 2 r(x)^{β}` of `AuxOmegaStar`,
  which combine with the geometric bound in the two regimes `‖x-y‖ ≤ r x / 2` (where the
  `1/r`-Lipschitz behaviour of `e_θ` is compensated by the vanishing of `A0`) and
  `‖x-y‖ > r x / 2` (where the plain bound `‖e_θ‖ ≤ 1` and `A0 ≤ 1/2` are used).

Outside `‖x - y‖ ≤ 1` the two terms are simply bounded by `A0 x + A0 y ≤ 1 ≤ ‖x - y‖^β`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.AuxOmegaStar
import Submission.Work.ConstructionInstance.eTheta_dist_le
import Submission.Work.ConstructionInstance.omegaStar_eq_Aom
import Submission.Work.ConstructionInstance.A0_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## Elementary geometric and `rpow` estimates -/

/-- `|x₂ - y₂| ≤ ‖x - y‖`. -/
lemma abs_ax_sub_le (x y : R3) : |x 2 - y 2| ≤ ‖x - y‖ := by
  have h1 : ‖x - y‖ ^ 2 = (x 2 - y 2) ^ 2 + ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, Work.Cyl.inner_eq]
    simp only [PiLp.sub_apply]
    ring
  nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1), norm_nonneg (x - y),
    sq_abs (x 2 - y 2)]

/-- `d r^{β-1} ≤ 2^{β-1} d^β` when `2d ≤ r`, `β ∈ (0,1]`, `d > 0`. -/
lemma mul_rpow_sub_le {β d r : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hd : 0 < d) (hr : 2 * d ≤ r) :
    d * r ^ (β - 1) ≤ 2 ^ (β - 1) * d ^ β := by
  have h1 : r ^ (β - 1) ≤ (2 * d) ^ (β - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
  have h2 : (2 * d) ^ (β - 1) = 2 ^ (β - 1) * d ^ (β - 1) :=
    Real.mul_rpow (by norm_num) hd.le
  have h3 : d * d ^ (β - 1) = d ^ β := by
    have h := Real.rpow_add hd (β - 1) 1
    rw [show β - 1 + 1 = β by ring, Real.rpow_one] at h
    rw [h, mul_comm]
  calc d * r ^ (β - 1) ≤ d * (2 * d) ^ (β - 1) := mul_le_mul_of_nonneg_left h1 hd.le
    _ = d * (2 ^ (β - 1) * d ^ (β - 1)) := by rw [h2]
    _ = 2 ^ (β - 1) * (d * d ^ (β - 1)) := by ring
    _ = 2 ^ (β - 1) * d ^ β := by rw [h3]

/-- **The amplitude-weighted angular difference is `β`-Hölder** (for `‖x - y‖ ≤ 1`):
`A0 β x · ‖e_θ x - e_θ y‖ ≤ 2^{2β+2} ‖x - y‖^β`.  The case distinction is
`‖x - y‖ ≤ r x / 2` (where `eTheta_dist_le` gives `√2 d / min(r x, r y) ≤ 2√2 d / r x` and
`A0 β x ≤ 2 r x^β`) against `‖x - y‖ > r x / 2` (where `‖e_θ‖ ≤ 1` and `A0 β x ≤ 2 r x^{2β}`). -/
lemma A0_mul_eTheta_sub_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {x y : R3}
    (hd : ‖x - y‖ ≤ 1) :
    A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ ≤ (2 : ℝ) ^ (2 * β + 2) * ‖x - y‖ ^ β := by
  by_cases hxy : x = y
  · subst hxy
    have h0 : ‖x - x‖ ^ β = 0 := by
      rw [sub_self, norm_zero, Real.zero_rpow (ne_of_gt hβ)]
    rw [sub_self, norm_zero, mul_zero, h0, mul_zero]
  rcases eq_or_ne (Work.Cyl.radial x) 0 with hrx0 | hrx0
  · rw [A0_eq_zero_of_radial_eq_zero β hβ hrx0, zero_mul]; positivity
  · have hrxp : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hrx0)
    have hdn : 0 < ‖x - y‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr hxy
    by_cases hd2 : ‖x - y‖ ≤ Work.Cyl.radial x / 2
    · -- sub-case 1: `d ≤ r x / 2`
      have hry : 0 < Work.Cyl.radial y := by
        have h := (abs_le.mp (radial_dist_le x y)).2
        linarith
      have hmin : Work.Cyl.radial x / 2 ≤ min (Work.Cyl.radial x) (Work.Cyl.radial y) := by
        have h := (abs_le.mp (radial_dist_le x y)).2
        exact le_min (by linarith) (by linarith)
      have hE1 : ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
          ≤ 2 * Real.sqrt 2 * ‖x - y‖ / Work.Cyl.radial x := by
        have h1 := eTheta_dist_le x y hrxp hry
        have h2 : Real.sqrt 2 * ‖x - y‖ / min (Work.Cyl.radial x) (Work.Cyl.radial y)
            ≤ Real.sqrt 2 * ‖x - y‖ / (Work.Cyl.radial x / 2) := by
          rw [div_le_div_iff_of_pos_left (by positivity) (lt_min hrxp hry) (by positivity)]
          exact hmin
        have h2' : Real.sqrt 2 * ‖x - y‖ / (Work.Cyl.radial x / 2)
            = 2 * Real.sqrt 2 * ‖x - y‖ / Work.Cyl.radial x := by
          field_simp
        linarith [h2.trans_eq h2']
      have hA : A0 β x ≤ 2 * (Work.Cyl.radial x) ^ β := A0_le_rpow β hβ x
      have heq : (2 * (Work.Cyl.radial x) ^ β) * (2 * Real.sqrt 2 * ‖x - y‖ / Work.Cyl.radial x)
          = 4 * Real.sqrt 2 * (‖x - y‖ * (Work.Cyl.radial x) ^ (β - 1)) := by
        rw [Real.rpow_sub hrxp, Real.rpow_one]
        field_simp
        ring
      have hr2 : 2 * ‖x - y‖ ≤ Work.Cyl.radial x := by linarith
      have hstep := mul_rpow_sub_le hβ hβ1 hdn hr2
      have h5 : 4 * Real.sqrt 2 * (2 : ℝ) ^ (β - 1) ≤ (2 : ℝ) ^ (2 * β + 2) := by
        have h3 : 4 * Real.sqrt 2 ≤ (8 : ℝ) := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        have h4 : 8 * (2 : ℝ) ^ (β - 1) = (2 : ℝ) ^ (β + 2) := by
          rw [show β + 2 = 3 + (β - 1) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          norm_num
        have h6 : (2 : ℝ) ^ (β + 2) ≤ (2 : ℝ) ^ (2 * β + 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (β - 1)]
      calc A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
          ≤ (2 * (Work.Cyl.radial x) ^ β) * (2 * Real.sqrt 2 * ‖x - y‖ / Work.Cyl.radial x) :=
            mul_le_mul hA hE1 (norm_nonneg _) (by positivity)
        _ = 4 * Real.sqrt 2 * (‖x - y‖ * (Work.Cyl.radial x) ^ (β - 1)) := heq
        _ ≤ 4 * Real.sqrt 2 * ((2 : ℝ) ^ (β - 1) * ‖x - y‖ ^ β) := by
            have hs := Real.sqrt_nonneg 2
            have hdβ := Real.rpow_nonneg hdn.le β
            nlinarith [hstep]
        _ ≤ (2 : ℝ) ^ (2 * β + 2) * ‖x - y‖ ^ β := by
            have hdβ := Real.rpow_nonneg hdn.le β
            nlinarith [h5]
    · -- sub-case 2: `d > r x / 2`
      have hE2 : ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ ≤ 2 := eTheta_norm_sub_le_two x y
      have hA : A0 β x ≤ 2 * (Work.Cyl.radial x) ^ (2 * β) := A0_le_rpow2 β hβ x
      have hp : A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
          ≤ 4 * (Work.Cyl.radial x) ^ (2 * β) := by
        have h0 := A0_nonneg β x
        have h1 : A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ ≤ A0 β x * 2 :=
          mul_le_mul_of_nonneg_left hE2 h0
        nlinarith [hA, h1]
      have hr2 : Work.Cyl.radial x ≤ 2 * ‖x - y‖ := by
        have := lt_of_not_ge hd2
        linarith
      have hs : (Work.Cyl.radial x) ^ (2 * β) ≤ (2 * ‖x - y‖) ^ (2 * β) :=
        Real.rpow_le_rpow (Work.Cyl.radial_nonneg x) hr2 (by linarith)
      have hs2 : (2 * ‖x - y‖) ^ (2 * β) = (2 : ℝ) ^ (2 * β) * ‖x - y‖ ^ (2 * β) :=
        Real.mul_rpow (by norm_num) (norm_nonneg _)
      have hdβ : ‖x - y‖ ^ (2 * β) ≤ ‖x - y‖ ^ β :=
        Real.rpow_le_rpow_of_exponent_ge hdn hd (by linarith)
      have hconst : 4 * (2 : ℝ) ^ (2 * β) = (2 : ℝ) ^ (2 * β + 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) (2 * β) 2]
        norm_num
        ring
      calc A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
          ≤ 4 * (Work.Cyl.radial x) ^ (2 * β) := hp
        _ ≤ 4 * ((2 : ℝ) ^ (2 * β) * ‖x - y‖ ^ (2 * β)) := by
            have h2β := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * β)
            nlinarith [hs, hs2]
        _ ≤ 4 * ((2 : ℝ) ^ (2 * β) * ‖x - y‖ ^ β) := by
            have h2β := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * β)
            have hb := Real.rpow_nonneg hdn.le β
            nlinarith [hdβ]
        _ = (4 * (2 : ℝ) ^ (2 * β)) * ‖x - y‖ ^ β := by ring
        _ = (2 : ℝ) ^ (2 * β + 2) * ‖x - y‖ ^ β := by rw [hconst]

/-- `|Aom β x - Aom β y| ≤ (C + 4) ‖x - y‖^β` whenever `A0` is `β`-Hölder with constant `C`.
Because `|cSign| ≤ 1` and `cSign` takes one value on `x₂ ≥ 0` and another on `x₂ < 0`, the only
extra term appears when the two points straddle the plane `x₂ = 0`; then `|x₂|, |y₂| ≤ ‖x-y‖`
and `A0 β y ≤ 2 |y₂|^β` closes the estimate with `4 ‖x-y‖^β`. -/
lemma Aom_sub_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {C : NNReal}
    (hC : ∀ x y : R3, |A0 β x - A0 β y| ≤ (C : ℝ) * ‖x - y‖ ^ β) (x y : R3) :
    |Aom β x - Aom β y| ≤ ((C : ℝ) + 4) * ‖x - y‖ ^ β := by
  have hcx : |cSign β (x 2)| ≤ 1 := abs_cSign_le_one β (x 2)
  have hcy : |cSign β (y 2)| ≤ 1 := abs_cSign_le_one β (y 2)
  have hd : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
  have hsplit : cSign β (x 2) * A0 β x - cSign β (y 2) * A0 β y
      = cSign β (x 2) * (A0 β x - A0 β y) + (cSign β (x 2) - cSign β (y 2)) * A0 β y := by
    ring
  rw [Aom, Aom, hsplit]
  by_cases hsign : cSign β (x 2) = cSign β (y 2)
  · rw [sub_eq_zero.mpr hsign, zero_mul, add_zero]
    calc |cSign β (x 2) * (A0 β x - A0 β y)|
        = |cSign β (x 2)| * |A0 β x - A0 β y| := abs_mul _ _
      _ ≤ 1 * ((C : ℝ) * ‖x - y‖ ^ β) :=
          mul_le_mul hcx (hC x y) (abs_nonneg _) (by norm_num)
      _ ≤ ((C : ℝ) + 4) * ‖x - y‖ ^ β := by
          have hCc : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
          nlinarith
  · have h2 : |A0 β y| ≤ 2 * ‖x - y‖ ^ β := by
      have hA := A0_le_ax β hβ y
      have hz : |y 2| ≤ ‖x - y‖ := by
        have hxy2 : |x 2 - y 2| ≤ ‖x - y‖ := abs_ax_sub_le x y
        by_cases hy2 : 0 ≤ y 2
        · have hx : x 2 < 0 := by
            by_contra hx
            exact hsign (by rw [cSign, if_pos (not_lt.mp hx), cSign, if_pos hy2])
          calc |y 2| = y 2 := abs_of_nonneg hy2
            _ ≤ y 2 - x 2 := by linarith
            _ = -(x 2 - y 2) := by ring
            _ ≤ |x 2 - y 2| := neg_le_abs _
            _ ≤ ‖x - y‖ := hxy2
        · have hy : y 2 < 0 := lt_of_not_ge hy2
          have hx : 0 ≤ x 2 := by
            by_contra hx
            exact hsign (by rw [cSign, if_neg hx, cSign, if_neg hy2])
          calc |y 2| = -y 2 := abs_of_neg hy
            _ ≤ x 2 - y 2 := by linarith
            _ ≤ |x 2 - y 2| := le_abs_self _
            _ ≤ ‖x - y‖ := hxy2
      calc |A0 β y| = A0 β y := abs_of_nonneg (A0_nonneg β y)
        _ ≤ 2 * |y 2| ^ β := hA
        _ ≤ 2 * ‖x - y‖ ^ β := by
            have h := Real.rpow_le_rpow (abs_nonneg _) hz hβ.le
            linarith
    have h4 : |cSign β (x 2) - cSign β (y 2)| ≤ 2 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [neg_abs_le (cSign β (x 2)), le_abs_self (cSign β (x 2)),
        neg_abs_le (cSign β (y 2)), le_abs_self (cSign β (y 2))]
    have h5 : |cSign β (x 2)| * |A0 β x - A0 β y| ≤ (C : ℝ) * ‖x - y‖ ^ β := by
      calc |cSign β (x 2)| * |A0 β x - A0 β y| ≤ 1 * ((C : ℝ) * ‖x - y‖ ^ β) :=
            mul_le_mul hcx (hC x y) (abs_nonneg _) (by norm_num)
        _ = (C : ℝ) * ‖x - y‖ ^ β := one_mul _
    have h6 : |cSign β (x 2) - cSign β (y 2)| * |A0 β y| ≤ 2 * (2 * ‖x - y‖ ^ β) :=
      mul_le_mul h4 h2 (abs_nonneg _) (by norm_num)
    have hab : |cSign β (x 2) * (A0 β x - A0 β y) + (cSign β (x 2) - cSign β (y 2)) * A0 β y|
        ≤ |cSign β (x 2)| * |A0 β x - A0 β y|
          + |cSign β (x 2) - cSign β (y 2)| * |A0 β y| := by
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_) <;> rw [abs_mul]
    linarith [hab, h5, h6]

/-! ## The Hölder estimate -/

theorem holder_omegaStar {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Holder ⟨β, hβ.le⟩ (Work.ConstructionInstance.omegaStar β) := by
  obtain ⟨C, hC⟩ := A0_holder hβ hβ1
  set K : ℝ := (C : ℝ) + (2 : ℝ) ^ (2 * β + 2) + 4 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨NNReal.mk K hK0, ?_⟩
  refine holder_of_norm_le (βr := β) rfl hβ.le ?_
  intro x y
  change ‖Work.ConstructionInstance.omegaStar β x - Work.ConstructionInstance.omegaStar β y‖
    ≤ K * ‖x - y‖ ^ β
  have hdβ : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
  by_cases hd1 : ‖x - y‖ ≤ 1
  · -- near case: the two `β`-Hölder pieces
    rw [omegaStar_eq_Aom β hβ x, omegaStar_eq_Aom β hβ y]
    have hdec : Aom β x • Work.Cyl.eTheta x - Aom β y • Work.Cyl.eTheta y
        = Aom β x • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)
          + (Aom β x - Aom β y) • Work.Cyl.eTheta y := by
      rw [smul_sub, sub_smul]; abel
    rw [hdec]
    have h1 : A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
        ≤ (2 : ℝ) ^ (2 * β + 2) * ‖x - y‖ ^ β := A0_mul_eTheta_sub_le hβ hβ1 hd1
    have h2 : |Aom β x - Aom β y| ≤ ((C : ℝ) + 4) * ‖x - y‖ ^ β := Aom_sub_le hβ hβ1 hC x y
    have ha : ‖Aom β x • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
        ≤ A0 β x * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_Aom_le_A0 β x) (norm_nonneg _)
    have hb : ‖(Aom β x - Aom β y) • Work.Cyl.eTheta y‖ ≤ |Aom β x - Aom β y| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |Aom β x - Aom β y| * ‖Work.Cyl.eTheta y‖ ≤ |Aom β x - Aom β y| * 1 :=
            mul_le_mul_of_nonneg_left (norm_eTheta_le_one y) (abs_nonneg _)
        _ = |Aom β x - Aom β y| := mul_one _
    refine le_trans (norm_add_le _ _) ?_
    rw [hK]
    nlinarith [ha, hb, h1, h2, hdβ]
  · -- far case: both amplitudes are below `1/2`
    have hd0 : 1 ≤ ‖x - y‖ := le_of_lt (lt_of_not_ge hd1)
    have hpow : (1 : ℝ) ≤ ‖x - y‖ ^ β := Real.one_le_rpow hd0 (le_of_lt hβ)
    have hax : ‖Work.ConstructionInstance.omegaStar β x‖ ≤ A0 β x := by
      rw [omegaStar_eq_Aom β hβ x, norm_smul, Real.norm_eq_abs]
      calc |Aom β x| * ‖Work.Cyl.eTheta x‖ ≤ |Aom β x| * 1 :=
            mul_le_mul_of_nonneg_left (norm_eTheta_le_one x) (abs_nonneg _)
        _ = |Aom β x| := mul_one _
        _ ≤ A0 β x := abs_Aom_le_A0 β x
    have hay : ‖Work.ConstructionInstance.omegaStar β y‖ ≤ A0 β y := by
      rw [omegaStar_eq_Aom β hβ y, norm_smul, Real.norm_eq_abs]
      calc |Aom β y| * ‖Work.Cyl.eTheta y‖ ≤ |Aom β y| * 1 :=
            mul_le_mul_of_nonneg_left (norm_eTheta_le_one y) (abs_nonneg _)
        _ = |Aom β y| := mul_one _
        _ ≤ A0 β y := abs_Aom_le_A0 β y
    have hhalff : A0 β x + A0 β y ≤ 1 := by
      have h1 := A0_le_half β hβ x
      have h2 := A0_le_half β hβ y
      linarith
    rw [hK]
    have h1 := C.coe_nonneg
    have h2 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * β + 2)
    calc ‖Work.ConstructionInstance.omegaStar β x - Work.ConstructionInstance.omegaStar β y‖
        ≤ A0 β x + A0 β y := le_trans (norm_sub_le _ _) (add_le_add hax hay)
      _ ≤ 1 := hhalff
      _ ≤ ‖x - y‖ ^ β := hpow
      _ ≤ ((C : ℝ) + (2 : ℝ) ^ (2 * β + 2) + 4) * ‖x - y‖ ^ β := by
          nlinarith [hdβ, hpow, h2]

end Work.ConstructionInstance
