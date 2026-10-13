import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

noncomputable section

set_option autoImplicit false

/-! ## The quotient `Ψ = Φ / sin 2θ` and the two slice functionals attached to it -/

/-- The quotient `Ψ = Φ / sin 2θ`.  (The totalised division patches `{sin 2θ = 0}` with
the value `0`, which is harmless everywhere below.) -/
def psi (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Φ z θ / Work.Construction.s2 θ

/-- The `(i,j) = (0,0)` slot `∫_θ Ψ² w² sin(2θ)^{-η}` of the `ℋ^6`-integrand of `Ψ`. -/
def slot0 (Φ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    (psi Φ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The `θ`-slice of the `ℋ^6`-integrand of `Ψ = psi Φ`. -/
def sliceHk (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (psi Φ) z θ

@[simp] lemma psi_apply (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    psi Φ z θ = Φ z θ / Work.Construction.s2 θ := rfl

@[simp] lemma slot0_apply (Φ : ℝ → ℝ → ℝ) (z : ℝ) :
    slot0 Φ z = ∫ θ in Work.Spaces.Iθ,
      (psi Φ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl

@[simp] lemma sliceHk_apply (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) :
    sliceHk α Φ z = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (psi Φ) z θ := rfl

/-! ## Elementary facts about `sin 2θ`, `η` and the weight `w` -/

lemma eta_pos' : (0 : ℝ) < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num

lemma two_add_eta_pos : (0 : ℝ) < 2 + Work.Spaces.eta := by
  have := eta_pos'; linarith

/-- `sin 2θ ≥ 0` on `Iθ = [0,π/2]`. -/
lemma sin_two_nonneg_of_mem_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin 2θ > 0` on the open interval `(0,π/2)`. -/
lemma sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) := by
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-- `z > 0` lies in `Iz = [0,∞)`. -/
lemma mem_Iz_of_pos {z : ℝ} (hz : 0 < z) : z ∈ Work.Spaces.Iz := le_of_lt hz

/-- `z ∈ (0,∞)` lies in `Iz = [0,∞)`. -/
lemma mem_Iz_of_mem_Ioi {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) : z ∈ Work.Spaces.Iz :=
  le_of_lt (show (0 : ℝ) < z from hz)

/-- `w(z) ≥ 1` for `z > 0`. -/
lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  rw [Work.Spaces.w, le_div_iff₀ hz2]
  nlinarith

lemma one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have h := one_le_w hz
  nlinarith [h]

lemma w_sq_pos {z : ℝ} (hz : 0 < z) : 0 < (Work.Spaces.w z) ^ 2 :=
  lt_of_lt_of_le one_pos (one_le_w_sq hz)

/-- The weight identity `w(z)² = (1+z)⁴/z⁴`. -/
lemma w_sq_eq {z : ℝ} : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow, ← pow_mul, ← pow_mul]

/-- `z^{-4} = (z⁴)^{-1}` for `z ≥ 0`. -/
lemma rpow_neg_four {z : ℝ} (hz : 0 ≤ z) : z ^ (-4 : ℝ) = (z ^ 4)⁻¹ := by
  have hcast : z ^ (4 : ℕ) = z ^ (4 : ℝ) :=
    (Real.rpow_natCast (x := z) (n := 4)).symm
  rw [hcast, ← Real.rpow_neg hz (4 : ℝ)]

lemma sliceEnergy_nonneg (Φ : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sliceEnergy Φ z := by
  rw [sliceEnergy]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
  exact mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)

lemma slot0_nonneg (Φ : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ slot0 Φ z :=
  integral_nonneg fun θ => sq_nonneg _

lemma sliceHk_nonneg {α : ℝ} (Φ : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sliceHk α Φ z :=
  integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 (psi Φ) z θ

/-- `√t ≤ t + 1` for `t ≥ 0`. -/
lemma sqrt_le_add_one {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ≤ t + 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  nlinarith [ht]

/-! ## The two pointwise identities at the heart of the reduction -/

/-- `Φ² · sin(2θ)^{-(2+η)} = Ψ² · sin(2θ)^{-η}`; the identity holds at the endpoints too,
where both sides vanish. -/
lemma Phi_sq_rootWeight_eq {Φ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Φ z θ ^ 2 * rootWeight θ
      = (psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ' hθ
  rw [rootWeight, psi, Work.Construction.s2]
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (show (-(2 + Work.Spaces.eta)) ≠ 0 by
        have := two_add_eta_pos; linarith),
      Real.zero_rpow (show (-Work.Spaces.eta) ≠ 0 by
        have := eta_pos'; linarith)]
    ring
  · have hcast : (Real.sin (2 * θ)) ^ (2 : ℕ) = (Real.sin (2 * θ)) ^ (2 : ℝ) :=
      (Real.rpow_natCast (x := Real.sin (2 * θ)) (n := 2)).symm
    rw [show (-(2 + Work.Spaces.eta)) = (-2 : ℝ) + (-Work.Spaces.eta) by ring,
      Real.rpow_add h (-2 : ℝ) (-Work.Spaces.eta), div_pow, div_eq_mul_inv, hcast,
      ← Real.rpow_neg (le_of_lt h) (2 : ℝ)]
    ring

/-- `(Ψ w / sin(2θ)^{η/2})² = w² · Ψ² · sin(2θ)^{-η}`. -/
lemma slot0_integrand_eq (Φ : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (psi Φ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ' hθ
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (show (Work.Spaces.eta / 2) ≠ 0 by
        have := eta_pos'; linarith), div_zero, mul_zero, pow_two, mul_zero,
      Real.zero_rpow (show (-Work.Spaces.eta) ≠ 0 by
        have := eta_pos'; linarith), mul_zero, mul_zero]
  · have hcast : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℕ)
        = (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℝ) :=
      (Real.rpow_natCast (x := Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) (n := 2)).symm
    have h1 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℝ)
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [← Real.rpow_mul (le_of_lt h) (Work.Spaces.eta / 2) (2 : ℝ)]
      congr 1
      ring
    rw [mul_pow, div_pow, div_eq_mul_inv, hcast, h1,
      ← Real.rpow_neg (le_of_lt h) Work.Spaces.eta]
    ring

/-- `slot0 Φ z = w(z)² · sliceEnergy Φ z`. -/
lemma slot0_eq_w_sq_sliceEnergy (Φ : ℝ → ℝ → ℝ) (z : ℝ) :
    slot0 Φ z = (Work.Spaces.w z) ^ 2 * sliceEnergy Φ z := by
  have h1 : slot0 Φ z = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
      * ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    rw [slot0_apply]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => slot0_integrand_eq Φ z hθ)
  rw [h1, MeasureTheory.integral_const_mul]
  congr 1
  rw [sliceEnergy]
  exact setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => (Phi_sq_rootWeight_eq (Φ := Φ) (z := z) hθ).symm)

/-! ## Dominating `sliceEnergy` by the `(0,0)` slot of the `ℋ^6`-form -/

/-- The `(0,0)` slot is one of the summands of `HkIntegrand`. -/
lemma slot0_le_sliceHk {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hHk : Work.Spaces.HkMem α 6 (psi Φ)) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    slot0 Φ z ≤ sliceHk α Φ z := by
  rw [slot0_apply, sliceHk_apply]
  refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    (hHk.1 z hz) (Eventually.of_forall fun θ => ?_)
  exact Work.Spaces.sq_le_HkIntegrand_z α 6 (psi Φ) z θ 0 (by norm_num)

/-- `sliceEnergy ≤ sliceHk` for `z > 0`, because `w(z)² ≥ 1`. -/
lemma sliceEnergy_le_sliceHk {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hHk : Work.Spaces.HkMem α 6 (psi Φ)) {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    sliceEnergy Φ z ≤ sliceHk α Φ z := by
  have hzIz : z ∈ Work.Spaces.Iz := by show (0 : ℝ) ≤ z; exact le_of_lt hz
  have hA0 : 0 ≤ slot0 Φ z := slot0_nonneg Φ z
  have hW : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq hz
  have hWpos : 0 < (Work.Spaces.w z) ^ 2 := w_sq_pos hz
  have hsplit : (Work.Spaces.w z) ^ 2 * sliceEnergy Φ z = slot0 Φ z :=
    (slot0_eq_w_sq_sliceEnergy Φ z).symm
  calc sliceEnergy Φ z
      = ((Work.Spaces.w z) ^ 2 * sliceEnergy Φ z) / (Work.Spaces.w z) ^ 2 := by
        rw [mul_div_cancel_left₀ _ (ne_of_gt hWpos)]
    _ = slot0 Φ z / (Work.Spaces.w z) ^ 2 := by rw [hsplit]
    _ ≤ slot0 Φ z := by
        rw [div_le_iff₀ hWpos]
        nlinarith
    _ ≤ sliceHk α Φ z := slot0_le_sliceHk hHk hzIz

/-- `sliceEnergy Φ z · z^{-4} ≤ sliceHk α Φ z` for `z > 0`, because `w(z)² = (1+z)⁴/z⁴`. -/
lemma sliceEnergy_mul_rpow_le_sliceHk {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hHk : Work.Spaces.HkMem α 6 (psi Φ)) {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    sliceEnergy Φ z * z ^ (-4 : ℝ) ≤ sliceHk α Φ z := by
  have hzIz : z ∈ Work.Spaces.Iz := by show (0 : ℝ) ≤ z; exact le_of_lt hz
  have hz0 : (0 : ℝ) < z := hz
  have hWpos : 0 < (Work.Spaces.w z) ^ 2 := w_sq_pos hz
  have hsl : sliceEnergy Φ z = slot0 Φ z / (Work.Spaces.w z) ^ 2 := by
    rw [eq_div_iff (ne_of_gt hWpos), mul_comm]
    exact (slot0_eq_w_sq_sliceEnergy Φ z).symm
  have hzpow : (0 : ℝ) < z ^ 4 := by positivity
  have h1zpow : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have h1z4 : z ^ 4 ≠ 0 := ne_of_gt hzpow
  have h1z1 : (1 + z) ^ 4 ≠ 0 := ne_of_gt h1zpow
  have key : sliceEnergy Φ z * z ^ (-4 : ℝ) = slot0 Φ z / (1 + z) ^ 4 := by
    rw [hsl, w_sq_eq, rpow_neg_four (le_of_lt hz)]
    field_simp
  rw [key]
  refine le_trans ?_ (slot0_le_sliceHk hHk hzIz)
  rw [div_le_iff₀ h1zpow]
  have hge : 1 ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
  nlinarith [slot0_nonneg Φ z, hge]

end

end Work.FTS.StrongEps.EComparison
