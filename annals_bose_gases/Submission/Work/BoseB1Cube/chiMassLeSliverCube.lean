import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.chi_boundary_taylor
import Submission.Work.BoseFixB1S.mfBoxAbbrev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory
open scoped Real

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open Submission.BoseGases

/-! ## 1.  The support of the cube window lies in the sliding box -/

/-- `chiSmallB M ℓ d u x ≠ 0` forces `x ∈ dlBox ℓ d u`: the `ℓ`-scale factor confines `x` to
`acube ℓ` (the corpus bump `χ` is supported in the ball of radius `1/2`) and the `ℓd`-scale
cosine factor confines `x − (ℓd)•u` to `acube (ℓd)`. -/
lemma chiSmallB_support_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u x : EuclideanSpace ℝ (Fin 3)} (hx : chiSmallB M ℓ d u x ≠ 0) :
    x ∈ dlBox ℓ d u := by
  rw [mem_dlBox_iff]
  constructor
  · rw [mem_acube_iff]
    intro m
    rw [Set.mem_Icc]
    have hb := abs_le.mp (chiSmallB_support_big_box hM hℓ hx m)
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · rw [mem_acube_iff]
    intro m
    rw [Set.mem_Icc]
    have hc : 0 < ℓ * d := mul_pos hℓ hd
    have h := chiSmallB_support_small_box (M := M) hM (u := u) (x := x) hx m
    have hrew : (ℓ * d)⁻¹ • x - u = (ℓ * d)⁻¹ • (x - (ℓ * d) • u) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    rw [hrew] at h
    have hsmul : ((ℓ * d)⁻¹ • (x - (ℓ * d) • u)).ofLp m
        = (ℓ * d)⁻¹ * (x - (ℓ * d) • u).ofLp m := by simp
    rw [hsmul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))] at h
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hc)
    have hfin : |(x - (ℓ * d) • u).ofLp m| ≤ (ℓ * d) / 2 := by
      calc |(x - (ℓ * d) • u).ofLp m|
          = (ℓ * d) * ((ℓ * d)⁻¹ * |(x - (ℓ * d) • u).ofLp m|) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
        _ ≤ (ℓ * d) * (1 / 2) := hmul
        _ = (ℓ * d) / 2 := by ring
    have hf := abs_le.mp hfin
    exact ⟨by linarith [hf.1], by linarith [hf.2]⟩

/-- `chiSmallB` vanishes outside the sliding box. -/
lemma chiSmallB_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ dlBox ℓ d u) :
    chiSmallB M ℓ d u x = 0 := by
  by_contra hne
  exact hx (chiSmallB_support_dlBox hM hℓ hd hne)

/-! ## 2.  The `ℓ`-scale factor on the sliver -/

/-- **Pointwise decay of the `ℓ`-scale factor on the sliver.**  If `x` satisfies
`ℓ (1/2 - ε) ≤ ‖x‖` with `0 ≤ ε` then `chiScale ℓ x = χ(x/ℓ) ≤ C₀ ε`, where `C₀` is a constant
of the linear boundary-decay bound `chi z ≤ C₀ (1/2 - ‖z‖)` on `‖z‖ ≤ 1/2`.

(No hypothesis `ε ≤ 1/2` is needed: the sliver hypothesis itself supplies the bound.) -/
lemma chiScale_le_of_sliver {C₀ : ℝ}
    (hC₀ : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 → chi z ≤ C₀ * (1 / 2 - ‖z‖))
    (hC₀pos : 0 < C₀) {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 ≤ ε) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ℓ * (1 / 2 - ε) ≤ ‖x‖) : chiScale ℓ x ≤ C₀ * ε := by
  have hz : (1 / 2 : ℝ) - ε ≤ ‖(ℓ⁻¹ : ℝ) • x‖ := by
    have h1 : (ℓ⁻¹ : ℝ) * (ℓ * (1 / 2 - ε)) ≤ (ℓ⁻¹ : ℝ) * ‖x‖ :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hℓ.le)
    rw [inv_mul_cancel_left₀ (ne_of_gt hℓ)] at h1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le)]
    exact h1
  by_cases hzc : ‖(ℓ⁻¹ : ℝ) • x‖ ≤ 1 / 2
  · have hmain := hC₀ ((ℓ⁻¹ : ℝ) • x) hzc
    have hle : (1 / 2 : ℝ) - ‖(ℓ⁻¹ : ℝ) • x‖ ≤ ε := by linarith
    calc chiScale ℓ x = chi ((ℓ⁻¹ : ℝ) • x) := rfl
      _ ≤ C₀ * ((1 / 2 : ℝ) - ‖(ℓ⁻¹ : ℝ) • x‖) := hmain
      _ ≤ C₀ * ε := mul_le_mul_of_nonneg_left hle hC₀pos.le
  · have hlt : (1 / 2 : ℝ) < ‖(ℓ⁻¹ : ℝ) • x‖ := lt_of_not_ge hzc
    have hzero : chiScale ℓ x = 0 := by
      rw [show chiScale ℓ x = chi ((ℓ⁻¹ : ℝ) • x) from rfl,
        chi_eq_zero_of_half_le_norm _ (le_of_lt hlt)]
    rw [hzero]
    exact mul_nonneg hC₀pos.le hε

/-! ## 3.  The pointwise bound on the square of the cube window -/

/-- **The pointwise sliver bound.**  On the sliver,
`(chiSmallB M ℓ d u x)² ≤ (C₀ · chiSmallDecay M)² · ε²`: the `ℓ`-scale factor is `≤ C₀ ε` by
`chiScale_le_of_sliver`, the `ℓd`-scale factor is bounded by its sup `chiSmallDecay M`
(`chiSmall_decay_coord_le_decay`), and both factors are nonnegative. -/
lemma chiSmallB_sq_le_of_sliver {C₀ : ℝ}
    (hC₀ : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 → chi z ≤ C₀ * (1 / 2 - ‖z‖))
    (hC₀pos : 0 < C₀) {M : ℕ} (hM : 1 ≤ M) {ℓ d ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    {u x : EuclideanSpace ℝ (Fin 3)} (hx : ℓ * (1 / 2 - ε) ≤ ‖x‖) :
    (chiSmallB M ℓ d u x) ^ 2 ≤ (C₀ * chiSmallDecay M) ^ 2 * ε ^ 2 := by
  have h1 : chiScale ℓ x ≤ C₀ * ε := chiScale_le_of_sliver hC₀ hC₀pos hℓ hε hx
  have h2 : chiSmall M ((ℓ * d)⁻¹ • x - u) ≤ chiSmallDecay M := by
    have h := chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u)
    rwa [abs_of_nonneg (chiSmall_nonneg M _)] at h
  have hprod : chiSmallB M ℓ d u x ≤ (C₀ * ε) * chiSmallDecay M := by
    rw [chiSmallB]
    exact mul_le_mul h1 h2 (chiSmall_nonneg M _) (mul_nonneg hC₀pos.le hε)
  have hnn : 0 ≤ chiSmallB M ℓ d u x := by
    rw [chiSmallB]
    exact mul_nonneg (chiScale_nonneg ℓ x) (chiSmall_nonneg M _)
  calc (chiSmallB M ℓ d u x) ^ 2
      ≤ ((C₀ * ε) * chiSmallDecay M) ^ 2 := pow_le_pow_left₀ hnn hprod 2
    _ = (C₀ * chiSmallDecay M) ^ 2 * ε ^ 2 := by ring

/-! ## 4.  The sliver bound on the cube windowed mass -/

theorem chiMassLeSliverCube {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ℓ d ε : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hε : 0 < ε) (hεle : ε ≤ 1 / 2)
      (u : EuclideanSpace ℝ (Fin 3)),
      (∀ x, x ∈ Submission.BoseGases.dlBox ℓ d u → ℓ * (1 / 2 - ε) ≤ ‖x‖) →
      Work.SmallBoxSliding.chiMass M ℓ d u
        ≤ C * ε ^ 2 * Work.SmallBoxSliding.boxMass ℓ d u := by
  obtain ⟨C₀, hC₀pos, hC₀raw⟩ := Work.BoseFixB1.chi_boundary_taylor 1
  have hC₀ : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 → chi z ≤ C₀ * (1 / 2 - ‖z‖) :=
    fun z hz => by simpa using hC₀raw z hz
  have hdecpos : 0 < chiSmallDecay M := by
    have h1 : 0 < chiSmallNormSq M := chiSmallNormSq_pos hM
    have h2 : 0 < (Real.sqrt (chiSmallNormSq M))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr h1)
    rw [chiSmallDecay, chiSmallNormFactor]
    exact mul_pos h2 (pow_pos (by norm_num) M)
  refine ⟨(C₀ * chiSmallDecay M) ^ 2, pow_pos (mul_pos hC₀pos hdecpos) 2, ?_⟩
  intro ℓ d ε hℓ hd hε hεle u hsliver
  have hK : ∀ x : EuclideanSpace ℝ (Fin 3), x ∈ dlBox ℓ d u →
      (chiSmallB M ℓ d u x) ^ 2 ≤ (C₀ * chiSmallDecay M) ^ 2 * ε ^ 2 :=
    fun x hx => chiSmallB_sq_le_of_sliver hC₀ hC₀pos hM hℓ hε.le (hsliver x hx)
  -- the integrand vanishes off the box
  have hzero : ∀ x ∉ dlBox ℓ d u, (chiSmallB M ℓ d u x) ^ 2 = 0 := by
    intro x hx
    rw [chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd hx]
    ring
  have hset : (∫ x in dlBox ℓ d u, (chiSmallB M ℓ d u x) ^ 2)
      = ∫ x : EuclideanSpace ℝ (Fin 3), (chiSmallB M ℓ d u x) ^ 2 :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hfin : (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) (dlBox ℓ d u) < ⊤ :=
    Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
  have hpt : ∀ x ∈ dlBox ℓ d u,
      ‖(chiSmallB M ℓ d u x) ^ 2‖ ≤ (C₀ * chiSmallDecay M) ^ 2 * ε ^ 2 := by
    intro x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hK x hx
  have hbound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) hfin hpt
  have hnonneg : 0 ≤ ∫ x in dlBox ℓ d u, (chiSmallB M ℓ d u x) ^ 2 :=
    MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_of_all _ (fun x => sq_nonneg (chiSmallB M ℓ d u x)))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, MeasureTheory.measureReal_def] at hbound
  rw [Work.SmallBoxSliding.chiMass_def, ← hset]
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.measureReal_def]
  exact hbound

end

end Work.BoseB1Cube
