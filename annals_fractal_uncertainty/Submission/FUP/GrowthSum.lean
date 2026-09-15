import Submission.FUP.BMReduction
import Submission.FUP.ModifyWeight2
import Submission.Commons.MeasureTheory.Integral.measurable_iSup_sphere
import Submission.Commons.MeasureTheory.Integral.sum_dyadic_interval_integral_le
import Submission.Commons.MeasureTheory.Integral.intervalIntegral_le_two_mul_double
import Submission.Commons.MeasureTheory.Function.aestronglyMeasurable_comp_mul_right_Ioi

open MeasureTheory Metric Filter
open scoped Real BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, III: the growth functional and the constants `q_k`

The paper bounds the constants `q_k` by the growth functional

`G*(r) = sup_{‖x‖ = r} ∫_{1/2}^2 |ω(sx)| ds`,  `growthFunctional ω = ∫_0^∞ G*(r)/(1+r²) dr`,

and then the dyadic doubling property of `G*` makes `∑_k |q_k|` summable.

This module introduces `Gstar`, relates it to `growthFunctional` definitionally, and proves the
first half of the estimate: `|q_k| ≤ 4·2^{-k} G*(2^k)`.
-/

/-! `Gstar` is defined in `Submission.FUP.Growth` (together with `growthFunctional` and
`HasFiniteGrowth`); it is available here through `Submission.FUP.BMReduction`. -/

lemma growthFunctional_eq_Gstar (w : ℝᵈ → ℝ) :
    growthFunctional w = ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) := rfl

/-- The supremum is attained at any point of the sphere (as an upper bound). -/
lemma le_Gstar {w : ℝᵈ → ℝ} {r : ℝ}
    (hB : BddAbove (Set.range (fun x : {x : ℝᵈ // ‖x‖ = r} =>
      ∫ t in (1 / 2 : ℝ)..2, |w (t • (x : ℝᵈ))|))) {x : ℝᵈ} (hx : ‖x‖ = r) :
    ∫ t in (1 / 2 : ℝ)..2, |w (t • x)| ≤ Gstar w r :=
  le_ciSup hB ⟨x, hx⟩

lemma bddAbove_Gstar {w : ℝᵈ → ℝ} {M r : ℝ}
    (h : ∀ x : ℝᵈ, ‖x‖ = r → ∫ t in (1 / 2 : ℝ)..2, |w (t • x)| ≤ M) :
    BddAbove (Set.range (fun x : {x : ℝᵈ // ‖x‖ = r} =>
      ∫ t in (1 / 2 : ℝ)..2, |w (t • (x : ℝᵈ))|)) :=
  ⟨M, by rintro y ⟨x, rfl⟩; exact h x x.2⟩

/-- `BddAbove` for `Gstar`, from the regularity bound `|ω(x)| ≤ C_reg (1+‖x‖²)^{1/2}`. -/
lemma bddAbove_Gstar_of_regular {w : ℝᵈ → ℝ} {Creg r : ℝ} (hw : Continuous w) (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)) :
    BddAbove (Set.range (fun x : {x : ℝᵈ // ‖x‖ = r} =>
      ∫ t in (1 / 2 : ℝ)..2, |w (t • (x : ℝᵈ))|)) := by
  refine bddAbove_Gstar (M := (3 / 2) * (Creg * (1 + 4 * r ^ 2) ^ ((1 : ℝ) / 2)))
    (fun x hx => ?_)
  have hpt : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2, |w (t • x)| ≤ Creg * (1 + 4 * r ^ 2) ^ ((1 : ℝ) / 2) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
    have hn : ‖t • x‖ = t * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hx]
    have h1 : (1 : ℝ) + ‖t • x‖ ^ 2 ≤ 1 + 4 * r ^ 2 := by
      rw [hn]
      nlinarith [ht.2, hx ▸ norm_nonneg x, abs_nonneg r, sq_nonneg (t * r - 2 * r)]
    calc |w (t • x)| ≤ ‖w (t • x)‖ := le_of_eq (Real.norm_eq_abs _).symm
      _ ≤ Creg * (1 + ‖t • x‖ ^ 2) ^ ((1 : ℝ) / 2) := hreg _
      _ ≤ Creg * (1 + 4 * r ^ 2) ^ ((1 : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hCreg
          exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hmono : (∫ t in (1 / 2 : ℝ)..2, |w (t • x)|)
      ≤ ∫ t in (1 / 2 : ℝ)..2, (Creg * (1 + 4 * r ^ 2) ^ ((1 : ℝ) / 2)) :=
    intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by
        exact (hw.comp (continuous_id.smul continuous_const)).abs) _ _)
      (Continuous.intervalIntegrable continuous_const _ _) hpt
  rw [intervalIntegral.integral_const] at hmono
  have h32 : ((2:ℝ) - 1/2) = 3/2 := by norm_num
  rw [h32] at hmono
  simpa using hmono

/-! ## The bound `|q_k| ≤ 4·2^{-k} G*(2^k)` -/

lemma omegaPiece_nonpos {w : ℝᵈ → ℝ} (hw : ∀ x, w x ≤ 0) (k : ℕ) (x : ℝᵈ) :
    omegaPiece k w x ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (radialPsi_nonneg k x) (hw x)

lemma abs_radialPsi_le_one (k : ℕ) (x : ℝᵈ) : |radialPsi (d := d) k x| ≤ 1 := by
  rw [abs_of_nonneg (radialPsi_nonneg k x)]
  exact radialPsi_le_one k x

/-- `-π ω_k(v) = ∫_0^∞ |ω_k(t v)| t^{-2} dt` for a nonpositive weight. -/
lemma neg_sphProj_omegaPiece {w : ℝᵈ → ℝ} (hw : ∀ x, w x ≤ 0) (k : ℕ) (v : ℝᵈ) :
    -sphProj (omegaPiece k w) v
      = ∫ t in Set.Ioi (0 : ℝ), |omegaPiece k w (t • v)| * (t ^ 2)⁻¹ := by
  rw [sphProj, ← MeasureTheory.integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [abs_of_nonpos (omegaPiece_nonpos hw k (t • v))]
  ring

lemma sphProj_omegaPiece_nonpos {w : ℝᵈ → ℝ} (hw : ∀ x, w x ≤ 0) (k : ℕ) (v : ℝᵈ) :
    sphProj (omegaPiece k w) v ≤ 0 := by
  have h := neg_sphProj_omegaPiece hw k v
  have h2 : (0 : ℝ) ≤ ∫ t in Set.Ioi (0 : ℝ), |omegaPiece k w (t • v)| * (t ^ 2)⁻¹ :=
    integral_nonneg_of_ae (Eventually.of_forall (fun t => by positivity))
  linarith [h, h2]

lemma setIntegral_Icc_eq_intervalIntegral (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Icc a b, f t = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume))]

/-- Rescaling an interval integral to the dyadic window `[1/2,2]`. -/
lemma integral_pow_two_window (g : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), g t
      = (2 : ℝ) ^ k * ∫ s in (1 / 2 : ℝ)..2, g ((2 : ℝ) ^ k * s) := by
  have hc : (2 : ℝ) ^ k ≠ 0 := by positivity
  have h1 : (2 : ℝ) ^ k * (1 / 2) = (2 : ℝ) ^ (k - 1) := by
    have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ]
    rw [hpow]
    ring
  have h2 : (2 : ℝ) ^ k * 2 = (2 : ℝ) ^ (k + 1) := by rw [← pow_succ]
  have h := intervalIntegral.integral_comp_mul_left (f := g) (a := (1 / 2 : ℝ)) (b := 2)
    (c := (2 : ℝ) ^ k) hc
  rw [h1, h2] at h
  have h3 : (2 : ℝ) ^ k • (∫ s in (1 / 2 : ℝ)..2, g ((2 : ℝ) ^ k * s))
      = ∫ t in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), g t := by
    rw [h, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [← h3, smul_eq_mul]

/-- The main estimate of §4 for the dyadic constants: `|π ω_k(v̂)|` is bounded by the growth
functional sampled at the dyadic scale `2^k`. -/
lemma abs_sphProj_omegaPiece_le_Gstar (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hwcont : Continuous w) (hwnonpos : ∀ x, w x ≤ 0) {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {v : ℝᵈ} (hv : ‖v‖ = 1) :
    |sphProj (omegaPiece k w) v| ≤ 4 * ((2 : ℝ) ^ k)⁻¹ * Gstar w ((2 : ℝ) ^ k) := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ (k - 1) := by positivity
  have hab : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hB : BddAbove (Set.range (fun x : {x : ℝᵈ // ‖x‖ = (2 : ℝ) ^ k} =>
      ∫ t in (1 / 2 : ℝ)..2, |w (t • (x : ℝᵈ))|)) :=
    bddAbove_Gstar_of_regular hwcont hCreg hreg
  have hnorm : ‖((2 : ℝ) ^ k) • v‖ = (2 : ℝ) ^ k := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hv, mul_one]
  -- pointwise bound on the window
  have hpt : ∀ t ∈ Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)),
      |omegaPiece k w (t • v)| * (t ^ 2)⁻¹
        ≤ (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * |w (t • v)| := by
    intro t ht
    have h1 : |omegaPiece k w (t • v)| ≤ |w (t • v)| := by
      rw [omegaPiece_apply, abs_mul]
      calc |radialPsi (d := d) k (t • v)| * |w (t • v)| ≤ 1 * |w (t • v)| :=
            mul_le_mul_of_nonneg_right (abs_radialPsi_le_one k _) (abs_nonneg _)
        _ = |w (t • v)| := one_mul _
    have h2 : (t ^ 2)⁻¹ ≤ (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [ht.1, ha])
    calc |omegaPiece k w (t • v)| * (t ^ 2)⁻¹
        ≤ |w (t • v)| * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ |w (t • v)| * (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * |w (t • v)| := by ring
  -- support rewrite
  have hsub : Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)) ⊆ Set.Ioi (0 : ℝ) :=
    fun t ht => lt_of_lt_of_le ha ht.1
  have hzero : ∀ t ∈ Set.Ioi (0 : ℝ),
      t ∉ Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)) →
      |omegaPiece k w (t • v)| * (t ^ 2)⁻¹ = 0 := by
    intro t ht hnot
    have hlt : t < (2 : ℝ) ^ (k - 1) ∨ (2 : ℝ) ^ (k + 1) < t := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hnot
      exact hnot
    rw [omegaPiece_apply, radialPsi_smul_unit k hv ht, abs_mul,
      hlt.elim (fun h => dyadPsi_eq_zero_of_le_pow k hk1 (le_of_lt h))
        (fun h => dyadPsi_eq_zero_of_ge_pow k hk1 (le_of_lt h))]
    ring
  -- continuity on the window
  have hcont' : Continuous (fun t : ℝ => omegaPiece k w (t • v)) :=
    ((contDiff_radialPsi (d := d) k).continuous.mul hwcont).comp
      (continuous_id.smul continuous_const)
  have hcontW : Continuous (fun t : ℝ => w (t • v)) :=
    hwcont.comp (continuous_id.smul continuous_const)
  have hden : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹)
      (Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1))) :=
    (continuousOn_id.pow 2).inv₀ (fun t ht => by
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht.1
      exact pow_ne_zero 2 ht0.ne')
  have hF : IntegrableOn (fun t : ℝ => |omegaPiece k w (t • v)| * (t ^ 2)⁻¹)
      (Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1))) volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hcont'.abs.continuousOn.mul hden)
  have hG : IntegrableOn (fun t : ℝ => (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * |w (t • v)|)
      (Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1))) volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_const.mul hcontW.abs.continuousOn)
  have hmono := MeasureTheory.setIntegral_mono_on hF hG measurableSet_Icc hpt
  rw [abs_of_nonpos (sphProj_omegaPiece_nonpos hwnonpos k v),
    neg_sphProj_omegaPiece hwnonpos k v,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
      (fun x hx => hzero x hx.1 hx.2)]
  refine le_trans hmono ?_
  have hcm : (∫ x in Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)),
        (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * |w (x • v)|)
      = (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹
        * ∫ x in Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)), |w (x • v)| :=
    MeasureTheory.integral_const_mul _ _
  rw [hcm, setIntegral_Icc_eq_intervalIntegral _ hab,
    integral_pow_two_window (g := fun t : ℝ => |w (t • v)|) k hk1]
  have hG' : (∫ s in (1 / 2 : ℝ)..2, |w ((((2 : ℝ) ^ k) * s) • v)|)
      ≤ Gstar w ((2 : ℝ) ^ k) := by
    have hcomm : ∀ s : ℝ, |w ((((2 : ℝ) ^ k) * s) • v)| = |w (s • (((2 : ℝ) ^ k) • v))| := by
      intro s; rw [mul_smul, smul_comm]
    simp only [hcomm]
    exact le_Gstar hB hnorm
  have hconst : (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * (2 : ℝ) ^ k = 4 * ((2 : ℝ) ^ k)⁻¹ := by
    have hpk : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ]
    rw [hpk]
    field_simp
    ring
  have hpos : (0 : ℝ) ≤ (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * (2 : ℝ) ^ k := by positivity
  calc (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * ((2 : ℝ) ^ k
        * ∫ s in (1 / 2 : ℝ)..2, |w ((((2 : ℝ) ^ k) * s) • v)|)
      = (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * (2 : ℝ) ^ k
          * ∫ s in (1 / 2 : ℝ)..2, |w ((((2 : ℝ) ^ k) * s) • v)| := by ring
    _ ≤ (((2 : ℝ) ^ (k - 1)) ^ 2)⁻¹ * (2 : ℝ) ^ k * Gstar w ((2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hG' hpos
    _ = 4 * ((2 : ℝ) ^ k)⁻¹ * Gstar w ((2 : ℝ) ^ k) := by rw [hconst]

/-- **The dyadic constants are summable against the growth functional.** -/
lemma abs_qk_le_Gstar (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hwcont : Continuous w) (hwnonpos : ∀ x, w x ≤ 0) {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)) :
    |qk k w| ≤ 4 * ((2 : ℝ) ^ k)⁻¹ * Gstar w ((2 : ℝ) ^ k) := by
  have hB := bddBelow_sphProj_omegaPiece (d := d) k hk1 hCreg hreg
  refine abs_le.mpr ⟨?_, ?_⟩
  · refine le_qk hd k w (fun v => ?_)
    exact (abs_le.mp (abs_sphProj_omegaPiece_le_Gstar k hk1 hwcont hwnonpos hCreg hreg v.2)).1
  · refine le_trans (qk_le (d := d) k w hB (unitVec hd)) ?_
    exact (abs_le.mp (abs_sphProj_omegaPiece_le_Gstar k hk1 hwcont hwnonpos hCreg hreg
      (unitVec hd).2)).2

/-! ## Measurability and local integrability of `G*` -/

/-- `G*(r)` as a supremum over the image of the sphere. -/
lemma Gstar_eq_sSup (w : ℝᵈ → ℝ) (r : ℝ) :
    Gstar w r = sSup ((fun y : ℝᵈ => ∫ t in (1 / 2 : ℝ)..2, |w (t • y)|) ''
      {x : ℝᵈ | ‖x‖ = r}) := by
  change sSup (Set.range (fun x : {x : ℝᵈ // ‖x‖ = r} =>
      ∫ t in (1 / 2 : ℝ)..2, |w (t • (x : ℝᵈ))|))
    = sSup ((fun y : ℝᵈ => ∫ t in (1 / 2 : ℝ)..2, |w (t • y)|) '' {x : ℝᵈ | ‖x‖ = r})
  congr 1
  ext a
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v : ℝᵈ), v.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The profile `y ↦ ∫_{1/2}^2 |w (t • y)| dt` is continuous. -/
lemma continuous_sphProfile {w : ℝᵈ → ℝ} (hw : Continuous w) :
    Continuous (fun y : ℝᵈ => ∫ t in (1 / 2 : ℝ)..2, |w (t • y)|) := by
  have hF : Continuous (Function.uncurry fun (y : ℝᵈ) (t : ℝ) => |w (t • y)|) := by
    have h1 : Continuous (fun p : ℝᵈ × ℝ => p.2 • p.1) := continuous_snd.smul continuous_fst
    have h2 : Continuous (fun p : ℝᵈ × ℝ => |w (p.2 • p.1)|) := (hw.comp h1).abs
    change Continuous (fun p : ℝᵈ × ℝ => |w (p.2 • p.1)|)
    exact h2
  have h : Continuous (fun y : ℝᵈ => ∫ t in Set.Icc (1 / 2 : ℝ) 2, |w (t • y)|) :=
    continuous_parametric_integral_of_continuous (μ := volume)
      (f := fun (y : ℝᵈ) (t : ℝ) => |w (t • y)|) hF isCompact_Icc
  have heq : (fun y : ℝᵈ => ∫ t in (1 / 2 : ℝ)..2, |w (t • y)|)
      = fun y : ℝᵈ => ∫ t in Set.Icc (1 / 2 : ℝ) 2, |w (t • y)| := by
    funext y
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) / 2 ≤ 2),
      setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume))]
  rw [heq]
  exact h

/-- `G*` is measurable whenever `w` is continuous (the spherical maximal function of `w`'s
profile). -/
lemma aestronglyMeasurable_Gstar {w : ℝᵈ → ℝ} (hd : 1 ≤ d) (hw : Continuous w) :
    AEStronglyMeasurable (Gstar w) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 := Commons.MeasureTheory.Integral.measurable_iSup_sphere (d := d) hd
    (continuous_sphProfile (d := d) hw)
  have heq : (fun r : ℝ => sSup ((fun y : ℝᵈ => ∫ t in (1 / 2 : ℝ)..2, |w (t • y)|) ''
      {x : ℝᵈ | ‖x‖ = r})) = Gstar w := by
    funext r
    exact (Gstar_eq_sSup w r).symm
  rwa [heq] at h1

lemma Gstar_nonneg (w : ℝᵈ → ℝ) (r : ℝ) : 0 ≤ Gstar w r := by
  rw [Gstar]
  refine Real.sSup_nonneg ?_
  rintro a ⟨x, rfl⟩
  exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _)

lemma nonempty_sphere {r : ℝ} (hr : 0 < r) (hd : 1 ≤ d) : Nonempty {x : ℝᵈ // ‖x‖ = r} :=
  ⟨⟨r • (unitVec hd : ℝᵈ), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.le, (unitVec hd).2, mul_one]⟩⟩

/-- Pointwise bound for `G*` at radius `r` from the regularity hypothesis. -/
lemma Gstar_le_of_regular {w : ℝᵈ → ℝ} {Creg r : ℝ} (hw : Continuous w) (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)) (hd : 1 ≤ d)
    (hr : 0 < r) :
    Gstar w r ≤ (3 / 2) * (Creg * (1 + 4 * r ^ 2) ^ ((1 : ℝ) / 2)) := by
  haveI := nonempty_sphere (d := d) hr hd
  rw [Gstar]
  refine ciSup_le fun x => ?_
  have hpt : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2,
      |w (t • (x : ℝᵈ))| ≤ Creg * (1 + 4 * r ^ 2) ^ ((1 : ℝ) / 2) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
    have hn : ‖t • (x : ℝᵈ)‖ = t * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, x.2]
    have h1 : (1 : ℝ) + ‖t • (x : ℝᵈ)‖ ^ 2 ≤ 1 + 4 * r ^ 2 := by
      rw [hn]; nlinarith [ht.2, sq_nonneg (t * r - 2 * r)]
    calc |w (t • (x : ℝᵈ))| ≤ ‖w (t • (x : ℝᵈ))‖ := le_of_eq (Real.norm_eq_abs _).symm
      _ ≤ Creg * (1 + ‖t • (x : ℝᵈ)‖ ^ 2) ^ ((1 : ℝ) / 2) := hreg _
      _ ≤ Creg * (1 + 4 * r ^ 2) ^ ((1 : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hCreg
          exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hmono : (∫ t in (1 / 2 : ℝ)..2, |w (t • (x : ℝᵈ))|)
      ≤ ∫ t in (1 / 2 : ℝ)..2, (Creg * (1 + 4 * r ^ 2) ^ ((1 : ℝ) / 2)) :=
    intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable continuous_const _ _) hpt
  rw [intervalIntegral.integral_const, show (2 : ℝ) - 1 / 2 = 3 / 2 from by norm_num] at hmono
  exact hmono

/-- `G*` is integrable on each dyadic window, from the regularity bound on `w`. -/
lemma integrableOn_Gstar_Icc {w : ℝᵈ → ℝ} {Creg : ℝ} (hd : 1 ≤ d) (hw : Continuous w)
    (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {a b : ℝ} (hab : 0 < a) :
    IntegrableOn (Gstar w) (Set.Icc a b) volume := by
  have hmeas' : AEStronglyMeasurable (Gstar w) (volume.restrict (Set.Icc a b)) :=
    (aestronglyMeasurable_Gstar (d := d) hd hw).mono_measure
      (Measure.restrict_mono (fun t ht => lt_of_lt_of_le hab ht.1) le_rfl)
  refine IntegrableOn.of_bound measure_Icc_lt_top hmeas'
    ((3 / 2) * (Creg * (1 + 4 * (max a b) ^ 2) ^ ((1 : ℝ) / 2))) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hab hr.1
  have hb : r ≤ max a b := le_trans hr.2 (le_max_right _ _)
  have hsup := Gstar_le_of_regular (d := d) hw hCreg hreg hd hr0
  rw [Real.norm_eq_abs, abs_of_nonneg (Gstar_nonneg w r)]
  refine le_trans hsup ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCreg) (by norm_num)
  refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
  nlinarith [hb, hr0.le, le_max_left a b, le_max_right a b]


/-! ## The dyadic doubling inequality for `G*` -/

/-- **The "zoom out" inequality for the growth functional**: at the dyadic scale `2^k` the profile
integral is controlled by the average of `G*` over the surrounding window `[2^{k-1},2^{k+1}]`.
This is the step that makes `Σ_k 2^{-k}G*(2^k)` summable against `∫G*/(1+r²)`. -/
lemma Gstar_dyadic_le {w : ℝᵈ → ℝ} {Creg : ℝ} (hd : 1 ≤ d) (hw : Continuous w)
    (hCreg : 0 ≤ Creg) (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {k : ℕ} (hk1 : 1 ≤ k) :
    Gstar w ((2 : ℝ) ^ k)
      ≤ 2 * ((2 : ℝ) ^ k)⁻¹ * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r := by
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hne : (2 : ℝ) ^ k ≠ 0 := hkpos.ne'
  haveI := nonempty_sphere (d := d) hkpos hd
  rw [Gstar]
  refine ciSup_le fun x => ?_
  have hcontf : Continuous (fun s : ℝ => |w (s • (x : ℝᵈ))|) :=
    (hw.comp (continuous_id.smul continuous_const)).abs
  have hdouble := Commons.MeasureTheory.Integral.intervalIntegral_le_two_mul_double
    (fun s : ℝ => |w (s • (x : ℝᵈ))|) hcontf (fun s => abs_nonneg _)
  refine le_trans hdouble ?_
  -- pointwise bound of the inner integral by `G*` at the rescaled radius
  have hpt : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2,
      (∫ s in (1 / 2 : ℝ)..2, |w (((s * t) : ℝ) • (x : ℝᵈ))|) ≤ Gstar w (t * (2 : ℝ) ^ k) := by
    intro t ht
    have ht1 : (1 / 2 : ℝ) ≤ t := ht.1
    have htp : 0 < t := lt_of_lt_of_le (by norm_num) ht1
    have hnorm : ‖t • (x : ℝᵈ)‖ = t * (2 : ℝ) ^ k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htp, x.2]
    have hB : BddAbove (Set.range (fun y : {y : ℝᵈ // ‖y‖ = t * (2 : ℝ) ^ k} =>
        ∫ s in (1 / 2 : ℝ)..2, |w (s • (y : ℝᵈ))|)) :=
      bddAbove_Gstar_of_regular hw hCreg hreg
    have heq : (fun s : ℝ => |w (((s * t) : ℝ) • (x : ℝᵈ))|)
        = fun s : ℝ => |w (s • (t • (x : ℝᵈ)))| := by
      funext s
      rw [mul_smul]
    rw [heq]
    exact le_Gstar hB hnorm
  have hcontInner : Continuous
      (fun t : ℝ => ∫ s in (1 / 2 : ℝ)..2, |w (((s * t) : ℝ) • (x : ℝᵈ))|) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      (a₀ := (1 / 2 : ℝ)) (s := fun _ : ℝ => 2) ?_ continuous_const
    have h1 : Continuous (fun p : ℝ × ℝ => |w (((p.2 * p.1) : ℝ) • (x : ℝᵈ))|) :=
      (hw.comp (((continuous_snd.mul continuous_fst).smul continuous_const))).abs
    exact h1
  have hInt1 : IntervalIntegrable
      (fun t : ℝ => ∫ s in (1 / 2 : ℝ)..2, |w (((s * t) : ℝ) • (x : ℝᵈ))|) volume
      (1 / 2) 2 :=
    hcontInner.intervalIntegrable _ _
  have hle0 : Set.Ioc (1 / 2 : ℝ) 2 ⊆ Set.Ioi (0 : ℝ) :=
    Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (by norm_num))
  have hmeas2 : AEStronglyMeasurable (fun t : ℝ => Gstar w (t * (2 : ℝ) ^ k))
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 2)) :=
    (Commons.MeasureTheory.Function.aestronglyMeasurable_comp_mul_right_Ioi hkpos
      (aestronglyMeasurable_Gstar (d := d) hd hw)).mono_measure
      (Measure.restrict_mono (μ := volume) (ν := volume) hle0 le_rfl)
  have hbound2 : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 2)),
      ‖Gstar w (t * (2 : ℝ) ^ k)‖
        ≤ (3 / 2) * (Creg * (1 + 4 * ((2 : ℝ) ^ (k + 1)) ^ 2) ^ ((1 : ℝ) / 2)) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have ht1 : (1 / 2 : ℝ) ≤ t := ht.1.le
    have ht2 : t ≤ 2 := ht.2
    have htp : 0 < t := lt_of_lt_of_le (by norm_num) ht1
    have hr : 0 < t * (2 : ℝ) ^ k := mul_pos htp hkpos
    have hrle : t * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      have h1 : t * (2 : ℝ) ^ k ≤ 2 * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right ht2 hkpos.le
      have h2 : 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by rw [pow_succ']
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Gstar_nonneg w _)]
    refine le_trans (Gstar_le_of_regular (d := d) hw hCreg hreg hd hr) ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCreg) (by norm_num)
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    nlinarith [hrle, hr.le, pow_pos (by norm_num : (0:ℝ) < 2) (k+1)]
  have hInt2 : IntervalIntegrable (fun t : ℝ => Gstar w (t * (2 : ℝ) ^ k)) volume
      (1 / 2) 2 :=
    have hempty : Set.Ioc (2 : ℝ) (1 / 2) = ∅ := Set.Ioc_eq_empty_iff.mpr (by norm_num)
    ⟨IntegrableOn.of_bound measure_Ioc_lt_top hmeas2 _ hbound2, by
      rw [hempty]; exact integrableOn_empty⟩
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (1 / 2 : ℝ) ≤ 2) hInt1 hInt2 hpt
  -- the window identity
  have hwin : (∫ t in (1 / 2 : ℝ)..2, Gstar w (t * (2 : ℝ) ^ k))
      = ((2 : ℝ) ^ k)⁻¹ * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r := by
    have h := integral_pow_two_window (g := Gstar w) k hk1
    have hcomm : (∫ t in (1 / 2 : ℝ)..2, Gstar w (t * (2 : ℝ) ^ k))
        = ∫ s in (1 / 2 : ℝ)..2, Gstar w ((2 : ℝ) ^ k * s) := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      rw [mul_comm]
    rw [hcomm]
    rw [h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  calc 2 * (∫ t in (1 / 2 : ℝ)..2,
          ∫ s in (1 / 2 : ℝ)..2, |w (((s * t) : ℝ) • (x : ℝᵈ))|)
      ≤ 2 * ∫ t in (1 / 2 : ℝ)..2, Gstar w (t * (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 2 * (((2 : ℝ) ^ k)⁻¹
          * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r) := by rw [hwin]
    _ = 2 * ((2 : ℝ) ^ k)⁻¹
          * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r := by ring


/-- Arithmetic: `((2^k)⁻¹)² · 2^{2k+3} = 8`. -/
lemma inv_sq_pow_mul (k : ℕ) :
    ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ (2 * k + 3) = 8 := by
  have hne : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ (2 * k + 3) = ((2 : ℝ) ^ k) ^ 2 * 8 := by
    rw [show 2 * k + 3 = 2 * k + 3 from rfl, pow_add,
      show (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 by
        rw [show 2 * k = k * 2 by ring, pow_mul]]
    norm_num
  rw [hpow, sq]
  field_simp

/-- Arithmetic: `1 + r² ≤ 2^{2k+3}` for `r ∈ [2^{k-1}, 2^{k+1}]`, `k ≥ 1`. -/
lemma one_add_sq_le (k : ℕ) (hk1 : 1 ≤ k) {r : ℝ} (hr : r ∈ Set.Icc ((2 : ℝ) ^ (k - 1))
    ((2 : ℝ) ^ (k + 1))) :
    1 + r ^ 2 ≤ (2 : ℝ) ^ (2 * k + 3) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr.1
  have hsq : r ^ 2 ≤ (2 : ℝ) ^ (2 * k + 2) := by
    have h1 : r ^ 2 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 := pow_le_pow_left₀ hr0.le hr.2 2
    have h2 : ((2 : ℝ) ^ (k + 1)) ^ 2 = (2 : ℝ) ^ (2 * k + 2) := by
      rw [sq, ← pow_add]
      congr 1
      omega
    rwa [h2] at h1
  have hpow : (2 : ℝ) ^ (2 * k + 3) = (2 : ℝ) ^ (2 * k + 2) * 2 := by
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by ring, pow_succ]
  have hge : 1 ≤ (2 : ℝ) ^ (2 * k + 2) := one_le_pow₀ (by norm_num)
  rw [hpow]
  linarith

/-- **The dyadic constants against the growth functional**: `|q_k|` is bounded by `64` times the
integral of `G*/(1+r²)` over the dyadic window `[2^{k-1}, 2^{k+1}]`. -/
lemma abs_qk_le_integral (hd : 1 ≤ d) {k : ℕ} (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hwcont : Continuous w) (hwnonpos : ∀ x, w x ≤ 0) {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0)) :
    |qk k w| ≤ 64 * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1),
        Gstar w r / (1 + r ^ 2) := by
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hne : (2 : ℝ) ^ k ≠ 0 := hkpos.ne'
  have ha : (0 : ℝ) < (2 : ℝ) ^ (k - 1) := by positivity
  have hab : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  set hf : ℝ → ℝ := fun r => Gstar w r / (1 + r ^ 2) with hfdef
  have hf_nonneg : ∀ r : ℝ, 0 ≤ hf r := fun r => by
    rw [hfdef]
    exact div_nonneg (Gstar_nonneg w r) (by positivity)
  -- step 1 + 2
  have h3 : |qk k w| ≤ 8 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹
      * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r := by
    have h1 := abs_qk_le_Gstar hd k hk1 hwcont hwnonpos hCreg hreg
    have h2 := Gstar_dyadic_le (d := d) hd hwcont hCreg hreg hk1
    calc |qk k w| ≤ 4 * ((2 : ℝ) ^ k)⁻¹ * Gstar w ((2 : ℝ) ^ k) := h1
      _ ≤ 4 * ((2 : ℝ) ^ k)⁻¹ * (2 * ((2 : ℝ) ^ k)⁻¹
            * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 8 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹
            * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r := by ring
  -- step 3: `∫_{I_k} G* ≤ 2^{2k+3} ∫_{I_k} hf`
  have hCk : ∀ r ∈ Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)),
      Gstar w r ≤ (2 : ℝ) ^ (2 * k + 3) * hf r := by
    intro r hr
    have heq : Gstar w r = (1 + r ^ 2) * hf r := by
      rw [hfdef]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (one_add_sq_le k hk1 hr) (hf_nonneg r)
  have hInt1 : IntervalIntegrable (Gstar w) volume ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)) :=
    ⟨(integrableOn_Gstar_Icc (d := d) hd hwcont hCreg hreg ha).mono_set Set.Ioc_subset_Icc_self,
      by
        rw [Set.Ioc_eq_empty_iff.mpr (not_lt.mpr hab)]; exact integrableOn_empty⟩
  have hIoch : Set.Ioc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)) ⊆ Set.Ioi (0 : ℝ) :=
    fun r hr => lt_trans ha hr.1
  have hInt2 : IntervalIntegrable (fun r => (2 : ℝ) ^ (2 * k + 3) * hf r) volume
      ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)) :=
    ⟨((hint.mono_set hIoch).const_mul ((2 : ℝ) ^ (2 * k + 3))),
      by
        rw [Set.Ioc_eq_empty_iff.mpr (not_lt.mpr hab)]; exact integrableOn_empty⟩
  have hmono3 : (∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r)
      ≤ (2 : ℝ) ^ (2 * k + 3) * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), hf r := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hab hInt1 hInt2 hCk
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_const_mul] at h
    rwa [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  calc |qk k w| ≤ 8 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹
        * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r := h3
    _ ≤ 8 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹
        * ((2 : ℝ) ^ (2 * k + 3)
          * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), hf r) :=
        mul_le_mul_of_nonneg_left hmono3 (by positivity)
    _ = 64 * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), hf r := by
        rw [show (8 : ℝ) * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹
              * ((2 : ℝ) ^ (2 * k + 3) * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), hf r)
            = 8 * (((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ (2 * k + 3))
              * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), hf r from by ring,
          inv_sq_pow_mul k]
        norm_num


/-- **The sum of the dyadic constants is controlled by the growth functional**: the second half of
estimate (v) in Lemma `lem:modify_weight_lemma`. -/
lemma sum_abs_qk_le_growth (hd : 1 ≤ d) {K : ℕ} {w : ℝᵈ → ℝ}
    (hwcont : Continuous w) (hwnonpos : ∀ x, w x ≤ 0) {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0)) :
    (∑ k ∈ Finset.Icc 1 K, |qk k w|)
      ≤ 128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) := by
  have hfnn : ∀ r : ℝ, 0 ≤ Gstar w r / (1 + r ^ 2) :=
    fun r => div_nonneg (Gstar_nonneg w r) (by positivity)
  calc (∑ k ∈ Finset.Icc 1 K, |qk k w|)
      ≤ ∑ k ∈ Finset.Icc 1 K, 64 * ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1),
          Gstar w r / (1 + r ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact abs_qk_le_integral hd (Finset.mem_Icc.mp hk).1 hwcont hwnonpos hCreg hreg hint
    _ = 64 * ∑ k ∈ Finset.Icc 1 K,
          ∫ r in (2 : ℝ) ^ (k - 1)..(2 : ℝ) ^ (k + 1), Gstar w r / (1 + r ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 64 * (2 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Commons.MeasureTheory.Integral.sum_dyadic_interval_integral_le
          (fun r => Gstar w r / (1 + r ^ 2)) hfnn hint K
    _ = 128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) := by ring

end Submission.FUP
