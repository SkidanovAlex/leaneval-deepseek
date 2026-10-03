/-
# Auxiliary lemmas for the `fkr` interchange lemma

Continuation of `Submission.Work.KMTPlan.A6.FkrBasic`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.FkrBasic
import Submission.VarNorm
import Submission.LpMinkowski
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- The `ℓ^r` norm of a finite vector, written in `ℝ≥0∞`. -/
lemma fkr_ofReal_norm_toLp {r : NNReal} (hr : 1 ≤ r) {J : ℕ} (F : Fin J → ℂ) :
    ENNReal.ofReal ‖WithLp.toLp r F‖ = (∑ i : Fin J, ‖F i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hpr : 0 < (r : ENNReal).toReal := by
    rw [ENNReal.coe_toReal]; exact hr0
  have hnorm : ‖WithLp.toLp r F‖ = (∑ i : Fin J, ‖F i‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
    rw [PiLp.norm_eq_sum hpr, WithLp.ofLp_toLp, ENNReal.coe_toReal]
  rw [hnorm, ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (norm_nonneg _) _) (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
  have hsum : (∑ i : Fin J, ENNReal.ofReal (‖F i‖ ^ (r : ℝ)))
      = (∑ i : Fin J, ‖F i‖ₑ ^ (r : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le, ofReal_norm]
  rw [hsum]

/-- The free variation `varPart` of a sequence is the supremum of the clamped variations. -/
theorem varPart_le_iSup_varKc (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r a ≤ ⨆ K, varKc (r : ℝ) K a := by
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  rw [fkr_ofReal_norm_toLp hr]
  set K : ℕ := max J (N J) with hK
  have hJ : J < K + 1 := by
    have : J ≤ max J (N J) := le_max_left _ _
    omega
  have hle : ∀ i : Fin (J + 1), N i ≤ K := by
    intro i
    have h1 : (i : ℕ) ≤ J := Nat.lt_succ_iff.mp i.2
    have h2 : N i ≤ N J := hN h1
    have : N J ≤ max J (N J) := le_max_right _ _
    omega
  have humono : Monotone (fun i : Fin (J + 1) => (⟨N i, by have := hle i; omega⟩ : Fin (K + 1))) :=
    fun i j hij => hN (by simpa only [Fin.le_def] using hij)
  refine le_trans ?_ (le_iSup_of_le K (le_iSup_of_le
    (⟨⟨J, hJ⟩, ⟨fun i => ⟨N i, by have := hle i; omega⟩, humono⟩⟩ : Chain K) le_rfl))
  simp only [Fin.val_mk, Fin.val_succ, Fin.val_castSucc]
  exact le_rfl

/-- The clamped variation is monotone in the clamping parameter. -/
lemma varKc_mono (r : ℝ) {K K' : ℕ} (hKK' : K ≤ K') (a : ℕ → ℂ) :
    varKc r K a ≤ varKc r K' a := by
  refine iSup_le fun p => ?_
  refine le_iSup_of_le (⟨⟨p.1.1, by have := p.1.2; omega⟩,
    ⟨fun i => Fin.castLE (by omega) (p.2.1 i),
      fun i j hij => by simpa only [Fin.le_def, Fin.val_castLE] using p.2.2 hij⟩⟩ : Chain K') ?_
  refine le_of_eq (congrArg (fun z : ENNReal => z ^ (1 / r)) (Finset.sum_congr rfl fun i _ => ?_))
  simp only [Fin.val_castLE]

/-- Measurability of the clamped variation of a measurable sequence. -/
lemma measurable_varKc {g : ℕ → X → ℂ} (hg : ∀ k, Measurable (g k)) (r : ℝ) (K : ℕ) :
    Measurable (fun x => varKc r K (fun k => g k x)) := by
  refine Measurable.iSup fun p => ?_
  refine ENNReal.continuous_rpow_const.measurable.comp ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  refine ENNReal.continuous_rpow_const.measurable.comp ?_
  exact ((hg _).sub (hg _)).enorm

lemma eLpNorm_mono_ennreal {p : ENNReal} (hp : p ≠ ⊤) {f g : X → ENNReal}
    (h : ∀ x, f x ≤ g x) (μ : Measure X) (hf : AEStronglyMeasurable f μ := by pw_aesm) :
    eLpNorm f p μ ≤ eLpNorm g p μ := by
  by_cases hg : AEStronglyMeasurable g μ
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hg]
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm_exponent_zero hf]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf) hp0 hp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hg) hp0 hp]
  simp only [enorm_eq_self]
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by positivity)
  exact ENNReal.rpow_le_rpow (h x) (by positivity)

/-- `t ↦ t^{1/r}` for ENNReal-valued `t` is subadditive on finite sums (concavity). -/
lemma fkr_sum_rpow_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {ι : Type*} (s : Finset ι)
    (x : ι → ENNReal) : (∑ i ∈ s, x i) ^ q ≤ ∑ i ∈ s, (x i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hq0]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (ENNReal.rpow_add_le_add_rpow (x a) (∑ i ∈ s, x i) hq0.le hq1).trans
        (add_le_add_right ih _)

/-- A strictly increasing perturbation of a monotone function. -/
lemma fkrB_strict {A : ℕ → ℝ} (hA : Monotone A) {η : ℝ} (hη : 0 < η) :
    StrictMono (fun k => A k + (k + 1) * η) := by
  intro m n hmn
  have h1 : A m ≤ A n := hA (le_of_lt hmn)
  have h2 : ((m : ℝ) + 1) < ((n : ℝ) + 1) := by
    have : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    linarith
  nlinarith

/-- The `2`-scaled `ℓ^r` norm of a family is twice its `ℓ^r` norm. -/
lemma fkr_two_mul_rpow {ι : Type*} [Fintype ι] {q : ℝ} (hq : 0 < q) {Ω : Type*}
    (v : ι → Ω → ℂ) (x : Ω) :
    (∑ i, ‖(2 : ℂ) • v i x‖ₑ ^ q) ^ (1 / q)
      = 2 * (∑ i, ‖v i x‖ₑ ^ q) ^ (1 / q) := by
  have h2 : ‖(2 : ℂ)‖ₑ = (2 : ENNReal) := by rw [← ofReal_norm]; norm_num
  have h1 : ∀ i : ι, ‖(2 : ℂ) • v i x‖ₑ ^ q = (2 : ENNReal) ^ q * ‖v i x‖ₑ ^ q := by
    intro i
    rw [enorm_smul, h2, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / q), ← ENNReal.rpow_mul,
    mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- The dyadic identity . -/
lemma fkr_geom_ident {q R : ℝ} (hq : 0 < q) (hR : 0 < R) (l : ℕ) :
    ((2 : ℝ) ^ l) ^ (1 / q) * ((1 : ℝ) / 2 ^ l) ^ (1 / R)
      = (2 : ℝ) ^ ((l : ℝ) * (1 / q - 1 / R)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have e1 : ((2 : ℝ) ^ l) ^ (1 / q) = (2 : ℝ) ^ ((l : ℝ) * (1 / q)) := by
    rw [← Real.rpow_natCast (2 : ℝ) l, ← Real.rpow_mul h2.le]
  have e2 : ((1 : ℝ) / 2 ^ l) ^ (1 / R) = (2 : ℝ) ^ (-((l : ℝ) * (1 / R))) := by
    rw [one_div, Real.inv_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ l),
      ← Real.rpow_natCast (2 : ℝ) l, ← Real.rpow_mul h2.le, ← Real.rpow_neg h2.le]
  rw [e1, e2, ← Real.rpow_add h2]
  congr 1
  ring

/-- `(n • c^q)^{1/q} = n^{1/q} c` in `ℝ≥0∞`. -/
lemma ENNReal_nsmul_rpow {n : ℕ} {c : ℝ≥0∞} {q : ℝ} (hq : 0 < q) :
    (n • (c ^ q)) ^ (1 / q) = ((n : ℕ) : ENNReal) ^ (1 / q) * c := by
  rw [nsmul_eq_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / q),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- `n^{1/q} = ofReal (n^{1/q})` in `ℝ≥0∞`. -/
lemma ENNReal_natCast_rpow {n : ℕ} {q : ℝ} (hq : 0 < q) :
    (((n : ℕ) : ENNReal)) ^ (1 / q) = ENNReal.ofReal ((n : ℝ) ^ (1 / q)) := by
  rw [show ((n : ℕ) : ENNReal) = ENNReal.ofReal ((n : ℝ)) from (ENNReal.ofReal_natCast n).symm,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]

/-- `(ofReal 2)^n = (2^n : ℕ)` in `ℝ≥0∞`. -/
lemma ENNReal_ofReal_two_pow (n : ℕ) :
    (((2 : ℕ) ^ n : ℕ) : ENNReal) = (ENNReal.ofReal 2) ^ n := by
  rw [show (((2 : ℕ) ^ n : ℕ) : ENNReal)
        = ENNReal.ofReal ((((2 : ℕ) ^ n : ℕ)) : ℝ) from (ENNReal.ofReal_natCast _).symm,
    show ((((2 : ℕ) ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n from by push_cast; ring,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]

/-- The arithmetic core of the level bound of `fkr_step`. -/
lemma fkr_level_arith {q R : ℝ} (hq : 0 < q) (hR : 0 < R) (hRq : R < q) (l : ℕ)
    {B : ℝ} (hB : 0 ≤ B) :
    (((2 ^ l : ℕ)) : ENNReal) ^ (1 / q) * ENNReal.ofReal (B * ((1 : ℝ) / 2 ^ l) ^ (1 / R))
      = ENNReal.ofReal B * (ENNReal.ofReal (2 ^ (1 / q - 1 / R))) ^ l := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hq0 : (0 : ℝ) < 1 / q := one_div_pos.mpr hq
  have hcn : (0 : ℝ) ≤ 2 ^ (1 / q - 1 / R) := Real.rpow_nonneg (by norm_num) _
  have hcard : (((2 ^ l : ℕ)) : ENNReal) ^ (1 / q)
      = ENNReal.ofReal (((2 : ℝ) ^ l) ^ (1 / q)) := by
    rw [show (((2 ^ l : ℕ)) : ENNReal) = ENNReal.ofReal (((2 ^ l : ℕ) : ℝ)) from
        (ENNReal.ofReal_natCast _).symm,
      show (((2 ^ l : ℕ) : ℝ)) = (2 : ℝ) ^ l from by push_cast; ring]
    exact ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq0.le
  rw [hcard, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ l) ^ (1 / q)),
    ← ENNReal.ofReal_pow hcn, ← ENNReal.ofReal_mul hB]
  congr 1
  rw [show (((2 : ℝ) ^ (1 / q - 1 / R)) ^ l) = (2 : ℝ) ^ ((l : ℝ) * (1 / q - 1 / R)) from by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm],
    show ((2 : ℝ) ^ l) ^ (1 / q) * (B * ((1 : ℝ) / 2 ^ l) ^ (1 / R))
      = B * (((2 : ℝ) ^ l) ^ (1 / q) * ((1 : ℝ) / 2 ^ l) ^ (1 / R)) from by ring,
    fkr_geom_ident hq hR l]

end Work.KMTPlan.A6
