
import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.tau_meas_posV2
import Submission.Work.HP.HP2.measure_separated_points
import Submission.Work.HP.HP2.lagrange_eval_bound
import Submission.Work.HP.HP2.exists_orthogonal_mulVec
import Submission.Work.HP.HP2.exists_fibre_poly

set_option autoImplicit false
noncomputable section

namespace Work.HP2

open MeasureTheory Polynomial Finset
open scoped ENNReal BigOperators Pointwise
open Work.HP

variable {m D : ℕ}

/-! ## A Lagrange bound for the leading coefficient -/

/-- The top coefficient of `∏ j ∈ s, (X - C (x j))` is `1`. -/
theorem coeff_prod_X_sub_C_card {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∏ j ∈ s, (X - C (x j) : ℝ[X])).coeff s.card = 1 := by
  have hne : ∀ j ∈ s, (X - C (x j) : ℝ[X]) ≠ 0 := fun j _ => sub_ne_zero.mpr (X_ne_C (x j))
  have hnd : (∏ j ∈ s, (X - C (x j) : ℝ[X])).natDegree = s.card := by
    rw [natDegree_prod s (fun j => (X - C (x j) : ℝ[X])) hne]
    simp_rw [natDegree_X_sub_C]
    simp
  rw [← hnd]
  exact (monic_prod_of_monic s (fun j => (X - C (x j) : ℝ[X]))
    (fun j _ => monic_X_sub_C (x j))).coeff_natDegree

/-- **Lagrange bound on the leading coefficient.**  If `|p.eval (x i)| ≤ lam` at `D + 1` nodes
`x i` that are pairwise `sep`-separated (`sep > 0`), then `|p.coeff D| ≤ (D+1) * lam / sep^D`.

Indeed the Lagrange interpolation formula
`p = Σ i, C (p.eval (x i) / ∏_{j≠i} (x i - x j)) * ∏_{j≠i} (X - C (x j))`
(`Polynomial.Lagrange.eq_interpolate`, `Lagrange.interpolate_eq_sum`) has each basis numerator of
`natDegree D` and `coeff D = 1`, so taking `coeff D` of both sides gives
`p.coeff D = Σ i, p.eval (x i) / ∏_{j≠i} (x i - x j)`, and every factor of every denominator is
`≥ sep`. -/
theorem lagrange_coeff_bound (D : ℕ) (p : Polynomial ℝ) (hdeg : p.natDegree ≤ D)
    (x : Fin (D + 1) → ℝ) {sep lam : ℝ} (hsep : 0 < sep) (hlam : 0 ≤ lam)
    (hx : ∀ i j, i ≠ j → sep ≤ |x i - x j|) (hval : ∀ i, |p.eval (x i)| ≤ lam) :
    |p.coeff D| ≤ ((D : ℝ) + 1) * (lam / sep ^ D) := by
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have h := hx i j hne
    rw [hij, sub_self, abs_zero] at h
    linarith
  have hcard : (Finset.univ : Finset (Fin (D + 1))).card = D + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hdeg' : p.degree < ((Finset.univ : Finset (Fin (D + 1))).card : WithBot ℕ) := by
    rw [hcard]
    exact lt_of_le_of_lt (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hdeg))
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))
  have hpq : p = Lagrange.interpolate (Finset.univ : Finset (Fin (D + 1))) x
      (fun i => p.eval (x i)) := Lagrange.eq_interpolate hinj.injOn hdeg'
  have herase : ∀ i : Fin (D + 1), (Finset.univ.erase i : Finset (Fin (D + 1))).card = D := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have key : p.coeff D = ∑ i ∈ (Finset.univ : Finset (Fin (D + 1))),
      p.eval (x i) / ∏ j ∈ (Finset.univ.erase i : Finset (Fin (D + 1))), (x i - x j) := by
    conv_lhs => rw [hpq]
    rw [Lagrange.interpolate_eq_sum, finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoeff : (∏ j ∈ (Finset.univ.erase i : Finset (Fin (D + 1))),
        (X - C (x j) : ℝ[X])).coeff D = 1 := by
      have h := coeff_prod_X_sub_C_card (Finset.univ.erase i) x
      rwa [herase i] at h
    rw [coeff_C_mul, hcoeff, mul_one]
  rw [key]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (D + 1))),
      |p.eval (x i) / ∏ j ∈ (Finset.univ.erase i : Finset (Fin (D + 1))), (x i - x j)|
        ≤ lam / sep ^ D := by
    intro i _
    rw [abs_div]
    refine div_le_div₀ hlam (hval i) (pow_pos hsep D) ?_
    rw [abs_prod]
    have h2 := Work.HP.HP2.pow_le_prod_abs_sub (Finset.univ.erase i) (x i) x hsep
      (fun j hj => hx i j (Ne.symm (Finset.mem_erase.mp hj).1))
    simpa [herase i] using h2
  calc |∑ i ∈ (Finset.univ : Finset (Fin (D + 1))),
        p.eval (x i) / ∏ j ∈ (Finset.univ.erase i : Finset (Fin (D + 1))), (x i - x j)|
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin (D + 1))),
        |p.eval (x i) / ∏ j ∈ (Finset.univ.erase i : Finset (Fin (D + 1))), (x i - x j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin (D + 1))), lam / sep ^ D := Finset.sum_le_sum hterm
    _ = ((D : ℝ) + 1) * (lam / sep ^ D) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## The one-variable sublevel bound -/

/-- Sublevel-set bound for a one-variable polynomial in terms of its leading coefficient: the set
of `t ∈ [-r,r]` with `|p.eval t| ≤ lam` has measure at most `C * (lam / |p.coeff D|)^{1/D}` with a
constant `C > 0` depending only on `D`; in particular the bound is independent of `r`.

The proof separates `D + 1` points of the sublevel set (`Work.HP.HP2.measure_separated_points`,
after rescaling the interval `[-r,r]` to `[-1,1]` with `Real.volume_preimage_mul_right`) and applies
`lagrange_coeff_bound` to them. -/
theorem fibre_sublevel_lc' (D : ℕ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℝ) (r lam : ℝ), 0 ≤ r → p.natDegree ≤ D →
      p.coeff D ≠ 0 → 0 ≤ lam →
      (volume {t : ℝ | |p.eval t| ≤ lam ∧ t ∈ Set.Icc (-r) r}).toReal ≤
        C * Real.rpow (lam / |p.coeff D|) (1 / (D : ℝ)) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hDne' : D ≠ 0 := by omega
  refine ⟨2 * ((D : ℝ) + 1) ^ 2, by positivity, ?_⟩
  intro p r lam hr hdeg hc0 hlam
  set E : Set ℝ := {t : ℝ | |p.eval t| ≤ lam ∧ t ∈ Set.Icc (-r) r} with hEdef
  set s : ℝ := (volume E).toReal with hsdef
  have hRHS : 0 ≤ 2 * ((D : ℝ) + 1) ^ 2 * Real.rpow (lam / |p.coeff D|) (1 / (D : ℝ)) := by
    have h1 : 0 ≤ lam / |p.coeff D| := div_nonneg hlam (abs_nonneg _)
    have h2 : 0 ≤ Real.rpow (lam / |p.coeff D|) (1 / (D : ℝ)) := Real.rpow_nonneg h1 _
    positivity
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · have hsub0 : E ⊆ {0} := by
      intro t ht
      rw [hEdef] at ht
      have h2 := ht.2
      rw [← hr0] at h2
      simp only [Set.mem_Icc] at h2
      simp only [Set.mem_singleton_iff]
      linarith [h2.1, h2.2]
    have hvol0 : volume E = 0 := measure_mono_null hsub0 (measure_singleton 0)
    have hs0 : s = 0 := by rw [hsdef, hvol0, ENNReal.toReal_zero]
    rw [hs0]
    exact hRHS
  · have hrne : r ≠ 0 := ne_of_gt hrpos
    have hEmeas : MeasurableSet E := by
      rw [hEdef]
      exact (measurableSet_le (p.continuous.abs).measurable measurable_const).inter
        isClosed_Icc.measurableSet
    set E' : Set ℝ := (fun y : ℝ => y * r) ⁻¹' E with hE'def
    have hE'meas : MeasurableSet E' := by
      rw [hE'def]
      exact hEmeas.preimage (measurable_id.mul_const r)
    have hE'vol : volume E' = ENNReal.ofReal r⁻¹ * volume E := by
      rw [hE'def, Real.volume_preimage_mul_right hrne E,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ r⁻¹)]
    have hE'toReal : (volume E').toReal = r⁻¹ * s := by
      rw [hE'vol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ r⁻¹),
        ← hsdef]
    have hsub' : E' ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro y hy
      have hy' : y * r ∈ E := hy
      rw [hEdef] at hy'
      have h2 : y * r ∈ Set.Icc (-r) r := hy'.2
      rw [Set.mem_Icc] at h2 ⊢
      constructor
      · have h := (le_div_iff₀ hrpos).mpr (show (-1) * r ≤ y * r by simpa using h2.1)
        rwa [mul_div_cancel_right₀ y hrne] at h
      · have h := (div_le_iff₀ hrpos).mpr (show y * r ≤ 1 * r by simpa using h2.2)
        rwa [mul_div_cancel_right₀ y hrne] at h
    by_cases hs0 : s = 0
    · rw [hs0]
      exact hRHS
    · have hspos : 0 < s := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hs0)
      set sep : ℝ := s / (2 * ((D : ℝ) + 1)) with hsepdef
      have hseppos : 0 < sep := by rw [hsepdef]; positivity
      have hsepdivpos : 0 < sep / r := div_pos hseppos hrpos
      have hvol' : 2 * ((D + 1 : ℕ) : ℝ) * (sep / r) ≤ (volume E').toReal := by
        have hcast : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
        rw [hcast, hE'toReal, hsepdef]
        have hD1 : ((D : ℝ) + 1) ≠ 0 := by positivity
        have hkey : 2 * ((D : ℝ) + 1) * (s / (2 * ((D : ℝ) + 1)) / r) = r⁻¹ * s := by
          field_simp
        rw [hkey]
      obtain ⟨y, hyE', hysep⟩ :=
        Work.HP.HP2.measure_separated_points hE'meas hsub' (D + 1) hsepdivpos hvol'
      have hxE : ∀ i, |p.eval (r * y i)| ≤ lam := by
        intro i
        have h1 : y i * r ∈ E := hyE' i
        rw [hEdef] at h1
        simpa [mul_comm] using h1.1
      have hxsep : ∀ i j, i ≠ j → sep ≤ |r * y i - r * y j| := by
        intro i j hij
        have h1 := hysep i j hij
        have h2 : |r * y i - r * y j| = r * |y i - y j| := by
          rw [← mul_sub, abs_mul, abs_of_pos hrpos]
        rw [h2]
        calc sep = r * (sep / r) := by field_simp
          _ ≤ r * |y i - y j| := mul_le_mul_of_nonneg_left h1 hrpos.le
      have hbound := lagrange_coeff_bound D p hdeg (fun i => r * y i) hseppos hlam hxsep hxE
      have hcpos : 0 < |p.coeff D| := abs_pos.mpr hc0
      have h1 : |p.coeff D| * sep ^ D ≤ ((D : ℝ) + 1) * lam := by
        have h2 := mul_le_mul_of_nonneg_right hbound (pow_nonneg hseppos.le D)
        rw [mul_assoc, div_mul_cancel₀ lam (pow_ne_zero D (ne_of_gt hseppos))] at h2
        exact h2
      have hsepD : sep ^ D ≤ (((D : ℝ) + 1) * lam) / |p.coeff D| := by
        rw [le_div_iff₀ hcpos, mul_comm]
        exact h1
      have hsep_le : sep ≤ ((((D : ℝ) + 1) * lam / |p.coeff D|) ^ (1 / (D : ℝ))) := by
        have h4 : sep = (sep ^ D) ^ ((1 : ℝ) / (D : ℝ)) := by
          rw [one_div]
          exact (Real.pow_rpow_inv_natCast hseppos.le hDne').symm
        rw [h4]
        exact Real.rpow_le_rpow (pow_nonneg hseppos.le D) hsepD (by positivity)
      have hrpow_le : Real.rpow ((D : ℝ) + 1) (1 / (D : ℝ)) ≤ (D : ℝ) + 1 := by
        refine Real.rpow_le_self_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) D]) ?_
        rw [div_le_one hDpos]
        exact_mod_cast hD
      have hs_eq : s = 2 * ((D : ℝ) + 1) * sep := by
        rw [hsepdef]
        have hD1 : ((D : ℝ) + 1) ≠ 0 := by positivity
        field_simp
      calc s = 2 * ((D : ℝ) + 1) * sep := hs_eq
        _ ≤ 2 * ((D : ℝ) + 1) * ((((D : ℝ) + 1) * lam / |p.coeff D|) ^ (1 / (D : ℝ))) :=
              mul_le_mul_of_nonneg_left hsep_le (by positivity)
        _ = 2 * ((D : ℝ) + 1) * (((D : ℝ) + 1) ^ (1 / (D : ℝ)) *
              (lam / |p.coeff D|) ^ (1 / (D : ℝ))) := by
              rw [mul_div_assoc, Real.mul_rpow (by positivity) (div_nonneg hlam hcpos.le)]
        _ ≤ 2 * ((D : ℝ) + 1) * (((D : ℝ) + 1) *
              (lam / |p.coeff D|) ^ (1 / (D : ℝ))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right hrpow_le
                (Real.rpow_nonneg (div_nonneg hlam hcpos.le) _)
        _ = 2 * ((D : ℝ) + 1) ^ 2 * (lam / |p.coeff D|) ^ (1 / (D : ℝ)) := by ring

/-! ## Homogeneity of the sublevel measure under dilation -/

/-- For `T > 0` and `P` homogeneous of degree `D` for nonnegative scalars, the sublevel set of `P`
in the ball of radius `T` is the `T`-dilate of the corresponding sublevel set in the unit ball. -/
theorem volume_hom_sublevel_smul' (m D : ℕ) (P : (Fin (m + 1) → ℝ) → ℝ) (lam T : ℝ) (hT : 0 < T)
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ x : Fin (m + 1) → ℝ, P (c • x) = c ^ D * P x) :
    volume {x : Fin (m + 1) → ℝ | rNorm x ≤ T ∧ |P x| ≤ lam}
      = ENNReal.ofReal (T ^ (m + 1)) *
        volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |P x| ≤ lam / T ^ D} := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hset : {x : Fin (m + 1) → ℝ | rNorm x ≤ T ∧ |P x| ≤ lam}
      = T • ({y : Fin (m + 1) → ℝ | rNorm y ≤ 1 ∧ |P y| ≤ lam / T ^ D} :
          Set (Fin (m + 1) → ℝ)) := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨T⁻¹ • x, ⟨?_, ?_⟩, smul_inv_smul₀ hTne x⟩
      · rw [rNorm_smul', abs_of_nonneg (by positivity : (0:ℝ) ≤ T⁻¹), inv_mul_le_iff₀' hT,
          one_mul]
        exact hx1
      · have h := hhom T⁻¹ (by positivity) x
        rw [h, abs_mul, abs_of_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ T⁻¹) D)]
        calc T⁻¹ ^ D * |P x| ≤ T⁻¹ ^ D * lam :=
              mul_le_mul_of_nonneg_left hx2 (pow_nonneg (by positivity) D)
          _ = lam / T ^ D := by rw [inv_pow, inv_mul_eq_div]
    · rintro ⟨y, ⟨hy1, hy2⟩, hxy⟩
      rw [← hxy]
      constructor
      · rw [rNorm_smul', abs_of_nonneg hT.le]
        exact mul_le_of_le_one_right hT.le hy1
      · have h := hhom T hT.le y
        rw [h, abs_mul, abs_of_nonneg (pow_nonneg hT.le D)]
        calc T ^ D * |P y| ≤ T ^ D * (lam / T ^ D) :=
              mul_le_mul_of_nonneg_left hy2 (pow_nonneg hT.le D)
          _ = lam := by field_simp
  rw [hset, Measure.addHaar_smul_of_nonneg volume hT.le, Module.finrank_fintype_fun_eq_card]
  simp

/-! ## Homogeneity of a form -/

theorem veronese_smul (c : ℝ) (x : Fin (m + 1) → ℝ) (μ : Mon D m) :
    veronese D m (c • x) μ = c ^ D * veronese D m x μ := by
  have h1 : (∏ i : Fin (m + 1), (c * x i) ^ (μ.1 i : ℕ))
      = (∏ i : Fin (m + 1), c ^ (μ.1 i : ℕ)) * ∏ i : Fin (m + 1), x i ^ (μ.1 i : ℕ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow c (x i) _
  have h2 : (∏ i : Fin (m + 1), c ^ (μ.1 i : ℕ)) = c ^ D := by
    rw [Finset.prod_pow_eq_pow_sum]
    rw [μ.2]
  simp only [veronese, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]

theorem formEvalR_smul' (c : ℝ) (x : Fin (m + 1) → ℝ) (F : Mon D m → ℝ) :
    formEvalR D m F (c • x) = c ^ D * formEvalR D m F x := by
  simp only [formEvalR]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [veronese_smul]
  ring

/-! ## A peel lemma for the fibre decomposition -/

theorem peel_sublevel' {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
    (A : Set (ℝ × X)) (hA : MeasurableSet A) (B : Set X) (hB : MeasurableSet B)
    (hAB : ∀ t x, (t, x) ∈ A → x ∈ B) (b : ℝ)
    (hfib : ∀ x ∈ B, volume ((fun t : ℝ => (t, x)) ⁻¹' A) ≤ ENNReal.ofReal b) :
    (volume.prod ν) A ≤ ENNReal.ofReal b * ν B := by
  rw [Measure.prod_apply_symm hA]
  calc ∫⁻ x, volume ((fun t : ℝ => (t, x)) ⁻¹' A) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal b * (B.indicator (1 : X → ℝ≥0∞)) x ∂ν :=
        lintegral_mono fun x => by
          by_cases hx : x ∈ B
          · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
            exact hfib x hx
          · rw [Set.indicator_of_notMem hx, mul_zero]
            exact le_of_eq (measure_mono_null (fun t ht => absurd (hAB t x ht) hx) measure_empty)
    _ = ENNReal.ofReal b * ∫⁻ x, (B.indicator (1 : X → ℝ≥0∞)) x ∂ν :=
        lintegral_const_mul _ (measurable_const.indicator hB)
    _ = ENNReal.ofReal b * ν B := by rw [lintegral_indicator_one hB]

/-! ## Norm of a vector with an inserted coordinate -/

theorem rNorm_insertNth' (c' : Fin m → ℝ) (t : ℝ) :
    rNorm (Fin.insertNth (0 : Fin (m + 1)) t c') ^ 2 = t ^ 2 + rNorm c' ^ 2 := by
  rw [rNorm_sq, rNorm_sq, Fin.insertNth_zero, Fin.sum_univ_succ]
  simp

/-! ## A linear map applied to an inserted coordinate -/

theorem mulVec_insertNth' (Mmat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (c' : Fin m → ℝ) (t : ℝ) :
    Mmat.mulVec (Fin.insertNth (0 : Fin (m + 1)) t c')
      = t • (Mmat.mulVec (Pi.single 0 1)) + Mmat.mulVec (Fin.insertNth (0 : Fin (m + 1)) 0 c') := by
  have h1 : Fin.insertNth (0 : Fin (m + 1)) t c'
      = t • (Pi.single (0 : Fin (m + 1)) (1 : ℝ))
        + Fin.insertNth (0 : Fin (m + 1)) (0 : ℝ) c' := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Pi.single_eq_same]
    · intro j
      simp
  rw [h1, Matrix.mulVec_add, Matrix.mulVec_smul]

/-! ## Continuity -/

theorem continuous_formEvalR' (F : Mon D m → ℝ) :
    Continuous (fun x : Fin (m + 1) → ℝ => formEvalR D m F x) := by
  unfold formEvalR veronese
  apply continuous_finsetSum
  intro μ _
  apply Continuous.mul
  · exact continuous_const
  · apply continuous_finsetProd
    intro i _
    exact (continuous_apply i).pow _

/-! ## The unit ball in the `m`-dimensional coordinate space -/

theorem volume_rNorm_ball_le' (m : ℕ) :
    volume {c' : Fin m → ℝ | rNorm c' ≤ 1} ≤ ENNReal.ofReal ((2 : ℝ) ^ m) := by
  have hsub : {c' : Fin m → ℝ | rNorm c' ≤ 1} ⊆
      Set.pi Set.univ (fun _ : Fin m => Set.Icc (-1 : ℝ) 1) := by
    intro c' hc'
    rw [Set.mem_pi]
    intro i _
    have h := abs_apply_le_rNorm c' i
    have h1 : |c' i| ≤ 1 := le_trans h hc'
    exact abs_le.mp h1
  calc volume {c' : Fin m → ℝ | rNorm c' ≤ 1}
      ≤ volume (Set.pi Set.univ (fun _ : Fin m => Set.Icc (-1 : ℝ) 1)) := measure_mono hsub
    _ = ∏ _i : Fin m, volume (Set.Icc (-1 : ℝ) 1) := by
          rw [volume_pi_pi]
    _ = ∏ _i : Fin m, ENNReal.ofReal 2 := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Real.volume_Icc]; norm_num
    _ = ENNReal.ofReal 2 ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ENNReal.ofReal ((2 : ℝ) ^ m) := (ENNReal.ofReal_pow (by norm_num) m).symm

/-! ## The main theorem -/

theorem form_sublevel_clean (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (F : Mon D m → ℝ) (M lam : ℝ), 0 < M →
      (∀ x : Fin (m + 1) → ℝ, rNorm x ≤ 1 → |∑ μ, F μ * veronese D m x μ| ≤ M) →
      (∃ x : Fin (m + 1) → ℝ, rNorm x ≤ 1 ∧ M ≤ |∑ μ, F μ * veronese D m x μ|) →
      0 ≤ lam →
      (MeasureTheory.volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧
          |∑ μ, F μ * veronese D m x μ| ≤ lam}).toReal ≤
        C * Real.rpow (lam / M) (1 / K) := by
  obtain ⟨Cf, hCfpos, hCf⟩ := fibre_sublevel_lc' D hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  refine ⟨Cf * 2 ^ m, (D : ℝ), by positivity, hDpos, ?_⟩
  intro F M lam hM hsup hatt hlam
  set f : (Fin (m + 1) → ℝ) → ℝ := fun x => ∑ μ, F μ * veronese D m x μ with hf
  have hfx : ∀ x, f x = ∑ μ, F μ * veronese D m x μ := fun x => by rw [hf]
  -- Step 1: find a unit vector `e` with `|f e| = M`.
  obtain ⟨x₀, hx₀norm, hx₀val⟩ := hatt
  have hfx₀ : |f x₀| = M := le_antisymm (by rw [hfx]; exact hsup x₀ hx₀norm) hx₀val
  have hf0 : f 0 = 0 := by
    have h := formEvalR_smul' (D := D) (m := m) (0 : ℝ) x₀ F
    have hDne : D ≠ 0 := by omega
    have h2 : formEvalR D m F (0 : Fin (m + 1) → ℝ) = 0 := by
      simpa only [zero_smul, zero_pow hDne, zero_mul] using h
    rw [hf]
    exact h2
  have hx₀ne : x₀ ≠ 0 := by
    intro hzero
    rw [hzero, hf0, abs_zero] at hfx₀
    linarith
  have hrne : rNorm x₀ ≠ 0 := fun h => hx₀ne (rNorm_eq_zero.mp h)
  have hrpos : 0 < rNorm x₀ := lt_of_le_of_ne (rNorm_nonneg x₀) (Ne.symm hrne)
  set e : Fin (m + 1) → ℝ := (rNorm x₀)⁻¹ • x₀ with he
  have he_norm : rNorm e = 1 := by
    rw [he, rNorm_smul', abs_inv, abs_of_pos hrpos, inv_mul_cancel₀ hrne]
  have hfe : f e = ((rNorm x₀)⁻¹) ^ D * f x₀ := by
    rw [he, hf]
    exact formEvalR_smul' (D := D) (m := m) ((rNorm x₀)⁻¹) x₀ F
  have he_val : |f e| = M := by
    refine le_antisymm ?_ ?_
    · rw [he]
      exact hsup e he_norm.le
    · have hle1 : (1 : ℝ) ≤ (rNorm x₀)⁻¹ := (one_le_inv₀ hrpos).mpr hx₀norm
      have h1 : (1 : ℝ) ≤ ((rNorm x₀)⁻¹) ^ D := one_le_pow₀ hle1
      have h3 : |((rNorm x₀)⁻¹) ^ D| = ((rNorm x₀)⁻¹) ^ D :=
        abs_of_nonneg (le_trans zero_le_one h1)
      rw [hfe, abs_mul, h3, hfx₀]
      calc M = 1 * M := (one_mul M).symm
        _ ≤ ((rNorm x₀)⁻¹) ^ D * M := mul_le_mul_of_nonneg_right h1 hM.le
  -- Step 2: the rotation.
  obtain ⟨Mmat, hMm_orth, hMm_norm, hMm_col, hMm_map⟩ :=
    Work.HP.HP2.exists_orthogonal_mulVec m e he_norm
  set T : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) := fun y => Mmat.mulVec y with hT
  have hTnorm : ∀ y, rNorm (T y) = rNorm y := by
    intro y; rw [hT]; exact hMm_norm y
  have hTcol : T (Pi.single (0 : Fin (m + 1)) (1 : ℝ)) = e := by
    rw [hT]; exact hMm_col
  have hTmap : Measure.map T volume = volume := by rw [hT]; exact hMm_map
  have hfcont : Continuous f := by rw [hf]; exact continuous_formEvalR' F
  have hTcont : Continuous T := by
    rw [hT]
    have h1 : (fun y : Fin (m + 1) → ℝ => Mmat.mulVec y) = ⇑(Matrix.toLin' Mmat) := by
      funext y; rw [Matrix.toLin'_apply]
    rw [h1]
    exact (Matrix.toLin' Mmat).continuous_of_finiteDimensional
  have hS_meas : MeasurableSet {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f x| ≤ lam} :=
    MeasurableSet.inter
      (measurableSet_le continuous_rNorm.measurable measurable_const)
      (measurableSet_le (hfcont.abs).measurable measurable_const)
  have hS₂_meas : MeasurableSet {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f (T x)| ≤ lam} :=
    MeasurableSet.inter
      (measurableSet_le continuous_rNorm.measurable measurable_const)
      (measurableSet_le ((hfcont.comp hTcont).abs).measurable measurable_const)
  have hvol_eq : volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f x| ≤ lam}
      = volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f (T x)| ≤ lam} := by
    have h1 : volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f x| ≤ lam}
        = volume (T ⁻¹' {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f x| ≤ lam}) := by
      rw [← Measure.map_apply hTcont.measurable hS_meas, hTmap]
    rw [h1]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hTnorm x]
  -- Step 3: slice along the first coordinate.
  set φ : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 with hφ
  have hφmp : MeasurePreserving φ volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hφsymm : ∀ (t : ℝ) (c' : Fin m → ℝ), φ.symm (t, c') = Fin.insertNth (0 : Fin (m + 1)) t c' := by
    intro t c'
    rw [hφ, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hmap_symm : Measure.map φ.symm volume = volume := (MeasurePreserving.symm φ hφmp).map_eq
  have hφimage_eq : φ '' {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f (T x)| ≤ lam}
      = φ.symm ⁻¹' {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f (T x)| ≤ lam} := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hp; exact ⟨φ.symm p, by simpa using hp, φ.apply_symm_apply p⟩
  have hφ_image : volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f (T x)| ≤ lam}
      = volume (φ '' {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f (T x)| ≤ lam}) := by
    rw [hφimage_eq, ← Measure.map_apply (MeasurableEquiv.measurable φ.symm) hS₂_meas, hmap_symm]
  -- The sliced set, described explicitly.
  set A : Set (ℝ × (Fin m → ℝ)) :=
    {p | rNorm (Fin.insertNth (0 : Fin (m + 1)) p.1 p.2) ≤ 1 ∧
        |f (T (Fin.insertNth (0 : Fin (m + 1)) p.1 p.2))| ≤ lam} with hA
  have hA_eq : A = φ '' {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f (T x)| ≤ lam} := by
    rw [hA]
    ext p
    obtain ⟨t, c'⟩ := p
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro h
      exact ⟨φ.symm (t, c'), by rw [hφsymm]; exact h, φ.apply_symm_apply _⟩
    · rintro ⟨y, hy, hyy⟩
      have hy' : φ.symm (t, c') = y := by rw [← hyy]; simp
      have hy2 := hy
      rw [← hy'] at hy2
      rw [hφsymm t c'] at hy2
      exact hy2
  have hA_meas : MeasurableSet A := by
    rw [hA_eq, hφimage_eq]
    exact hS₂_meas.preimage (MeasurableEquiv.measurable φ.symm)
  have hvol_A : (volume.prod volume) A
      = volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f (T x)| ≤ lam} := by
    rw [hA_eq, ← MeasureTheory.Measure.volume_eq_prod ℝ (Fin m → ℝ), hφ_image]
  -- Step 4: the peel.
  have hvolB : volume {c' : Fin m → ℝ | rNorm c' ≤ 1} ≤ ENNReal.ofReal ((2 : ℝ) ^ m) :=
    volume_rNorm_ball_le' m
  have hb_nonneg : 0 ≤ Cf * Real.rpow (lam / M) (1 / (D : ℝ)) :=
    mul_nonneg hCfpos.le (Real.rpow_nonneg (div_nonneg hlam hM.le) _)
  have hAB : ∀ t c', (t, c') ∈ A → c' ∈ {c' : Fin m → ℝ | rNorm c' ≤ 1} := by
    rintro t c' ht
    show rNorm c' ≤ 1
    have h1 : rNorm (Fin.insertNth (0 : Fin (m + 1)) t c') ≤ 1 := ht.1
    have h2 : rNorm (Fin.insertNth (0 : Fin (m + 1)) t c') ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (rNorm_nonneg (Fin.insertNth (0 : Fin (m + 1)) t c')) h1 2
      simpa using this
    rw [rNorm_insertNth'] at h2
    have h3 : rNorm c' ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    nlinarith [rNorm_nonneg c', sq_nonneg (rNorm c' - 1)]
  have hfib : ∀ c' ∈ {c' : Fin m → ℝ | rNorm c' ≤ 1},
      volume ((fun t : ℝ => (t, c')) ⁻¹' A)
        ≤ ENNReal.ofReal (Cf * Real.rpow (lam / M) (1 / (D : ℝ))) := by
    intro c' hc'
    obtain ⟨p, hpdeg, hpcoeff, hpeval⟩ :=
      Work.HP.HP2.exists_fibre_poly m D F (T (Fin.insertNth (0 : Fin (m + 1)) 0 c')) e
    set r : ℝ := Real.sqrt (1 - rNorm c' ^ 2) with hr
    have hnr : 0 ≤ r := Real.sqrt_nonneg _
    have hsq : r ^ 2 = 1 - rNorm c' ^ 2 := by
      rw [hr, Real.sq_sqrt]
      have h := pow_le_pow_left₀ (rNorm_nonneg c') hc' 2
      simp only [one_pow] at h
      linarith
    have hpcoeff_ne : p.coeff D ≠ 0 := by
      rw [hpcoeff, ← hfx e]
      intro hzero
      rw [hzero, abs_zero] at he_val
      linarith
    have hTins : ∀ t : ℝ, T (Fin.insertNth (0 : Fin (m + 1)) t c')
        = t • e + T (Fin.insertNth (0 : Fin (m + 1)) 0 c') := by
      intro t
      simp only [hT]
      rw [mulVec_insertNth', hMm_col]
    have hpval : ∀ t : ℝ, p.eval t = f (T (Fin.insertNth (0 : Fin (m + 1)) t c')) := by
      intro t
      rw [hpeval t, hTins t, hfx]
      refine Finset.sum_congr rfl fun μ _ => ?_
      congr 1
      simp only [veronese, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.prod_congr rfl fun i _ => by congr 1; ring
    have hsub : (fun t : ℝ => (t, c')) ⁻¹' A
        ⊆ {t : ℝ | |p.eval t| ≤ lam ∧ t ∈ Set.Icc (-r) r} := by
      intro t ht
      have h1 : rNorm (Fin.insertNth (0 : Fin (m + 1)) t c') ≤ 1 := ht.1
      have h2 : |f (T (Fin.insertNth (0 : Fin (m + 1)) t c'))| ≤ lam := ht.2
      refine ⟨?_, ?_⟩
      · rw [hpval t]; exact h2
      · rw [Set.mem_Icc, ← abs_le, ← Real.sqrt_sq (abs_nonneg t)]
        apply Real.sqrt_le_sqrt
        have h3 : rNorm (Fin.insertNth (0 : Fin (m + 1)) t c') ^ 2 ≤ 1 := by
          have := pow_le_pow_left₀ (rNorm_nonneg (Fin.insertNth (0 : Fin (m + 1)) t c')) h1 2
          simpa using this
        rw [rNorm_insertNth'] at h3
        rw [sq_abs, ← hsq]
        linarith
    have hfin : volume {t : ℝ | |p.eval t| ≤ lam ∧ t ∈ Set.Icc (-r) r} ≠ ⊤ := by
      have hle : volume {t : ℝ | |p.eval t| ≤ lam ∧ t ∈ Set.Icc (-r) r}
          ≤ ENNReal.ofReal (2 * r) := by
        calc volume {t : ℝ | |p.eval t| ≤ lam ∧ t ∈ Set.Icc (-r) r}
            ≤ volume (Set.Icc (-r) r) := measure_mono (fun t ht => ht.2)
          _ = ENNReal.ofReal (r - (-r)) := Real.volume_Icc
          _ = ENNReal.ofReal (2 * r) := by ring_nf
      exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
    calc volume ((fun t : ℝ => (t, c')) ⁻¹' A)
        ≤ volume {t : ℝ | |p.eval t| ≤ lam ∧ t ∈ Set.Icc (-r) r} := measure_mono hsub
      _ = ENNReal.ofReal ((volume {t : ℝ | |p.eval t| ≤ lam ∧ t ∈ Set.Icc (-r) r}).toReal) :=
            (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (Cf * Real.rpow (lam / M) (1 / (D : ℝ))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hcf := hCf p r lam hnr hpdeg hpcoeff_ne hlam
            rw [hpcoeff] at hcf
            rw [← hfx e, he_val] at hcf
            exact hcf
  have hpeel := peel_sublevel' volume A hA_meas {c' : Fin m → ℝ | rNorm c' ≤ 1}
    (measurableSet_le continuous_rNorm.measurable measurable_const) hAB
    (Cf * Real.rpow (lam / M) (1 / (D : ℝ))) hfib
  have hmain : (volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f x| ≤ lam}).toReal
      ≤ Cf * 2 ^ m * Real.rpow (lam / M) (1 / (D : ℝ)) := by
    have hone : volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |f x| ≤ lam} = (volume.prod volume) A := by
      rw [hvol_eq, hvol_A]
    rw [hone]
    calc ((volume.prod volume) A).toReal
        ≤ (ENNReal.ofReal (Cf * Real.rpow (lam / M) (1 / (D : ℝ)))
            * volume {c' : Fin m → ℝ | rNorm c' ≤ 1}).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolB)) hpeel
      _ ≤ (ENNReal.ofReal (Cf * Real.rpow (lam / M) (1 / (D : ℝ)))
            * ENNReal.ofReal ((2 : ℝ) ^ m)).toReal := by
          refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ?_
          exact mul_le_mul_of_nonneg_left hvolB zero_le
      _ = (ENNReal.ofReal ((Cf * Real.rpow (lam / M) (1 / (D : ℝ))) * (2 : ℝ) ^ m)).toReal := by
          rw [ENNReal.ofReal_mul hb_nonneg]
      _ = Cf * Real.rpow (lam / M) (1 / (D : ℝ)) * 2 ^ m := by
          rw [ENNReal.toReal_ofReal]; positivity
      _ = Cf * 2 ^ m * Real.rpow (lam / M) (1 / (D : ℝ)) := by ring
  exact hmain



theorem hom_sublevel (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (P : (Fin (m + 1) → ℝ) → ℝ) (H : Work.HP.Mon D m → ℝ)
        (M lam T : ℝ),
      (∀ x, P x = ∑ μ : Work.HP.Mon D m, H μ * Work.HP.veronese D m x μ) →
      (∀ c : ℝ, 0 ≤ c → ∀ x, P (c • x) = c ^ D * P x) →
      0 < M → (∀ x, Work.HP.rNorm x ≤ 1 → |P x| ≤ M) →
      (∃ x, Work.HP.rNorm x ≤ 1 ∧ M ≤ |P x|) → 0 ≤ lam → 0 < T →
      (MeasureTheory.volume {x : Fin (m + 1) → ℝ | Work.HP.rNorm x ≤ T ∧ |P x| ≤ lam}).toReal
        ≤ T ^ (m + 1) * C * Real.rpow (lam / (T ^ D * M)) (1 / K) := by
  obtain ⟨C, K, hCpos, hKpos, hC⟩ := form_sublevel_clean m D hm hD
  refine ⟨C, K, hCpos, hKpos, ?_⟩
  intro P H M lam T hP hhom hM hsup hatt hlam hT
  have hsup' : ∀ x : Fin (m + 1) → ℝ, rNorm x ≤ 1 →
      |∑ μ, H μ * veronese D m x μ| ≤ M := by
    intro x hx
    rw [← hP x]
    exact hsup x hx
  have hatt' : ∃ x : Fin (m + 1) → ℝ, rNorm x ≤ 1 ∧
      M ≤ |∑ μ, H μ * veronese D m x μ| := by
    obtain ⟨x, hx, hval⟩ := hatt
    exact ⟨x, hx, by rwa [← hP x]⟩
  have hlam' : 0 ≤ lam / T ^ D := div_nonneg hlam (by positivity)
  have hbound := hC H M (lam / T ^ D) hM hsup' hatt' hlam'
  have hscal := volume_hom_sublevel_smul' m D P lam T hT hhom
  have hseteq : {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧
        |∑ μ, H μ * veronese D m x μ| ≤ lam / T ^ D}
      = {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧ |P x| ≤ lam / T ^ D} := by
    ext x
    simp only [Set.mem_ofPred_eq, hP x]
  have hbound' : (volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧
        |P x| ≤ lam / T ^ D}).toReal ≤ C * Real.rpow ((lam / T ^ D) / M) (1 / K) := by
    rw [← hseteq]
    exact hbound
  rw [hscal, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  calc T ^ (m + 1) * (volume {x : Fin (m + 1) → ℝ | rNorm x ≤ 1 ∧
          |P x| ≤ lam / T ^ D}).toReal
      ≤ T ^ (m + 1) * (C * Real.rpow ((lam / T ^ D) / M) (1 / K)) :=
        mul_le_mul_of_nonneg_left hbound' (by positivity)
    _ = T ^ (m + 1) * C * Real.rpow (lam / (T ^ D * M)) (1 / K) := by
        rw [div_div]
        ring

end Work.HP2
