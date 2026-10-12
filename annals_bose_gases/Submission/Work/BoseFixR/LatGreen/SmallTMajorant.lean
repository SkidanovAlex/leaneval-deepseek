import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.LatGreen.MadelungDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.SmallTMajorant`

The short-time (direct/Gaussian) majorant of the Ewald splitting of the `ℤ³` lattice Green's
function.

`Work.BoseFixR.LatGreen.tauZ t = 2 Σ_{j ≥ 1} e^{−(j−1/2)²/(4t)}` is the short-time tail
parameter (`MadelungDefs`).  The lemma proved here is the numerical bound needed for the
short-time piece of the Ewald splitting: with `η = etaZ = 1/32`,

`∫_0^η (4πt)^{−3/2} ((1 + τ(t))³ − 1) dt ≤ 1/12`.

The proof has three ingredients.

* `tauZ_le_exp`: on `(0, η]` one has `τ(t) ≤ 2.0001 · e^{−1/(16t)}`.  Indeed
  `τ(t) = 2 e^{−x/4} Σ_{j≥0} e^{−(j²+j)x}` with `x = 1/(4t) ≥ 8`; the `j = 0` term is `1` and
  the tail is `≤ 2 e^{−2x} ≤ 2 e^{−16}`, so the sum is `≤ 1.000001` and
  `τ ≤ 2.0001 e^{−1/(16t)}`.  Consequently, writing `E = e^{−1/(16t)}` and using
  `(1+τ)³ − 1 = 3τ + 3τ² + τ³` with `τ ≤ 2.0001 E`,

  `(4πt)^{−3/2}((1+τ)³ − 1) ≤ A · (6.001 E + 12.002 E² + 8.002 E³)`,  `A = (4π)^{−3/2}`,

  and `E^k = e^{−c_k/t}` with `c₁ = 1/16, c₂ = 1/8, c₃ = 3/16`.

* `integral_psiExp`: the elementary substitution `u = c/t` gives
  `∫_0^a t^{−3/2} e^{−c/t} dt = c^{−1/2} ∫_{c/a}^∞ u^{−1/2} e^{−u} du ≤ √a/c · e^{−c/a}`
  (formalised with the one-dimensional change of variables
  `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`).  At `a = η` the exponents
  `c_k/a` are `2, 4, 6`.

* the numerical estimate `√η ≤ 1/5`, `e^{−2} ≤ 0.13534`, `e^{−4} ≤ 0.13534²`,
  `e^{−6} ≤ 0.13534³` and `(4π)^{3/2} ≥ 40` (from `π > 3`) combine to
  `A · (6.001·16·√η·e^{−2} + 12.002·8·√η·e^{−4} + 8.002·(16/3)·√η·e^{−6}) ≤ 1/12`.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-! ### Measurability and upper bounds for `tauZ` -/

private lemma measurable_tauZ : Measurable tauZ := by
  unfold tauZ
  refine Measurable.const_mul (Measurable.tsum fun j => ?_) 2
  fun_prop

private lemma tauZ_nonneg (t : ℝ) : 0 ≤ tauZ t := by
  unfold tauZ
  exact mul_nonneg (by norm_num) (tsum_nonneg fun j => Real.exp_nonneg _)

/-- On `(0, etaZ]` the short-time tail parameter is bounded by `2.0001 e^{-1/(16t)}`. -/
private lemma tauZ_le_exp (t : ℝ) (ht : 0 < t) (htη : t ≤ etaZ) :
    tauZ t ≤ 2.0001 * Real.exp (-(1/(16*t))) := by
  have ht32 : t ≤ 1/32 := htη
  have hpos : 0 < 1/(2*t) := by positivity
  have h16 : 16 ≤ 1/(2*t) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  set r := Real.exp (-(1/(2*t))) with hr_def
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by rw [hr_def, Real.exp_lt_one_iff]; linarith
  have hle : ∀ j : ℕ, Real.exp (-(((j:ℝ)+1/2)^2)/(4*t))
      ≤ Real.exp (-(1/(16*t))) * r^j := by
    intro j
    rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h4t : 0 < 4*t := by positivity
    rw [div_le_iff₀ h4t]
    have hsimp : (-(1/(16*t)) + (j:ℝ) * (-(1/(2*t)))) * (4*t) = -(1/4) - 2*(j:ℝ) := by
      field_simp
      ring
    rw [hsimp]
    have hj : (0:ℝ) ≤ (j:ℝ) * ((j:ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; norm_num
      · have h1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast h
        nlinarith
    nlinarith [hj]
  have hgeom : Summable (fun j : ℕ => Real.exp (-(1/(16*t))) * r^j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsummable : Summable (fun j : ℕ => Real.exp (-(((j:ℝ)+1/2)^2)/(4*t))) :=
    Summable.of_nonneg_of_le (fun j => Real.exp_nonneg _) (fun j => hle j) hgeom
  have htsum : (∑' j : ℕ, Real.exp (-(((j:ℝ)+1/2)^2)/(4*t)))
      ≤ Real.exp (-(1/(16*t))) * (1 - r)⁻¹ := by
    calc (∑' j : ℕ, Real.exp (-(((j:ℝ)+1/2)^2)/(4*t)))
        ≤ ∑' j : ℕ, Real.exp (-(1/(16*t))) * r^j :=
          Summable.tsum_le_tsum (fun j => hle j) hsummable hgeom
      _ = Real.exp (-(1/(16*t))) * ∑' j : ℕ, r^j := tsum_mul_left
      _ = Real.exp (-(1/(16*t))) * (1 - r)⁻¹ := by
          rw [tsum_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)]
  have hexp16 : (1000000:ℝ) < Real.exp 16 := by
    have h1 : (2.7:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h2 : (1000000:ℝ) < (2.7:ℝ)^16 := by norm_num
    have h3 : (2.7:ℝ)^16 < (Real.exp 1)^16 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    have h4 : Real.exp 16 = (Real.exp 1)^16 := by
      rw [← Real.exp_nat_mul]; norm_num
    linarith [h4.symm ▸ h3]
  have hrle : r ≤ 1/1000000 := by
    have h : Real.exp (-(1/(2*t))) ≤ Real.exp (-16) := by
      refine Real.exp_le_exp.mpr ?_; linarith
    rw [hr_def]
    refine le_trans h ?_
    rw [Real.exp_neg, show (1:ℝ)/1000000 = (1000000:ℝ)⁻¹ by simp [one_div]]
    rw [inv_le_inv₀ (by positivity) (by norm_num)]
    exact hexp16.le
  have hfinal : (1 - r)⁻¹ ≤ 1.00001 := by
    have h1 : (1 - (1:ℝ)/1000000) ≤ 1 - r := by linarith
    have h2 : (1 - (1:ℝ)/1000000 : ℝ) = 999999/1000000 := by norm_num
    have h3 : (1 - r)⁻¹ ≤ (1 - (1:ℝ)/1000000)⁻¹ := by
      rw [inv_le_inv₀ (by linarith) (by norm_num)]
      exact h1
    rw [h2] at h3
    refine le_trans h3 ?_
    norm_num
  unfold tauZ
  have hE : (0:ℝ) ≤ Real.exp (-(1/(16*t))) := Real.exp_nonneg _
  nlinarith [htsum, hfinal, hE]

/-! ### The majorant and the elementary integral estimate -/

/-- The single-exponential building block `t^{−3/2} e^{−c/t}`. -/
private noncomputable def psiExp (c t : ℝ) : ℝ := t ^ (-(3/2:ℝ)) * Real.exp (-(c/t))

private lemma IntegrableOn.const_mul' {f : ℝ → ℝ} {s : Set ℝ} (h : IntegrableOn f s) (c : ℝ) :
    IntegrableOn (fun t => c * f t) s := by
  rw [MeasureTheory.IntegrableOn] at h ⊢
  exact h.const_mul c

/-- Pointwise form of the substitution `u = c/t` for `t^{−3/2} e^{−c/t}`. -/
private lemma psi_exp_pointwise {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    |-(c/u^2)| • ((c/u) ^ (-(3/2:ℝ)) * Real.exp (-(c/(c/u))))
      = c ^ (-(1/2:ℝ)) * (u ^ (-(1/2:ℝ)) * Real.exp (-u)) := by
  have hcu : c / (c/u) = u := by field_simp
  have habs : |-(c/u^2)| = c/u^2 := by
    rw [abs_of_nonpos (neg_nonpos.mpr (by positivity)), neg_neg]
  rw [hcu, habs, smul_eq_mul]
  have halg : c/u^2 * (c/u) ^ (-(3/2:ℝ)) = c^(-(1/2:ℝ)) * u^(-(1/2:ℝ)) := by
    rw [Real.div_rpow hc.le hu.le, Real.rpow_neg hu.le (3/2:ℝ), div_inv_eq_mul, div_eq_mul_inv]
    have hc1 : c * c ^ (-(3/2:ℝ)) = c ^ (-(1/2:ℝ)) := by
      have h : c ^ (1:ℝ) * c ^ (-(3/2:ℝ)) = c ^ (-(1/2:ℝ)) := by
        rw [← Real.rpow_add hc]; norm_num
      simpa using h
    have hu1 : (u^2)⁻¹ * u ^ (3/2:ℝ) = u ^ (-(1/2:ℝ)) := by
      have h2 : u^2 = u ^ (2:ℝ) := (Real.rpow_natCast u 2).symm
      rw [h2, ← Real.rpow_neg (le_of_lt hu) (2:ℝ), ← Real.rpow_add hu]
      norm_num
    calc c * (u^2)⁻¹ * (c ^ (-(3/2:ℝ)) * u ^ (3/2:ℝ))
        = (c * c ^ (-(3/2:ℝ))) * ((u^2)⁻¹ * u ^ (3/2:ℝ)) := by ring
      _ = c ^ (-(1/2:ℝ)) * u ^ (-(1/2:ℝ)) := by rw [hc1, hu1]
  rw [← mul_assoc, halg, mul_assoc]

/-- `∫_0^a t^{−3/2} e^{−c/t} dt ≤ √a / c · e^{−c/a}`, together with integrability, for
`a, c > 0`.  The substitution `u = c/t` turns the integral into
`c^{−1/2} ∫_{c/a}^∞ u^{−1/2} e^{−u} du`, and `u^{−1/2} ≤ (c/a)^{−1/2}` on the range of
integration. -/
private lemma integral_psiExp {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (-(3/2:ℝ)) * Real.exp (-(c/t))) (Ioc 0 a) ∧
    ∫ t in Ioc 0 a, t ^ (-(3/2:ℝ)) * Real.exp (-(c/t)) ≤ Real.sqrt a / c * Real.exp (-(c/a)) := by
  have hca : 0 < c/a := div_pos hc ha
  set F : ℝ → ℝ := fun u => c/u with hFdef
  set f' : ℝ → ℝ := fun u => -(c/u^2) with hf'def
  set s : Set ℝ := Ioi (c/a) with hsdef
  have hs : MeasurableSet s := measurableSet_Ioi
  have hsmem : ∀ u ∈ s, c/a ≤ u := fun u hu => le_of_lt (show c/a < u from hu)
  have hderiv : ∀ u ∈ s, HasDerivWithinAt F (f' u) s u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hca (show c/a < u from hu)
    have h1 : HasDerivAt (fun y : ℝ => c * y⁻¹) (c * (-(u^2)⁻¹)) u :=
      (hasDerivAt_inv (ne_of_gt hu0)).const_mul c
    have h2 : HasDerivAt F (f' u) u := by
      rw [hf'def, hFdef]
      convert h1 using 1
      · funext y; simp [div_eq_mul_inv]
      · field_simp
    exact h2.hasDerivWithinAt
  have hinj : InjOn F s := by
    intro u1 _ u2 _ h
    simp only [hFdef, div_eq_mul_inv] at h
    exact inv_injective (mul_left_cancel₀ (ne_of_gt hc) h)
  have himg : F '' s = Ioo 0 a := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu0 : 0 < u := lt_trans hca (show c/a < u from hu)
      refine ⟨div_pos hc hu0, ?_⟩
      rw [div_lt_iff₀ hu0]
      have h : c/a < u := hu
      rw [div_lt_iff₀ ha] at h
      linarith
    · rintro ⟨hv0, hva⟩
      refine ⟨c/v, ?_, ?_⟩
      · change c/a < c/v
        rw [div_lt_div_iff₀ ha hv0]
        exact mul_lt_mul_of_pos_left hva hc
      · rw [hFdef]; field_simp
  have hg : IntegrableOn (fun u : ℝ => (c/a) ^ (-(1/2:ℝ)) * Real.exp (-u)) s := by
    have h0 : IntegrableOn (fun u : ℝ => Real.exp (-u)) s := by
      rw [hsdef]; exact integrableOn_exp_neg_Ioi (c/a)
    rw [MeasureTheory.IntegrableOn] at h0 ⊢
    exact h0.const_mul _
  have hcont : ContinuousOn (fun u : ℝ => u ^ (-(1/2:ℝ)) * Real.exp (-u)) s := by
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_id.rpow_const
        (fun u hu => Or.inl (ne_of_gt (lt_trans hca (show c/a < u from hu))))
    · exact Real.continuous_exp.comp_continuousOn continuousOn_id.neg
  have huf : IntegrableOn (fun u : ℝ => u ^ (-(1/2:ℝ)) * Real.exp (-u)) s := by
    rw [MeasureTheory.IntegrableOn] at hg ⊢
    refine MeasureTheory.Integrable.mono' hg (hcont.aestronglyMeasurable hs) ?_
    rw [MeasureTheory.ae_restrict_iff' hs]
    refine Filter.Eventually.of_forall fun u hu => ?_
    rw [Real.norm_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (le_of_lt (lt_trans hca (show c/a < u from hu))) _) (Real.exp_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hca (hsmem u hu) (by norm_num : -(1/2:ℝ) ≤ 0))
      (Real.exp_nonneg _)
  have hbound : ∫ u in s, u ^ (-(1/2:ℝ)) * Real.exp (-u)
      ≤ (c/a) ^ (-(1/2:ℝ)) * Real.exp (-(c/a)) := by
    calc ∫ u in s, u ^ (-(1/2:ℝ)) * Real.exp (-u)
        ≤ ∫ u in s, (c/a) ^ (-(1/2:ℝ)) * Real.exp (-u) :=
          setIntegral_mono_on huf hg hs (fun u hu => mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hca (hsmem u hu) (by norm_num : -(1/2:ℝ) ≤ 0))
            (Real.exp_nonneg _))
      _ = (c/a) ^ (-(1/2:ℝ)) * Real.exp (-(c/a)) := by
          rw [hsdef, integral_const_mul, integral_exp_neg_Ioi]
  have hkey : c ^ (-(1/2:ℝ)) * (c/a) ^ (-(1/2:ℝ)) = Real.sqrt a / c := by
    have h1 : (c/a) ^ (-(1/2:ℝ)) = c ^ (-(1/2:ℝ)) * a ^ (1/2:ℝ) := by
      rw [Real.div_rpow hc.le ha.le, Real.rpow_neg ha.le (1/2:ℝ), div_inv_eq_mul]
    have h2 : c ^ (-(1/2:ℝ)) * c ^ (-(1/2:ℝ)) = c⁻¹ := by
      rw [← Real.rpow_add hc, show -(1/2:ℝ) + -(1/2) = -(1:ℝ) by norm_num, Real.rpow_neg hc.le 1,
        Real.rpow_one]
    rw [h1, ← mul_assoc, h2, ← Real.sqrt_eq_rpow]
    ring
  have hJ' : ∫ x in Ioo 0 a, x ^ (-(3/2:ℝ)) * Real.exp (-(c/x))
      = ∫ u in s, c ^ (-(1/2:ℝ)) * (u ^ (-(1/2:ℝ)) * Real.exp (-u)) := by
    have hJ := integral_image_eq_integral_abs_deriv_smul (s := s) (f := F) (f' := f')
      hs hderiv hinj (fun t : ℝ => t ^ (-(3/2:ℝ)) * Real.exp (-(c/t)))
    rw [← himg, hJ]
    refine setIntegral_congr_fun hs fun u hu => ?_
    have := psi_exp_pointwise hc (lt_trans hca (show c/a < u from hu))
    simpa [hFdef, hf'def] using this
  have hInt'' : IntegrableOn (fun u : ℝ => c ^ (-(1/2:ℝ)) * (u ^ (-(1/2:ℝ)) * Real.exp (-u))) s := by
    rw [MeasureTheory.IntegrableOn] at huf ⊢
    exact huf.const_mul _
  have hInt' : IntegrableOn
      (fun u => |f' u| • ((fun t : ℝ => t ^ (-(3/2:ℝ)) * Real.exp (-(c/t))) (F u))) s := by
    refine hInt''.congr_fun (fun u hu => ?_) hs
    have := psi_exp_pointwise hc (lt_trans hca (show c/a < u from hu))
    simpa [hFdef, hf'def] using this.symm
  have hIoop : IntegrableOn (fun t : ℝ => t ^ (-(3/2:ℝ)) * Real.exp (-(c/t))) (Ioo 0 a) := by
    rw [← himg]
    exact (integrableOn_image_iff_integrableOn_abs_deriv_smul hs hderiv hinj
      (fun t : ℝ => t ^ (-(3/2:ℝ)) * Real.exp (-(c/t)))).mpr hInt'
  constructor
  · have hsing : IntegrableOn (fun t : ℝ => t ^ (-(3/2:ℝ)) * Real.exp (-(c/t))) {a} := by
      rw [MeasureTheory.integrableOn_singleton_iff]
      right; simp
    have := hIoop.union hsing
    rwa [Set.Ioo_union_right ha] at this
  · calc ∫ t in Ioc 0 a, t ^ (-(3/2:ℝ)) * Real.exp (-(c/t))
        = ∫ t in Ioo 0 a, t ^ (-(3/2:ℝ)) * Real.exp (-(c/t)) := integral_Ioc_eq_integral_Ioo
      _ = ∫ u in s, c ^ (-(1/2:ℝ)) * (u ^ (-(1/2:ℝ)) * Real.exp (-u)) := hJ'
      _ = c ^ (-(1/2:ℝ)) * ∫ u in s, u ^ (-(1/2:ℝ)) * Real.exp (-u) := integral_const_mul _ _
      _ ≤ c ^ (-(1/2:ℝ)) * ((c/a) ^ (-(1/2:ℝ)) * Real.exp (-(c/a))) :=
            mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hc.le _)
      _ = Real.sqrt a / c * Real.exp (-(c/a)) := by rw [← mul_assoc, hkey]

/-! ### The majorant -/

/-- The cubic majorant with the exponentials written out. -/
private noncomputable def smallT (t : ℝ) : ℝ :=
  (4*Real.pi*t)^(-(3/2:ℝ)) * (6.001 * Real.exp (-(1/(16*t)))
    + 12.002 * (Real.exp (-(1/(16*t))))^2 + 8.002 * (Real.exp (-(1/(16*t))))^3)

/-- The same majorant in the form used for the integral estimate:
`(4π)^{−3/2} (6.001 t^{−3/2}e^{−1/(16t)} + 12.002 t^{−3/2}e^{−1/(8t)}
+ 8.002 t^{−3/2}e^{−3/(16t)})`. -/
private noncomputable def smallTMaj (t : ℝ) : ℝ :=
  (4*Real.pi)^(-(3/2:ℝ)) *
    (6.001 * psiExp (1/16) t + 12.002 * psiExp (1/8) t + 8.002 * psiExp (3/16) t)

/-- The cubic estimate: for `E > 0` and `0 ≤ τ ≤ 2.0001 E`,
`(1+τ)³ − 1 ≤ 6.001 E + 12.002 E² + 8.002 E³`. -/
private lemma cubic_le {E τ : ℝ} (hE : 0 < E) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 2.0001 * E) :
    (1 + τ)^3 - 1 ≤ 6.001 * E + 12.002 * E^2 + 8.002 * E^3 := by
  have h1 : (1 + τ)^3 - 1 = 3*τ + 3*τ^2 + τ^3 := by ring
  rw [h1]
  have h2 : τ^2 ≤ (2.0001*E)^2 := pow_le_pow_left₀ hτ0 hτ 2
  have h3 : τ^3 ≤ (2.0001*E)^3 := pow_le_pow_left₀ hτ0 hτ 3
  have h4 : 3*(2.0001*E)^2 ≤ 12.002*E^2 := by nlinarith [sq_nonneg E]
  have h5 : (2.0001*E)^3 ≤ 8.002*E^3 := by
    have hE0 : (0:ℝ) ≤ E := hE.le
    nlinarith [sq_nonneg E, mul_nonneg hE0 (sq_nonneg E)]
  have h6 : 3*(2.0001*E) ≤ 6.001*E := by linarith
  linarith

private lemma exp_sq_eq (t : ℝ) (ht : 0 < t) :
    (Real.exp (-(1/(16*t))))^2 = Real.exp (-((1/8)/t)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp
  norm_num

private lemma exp_cube_eq (t : ℝ) (ht : 0 < t) :
    (Real.exp (-(1/(16*t))))^3 = Real.exp (-((3/16)/t)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp
  norm_num

private lemma exp_one_div_eq (t : ℝ) (ht : 0 < t) :
    Real.exp (-(1/(16*t))) = Real.exp (-((1/16)/t)) := by
  congr 1
  field_simp

/-- The two descriptions of the majorant agree for `t > 0`. -/
private lemma smallT_eq (t : ℝ) (ht : 0 < t) : smallT t = smallTMaj t := by
  have h1 : Real.exp (-(1/(16*t))) = Real.exp (-((1/16)/t)) := exp_one_div_eq t ht
  have h2 : (Real.exp (-(1/(16*t))))^2 = Real.exp (-((1/8)/t)) := exp_sq_eq t ht
  have h3 : (Real.exp (-(1/(16*t))))^3 = Real.exp (-((3/16)/t)) := exp_cube_eq t ht
  simp only [smallT, smallTMaj, psiExp]
  rw [h2, h3, h1, Real.mul_rpow (by positivity : (0:ℝ) ≤ 4*Real.pi) ht.le]
  ring

/-! ### The numerical constants -/

private lemma exp_neg_two_le : Real.exp (-2) ≤ (0.13534:ℝ) := by
  have h2 : Real.exp 2 = (Real.exp 1)^2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hb : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsq : (2.7182818283:ℝ)^2 < (Real.exp 1)^2 :=
    pow_lt_pow_left₀ hb (by norm_num) (by norm_num)
  have h7 : (7.389:ℝ) < Real.exp 2 := by
    rw [h2]
    have : (7.389:ℝ) < (2.7182818283:ℝ)^2 := by norm_num
    linarith
  have hinv : Real.exp (-2) = (Real.exp 2)⁻¹ := by rw [Real.exp_neg]
  rw [hinv, inv_le_iff_one_le_mul₀ (Real.exp_pos 2)]
  have h0 : (0.13534:ℝ) * 7.389 < 0.13534 * Real.exp 2 :=
    mul_lt_mul_of_pos_left h7 (by norm_num)
  have h1 : (1:ℝ) < 0.13534 * 7.389 := by norm_num
  linarith

private lemma exp_neg_four_le : Real.exp (-4) ≤ (0.13534:ℝ)^2 := by
  have h4 : Real.exp (-4) = (Real.exp (-2))^2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_two_le 2

private lemma exp_neg_six_le : Real.exp (-6) ≤ (0.13534:ℝ)^3 := by
  have h6 : Real.exp (-6) = (Real.exp (-2))^3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h6]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_two_le 3

private lemma sqrt_etaZ_le : Real.sqrt etaZ ≤ (0.2:ℝ) := by
  rw [Real.sqrt_le_iff]
  exact ⟨by norm_num, by norm_num [etaZ]⟩

private lemma four_pi_rpow_ge : (40:ℝ) ≤ (4*Real.pi)^(3/2:ℝ) := by
  have hsq : ((4*Real.pi)^(3/2:ℝ))^2 = (4*Real.pi)^3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 4*Real.pi), ← Real.rpow_natCast]
    congr 1
    norm_num
  have hpos : (0:ℝ) ≤ (4*Real.pi)^(3/2:ℝ) := Real.rpow_nonneg (by positivity) _
  have h16 : (1600:ℝ) ≤ (4*Real.pi)^3 := by
    have h4pi : (12:ℝ) ≤ 4*Real.pi := by linarith [Real.pi_gt_three]
    calc (1600:ℝ) ≤ (12:ℝ)^3 := by norm_num
      _ ≤ (4*Real.pi)^3 := pow_le_pow_left₀ (by norm_num) h4pi 3
  nlinarith [hpos, hsq, h16]

/-! ### The main estimate -/

theorem SmallTMajorant :
    MeasureTheory.IntegrableOn
        (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * ((1 + Work.BoseFixR.LatGreen.tauZ t) ^ 3 - 1))
        (Set.Ioc 0 Work.BoseFixR.LatGreen.etaZ)
      ∧ ∫ t in Set.Ioc 0 Work.BoseFixR.LatGreen.etaZ,
          (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * ((1 + Work.BoseFixR.LatGreen.tauZ t) ^ 3 - 1) ≤ 1 / 12 := by
  have hEta : (0:ℝ) < etaZ := by norm_num [etaZ]
  have hApos : (0:ℝ) < (4*Real.pi)^(-(3/2:ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨I1int, I1le⟩ := integral_psiExp (a := etaZ) (c := 1/16) hEta (by norm_num)
  obtain ⟨I2int, I2le⟩ := integral_psiExp (a := etaZ) (c := 1/8) hEta (by norm_num)
  obtain ⟨I3int, I3le⟩ := integral_psiExp (a := etaZ) (c := 3/16) hEta (by norm_num)
  have hin1 : IntegrableOn (fun t : ℝ => 6.001 * psiExp (1/16) t) (Ioc 0 etaZ) :=
    I1int.const_mul' _
  have hin2 : IntegrableOn (fun t : ℝ => 12.002 * psiExp (1/8) t) (Ioc 0 etaZ) :=
    I2int.const_mul' _
  have hin3 : IntegrableOn (fun t : ℝ => 8.002 * psiExp (3/16) t) (Ioc 0 etaZ) :=
    I3int.const_mul' _
  have hmaj_int : IntegrableOn smallTMaj (Ioc 0 etaZ) := by
    unfold smallTMaj
    exact ((hin1.add hin2).add hin3).const_mul' _
  have hmaj_eq : ∫ t in Ioc 0 etaZ, smallTMaj t
      = (4*Real.pi)^(-(3/2:ℝ)) * (6.001 * (∫ t in Ioc 0 etaZ, psiExp (1/16) t)
          + 12.002 * (∫ t in Ioc 0 etaZ, psiExp (1/8) t)
          + 8.002 * (∫ t in Ioc 0 etaZ, psiExp (3/16) t)) := by
    unfold smallTMaj
    rw [integral_const_mul]
    have e1 : (fun t : ℝ => 6.001 * psiExp (1/16) t + 12.002 * psiExp (1/8) t
          + 8.002 * psiExp (3/16) t)
        = (fun t : ℝ =>
            ((fun t : ℝ => 6.001 * psiExp (1/16) t) + (fun t : ℝ => 12.002 * psiExp (1/8) t)) t
              + (fun t : ℝ => 8.002 * psiExp (3/16) t) t) := rfl
    rw [e1, MeasureTheory.integral_add (hin1.add hin2) hin3]
    have e2 : (fun t : ℝ =>
          ((fun t : ℝ => 6.001 * psiExp (1/16) t) + (fun t : ℝ => 12.002 * psiExp (1/8) t)) t)
        = (fun t : ℝ => 6.001 * psiExp (1/16) t + 12.002 * psiExp (1/8) t) := rfl
    rw [e2, MeasureTheory.integral_add hin1 hin2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  have hpt : ∀ t ∈ Ioc 0 etaZ,
      (4*Real.pi*t)^(-(3/2:ℝ)) * ((1+tauZ t)^3 - 1) ≤ smallTMaj t := by
    intro t ht
    obtain ⟨ht0, htη⟩ := ht
    have hE := Real.exp_pos (-(1/(16*t)))
    have hp : (0:ℝ) ≤ (4*Real.pi*t)^(-(3/2:ℝ)) := Real.rpow_nonneg (by positivity) _
    have h : (4*Real.pi*t)^(-(3/2:ℝ)) * ((1+tauZ t)^3 - 1) ≤ smallT t :=
      mul_le_mul_of_nonneg_left (cubic_le hE (tauZ_nonneg t) (tauZ_le_exp t ht0 htη)) hp
    rwa [smallT_eq t ht0] at h
  have hmeas : Measurable (fun t : ℝ => (4*Real.pi*t)^(-(3/2:ℝ)) * ((1 + tauZ t)^3 - 1)) := by
    have h1 : Measurable tauZ := measurable_tauZ
    fun_prop (disch := assumption)
  have hfn : ∀ t ∈ Ioc 0 etaZ, (0:ℝ) ≤ (4*Real.pi*t)^(-(3/2:ℝ)) * ((1+tauZ t)^3 - 1) := by
    intro t ht
    obtain ⟨ht0, _⟩ := ht
    refine mul_nonneg (Real.rpow_nonneg (by positivity) _) ?_
    have h2 : (1 + tauZ t)^3 - 1 = tauZ t * (3 + 3*tauZ t + (tauZ t)^2) := by ring
    rw [h2]
    exact mul_nonneg (tauZ_nonneg t) (by nlinarith [sq_nonneg (tauZ t), tauZ_nonneg t])
  have hf_int : IntegrableOn (fun t : ℝ => (4*Real.pi*t)^(-(3/2:ℝ)) * ((1+tauZ t)^3 - 1))
      (Ioc 0 etaZ) := by
    refine MeasureTheory.Integrable.mono' hmaj_int (hmeas.aestronglyMeasurable.restrict) ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_of_nonneg (hfn t ht)]
    exact hpt t ht
  constructor
  · exact hf_int
  · have hI1b : ∫ t in Ioc 0 etaZ, psiExp (1/16) t ≤ Real.sqrt etaZ / (1/16) * Real.exp (-2) := by
      have he : Real.exp (-((1/16)/etaZ)) = Real.exp (-2) := by congr 1; norm_num [etaZ]
      have h := I1le
      rw [he] at h
      exact h
    have hI2b : ∫ t in Ioc 0 etaZ, psiExp (1/8) t ≤ Real.sqrt etaZ / (1/8) * Real.exp (-4) := by
      have he : Real.exp (-((1/8)/etaZ)) = Real.exp (-4) := by congr 1; norm_num [etaZ]
      have h := I2le
      rw [he] at h
      exact h
    have hI3b : ∫ t in Ioc 0 etaZ, psiExp (3/16) t ≤ Real.sqrt etaZ / (3/16) * Real.exp (-6) := by
      have he : Real.exp (-((3/16)/etaZ)) = Real.exp (-6) := by congr 1; norm_num [etaZ]
      have h := I3le
      rw [he] at h
      exact h
    have hbnd : 6.001 * (∫ t in Ioc 0 etaZ, psiExp (1/16) t)
          + 12.002 * (∫ t in Ioc 0 etaZ, psiExp (1/8) t)
          + 8.002 * (∫ t in Ioc 0 etaZ, psiExp (3/16) t) ≤ Real.sqrt etaZ * (14.86:ℝ) := by
      have h1 : 6.001 * (∫ t in Ioc 0 etaZ, psiExp (1/16) t)
          ≤ 6.001 * (Real.sqrt etaZ / (1/16) * Real.exp (-2)) :=
        mul_le_mul_of_nonneg_left hI1b (by norm_num)
      have h2 : 12.002 * (∫ t in Ioc 0 etaZ, psiExp (1/8) t)
          ≤ 12.002 * (Real.sqrt etaZ / (1/8) * Real.exp (-4)) :=
        mul_le_mul_of_nonneg_left hI2b (by norm_num)
      have h3 : 8.002 * (∫ t in Ioc 0 etaZ, psiExp (3/16) t)
          ≤ 8.002 * (Real.sqrt etaZ / (3/16) * Real.exp (-6)) :=
        mul_le_mul_of_nonneg_left hI3b (by norm_num)
      have hb : 6.001 * (Real.sqrt etaZ / (1/16) * Real.exp (-2))
            + 12.002 * (Real.sqrt etaZ / (1/8) * Real.exp (-4))
            + 8.002 * (Real.sqrt etaZ / (3/16) * Real.exp (-6)) ≤ Real.sqrt etaZ * (14.86:ℝ) := by
        have hs : (0:ℝ) ≤ Real.sqrt etaZ := Real.sqrt_nonneg _
        have h16 : Real.sqrt etaZ / (1/16) = 16 * Real.sqrt etaZ := by ring
        have h8 : Real.sqrt etaZ / (1/8) = 8 * Real.sqrt etaZ := by ring
        have h316 : Real.sqrt etaZ / (3/16) = (16/3) * Real.sqrt etaZ := by ring
        rw [h16, h8, h316]
        have hb1 := mul_le_mul_of_nonneg_left exp_neg_two_le hs
        have hb2 := mul_le_mul_of_nonneg_left exp_neg_four_le hs
        have hb3 := mul_le_mul_of_nonneg_left exp_neg_six_le hs
        nlinarith [hb1, hb2, hb3]
      linarith
    have hfinal : (4*Real.pi)^(-(3/2:ℝ)) * (Real.sqrt etaZ * (14.86:ℝ)) ≤ 1/12 := by
      have h1 : (4*Real.pi)^(-(3/2:ℝ)) * (Real.sqrt etaZ * 14.86)
          ≤ (4*Real.pi)^(-(3/2:ℝ)) * ((0.2:ℝ) * 14.86) := by
        refine mul_le_mul_of_nonneg_left ?_ hApos.le
        exact mul_le_mul_of_nonneg_right sqrt_etaZ_le (by norm_num)
      refine le_trans h1 ?_
      have hAeq : (4*Real.pi)^(-(3/2:ℝ)) = ((4*Real.pi)^(3/2:ℝ))⁻¹ := by
        rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 4*Real.pi)]
      rw [hAeq, ← div_eq_inv_mul, div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)]
      nlinarith [four_pi_rpow_ge]
    have hle : ∫ t in Ioc 0 etaZ, (4*Real.pi*t)^(-(3/2:ℝ)) * ((1+tauZ t)^3 - 1)
        ≤ ∫ t in Ioc 0 etaZ, smallTMaj t := by
      refine integral_mono_ae hf_int hmaj_int ?_
      show ∀ᵐ t ∂(volume.restrict (Ioc 0 etaZ)),
        (4*Real.pi*t)^(-(3/2:ℝ)) * ((1+tauZ t)^3 - 1) ≤ smallTMaj t
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun t ht => hpt t ht
    calc ∫ t in Ioc 0 etaZ, (4*Real.pi*t)^(-(3/2:ℝ)) * ((1+tauZ t)^3 - 1)
        ≤ ∫ t in Ioc 0 etaZ, smallTMaj t := hle
      _ = (4*Real.pi)^(-(3/2:ℝ)) * (6.001 * (∫ t in Ioc 0 etaZ, psiExp (1/16) t)
            + 12.002 * (∫ t in Ioc 0 etaZ, psiExp (1/8) t)
            + 8.002 * (∫ t in Ioc 0 etaZ, psiExp (3/16) t)) := hmaj_eq
      _ ≤ (4*Real.pi)^(-(3/2:ℝ)) * (Real.sqrt etaZ * (14.86:ℝ)) :=
            mul_le_mul_of_nonneg_left hbnd hApos.le
      _ ≤ 1/12 := hfinal

end Work.BoseFixR.LatGreen
