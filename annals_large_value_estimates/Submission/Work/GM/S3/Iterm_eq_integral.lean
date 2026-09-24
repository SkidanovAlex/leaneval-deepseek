import Mathlib
import Submission.Work.GM.S3.Base

/-!
# GM (7.3): the integral representation of `Iterm`

This file proves `Work.GM.S3.Iterm_eq_integral`: expanding the three Fourier transforms
`hhat (tᵢ - tᵢ₊₁) (mᵢN) = ∫ e(-mᵢNu) w(u)² u^{i(tᵢ-tᵢ₊₁)} du` and summing the finite
`t`-sums gives the triple integral over `ℝ³` displayed in the statement.

The proof is organized in three layers, mirroring the small "chapter" of facts the identity
needs:

* `itermZp v t = exp (log |v| * t * I)` is the unitary phase `|v|^{it}`; it behaves
  multiplicatively (`Zp_add`, `Zp_div`) and equals `(|v| : ℂ)^{It}` on `v ≠ 0`
  (`itermZp_eq_cpow`).  Everything is phrased with `Zp` so that all the `cpow`-manipulations
  reduce to `field_simp`/`ring`, which are valid on the support of the bump (there all `uᵢ ≥ 1`).
* `itermFp N d m u = e(-u(mN)) w(u)² Zp u d` is the single-variable factor; `hhat d (mN)` is its
  integral over `ℝ` (`iterm_hhat_eq_Fp`), and it is continuous with compact support, hence
  integrable (`iterm_integrable`).  Fubini for the product of three such factors
  (`iterm_integral_prod3`) is `MeasureTheory.integral_prod_mul` twice.
* The pointwise identity `iterm_integrand_eq_sum` rewrites the integrand of the statement
  (with its three `Rfun` factors) as the triple `t`-sum of products of `itermFp`'s.  Where some
  `w(uᵢ) = 0` both sides vanish; where no `w(uᵢ) = 0` all `uᵢ ∈ [1,2]` are positive and the
  algebraic identity `Σ_{t₁,t₂,t₃}(u₁/u₃)^{it₁}(u₂/u₁)^{it₂}(u₃/u₂)^{it₃}
  = R(u₁/u₃)R(u₂/u₁)R(u₃/u₂)` is the summand-wise identity `iterm_summand_id`.

The main theorem then follows by exchanging the finite `t`-sums with the integral
(`MeasureTheory.integral_finsetSum`) and Fubini.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory

/-- The unitary phase `|v|^{it} = exp (log |v| * t * I)` (`t` real).

Phrasing the phase this way makes the multiplicativity of `|·|^{it}` in the base available
without any nonzeroness side conditions on the exponents (they are only needed on the bases,
where the bump support gives them for free). -/
noncomputable def itermZp (v t : ℝ) : ℂ := Complex.exp (((Real.log |v| * t : ℝ) : ℂ) * Complex.I)

/-- The single-variable factor whose integral over `ℝ` is `hhat d (mN)`. -/
noncomputable def itermFp (N : ℕ) (d : ℝ) (m : ℤ) (u : ℝ) : ℂ :=
  ((Real.fourierChar (-(u * ((m : ℝ) * (N : ℝ)))) : Circle) : ℂ) *
    ((Submission.LargeValues.bumpW u : ℂ) ^ 2) * itermZp u d

/-- On the support of the bump, `u ≥ 1 > 0`. -/
lemma iterm_bumpW_pos_of_ne {x : ℝ} (h : Submission.LargeValues.bumpW x ≠ 0) : 0 < x :=
  lt_of_lt_of_le zero_lt_one (Submission.LargeValues.bumpW_spec.2.2.1 x h).1

theorem itermZp_eq_cpow {v : ℝ} (hv : v ≠ 0) (t : ℝ) :
    itermZp v t = ((|v| : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) := by
  have h : ((|v| : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact abs_ne_zero.mpr hv
  rw [itermZp, Complex.cpow_def_of_ne_zero h, ← Complex.ofReal_log (abs_nonneg v)]
  congr 1
  push_cast
  ring

lemma itermZp_add (v a b : ℝ) : itermZp v (a + b) = itermZp v a * itermZp v b := by
  rw [itermZp, itermZp, itermZp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma itermZp_neg (v a : ℝ) : itermZp v (-a) = (itermZp v a)⁻¹ := by
  rw [itermZp, itermZp, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

lemma itermZp_sub (v a b : ℝ) : itermZp v (a - b) = itermZp v a / itermZp v b := by
  rw [sub_eq_add_neg, itermZp_add, itermZp_neg, div_eq_mul_inv]

lemma itermZp_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (t : ℝ) :
    itermZp (x / y) t = itermZp x t / itermZp y t := by
  rw [itermZp, itermZp, itermZp, abs_div,
    Real.log_div (abs_ne_zero.mpr hx) (abs_ne_zero.mpr hy), ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- GM (7.3), summand-wise: `(u₁/u₃)^{it₁}(u₂/u₁)^{it₂}(u₃/u₂)^{it₃}` re-associates the
exponents into the differences `t₁-t₂`, `t₂-t₃`, `t₃-t₁`. -/
lemma iterm_summand_id {u₁ u₂ u₃ t₁ t₂ t₃ : ℝ} (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) (h₃ : u₃ ≠ 0) :
    itermZp u₁ (t₁ - t₂) * itermZp u₂ (t₂ - t₃) * itermZp u₃ (t₃ - t₁)
      = itermZp (u₁ / u₃) t₁ * itermZp (u₂ / u₁) t₂ * itermZp (u₃ / u₂) t₃ := by
  rw [itermZp_sub, itermZp_sub, itermZp_sub, itermZp_div h₁ h₃, itermZp_div h₂ h₁,
    itermZp_div h₃ h₂]
  field_simp

/-- The additive character splits the phase `N(m₁u₁+m₂u₂+m₃u₃)` into the three phases that
appear in `itermFp`. -/
lemma iterm_fourierChar_split (N : ℕ) (m₁ m₂ m₃ : ℤ) (u₁ u₂ u₃ : ℝ) :
    ((Real.fourierChar
        (-((N : ℝ) * ((m₁ : ℝ) * u₁ + (m₂ : ℝ) * u₂ + (m₃ : ℝ) * u₃))) : Circle) : ℂ) =
      (Real.fourierChar (-(u₁ * ((m₁ : ℝ) * (N : ℝ)))) : ℂ) *
        (Real.fourierChar (-(u₂ * ((m₂ : ℝ) * (N : ℝ)))) : ℂ) *
        (Real.fourierChar (-(u₃ * ((m₃ : ℝ) * (N : ℝ)))) : ℂ) := by
  rw [show (-((N : ℝ) * ((m₁ : ℝ) * u₁ + (m₂ : ℝ) * u₂ + (m₃ : ℝ) * u₃))) =
      -(u₁ * ((m₁ : ℝ) * (N : ℝ))) +
        (-(u₂ * ((m₂ : ℝ) * (N : ℝ))) + -(u₃ * ((m₃ : ℝ) * (N : ℝ)))) by ring]
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  push_cast
  ring

/-- `Rfun W v = Σ_{t ∈ W} |v|^{it}` for `v ≠ 0`. -/
lemma iterm_Rfun_eq_sum (W : Finset ℝ) {v : ℝ} (hv : v ≠ 0) :
    Submission.GM.Rfun W v = ∑ t ∈ W, itermZp v t := by
  rw [Submission.GM.Rfun]
  apply Finset.sum_congr rfl
  intro t _
  exact (itermZp_eq_cpow hv t).symm

/-- A summand comparison: on the support of the bump the `t₁,t₂,t₃`-summand of the integrand
equals the product of the three `itermFp` factors. -/
lemma iterm_summand_eq (N : ℕ) (m : ℤ × ℤ × ℤ) (t₁ t₂ t₃ u₁ u₂ u₃ : ℝ)
    (h₁ : 0 < u₁) (h₂ : 0 < u₂) (h₃ : 0 < u₃) :
    (Real.fourierChar
        (-((N : ℝ) * ((m.1 : ℝ) * u₁ + (m.2.1 : ℝ) * u₂ + (m.2.2 : ℝ) * u₃))) : ℂ) *
        ((Submission.LargeValues.bumpW u₁ : ℂ) ^ 2 * (Submission.LargeValues.bumpW u₂ : ℂ) ^ 2 *
          (Submission.LargeValues.bumpW u₃ : ℂ) ^ 2) *
        (itermZp (u₁ / u₃) t₁ * itermZp (u₂ / u₁) t₂ * itermZp (u₃ / u₂) t₃)
      = itermFp N (t₁ - t₂) m.1 u₁ * itermFp N (t₂ - t₃) m.2.1 u₂ *
        itermFp N (t₃ - t₁) m.2.2 u₃ := by
  rw [itermFp, itermFp, itermFp]
  rw [← iterm_summand_id (ne_of_gt h₁) (ne_of_gt h₂) (ne_of_gt h₃)]
  rw [iterm_fourierChar_split N m.1 m.2.1 m.2.2 u₁ u₂ u₃]
  ring

/-- `(Σ f)(Σ g)(Σ h) = ΣΣΣ f g h` for a common index set. -/
lemma iterm_sum3 (s : Finset ℝ) (f g h : ℝ → ℂ) :
    (∑ i ∈ s, f i) * (∑ j ∈ s, g j) * (∑ k ∈ s, h k)
      = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i * g j * h k := by
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul_sum]

/-- A constant times a product of three sums is the triple sum of the multiplied summands. -/
lemma iterm_const_mul_sum3 (c : ℂ) (s : Finset ℝ) (f g h : ℝ → ℂ) :
    c * (∑ i ∈ s, f i) * (∑ j ∈ s, g j) * (∑ k ∈ s, h k)
      = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, c * (f i * g j * h k) := by
  rw [show c * (∑ i ∈ s, f i) * (∑ j ∈ s, g j) * (∑ k ∈ s, h k)
        = c * ((∑ i ∈ s, f i) * (∑ j ∈ s, g j) * (∑ k ∈ s, h k)) by ring]
  rw [iterm_sum3]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

/-- **GM (7.3)**, pointwise form: the integrand of the statement is the triple `t`-sum of the
products of `itermFp` factors. -/
lemma iterm_integrand_eq_sum (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (u : ℝ × ℝ × ℝ) :
    (Real.fourierChar (-((N : ℝ) * ((m.1 : ℝ) * u.1 + (m.2.1 : ℝ) * u.2.1 +
          (m.2.2 : ℝ) * u.2.2))) : ℂ) *
        ((Submission.LargeValues.bumpW u.1 : ℂ) ^ 2 * (Submission.LargeValues.bumpW u.2.1 : ℂ) ^ 2 *
          (Submission.LargeValues.bumpW u.2.2 : ℂ) ^ 2) *
        Submission.GM.Rfun W (u.1 / u.2.2) * Submission.GM.Rfun W (u.2.1 / u.1) *
        Submission.GM.Rfun W (u.2.2 / u.2.1)
      = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
            itermFp N (t₃ - t₁) m.2.2 u.2.2 := by
  by_cases h : Submission.LargeValues.bumpW u.1 ≠ 0 ∧ Submission.LargeValues.bumpW u.2.1 ≠ 0 ∧
      Submission.LargeValues.bumpW u.2.2 ≠ 0
  · obtain ⟨h1, h2, h3⟩ := h
    have hu1 := iterm_bumpW_pos_of_ne h1
    have hu2 := iterm_bumpW_pos_of_ne h2
    have hu3 := iterm_bumpW_pos_of_ne h3
    rw [iterm_Rfun_eq_sum W (div_ne_zero (ne_of_gt hu1) (ne_of_gt hu3)),
      iterm_Rfun_eq_sum W (div_ne_zero (ne_of_gt hu2) (ne_of_gt hu1)),
      iterm_Rfun_eq_sum W (div_ne_zero (ne_of_gt hu3) (ne_of_gt hu2))]
    rw [iterm_const_mul_sum3]
    apply Finset.sum_congr rfl
    intro t₁ _
    apply Finset.sum_congr rfl
    intro t₂ _
    apply Finset.sum_congr rfl
    intro t₃ _
    exact iterm_summand_eq N m t₁ t₂ t₃ u.1 u.2.1 u.2.2 hu1 hu2 hu3
  · rcases (not_and_or.mp h) with h | h
    · have h0 : Submission.LargeValues.bumpW u.1 = 0 := not_not.mp h
      simp [itermFp, h0]
    · rcases (not_and_or.mp h) with h | h
      · have h0 : Submission.LargeValues.bumpW u.2.1 = 0 := not_not.mp h
        simp [itermFp, h0]
      · have h0 : Submission.LargeValues.bumpW u.2.2 = 0 := not_not.mp h
        simp [itermFp, h0]

/-- `itermFp N d m` is continuous on the support `[1,2]` of the bump (where `log |u|` is
continuous). -/
lemma iterm_continuousOn_Fp (N : ℕ) (d : ℝ) (m : ℤ) :
    ContinuousOn (itermFp N d m) (Set.Icc 1 2) := by
  intro u hu
  have hu0 : u ≠ 0 := by
    have h := hu.1
    linarith
  have hlog : ContinuousAt (fun x : ℝ => Real.log |x|) u :=
    (Real.continuousAt_log (abs_ne_zero.mpr hu0)).comp continuous_abs.continuousAt
  have hZp : ContinuousAt (fun x : ℝ => itermZp x d) u := by
    simp only [itermZp]
    refine (Complex.continuous_exp.continuousAt).comp ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    refine (Complex.continuous_ofReal.continuousAt).comp ?_
    exact hlog.mul continuousAt_const
  have h1 : ContinuousAt
      (fun x : ℝ => ((Real.fourierChar (-(x * ((m : ℝ) * (N : ℝ)))) : Circle) : ℂ)) u := by
    fun_prop
  have h2 : ContinuousAt (fun x : ℝ => (Submission.LargeValues.bumpW x : ℂ)) u :=
    Complex.continuous_ofReal.continuousAt.comp
      Submission.LargeValues.bumpW_contDiff.continuous.continuousAt
  have h3 : ContinuousAt (fun x : ℝ => (Submission.LargeValues.bumpW x : ℂ) ^ 2) u := h2.pow 2
  have h4 : ContinuousWithinAt
      (fun x : ℝ => ((Real.fourierChar (-(x * ((m : ℝ) * (N : ℝ)))) : Circle) : ℂ) *
        ((Submission.LargeValues.bumpW x : ℂ) ^ 2 * itermZp x d)) (Set.Icc 1 2) u :=
    (h1.mul (h3.mul hZp)).continuousWithinAt
  change ContinuousWithinAt
    (fun x : ℝ => ((Real.fourierChar (-(x * ((m : ℝ) * (N : ℝ)))) : Circle) : ℂ) *
      ((Submission.LargeValues.bumpW x : ℂ) ^ 2) * itermZp x d) (Set.Icc 1 2) u
  simpa only [mul_assoc] using h4

/-- `itermFp N d m` vanishes off `[1,2]`. -/
lemma iterm_support_Fp (N : ℕ) (d : ℝ) (m : ℤ) :
    Function.support (itermFp N d m) ⊆ Set.Icc 1 2 := by
  rw [Function.support_subset_iff']
  intro x hx
  have hw : Submission.LargeValues.bumpW x = 0 :=
    Submission.LargeValues.bumpW_eq_zero_of_notMem hx
  simp [itermFp, hw]

/-- `itermFp N d m` is integrable on `ℝ`. -/
lemma iterm_integrable_Fp (N : ℕ) (d : ℝ) (m : ℤ) : Integrable (itermFp N d m) volume := by
  rw [← integrableOn_iff_integrable_of_support_subset (iterm_support_Fp N d m)]
  exact (iterm_continuousOn_Fp N d m).integrableOn_compact isCompact_Icc

/-- The integrand of the triple integral is integrable. -/
lemma iterm_integrable_term (N : ℕ) (d₁ d₂ d₃ : ℝ) (m₁ m₂ m₃ : ℤ) :
    Integrable (fun u : ℝ × ℝ × ℝ =>
      itermFp N d₁ m₁ u.1 * itermFp N d₂ m₂ u.2.1 * itermFp N d₃ m₃ u.2.2) := by
  have h23 : Integrable (fun y : ℝ × ℝ => itermFp N d₂ m₂ y.1 * itermFp N d₃ m₃ y.2) :=
    Integrable.mul_prod (iterm_integrable_Fp N d₂ m₂) (iterm_integrable_Fp N d₃ m₃)
  have h123 : Integrable (fun u : ℝ × ℝ × ℝ =>
      itermFp N d₁ m₁ u.1 * (itermFp N d₂ m₂ u.2.1 * itermFp N d₃ m₃ u.2.2)) :=
    Integrable.mul_prod (iterm_integrable_Fp N d₁ m₁) h23
  simpa only [mul_assoc] using h123

/-- `hhat d ξ` as the integral of `e(-uξ) w(u)² u^{id}`. -/
lemma iterm_hhat_eq_integral (d ξ : ℝ) :
    Submission.GM.hhat d ξ = ∫ u, ((Real.fourierChar (-(u * ξ)) : Circle) : ℂ) *
      ((Submission.LargeValues.bumpW u : ℂ) ^ 2) * (u : ℂ) ^ (Complex.I * (d : ℂ)) := by
  rw [Submission.GM.hhat, Real.fourier_eq]
  simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul, Submission.GM.hfun,
    Complex.ofReal_pow]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  ring

/-- On positive reals, `u^{id} = itermZp u d`. -/
lemma iterm_cpow_eq_Zp_of_pos {u d : ℝ} (hu : 0 < u) :
    (u : ℂ) ^ (Complex.I * (d : ℂ)) = itermZp u d := by
  rw [itermZp_eq_cpow (ne_of_gt hu) d, abs_of_pos hu]

/-- `hhat d ξ` as the integral of `e(-uξ) w(u)² |u|^{id}` (`u^{id}` and `|u|^{id}` agree on the
support of `w`, and off it the bump factor vanishes). -/
lemma iterm_hhat_eq_integral_Zp (d ξ : ℝ) :
    Submission.GM.hhat d ξ = ∫ u, ((Real.fourierChar (-(u * ξ)) : Circle) : ℂ) *
      ((Submission.LargeValues.bumpW u : ℂ) ^ 2) * itermZp u d := by
  rw [iterm_hhat_eq_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  by_cases h : Submission.LargeValues.bumpW u = 0
  · simp [h]
  · rw [iterm_cpow_eq_Zp_of_pos (iterm_bumpW_pos_of_ne h)]

/-- The values of `hhat` occurring in `Iterm` are integrals of `itermFp`. -/
lemma iterm_hhat_eq_Fp (N : ℕ) (d : ℝ) (m : ℤ) :
    Submission.GM.hhat d ((m : ℝ) * (N : ℝ)) = ∫ u, itermFp N d m u := by
  rw [iterm_hhat_eq_integral_Zp]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  simp only [itermFp]

/-- Fubini for the product of three functions of one variable (no integrability hypotheses). -/
lemma iterm_integral_prod3 (f g h : ℝ → ℂ) :
    ∫ u : ℝ × ℝ × ℝ, f u.1 * g u.2.1 * h u.2.2 = (∫ u, f u) * (∫ u, g u) * (∫ u, h u) := by
  simp only [mul_assoc]
  rw [MeasureTheory.Measure.volume_eq_prod ℝ (ℝ × ℝ)]
  rw [MeasureTheory.integral_prod_mul (f := f) (g := fun y : ℝ × ℝ => g y.1 * h y.2)]
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.integral_prod_mul (f := g) (g := h)]

/-- The summand of `Iterm` is the triple integral of the corresponding product of `itermFp`'s. -/
lemma iterm_per_summand (N : ℕ) (m : ℤ × ℤ × ℤ) (t₁ t₂ t₃ : ℝ) :
    Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * (N : ℝ)) *
        Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * (N : ℝ)) *
        Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * (N : ℝ))
      = ∫ u : ℝ × ℝ × ℝ,
          itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
            itermFp N (t₃ - t₁) m.2.2 u.2.2 := by
  rw [iterm_hhat_eq_Fp, iterm_hhat_eq_Fp, iterm_hhat_eq_Fp]
  exact (iterm_integral_prod3 _ _ _).symm

/-- Exchange of the finite triple `t`-sum with the integral. -/
lemma iterm_integral_sum3 (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    ∫ u : ℝ × ℝ × ℝ, (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
          itermFp N (t₃ - t₁) m.2.2 u.2.2)
      = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ∫ u : ℝ × ℝ × ℝ,
            itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
              itermFp N (t₃ - t₁) m.2.2 u.2.2 := by
  have h1 : ∀ t₁ ∈ W, Integrable (fun u : ℝ × ℝ × ℝ => ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
        itermFp N (t₃ - t₁) m.2.2 u.2.2) := by
    intro t₁ _
    exact integrable_finsetSum W (f := fun t₂ => fun u : ℝ × ℝ × ℝ => ∑ t₃ ∈ W,
      itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
        itermFp N (t₃ - t₁) m.2.2 u.2.2)
      (fun t₂ _ => integrable_finsetSum W
        (f := fun t₃ => fun u : ℝ × ℝ × ℝ =>
          itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
            itermFp N (t₃ - t₁) m.2.2 u.2.2)
        (fun t₃ _ => iterm_integrable_term N (t₁ - t₂) (t₂ - t₃) (t₃ - t₁) m.1 m.2.1 m.2.2))
  rw [integral_finsetSum W (f := fun t₁ => fun u : ℝ × ℝ × ℝ => ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
        itermFp N (t₃ - t₁) m.2.2 u.2.2) h1]
  apply Finset.sum_congr rfl
  intro t₁ _
  have h2 : ∀ t₂ ∈ W, Integrable (fun u : ℝ × ℝ × ℝ => ∑ t₃ ∈ W,
      itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
        itermFp N (t₃ - t₁) m.2.2 u.2.2) :=
    fun t₂ _ => integrable_finsetSum W
      (f := fun t₃ => fun u : ℝ × ℝ × ℝ =>
        itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
          itermFp N (t₃ - t₁) m.2.2 u.2.2)
      (fun t₃ _ => iterm_integrable_term N (t₁ - t₂) (t₂ - t₃) (t₃ - t₁) m.1 m.2.1 m.2.2)
  rw [integral_finsetSum W (f := fun t₂ => fun u : ℝ × ℝ × ℝ => ∑ t₃ ∈ W,
      itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
        itermFp N (t₃ - t₁) m.2.2 u.2.2) h2]
  apply Finset.sum_congr rfl
  intro t₂ _
  rw [integral_finsetSum W (f := fun t₃ => fun u : ℝ × ℝ × ℝ =>
      itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
        itermFp N (t₃ - t₁) m.2.2 u.2.2)
    (fun t₃ _ => iterm_integrable_term N (t₁ - t₂) (t₂ - t₃) (t₃ - t₁) m.1 m.2.1 m.2.2)]

/-- **GM (7.3)**: the integral representation of `Iterm`. Expanding
`hhat t ξ = ∫ e(-ξu) (w(u)^2 u^{it}) du` in the definition of `Iterm` and summing the finite
`t`-sums gives, using `Σ_{t₁,t₂,t₃}(u₁/u₃)^{it₁}(u₂/u₁)^{it₂}(u₃/u₂)^{it₃}
= R(u₁/u₃)R(u₂/u₁)R(u₃/u₂)`,

`Iterm N W m = N^3 ∫_{ℝ³} e(-N(m₁u₁+m₂u₂+m₃u₃)) w(u₁)^2 w(u₂)^2 w(u₃)^2
                     R(u₁/u₃)R(u₂/u₁)R(u₃/u₂) du₁du₂du₃`.

The two sides are equal pointwise: on the support of `w(u₁)w(u₂)w(u₃)` all `u_i ∈ [1,2]` are positive
(so `|u_i/u_j| = u_i/u_j` in `Rfun`), and where some `w(u_i) = 0` both sides vanish.

Proof: exchange the finite `t`-sums with the integral (`integral_finset_sum`; each term is integrable
since `hfun` is bounded with compact support), `Real.fourier_eq`, `Complex.cpow_add`/`cpow_sub` for
non-zero positive reals, and `Finset.sum_mul_sum` to factor the triple sum. -/
theorem Iterm_eq_integral (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    Submission.GM.Iterm N W m = (N : ℂ) ^ 3 *
      ∫ u : ℝ × ℝ × ℝ,
        (Real.fourierChar (-((N : ℝ) * ((m.1 : ℝ) * u.1 + (m.2.1 : ℝ) * u.2.1 +
            (m.2.2 : ℝ) * u.2.2))) : ℂ) *
          ((Submission.LargeValues.bumpW u.1 : ℂ) ^ 2 * (Submission.LargeValues.bumpW u.2.1 : ℂ) ^ 2 *
            (Submission.LargeValues.bumpW u.2.2 : ℂ) ^ 2) *
          Submission.GM.Rfun W (u.1 / u.2.2) * Submission.GM.Rfun W (u.2.1 / u.1) *
          Submission.GM.Rfun W (u.2.2 / u.2.1) := by
  have key : (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * (N : ℝ)) *
          Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * (N : ℝ)) *
          Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * (N : ℝ))) =
      ∫ u : ℝ × ℝ × ℝ,
        (Real.fourierChar (-((N : ℝ) * ((m.1 : ℝ) * u.1 + (m.2.1 : ℝ) * u.2.1 +
            (m.2.2 : ℝ) * u.2.2))) : ℂ) *
          ((Submission.LargeValues.bumpW u.1 : ℂ) ^ 2 * (Submission.LargeValues.bumpW u.2.1 : ℂ) ^ 2 *
            (Submission.LargeValues.bumpW u.2.2 : ℂ) ^ 2) *
          Submission.GM.Rfun W (u.1 / u.2.2) * Submission.GM.Rfun W (u.2.1 / u.1) *
          Submission.GM.Rfun W (u.2.2 / u.2.1) := by
    have hA : (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * (N : ℝ)) *
            Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * (N : ℝ)) *
            Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * (N : ℝ))) =
        ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ∫ u : ℝ × ℝ × ℝ,
            itermFp N (t₁ - t₂) m.1 u.1 * itermFp N (t₂ - t₃) m.2.1 u.2.1 *
              itermFp N (t₃ - t₁) m.2.2 u.2.2 := by
      apply Finset.sum_congr rfl
      intro t₁ _
      apply Finset.sum_congr rfl
      intro t₂ _
      apply Finset.sum_congr rfl
      intro t₃ _
      exact iterm_per_summand N m t₁ t₂ t₃
    rw [hA]
    refine (iterm_integral_sum3 N W m).symm.trans ?_
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    exact (iterm_integrand_eq_sum N W m u).symm
  rw [Submission.GM.Iterm, key]

end Work.GM.S3
