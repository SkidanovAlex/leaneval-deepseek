import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.JPrelim
import Submission.Work.Diff.STE.B3.scoeff_add_of_support
import Submission.Work.Diff.STE.Lead.KSBP.Defs
import Submission.Work.Diff.STE.Lead.KSBP.sbp_bound
import Submission.Work.Diff.STE.Lead.KSBP.diff_mass_le
import Submission.Work.Diff.STE.Lead.KSBP.psi_integral_shift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L^∞ → L^∞` bound for the Friedrichs truncation `STruncR`

`Work.Diff.STE.Lead.STruncR_sup_le`: the real Fourier multiplier `trunc ρ ε` (with `ρ` smooth and
compactly supported) is bounded on `L^∞` *uniformly in `ε ∈ (0,1]`*.  The proof isolates the kernel
`Work.Diff.STE.Lead.KSBP.kernel ρ ε`, expands `STruncR` as the pairing of `f`'s periodisation with
the kernel, and uses summation by parts (`Work.Diff.STE.Lead.KSBP.sbp_bound`) plus the second-order
difference estimate (`Work.Diff.STE.Lead.KSBP.diff_mass_le`) to bound the `L¹` norm of the kernel
uniformly in `ε` (the weight `KSBP.psi` and `KSBP.psi_integral_shift`).

All auxiliary lemmas of this file are private to it (they are prefixed `stl_` and live in the
sub-namespace `KSBP` to avoid any clash with the vocabulary modules).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.Diff.STE.Lead.KSBP

-- children's statements, as yet unproved



/-- The support of the coefficient family `coef ρ ε` is finite. -/
lemma stl_coef_support_finite {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hρ0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) :
    (Function.support (coef ρ ε)).Finite := by
  refine Set.Finite.subset (s := (↑(Work.Diff.STE.B3.truncBox (n := n) ε) : Set (Fin n → ℤ)))
    (Work.Diff.STE.B3.truncBox (n := n) ε).finite_toSet ?_
  intro m hm
  by_contra hmb
  have h0 := Work.Diff.STE.B3.trunc_eq_zero_of_notMem_truncBox (n := n) ρ ε hε hρ0
    (fun _ : Fin n → ℤ => (1 : ℂ)) m hmb
  have harg : (fun i : Fin n => ε * (m i : ℝ)) = (ε • fun i : Fin n => (m i : ℝ)) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
  have hcoe : coef ρ ε m = Work.Diff.STE.trunc ρ ε (fun _ : Fin n → ℤ => (1 : ℂ)) m := by
    rw [coef, Work.Diff.STE.trunc, harg]
    simp
  have hmne : coef ρ ε m ≠ 0 := Function.mem_support.mp hm
  rw [hcoe, h0] at hmne
  exact hmne rfl

/-- **Pointwise bound for the truncated kernel.** -/
theorem stl_kernel_pointwise {n : ℕ} (ρ : (Fin n → ℝ) → ℝ)
    (hρ : ∀ y : Fin n → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x : Fin n → ℝ,
      ‖kernel ρ ε x‖ ≤ C * ε⁻¹ ^ n * ∏ i, psi ε (x i) := by
  obtain ⟨Cb, hCb, hbound⟩ := diff_mass_le (n := n) ρ hρ hρ0 hρs
  refine ⟨Cb, hCb, ?_⟩
  intro ε hεmem x
  obtain ⟨hεpos, hεle⟩ := hεmem
  set l : List (Fin n) := (List.finRange n).filter
    (fun i => decide (¬ (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ < 4 * ε)))
    with hl
  set F : Finset (Fin n) := l.toFinset with hF
  have hmem_l : ∀ i : Fin n, i ∈ l ↔
      ¬ (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ < 4 * ε) := by
    intro i
    rw [hl, List.mem_filter]
    constructor
    · intro h; exact decide_eq_true_iff.mp h.2
    · intro h; exact ⟨List.mem_finRange i, decide_eq_true_iff.mpr h⟩
  have hmem_F : ∀ i : Fin n, i ∈ F ↔
      ¬ (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ < 4 * ε) := by
    intro i
    rw [hF, List.mem_toFinset, hmem_l]
  have hfar : ∀ i ∈ F, 4 * ε ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ :=
    fun i hi => not_lt.mp ((hmem_F i).mp hi)
  have hnear : ∀ i, i ∉ F → ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ < 4 * ε :=
    fun i hi => by
      by_contra hc
      exact hi ((hmem_F i).mpr hc)
  have hnz : ∀ i ∈ F, (0:ℝ) < ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ := by
    intro i hi
    have h4 : (0:ℝ) < 4 * ε := by linarith
    linarith [hfar i hi]
  have hpsi_eq : ∀ i ∈ F, psi ε (x i)
      = (4 * ε / ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖) ^ 2 := by
    intro i hi
    rw [psi, if_neg]
    exact not_lt.mpr (hfar i hi)
  have hpsi_one : ∀ i, i ∉ F → psi ε (x i) = 1 := by
    intro i hi
    rw [psi, if_pos (hnear i hi)]
  -- list bookkeeping
  have hnodup : l.Nodup := by
    rw [hl]
    exact (List.nodup_finRange n).filter _
  have hlen : l.length ≤ n := by
    have h := List.length_filter_le
      (fun i : Fin n => decide (¬ (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ < 4 * ε)))
      (List.finRange n)
    rw [hl]
    simpa [List.length_finRange] using h
  have hcard : F.card = l.length := List.toFinset_card_of_nodup hnodup
  have hx_ne : ∀ i ∈ l, Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) ≠ 1 := by
    intro i hi h1
    have h2 : (0:ℝ) < 4 * ε := by linarith
    have h3 : ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ = 0 := by rw [h1]; simp
    have h4 := not_lt.mp ((hmem_l i).mp hi)
    linarith
  have hsbp := sbp_bound (n := n) (coef ρ ε) l x (stl_coef_support_finite (n := n) ρ hεpos hρ0) hx_ne
  have hmass := hbound ε ⟨hεpos, hεle⟩ l hlen
  -- products
  have hprod_l : (l.map (fun i =>
        (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹)).prod
      = ∏ i ∈ F, (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹ := by
    rw [hF, List.prod_toFinset _ hnodup]
  have hprod_psi : ∏ i, psi ε (x i) = ∏ i ∈ F, psi ε (x i) := by
    have h := Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => i ∈ F) (f := fun i => psi ε (x i))
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter] at h
    have h1 : ∏ i ∈ (Finset.univ : Finset (Fin n)) with ¬ (i ∈ F), psi ε (x i) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      exact hpsi_one i (by simpa using hi)
    rw [h1, mul_one] at h
    exact h.symm
  -- the key estimate
  have hkey : (∏ i ∈ F, (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹)
      * ε ^ (2 * l.length) ≤ ∏ i ∈ F, psi ε (x i) := by
    rw [← hcard, pow_mul, ← Finset.prod_const (s := F) (b := ε ^ 2),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
    · exact mul_nonneg (by positivity) (pow_nonneg hεpos.le 2)
    · have h2 : (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹ * ε ^ 2
          = (ε / ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖) ^ 2 := by
        rw [div_pow, div_eq_mul_inv, mul_comm]
      rw [h2, hpsi_eq i hi]
      have hpos := hnz i hi
      have h1 : ε / ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖
          ≤ 4 * ε / ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ := by
        rw [div_le_div_iff_of_pos_right hpos]; linarith
      have h2' : (0:ℝ) ≤ ε / ‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ :=
        div_nonneg (le_of_lt hεpos) (le_of_lt hpos)
      nlinarith [h1, h2']
  calc ‖kernel ρ ε x‖
      = ‖∑' m : Fin n → ℤ, coef ρ ε m * Work.Diff.STE.fourierExp m x‖ := rfl
    _ ≤ (l.map (fun i =>
          (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹)).prod
          * ∑' m : Fin n → ℤ, ‖diffL l (coef ρ ε) m‖ := hsbp
    _ ≤ (l.map (fun i =>
          (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹)).prod
          * (Cb * ε ^ (2 * l.length) * ε⁻¹ ^ n) := by
        refine mul_le_mul_of_nonneg_left hmass ?_
        rw [hprod_l]
        exact Finset.prod_nonneg fun i _ => by positivity
    _ = Cb * ε⁻¹ ^ n
          * ((∏ i ∈ F, (‖Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ)) - 1‖ ^ 2)⁻¹)
              * ε ^ (2 * l.length)) := by
        rw [hprod_l]; ring
    _ ≤ Cb * ε⁻¹ ^ n * ∏ i ∈ F, psi ε (x i) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = Cb * ε⁻¹ ^ n * ∏ i, psi ε (x i) := by rw [hprod_psi]

/-- The weight `psi ε` is measurable. -/
lemma stl_measurable_psi (ε : ℝ) : Measurable (psi ε) := by
  unfold psi
  have hc : Measurable (fun t : ℝ => ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖) :=
    (by fun_prop (disch := simp) : Continuous _).measurable
  refine Measurable.ite
    (p := fun t : ℝ => ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖ < 4 * ε)
    ?_ measurable_const ?_
  · exact measurableSet_lt hc measurable_const
  · exact (measurable_const.div hc).pow_const 2

lemma stl_psi_nonneg (ε t : ℝ) : 0 ≤ psi ε t := by
  rw [psi]; split_ifs <;> positivity

lemma stl_psi_le_one {ε t : ℝ} (hε : 0 ≤ ε) : psi ε t ≤ 1 := by
  rw [psi]
  split_ifs with h
  · exact le_rfl
  · have hle : 4 * ε ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖ := not_lt.mp h
    rcases eq_or_lt_of_le (norm_nonneg (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1)) with hc | hc
    · rw [← hc, div_zero]; norm_num
    · have h1 : 4 * ε / ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖ ≤ 1 :=
        (div_le_one hc).mpr hle
      have h2 : 0 ≤ 4 * ε / ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖ :=
        div_nonneg (by linarith) hc.le
      nlinarith

/-- **`L¹` bound for the shifted kernel.** -/
theorem stl_kernel_shift_L1 {n : ℕ} (ρ : (Fin n → ℝ) → ℝ)
    (hρ : ∀ y : Fin n → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ z : Fin n → ℝ,
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖kernel ρ ε (z - x)‖ ≤ C := by
  obtain ⟨C₀, hC₀, hpt⟩ := stl_kernel_pointwise (n := n) ρ hρ hρ0 hρs
  refine ⟨C₀ * 4 ^ n, by positivity, ?_⟩
  intro ε hεmem z
  obtain ⟨hεpos, hεle⟩ := hεmem
  have hεnn : (0:ℝ) ≤ ε := le_of_lt hεpos
  have hpt' : ∀ x : Fin n → ℝ,
      ‖kernel ρ ε (z - x)‖ ≤ C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i) := by
    intro x
    have h := hpt ε ⟨hεpos, hεle⟩ (z - x)
    simpa [Pi.sub_apply] using h
  have hgmeas : Measurable (fun x : Fin n → ℝ => C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)) := by
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_prod _ (fun i _ => ?_)
    exact (stl_measurable_psi ε).comp (by fun_prop)
  have hgbound : ∀ x : Fin n → ℝ,
      ‖C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)‖ ≤ C₀ * ε⁻¹ ^ n := by
    intro x
    have hphi1 : ∏ i : Fin n, psi ε (z i - x i) ≤ 1 := by
      rw [← Finset.prod_const_one (s := (Finset.univ : Finset (Fin n)))]
      exact Finset.prod_le_prod₀ (fun i _ => stl_psi_nonneg _ _) (fun i _ => stl_psi_le_one hεnn)
    have hphi0 : 0 ≤ ∏ i : Fin n, psi ε (z i - x i) :=
      Finset.prod_nonneg (fun i _ => stl_psi_nonneg _ _)
    have hc0 : 0 ≤ C₀ * ε⁻¹ ^ n := mul_nonneg hC₀ (pow_nonneg (inv_nonneg.mpr hεnn) n)
    rw [norm_mul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg hphi0]
    exact mul_le_of_le_one_right hc0 hphi1
  have hgint : MeasureTheory.IntegrableOn
      (fun x : Fin n → ℝ => C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i))
      (Work.Diff.STE.unitCube (ι := Fin n)) volume := by
    refine MeasureTheory.IntegrableOn.of_bound (C := C₀ * ε⁻¹ ^ n) ?_
      hgmeas.aestronglyMeasurable ?_
    · rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
      simp
    · filter_upwards with x using hgbound x
  have hmono : ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖kernel ρ ε (z - x)‖
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hgint ?_
    · filter_upwards with x using norm_nonneg _
    · filter_upwards with x using hpt' x
  have hconst : ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)
      = C₀ * ε⁻¹ ^ n * ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ∏ i, psi ε (z i - x i) :=
    MeasureTheory.integral_const_mul _ _
  have hpsi := psi_integral_shift (n := n) hεpos hεle z
  calc ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖kernel ρ ε (z - x)‖
      ≤ C₀ * ε⁻¹ ^ n * ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ∏ i, psi ε (z i - x i) := by
        rw [← hconst]; exact hmono
    _ ≤ C₀ * ε⁻¹ ^ n * (4 * ε) ^ n := by
        refine mul_le_mul_of_nonneg_left hpsi (mul_nonneg hC₀ ?_)
        exact pow_nonneg (inv_nonneg.mpr hεnn) n
    _ = C₀ * 4 ^ n := by
        rw [mul_assoc]
        have h4 : ε⁻¹ ^ n * (4 * ε) ^ n = 4 ^ n := by
          rw [← mul_pow]
          have : ε⁻¹ * (4 * ε) = 4 := by field_simp
          rw [this]
        rw [h4]


/-- The characters have modulus one. -/
lemma stl_norm_fourierExp_eq_one {n : ℕ} (m : Fin n → ℤ) (x : Fin n → ℝ) :
    ‖Work.Diff.STE.fourierExp m x‖ = 1 := by
  rw [Work.Diff.STE.fourierExp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((m i : ℤ) : ℂ) * ((x i : ℝ) : ℂ))
      = (((2 * Real.pi * ∑ i, ((m i : ℤ) : ℝ) * x i : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- `e_m(z) · e_{-m}(x) = e_m(z - x)`. -/
lemma stl_fourierExp_mul_neg_sub {n : ℕ} (m : Fin n → ℤ) (z x : Fin n → ℝ) :
    Work.Diff.STE.fourierExp m z * Work.Diff.STE.fourierExp (-m) x
      = Work.Diff.STE.fourierExp m (z - x) := by
  rw [Work.Diff.STE.fourierExp, Work.Diff.STE.fourierExp, Work.Diff.STE.fourierExp,
    ← Complex.exp_add]
  congr 1
  have h : (∑ i, ((m i : ℤ) : ℂ) * ((z - x) i : ℂ))
      = (∑ i, ((m i : ℤ) : ℂ) * (z i : ℂ))
        + ∑ i, (((-m) i : ℤ) : ℂ) * (x i : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Pi.neg_apply]
    push_cast
    ring
  rw [h]
  ring

/-- `e_{-m}(x) · e_m(x) = 1`. -/
lemma stl_fourierExp_neg_mul_self {n : ℕ} (m : Fin n → ℤ) (x : Fin n → ℝ) :
    Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.fourierExp m x = 1 := by
  have h := stl_fourierExp_mul_neg_sub (m := -m) (z := x) (x := x)
  rw [neg_neg] at h
  rw [h, sub_self, Work.Diff.STE.fourierExp]
  simp

/-- `coef ρ ε` vanishes off the finite box `truncBox ε`. -/
lemma stl_coef_eq_zero_of_notMem_truncBox {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hρ0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) {m : Fin n → ℤ}
    (hm : m ∉ Work.Diff.STE.B3.truncBox (n := n) ε) : coef ρ ε m = 0 := by
  have h0 := Work.Diff.STE.B3.trunc_eq_zero_of_notMem_truncBox (n := n) ρ ε hε hρ0
    (fun _ : Fin n → ℤ => (1 : ℂ)) m hm
  have harg : (fun i : Fin n => ε * (m i : ℝ)) = (ε • fun i : Fin n => (m i : ℝ)) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
  have hcoe : coef ρ ε m = Work.Diff.STE.trunc ρ ε (fun _ : Fin n → ℤ => (1 : ℂ)) m := by
    rw [coef, Work.Diff.STE.trunc, harg]
    simp
  rw [hcoe, h0]

/-- **The norm of the periodisation is bounded by the sup norm of `f`** (for `f` supported in the
open unit cube). -/
lemma stl_perFun_norm_le {n : ℕ} (f : (Fin n → ℝ) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z, |f z| ≤ M)
    (hsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ∀ y, ‖Work.Diff.STE.B3.perFun f y‖ ≤ M := by
  intro y
  rw [Work.Diff.STE.B3.perFun]
  by_cases h : ∃ k : Fin n → ℤ, f (y + Work.Diff.STE.iVec k) ≠ 0
  · obtain ⟨k₀, hk₀⟩ := h
    have hsingle : ∀ k : Fin n → ℤ, k ≠ k₀ →
        ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ) = 0 := by
      intro k hk
      by_contra hne
      have hmem1 : y + Work.Diff.STE.iVec k ∈
          Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
        hsupp (by simpa [Function.mem_support] using hne)
      have hmem0 : y + Work.Diff.STE.iVec k₀ ∈
          Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
        hsupp (by simpa [Function.mem_support] using hk₀)
      apply hk
      funext i
      have hb1 := Set.mem_pi.mp hmem1 i (Set.mem_univ i)
      have hb0 := Set.mem_pi.mp hmem0 i (Set.mem_univ i)
      simp only [Set.mem_Ioo, Pi.add_apply, Work.Diff.STE.iVec_apply] at hb1 hb0
      have h3 : ((k i - k₀ i : ℤ) : ℝ) = (y i + (k i : ℝ)) - (y i + (k₀ i : ℝ)) := by
        push_cast
        ring
      have h4 : |((k i - k₀ i : ℤ) : ℝ)| < 1 := by
        rw [h3, abs_lt]
        exact ⟨by linarith [hb1.1, hb0.2], by linarith [hb1.2, hb0.1]⟩
      have h5 : ((|k i - k₀ i| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h4
      have h6 : |k i - k₀ i| < (1 : ℤ) := by exact_mod_cast h5
      exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp h6)
    rw [tsum_eq_single k₀ hsingle]
    simpa using hf (y + Work.Diff.STE.iVec k₀)
  · push_neg at h
    have hzero : (∑' k : Fin n → ℤ, ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)) = 0 := by
      have hz : (fun k : Fin n → ℤ => ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)) = fun _ => 0 := by
        funext k
        rw [h k, Complex.ofReal_zero]
      rw [hz, tsum_zero]
    rw [hzero, norm_zero]
    exact hM

/-- **The pairing with the truncated kernel is bounded by `M` times the `L¹` norm of the kernel.** -/
theorem stl_pairing_le {n : ℕ} (ρ : (Fin n → ℝ) → ℝ)
    (hρ : ∀ y : Fin n → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : (Fin n → ℝ) → ℂ) (M : ℝ), 0 ≤ M →
      (∀ x, ‖g x‖ ≤ M) → ∀ z : Fin n → ℝ,
      ‖∫ x in Work.Diff.STE.unitCube (ι := Fin n), kernel ρ ε (z - x) * g x‖ ≤ C * M := by
  obtain ⟨C₀, hC₀, hpt⟩ := stl_kernel_pointwise (n := n) ρ hρ hρ0 hρs
  refine ⟨C₀ * 4 ^ n, by positivity, ?_⟩
  intro ε hεmem g M hM hg z
  obtain ⟨hεpos, hεle⟩ := hεmem
  have hεnn : (0:ℝ) ≤ ε := le_of_lt hεpos
  have hpt' : ∀ x : Fin n → ℝ,
      ‖kernel ρ ε (z - x)‖ ≤ C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i) := by
    intro x
    have h := hpt ε ⟨hεpos, hεle⟩ (z - x)
    simpa [Pi.sub_apply] using h
  have hgmeas : Measurable (fun x : Fin n → ℝ => C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)) := by
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_prod _ (fun i _ => ?_)
    exact (stl_measurable_psi ε).comp (measurable_const.sub (measurable_pi_apply i))
  have hgbound : ∀ x : Fin n → ℝ,
      ‖C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)‖ ≤ C₀ * ε⁻¹ ^ n := by
    intro x
    have hphi1 : ∏ i : Fin n, psi ε (z i - x i) ≤ 1 := by
      rw [← Finset.prod_const_one (s := (Finset.univ : Finset (Fin n)))]
      exact Finset.prod_le_prod₀ (fun i _ => stl_psi_nonneg _ _) (fun i _ => stl_psi_le_one hεnn)
    have hphi0 : 0 ≤ ∏ i : Fin n, psi ε (z i - x i) :=
      Finset.prod_nonneg (fun i _ => stl_psi_nonneg _ _)
    have hc0 : 0 ≤ C₀ * ε⁻¹ ^ n := mul_nonneg hC₀ (pow_nonneg (inv_nonneg.mpr hεnn) n)
    rw [norm_mul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg hphi0]
    exact mul_le_of_le_one_right hc0 hphi1
  have hgint : MeasureTheory.IntegrableOn
      (fun x : Fin n → ℝ => C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i))
      (Work.Diff.STE.unitCube (ι := Fin n)) volume := by
    refine MeasureTheory.IntegrableOn.of_bound (C := C₀ * ε⁻¹ ^ n) ?_
      hgmeas.aestronglyMeasurable ?_
    · rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
      simp
    · filter_upwards with x using hgbound x
  have hint2 : MeasureTheory.IntegrableOn
      (fun x : Fin n → ℝ => M * (C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)))
      (Work.Diff.STE.unitCube (ι := Fin n)) volume :=
    MeasureTheory.Integrable.const_mul hgint M
  have hmono : ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖kernel ρ ε (z - x)‖ * ‖g x‖
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          M * (C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hint2 ?_
    · filter_upwards with x using mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · filter_upwards with x
      have h1 := hpt' x
      have h2 := hg x
      have h3 : (0:ℝ) ≤ C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i) :=
        le_trans (norm_nonneg _) h1
      calc ‖kernel ρ ε (z - x)‖ * ‖g x‖
          ≤ (C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)) * M := mul_le_mul h1 h2 (norm_nonneg _) h3
        _ = M * (C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)) := by ring
  have hconst : ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        M * (C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i))
      = M * (C₀ * ε⁻¹ ^ n * ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ∏ i, psi ε (z i - x i)) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hpsi := psi_integral_shift (n := n) hεpos hεle z
  calc ‖∫ x in Work.Diff.STE.unitCube (ι := Fin n), kernel ρ ε (z - x) * g x‖
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖kernel ρ ε (z - x) * g x‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖kernel ρ ε (z - x)‖ * ‖g x‖ := by
        simp only [norm_mul]
    _ ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          M * (C₀ * ε⁻¹ ^ n * ∏ i, psi ε (z i - x i)) := hmono
    _ = M * (C₀ * ε⁻¹ ^ n * ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ∏ i, psi ε (z i - x i)) := hconst
    _ ≤ M * (C₀ * ε⁻¹ ^ n * (4 * ε) ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        refine mul_le_mul_of_nonneg_left hpsi (mul_nonneg hC₀ ?_)
        exact pow_nonneg (inv_nonneg.mpr hεnn) n
    _ = C₀ * 4 ^ n * M := by
        have h4 : ε⁻¹ ^ n * (4 * ε) ^ n = 4 ^ n := by
          rw [← mul_pow]
          have h5 : ε⁻¹ * (4 * ε) = 4 := by field_simp
          rw [h5]
        rw [show M * (C₀ * ε⁻¹ ^ n * (4 * ε) ^ n)
            = M * (C₀ * (ε⁻¹ ^ n * (4 * ε) ^ n)) by ring, h4]
        ring



end Work.Diff.STE.Lead.KSBP

namespace Work.Diff.STE.Lead

/-- **Main theorem (scratch name).** -/
theorem STruncR_sup_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (M : ℝ), 0 ≤ M →
        (∀ z : Fin (Module.finrank ℝ E) → ℝ, |f z| ≤ M) →
        (Function.support f ⊆ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
          Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) →
        ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          |Work.Diff.STE.B3Data.STruncR ρ ε f z| ≤ C * M := by
  obtain ⟨C, hC, hpair⟩ := KSBP.stl_pairing_le (n := Module.finrank ℝ E) ρ hρ hρ0 hρs
  refine ⟨C, hC, ?_⟩
  intro ε hεmem f M hM hf hsupp z
  obtain ⟨hεpos, hεle⟩ := hεmem
  -- the box of frequencies
  have hexp : Work.Diff.STE.B3Data.STruncR ρ ε f z
      = (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
          (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.B3.perCoeff f m
            * Work.Diff.STE.fourierExp m z).re := by
    rw [Work.Diff.STE.B3.STruncR_eq_sum (E := E) ρ ε hεpos hρ0 f z, Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Work.Diff.STE.trunc]
  -- the kernel is the finite sum over the box
  have hkernel : ∀ x : Fin (Module.finrank ℝ E) → ℝ,
      Work.Diff.STE.Lead.KSBP.kernel ρ ε (z - x)
        = ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
            (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m (z - x) := by
    intro x
    rw [Work.Diff.STE.Lead.KSBP.kernel]
    refine tsum_eq_sum (s := Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε)
      (fun m hm => ?_)
    rw [Work.Diff.STE.Lead.KSBP.stl_coef_eq_zero_of_notMem_truncBox (ε := ε) ρ hεpos hρ0 hm,
      zero_mul]
  by_cases hInt : MeasureTheory.Integrable (Work.Diff.STE.B3.perFun f)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E))))
  · -- the good case: `STruncR` is the pairing of the kernel with the periodisation
    have hid : Work.Diff.STE.B3Data.STruncR ρ ε f z
        = (∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            Work.Diff.STE.Lead.KSBP.kernel ρ ε (z - x) * Work.Diff.STE.B3.perFun f x).re := by
      rw [hexp]
      have hcoeff : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
          Work.Diff.STE.B3.perCoeff f m
            = ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
                Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x := fun m => rfl
      have hSint : ∀ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
          MeasureTheory.Integrable
            (fun x : Fin (Module.finrank ℝ E) → ℝ =>
              (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
                * (Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x))
            (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) := by
        intro m _
        have hcont : Continuous (Work.Diff.STE.fourierExp (-m)) :=
          Work.Diff.STE.B3.continuous_fourierExp (E := E) (-m)
        have hbdd : ∀ᵐ x ∂(volume.restrict
            (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))),
            ‖Work.Diff.STE.fourierExp (-m) x‖ ≤ 1 :=
          Filter.Eventually.of_forall fun x => by rw [KSBP.stl_norm_fourierExp_eq_one]
        have hmul := hInt.mul_bdd hcont.aestronglyMeasurable hbdd
        have hmul' : MeasureTheory.Integrable
            (fun x : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x)
            (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) :=
          hmul.congr (Filter.Eventually.of_forall fun x => by ring)
        exact MeasureTheory.Integrable.const_mul hmul' _
      congr 1
      rw [show (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
            (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.B3.perCoeff f m
              * Work.Diff.STE.fourierExp m z)
          = ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
              ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
                (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
                  * (Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x) from by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hcoeff m]
        rw [show (ρ (ε • (fun i => (m i : ℝ))) : ℂ)
              * (∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
                  Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x)
              * Work.Diff.STE.fourierExp m z
            = ((ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z)
              * ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
                  Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x by ring,
          ← MeasureTheory.integral_const_mul]]
      rw [← MeasureTheory.integral_finsetSum _ hSint]
      rw [show (∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
              (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
                * (Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x))
          = ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
              (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
                (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
                  * Work.Diff.STE.fourierExp (-m) x) * Work.Diff.STE.B3.perFun f x from by
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun x => ?_)
        show (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
              (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
                * (Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x))
            = (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
                (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
                  * Work.Diff.STE.fourierExp (-m) x) * Work.Diff.STE.B3.perFun f x
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring]
      rw [show (∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
              (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
                (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
                  * Work.Diff.STE.fourierExp (-m) x) * Work.Diff.STE.B3.perFun f x)
          = ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
              Work.Diff.STE.Lead.KSBP.kernel ρ ε (z - x) * Work.Diff.STE.B3.perFun f x from by
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun x => ?_)
        show (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
                (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
                  * Work.Diff.STE.fourierExp (-m) x) * Work.Diff.STE.B3.perFun f x
            = Work.Diff.STE.Lead.KSBP.kernel ρ ε (z - x) * Work.Diff.STE.B3.perFun f x
        rw [hkernel x]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [show (ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierExp m z
              * Work.Diff.STE.fourierExp (-m) x
            = (ρ (ε • (fun i => (m i : ℝ))) : ℂ)
              * (Work.Diff.STE.fourierExp m z * Work.Diff.STE.fourierExp (-m) x) by ring,
          KSBP.stl_fourierExp_mul_neg_sub]]
    rw [hid]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    exact hpair ε ⟨hεpos, hεle⟩ (Work.Diff.STE.B3.perFun f) M hM
      (KSBP.stl_perFun_norm_le f M hM hf hsupp) z
  · -- the bad case: the coefficients all vanish
    have hcoeffzero : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
        Work.Diff.STE.B3.perCoeff f m = 0 := by
      intro m
      have hcoe : Work.Diff.STE.B3.perCoeff f m
          = ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
              Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x := rfl
      rw [hcoe]
      refine MeasureTheory.integral_undef ?_
      intro hint
      have hcont : Continuous (Work.Diff.STE.fourierExp m) :=
        Work.Diff.STE.B3.continuous_fourierExp (E := E) m
      have hbdd : ∀ᵐ x ∂(volume.restrict
          (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))),
          ‖Work.Diff.STE.fourierExp m x‖ ≤ 1 :=
        Filter.Eventually.of_forall fun x => by rw [KSBP.stl_norm_fourierExp_eq_one]
      have hprod := hint.mul_bdd hcont.aestronglyMeasurable hbdd
      have hfin : MeasureTheory.Integrable (Work.Diff.STE.B3.perFun f)
          (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) :=
        hprod.congr (Filter.Eventually.of_forall fun x => by
          change Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x
              * Work.Diff.STE.fourierExp m x = Work.Diff.STE.B3.perFun f x
          rw [show Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.B3.perFun f x
                * Work.Diff.STE.fourierExp m x
              = (Work.Diff.STE.fourierExp (-m) x * Work.Diff.STE.fourierExp m x)
                * Work.Diff.STE.B3.perFun f x by ring,
            KSBP.stl_fourierExp_neg_mul_self m x, one_mul])
      exact hInt hfin
    rw [hexp, Finset.sum_eq_zero (fun m _ => by rw [hcoeffzero m]; ring), Complex.zero_re,
      abs_zero]
    exact mul_nonneg hC hM

end Work.Diff.STE.Lead
