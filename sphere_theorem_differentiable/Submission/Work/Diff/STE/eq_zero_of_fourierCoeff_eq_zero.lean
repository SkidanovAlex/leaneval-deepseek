import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.trigPoly_dense_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A continuous periodic function with vanishing Fourier coefficients is zero

Layer A of the STE Fourier toolkit: the Fourier coefficients on the unit cube determine a
continuous `1`-periodic function `h : (ι → ℝ) → ℂ`.

The proof is the standard `L²` density argument, on top of `trigPoly_dense_L2` (density of the
trigonometric polynomials in `L²` of the cube `unitCube = (0,1]^ι`).  Writing
`A = ∫_{unitCube} ‖h‖²` and `T` for a trigonometric polynomial, `hcoef` gives

  `∫_{unitCube} conj T · h = 0`,

so the expansion `‖h - T‖² = ‖h‖² - 2 Re(conj T · h) + ‖T‖²` gives
`A ≤ ∫_{unitCube} ‖h - T‖²`, and since `T` can be chosen with `∫ ‖h - T‖² < ε²` for every
`ε > 0`, we get `A ≤ 0`, i.e. `A = 0`.  Continuity then upgrades `A = 0` to `h ≡ 0` (a nonempty
open set has positive Lebesgue measure), and `1`-periodicity spreads this from the closed cube
`[0,1]^ι` to all of `ι → ℝ`.

The auxiliary lemmas are:

* `integrableOn_unitCube_of_continuous_real`, `integrableOn_unitCube_of_continuous_cplx` :
  a continuous function is integrable on the bounded cube;
* `conj_fourierExp` : `conj (fourierExp k x) = fourierExp (-k) x`;
* `integral_re_eq` : `∫ Re f = Re ∫ f`;
* `integral_re_conj_trigPoly_mul_eq_zero` : `h` is orthogonal (real part) to every
  trigonometric polynomial;
* `integral_normSq_sub_eq` : the expansion of `∫ ‖h - T‖²`;
* `eq_zero_on_closedCube_of_integral_normSq_eq_zero` : positivity of Lebesgue measure of open
  sets: a continuous function whose `L²` norm on the cube vanishes vanishes on the closed cube;
* `eq_zero_of_eq_zero_on_closedCube` : invariance under integer translations.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators Filter
open scoped ComplexConjugate ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Integrability on the unit cube -/

omit [DecidableEq ι] in
/-- A continuous real-valued function is integrable on the (bounded) unit cube. -/
lemma integrableOn_unitCube_of_continuous_real {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict unitCube) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

omit [DecidableEq ι] in
/-- A continuous complex-valued function is integrable on the (bounded) unit cube. -/
lemma integrableOn_unitCube_of_continuous_cplx {F : (ι → ℝ) → ℂ} (hF : Continuous F) :
    Integrable F (volume.restrict unitCube) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

/-! ## Conjugation of the characters -/

omit [DecidableEq ι] in
/-- The characters are unitary: the conjugate of `fourierExp k` is `fourierExp (-k)`. -/
lemma conj_fourierExp (k : ι → ℤ) (x : ι → ℝ) :
    conj (fourierExp k x) = fourierExp (-k) x := by
  have hSre : conj (∑ i, ((k i : ℤ) : ℂ) * ((x i : ℝ) : ℂ))
      = ∑ i, ((k i : ℤ) : ℂ) * ((x i : ℝ) : ℂ) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hS' : (∑ i, (((-k) i : ℤ) : ℂ) * ((x i : ℝ) : ℂ))
      = -(∑ i, ((k i : ℤ) : ℂ) * ((x i : ℝ) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.neg_apply]
  simp only [fourierExp]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat]
  rw [hSre, hS']
  ring

/-! ## The real part of a complex integral -/

omit [DecidableEq ι] in
/-- The real part of an integral is the integral of the real part. -/
lemma integral_re_eq (f : (ι → ℝ) → ℂ) (hf : Integrable f (volume.restrict unitCube)) :
    ∫ x in unitCube, (f x).re = (∫ x in unitCube, f x).re := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
  simpa only [Complex.reCLM_apply] using h

/-! ## Orthogonality to the trigonometric polynomials -/

omit [DecidableEq ι] in
/-- A continuous function all of whose Fourier coefficients vanish is orthogonal (in real part)
to every trigonometric polynomial. -/
theorem integral_re_conj_trigPoly_mul_eq_zero
    (h : (ι → ℝ) → ℂ) (hh : Continuous h)
    (hcoef : ∀ k : ι → ℤ, fourierCoeff h k = 0) (p : (ι → ℤ) →₀ ℂ) :
    ∫ x in unitCube, (conj (∑ k ∈ p.support, p k * fourierExp k x) * h x).re = 0 := by
  have hconj : ∀ x : ι → ℝ, conj (∑ k ∈ p.support, p k * fourierExp k x) * h x
      = ∑ k ∈ p.support, conj (p k) * (fourierExp (-k) x * h x) := by
    intro x
    have h1 : conj (∑ k ∈ p.support, p k * fourierExp k x)
        = ∑ k ∈ p.support, conj (p k) * fourierExp (-k) x := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, conj_fourierExp]
    rw [h1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsumint : Integrable
      (fun x : ι → ℝ => ∑ k ∈ p.support, conj (p k) * (fourierExp (-k) x * h x))
      (volume.restrict unitCube) := by
    refine integrableOn_unitCube_of_continuous_cplx ?_
    refine continuous_finsetSum _ fun k _ => Continuous.mul continuous_const ?_
    exact (continuous_fourierExp (-k)).mul hh
  have hterm : ∀ k ∈ p.support, Integrable
      (fun x : ι → ℝ => conj (p k) * (fourierExp (-k) x * h x))
      (volume.restrict unitCube) := by
    intro k _
    refine integrableOn_unitCube_of_continuous_cplx ?_
    exact Continuous.mul continuous_const ((continuous_fourierExp (-k)).mul hh)
  calc ∫ x in unitCube, (conj (∑ k ∈ p.support, p k * fourierExp k x) * h x).re
      = ∫ x in unitCube,
          ((∑ k ∈ p.support, conj (p k) * (fourierExp (-k) x * h x))).re :=
        integral_congr_ae (Eventually.of_forall fun x => congrArg Complex.re (hconj x))
    _ = (∫ x in unitCube,
          (∑ k ∈ p.support, conj (p k) * (fourierExp (-k) x * h x))).re :=
        integral_re_eq _ hsumint
    _ = (∑ k ∈ p.support, conj (p k) * fourierCoeff h k).re := by
        congr 1
        rw [integral_finsetSum p.support hterm]
        exact Finset.sum_congr rfl fun k _ => by
          rw [integral_const_mul]
          rfl
    _ = 0 := by simp [hcoef]

/-! ## The expansion of `∫ ‖h - T‖²` -/

omit [DecidableEq ι] in
/-- The `L²` expansion of a difference: `∫‖h - T‖² = ∫‖h‖² - 2 Re ∫ conj(T) h + ∫‖T‖²`. -/
theorem integral_normSq_sub_eq (h T : (ι → ℝ) → ℂ) (hh : Continuous h) (hT : Continuous T) :
    ∫ x in unitCube, ‖h x - T x‖ ^ 2
      = (∫ x in unitCube, ‖h x‖ ^ 2)
        - 2 * (∫ x in unitCube, (conj (T x) * h x).re)
        + ∫ x in unitCube, ‖T x‖ ^ 2 := by
  have hpt : ∀ x : ι → ℝ,
      ‖h x - T x‖ ^ 2 = ‖h x‖ ^ 2 - 2 * (conj (T x) * h x).re + ‖T x‖ ^ 2 := by
    intro x
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub, mul_comm (h x) (conj (T x))]
    ring
  have hint1 : Integrable (fun x : ι → ℝ => ‖h x‖ ^ 2) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous_real (hh.norm.pow 2)
  have hint2 : Integrable (fun x : ι → ℝ => ‖T x‖ ^ 2) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous_real (hT.norm.pow 2)
  have hint3 : Integrable (fun x : ι → ℝ => (conj (T x) * h x).re)
      (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous_real
      (Complex.continuous_re.comp ((Complex.continuous_conj.comp hT).mul hh))
  have h1 : (∫ x in unitCube, ‖h x - T x‖ ^ 2)
      = (∫ x in unitCube, (‖h x‖ ^ 2 - 2 * (conj (T x) * h x).re + ‖T x‖ ^ 2)) :=
    integral_congr_ae (Eventually.of_forall hpt)
  have h2 : (∫ x in unitCube, (‖h x‖ ^ 2 - 2 * (conj (T x) * h x).re + ‖T x‖ ^ 2))
      = (∫ x in unitCube, (‖h x‖ ^ 2 - 2 * (conj (T x) * h x).re))
        + (∫ x in unitCube, ‖T x‖ ^ 2) :=
    integral_add (f := fun x : ι → ℝ => ‖h x‖ ^ 2 - 2 * (conj (T x) * h x).re)
      (g := fun x : ι → ℝ => ‖T x‖ ^ 2) (hint1.sub (hint3.const_mul 2)) hint2
  have h3 : (∫ x in unitCube, (‖h x‖ ^ 2 - 2 * (conj (T x) * h x).re))
      = (∫ x in unitCube, ‖h x‖ ^ 2)
        - (∫ x in unitCube, 2 * (conj (T x) * h x).re) :=
    integral_sub (f := fun x : ι → ℝ => ‖h x‖ ^ 2)
      (g := fun x : ι → ℝ => 2 * (conj (T x) * h x).re) hint1 (hint3.const_mul 2)
  have h4 : (∫ x in unitCube, 2 * (conj (T x) * h x).re)
      = 2 * (∫ x in unitCube, (conj (T x) * h x).re) :=
    integral_const_mul 2 (fun x : ι → ℝ => (conj (T x) * h x).re)
  rw [h1, h2, h3, h4]

/-! ## Vanishing on the closed cube -/

omit [DecidableEq ι] in
/-- A continuous function whose `L²` norm over the unit cube vanishes is `0` on the closed cube:
a nonempty open set has positive Lebesgue measure. -/
theorem eq_zero_on_closedCube_of_integral_normSq_eq_zero
    (h : (ι → ℝ) → ℂ) (hh : Continuous h)
    (hint : ∫ x in unitCube, ‖h x‖ ^ 2 = 0) :
    ∀ x ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0:ℝ) 1), h x = 0 := by
  intro x hxcube
  by_contra hxne
  have hfcont : Continuous fun z : ι → ℝ => ‖h z‖ ^ 2 := hh.norm.pow 2
  set m : ℝ := ‖h x‖ ^ 2 / 2 with hm
  have hmpos : 0 < m := by rw [hm]; linarith [pow_pos (norm_pos_iff.mpr hxne) 2]
  have hev : ∀ᶠ z in nhds x, m < ‖h z‖ ^ 2 :=
    ContinuousAt.eventually_lt continuousAt_const hfcont.continuousAt (by rw [hm]; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hxcl : x ∈ closure (Set.pi Set.univ (fun _ : ι => Set.Ioo (0:ℝ) 1)) := by
    rw [closure_pi_set]
    intro i _
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact (Set.mem_univ_pi.mp hxcube) i
  have hne : (Metric.ball x (r/2) ∩ Set.pi Set.univ (fun _ : ι => Set.Ioo (0:ℝ) 1)).Nonempty :=
    mem_closure_iff.mp hxcl _ Metric.isOpen_ball (Metric.mem_ball_self (by linarith))
  obtain ⟨y, hy⟩ := hne
  rw [Set.mem_inter_iff] at hy
  obtain ⟨hyball, hycube⟩ := hy
  have hyball' : dist y x < r/2 := Metric.mem_ball.mp hyball
  have hy_open : ∀ i, y i ∈ Set.Ioo (0:ℝ) 1 := fun i => Set.mem_univ_pi.mp hycube i
  set ρ : ι → ℝ := fun i => min (r/4) ((min (y i) (1 - y i)) / 2) with hρ
  have hρpos : ∀ i, 0 < ρ i := by
    intro i
    have h2 : 0 < min (y i) (1 - y i) := lt_min (hy_open i).1 (by linarith [(hy_open i).2])
    simp only [hρ]
    exact lt_min (by linarith) (by linarith)
  have hρ_le_r : ∀ i, ρ i ≤ r / 4 := by
    intro i; simp only [hρ]; exact min_le_left _ _
  have hρ_le_y : ∀ i, ρ i ≤ (y i) / 2 := by
    intro i; simp only [hρ]
    calc min (r/4) ((min (y i) (1 - y i))/2) ≤ (min (y i) (1 - y i))/2 := min_le_right _ _
      _ ≤ y i / 2 := by linarith [min_le_left (y i) (1 - y i)]
  have hρ_le_one : ∀ i, ρ i ≤ (1 - y i) / 2 := by
    intro i; simp only [hρ]
    calc min (r/4) ((min (y i) (1 - y i))/2) ≤ (min (y i) (1 - y i))/2 := min_le_right _ _
      _ ≤ (1 - y i) / 2 := by linarith [min_le_right (y i) (1 - y i)]
  set B : Set (ι → ℝ) := Set.pi Set.univ fun i => Set.Ioo (y i - ρ i) (y i + ρ i) with hB
  have hBmeas : MeasurableSet B := by
    rw [hB]; exact MeasurableSet.univ_pi fun i => measurableSet_Ioo
  have hBsub_cube : B ⊆ unitCube := by
    intro z hz
    rw [hB] at hz
    rw [Set.mem_univ_pi] at hz
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    have h1 := hz i
    exact ⟨by linarith [h1.1, hρ_le_y i, (hy_open i).1],
           by linarith [h1.2, hρ_le_one i, (hy_open i).2]⟩
  have hBsub_ball : B ⊆ Metric.ball x r := by
    intro z hz
    rw [hB] at hz
    have hzi : ∀ i, dist (z i) (y i) < r / 4 := by
      intro i
      have h1 := hz i (Set.mem_univ i)
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [h1.1, hρ_le_r i], by linarith [h1.2, hρ_le_r i]⟩
    have hzy : dist z y ≤ r / 4 :=
      le_of_lt ((dist_pi_lt_iff (by linarith : (0:ℝ) < r / 4)).mpr hzi)
    rw [Metric.mem_ball]
    linarith [dist_triangle z y x, hyball']
  have hf_on_B : ∀ z ∈ B, m < ‖h z‖ ^ 2 := fun z hz => hball (hBsub_ball hz)
  have hvolB : volume B = ∏ i, ENNReal.ofReal (2 * ρ i) := by
    rw [hB, Real.volume_pi_Ioo]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (y i + ρ i) - (y i - ρ i) = 2 * ρ i by ring]
  have hvolB_ne_top : volume B ≠ ⊤ := by
    have hle : volume B ≤ volume unitCube := measure_mono hBsub_cube
    rw [volume_unitCube] at hle
    exact ne_of_lt (lt_of_le_of_lt hle (by norm_num))
  have hvolB_ne_zero : volume B ≠ 0 := by
    rw [hvolB, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [hρpos i])]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Finset.prod_pos fun i _ => by linarith [hρpos i]))
  have hvolBpos : 0 < (volume B).toReal := ENNReal.toReal_pos hvolB_ne_zero hvolB_ne_top
  have hInt_uc : IntegrableOn (fun z : ι → ℝ => ‖h z‖ ^ 2) unitCube volume :=
    integrableOn_unitCube_of_continuous_real hfcont
  have hInt_B : IntegrableOn (fun z : ι → ℝ => ‖h z‖ ^ 2) B volume :=
    hInt_uc.mono_set hBsub_cube
  have hm_ass : (∫ z in B, m) ≤ ∫ z in B, ‖h z‖ ^ 2 :=
    setIntegral_mono_on (integrableOn_const (μ := volume) (s := B) hvolB_ne_top) hInt_B hBmeas
      (fun z hz => le_of_lt (hf_on_B z hz))
  have hm_val : (∫ z in B, m) = m * (volume B).toReal := by
    rw [integral_const]
    simp [Measure.real_def]
    ring
  have hB_le : (∫ z in B, ‖h z‖ ^ 2) ≤ ∫ z in unitCube, ‖h z‖ ^ 2 :=
    setIntegral_mono_set hInt_uc (Eventually.of_forall fun z => sq_nonneg _)
      (Eventually.of_forall fun z hz => hBsub_cube hz)
  have hBpos : 0 < ∫ z in B, ‖h z‖ ^ 2 := by
    have h1 := hm_ass
    rw [hm_val] at h1
    linarith [mul_pos hmpos hvolBpos]
  have : 0 < ∫ z in unitCube, ‖h z‖ ^ 2 := lt_of_lt_of_le hBpos hB_le
  rw [hint] at this
  exact lt_irrefl 0 this

/-! ## Periodicity: from the closed cube to the whole space -/

/-- A `1`-periodic function that vanishes on the closed cube vanishes everywhere. -/
theorem eq_zero_of_eq_zero_on_closedCube
    (h : (ι → ℝ) → ℂ) (hper : Periodic1 h)
    (h0 : ∀ x ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0:ℝ) 1), h x = 0) :
    ∀ x, h x = 0 := by
  intro x
  have hper_int : ∀ (m : ι → ℤ) (u : ι → ℝ), h (u + (fun i => (m i : ℝ))) = h u := by
    intro m u
    have hvi : ∀ i : ι, Function.Periodic h ((m i : ℝ) • (Pi.single i 1 : ι → ℝ)) := by
      intro i
      have hz : Function.Periodic h ((m i) • (Pi.single i 1 : ι → ℝ)) :=
        Function.Periodic.zsmul (hper i) (m i)
      rwa [← Int.cast_smul_eq_zsmul ℝ (m i) (Pi.single i 1 : ι → ℝ)] at hz
    have hsum : ∀ s : Finset ι,
        Function.Periodic h (∑ i ∈ s, (m i : ℝ) • (Pi.single i 1 : ι → ℝ)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro y; simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          intro y
          rw [← add_assoc, ih (y + (m a : ℝ) • (Pi.single a 1 : ι → ℝ)), hvi a y]
    have hvec : (∑ i : ι, (m i : ℝ) • (Pi.single i 1 : ι → ℝ)) = fun i => (m i : ℝ) := by
      funext j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp only [Ne.symm hb, ite_false, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have := hsum Finset.univ
    rw [hvec] at this
    exact this u
  set v : ι → ℝ := fun i => Int.fract (x i) with hv
  have hv_mem : v ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0:ℝ) 1) := by
    intro i _
    rw [hv]
    exact ⟨Int.fract_nonneg (x i), le_of_lt (Int.fract_lt_one (x i))⟩
  have hx : x = v + fun i => ((⌊x i⌋ : ℤ) : ℝ) := by
    funext i
    show x i = v i + _
    rw [hv]
    exact (Int.fract_add_floor (x i)).symm
  have hxy : h x = h v := by
    conv_lhs => rw [hx]
    exact hper_int _ v
  rw [hxy]
  exact h0 v hv_mem

/-! ## The main theorem -/

theorem eq_zero_of_fourierCoeff_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : (ι → ℝ) → ℂ) (hh : Continuous h) (hper : Work.Diff.STE.Periodic1 h)
    (hcoef : ∀ k : ι → ℤ, Work.Diff.STE.fourierCoeff h k = 0) :
    ∀ x, h x = 0 := by
  have hint : Integrable (fun x : ι → ℝ => ‖h x‖ ^ 2) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous_real (hh.norm.pow 2)
  have hmain : ∫ x in unitCube, ‖h x‖ ^ 2 = 0 := by
    refine le_antisymm ?_ (integral_nonneg fun x => sq_nonneg _)
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have hδ1 : (0:ℝ) < min δ 1 := lt_min hδ zero_lt_one
    obtain ⟨p, hp⟩ := trigPoly_dense_L2 h hint hδ1
    set T : (ι → ℝ) → ℂ := fun x => ∑ k ∈ p.support, p k * fourierExp k x with hT
    have hpT : (∫ x in unitCube, ‖h x - T x‖ ^ 2) < (min δ 1) ^ 2 := by
      simpa only [hT] using hp
    have hTcont : Continuous T := by
      rw [hT]
      exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_fourierExp k)
    have hczero : (∫ x in unitCube, (conj (T x) * h x).re) = 0 := by
      rw [hT]
      exact integral_re_conj_trigPoly_mul_eq_zero h hh hcoef p
    have hexp := integral_normSq_sub_eq h T hh hTcont
    rw [hczero] at hexp
    have hBnn : 0 ≤ ∫ x in unitCube, ‖T x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
    have h3 : (min δ 1) ^ 2 ≤ δ := by
      have hpos : 0 ≤ min δ 1 := le_of_lt hδ1
      have hle1 : min δ 1 ≤ 1 := min_le_right δ 1
      nlinarith [hpos, hle1, min_le_left δ 1]
    linarith
  have hcube := eq_zero_on_closedCube_of_integral_normSq_eq_zero h hh hmain
  exact eq_zero_of_eq_zero_on_closedCube h hper hcube

end Work.Diff.STE
