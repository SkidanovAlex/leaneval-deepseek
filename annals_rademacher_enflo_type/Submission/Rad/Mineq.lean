import Submission.Rad.Main
import Submission.Rad.EType
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal BigOperators Interval
noncomputable section
namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Right multiplication by `ξ` is a bijection of the cube (it is an involution). -/
lemma sum_comp_mulΩ {n : ℕ} (F : Ω n → ℝ) (ξ : Ω n) :
    (∑ x : Ω n, F (mulΩ x ξ)) = ∑ y : Ω n, F y := by
  exact Fintype.sum_bijective (fun x : Ω n => mulΩ x ξ)
    (by
      constructor
      · intro a b h
        exact mulΩ_injective ξ (by simpa [mulΩ_comm] using h)
      · simpa [mulΩ_comm] using mulΩ_surjective ξ)
    (fun x : Ω n => F (mulΩ x ξ)) F (fun x => rfl)

/-- Pointwise (in `x`) bound: the smooth integrand is controlled by the biased expectation. -/
lemma Jsmooth_pow_le_biased_sum {n : ℕ} (f : Ω n → X) (x : Ω n) {pow : ℝ} (hp1 : 1 ≤ pow)
    (θ : ℝ) (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    ‖Jsmooth θ f x‖ ^ pow ≤
      ∑ ξ : Ω n, biasW θ ξ *
        ‖(∑ j : Fin n, (delta θ ξ j) • (D j f) (mulΩ x ξ))‖ ^ pow := by
  have hsin : Real.sin θ ≠ 0 := ne_of_gt (sin_pos_on_Ioc θ hθ)
  calc
    ‖Jsmooth θ f x‖ ^ pow = ‖Jint θ f x‖ ^ pow := by
          rw [Jint_eq_Jsmooth_on f x θ hθ]
    _ ≤ (∫ ξ : Ω n, ‖Wfun θ f x ξ‖ ^ pow ∂(biasedMeasure (n := n) θ)) := by
          exact Jint_pow_le_expW f x hp1 θ hsin
    _ = ∑ ξ : Ω n, biasW θ ξ * ‖Wfun θ f x ξ‖ ^ pow := by
          rw [integral_biased_eq θ (fun ξ : Ω n => ‖Wfun θ f x ξ‖ ^ pow)]
          simp
    _ = ∑ ξ : Ω n, biasW θ ξ *
          ‖(∑ j : Fin n, (delta θ ξ j) • (D j f) (mulΩ x ξ))‖ ^ pow := by
          rfl



/-- Pointwise bound in `θ ∈ (0, π/2]` for the smooth weighted integrand. -/
lemma pointwise_bound {n : ℕ} (hn : 1 ≤ n) (f : Ω n → X) {pow : ℝ} (hp1 : 1 ≤ pow) (hp2 : pow ≤ 2)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hRad : ∀ (m : ℕ), 1 ≤ m → ∀ x : Fin m → X,
      (∑ ε : Ω m, ((1 / 2 : ℝ) ^ m) * ‖∑ j : Fin m, (((ε j : C) : ℝ) • x j)‖ ^ pow)
        ≤ c ^ pow * (∑ j : Fin m, ‖x j‖ ^ pow))
    (θ : ℝ) (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    (∑ x : Ω n, ((1 / 2 : ℝ) ^ n) * ‖Jsmooth θ f x‖ ^ pow)
      ≤ (2 : ℝ) ^ (pow / 2) * c ^ pow * (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow)) := by
  have hs0 : 0 < Real.sin θ := sin_pos_on_Ioc θ hθ
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  let w : ℝ := (1 / 2 : ℝ) ^ n
  have hw : 0 ≤ w := by positivity
  let inner : Ω n → Ω n → ℝ := fun x ξ =>
    biasW θ ξ * ‖(∑ j : Fin n, (delta θ ξ j) • (D j f) (mulΩ x ξ))‖ ^ pow
  let g : Ω n → Ω n → ℝ := fun y ξ =>
    biasW θ ξ * ‖(∑ j : Fin n, (delta θ ξ j) • (D j f) y)‖ ^ pow
  have hxbound : ∀ x : Ω n, ‖Jsmooth θ f x‖ ^ pow ≤ ∑ ξ : Ω n, inner x ξ := by
    intro x
    exact Jsmooth_pow_le_biased_sum f x hp1 θ hθ
  have hbt : ∀ y : Ω n,
      (∑ ξ : Ω n, g y ξ)
        ≤ (2 : ℝ) ^ (pow / 2) * c ^ pow * (∑ j : Fin n, ‖(D j f) y‖ ^ pow) := by
    intro y
    unfold g
    exact biased_type_le (n := n) hn θ hs0 hs1 (fun j : Fin n => (D j f) y) (pow := pow) hp1 hp2
      (c := c) hc0 hRad
  calc
    (∑ x : Ω n, w * ‖Jsmooth θ f x‖ ^ pow)
        ≤ ∑ x : Ω n, w * (∑ ξ : Ω n, inner x ξ) := by
            apply Finset.sum_le_sum
            intro x hxmem
            exact mul_le_mul_of_nonneg_left (hxbound x) hw
    _ = ∑ x : Ω n, ∑ ξ : Ω n, w * inner x ξ := by
            apply Finset.sum_congr rfl
            intro x hxmem
            exact Finset.mul_sum (s := Finset.univ) (f := fun ξ : Ω n => inner x ξ) (a := w)
    _ = ∑ ξ : Ω n, ∑ x : Ω n, w * inner x ξ := by
            exact Finset.sum_comm
    _ = ∑ ξ : Ω n, ∑ y : Ω n, w * g y ξ := by
            apply Finset.sum_congr rfl
            intro ξ hξmem
            calc
              (∑ x : Ω n, w * inner x ξ) = ∑ x : Ω n, w * g (mulΩ x ξ) ξ := by rfl
              _ = ∑ y : Ω n, w * g y ξ := sum_comp_mulΩ (fun z : Ω n => w * g z ξ) ξ
    _ = ∑ y : Ω n, ∑ ξ : Ω n, w * g y ξ := by
            exact Finset.sum_comm
    _ = ∑ y : Ω n, w * (∑ ξ : Ω n, g y ξ) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact (Finset.mul_sum (s := Finset.univ) (f := fun ξ : Ω n => g y ξ) (a := w)).symm
    _ ≤ ∑ y : Ω n, w * ((2 : ℝ) ^ (pow / 2) * c ^ pow * (∑ j : Fin n, ‖(D j f) y‖ ^ pow)) := by
            apply Finset.sum_le_sum
            intro y hy
            exact mul_le_mul_of_nonneg_left (hbt y) hw
    _ = (2 : ℝ) ^ (pow / 2) * c ^ pow * (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow)) := by
          calc
            (∑ y : Ω n, w * ((2 : ℝ) ^ (pow / 2) * c ^ pow * (∑ j : Fin n, ‖(D j f) y‖ ^ pow)))
                = ∑ y : Ω n, ((2 : ℝ) ^ (pow / 2) * c ^ pow) * (w * ∑ j : Fin n, ‖(D j f) y‖ ^ pow) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
            _ = ((2 : ℝ) ^ (pow / 2) * c ^ pow) * (∑ y : Ω n, w * ∑ j : Fin n, ‖(D j f) y‖ ^ pow) := by
                    exact (Finset.mul_sum (s := Finset.univ)
                      (f := fun y : Ω n => w * ∑ j : Fin n, ‖(D j f) y‖ ^ pow)
                      (a := ((2 : ℝ) ^ (pow / 2) * c ^ pow))).symm
            _ = ((2 : ℝ) ^ (pow / 2) * c ^ pow) * (∑ j : Fin n, ∑ y : Ω n, w * ‖(D j f) y‖ ^ pow) := by
                    congr 1
                    calc
                      (∑ y : Ω n, w * (∑ j : Fin n, ‖(D j f) y‖ ^ pow))
                          = ∑ y : Ω n, ∑ j : Fin n, w * ‖(D j f) y‖ ^ pow := by
                              apply Finset.sum_congr rfl
                              intro y hy
                              exact Finset.mul_sum (s := Finset.univ) (f := fun j : Fin n => ‖(D j f) y‖ ^ pow) (a := w)
                      _ = ∑ j : Fin n, ∑ y : Ω n, w * ‖(D j f) y‖ ^ pow := by
                              exact Finset.sum_comm
            _ = ((2 : ℝ) ^ (pow / 2) * c ^ pow) * (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow)) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro j hj
                    exact (meanReal_eq_sum (fun x : Ω n => ‖D j f x‖ ^ pow)).symm

/-- The main dimension-free inequality (real form, uniform expectation over the cube):
`E‖f - Ef‖^pow ≤ (π/2)^pow 2^(pow/2) c^pow Σ_j E‖D_j f‖^pow`. -/
lemma main_ineq {n : ℕ} (hn : 1 ≤ n) (f : Ω n → X) {pow : ℝ} (hp1 : 1 ≤ pow) (hp2 : pow ≤ 2)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hRad : ∀ (m : ℕ), 1 ≤ m → ∀ x : Fin m → X,
      (∑ ε : Ω m, ((1 / 2 : ℝ) ^ m) * ‖∑ j : Fin m, (((ε j : C) : ℝ) • x j)‖ ^ pow)
        ≤ c ^ pow * (∑ j : Fin m, ‖x j‖ ^ pow)) :
    meanReal (fun x : Ω n => ‖f x - meanX f‖ ^ pow)
      ≤ (Real.pi / 2) ^ pow * (2 : ℝ) ^ (pow / 2) * c ^ pow *
          (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow)) := by
  have hp0 : 0 ≤ pow := by linarith
  let w : ℝ := (1 / 2 : ℝ) ^ n
  have hw : 0 ≤ w := by positivity
  let C0 : ℝ := (2 : ℝ) ^ (pow / 2) * c ^ pow *
      (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow))
  have hint_x : ∀ x : Ω n, Integrable (fun θ : ℝ => w * ‖Jsmooth θ f x‖ ^ pow) thetaMeasure := by
    intro x
    exact (integrable_norm_Jsmooth_pow f x hp0).const_mul w
  have hintG : Integrable (fun θ : ℝ => ∑ x : Ω n, w * ‖Jsmooth θ f x‖ ^ pow) thetaMeasure := by
    exact integrable_finsetSum (s := (Finset.univ : Finset (Ω n)))
      (f := fun (x : Ω n) (θ : ℝ) => w * ‖Jsmooth θ f x‖ ^ pow) (by intro x hxmem; exact hint_x x)
  have hintC : Integrable (fun _ : ℝ => C0) thetaMeasure := integrable_const C0
  have hae : ∀ᵐ θ : ℝ ∂thetaMeasure, (∑ x : Ω n, w * ‖Jsmooth θ f x‖ ^ pow) ≤ C0 := by
    rw [MeasureTheory.ae_iff]
    have hsub : {θ : ℝ | ¬ (∑ x : Ω n, w * ‖Jsmooth θ f x‖ ^ pow) ≤ C0} ⊆
        {θ : ℝ | θ ∉ Set.Ioc (0 : ℝ) (Real.pi / 2)} := by
      intro θ hθ
      by_contra hnot
      have hnot' : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by simpa using hnot
      have hb := pointwise_bound (n := n) hn f hp1 hp2 hc0 hRad θ hnot'
      exact hθ hb
    apply measure_mono_null hsub
    unfold thetaMeasure thetaSet
    rw [Measure.smul_apply]
    change ENNReal.ofReal (2 / Real.pi) • (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2)))
      (Set.Ioc (0 : ℝ) (Real.pi / 2))ᶜ = 0
    rw [Measure.restrict_apply (measurableSet_Ioc.compl)]
    simp
  have hint_le : (∫ θ : ℝ, (∑ x : Ω n, w * ‖Jsmooth θ f x‖ ^ pow) ∂thetaMeasure) ≤ C0 := by
    simpa using integral_mono_ae (μ := thetaMeasure) hintG hintC hae
  calc
    meanReal (fun x : Ω n => ‖f x - meanX f‖ ^ pow)
        = ∑ x : Ω n, w * ‖f x - meanX f‖ ^ pow := by
            simpa [w] using (meanReal_eq_sum (fun x : Ω n => ‖f x - meanX f‖ ^ pow))
    _ ≤ ∑ x : Ω n, w * ((Real.pi / 2) ^ pow * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure)) := by
            have hx : ∀ x : Ω n, ‖f x - meanX f‖ ^ pow ≤
                (Real.pi / 2) ^ pow * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure) := by
              intro x
              exact pointwise_pow_le f x hp1
            apply Finset.sum_le_sum
            intro x hxmem
            exact mul_le_mul_of_nonneg_left (hx x) hw
    _ = (Real.pi / 2) ^ pow * (∑ x : Ω n, w * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure)) := by
          calc
            (∑ x : Ω n, w * ((Real.pi / 2) ^ pow * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure)))
                = ∑ x : Ω n, (Real.pi / 2) ^ pow * (w * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure)) := by
                    apply Finset.sum_congr rfl
                    intro x hxmem
                    ring
            _ = (Real.pi / 2) ^ pow * (∑ x : Ω n, w * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure)) := by
                    exact (Finset.mul_sum (s := Finset.univ)
                      (f := fun x : Ω n => w * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure))
                      (a := (Real.pi / 2) ^ pow)).symm
    _ = (Real.pi / 2) ^ pow * (∫ θ : ℝ, (∑ x : Ω n, w * ‖Jsmooth θ f x‖ ^ pow) ∂thetaMeasure) := by
          congr 1
          calc
            (∑ x : Ω n, w * (∫ θ : ℝ, ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure))
                = ∑ x : Ω n, ∫ θ : ℝ, w * ‖Jsmooth θ f x‖ ^ pow ∂thetaMeasure := by
                    apply Finset.sum_congr rfl
                    intro x hxmem
                    exact (MeasureTheory.integral_const_mul (r := w)
                      (f := fun θ : ℝ => ‖Jsmooth θ f x‖ ^ pow)).symm
            _ = ∫ θ : ℝ, (∑ x : Ω n, w * ‖Jsmooth θ f x‖ ^ pow) ∂thetaMeasure := by
                    exact (integral_finsetSum (s := (Finset.univ : Finset (Ω n)))
                      (f := fun (x : Ω n) (θ : ℝ) => w * ‖Jsmooth θ f x‖ ^ pow)
                      (by intro x hxmem; exact hint_x x)).symm
    _ ≤ (Real.pi / 2) ^ pow * C0 := by
          exact mul_le_mul_of_nonneg_left hint_le (by positivity : 0 ≤ (Real.pi / 2) ^ pow)
    _ = (Real.pi / 2) ^ pow * (2 : ℝ) ^ (pow / 2) * c ^ pow *
          (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ pow)) := by
          simp [C0]
          ring

end RadType
