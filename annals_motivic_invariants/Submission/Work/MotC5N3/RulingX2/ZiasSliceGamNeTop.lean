import Submission.Work.MotC5N3.RulingX2.ZiasGamIdKey
import Submission.Work.MotC5N3.RulingX2.ZiasGamQ
import Submission.Work.MotC5N3.RulingX2.span_three_quadratic_linear_ne_top
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3.RulingX2

open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

/-- `2 ≠ 0` in characteristic `5`. -/
lemma two_ne_zero_chi5 : (2 : K) ≠ 0 := by
  intro h
  have h2 : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp h
  norm_num at h2

/-- `a ≠ 3b` as soon as `a ^ 2 - ab - b ^ 2 ≠ 0` in characteristic `5`. -/
lemma a_ne_three_b (a b : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) : a - 3 * b ≠ 0 := by
  intro h
  apply ha
  have h' : a = 3 * b := sub_eq_zero.mp h
  rw [h']
  ring_nf
  rw [show (5 : K) = 0 from CharP.cast_eq_zero K 5, mul_zero]

lemma P4v_eq (a b g : K) :
    P4v a b g = a * b * (a - 3 * b) * (2 * (a ^ 2 - a * b - b ^ 2)) := by
  dsimp only [P4v]
  refl_ring1 (mod := 5)

lemma P4v_ne_zero (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) :
    P4v a b g ≠ 0 := by
  rw [P4v_eq]
  exact mul_ne_zero (mul_ne_zero hab (a_ne_three_b a b ha))
    (mul_ne_zero two_ne_zero_chi5 ha)

lemma Pr_eq_explicit (a b g : K) :
    Pr a b g = Polynomial.C (q0 a b g) + Polynomial.C (q1 a b g) * Polynomial.X
      + Polynomial.C (q2 a b g) * Polynomial.X ^ 2 + Polynomial.C (q3 a b g) * Polynomial.X ^ 3
      + Polynomial.C (P4v a b g) * Polynomial.X ^ 4 + Polynomial.C (q5 a b g) * Polynomial.X ^ 5 := by
  dsimp only [Pr, Slice.PhatPoly, Slice.Phat, Slice.Phat_p0, Slice.Phat_p1, q0, q1, q2, q3, q5,
    P4v]
  simp only [toK_C, toK_X1, map_add, map_mul, map_pow, map_one, map_zero, map_ofNat,
    Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]
  refl_ring1

lemma Pr_coeff4 (a b g : K) : (Pr a b g).coeff 4 = P4v a b g := by
  rw [Pr_eq_explicit]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_zero, Polynomial.coeff_one]
  norm_num

lemma Pr_not_isUnit (a b g : K) (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) :
    ¬ IsUnit (Pr a b g) := by
  intro h
  have h4 : (Pr a b g).coeff 4 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt
      (by rw [Polynomial.isUnit_iff_degree_eq_zero.mp h]; norm_num)
  rw [Pr_coeff4 a b g] at h4
  exact P4v_ne_zero a b g ha hab h4

/-- The divisibility `Pr ∣ nrm` in `K[X]`, transferred along `ev`. -/
lemma Pr_dvd_nrm (a b g : K) (hden : (2 : K) * (a - 3 * b) ^ 5 ≠ 0) (hP4 : P4v a b g ≠ 0) :
    Pr a b g ∣ nrm a b g := by
  have h3 : Polynomial.C (nrm a b g)
      = Polynomial.C (Polynomial.C ((P4v a b g * ((2 : K) * (a - 3 * b) ^ 5))⁻¹ * N5v a b g)
          * Polynomial.X * Pr a b g) := by
    rw [← ev_nrmMv, nrmMv_eq a b g hden hP4]
    simp only [map_mul, ev_C, ev_X1, ev_Phat, Polynomial.C_mul]
    refl_ring1
  refine ⟨Polynomial.C ((P4v a b g * ((2 : K) * (a - 3 * b) ^ 5))⁻¹ * N5v a b g)
    * Polynomial.X, ?_⟩
  rw [Polynomial.C_injective h3]
  refl_ring1

/-- Transfer of properness from `(K[X])[X]` back to `K[X 0, X 1]`. -/
lemma span_ne_top_of_ev (f g h : MvPolynomial (Fin 2) K)
    (hfg : Ideal.span ({ev f, ev g, ev h} : Set (Polynomial (Polynomial K))) ≠ ⊤) :
    Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 2) K)) ≠ ⊤ := by
  intro htop
  apply hfg
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : MvPolynomial (Fin 2) K) ∈ Ideal.span ({f, g, h} : Set _) := by
    rw [htop]; exact Submodule.mem_top
  have hle : Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 2) K)) ≤
      Ideal.comap ev (Ideal.span ({ev f, ev g, ev h} : Set (Polynomial (Polynomial K)))) := by
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl | rfl) <;> exact Ideal.subset_span (by simp)
  have : (1 : MvPolynomial (Fin 2) K) ∈
      Ideal.comap ev (Ideal.span ({ev f, ev g, ev h} : Set (Polynomial (Polynomial K)))) :=
    hle h1
  rw [Ideal.mem_comap] at this
  simpa using this

theorem ZiasSliceGamNeTop (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) :
    Ideal.span {Work.MotC5N3.RulingX2.Slice.Phisq a b g,
                Work.MotC5N3.RulingX2.Slice.Gam a b g,
                Work.MotC5N3.RulingX2.Slice.PhatPoly a b g} ≠ ⊤ := by
  have ha3 : a - 3 * b ≠ 0 := a_ne_three_b a b ha
  have hden : (2 : K) * (a - 3 * b) ^ 5 ≠ 0 :=
    mul_ne_zero two_ne_zero_chi5 (pow_ne_zero 5 ha3)
  have hP4 : P4v a b g ≠ 0 := P4v_ne_zero a b g ha hab
  have hdiv : Pr a b g ∣ nrm a b g := Pr_dvd_nrm a b g hden hP4
  have hunit : ¬ IsUnit (Pr a b g) := Pr_not_isUnit a b g ha hab
  have hproper := span_three_quadratic_linear_ne_top (Pr a b g) (Al a b g) (Be a b g) (Dr a b g)
    (Rr a b g) hunit hdiv
  have hproper' : Ideal.span ({ev (Slice.PhatPoly a b g), ev (Slice.Phisq a b g),
      ev (Slice.Gam a b g)} : Set (Polynomial (Polynomial K))) ≠ ⊤ := by
    rw [ev_Phat, ev_Phisq, ev_Gam]
    exact hproper
  have hmain := span_ne_top_of_ev (K := K) (Slice.PhatPoly a b g) (Slice.Phisq a b g)
    (Slice.Gam a b g) hproper'
  have hset : ({Slice.PhatPoly a b g, Slice.Phisq a b g, Slice.Gam a b g} :
      Set (MvPolynomial (Fin 2) K)) = {Slice.Phisq a b g, Slice.Gam a b g,
        Slice.PhatPoly a b g} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rwa [hset] at hmain

end Work.MotC5N3.RulingX2
