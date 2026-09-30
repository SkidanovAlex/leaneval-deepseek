import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.Algebra.BigOperators.sum_double_eq_diag_add_pairs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Real BigOperators ComplexConjugate
open MeasureTheory

noncomputable section

namespace MvHilbert

lemma normSq_eq_re (z : ℂ) : Complex.normSq z = (z * conj z).re := by
  have h2 : (Complex.normSq z : ℂ) = conj z * z := Complex.normSq_eq_conj_mul_self
  have hre := congrArg Complex.re h2
  rw [Complex.ofReal_re] at hre
  rw [mul_comm] at hre
  exact hre

lemma re_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  simpa [Complex.reAddGroupHom] using (map_sum Complex.reAddGroupHom f s)

lemma im_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  simpa [Complex.imAddGroupHom] using (map_sum Complex.imAddGroupHom f s)

lemma exp_re (r : ℤ) (θ : ℝ) :
    (Complex.exp (((r : ℝ) * θ) * Complex.I)).re = Real.cos ((r : ℝ) * θ) := by
  let x : ℝ := (r : ℝ) * θ
  have harg : (((r : ℝ) * θ) * Complex.I) = ((x : ℂ) * Complex.I) := by
    dsimp [x]
    push_cast
    ring
  rw [harg]
  rw [Complex.exp_mul_I]
  rw [Complex.add_re]
  rw [Complex.cos_ofReal_re]
  rw [Complex.mul_re]
  rw [Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  simp [x]

lemma exp_im (r : ℤ) (θ : ℝ) :
    (Complex.exp (((r : ℝ) * θ) * Complex.I)).im = Real.sin ((r : ℝ) * θ) := by
  let x : ℝ := (r : ℝ) * θ
  have harg : (((r : ℝ) * θ) * Complex.I) = ((x : ℂ) * Complex.I) := by
    dsimp [x]
    push_cast
    ring
  rw [harg]
  rw [Complex.exp_mul_I]
  rw [Complex.add_im]
  rw [Complex.mul_im]
  rw [Complex.cos_ofReal_im]
  rw [Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  simp [x]

lemma conj_exp (r : ℤ) (θ : ℝ) :
    conj (Complex.exp (((r : ℝ) * θ) * Complex.I)) = Complex.exp (-(((r : ℝ) * θ) * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma exp_mul_exp_neg (n : ℝ → ℤ) (a b : ℝ) (θ : ℝ) :
    Complex.exp (((n a : ℝ) * θ) * Complex.I) *
        Complex.exp (-(((n b : ℝ) * θ) * Complex.I)) =
      Complex.exp (((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  ring

def U (S : Finset ℝ) (n : ℝ → ℤ) (u : ℝ → ℝ) (θ : ℝ) : ℂ :=
  ∑ a ∈ S, (u a : ℂ) * Complex.exp (((n a : ℝ) * θ) * Complex.I)

lemma conj_U (S : Finset ℝ) (n : ℝ → ℤ) (u : ℝ → ℝ) (θ : ℝ) :
    conj (U S n u θ) = ∑ b ∈ S, (u b : ℂ) * Complex.exp (-(((n b : ℝ) * θ) * Complex.I)) := by
  unfold U
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [map_mul]
  rw [Complex.conj_ofReal]
  rw [conj_exp]

-- U(u)θ · conj(U(v)θ) = Σ_{a,b} u a·v b·exp(i(n a−n b)θ)
lemma U_conj_V (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) (θ : ℝ) :
    U S n u θ * conj (U S n v θ) =
      ∑ a ∈ S, ∑ b ∈ S, (u a : ℂ) * (v b : ℂ) *
        Complex.exp ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I) := by
  rw [conj_U]
  unfold U
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  refine Finset.sum_congr rfl ?_
  intro b hb
  calc
    (u a : ℂ) * Complex.exp (((n a : ℝ) * θ) * Complex.I) *
        ((v b : ℂ) * Complex.exp (-(((n b : ℝ) * θ) * Complex.I)))
        = (u a : ℂ) * (v b : ℂ) *
            (Complex.exp (((n a : ℝ) * θ) * Complex.I) *
              Complex.exp (-(((n b : ℝ) * θ) * Complex.I))) := by ring
    _ = (u a : ℂ) * (v b : ℂ) *
        Complex.exp ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I) := by
          rw [exp_mul_exp_neg]

-- Q(θ) = Σ u a v b sin((n a − n b) θ) equals Im(U u conj U v)
def Q (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, u a * v b * Real.sin (((n a - n b : ℤ) : ℝ) * θ)

lemma Q_eq_im (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) (θ : ℝ) :
    Q S n u v θ = (U S n u θ * conj (U S n v θ)).im := by
  unfold Q
  rw [U_conj_V]
  rw [im_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [im_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro b hb
  have him := exp_im (n a - n b) θ
  have harg : ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I) =
      (((((n a - n b : ℤ) : ℝ) * θ) * Complex.I)) := by
    push_cast
    ring
  rw [← harg] at him
  -- im((u a)(v b)·exp) = u a v b · sin
  have hsc : (u a : ℂ) * (v b : ℂ) = ((u a * v b : ℝ) : ℂ) := by push_cast; ring
  rw [hsc]
  rw [Complex.im_ofReal_mul]
  rw [him]

-- |Uθ|² = Σ u a u b cos(...)
lemma normSq_U_eq (S : Finset ℝ) (n : ℝ → ℤ) (u : ℝ → ℝ) (θ : ℝ) :
    ‖U S n u θ‖ ^ 2 = ∑ a ∈ S, ∑ b ∈ S, u a * u b * Real.cos (((n a - n b : ℤ) : ℝ) * θ) := by
  have hM := U_conj_V S n u u θ
  have hreM : (∑ a ∈ S, ∑ b ∈ S,
        ((u a : ℂ) * (u b : ℂ) * Complex.exp ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I)).re) =
      (∑ a ∈ S, ∑ b ∈ S, u a * u b * Real.cos (((n a - n b : ℤ) : ℝ) * θ)) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    refine Finset.sum_congr rfl ?_
    intro b hb
    have hterm : (((u a : ℂ) * (u b : ℂ) * Complex.exp ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I)).re) =
        u a * u b * Real.cos (((n a - n b : ℤ) : ℝ) * θ) := by
      have hsc : (u a : ℂ) * (u b : ℂ) = ((u a * u b : ℝ) : ℂ) := by push_cast; ring
      rw [hsc]
      rw [Complex.re_ofReal_mul]
      have hre := exp_re (n a - n b) θ
      have harg : ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I) =
          (((((n a - n b : ℤ) : ℝ) * θ) * Complex.I)) := by
        push_cast
        ring
      rw [← harg] at hre
      rw [hre]
    exact hterm
  have hdd : (∑ a ∈ S, ∑ b ∈ S,
        ((u a : ℂ) * (u b : ℂ) * Complex.exp ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I))).re =
      ∑ a ∈ S, ∑ b ∈ S,
        (((u a : ℂ) * (u b : ℂ) * Complex.exp ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I)).re) := by
    simp [re_finset_sum]
  calc
    ‖U S n u θ‖ ^ 2 = Complex.normSq (U S n u θ) := (Complex.normSq_eq_norm_sq _).symm
    _ = (U S n u θ * conj (U S n u θ)).re := normSq_eq_re (U S n u θ)
    _ = (∑ a ∈ S, ∑ b ∈ S, (u a : ℂ) * (u b : ℂ) *
        Complex.exp ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I)).re := by rw [hM]
    _ = ∑ a ∈ S, ∑ b ∈ S,
        (((u a : ℂ) * (u b : ℂ) * Complex.exp ((((n a : ℝ) - (n b : ℝ)) * θ) * Complex.I)).re) := hdd
    _ = ∑ a ∈ S, ∑ b ∈ S, u a * u b * Real.cos (((n a - n b : ℤ) : ℝ) * θ) := hreM



lemma deriv_sin_mul (k : ℝ) : deriv (fun θ : ℝ => Real.sin (k * θ)) = fun θ : ℝ => k * Real.cos (k * θ) := by
  funext θ
  have hc : DifferentiableAt ℝ (fun θ : ℝ => k * θ) θ := by fun_prop
  rw [deriv_sin (f := fun θ : ℝ => k * θ) hc]
  rw [deriv_const_mul_id k]
  ring

lemma deriv_cos_mul (k : ℝ) : deriv (fun θ : ℝ => Real.cos (k * θ)) = fun θ : ℝ => -k * Real.sin (k * θ) := by
  funext θ
  have hc : DifferentiableAt ℝ (fun θ : ℝ => k * θ) θ := by fun_prop
  rw [deriv_cos (f := fun θ : ℝ => k * θ) hc]
  rw [deriv_const_mul_id k]
  ring

lemma deriv_theta_cos (k : ℝ) : deriv (fun θ : ℝ => θ * Real.cos (k * θ)) =
    fun θ : ℝ => Real.cos (k * θ) - θ * k * Real.sin (k * θ) := by
  funext θ
  change deriv ((fun θ : ℝ => θ) * (fun θ : ℝ => Real.cos (k * θ))) θ =
      Real.cos (k * θ) - θ * k * Real.sin (k * θ)
  have h1 : DifferentiableAt ℝ (fun θ : ℝ => θ) θ := by fun_prop
  have h2 : DifferentiableAt ℝ (fun θ : ℝ => Real.cos (k * θ)) θ := by fun_prop
  rw [deriv_mul h1 h2]
  have hdc := deriv_cos_mul k
  rw [hdc]
  simp
  ring_nf

lemma deriv_prim (k : ℝ) (hk : k ≠ 0) :
    deriv (fun θ : ℝ => -θ * Real.cos (k * θ) / k + Real.sin (k * θ) / k ^ 2) =
      fun θ : ℝ => θ * Real.sin (k * θ) := by
  funext θ
  change deriv ((fun θ : ℝ => -θ * Real.cos (k * θ) / k) + (fun θ : ℝ => Real.sin (k * θ) / k ^ 2)) θ =
      θ * Real.sin (k * θ)
  have h1 : DifferentiableAt ℝ (fun θ : ℝ => -θ * Real.cos (k * θ) / k) θ := by fun_prop
  have h2 : DifferentiableAt ℝ (fun θ : ℝ => Real.sin (k * θ) / k ^ 2) θ := by fun_prop
  rw [deriv_add h1 h2]
  have hdn : deriv (fun θ : ℝ => -θ * Real.cos (k * θ) / k) θ =
      (deriv (fun θ : ℝ => -θ * Real.cos (k * θ)) θ) / k := by
    simpa using (deriv_div_const (c := fun θ : ℝ => -θ * Real.cos (k * θ)) (d := k) (x := θ))
  rw [hdn]
  have hdnn : deriv (fun θ : ℝ => -θ * Real.cos (k * θ)) θ = -deriv (fun θ : ℝ => θ * Real.cos (k * θ)) θ := by
    have h3 : DifferentiableAt ℝ (fun θ : ℝ => θ * Real.cos (k * θ)) θ := by fun_prop
    simpa using (deriv_neg h3)
  rw [hdnn]
  have hdpc := deriv_theta_cos k
  rw [hdpc]
  have hds2 : deriv (fun θ : ℝ => Real.sin (k * θ) / k ^ 2) θ = (deriv (fun θ : ℝ => Real.sin (k * θ)) θ) / k ^ 2 := by
    simpa using (deriv_div_const (c := fun θ : ℝ => Real.sin (k * θ)) (d := k ^ 2) (x := θ))
  rw [hds2]
  have hds := deriv_sin_mul k
  rw [hds]
  ring_nf
  field_simp [hk]
  ring

lemma sin_int_two_pi_mul (k : ℤ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * θ)) = 0 := by
  have hs := intervalIntegral.mul_integral_comp_mul_left (c := (k : ℝ)) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := Real.sin)
  have h' : (k : ℝ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * θ)) =
      (∫ u in 0..(k : ℝ) * (2 * Real.pi), Real.sin u) := by
    simpa using hs
  have hz : (∫ u in 0..(k : ℝ) * (2 * Real.pi), Real.sin u) = 0 := by
    rw [integral_sin]
    have hcos : Real.cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
      have hc := Real.cos_int_mul_two_pi (n := k)
      convert hc using 1
    rw [hcos]
    simp
  by_cases hk : k = 0
  · subst k
    simp
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * θ))
          = ((k : ℝ)⁻¹) * ((k : ℝ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * θ))) := by
            field_simp [hk0]
      _ = (k : ℝ)⁻¹ * 0 := by rw [h', hz]
      _ = 0 := by ring

lemma cos_int_two_pi_mul (k : ℤ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * θ)) =
      (if k = 0 then (2 * Real.pi : ℝ) else 0) := by
  have hs := intervalIntegral.mul_integral_comp_mul_left (c := (k : ℝ)) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := Real.cos)
  have h' : (k : ℝ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * θ)) =
      (∫ u in 0..(k : ℝ) * (2 * Real.pi), Real.cos u) := by
    simpa using hs
  have hz : (∫ u in 0..(k : ℝ) * (2 * Real.pi), Real.cos u) = 0 := by
    rw [integral_cos]
    have hs2 : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
      have hss := Real.sin_int_mul_pi (n := 2 * k)
      rw [← hss]
      congr 1
      push_cast
      ring_nf
    rw [hs2]
    simp
  by_cases hk : k = 0
  · subst k
    simp
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * θ))
          = ((k : ℝ)⁻¹) * ((k : ℝ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * θ))) := by
            field_simp [hk0]
      _ = (k : ℝ)⁻¹ * 0 := by rw [h', hz]
      _ = 0 := by ring
      _ = (if k = 0 then (2 * Real.pi : ℝ) else 0) := by simp [hk]

-- ∫_0^{2π} θ sin(kθ) dθ = -2π/k
lemma theta_sin_int (k : ℤ) (hk : k ≠ 0) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), θ * Real.sin ((k : ℝ) * θ)) = (-2 * Real.pi) / (k : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  let F : ℝ → ℝ := fun t => -t * Real.cos ((k : ℝ) * t) / (k : ℝ) + Real.sin ((k : ℝ) * t) / (k : ℝ) ^ 2
  let f' : ℝ → ℝ := fun t => t * Real.sin ((k : ℝ) * t)
  have hderiv : deriv F = f' := by
    dsimp [F, f']
    exact deriv_prim (k : ℝ) hk0
  have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), DifferentiableAt ℝ F x := by
    intro x hx
    dsimp [F]
    fun_prop
  have hcont : ContinuousOn f' (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    dsimp [f']
    fun_prop
  have h := intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont
  have hF : F (2 * Real.pi) - F 0 = (-2 * Real.pi) / (k : ℝ) := by
    dsimp [F]
    have hc2 : Real.cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
      have hc := Real.cos_int_mul_two_pi (n := k)
      convert hc using 1
    have hs2 : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
      have hss := Real.sin_int_mul_pi (n := 2 * k)
      rw [← hss]
      congr 1
      push_cast
      ring_nf
    have hc0 : Real.cos ((k : ℝ) * 0) = 1 := by simp
    have hs0 : Real.sin ((k : ℝ) * 0) = 0 := by simp
    rw [hc2, hs2, hc0, hs0]
    field_simp [hk0]
    ring
  simpa [f'] using h.trans hF

-- coefficient identity: (k:ℝ)⁻¹ = (1/(2π)) ∫_0^{2π} (π − θ)·sin(kθ)
lemma coeff_int (k : ℤ) :
    (k : ℝ)⁻¹ = (1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Real.sin ((k : ℝ) * θ)) := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hsplit : (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Real.sin ((k : ℝ) * θ)) =
        Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * θ)) -
          (∫ θ in (0 : ℝ)..(2 * Real.pi), θ * Real.sin ((k : ℝ) * θ)) := by
      have hcong : (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Real.sin ((k : ℝ) * θ)) =
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (Real.pi * Real.sin ((k : ℝ) * θ) - θ * Real.sin ((k : ℝ) * θ))) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        ring
      rw [hcong]
      calc
        (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.pi * Real.sin ((k : ℝ) * θ) - θ * Real.sin ((k : ℝ) * θ))
            = (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.pi * Real.sin ((k : ℝ) * θ)) -
                (∫ θ in (0 : ℝ)..(2 * Real.pi), θ * Real.sin ((k : ℝ) * θ)) := by
              exact intervalIntegral.integral_sub
                (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) (2 * Real.pi))
                (Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) (2 * Real.pi))
        _ = Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * θ)) -
                (∫ θ in (0 : ℝ)..(2 * Real.pi), θ * Real.sin ((k : ℝ) * θ)) := by
              rw [intervalIntegral.integral_const_mul (r := Real.pi)
                (f := fun θ : ℝ => Real.sin ((k : ℝ) * θ))]
    have hvalue : (1 / (2 * Real.pi)) *
        (Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * θ)) -
          (∫ θ in (0 : ℝ)..(2 * Real.pi), θ * Real.sin ((k : ℝ) * θ))) = (k : ℝ)⁻¹ := by
      rw [sin_int_two_pi_mul k, theta_sin_int k hk]
      field_simp [hk0]
      ring
    calc
      (k : ℝ)⁻¹ = (1 / (2 * Real.pi)) *
        (Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * θ)) -
          (∫ θ in (0 : ℝ)..(2 * Real.pi), θ * Real.sin ((k : ℝ) * θ))) := hvalue.symm
      _ = (1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Real.sin ((k : ℝ) * θ)) := by
            rw [hsplit]


/-- Parseval on the circle: ∫₀^{2π} |Σ u a e^{i n a θ}|² dθ = 2π Σ u a². -/
lemma parseval_U (S : Finset ℝ) (n : ℝ → ℤ)
    (hinj : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → n a = n b → a = b)
    (u : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖U S n u θ‖ ^ 2) = 2 * Real.pi * (∑ a ∈ S, u a ^ 2) := by
  have hfun : (fun θ : ℝ => ‖U S n u θ‖ ^ 2) =
      (fun θ : ℝ => ∑ a ∈ S, ∑ b ∈ S, u a * u b * Real.cos (((n a - n b : ℤ) : ℝ) * θ)) := by
    funext θ
    exact normSq_U_eq S n u θ
  rw [hfun]
  -- interchange the double sum with the integral
  have hstep1 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ∑ a ∈ S, ∑ b ∈ S, u a * u b * Real.cos (((n a - n b : ℤ) : ℝ) * θ)) =
      ∑ a ∈ S, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ∑ b ∈ S, u a * u b * Real.cos (((n a - n b : ℤ) : ℝ) * θ) := by
    rw [intervalIntegral.integral_finset_sum]
    intro a ha
    apply Continuous.intervalIntegrable <;> fun_prop
  have hstep2 : (∑ a ∈ S, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ∑ b ∈ S, u a * u b * Real.cos (((n a - n b : ℤ) : ℝ) * θ)) =
      ∑ a ∈ S, ∑ b ∈ S, u a * u b * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos (((n a - n b : ℤ) : ℝ) * θ)) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro b hb
      rw [intervalIntegral.integral_const_mul]
    · intro b hb
      apply Continuous.intervalIntegrable <;> fun_prop
  rw [hstep1, hstep2]
  -- evaluate the cos integrals
  have hcos : (∑ a ∈ S, ∑ b ∈ S, u a * u b * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos (((n a - n b : ℤ) : ℝ) * θ))) =
      (∑ a ∈ S, ∑ b ∈ S, u a * u b * (if (n a - n b : ℤ) = 0 then (2 * Real.pi : ℝ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    refine Finset.sum_congr rfl ?_
    intro b hb
    rw [cos_int_two_pi_mul (n a - n b)]
  rw [hcos]
  -- diagonal collapse
  have hdiag : (∑ a ∈ S, ∑ b ∈ S, u a * u b * (if (n a - n b : ℤ) = 0 then (2 * Real.pi : ℝ) else 0)) =
      2 * Real.pi * (∑ a ∈ S, u a ^ 2) := by
    have hif : ∀ a ∈ S, ∀ b ∈ S, (if (n a - n b : ℤ) = 0 then (2 * Real.pi : ℝ) else 0) =
        (if a = b then (2 * Real.pi : ℝ) else 0) := by
      intro a ha b hb
      by_cases h : a = b
      · subst h
        simp
      · have hn : n a ≠ n b := by
          intro hn
          exact h (hinj ha hb hn)
        have hn' : (n a - n b : ℤ) ≠ 0 := by
          intro hz
          apply hn
          exact sub_eq_zero.mp hz
        simp [h, hn']
    calc
      (∑ a ∈ S, ∑ b ∈ S, u a * u b * (if (n a - n b : ℤ) = 0 then (2 * Real.pi : ℝ) else 0))
          = ∑ a ∈ S, ∑ b ∈ S, u a * u b * (if a = b then (2 * Real.pi : ℝ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              rw [hif a ha b hb]
      _ = ∑ a ∈ S, u a * u a * (2 * Real.pi) := by
            simp [Finset.sum_ite_eq']
      _ = 2 * Real.pi * (∑ a ∈ S, u a ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro a ha
            ring
  exact hdiag










/-- c / k = (1/(2π)) ∫ (π−θ)·c·sin(kθ)  -- per-pair rewriting via `coeff_int`. -/
lemma pair_integral (k : ℤ) (c : ℝ) :
    c * (k : ℝ)⁻¹ = (1 / (2 * Real.pi)) *
      (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * (c * Real.sin ((k : ℝ) * θ))) := by
  have hc := coeff_int k
  calc
    c * (k : ℝ)⁻¹ = c * ((1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Real.pi - θ) * Real.sin ((k : ℝ) * θ))) := by rw [hc]
    _ = (1 / (2 * Real.pi)) * (c * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Real.pi - θ) * Real.sin ((k : ℝ) * θ))) := by ring
    _ = (1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Real.pi - θ) * (c * Real.sin ((k : ℝ) * θ))) := by
      congr 1
      rw [← intervalIntegral.integral_const_mul (r := c)
        (f := fun θ : ℝ => (Real.pi - θ) * Real.sin ((k : ℝ) * θ))]
      apply intervalIntegral.integral_congr
      intro θ hθ
      ring

/-- A(u,v) = (1/(2π))·∫₀^{2π} (π−θ)·Q(θ) dθ. -/
lemma integral_double_sum_real (S : Finset ℝ) (t : ℝ → ℝ → ℝ → ℝ)
    (hcont : ∀ a ∈ S, ∀ b ∈ S, Continuous (t a b)) :
    (∑ a ∈ S, ∑ b ∈ S, (∫ θ in (0 : ℝ)..(2 * Real.pi), t a b θ)) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (∑ a ∈ S, ∑ b ∈ S, t a b θ) := by
  have hinner : ∀ a ∈ S, (∑ b ∈ S, (∫ θ in (0 : ℝ)..(2 * Real.pi), t a b θ)) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (∑ b ∈ S, t a b θ) := by
    intro a ha
    exact (intervalIntegral.integral_finsetSum (μ := volume) (s := S) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := fun b θ => t a b θ)
      (fun b hb => Continuous.intervalIntegrable (hcont a ha b hb) (0 : ℝ) (2 * Real.pi))).symm
  calc
    (∑ a ∈ S, ∑ b ∈ S, (∫ θ in (0 : ℝ)..(2 * Real.pi), t a b θ))
        = ∑ a ∈ S, ∫ θ in (0 : ℝ)..(2 * Real.pi), (∑ b ∈ S, t a b θ) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          exact hinner a ha
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), (∑ a ∈ S, ∑ b ∈ S, t a b θ) := by
          exact (intervalIntegral.integral_finsetSum (μ := volume) (s := S) (a := (0 : ℝ)) (b := 2 * Real.pi)
            (f := fun a θ => ∑ b ∈ S, t a b θ)
            (fun a ha => Continuous.intervalIntegrable (by
                apply continuous_finset_sum
                intro b hb
                exact hcont a ha b hb) (0 : ℝ) (2 * Real.pi))).symm

lemma hilbert_integral_form (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ S, u a * v b * ((n a - n b : ℤ) : ℝ)⁻¹) =
      (1 / (2 * Real.pi)) *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ) := by
  calc
    (∑ a ∈ S, ∑ b ∈ S, u a * v b * ((n a - n b : ℤ) : ℝ)⁻¹)
        = ∑ a ∈ S, ∑ b ∈ S, (1 / (2 * Real.pi)) *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              (Real.pi - θ) * ((u a * v b) * Real.sin (((n a - n b : ℤ) : ℝ) * θ))) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              exact pair_integral (n a - n b) (u a * v b)
    _ = (1 / (2 * Real.pi)) * (∑ a ∈ S, ∑ b ∈ S,
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              (Real.pi - θ) * ((u a * v b) * Real.sin (((n a - n b : ℤ) : ℝ) * θ)))) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [Finset.mul_sum]
    _ = (1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
            ∑ a ∈ S, ∑ b ∈ S,
              (Real.pi - θ) * ((u a * v b) * Real.sin (((n a - n b : ℤ) : ℝ) * θ))) := by
              congr 1
              exact integral_double_sum_real S
                (fun a b θ => (Real.pi - θ) * ((u a * v b) * Real.sin (((n a - n b : ℤ) : ℝ) * θ)))
                (by intro a ha b hb; fun_prop)
    _ = (1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ) := by
              congr 1
              have hfun : (fun θ : ℝ => ∑ a ∈ S, ∑ b ∈ S,
                      (Real.pi - θ) * ((u a * v b) * Real.sin (((n a - n b : ℤ) : ℝ) * θ))) =
                  (fun θ : ℝ => (Real.pi - θ) * Q S n u v θ) := by
                funext θ
                unfold Q
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro a ha
                rw [Finset.mul_sum]
              rw [hfun]

lemma abs_im_le_norm (z : ℂ) : |z.im| ≤ ‖z‖ := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hz2 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re]
  exact (sq_le_sq.mp hz2).trans_eq (abs_of_nonneg hz0)

/-- |Q(θ)| ≤ ‖U u θ‖ · ‖U v θ‖. -/
lemma abs_Q_le (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) (θ : ℝ) :
    |Q S n u v θ| ≤ ‖U S n u θ‖ * ‖U S n v θ‖ := by
  rw [Q_eq_im S n u v θ]
  calc
    |(U S n u θ * conj (U S n v θ)).im| ≤ ‖U S n u θ * conj (U S n v θ)‖ := abs_im_le_norm _
    _ = ‖U S n u θ‖ * ‖conj (U S n v θ)‖ := by rw [norm_mul]
    _ = ‖U S n u θ‖ * ‖U S n v θ‖ := by rw [Complex.norm_conj]

/-- Pointwise: |Q θ| ≤ (‖U u θ‖² + ‖U v θ‖²)/2. -/
lemma abs_Q_le_half (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) (θ : ℝ) :
    |Q S n u v θ| ≤ (‖U S n u θ‖ ^ 2 + ‖U S n v θ‖ ^ 2) / 2 := by
  have h := abs_Q_le S n u v θ
  have ha : 0 ≤ ‖U S n u θ‖ := norm_nonneg _
  have hb : 0 ≤ ‖U S n v θ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖U S n u θ‖ - ‖U S n v θ‖)]

/-- ∫₀^{2π} |Q| ≤ π·(Σu² + Σv²). -/
lemma continuous_U_aux (S : Finset ℝ) (n : ℝ → ℤ) (u : ℝ → ℝ) : Continuous (U S n u) := by
  unfold U
  fun_prop

lemma cont_normSq_U (S : Finset ℝ) (n : ℝ → ℤ) (u : ℝ → ℝ) :
    Continuous (fun θ : ℝ => ‖U S n u θ‖ ^ 2) := by
  exact (continuous_U_aux S n u).norm.pow 2

lemma continuous_Q (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) : Continuous (Q S n u v) := by
  unfold Q
  fun_prop

lemma cont_abs_Q (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) :
    Continuous (fun θ : ℝ => |Q S n u v θ|) := by
  exact (continuous_Q S n u v).abs

lemma int_abs_Q_le (S : Finset ℝ) (n : ℝ → ℤ)
    (hinj : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → n a = n b → a = b)
    (u v : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), |Q S n u v θ|) ≤
      Real.pi * (∑ a ∈ S, u a ^ 2 + ∑ a ∈ S, v a ^ 2) := by
  have hRHS : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (‖U S n u θ‖ ^ 2 + ‖U S n v θ‖ ^ 2) / 2) =
      (1 / 2) * (2 * Real.pi * (∑ a ∈ S, u a ^ 2) + 2 * Real.pi * (∑ a ∈ S, v a ^ 2)) := by
    rw [show (fun θ : ℝ => (‖U S n u θ‖ ^ 2 + ‖U S n v θ‖ ^ 2) / 2) =
        (fun θ : ℝ => (1 / 2) * (‖U S n u θ‖ ^ 2 + ‖U S n v θ‖ ^ 2)) by
          funext θ
          ring]
    rw [intervalIntegral.integral_const_mul (μ := volume) (r := (1 / 2 : ℝ))
      (f := fun θ : ℝ => ‖U S n u θ‖ ^ 2 + ‖U S n v θ‖ ^ 2)]
    congr 1
    rw [intervalIntegral.integral_add (μ := volume)]
    · rw [parseval_U S n hinj u, parseval_U S n hinj v]
    · exact Continuous.intervalIntegrable (μ := volume) (cont_normSq_U S n u) (0 : ℝ) (2 * Real.pi)
    · exact Continuous.intervalIntegrable (μ := volume) (cont_normSq_U S n v) (0 : ℝ) (2 * Real.pi)
  have hmono : (∫ θ in (0 : ℝ)..(2 * Real.pi), |Q S n u v θ|) ≤
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (‖U S n u θ‖ ^ 2 + ‖U S n v θ‖ ^ 2) / 2) := by
    exact intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (Continuous.intervalIntegrable (μ := volume) (cont_abs_Q S n u v) (0 : ℝ) (2 * Real.pi))
      (Continuous.intervalIntegrable (μ := volume)
        (Continuous.div_const ((cont_normSq_U S n u).add (cont_normSq_U S n v)) 2) (0 : ℝ) (2 * Real.pi))
      (by intro θ hθ; exact abs_Q_le_half S n u v θ)
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), |Q S n u v θ|)
        ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi), (‖U S n u θ‖ ^ 2 + ‖U S n v θ‖ ^ 2) / 2) := hmono
    _ = (1 / 2) * (2 * Real.pi * (∑ a ∈ S, u a ^ 2) + 2 * Real.pi * (∑ a ∈ S, v a ^ 2)) := hRHS
    _ = Real.pi * (∑ a ∈ S, u a ^ 2 + ∑ a ∈ S, v a ^ 2) := by ring

/-- Real bilinear Hilbert bound: |Σ u v/(n a − n b)| ≤ (π/2)(Σu² + Σv²). -/
theorem real_hilbert_bound (S : Finset ℝ) (n : ℝ → ℤ)
    (hinj : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → n a = n b → a = b)
    (u v : ℝ → ℝ) :
    |∑ a ∈ S, ∑ b ∈ S, u a * v b * ((n a - n b : ℤ) : ℝ)⁻¹| ≤
      (Real.pi / 2) * (∑ a ∈ S, u a ^ 2 + ∑ a ∈ S, v a ^ 2) := by
  have hA := hilbert_integral_form S n u v
  have hpi_pos2 : 0 < (2 * Real.pi : ℝ) := by positivity
  have hpi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
  have h1 : |(∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ)| ≤
      Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), |Q S n u v θ|) := by
    have hnorm' : |(∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ)| ≤
        (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖(Real.pi - θ) * Q S n u v θ‖) := by
      have hnorm := intervalIntegral.norm_integral_le_integral_norm (E := ℝ) (μ := volume)
        (f := fun θ : ℝ => (Real.pi - θ) * Q S n u v θ)
        (a := (0 : ℝ)) (b := 2 * Real.pi) (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      simpa using hnorm
    have hpi : (∫ θ in (0 : ℝ)..(2 * Real.pi), |Real.pi - θ| * |Q S n u v θ|) ≤
        Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), |Q S n u v θ|) := by
      have hmono2 : (∫ θ in (0 : ℝ)..(2 * Real.pi), |Real.pi - θ| * |Q S n u v θ|) ≤
          (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.pi * |Q S n u v θ|) := by
        have cAbsPiSub : Continuous (fun θ : ℝ => |Real.pi - θ|) :=
          ((continuous_const : Continuous (fun θ : ℝ => Real.pi)).sub continuous_id).abs
        have cPimulAbsQ : Continuous (fun θ : ℝ => Real.pi * |Q S n u v θ|) :=
          (continuous_const : Continuous (fun θ : ℝ => Real.pi)).mul (cont_abs_Q S n u v)
        exact intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
          (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
          (Continuous.intervalIntegrable (μ := volume) (cAbsPiSub.mul (cont_abs_Q S n u v)) (0 : ℝ) (2 * Real.pi))
          (Continuous.intervalIntegrable (μ := volume) cPimulAbsQ (0 : ℝ) (2 * Real.pi))
          (by
            intro θ hθ
            have hθle : θ ≤ 2 * Real.pi := (Set.mem_Icc.mp hθ).2
            have hθge : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
            have habs : |Real.pi - θ| ≤ Real.pi := by
              rw [abs_le]
              constructor <;> nlinarith
            exact mul_le_mul_of_nonneg_right habs (abs_nonneg _))
      calc
        (∫ θ in (0 : ℝ)..(2 * Real.pi), |Real.pi - θ| * |Q S n u v θ|)
            ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.pi * |Q S n u v θ| := hmono2
        _ = Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), |Q S n u v θ|) := by
              rw [intervalIntegral.integral_const_mul (μ := volume) (r := Real.pi)
                (f := fun θ : ℝ => |Q S n u v θ|)]
    calc
      |(∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ)|
          ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖(Real.pi - θ) * Q S n u v θ‖ := hnorm'
      _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), |Real.pi - θ| * |Q S n u v θ| := by
            apply intervalIntegral.integral_congr
            intro θ hθ
            simp [abs_mul]
      _ ≤ Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), |Q S n u v θ|) := hpi
  have hgoal : (1 / (2 * Real.pi)) *
      |(∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ)| ≤
      (Real.pi / 2) * (∑ a ∈ S, u a ^ 2 + ∑ a ∈ S, v a ^ 2) := by
    calc
      (1 / (2 * Real.pi)) *
          |(∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ)|
          ≤ (1 / (2 * Real.pi)) * (Real.pi * (∫ θ in (0 : ℝ)..(2 * Real.pi), |Q S n u v θ|)) := by
              exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (1 / (2 * Real.pi)) * (Real.pi * (Real.pi * (∑ a ∈ S, u a ^ 2 + ∑ a ∈ S, v a ^ 2))) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (int_abs_Q_le S n hinj u v) (by positivity)) (by positivity)
      _ = (Real.pi / 2) * (∑ a ∈ S, u a ^ 2 + ∑ a ∈ S, v a ^ 2) := by
            field_simp [Real.pi_ne_zero]
  calc
    |∑ a ∈ S, ∑ b ∈ S, u a * v b * ((n a - n b : ℤ) : ℝ)⁻¹|
        = |(1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ)| := by rw [hA]
    _ = (1 / (2 * Real.pi)) *
        |(∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.pi - θ) * Q S n u v θ)| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    _ ≤ (Real.pi / 2) * (∑ a ∈ S, u a ^ 2 + ∑ a ∈ S, v a ^ 2) := hgoal

/-- Quadratic form of an antisymmetric real kernel vanishes. -/
lemma real_quad_zero (S : Finset ℝ) (n : ℝ → ℤ) (f : ℝ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ S, f a * f b * ((n a - n b : ℤ) : ℝ)⁻¹) = 0 := by
  classical
  let t : ℝ → ℝ → ℝ := fun i j => f i * f j * ((n i - n j : ℤ) : ℝ)⁻¹
  have hdiag : ∀ i ∈ S, t i i = 0 := by
    intro i hi
    dsimp [t]
    simp
  have hpair : ∀ i ∈ S, ∀ j ∈ S, t i j + t j i = 0 := by
    intro i hi j hj
    dsimp [t]
    have hm : ((n i - n j : ℤ) : ℝ)⁻¹ = -(((n j - n i : ℤ) : ℝ)⁻¹) := by
      have hz : ((n j - n i : ℤ) : ℝ) = -(((n i - n j : ℤ) : ℝ)) := by push_cast; ring
      rw [hz]
      rw [inv_neg]
      ring
    rw [hm]
    ring
  have h : (∑ a ∈ S, ∑ b ∈ S, t a b) = 0 := by
    rw [Commons.Algebra.BigOperators.sum_double_eq_diag_add_pairs (s := S) (f := t)]
    have hdi : (∑ i ∈ S, t i i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hdiag i hi
    have hpr : (∑ i ∈ S, ∑ j ∈ S, if i < j then t i j + t j i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hij : i < j
      · simp [hij, hpair i hi j hj]
      · simp [hij]
    rw [hdi, hpr]
    ring
  simpa [t] using h

lemma antim (n : ℝ → ℤ) (a b : ℝ) :
    ((n a - n b : ℤ) : ℝ)⁻¹ = -(((n b - n a : ℤ) : ℝ)⁻¹) := by
  have hz : ((n b - n a : ℤ) : ℝ) = -(((n a - n b : ℤ) : ℝ)) := by push_cast; ring
  rw [hz, inv_neg]
  ring

lemma double_sum_swap_real (S : Finset ℝ) (F : ℝ → ℝ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ S, F a b) = (∑ a ∈ S, ∑ b ∈ S, F b a) := by
  rw [Finset.sum_comm]

/-- B(u,v) = -B(v,u) for the antisymmetric kernel 1/(n a - n b). -/
lemma real_B_antisym (S : Finset ℝ) (n : ℝ → ℤ) (u v : ℝ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ S, u a * v b * ((n a - n b : ℤ) : ℝ)⁻¹) =
    - (∑ a ∈ S, ∑ b ∈ S, v a * u b * ((n a - n b : ℤ) : ℝ)⁻¹) := by
  calc
    (∑ a ∈ S, ∑ b ∈ S, u a * v b * ((n a - n b : ℤ) : ℝ)⁻¹)
        = ∑ a ∈ S, ∑ b ∈ S, v a * u b * ((n b - n a : ℤ) : ℝ)⁻¹ := by
            have hsw := double_sum_swap_real S (fun a b => u a * v b * ((n a - n b : ℤ) : ℝ)⁻¹)
            simpa [mul_comm, mul_left_comm, mul_assoc] using hsw
    _ = - (∑ a ∈ S, ∑ b ∈ S, v a * u b * ((n a - n b : ℤ) : ℝ)⁻¹) := by
            calc
              (∑ a ∈ S, ∑ b ∈ S, v a * u b * ((n b - n a : ℤ) : ℝ)⁻¹)
                  = ∑ a ∈ S, ∑ b ∈ S, -(v a * u b * ((n a - n b : ℤ) : ℝ)⁻¹) := by
                      refine Finset.sum_congr rfl ?_
                      intro a ha
                      refine Finset.sum_congr rfl ?_
                      intro b hb
                      rw [antim n b a]
                      ring
              _ = - (∑ a ∈ S, ∑ b ∈ S, v a * u b * ((n a - n b : ℤ) : ℝ)⁻¹) := by
                      simp_rw [Finset.sum_neg_distrib]

lemma z_mul_conj_expand (z w : ℂ) : z * conj w =
    (((z.re * w.re + z.im * w.im : ℝ) : ℂ)) + Complex.I * ((z.im * w.re - z.re * w.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma term_expand (z w : ℂ) (m : ℝ) : z * conj w * (m : ℂ) =
    ((((z.re * w.re + z.im * w.im) * m : ℝ) : ℂ)) + Complex.I * (((z.im * w.re - z.re * w.im) * m : ℝ) : ℂ) := by
  rw [z_mul_conj_expand]
  have hmul (r s : ℝ) : ((r : ℂ) * (s : ℂ)) = ((r * s : ℝ) : ℂ) := by
    exact (map_mul (algebraMap ℝ ℂ) r s).symm
  calc
    ((((z.re * w.re + z.im * w.im : ℝ) : ℂ) + Complex.I * ((z.im * w.re - z.re * w.im : ℝ) : ℂ)) * (m : ℂ))
        = ((((z.re * w.re + z.im * w.im) * m : ℝ) : ℂ)) +
            (Complex.I * ((z.im * w.re - z.re * w.im : ℝ) : ℂ)) * (m : ℂ) := by
            rw [add_mul]
            congr 1
            exact hmul (z.re * w.re + z.im * w.im) m
    _ = ((((z.re * w.re + z.im * w.im) * m : ℝ) : ℂ)) +
            Complex.I * ((((z.im * w.re - z.re * w.im) * m : ℝ) : ℂ)) := by
            congr 1
            rw [mul_assoc]
            congr 1
            exact hmul (z.im * w.re - z.re * w.im) m

lemma cast_sum_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (((∑ i ∈ s, f i : ℝ) : ℂ)) = ∑ i ∈ s, (f i : ℂ) := by
  exact map_sum (algebraMap ℝ ℂ) f s

lemma cast_sum_double (S : Finset ℝ) (F : ℝ → ℝ → ℝ) :
    (((∑ a ∈ S, ∑ b ∈ S, F a b : ℝ) : ℂ)) = ∑ a ∈ S, ∑ b ∈ S, (F a b : ℂ) := by
  calc
    (((∑ a ∈ S, ∑ b ∈ S, F a b : ℝ) : ℂ)) = ∑ a ∈ S, ((∑ b ∈ S, F a b : ℝ) : ℂ) := by
      exact cast_sum_real S (fun a => ∑ b ∈ S, F a b)
    _ = ∑ a ∈ S, ∑ b ∈ S, (F a b : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact cast_sum_real S (F a)

lemma norm_sq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Complex Hilbert inequality for an integer-injective map (constant π). -/
lemma re_mul_ofReal (z : ℂ) (m : ℝ) : (z * (m : ℂ)).re = z.re * m := by
  rw [Complex.mul_re]
  simp

lemma im_mul_ofReal (z : ℂ) (m : ℝ) : (z * (m : ℂ)).im = z.im * m := by
  rw [Complex.mul_im]
  simp

lemma re_zconj (z w : ℂ) : (z * conj w).re = z.re * w.re + z.im * w.im := by
  rw [Complex.mul_re]
  simp

lemma im_zconj (z w : ℂ) : (z * conj w).im = z.im * w.re - z.re * w.im := by
  rw [Complex.mul_im]
  simp
  ring

lemma re_zconj_m (z w : ℂ) (m : ℝ) :
    ((z * conj w) * (m : ℂ)).re = (z.re * w.re + z.im * w.im) * m := by
  rw [re_mul_ofReal, re_zconj]

lemma im_zconj_m (z w : ℂ) (m : ℝ) :
    ((z * conj w) * (m : ℂ)).im = (z.im * w.re - z.re * w.im) * m := by
  rw [im_mul_ofReal, im_zconj]

theorem int_hilbert_map (S : Finset ℝ) (n : ℝ → ℤ)
    (hinj : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → n a = n b → a = b)
    (z : ℝ → ℂ) :
    ‖∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * ((((n a - n b : ℤ) : ℝ)⁻¹ : ℝ) : ℂ)‖ ≤
      Real.pi * ∑ a ∈ S, ‖z a‖ ^ 2 := by
  let M : ℝ → ℝ → ℝ := fun a b => ((n a - n b : ℤ) : ℝ)⁻¹
  let x : ℝ → ℝ := fun a => (z a).re
  let y : ℝ → ℝ := fun a => (z a).im
  let Bxy : ℝ := ∑ a ∈ S, ∑ b ∈ S, x a * y b * M a b
  have hreal0 : (∑ a ∈ S, ∑ b ∈ S, (x a * x b + y a * y b) * M a b) = 0 := by
    have h1 := real_quad_zero S n x
    have h2 := real_quad_zero S n y
    calc
      (∑ a ∈ S, ∑ b ∈ S, (x a * x b + y a * y b) * M a b)
          = ∑ a ∈ S, ∑ b ∈ S, (x a * x b * M a b + y a * y b * M a b) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              ring
      _ = (∑ a ∈ S, ∑ b ∈ S, x a * x b * M a b) + (∑ a ∈ S, ∑ b ∈ S, y a * y b * M a b) := by
              simp_rw [Finset.sum_add_distrib]
      _ = 0 + 0 := by rw [h1, h2]
      _ = 0 := by ring
  have hmixed : (∑ a ∈ S, ∑ b ∈ S, (y a * x b - x a * y b) * M a b) = -2 * Bxy := by
    have hyx : (∑ a ∈ S, ∑ b ∈ S, y a * x b * M a b) =
        - (∑ a ∈ S, ∑ b ∈ S, x a * y b * M a b) := by
          dsimp [M]
          exact real_B_antisym S n y x
    calc
      (∑ a ∈ S, ∑ b ∈ S, (y a * x b - x a * y b) * M a b)
          = ∑ a ∈ S, ∑ b ∈ S, (y a * x b * M a b - x a * y b * M a b) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              ring
      _ = (∑ a ∈ S, ∑ b ∈ S, y a * x b * M a b) - (∑ a ∈ S, ∑ b ∈ S, x a * y b * M a b) := by
              simp_rw [Finset.sum_sub_distrib]
      _ = - (∑ a ∈ S, ∑ b ∈ S, x a * y b * M a b) - (∑ a ∈ S, ∑ b ∈ S, x a * y b * M a b) := by rw [hyx]
      _ = -2 * (∑ a ∈ S, ∑ b ∈ S, x a * y b * M a b) := by ring
  have hreV : (∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * (M a b : ℂ)).re =
      (∑ a ∈ S, ∑ b ∈ S, (x a * x b + y a * y b) * M a b) := by
    rw [re_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [re_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro b hb
    rw [re_zconj_m]
  have himV : (∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * (M a b : ℂ)).im =
      (∑ a ∈ S, ∑ b ∈ S, (y a * x b - x a * y b) * M a b) := by
    rw [im_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [im_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro b hb
    rw [im_zconj_m]
  have hV : (∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * (M a b : ℂ)) = -2 * Complex.I * (Bxy : ℂ) := by
    apply Complex.ext
    · calc
        (∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * (M a b : ℂ)).re
            = (∑ a ∈ S, ∑ b ∈ S, (x a * x b + y a * y b) * M a b) := hreV
        _ = 0 := hreal0
        _ = ((-2 * Complex.I) * (Bxy : ℂ)).re := by
              rw [Complex.mul_re]
              simp
    · calc
        (∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * (M a b : ℂ)).im
            = (∑ a ∈ S, ∑ b ∈ S, (y a * x b - x a * y b) * M a b) := himV
        _ = -2 * Bxy := hmixed
        _ = ((-2 * Complex.I) * (Bxy : ℂ)).im := by
              rw [Complex.mul_im]
              simp
  have hB : |Bxy| ≤ (Real.pi / 2) * (∑ a ∈ S, x a ^ 2 + ∑ a ∈ S, y a ^ 2) := by
    dsimp [Bxy, M]
    exact real_hilbert_bound S n hinj x y
  have hnorm : ‖(-2 * Complex.I) * (Bxy : ℂ)‖ = 2 * |Bxy| := by
    rw [norm_mul]
    have hnI : ‖(-2 * Complex.I : ℂ)‖ = 2 := by
      rw [norm_mul]
      rw [Complex.norm_I]
      norm_num
    rw [hnI]
    congr 1
    exact Complex.norm_real Bxy
  have hsum : (∑ a ∈ S, x a ^ 2 + ∑ a ∈ S, y a ^ 2) = ∑ a ∈ S, ‖z a‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro a ha
    dsimp [x, y]
    rw [norm_sq_re_im]
  calc
    ‖∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * ((((n a - n b : ℤ) : ℝ)⁻¹ : ℝ) : ℂ)‖
        = ‖∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * (M a b : ℂ)‖ := by rfl
    _ = ‖(-2 * Complex.I) * (Bxy : ℂ)‖ := by rw [hV]
    _ = 2 * |Bxy| := hnorm
    _ ≤ 2 * ((Real.pi / 2) * (∑ a ∈ S, x a ^ 2 + ∑ a ∈ S, y a ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = Real.pi * (∑ a ∈ S, x a ^ 2 + ∑ a ∈ S, y a ^ 2) := by ring
    _ = Real.pi * ∑ a ∈ S, ‖z a‖ ^ 2 := by rw [hsum]


lemma abs_int_eq_natAbs (n : ℤ) : |(n : ℝ)| = (n.natAbs : ℝ) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simp
  · simp [abs_neg]

lemma abs_sq_eq_nat (n : ℤ) : ((n : ℝ) ^ 2) = ((n.natAbs : ℝ) ^ 2) := by
  rw [← abs_int_eq_natAbs n]
  rw [sq_abs]

lemma one_le_sq_int {n : ℤ} (hn : n ≠ 0) : 1 ≤ ((n : ℝ) ^ 2) := by
  have h : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast (Int.natAbs_pos.mpr hn)
  have hs : ((n : ℝ) ^ 2) = ((n.natAbs : ℝ) ^ 2) := abs_sq_eq_nat n
  nlinarith [sq_nonneg ((n.natAbs : ℝ) - 1)]

lemma abs_inv_sub_eq (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    |p⁻¹ - q⁻¹| = |p - q| / (|p| * |q|) := by
  have h : p⁻¹ - q⁻¹ = (q - p) / (p * q) := by
    field_simp [hp, hq]
  rw [h, abs_div, abs_mul]
  rw [abs_sub_comm]

/-- If |p| ≥ 1 and |p − n| ≤ 1 (n : ℤ, n ≠ 0) then |1/p − 1/n| ≤ 2/n². -/
lemma inv_diff_le (p : ℝ) (n : ℤ) (hp : 1 ≤ |p|) (hpn : |p - (n : ℝ)| ≤ 1) (hn : n ≠ 0) :
    |p⁻¹ - ((n : ℝ)⁻¹)| ≤ 2 / ((n : ℝ) ^ 2) := by
  have hp0 : p ≠ 0 := by
    intro hpz
    rw [hpz] at hp
    norm_num at hp
  have hq0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hden_pos : 0 < |p| * |(n : ℝ)| := mul_pos (lt_of_lt_of_le zero_lt_one hp) (abs_pos.mpr hq0)
  have h1 : |p⁻¹ - ((n : ℝ)⁻¹)| ≤ 1 / (|p| * |(n : ℝ)|) := by
    rw [abs_inv_sub_eq p (n : ℝ) hp0 hq0]
    exact div_le_div_of_nonneg_right hpn (le_of_lt hden_pos)
  let d : ℝ := (n.natAbs : ℝ)
  have hqabs : |(n : ℝ)| = d := by
    dsimp [d]
    exact abs_int_eq_natAbs n
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast (Int.natAbs_pos.mpr hn)
  have hd1 : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (Nat.succ_le_of_lt (Int.natAbs_pos.mpr hn))
  have hpd : d / 2 ≤ |p| := by
    by_cases h2 : 2 ≤ d
    · have hdel := abs_sub_abs_le_abs_sub ((n : ℝ)) p
      have hpn2 : |(n : ℝ) - p| ≤ 1 := by
        simpa [abs_sub_comm] using hpn
      have hmain : |(n : ℝ)| - 1 ≤ |p| := by
        nlinarith [hdel, hpn2]
      rw [hqabs] at hmain
      nlinarith [hmain, h2]
    · have hdn : d < 2 := lt_of_not_ge h2
      have hk : ∃ k : ℕ, d = (k : ℝ) := ⟨n.natAbs, by dsimp [d]⟩
      rcases hk with ⟨k, hk⟩
      have hk2 : k < 2 := by
        have hkR : (k : ℝ) < 2 := by rwa [← hk]
        exact_mod_cast hkR
      have hk1 : 1 ≤ k := by
        have hkR : (1 : ℝ) ≤ k := by rwa [← hk]
        exact_mod_cast hkR
      have hk1' : k = 1 := by omega
      have hdle : d ≤ 1 := by
        rw [hk, hk1']
        norm_num
      nlinarith [hd1, hdle, hp]
  calc
    |p⁻¹ - ((n : ℝ)⁻¹)| ≤ 1 / (|p| * |(n : ℝ)|) := h1
    _ = 1 / (|p| * d) := by rw [hqabs]
    _ ≤ 2 / d ^ 2 := by
      have hden' : 0 < |p| * d := by positivity
      have hd0 : 0 ≤ d := le_of_lt hdpos
      have hmul : d * (d / 2) ≤ |p| * d := by
        nlinarith [hpd, hd0]
      have hrec : 1 / (|p| * d) ≤ 1 / (d * (d / 2)) := by
        exact one_div_le_one_div_of_le (by positivity : 0 < d * (d / 2)) hmul
      calc
        1 / (|p| * d) ≤ 1 / (d * (d / 2)) := hrec
        _ = 2 / d ^ 2 := by
              field_simp [hdpos.ne']
    _ = 2 / ((n : ℝ) ^ 2) := by
          have hn2 : ((n : ℝ) ^ 2) = d ^ 2 := by
            rw [← (sq_abs ((n : ℝ)))]
            rw [hqabs]
          rw [hn2]


lemma floor_diff_close (x y : ℝ) : |(x - y) - (((⌊x⌋ : ℝ) - (⌊y⌋ : ℝ)))| ≤ 1 := by
  have hx1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hx2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hy1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have hy2 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  rw [abs_le]
  constructor <;> linarith

-- ============ NEW: floor_sub_abs_lt_one ============
lemma floor_sub_abs_lt_one (u v : ℝ) (hf : ⌊u⌋ = ⌊v⌋) : |u - v| < 1 := by
  rw [abs_lt]
  have hu1 : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
  have hu2 : u < (⌊u⌋ : ℝ) + 1 := Int.lt_floor_add_one u
  have hv1 : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
  have hv2 : v < (⌊v⌋ : ℝ) + 1 := Int.lt_floor_add_one v
  have hfc : ((⌊u⌋ : ℤ) : ℝ) = ((⌊v⌋ : ℤ) : ℝ) := by exact_mod_cast hf
  constructor
  · linarith
  · linarith

-- ============ NEW: kernel_diff_bound (aux + main) ============
lemma kernel_diff_bound_aux (x y : ℝ) (m : ℤ) (hxy : 1 ≤ |x - y|)
    (hclose : |(x - y) - (m : ℝ)| ≤ 1) :
    |(x - y)⁻¹ - ((m : ℝ)⁻¹)| ≤ 4 / (1 + ((m : ℝ) ^ 2)) := by
  by_cases hm : m = 0
  · have h1 : |(x - y)⁻¹| ≤ 1 := by
      rw [abs_inv]
      exact inv_le_one_of_one_le₀ hxy
    rw [hm]
    simp only [Int.cast_zero, inv_zero, sub_zero, sq, zero_mul, add_zero, div_one]
    exact le_trans h1 (by norm_num)
  · have hb := inv_diff_le (x - y) m hxy hclose hm
    have hm2 : 1 ≤ ((m : ℝ) ^ 2) := one_le_sq_int hm
    have hle : 2 / ((m : ℝ) ^ 2) ≤ 4 / (1 + ((m : ℝ) ^ 2)) := by
      have hx0 : 0 < (m : ℝ) ^ 2 := lt_of_lt_of_le zero_lt_one hm2
      rw [div_le_div_iff₀ hx0 (by positivity : 0 < 1 + (m : ℝ) ^ 2)]
      nlinarith
    exact le_trans hb hle

lemma kernel_diff_bound (x y : ℝ) (hxy : 1 ≤ |x - y|) :
    |(x - y)⁻¹ - ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ)⁻¹| ≤
      4 / (1 + ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) ^ 2) := by
  exact kernel_diff_bound_aux x y (⌊x⌋ - ⌊y⌋) hxy (by simpa using floor_diff_close x y)

-- ============ NEW: floor_inj_sep, div_sep_ge_one ============
lemma floor_inj_sep (δ : ℝ) (hδ : 0 < δ) (a b : ℝ)
    (hsep : δ ≤ |a - b|) : ⌊a / δ⌋ = ⌊b / δ⌋ → a = b := by
  intro hf
  have habs : |a / δ - b / δ| < 1 := floor_sub_abs_lt_one (a / δ) (b / δ) hf
  have hdiv : |a / δ - b / δ| = |a - b| / δ := by
    rw [← sub_div]
    rw [abs_div]
    rw [abs_of_pos hδ]
  have hlt : |a - b| / δ < 1 := by simpa [hdiv] using habs
  have hlt' : |a - b| < δ := by
    have := (div_lt_iff₀ hδ).mp hlt
    simpa using this
  exact False.elim ((not_lt_of_ge hsep) hlt')

lemma div_sep_ge_one (δ : ℝ) (hδ : 0 < δ) (a b : ℝ) (hsep : δ ≤ |a - b|) :
    1 ≤ |a / δ - b / δ| := by
  have hdiv : |a / δ - b / δ| = |a - b| / δ := by
    rw [← sub_div]
    rw [abs_div]
    rw [abs_of_pos hδ]
  rw [hdiv]
  exact (le_div_iff₀ hδ).mpr (by simpa using hsep)

-- ============ NEW: inverse-square sums ============
lemma sum_Icc_inv_sq_le_two (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (((k : ℝ) ^ 2)⁻¹)) ≤ 2 := by
  by_cases hn : 1 ≤ n
  · have hset : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_Icc]
      constructor
      · intro h
        rcases h with ⟨h1k, hkn⟩
        by_cases hk : k = 1
        · exact Or.inl hk
        · exact Or.inr ⟨by omega, hkn⟩
      · intro h
        rcases h with rfl | h
        · exact ⟨by norm_num, hn⟩
        · rcases h with ⟨hk2, hkn⟩
          exact ⟨by omega, hkn⟩
    have hsplit : (∑ k ∈ Finset.Icc 1 n, (((k : ℝ) ^ 2)⁻¹))
        = 1 + (∑ k ∈ Finset.Icc 2 n, (((k : ℝ) ^ 2)⁻¹)) := by
      rw [hset, Finset.sum_insert]
      · norm_num
      · rw [Finset.mem_Icc]
        omega
    have hIooEq : Finset.Ioo 1 (n + 1) = Finset.Icc 2 n := by
      ext k
      simp only [Finset.mem_Ioo, Finset.mem_Icc]
      omega
    have hsmall : (∑ k ∈ Finset.Icc 2 n, (((k : ℝ) ^ 2)⁻¹)) ≤ 1 := by
      have hsum := sum_Ioo_inv_sq_le (α := ℝ) 1 (n + 1)
      rw [hIooEq] at hsum
      norm_num at hsum
      exact hsum
    calc
      (∑ k ∈ Finset.Icc 1 n, (((k : ℝ) ^ 2)⁻¹)) = 1 + (∑ k ∈ Finset.Icc 2 n, (((k : ℝ) ^ 2)⁻¹)) := hsplit
      _ ≤ 1 + 1 := by exact add_le_add (le_refl 1) hsmall
      _ = 2 := by norm_num
  · have hn0 : n = 0 := by omega
    subst n
    simp

lemma sum_inv_sq_le_two_of_one_le {A : Finset ℕ} (hA : ∀ k ∈ A, 1 ≤ k) :
    (∑ k ∈ A, (((k : ℝ) ^ 2)⁻¹)) ≤ 2 := by
  by_cases hne : A.Nonempty
  · let m := A.max' hne
    have hsub : A ⊆ Finset.Icc 1 m := by
      intro k hk
      exact (Finset.mem_Icc.mpr ⟨hA k hk, Finset.le_max' A k hk⟩)
    calc
      (∑ k ∈ A, (((k : ℝ) ^ 2)⁻¹))
          ≤ ∑ k ∈ Finset.Icc 1 m, (((k : ℝ) ^ 2)⁻¹) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro k hk hkA; positivity)
      _ ≤ 2 := sum_Icc_inv_sq_le_two m
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hAe]
    simp


-- ============ NEW: row bound ============
lemma sq_int_sub_comm (m n : ℤ) : ((m - n : ℤ) : ℝ) ^ 2 = ((n - m : ℤ) : ℝ) ^ 2 := by
  have h : ((m - n : ℤ) : ℝ) = -(((n - m : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [h]
  ring

lemma row_inv_one_add_sq_le (S : Finset ℝ) (q : ℝ → ℤ)
    (hinj : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → q a = q b → a = b)
    (a : ℝ) (ha : a ∈ S) :
    (∑ b ∈ S.erase a, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹) ≤ 4 := by
  let Fpos : Finset ℝ := (S.erase a).filter (fun b => q a < q b)
  let Fneg : Finset ℝ := (S.erase a).filter (fun b => q b < q a)
  have hmem : ∀ b ∈ S.erase a, q b ≠ q a := by
    intro b hb
    have hbS : b ∈ S := (Finset.mem_erase.mp hb).2
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    intro hq
    have : b = a := hinj (a := b) hbS (b := a) ha hq
    exact hba this
  have hdisj : Disjoint Fpos Fneg := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    have h1 : q a < q b := (Finset.mem_filter.mp hb1).2
    have h2 : q b < q a := (Finset.mem_filter.mp hb2).2
    exact (lt_asymm h1) h2
  have hunion : Fpos ∪ Fneg = S.erase a := by
    ext b
    simp only [Finset.mem_union]
    constructor
    · intro h
      rcases h with h1 | h2
      · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h2).1
    · intro hb
      have hqne : q b ≠ q a := hmem b hb
      by_cases h1 : q a < q b
      · exact Or.inl (Finset.mem_filter.mpr ⟨hb, h1⟩)
      · have hba2 : q b ≤ q a := le_of_not_gt h1
        have hlt : q b < q a := lt_of_le_of_ne hba2 hqne
        exact Or.inr (Finset.mem_filter.mpr ⟨hb, hlt⟩)
  have hpos : (∑ b ∈ Fpos, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹) ≤ 2 := by
    have hstep1 : (∑ b ∈ Fpos, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹)
        ≤ ∑ b ∈ Fpos, ((((q b - q a : ℤ) : ℝ) ^ 2)⁻¹) := by
      refine Finset.sum_le_sum ?_
      intro b hb
      have hlt : q a < q b := (Finset.mem_filter.mp hb).2
      have hm : ((q b - q a : ℤ) : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : (q b - q a : ℤ) ≠ 0)
      have hsqpos : 0 < ((q b - q a : ℤ) : ℝ) ^ 2 := sq_pos_of_ne_zero hm
      have hle1 : ((q b - q a : ℤ) : ℝ) ^ 2 ≤ 1 + ((q b - q a : ℤ) : ℝ) ^ 2 := by nlinarith
      simpa using (one_div_le_one_div_of_le hsqpos hle1)
    have hstep2 : (∑ b ∈ Fpos, ((((q b - q a : ℤ) : ℝ) ^ 2)⁻¹))
        = ∑ b ∈ Fpos, (((((q b - q a).natAbs : ℕ) : ℝ) ^ 2)⁻¹) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [abs_sq_eq_nat (q b - q a)]
    have hψ : Set.InjOn (fun b : ℝ => (q b - q a).natAbs) (↑Fpos : Set ℝ) := by
      intro b1 hb1 b2 hb2 hnat
      have hb1e : b1 ∈ S.erase a := (Finset.mem_filter.mp hb1).1
      have hb2e : b2 ∈ S.erase a := (Finset.mem_filter.mp hb2).1
      have hb1S : b1 ∈ S := (Finset.mem_erase.mp hb1e).2
      have hb2S : b2 ∈ S := (Finset.mem_erase.mp hb2e).2
      have hlt1 : q a < q b1 := (Finset.mem_filter.mp hb1).2
      have hlt2 : q a < q b2 := (Finset.mem_filter.mp hb2).2
      have hpos1 : 0 ≤ q b1 - q a := by omega
      have hpos2 : 0 ≤ q b2 - q a := by omega
      have hcast1 : (q b1 - q a : ℤ) = (((q b1 - q a).natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg hpos1).symm
      have hcast2 : (q b2 - q a : ℤ) = (((q b2 - q a).natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg hpos2).symm
      have hnat' : (((q b1 - q a).natAbs : ℕ) : ℤ) = (((q b2 - q a).natAbs : ℕ) : ℤ) := by exact_mod_cast hnat
      have hq : q b1 - q a = q b2 - q a := by
        rw [hcast1, hcast2, hnat']
      have hq' : q b1 = q b2 := by omega
      exact hinj (a := b1) hb1S (b := b2) hb2S hq'
    have hsumimg : (∑ b ∈ Fpos, (((((q b - q a).natAbs : ℕ) : ℝ) ^ 2)⁻¹))
        = ∑ k ∈ Fpos.image (fun b : ℝ => (q b - q a).natAbs), (((k : ℝ) ^ 2)⁻¹) := by
      exact (Finset.sum_image (s := Fpos) (g := fun b : ℝ => (q b - q a).natAbs)
        (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) hψ).symm
    have hA : ∀ k ∈ Fpos.image (fun b : ℝ => (q b - q a).natAbs), 1 ≤ k := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
      have hlt : q a < q b := (Finset.mem_filter.mp hb).2
      have hpos : 0 ≤ q b - q a := by omega
      have hcast : (q b - q a : ℤ) = (((q b - q a).natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg hpos).symm
      have hq : (1 : ℤ) ≤ (q b - q a : ℤ) := by omega
      have hq' : (1 : ℤ) ≤ (((q b - q a).natAbs : ℕ) : ℤ) := by rwa [hcast] at hq
      exact_mod_cast hq'
    calc
      (∑ b ∈ Fpos, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹)
          ≤ ∑ b ∈ Fpos, ((((q b - q a : ℤ) : ℝ) ^ 2)⁻¹) := hstep1
      _ = ∑ b ∈ Fpos, (((((q b - q a).natAbs : ℕ) : ℝ) ^ 2)⁻¹) := hstep2
      _ = ∑ k ∈ Fpos.image (fun b : ℝ => (q b - q a).natAbs), (((k : ℝ) ^ 2)⁻¹) := hsumimg
      _ ≤ 2 := sum_inv_sq_le_two_of_one_le hA
  have hneg : (∑ b ∈ Fneg, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹) ≤ 2 := by
    have hstep1 : (∑ b ∈ Fneg, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹)
        ≤ ∑ b ∈ Fneg, ((((q b - q a : ℤ) : ℝ) ^ 2)⁻¹) := by
      refine Finset.sum_le_sum ?_
      intro b hb
      have hlt : q b < q a := (Finset.mem_filter.mp hb).2
      have hm : ((q b - q a : ℤ) : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : (q b - q a : ℤ) ≠ 0)
      have hsqpos : 0 < ((q b - q a : ℤ) : ℝ) ^ 2 := sq_pos_of_ne_zero hm
      have hle1 : ((q b - q a : ℤ) : ℝ) ^ 2 ≤ 1 + ((q b - q a : ℤ) : ℝ) ^ 2 := by nlinarith
      simpa using (one_div_le_one_div_of_le hsqpos hle1)
    have hψ : Set.InjOn (fun b : ℝ => (q a - q b).natAbs) (↑Fneg : Set ℝ) := by
      intro b1 hb1 b2 hb2 hnat
      have hb1e : b1 ∈ S.erase a := (Finset.mem_filter.mp hb1).1
      have hb2e : b2 ∈ S.erase a := (Finset.mem_filter.mp hb2).1
      have hb1S : b1 ∈ S := (Finset.mem_erase.mp hb1e).2
      have hb2S : b2 ∈ S := (Finset.mem_erase.mp hb2e).2
      have hlt1 : q b1 < q a := (Finset.mem_filter.mp hb1).2
      have hlt2 : q b2 < q a := (Finset.mem_filter.mp hb2).2
      have hpos1 : 0 ≤ q a - q b1 := by omega
      have hpos2 : 0 ≤ q a - q b2 := by omega
      have hcast1 : (q a - q b1 : ℤ) = (((q a - q b1).natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg hpos1).symm
      have hcast2 : (q a - q b2 : ℤ) = (((q a - q b2).natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg hpos2).symm
      have hnat' : (((q a - q b1).natAbs : ℕ) : ℤ) = (((q a - q b2).natAbs : ℕ) : ℤ) := by exact_mod_cast hnat
      have hq : q a - q b1 = q a - q b2 := by
        rw [hcast1, hcast2, hnat']
      have hq' : q b1 = q b2 := by omega
      exact hinj (a := b1) hb1S (b := b2) hb2S hq'
    have hrew : (∑ b ∈ Fneg, ((((q b - q a : ℤ) : ℝ) ^ 2)⁻¹))
        = ∑ b ∈ Fneg, ((((q a - q b : ℤ) : ℝ) ^ 2)⁻¹) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      congr 1
      exact sq_int_sub_comm (q b) (q a)
    have hsumimg : (∑ b ∈ Fneg, (((((q a - q b).natAbs : ℕ) : ℝ) ^ 2)⁻¹))
        = ∑ k ∈ Fneg.image (fun b : ℝ => (q a - q b).natAbs), (((k : ℝ) ^ 2)⁻¹) := by
      exact (Finset.sum_image (s := Fneg) (g := fun b : ℝ => (q a - q b).natAbs)
        (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) hψ).symm
    have hA : ∀ k ∈ Fneg.image (fun b : ℝ => (q a - q b).natAbs), 1 ≤ k := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
      have hlt : q b < q a := (Finset.mem_filter.mp hb).2
      have hpos : 0 ≤ q a - q b := by omega
      have hcast : (q a - q b : ℤ) = (((q a - q b).natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg hpos).symm
      have hq : (1 : ℤ) ≤ (q a - q b : ℤ) := by omega
      have hq' : (1 : ℤ) ≤ (((q a - q b).natAbs : ℕ) : ℤ) := by rwa [hcast] at hq
      exact_mod_cast hq'
    calc
      (∑ b ∈ Fneg, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹)
          ≤ ∑ b ∈ Fneg, ((((q b - q a : ℤ) : ℝ) ^ 2)⁻¹) := hstep1
      _ = ∑ b ∈ Fneg, ((((q a - q b : ℤ) : ℝ) ^ 2)⁻¹) := hrew
      _ = ∑ b ∈ Fneg, (((((q a - q b).natAbs : ℕ) : ℝ) ^ 2)⁻¹) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [abs_sq_eq_nat (q a - q b)]
      _ = ∑ k ∈ Fneg.image (fun b : ℝ => (q a - q b).natAbs), (((k : ℝ) ^ 2)⁻¹) := hsumimg
      _ ≤ 2 := sum_inv_sq_le_two_of_one_le hA
  calc
    (∑ b ∈ S.erase a, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹)
        = ∑ b ∈ Fpos ∪ Fneg, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹ := by rw [← hunion]
    _ = (∑ b ∈ Fpos, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹)
        + (∑ b ∈ Fneg, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹) := Finset.sum_union hdisj
    _ ≤ 2 + 2 := add_le_add hpos hneg
    _ = 4 := by norm_num

lemma row_four_div_one_add_sq_le (S : Finset ℝ) (q : ℝ → ℤ)
    (hinj : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → q a = q b → a = b)
    (a : ℝ) (ha : a ∈ S) :
    (∑ b ∈ S.erase a, 4 / (1 + (((q b - q a : ℤ) : ℝ) ^ 2))) ≤ 16 := by
  have hrow := row_inv_one_add_sq_le S q hinj a ha
  calc
    (∑ b ∈ S.erase a, 4 / (1 + (((q b - q a : ℤ) : ℝ) ^ 2)))
        = 4 * (∑ b ∈ S.erase a, (1 + (((q b - q a : ℤ) : ℝ) ^ 2))⁻¹) := by
            rw [Finset.mul_sum]
            rfl
    _ ≤ 4 * 4 := by exact mul_le_mul_of_nonneg_left hrow (by norm_num)
    _ = 16 := by norm_num

-- ============ NEW: error bound ============
lemma double_sum_erase_comm (S : Finset ℝ) (F : ℝ → ℝ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ S.erase a, F a b) = (∑ b ∈ S, ∑ a ∈ S.erase b, F a b) := by
  classical
  calc
    (∑ a ∈ S, ∑ b ∈ S.erase a, F a b)
        = (∑ a ∈ S, ((∑ b ∈ S, F a b) - F a a)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Finset.sum_erase_eq_sub (s := S) (f := fun b : ℝ => F a b) ha]
    _ = (∑ a ∈ S, ∑ b ∈ S, F a b) - (∑ a ∈ S, F a a) := by
            simp_rw [Finset.sum_sub_distrib]
    _ = (∑ b ∈ S, ∑ a ∈ S, F a b) - (∑ a ∈ S, F a a) := by
            rw [Finset.sum_comm]
    _ = (∑ b ∈ S, ((∑ a ∈ S, F a b) - F b b)) := by
            simp_rw [Finset.sum_sub_distrib]
    _ = ∑ b ∈ S, ∑ a ∈ S.erase b, F a b := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [← Finset.sum_erase_eq_sub (s := S) (f := fun a : ℝ => F a b) hb]

lemma mul_le_sq_add_sq (x y : ℝ) : x * y ≤ x ^ 2 + y ^ 2 := by
  have h1 : 0 ≤ (x - y / 2) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (3 / 4 : ℝ) * y ^ 2 := by positivity
  nlinarith [h1, h2]

lemma sep_err_bound (S : Finset ℝ) (p : ℝ → ℝ) (z : ℝ → ℂ)
    (hp : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → ⌊p a⌋ = ⌊p b⌋ → a = b)
    (hsep : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → a ≠ b → 1 ≤ |p a - p b|) :
    ‖∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) *
        ((((p a - p b : ℝ)⁻¹ - ((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹) : ℝ) : ℂ)‖ ≤
      32 * (∑ a ∈ S, ‖z a‖ ^ 2) := by
  let q : ℝ → ℤ := fun x => ⌊p x⌋
  let e : ℝ → ℝ → ℝ := fun a b => ((p a - p b : ℝ)⁻¹ - ((q a - q b : ℤ) : ℝ)⁻¹)
  let c : ℝ → ℝ → ℝ := fun a b => 4 / (1 + (((q b - q a : ℤ) : ℝ) ^ 2))
  let T : ℝ → ℝ → ℂ := fun a b => z a * conj (z b) * (e a b : ℂ)
  let A : ℝ → ℝ := fun a => ‖z a‖ ^ 2
  have hqinj : ∀ ⦃a : ℝ⦄, a ∈ S → ∀ ⦃b : ℝ⦄, b ∈ S → q a = q b → a = b := by
    intro a ha b hb hq
    have : ⌊p a⌋ = ⌊p b⌋ := by simpa [q] using hq
    exact hp (a := a) ha (b := b) hb this
  have hnorm : ‖∑ a ∈ S, ∑ b ∈ S.erase a, T a b‖ ≤ ∑ a ∈ S, ∑ b ∈ S.erase a, ‖T a b‖ := by
    have h1 := norm_sum_le S (fun a => ∑ b ∈ S.erase a, T a b)
    have h2 : ∀ a ∈ S, ‖∑ b ∈ S.erase a, T a b‖ ≤ ∑ b ∈ S.erase a, ‖T a b‖ := by
      intro a ha
      exact norm_sum_le (S.erase a) (fun b => T a b)
    exact le_trans h1 (Finset.sum_le_sum h2)
  have hterm : ∀ a ∈ S, ∀ b ∈ S.erase a, ‖T a b‖ ≤ (A a + A b) * c a b := by
    intro a ha b hb
    have hbS : b ∈ S := (Finset.mem_erase.mp hb).2
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hne : a ≠ b := hba.symm
    have hsep1 : 1 ≤ |p a - p b| := hsep ha hbS hne
    have hk := kernel_diff_bound (p a) (p b) hsep1
    have hk2 : |e a b| ≤ 4 / (1 + (((q a - q b : ℤ) : ℝ) ^ 2)) := by
      simpa [e, q] using hk
    have hs : 4 / (1 + (((q a - q b : ℤ) : ℝ) ^ 2)) = 4 / (1 + (((q b - q a : ℤ) : ℝ) ^ 2)) := by
      rw [sq_int_sub_comm (q a) (q b)]
    have hk3 : |e a b| ≤ c a b := by
      dsimp [c]
      exact le_trans hk2 (le_of_eq hs)
    have hn : ‖T a b‖ = ‖z a‖ * ‖z b‖ * |e a b| := by
      dsimp [T]
      simp
    calc
      ‖T a b‖ = ‖z a‖ * ‖z b‖ * |e a b| := hn
      _ ≤ ‖z a‖ * ‖z b‖ * c a b := by
            exact mul_le_mul_of_nonneg_left hk3 (by positivity : 0 ≤ ‖z a‖ * ‖z b‖)
      _ ≤ (A a + A b) * c a b := by
            have hxy : ‖z a‖ * ‖z b‖ ≤ A a + A b := by
              dsimp [A]
              exact mul_le_sq_add_sq (‖z a‖) (‖z b‖)
            have hc : 0 ≤ c a b := by
              dsimp [c]
              positivity
            exact mul_le_mul_of_nonneg_right hxy hc
  have h1 : (∑ a ∈ S, ∑ b ∈ S.erase a, ‖T a b‖)
      ≤ ∑ a ∈ S, ∑ b ∈ S.erase a, (A a + A b) * c a b := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact hterm a ha b hb
  have hsplit : (∑ a ∈ S, ∑ b ∈ S.erase a, (A a + A b) * c a b)
      = (∑ a ∈ S, ∑ b ∈ S.erase a, A a * c a b) + (∑ a ∈ S, ∑ b ∈ S.erase a, A b * c a b) := by
        calc
          (∑ a ∈ S, ∑ b ∈ S.erase a, (A a + A b) * c a b)
              = ∑ a ∈ S, ∑ b ∈ S.erase a, (A a * c a b + A b * c a b) := by
                  refine Finset.sum_congr rfl ?_
                  intro a ha
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  ring
          _ = (∑ a ∈ S, ∑ b ∈ S.erase a, A a * c a b) + (∑ a ∈ S, ∑ b ∈ S.erase a, A b * c a b) := by
                  simp_rw [Finset.sum_add_distrib]
  have hrow_a : ∀ a ∈ S, (∑ b ∈ S.erase a, c a b) ≤ 16 := by
    intro a ha
    simpa [c] using (row_four_div_one_add_sq_le S q hqinj a ha)
  have hpart1 : (∑ a ∈ S, ∑ b ∈ S.erase a, A a * c a b) ≤ 16 * (∑ a ∈ S, A a) := by
    calc
      (∑ a ∈ S, ∑ b ∈ S.erase a, A a * c a b)
          = (∑ a ∈ S, A a * (∑ b ∈ S.erase a, c a b)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [← Finset.mul_sum]
      _ ≤ (∑ a ∈ S, A a * 16) := by
              refine Finset.sum_le_sum ?_
              intro a ha
              exact mul_le_mul_of_nonneg_left (hrow_a a ha) (by positivity : 0 ≤ A a)
      _ = 16 * (∑ a ∈ S, A a) := by
              rw [← Finset.sum_mul]
              ring
  have hrow_b : ∀ b ∈ S, (∑ a ∈ S.erase b, c a b) ≤ 16 := by
    intro b hb
    have h : (∑ a ∈ S.erase b, c a b) = ∑ a ∈ S.erase b, 4 / (1 + (((q a - q b : ℤ) : ℝ) ^ 2)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      dsimp [c]
      rw [sq_int_sub_comm (q b) (q a)]
    rw [h]
    exact row_four_div_one_add_sq_le S q hqinj b hb
  have hpart2 : (∑ a ∈ S, ∑ b ∈ S.erase a, A b * c a b) ≤ 16 * (∑ a ∈ S, A a) := by
    calc
      (∑ a ∈ S, ∑ b ∈ S.erase a, A b * c a b)
          = (∑ b ∈ S, ∑ a ∈ S.erase b, A b * c a b) := double_sum_erase_comm S (fun a b => A b * c a b)
      _ = (∑ b ∈ S, A b * (∑ a ∈ S.erase b, c a b)) := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              rw [← Finset.mul_sum]
      _ ≤ (∑ b ∈ S, A b * 16) := by
              refine Finset.sum_le_sum ?_
              intro b hb
              exact mul_le_mul_of_nonneg_left (hrow_b b hb) (by positivity : 0 ≤ A b)
      _ = 16 * (∑ a ∈ S, A a) := by
              rw [← Finset.sum_mul]
              ring
  have hbound : (∑ a ∈ S, ∑ b ∈ S.erase a, ‖T a b‖) ≤ 32 * (∑ a ∈ S, A a) := by
    calc
      (∑ a ∈ S, ∑ b ∈ S.erase a, ‖T a b‖)
          ≤ ∑ a ∈ S, ∑ b ∈ S.erase a, (A a + A b) * c a b := h1
      _ = (∑ a ∈ S, ∑ b ∈ S.erase a, A a * c a b) + (∑ a ∈ S, ∑ b ∈ S.erase a, A b * c a b) := hsplit
      _ ≤ 16 * (∑ a ∈ S, A a) + 16 * (∑ a ∈ S, A a) := add_le_add hpart1 hpart2
      _ = 32 * (∑ a ∈ S, A a) := by ring
  have hmain : ‖∑ a ∈ S, ∑ b ∈ S.erase a, T a b‖ ≤ 32 * (∑ a ∈ S, A a) := by
    exact le_trans hnorm hbound
  simpa [T, e, q, A] using hmain

-- ============ NEW: small assembly helpers ============
lemma sum_if_eq_erase (S : Finset ℝ) (F : ℝ → ℝ → ℂ) :
    (∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else F a b) = ∑ a ∈ S, ∑ b ∈ S.erase a, F a b := by
  classical
  refine Finset.sum_congr rfl ?_
  intro a ha
  calc
    (∑ b ∈ S, if a = b then 0 else F a b)
        = (∑ b ∈ S.erase a, if a = b then 0 else F a b) + (if a = a then 0 else F a a) := by
            rw [← Finset.sum_erase_add S (fun b : ℝ => if a = b then 0 else F a b) ha]
    _ = (∑ b ∈ S.erase a, F a b) := by
            have h0 : (if a = a then 0 else F a a) = 0 := by simp
            have hfun : ∀ b ∈ S.erase a, (if a = b then 0 else F a b) = F a b := by
              intro b hb
              have hne : a ≠ b := (Finset.mem_erase.mp hb).1.symm
              simp [hne]
            rw [h0, add_zero]
            refine Finset.sum_congr rfl ?_
            intro b hb
            exact hfun b hb

lemma sum_double_erase_eq_full (S : Finset ℝ) (F : ℝ → ℝ → ℂ) (hdiag : ∀ a ∈ S, F a a = 0) :
    (∑ a ∈ S, ∑ b ∈ S.erase a, F a b) = ∑ a ∈ S, ∑ b ∈ S, F a b := by
  refine Finset.sum_congr rfl ?_
  intro a ha
  calc
    (∑ b ∈ S.erase a, F a b) = (∑ b ∈ S.erase a, F a b) + F a a := by rw [hdiag a ha, add_zero]
    _ = (∑ b ∈ S, F a b) := (Finset.sum_erase_add S (fun b : ℝ => F a b) ha)

lemma inv_sub_div_eq (a b δ : ℝ) (hδ : δ ≠ 0) :
    (a - b : ℝ)⁻¹ = (δ : ℝ)⁻¹ * (a / δ - b / δ)⁻¹ := by
  have h1 : (a - b : ℝ) = δ * (a / δ - b / δ) := by
    field_simp [hδ]
  calc
    (a - b : ℝ)⁻¹ = (δ * (a / δ - b / δ))⁻¹ := by rw [h1]
    _ = (δ : ℝ)⁻¹ * (a / δ - b / δ)⁻¹ := by rw [mul_inv]

end MvHilbert

namespace Commons.LinearAlgebra.Matrix

theorem mv_hilbert_separated :
    ∃ C_H : ℝ, 0 < C_H ∧
      ∀ (δ : ℝ), 0 < δ → ∀ (S : Finset ℝ) (z : ℝ → ℂ),
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ |a - b|) →
          ‖∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ)‖ ≤
            C_H / δ * ∑ a ∈ S, ‖z a‖ ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨Real.pi + 32, by nlinarith, ?_⟩
  intro δ hδ S z hsep
  let p : ℝ → ℝ := fun a => a / δ
  let C : ℂ := (((δ : ℝ)⁻¹ : ℝ) : ℂ)
  let V : ℂ := ∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * (((p a - p b : ℝ)⁻¹ : ℝ) : ℂ)
  let I : ℂ := ∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * ((((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹ : ℝ) : ℂ)
  let E : ℂ := ∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) *
    (((((p a - p b : ℝ)⁻¹ - ((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹) : ℝ) : ℂ))
  have horig : (∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ))
      = (∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ)) := by
    exact MvHilbert.sum_if_eq_erase S (fun a b => z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ))
  have hsc : (∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ)) = C * V := by
    dsimp [C, V]
    calc
      (∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ))
          = ∑ a ∈ S, ∑ b ∈ S.erase a,
              (((δ : ℝ)⁻¹ : ℝ) : ℂ) * (z a * conj (z b) * (((p a - p b : ℝ)⁻¹ : ℝ) : ℂ)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              have hrid : (a - b : ℝ)⁻¹ = (δ : ℝ)⁻¹ * (p a - p b)⁻¹ := by
                have h1 : (a - b : ℝ) = δ * (p a - p b) := by
                  dsimp [p]
                  field_simp [hδ.ne']
                calc
                  (a - b : ℝ)⁻¹ = (δ * (p a - p b))⁻¹ := by rw [h1]
                  _ = (δ : ℝ)⁻¹ * (p a - p b)⁻¹ := by rw [mul_inv]
              rw [hrid]
              push_cast
              ring
      _ = (((δ : ℝ)⁻¹ : ℝ) : ℂ) * (∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * (((p a - p b : ℝ)⁻¹ : ℝ) : ℂ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [Finset.mul_sum]
  have hVie : V = I + E := by
    dsimp [V, I, E]
    calc
      (∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * (((p a - p b : ℝ)⁻¹ : ℝ) : ℂ))
          = ∑ a ∈ S, ∑ b ∈ S.erase a,
              (z a * conj (z b) * ((((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹ : ℝ) : ℂ)
                + z a * conj (z b) * (((((p a - p b : ℝ)⁻¹ - ((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹) : ℝ) : ℂ))) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              have hx : (p a - p b : ℝ)⁻¹
                  = ((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹ + ((p a - p b : ℝ)⁻¹ - ((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹) := by ring
              rw [hx]
              push_cast
              ring
      _ = (∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * ((((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹ : ℝ) : ℂ))
          + (∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * (((((p a - p b : ℝ)⁻¹ - ((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹) : ℝ) : ℂ))) := by
              simp_rw [Finset.sum_add_distrib]
  have hqinj : ∀ a ∈ S, ∀ b ∈ S, ⌊p a⌋ = ⌊p b⌋ → a = b := by
    intro a ha b hb hf
    by_cases hab : a = b
    · exact hab
    · have hsep' : δ ≤ |a - b| := hsep a ha b hb hab
      have hfl : ⌊a / δ⌋ = ⌊b / δ⌋ := by simpa [p] using hf
      exact MvHilbert.floor_inj_sep δ hδ a b hsep' hfl
  have hdiagI : ∀ a ∈ S, z a * conj (z a) * ((((⌊p a⌋ - ⌊p a⌋ : ℤ) : ℝ)⁻¹ : ℝ) : ℂ) = 0 := by
    intro a ha
    simp
  have hIfull : I = (∑ a ∈ S, ∑ b ∈ S, z a * conj (z b) * ((((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
    dsimp [I]
    exact MvHilbert.sum_double_erase_eq_full S
      (fun a b => z a * conj (z b) * ((((⌊p a⌋ - ⌊p b⌋ : ℤ) : ℝ)⁻¹ : ℝ) : ℂ)) hdiagI
  have hInorm : ‖I‖ ≤ Real.pi * (∑ a ∈ S, ‖z a‖ ^ 2) := by
    rw [hIfull]
    exact MvHilbert.int_hilbert_map S (fun a => ⌊p a⌋) hqinj z
  have hsep1 : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ |p a - p b| := by
    intro a ha b hb hab
    have hsep' : δ ≤ |a - b| := hsep a ha b hb hab
    simpa [p] using (MvHilbert.div_sep_ge_one δ hδ a b hsep')
  have hEnorm : ‖E‖ ≤ 32 * (∑ a ∈ S, ‖z a‖ ^ 2) := by
    dsimp [E]
    exact MvHilbert.sep_err_bound S p z hqinj hsep1
  have hVnorm : ‖V‖ ≤ (Real.pi + 32) * (∑ a ∈ S, ‖z a‖ ^ 2) := by
    have hvle : ‖V‖ ≤ ‖I‖ + ‖E‖ := by
      rw [hVie]
      exact norm_add_le I E
    calc
      ‖V‖ ≤ ‖I‖ + ‖E‖ := hvle
      _ ≤ Real.pi * (∑ a ∈ S, ‖z a‖ ^ 2) + 32 * (∑ a ∈ S, ‖z a‖ ^ 2) := add_le_add hInorm hEnorm
      _ = (Real.pi + 32) * (∑ a ∈ S, ‖z a‖ ^ 2) := by ring
  calc
    ‖∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ)‖
        = ‖∑ a ∈ S, ∑ b ∈ S.erase a, z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ)‖ := by rw [horig]
    _ = ‖C * V‖ := by rw [hsc]
    _ = ‖C‖ * ‖V‖ := by rw [norm_mul]
    _ = (δ : ℝ)⁻¹ * ‖V‖ := by
          have hC : ‖C‖ = (δ : ℝ)⁻¹ := by
            dsimp [C]
            rw [Complex.norm_real]
            rw [Real.norm_eq_abs]
            exact abs_of_pos (inv_pos.mpr hδ)
          rw [hC]
    _ ≤ (δ : ℝ)⁻¹ * ((Real.pi + 32) * (∑ a ∈ S, ‖z a‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hVnorm (le_of_lt (inv_pos.mpr hδ))
    _ = (Real.pi + 32) / δ * (∑ a ∈ S, ‖z a‖ ^ 2) := by ring

end Commons.LinearAlgebra.Matrix