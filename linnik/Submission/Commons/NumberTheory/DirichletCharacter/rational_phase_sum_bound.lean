import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.primePowSubgroup_quadratic_sum_bound
import Submission.Commons.NumberTheory.DirichletCharacter.primePowKernel_geom_sum_zmod
import Submission.Commons.Algebra.BigOperators.sum_range_mul_eq
import Submission.Commons.NumberTheory.DirichletCharacter.quadratic_deriv_dvd_iff
import Submission.Commons.NumberTheory.DirichletCharacter.rational_phase_cond_deg2
import Submission.Commons.NumberTheory.DirichletCharacter.rational_phase_lift

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

/-!
## Stationary phase for a `p`-adically shallow rational phase

Everything in this file serves the target `rational_phase_sum_bound`: the stationary-phase
factorisation `phase_factor`, the orthogonality on the top kernel `inner_sum_eval`, the
reindexing `range_split`, and the reduction of the surviving-class condition `cond_zero_iff`,
assembled in the strong induction `main_aux`.
-/

private lemma poly2_eq (Q : Polynomial ℤ) (h : Q.natDegree ≤ 2) :
    Q = Polynomial.C (Q.coeff 0) + Polynomial.C (Q.coeff 1) * Polynomial.X
        + Polynomial.C (Q.coeff 2) * Polynomial.X ^ 2 := by
  conv_lhs => rw [Q.as_sum_range_C_mul_X_pow]
  have hsum : (∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (Q.coeff i) * Polynomial.X ^ i)
      = ∑ i ∈ Finset.range 3, Polynomial.C (Q.coeff i) * Polynomial.X ^ i := by
    refine Finset.sum_subset (fun i hi => ?_) (fun i hi3 hni => ?_)
    · simp only [Finset.mem_range] at hi ⊢; omega
    · simp only [Finset.mem_range] at hi3 hni
      have : Q.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  ring

private lemma eval2 (Q : Polynomial ℤ) (h : Q.natDegree ≤ 2) (x : ℤ) :
    Q.eval x = Q.coeff 0 + Q.coeff 1 * x + Q.coeff 2 * x ^ 2 := by
  conv_lhs => rw [poly2_eq Q h]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]

private lemma deriv_eval2 (Q : Polynomial ℤ) (h : Q.natDegree ≤ 2) (x : ℤ) :
    (Polynomial.derivative Q).eval x = Q.coeff 1 + 2 * Q.coeff 2 * x := by
  conv_lhs => rw [poly2_eq Q h]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero,
    Polynomial.eval_one]
  ring_nf

private lemma eval_add_expand (Q : Polynomial ℤ) (h : Q.natDegree ≤ 2) (x d : ℤ) :
    Q.eval (x + d) = Q.eval x + d * (Polynomial.derivative Q).eval x + d ^ 2 * Q.coeff 2 := by
  rw [eval2 Q h (x + d), eval2 Q h x, deriv_eval2 Q h x]
  ring

private lemma isCoprime_prime_int (p : ℕ) [Fact p.Prime] (x : ℤ) (h : ¬ (p : ℤ) ∣ x) :
    IsCoprime (p : ℤ) x := by
  rw [Int.isCoprime_iff_nat_coprime]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun hd => h ((Int.natAbs_dvd_natAbs).mp (by simpa using hd)))

private lemma isUnit_of_not_dvd (p e : ℕ) [Fact p.Prime] (x : ℤ) (h : ¬ (p : ℤ) ∣ x) :
    IsUnit ((x : ℤ) : ZMod (p ^ e)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  exact (isCoprime_prime_int p x h).pow_left

private lemma A_val_mod (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (A : ZMod (p ^ e))
    (hA : (p : ZMod (p ^ e)) ∣ A - 1) : ((A.val : ℕ) : ZMod p) = 1 := by
  obtain ⟨w, hw⟩ := hA
  have hdvd : p ∣ p ^ e := by simpa using pow_dvd_pow p he
  have hcast : ZMod.castHom hdvd (ZMod p) A = 1 := by
    have h2 : A = 1 + (p : ZMod (p ^ e)) * w := by rw [← hw]; ring
    rw [h2, map_add, map_mul, map_one]
    simp
  rw [← hcast, ZMod.castHom_apply, ZMod.cast_eq_val]

/-- Mod-`p` condition ensuring the stationary-phase factorisation. -/
private lemma phase_cond (p e a : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (A : ZMod (p ^ e)) (hA : (p : ZMod (p ^ e)) ∣ A - 1)
    (N₂ G₂ : Polynomial ℤ) (hG : G₂.natDegree ≤ 2)
    (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0) (ha : 1 ≤ a) (y : ℕ) :
    (p : ℤ) ∣ (N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ)
      - ((((((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p)
            * (((G₂.coeff 0 : ℤ) : ZMod p))⁻¹ ^ 2).val : ℤ))
          * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
              * G₂.eval (y : ℤ)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hA1 : ((A.val : ℕ) : ZMod p) = 1 := A_val_mod p e he A hA
  have hGy : ((G₂.eval (y : ℤ) : ℤ) : ZMod p) = ((G₂.coeff 0 : ℤ) : ZMod p) := by
    have h1 : ((G₂.coeff 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (G₂.coeff 1) p).mpr hG1
    have h2 : ((G₂.coeff 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (G₂.coeff 2) p).mpr hG2
    rw [eval2 G₂ hG (y : ℤ)]
    push_cast
    rw [h1, h2]; ring
  have hGder : (((G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p) = 0 := by
    have h1 : ((G₂.coeff 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (G₂.coeff 1) p).mpr hG1
    have h2 : ((G₂.coeff 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (G₂.coeff 2) p).mpr hG2
    rw [deriv_eval2 G₂ hG (y : ℤ)]
    push_cast
    rw [h1, h2]; ring
  have hg0 : (((G₂.coeff 0 : ℤ) : ZMod p)) ≠ 0 := by
    intro h
    exact hG0 ((ZMod.intCast_zmod_eq_zero_iff_dvd (G₂.coeff 0) p).mp h)
  have hWval : (N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ)
      = (N₂.derivative).eval (y : ℤ) * G₂.eval (y : ℤ)
        - N₂.eval (y : ℤ) * (G₂.derivative).eval (y : ℤ) := by
    simp [Polynomial.eval_sub, Polynomial.eval_mul]
  rw [hWval]
  push_cast
  rw [ZMod.natCast_zmod_val]
  have hp0 : (((p : ℕ)) : ZMod p) = 0 := by simp
  rw [hA1, hGy, hGder, hp0]
  simp only [mul_zero, zero_mul, mul_one, add_zero]
  field_simp
  rw [zero_pow (by omega : a ≠ 0)]
  ring

private lemma pow_pred_mul_dvd {p e : ℕ} (he : 1 ≤ e) {Y : ℤ} (h : (p : ℤ) ∣ Y) :
    (p : ℤ) ^ e ∣ (p : ℤ) ^ (e - 1) * Y := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, ?_⟩
  rw [hs]
  have hpe : (p : ℤ) ^ e = (p : ℤ) ^ (e - 1) * (p : ℤ) := by
    conv_lhs => rw [show e = (e - 1) + 1 by omega, pow_succ]
  rw [hpe]
  ring

private lemma add_mul_inv_mul {R : Type*} [CommRing R] [Inv R] (A B G : R) (h : G * G⁻¹ = 1) :
    (A + B * G⁻¹) * G = A * G + B := by
  rw [add_mul, mul_assoc B G⁻¹ G, mul_comm G⁻¹ G, h, mul_one]

private lemma G₂_eval_sub_coeff0_dvd (p : ℕ) [Fact p.Prime] (G₂ : Polynomial ℤ)
    (hG : G₂.natDegree ≤ 2) (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (y : ℕ) : (p : ℤ) ∣ G₂.eval (y : ℤ) - G₂.coeff 0 := by
  have h : G₂.eval (y : ℤ) - G₂.coeff 0
      = G₂.coeff 1 * (y : ℤ) + G₂.coeff 2 * (y : ℤ) ^ 2 := by
    rw [eval2 G₂ hG (y : ℤ)]; ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left hG1 _) (dvd_mul_of_dvd_left hG2 _)

private lemma G₂_deriv_eval_dvd (p : ℕ) [Fact p.Prime] (G₂ : Polynomial ℤ)
    (hG : G₂.natDegree ≤ 2) (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (y : ℕ) : (p : ℤ) ∣ (G₂.derivative).eval (y : ℤ) := by
  rw [deriv_eval2 G₂ hG (y : ℤ)]
  exact dvd_add hG1 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hG2 (2:ℤ)) (y:ℤ))

private lemma G₂_eval_not_dvd (p : ℕ) [Fact p.Prime] (G₂ : Polynomial ℤ)
    (hG : G₂.natDegree ≤ 2) (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0) (y : ℕ) : ¬ (p : ℤ) ∣ G₂.eval (y : ℤ) := by
  intro h
  have h1 := G₂_eval_sub_coeff0_dvd p G₂ hG hG1 hG2 y
  have h2 : (p : ℤ) ∣ G₂.eval (y : ℤ) - (G₂.eval (y : ℤ) - G₂.coeff 0) := dvd_sub h h1
  rw [sub_sub_cancel] at h2
  exact hG0 h2

private lemma G₂_eval_unit (p e : ℕ) [Fact p.Prime] (G₂ : Polynomial ℤ)
    (hG : G₂.natDegree ≤ 2) (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0) (y : ℕ) :
    IsUnit (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))) :=
  isUnit_of_not_dvd p e _ (G₂_eval_not_dvd p G₂ hG hG1 hG2 hG0 y)

private lemma phase_factor (p e a k : ℕ) [Fact p.Prime] (he : 2 ≤ e)
    (hak : a + k = e - 1) (hk : 1 ≤ k)
    (A : ZMod (p ^ e))
    (N₂ G₂ : Polynomial ℤ) (hN : N₂.natDegree ≤ 2) (hG : G₂.natDegree ≤ 2)
    (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0)
    (χ : DirichletCharacter ℂ (p ^ e))
    (y t : ℕ) (c : ℤ)
    (hc : (p : ℤ) ∣ (N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ)
          - c * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
              * G₂.eval (y : ℤ))) :
    χ (A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval ((y + p ^ k * t : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
        * (((G₂.eval ((y + p ^ k * t : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)
      = χ (A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
          * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)
        * χ (1 + (((p ^ (e - 1) : ℕ)) : ZMod (p ^ e))
            * ((t : ZMod (p ^ e)) * ((c : ℤ) : ZMod (p ^ e)))) := by
  set z : ℕ := y + p ^ k * t with hz
  set K : ZMod (p ^ e) := ((p ^ (e - 1) : ℕ) : ZMod (p ^ e))
      * ((t : ZMod (p ^ e)) * ((c : ℤ) : ZMod (p ^ e))) with hK
  have hKeq : K = (((p : ℤ) ^ (e - 1) * ((t : ℤ) * c) : ℤ) : ZMod (p ^ e)) := by
    rw [hK]; push_cast; ring
  have hGy_unit : IsUnit (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))) :=
    G₂_eval_unit p e G₂ hG hG1 hG2 hG0 y
  have hGz_unit : IsUnit (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))) :=
    G₂_eval_unit p e G₂ hG hG1 hG2 hG0 z
  have hGy_mul : (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))
      * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hGy_unit
  have hGz_mul : (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))
      * (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hGz_unit
  -- integer expansions
  have hzy : (z : ℤ) = (y : ℤ) + (p : ℤ) ^ k * (t : ℤ) := by
    rw [hz]; push_cast; ring
  have hdvd_zy : (p : ℤ) ∣ (z : ℤ) - (y : ℤ) := by
    have h1 : (p : ℤ) ∣ (p : ℤ) ^ k := by simpa using pow_dvd_pow (p : ℤ) hk
    have h2 : (z : ℤ) - (y : ℤ) = (p : ℤ) ^ k * (t : ℤ) := by rw [hzy]; ring
    rw [h2]; exact dvd_mul_of_dvd_left h1 _
  have hGyGz : (p : ℤ) ∣ G₂.eval (y : ℤ) - G₂.eval (z : ℤ) := by
    have h2 : (y : ℤ) - (z : ℤ) ∣ G₂.eval (y : ℤ) - G₂.eval (z : ℤ) :=
      Polynomial.sub_dvd_eval_sub _ _ G₂
    have h3 : (p : ℤ) ∣ (y : ℤ) - (z : ℤ) := by
      have h4 : (y : ℤ) - (z : ℤ) = -((z : ℤ) - (y : ℤ)) := by ring
      rw [h4]; exact dvd_neg.mpr hdvd_zy
    exact dvd_trans h3 h2
  have hWc : (p : ℤ) ∣ (N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ)
      - c * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
          * G₂.eval (z : ℤ)) := by
    have h2 : (p : ℤ) ∣ c * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
        * (G₂.eval (y : ℤ) - G₂.eval (z : ℤ))) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hGyGz
        ((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))) c
    have h3 : (p : ℤ) ∣ ((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ)
        - c * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
            * G₂.eval (y : ℤ)))
        + c * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
            * (G₂.eval (y : ℤ) - G₂.eval (z : ℤ))) := dvd_add hc h2
    convert h3 using 1
    ring
  have hΔ : N₂.eval (z : ℤ) * G₂.eval (y : ℤ) - N₂.eval (y : ℤ) * G₂.eval (z : ℤ)
      = (p : ℤ) ^ k * (t : ℤ)
          * (G₂.eval (y : ℤ) * (N₂.derivative).eval (y : ℤ)
              - N₂.eval (y : ℤ) * (G₂.derivative).eval (y : ℤ))
        + (p : ℤ) ^ (k + k) * (t : ℤ) ^ 2
          * (G₂.eval (y : ℤ) * N₂.coeff 2 - N₂.eval (y : ℤ) * G₂.coeff 2) := by
    rw [hzy, eval_add_expand N₂ hN (y : ℤ) ((p : ℤ) ^ k * (t : ℤ)),
      eval_add_expand G₂ hG (y : ℤ) ((p : ℤ) ^ k * (t : ℤ))]
    ring
  have hWy : G₂.eval (y : ℤ) * (N₂.derivative).eval (y : ℤ)
      - N₂.eval (y : ℤ) * (G₂.derivative).eval (y : ℤ)
      = (N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    ring
  have hle : e ≤ a + 2 * k := by
    have h1 : a + 2 * k = (e - 1) + k := by rw [← hak]; ring
    rw [h1]; omega
  -- the integer divisibility
  have hInt : (p : ℤ) ^ e ∣ (p : ℤ) ^ a
        * (N₂.eval (z : ℤ) * G₂.eval (y : ℤ) - N₂.eval (y : ℤ) * G₂.eval (z : ℤ))
      - (p : ℤ) ^ (e - 1) * (t : ℤ) * c
        * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ)) * G₂.eval (z : ℤ)) := by
    have hkey : (p : ℤ) ^ a
        * (N₂.eval (z : ℤ) * G₂.eval (y : ℤ) - N₂.eval (y : ℤ) * G₂.eval (z : ℤ))
        - (p : ℤ) ^ (e - 1) * (t : ℤ) * c
          * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ)) * G₂.eval (z : ℤ))
        = (p : ℤ) ^ (e - 1) * ((t : ℤ) * ((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ)
              - c * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ)) * G₂.eval (z : ℤ))))
          + (p : ℤ) ^ (a + 2 * k) * ((t : ℤ) ^ 2
              * (G₂.eval (y : ℤ) * N₂.coeff 2 - N₂.eval (y : ℤ) * G₂.coeff 2)) := by
      rw [hΔ, hWy]
      rw [show (p : ℤ) ^ (e - 1) = (p : ℤ) ^ a * (p : ℤ) ^ k by rw [← hak, pow_add]]
      rw [show (p : ℤ) ^ (a + 2 * k) = (p : ℤ) ^ a * ((p : ℤ) ^ k * (p : ℤ) ^ k) by
        rw [show a + 2 * k = a + (k + k) by ring, pow_add, pow_add]]
      ring
    rw [hkey]
    refine dvd_add ?_ ?_
    · exact pow_pred_mul_dvd (show 1 ≤ e by omega) (dvd_mul_of_dvd_right hWc _)
    · exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) hle) _
  -- conclude the ZMod cross identity
  have hcross : (A * ((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))
        + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))
      * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
      = (A * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
          + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))
        * (1 + K) * ((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)) := by
    have hzero : (((p : ℤ) ^ a
        * (N₂.eval (z : ℤ) * G₂.eval (y : ℤ) - N₂.eval (y : ℤ) * G₂.eval (z : ℤ))
      - (p : ℤ) ^ (e - 1) * (t : ℤ) * c
        * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
            * G₂.eval (z : ℤ)) : ℤ) : ZMod (p ^ e)) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ e)).mpr (by simpa using hInt)
    rw [← sub_eq_zero]
    have hcast : (A * ((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))
          + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))
        * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
        - (A * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))
          * (1 + K) * ((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))
        = (((p : ℤ) ^ a
            * (N₂.eval (z : ℤ) * G₂.eval (y : ℤ) - N₂.eval (y : ℤ) * G₂.eval (z : ℤ))
          - (p : ℤ) ^ (e - 1) * (t : ℤ) * c
            * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
                * G₂.eval (z : ℤ)) : ℤ) : ZMod (p ^ e)) := by
      rw [hKeq]
      conv_lhs => rw [← ZMod.natCast_zmod_val A]
      push_cast
      ring
    rw [hcast, hzero]
  -- assemble
  have hgoal : A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))
        * (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹
      = (A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
          * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹) * (1 + K) := by
    have hx : (A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))
          * (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)
        * ((((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))) * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))))
        = (A * ((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))
          * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)) := by
      rw [← mul_assoc, add_mul_inv_mul A ((p : ZMod (p ^ e)) ^ a * ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))
        ((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)) hGz_mul]
    have hy : ((A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
          * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹) * (1 + K))
        * ((((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))) * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))))
        = (A * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))
          * (1 + K) * ((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)) := by
      have h1 : (A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
            * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)
          * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
          = A * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
            + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)) :=
        add_mul_inv_mul A ((p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))
          ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)) hGy_mul
      rw [show ((A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
              * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹) * (1 + K))
            * ((((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))) * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))))
          = ((A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
              * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)
              * ((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))) * (1 + K)
              * ((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)) by ring, h1]
    exact (IsUnit.mul_left_inj (hGz_unit.mul hGy_unit)).mp (by rw [hx, hy, hcross])
  rw [hgoal, map_mul]

private noncomputable def phaseC (p : ℕ) (N₂ G₂ : Polynomial ℤ) (y : ℕ) : ℤ :=
  (((((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p)
      * (((G₂.coeff 0 : ℤ) : ZMod p))⁻¹ ^ 2).val : ℤ)

private lemma inner_sum_eval (p e a k m : ℕ) [Fact p.Prime] (he : 2 ≤ e)
    (ha : 1 ≤ a) (hk : 1 ≤ k) (hm : 1 ≤ m) (hak : a + k = e - 1)
    (A : ZMod (p ^ e)) (hA : (p : ZMod (p ^ e)) ∣ A - 1)
    (N₂ G₂ : Polynomial ℤ) (hN : N₂.natDegree ≤ 2) (hG : G₂.natDegree ≤ 2)
    (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0)
    (χ : DirichletCharacter ℂ (p ^ e))
    (htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1) (y : ℕ) :
    ∑ t ∈ Finset.range (p ^ m),
        χ (A + (p : ZMod (p ^ e)) ^ a
          * ((N₂.eval ((y + p ^ k * t : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
          * (((G₂.eval ((y + p ^ k * t : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)
      = χ (A + (p : ZMod (p ^ e)) ^ a * ((N₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e))
            * (((G₂.eval (y : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)
        * (if (ZMod.castHom (by simpa using pow_dvd_pow p (show 1 ≤ e by omega)) (ZMod p)
              ((phaseC p N₂ G₂ y : ℤ) : ZMod (p ^ e)) = 0)
            then ((p ^ m : ℕ) : ℂ) else 0) := by
  have hc : (p : ℤ) ∣ (N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ)
      - phaseC p N₂ G₂ y * (((A.val : ℤ) * G₂.eval (y : ℤ) + (p : ℤ) ^ a * N₂.eval (y : ℤ))
          * G₂.eval (y : ℤ)) :=
    phase_cond p e a (by omega) A hA N₂ G₂ hG hG1 hG2 hG0 ha y
  rw [Finset.sum_congr rfl (fun t _ =>
    phase_factor p e a k he hak hk A N₂ G₂ hN hG hG1 hG2 hG0 χ y t (phaseC p N₂ G₂ y) hc)]
  rw [← Finset.mul_sum]
  congr 1
  exact primePowKernel_geom_sum_zmod p e he χ htop ((phaseC p N₂ G₂ y : ℤ) : ZMod (p ^ e)) m hm

private lemma range_split {α : Type*} [AddCommMonoid α] (p k m n : ℕ) (f : ℕ → α)
    (hn : k + m = n) (hk : 1 ≤ k) :
    ∑ z ∈ Finset.range (p ^ n), f z
      = ∑ a ∈ Finset.range p, ∑ y ∈ Finset.range (p ^ (k - 1)),
          ∑ t ∈ Finset.range (p ^ m), f (a + p * (y + p ^ (k - 1) * t)) := by
  have hn1 : 1 ≤ n := by omega
  have h1 : p ^ n = p * p ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
  have h2 : p ^ (n - 1) = p ^ (k - 1) * p ^ m := by
    rw [← pow_add]; congr 1; omega
  rw [h1, Commons.Algebra.BigOperators.sum_range_mul_eq f p (p ^ (n - 1))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [h2]
  exact Commons.Algebra.BigOperators.sum_range_mul_eq (fun s => f (a + p * s)) (p ^ (k - 1)) (p ^ m)

private lemma cond_zero_iff (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (N₂ G₂ : Polynomial ℤ) (hN : N₂.natDegree ≤ 2) (hN2 : ¬ (p : ℤ) ∣ N₂.coeff 2)
    (hG : G₂.natDegree ≤ 2) (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0)
    (a₀ : ℕ) (ha₀ : ∀ y : ℕ, (p : ℤ) ∣ N₂.derivative.eval (y : ℤ) ↔ (y : ZMod p) = (a₀ : ZMod p))
    (y : ℕ) :
    (ZMod.castHom (by simpa using pow_dvd_pow p (show 1 ≤ e by omega)) (ZMod p)
        ((phaseC p N₂ G₂ y : ℤ) : ZMod (p ^ e)) = 0)
      ↔ (y : ZMod p) = (a₀ : ZMod p) := by
  have h1 : (ZMod.castHom (by simpa using pow_dvd_pow p (show 1 ≤ e by omega)) (ZMod p)
        ((phaseC p N₂ G₂ y : ℤ) : ZMod (p ^ e)) = 0)
      ↔ (p : ℤ) ∣ phaseC p N₂ G₂ y := by
    rw [map_intCast]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd (phaseC p N₂ G₂ y) p
  rw [h1]
  have h2 : (p : ℤ) ∣ phaseC p N₂ G₂ y ↔
      ((((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p)
        * (((G₂.coeff 0 : ℤ) : ZMod p))⁻¹ ^ 2).val = 0 := by
    constructor
    · intro h
      have h' : p ∣ ((((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p)
          * (((G₂.coeff 0 : ℤ) : ZMod p))⁻¹ ^ 2).val := by
        rw [show phaseC p N₂ G₂ y
            = ((((((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p)
                * (((G₂.coeff 0 : ℤ) : ZMod p))⁻¹ ^ 2).val : ℕ) : ℤ) from rfl] at h
        exact_mod_cast h
      exact Nat.eq_zero_of_dvd_of_lt h' (ZMod.val_lt _)
    · intro h
      rw [show phaseC p N₂ G₂ y
          = ((((((N₂.derivative * G₂ - N₂ * G₂.derivative).eval (y : ℤ) : ℤ) : ZMod p)
              * (((G₂.coeff 0 : ℤ) : ZMod p))⁻¹ ^ 2).val : ℕ) : ℤ) from rfl, h]
      simp
  rw [h2]
  exact (rational_phase_cond_deg2 p N₂ G₂ hG hG1 hG2 hG0 y).trans (ha₀ y)

private lemma exp_key {e a k n : ℕ} (hak : a + k = e - 1) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((2 * n + a - e : ℕ) : ℝ) / 2 + 1 / 2 = (n : ℝ) - (k : ℝ) / 2 := by
  have h1 : (2 * n + a - e : ℕ) = 2 * n - k - 1 := by omega
  rw [h1, Nat.cast_sub (show 1 ≤ 2 * n - k by omega), Nat.cast_sub (show k ≤ 2 * n by omega)]
  push_cast
  ring

private lemma exp_key2 {e a k n m : ℕ} (hak : a + k = e - 1) (hm : m = n - k)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((2 * (k - 1) + (a + 2) - e : ℕ) : ℝ) / 2 + 1 / 2 + (m : ℝ)
      = ((2 * n + a - e : ℕ) : ℝ) / 2 + 1 / 2 := by
  have h1 : (2 * (k - 1) + (a + 2) - e : ℕ) = k - 1 := by omega
  have h2 : (2 * n + a - e : ℕ) = 2 * n - k - 1 := by omega
  rw [h1, h2, hm, Nat.cast_sub hkn, Nat.cast_sub (show 1 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ 2 * n - k by omega), Nat.cast_sub (show k ≤ 2 * n by omega)]
  push_cast
  ring

private lemma main_aux (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e))
    (htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1) :
    ∀ n a (A : ZMod (p ^ e)) (N₂ G₂ : Polynomial ℤ),
      1 ≤ a → a ≤ e - 2 → e ≤ a + n →
      (p : ZMod (p ^ e)) ∣ A - 1 →
      N₂.natDegree ≤ 2 → ¬ (p : ℤ) ∣ N₂.coeff 2 →
      G₂.natDegree ≤ 2 → (p : ℤ) ∣ G₂.coeff 1 → (p : ℤ) ∣ G₂.coeff 2 →
      ¬ (p : ℤ) ∣ G₂.coeff 0 →
      ‖∑ z ∈ Finset.range (p ^ n), χ (A + (p : ZMod (p ^ e)) ^ a *
        ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)) * (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)‖
        ≤ (p : ℝ) ^ (((2 * n + a - e : ℕ) : ℝ) / 2 + 1 / 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a A N₂ G₂ ha hak han hA hN hN2 hG hG1 hG2 hG0
    set k : ℕ := e - 1 - a with hkdef
    have hk1 : 1 ≤ k := by omega
    have hak' : a + k = e - 1 := by omega
    have hkn : k ≤ n := by omega
    set m : ℕ := n - k with hmdef
    have hm1 : 1 ≤ m := by omega
    obtain ⟨a₀, ha₀lt, ha₀⟩ := quadratic_deriv_dvd_iff p hp2 N₂ hN hN2
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
    have hpgt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    rw [range_split p k m n (fun z => χ (A + (p : ZMod (p ^ e)) ^ a
        * ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e))
        * (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)) (by omega) hk1]
    have hinner : ∀ a' : ℕ, a' < p → ∀ y : ℕ,
        (∑ t ∈ Finset.range (p ^ m), χ (A + (p : ZMod (p ^ e)) ^ a
          * ((N₂.eval ((a' + p * (y + p ^ (k - 1) * t) : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
          * (((G₂.eval ((a' + p * (y + p ^ (k - 1) * t) : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹))
        = χ (A + (p : ZMod (p ^ e)) ^ a
              * ((N₂.eval ((a' + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
              * (((G₂.eval ((a' + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)
            * (if a' = a₀ then ((p ^ m : ℕ) : ℂ) else 0) := by
      intro a' ha'lt y
      have hy0 : ∀ t : ℕ, a' + p * (y + p ^ (k - 1) * t) = (a' + p * y) + p ^ k * t := by
        intro t
        have hp : p * p ^ (k - 1) = p ^ k := by
          conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
          ring
        calc a' + p * (y + p ^ (k - 1) * t) = a' + p * y + (p * p ^ (k - 1)) * t := by ring
          _ = (a' + p * y) + p ^ k * t := by rw [hp]
      rw [Finset.sum_congr rfl (fun t _ => by rw [hy0 t])]
      rw [inner_sum_eval p e a k m he ha hk1 hm1 hak' A hA N₂ G₂ hN hG hG1 hG2 hG0 χ htop
        (a' + p * y)]
      have hmod : (((a' + p * y : ℕ)) : ZMod p) = ((a' : ℕ) : ZMod p) := by
        push_cast
        rw [show (((p : ℕ)) : ZMod p) = 0 by simp]
        ring
      have hab : (((a' : ℕ)) : ZMod p) = ((a₀ : ℕ) : ZMod p) ↔ a' = a₀ := by
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha'lt, Nat.mod_eq_of_lt ha₀lt]
      have hiff : (ZMod.castHom (by simpa using pow_dvd_pow p (show 1 ≤ e by omega)) (ZMod p)
            ((phaseC p N₂ G₂ (a' + p * y) : ℤ) : ZMod (p ^ e)) = 0) ↔ a' = a₀ :=
        (cond_zero_iff p e hp2 (by omega) N₂ G₂ hN hN2 hG hG1 hG2 hG0 a₀ ha₀ (a' + p * y)).trans
          (by rw [hmod]; exact hab)
      congr 1
      exact if_congr hiff rfl rfl
    have hmain : (∑ a' ∈ Finset.range p, ∑ y ∈ Finset.range (p ^ (k - 1)),
          ∑ t ∈ Finset.range (p ^ m), χ (A + (p : ZMod (p ^ e)) ^ a
            * ((N₂.eval ((a' + p * (y + p ^ (k - 1) * t) : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
            * (((G₂.eval ((a' + p * (y + p ^ (k - 1) * t) : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹))
        = (∑ y ∈ Finset.range (p ^ (k - 1)), χ (A + (p : ZMod (p ^ e)) ^ a
              * ((N₂.eval ((a₀ + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
              * (((G₂.eval ((a₀ + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹))
            * ((p ^ m : ℕ) : ℂ) := by
      rw [Finset.sum_congr rfl (fun a' ha' => Finset.sum_congr rfl
        (fun y _ => hinner a' (Finset.mem_range.mp ha') y))]
      rw [Finset.sum_eq_single a₀]
      · rw [if_pos rfl, Finset.sum_mul]
      · intro b _ hb
        rw [Finset.sum_congr rfl (fun y _ => by rw [if_neg hb, mul_zero]),
          Finset.sum_const_zero]
      · intro h; exact absurd (Finset.mem_range.mpr ha₀lt) h
    rw [hmain, norm_mul, Complex.norm_natCast]
    by_cases hk2 : k ≤ 2
    · -- k ≤ 2 : trivial bound
      have htriv : ‖∑ y ∈ Finset.range (p ^ (k - 1)), χ (A + (p : ZMod (p ^ e)) ^ a
            * ((N₂.eval ((a₀ + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
            * (((G₂.eval ((a₀ + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)‖ ≤ (p : ℝ) ^ (k - 1) := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum (fun y _ => DirichletCharacter.norm_le_one χ _)).trans ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
      calc ‖∑ y ∈ Finset.range (p ^ (k - 1)), χ (A + (p : ZMod (p ^ e)) ^ a
              * ((N₂.eval ((a₀ + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
              * (((G₂.eval ((a₀ + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)‖ * ((p ^ m : ℕ) : ℝ)
          ≤ (p : ℝ) ^ (k - 1) * ((p ^ m : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right htriv (by positivity)
        _ = (p : ℝ) ^ ((k - 1) + m) := by rw [Nat.cast_pow, ← pow_add]
        _ = (p : ℝ) ^ (n - 1) := by congr 1; omega
        _ ≤ (p : ℝ) ^ (((2 * n + a - e : ℕ) : ℝ) / 2 + 1 / 2) := by
            rw [← Real.rpow_natCast]
            rw [exp_key hak' hk1 hkn]
            refine (Real.rpow_le_rpow_left_iff hpgt).mpr ?_
            rw [Nat.cast_sub (show 1 ≤ n by omega)]
            push_cast
            have hk2' : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
            linarith
    · -- k ≥ 3 : recursion
      have hk3' : 3 ≤ k := by omega
      obtain ⟨A', N', G', hN'deg, hN'2, hG'deg, hG'1, hG'2, hG'0, hA', hlift⟩ :=
        rational_phase_lift p e a he ha A hA N₂ G₂ hN hN2 hG hG1 hG2 hG0 a₀ ((ha₀ a₀).mpr rfl)
      have hT : (∑ y ∈ Finset.range (p ^ (k - 1)), χ (A + (p : ZMod (p ^ e)) ^ a
            * ((N₂.eval ((a₀ + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e))
            * (((G₂.eval ((a₀ + p * y : ℕ) : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹))
          = ∑ u ∈ Finset.range (p ^ (k - 1)), χ (A' + (p : ZMod (p ^ e)) ^ (a + 2)
              * ((N'.eval (u : ℤ) : ℤ) : ZMod (p ^ e))
              * (((G'.eval (u : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹) :=
        Finset.sum_congr rfl (fun u _ => by rw [hlift u])
      rw [hT]
      have hIH := ih (k - 1) (by omega) (a + 2) A' N' G' (by omega) (by omega) (by omega)
        hA' hN'deg hN'2 hG'deg hG'1 hG'2 hG'0
      calc ‖∑ u ∈ Finset.range (p ^ (k - 1)), χ (A' + (p : ZMod (p ^ e)) ^ (a + 2)
              * ((N'.eval (u : ℤ) : ℤ) : ZMod (p ^ e))
              * (((G'.eval (u : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)‖ * ((p ^ m : ℕ) : ℝ)
          ≤ (p : ℝ) ^ (((2 * (k - 1) + (a + 2) - e : ℕ) : ℝ) / 2 + 1 / 2) * ((p ^ m : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hIH (by positivity)
        _ = (p : ℝ) ^ (((2 * (k - 1) + (a + 2) - e : ℕ) : ℝ) / 2 + 1 / 2 + (m : ℝ)) := by
            rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_add hppos]
        _ = (p : ℝ) ^ (((2 * n + a - e : ℕ) : ℝ) / 2 + 1 / 2) := by
            congr 1
            exact exp_key2 hak' hmdef hk1 hkn

/-- **Stationary-phase bound for a `p`-adically shallow rational phase.**

`p` odd prime, `e ≥ 2`, `χ` a Dirichlet character modulo `p^e` which is non-trivial on the top kernel
`1 + p^(e-1)`.  Let `a ≥ 1`, `n ≥ 0` with `a ≤ e-2` and `e ≤ a+n`, let `A : ZMod (p^e)` satisfy
`A ≡ 1 (mod p)`, let `N₂ ∈ ℤ[X]` have degree `≤ 2` with `p ∤ N₂.coeff 2`, and let `G₂ ∈ ℤ[X]` have
degree `≤ 2` with `p ∣ G₂.coeff 1`, `p ∣ G₂.coeff 2` and `p ∤ G₂.coeff 0` (so that `G₂ (z)` is a unit
for every `z`).  Then

`‖∑_{z < p^n} χ (A + p^a * N₂(z) * G₂(z)⁻¹)‖ ≤ p^((2n+a-e)/2 + 1/2)`.

Proof plan (the standard stationary phase):  put `k = e-1-a` (so `1 ≤ k ≤ n`), split the range as
`z = a' + p * (y + p^(k-1) * t)`, expand and use
`χ (V (y + p^k t)) = χ (V y) · χ (1 + p^(e-1) (t * c_y))`; orthogonality on the top kernel then
turns the `t`-sum into `p^n · [p ∣ c_y]`.  The surviving condition `p ∣ c_y` reduces to `p ∣ N₂'(y)`,
whose unique root modulo `p` selects the class `a' = a₀`; the residual sum is again of the same shape
with `(a, n)` replaced by `(a+2, k-1)` (`rational_phase_lift`), giving the balanced recursion. -/
theorem rational_phase_sum_bound (p e a n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e))
    (htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1)
    (ha : 1 ≤ a) (hak : a ≤ e - 2) (han : e ≤ a + n)
    (A : ZMod (p ^ e)) (hA : (p : ZMod (p ^ e)) ∣ A - 1)
    (N₂ G₂ : Polynomial ℤ) (hN : N₂.natDegree ≤ 2) (hN2 : ¬ (p : ℤ) ∣ N₂.coeff 2)
    (hG : G₂.natDegree ≤ 2) (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0) :
    ‖∑ z ∈ Finset.range (p ^ n), χ (A + (p : ZMod (p ^ e)) ^ a *
        ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)) * (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹)‖
      ≤ (p : ℝ) ^ (((2 * n + a - e : ℕ) : ℝ) / 2 + 1 / 2) :=
  main_aux p e hp2 he χ htop n a A N₂ G₂ ha hak han hA hN hN2 hG hG1 hG2 hG0

end Commons.NumberTheory.DirichletCharacter
