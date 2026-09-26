import Mathlib
import Submission.Work.Drive.fourCombDefs
import Submission.Work.Drive.fourCombPoly

/-!
# The kernel of the four-jet evaluation map

Combining the polynomial model `fcGamma` (`fourCombDefs`, `fourCombPoly`) with the double-root
criterion shows that the kernel of the scalar evaluation map
`x ↦ ((trigBasis j (t i) · x), (trigBasisD j (t i) · x))` at four parameters distinct modulo the
period has dimension at most one.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open Polynomial

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

/-! ## The double-root criterion -/

/-- A polynomial vanishing, together with its derivative, at `a` is divisible by `(X - C a)^2`. -/
lemma fc_sq_dvd_of_eval_of_derivative_eval {Q : ℂ[X]} {a : ℂ}
    (h0 : Q.eval a = 0) (h1 : Q.derivative.eval a = 0) :
    (Polynomial.X - Polynomial.C a)^2 ∣ Q := by
  obtain ⟨R, hR⟩ := (Polynomial.dvd_iff_isRoot).2 h0
  have hR0 : R.eval a = 0 := by
    have h := h1
    rw [hR] at h
    rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul] at h
    simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] using h
  obtain ⟨S, hS⟩ := (Polynomial.dvd_iff_isRoot).2 hR0
  exact ⟨S, by rw [hR, hS]; ring⟩

/-- **The double-root lemma.**  A coefficient vector whose trigonometric value and velocity
vanish at `t` produces a polynomial divisible by `(X - jetExp t) ^ 2`. -/
lemma fc_sq_dvd_fcGamma {x : Fin 9 → ℂ} {t : ℝ}
    (h0 : ∑ j : Fin 9, x j * (trigBasis j t : ℂ) = 0)
    (h1 : ∑ j : Fin 9, x j * (trigBasisD j t : ℂ) = 0) :
    (Polynomial.X - Polynomial.C (jetExp t))^2 ∣ fcGamma x := by
  refine fc_sq_dvd_of_eval_of_derivative_eval ?_ ?_
  · rw [fcGamma_eval x t, h0, mul_zero]
  · rw [fcGamma_derivative_eval x t]
    have hterm : ∀ j : Fin 9, x j * ((jetExp t)^3 * (4 * (trigBasis j t : ℂ)
        - Complex.I * (trigBasisD j t : ℂ)))
        = (jetExp t)^3 * (4 * (x j * (trigBasis j t : ℂ))
            - Complex.I * (x j * (trigBasisD j t : ℂ))) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, Finset.sum_sub_distrib]
    have hS : (∑ j : Fin 9, 4 * (x j * (trigBasis j t : ℂ)))
        = 4 * ∑ j : Fin 9, x j * (trigBasis j t : ℂ) := by rw [Finset.mul_sum]
    have hD : (∑ j : Fin 9, Complex.I * (x j * (trigBasisD j t : ℂ)))
        = Complex.I * ∑ j : Fin 9, x j * (trigBasisD j t : ℂ) := by rw [Finset.mul_sum]
    rw [hS, hD, h0, h1]
    ring

/-! ## The vertex polynomial and its divisibility -/

/-- The product of the squared linear factors at the four points `z 0, …, z 3`. -/
def fcPhi (z : Fin 4 → ℂ) : ℂ[X] :=
  ((Polynomial.X - Polynomial.C (z 0))^2 * (Polynomial.X - Polynomial.C (z 1))^2)
    * ((Polynomial.X - Polynomial.C (z 2))^2 * (Polynomial.X - Polynomial.C (z 3))^2)

lemma fc_monic_sq_sub_C (a : ℂ) : ((Polynomial.X - Polynomial.C a)^2 : ℂ[X]).Monic :=
  (Polynomial.monic_X_sub_C a).pow 2

lemma fc_sq_ne_zero (a : ℂ) : ((Polynomial.X - Polynomial.C a)^2 : ℂ[X]) ≠ 0 :=
  (fc_monic_sq_sub_C a).ne_zero

lemma fcPhi_monic (z : Fin 4 → ℂ) : (fcPhi z).Monic := by
  rw [fcPhi]
  exact ((fc_monic_sq_sub_C (z 0)).mul (fc_monic_sq_sub_C (z 1))).mul
    ((fc_monic_sq_sub_C (z 2)).mul (fc_monic_sq_sub_C (z 3)))

lemma fc_natDegree_sq_sub_C (a : ℂ) : ((Polynomial.X - Polynomial.C a)^2 : ℂ[X]).natDegree = 2 := by
  rw [Polynomial.Monic.natDegree_pow (Polynomial.monic_X_sub_C a), Polynomial.natDegree_X_sub_C]

lemma fcPhi_natDegree (z : Fin 4 → ℂ) : (fcPhi z).natDegree = 8 := by
  have hd : ∀ a : ℂ, ((Polynomial.X - Polynomial.C a)^2 : ℂ[X]).natDegree = 2 :=
    fc_natDegree_sq_sub_C
  have h0 := (fc_monic_sq_sub_C (z 0)).natDegree_mul (fc_monic_sq_sub_C (z 1))
  have h1 := (fc_monic_sq_sub_C (z 2)).natDegree_mul (fc_monic_sq_sub_C (z 3))
  have h2 := ((fc_monic_sq_sub_C (z 0)).mul (fc_monic_sq_sub_C (z 1))).natDegree_mul
    ((fc_monic_sq_sub_C (z 2)).mul (fc_monic_sq_sub_C (z 3)))
  rw [fcPhi, h2, h0, h1, hd, hd, hd, hd]

lemma fcPhi_coeff_eight (z : Fin 4 → ℂ) : (fcPhi z).coeff 8 = 1 := by
  rw [← fcPhi_natDegree z]
  exact (fcPhi_monic z).coeff_natDegree

lemma fcPhi_ne_zero (z : Fin 4 → ℂ) : fcPhi z ≠ 0 := (fcPhi_monic z).ne_zero

/-- The squared linear factors at distinct points are coprime. -/
lemma fc_coprime_sq_sub_C {a b : ℂ} (h : a ≠ b) :
    IsCoprime ((Polynomial.X - Polynomial.C a)^2 : ℂ[X]) ((Polynomial.X - Polynomial.C b)^2) := by
  have hc : IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit
  have h1 : IsCoprime ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a))
      (Polynomial.X - Polynomial.C b) := hc.mul_left hc
  have h2 : IsCoprime ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a))
      ((Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C b)) := h1.mul_right h1
  simpa only [pow_two] using h2

/-- Four double roots force divisibility by `fcPhi`. -/
lemma fcPhi_dvd {z : Fin 4 → ℂ} (hz : Function.Injective z) {Q : ℂ[X]}
    (h0 : (Polynomial.X - Polynomial.C (z 0))^2 ∣ Q)
    (h1 : (Polynomial.X - Polynomial.C (z 1))^2 ∣ Q)
    (h2 : (Polynomial.X - Polynomial.C (z 2))^2 ∣ Q)
    (h3 : (Polynomial.X - Polynomial.C (z 3))^2 ∣ Q) :
    fcPhi z ∣ Q := by
  have hne : ∀ i j : Fin 4, i ≠ j → z i ≠ z j := fun i j hij h => hij (hz h)
  have hA : (Polynomial.X - Polynomial.C (z 0))^2 * (Polynomial.X - Polynomial.C (z 1))^2 ∣ Q :=
    (fc_coprime_sq_sub_C (hne 0 1 (by decide))).mul_dvd h0 h1
  have hB : (Polynomial.X - Polynomial.C (z 2))^2 * (Polynomial.X - Polynomial.C (z 3))^2 ∣ Q :=
    (fc_coprime_sq_sub_C (hne 2 3 (by decide))).mul_dvd h2 h3
  have hC : IsCoprime
      ((Polynomial.X - Polynomial.C (z 0))^2 * (Polynomial.X - Polynomial.C (z 1))^2)
      ((Polynomial.X - Polynomial.C (z 2))^2 * (Polynomial.X - Polynomial.C (z 3))^2) :=
    (((fc_coprime_sq_sub_C (hne 0 2 (by decide))).mul_right
      (fc_coprime_sq_sub_C (hne 0 3 (by decide)))).mul_left
      ((fc_coprime_sq_sub_C (hne 1 2 (by decide))).mul_right
        (fc_coprime_sq_sub_C (hne 1 3 (by decide)))))
  rw [fcPhi]
  exact hC.mul_dvd hA hB

/-! ## Degree bounds and the final argument -/

lemma fc_coeff_fcPoly_eq_zero (j : Fin 9) {N : ℕ} (hN : 8 < N) : (fcPoly j).coeff N = 0 := by
  fin_cases j
  · show (fcPoly 0).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring
  · show (fcPoly 1).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring
  · show (fcPoly 2).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring
  · show (fcPoly 3).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring
  · show (fcPoly 4).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring
  · show (fcPoly 5).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring
  · show (fcPoly 6).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring
  · show (fcPoly 7).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring
  · show (fcPoly 8).coeff N = 0
    simp only [fcPoly, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> first | (exfalso; omega) | ring

lemma fc_natDegree_fcGamma_le (y : Fin 9 → ℂ) : (fcGamma y).natDegree ≤ 8 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [fcGamma_coeff]
  exact Finset.sum_eq_zero fun j _ => by rw [fc_coeff_fcPoly_eq_zero j hN, mul_zero]

/-- A polynomial of degree at most `8` divisible by `fcPhi z` is a scalar multiple of `fcPhi z`. -/
lemma fc_eq_smul_fcPhi_of_dvd {z : Fin 4 → ℂ} {Q : ℂ[X]} (hdvd : fcPhi z ∣ Q)
    (hdeg : Q.natDegree ≤ 8) : ∃ c : ℂ, c • fcPhi z = Q := by
  set c := Q.coeff 8 with hc
  have hdvd' : fcPhi z ∣ Q - c • fcPhi z := by
    refine dvd_sub hdvd ?_
    rw [Polynomial.smul_eq_C_mul]
    exact dvd_mul_left _ _
  have hnat : (Q - c • fcPhi z).natDegree ≤ 7 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [Polynomial.coeff_sub, Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul]
    rcases eq_or_lt_of_le (by omega : 8 ≤ N) with h | h
    · subst h
      rw [hc, fcPhi_coeff_eight z, mul_one, sub_self]
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero.mp hdeg N h,
        Polynomial.natDegree_le_iff_coeff_eq_zero.mp (le_of_eq (fcPhi_natDegree z)) N h,
        mul_zero, sub_zero]
  have hzero : Q - c • fcPhi z = 0 := by
    by_contra hne
    have h8 := Polynomial.natDegree_le_of_dvd hdvd' hne
    rw [fcPhi_natDegree z] at h8
    omega
  exact ⟨c, (sub_eq_zero.mp hzero).symm⟩

/-! ## The scalar jet map and its kernel -/

/-- The scalar (value, derivative) evaluation map at the parameters `t i`. -/
def fcJetMap (t : Fin 4 → ℝ) : (Fin 9 → ℝ) →ₗ[ℝ] ((Fin 4 → ℝ) × (Fin 4 → ℝ)) where
  toFun x := (fun i => ∑ j : Fin 9, trigBasis j (t i) * x j,
              fun i => ∑ j : Fin 9, trigBasisD j (t i) * x j)
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        RingHom.id_apply]
    · exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by ring

@[simp] lemma fcJetMap_fst (t : Fin 4 → ℝ) (x : Fin 9 → ℝ) (i : Fin 4) :
    (fcJetMap t x).1 i = ∑ j : Fin 9, trigBasis j (t i) * x j := rfl

@[simp] lemma fcJetMap_snd (t : Fin 4 → ℝ) (x : Fin 9 → ℝ) (i : Fin 4) :
    (fcJetMap t x).2 i = ∑ j : Fin 9, trigBasisD j (t i) * x j := rfl

/-- Complexification of the coefficient space. -/
def fcCplx : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℂ) where
  toFun x := fun j => (x j : ℂ)
  map_add' x y := by funext j; simp
  map_smul' c x := by funext j; simp

@[simp] lemma fcCplx_apply (x : Fin 9 → ℝ) (j : Fin 9) : fcCplx x j = (x j : ℂ) := rfl

lemma fcCplx_injective : Function.Injective fcCplx := by
  intro x y h
  funext j
  exact Complex.ofReal_inj.mp (congrFun h j)

lemma fc_ofReal_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.ofReal_add, ih]

lemma fc_ofReal_sum_mul (x : Fin 9 → ℝ) (B : Fin 9 → ℝ) :
    ((∑ j : Fin 9, B j * x j : ℝ) : ℂ)
      = ∑ j : Fin 9, fcCplx x j * (B j : ℂ) := by
  rw [fc_ofReal_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [fcCplx_apply]
  push_cast
  ring

/-- Distinct parameters modulo the period give distinct exponential points. -/
lemma fc_jetExp_injective_of_sep {t : Fin 4 → ℝ}
    (hsep : ∀ i j : Fin 4, i ≠ j → ∀ m : ℤ, t i - t j ≠ (m : ℝ) * period) :
    Function.Injective fun i => jetExp (t i) := by
  intro i j hij
  by_contra hne
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hij
  have h3 : (t i : ℂ) = (t j : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h4 : (t i : ℂ) * Complex.I
        = ((t j : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [hn]; ring
    exact mul_right_cancel₀ Complex.I_ne_zero h4
  have h5 : t i = t j + (n : ℝ) * (2 * Real.pi) := by
    have h6 : ((t i : ℂ)) = ((t j + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      push_cast; exact h3
    exact Complex.ofReal_inj.mp h6
  have h7 : t i - t j = (n : ℝ) * period := by rw [period]; linarith
  exact hsep i j hne n h7

/-- Membership in the kernel forces the polynomial model to be a multiple of `fcPhi`. -/
lemma fc_mem_span_fcPhi_of_mem_ker {t : Fin 4 → ℝ}
    (hz : Function.Injective fun i => jetExp (t i)) {x : Fin 9 → ℝ}
    (hx : x ∈ LinearMap.ker (fcJetMap t)) :
    ∃ c : ℂ, c • fcPhi (fun i => jetExp (t i)) = fcGamma (fcCplx x) := by
  have hx0 : fcJetMap t x = 0 := hx
  have hdiv : ∀ i : Fin 4,
      (Polynomial.X - Polynomial.C (jetExp (t i)))^2 ∣ fcGamma (fcCplx x) := by
    intro i
    have h1 : (∑ j : Fin 9, trigBasis j (t i) * x j) = 0 := by
      have h := congrFun (congrArg Prod.fst hx0) i
      simpa using h
    have h2 : (∑ j : Fin 9, trigBasisD j (t i) * x j) = 0 := by
      have h := congrFun (congrArg Prod.snd hx0) i
      simpa using h
    refine fc_sq_dvd_fcGamma ?_ ?_
    · rw [← fc_ofReal_sum_mul x (fun j => trigBasis j (t i)), h1, Complex.ofReal_zero]
    · rw [← fc_ofReal_sum_mul x (fun j => trigBasisD j (t i)), h2, Complex.ofReal_zero]
  exact fc_eq_smul_fcPhi_of_dvd (fcPhi_dvd hz (hdiv 0) (hdiv 1) (hdiv 2) (hdiv 3))
    (fc_natDegree_fcGamma_le _)

/-- **The kernel of the four-jet evaluation map has dimension at most one.** -/
theorem fc_finrank_ker_le_one {t : Fin 4 → ℝ}
    (hsep : ∀ i j : Fin 4, i ≠ j → ∀ m : ℤ, t i - t j ≠ (m : ℝ) * period) :
    Module.finrank ℝ (LinearMap.ker (fcJetMap t)) ≤ 1 := by
  classical
  have hzinj := fc_jetExp_injective_of_sep hsep
  rw [finrank_le_one_iff]
  by_cases hbot : LinearMap.ker (fcJetMap t) = ⊥
  · refine ⟨0, fun w => ⟨0, ?_⟩⟩
    have hw : (w : Fin 9 → ℝ) = 0 := by
      simpa [hbot] using w.2
    rw [zero_smul]
    exact Subtype.ext hw.symm
  · have hex : ∃ y ∈ LinearMap.ker (fcJetMap t), y ≠ 0 := by
      by_contra h
      apply hbot
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hx0
      exact h ⟨x, hx, hx0⟩
    obtain ⟨y, hy, hy0⟩ := hex
    refine ⟨⟨y, hy⟩, fun w => ?_⟩
    obtain ⟨cw, hw⟩ := fc_mem_span_fcPhi_of_mem_ker hzinj w.2
    obtain ⟨cy, hyc⟩ := fc_mem_span_fcPhi_of_mem_ker hzinj hy
    have hcy : cy ≠ 0 := by
      intro hc0
      have h1 : fcGamma (fcCplx y) = 0 := by rw [← hyc, hc0, zero_smul]
      have h2 : fcCplx y = 0 := fcGamma_injective (by rw [h1, map_zero])
      exact hy0 (fcCplx_injective (by rw [h2, map_zero]))
    set mu : ℂ := cw / cy with hmu
    have hzero : fcGamma (fcCplx (w : Fin 9 → ℝ) - mu • fcCplx y) = 0 := by
      rw [map_sub, map_smul, ← hw, ← hyc, hmu, smul_smul, div_mul_cancel₀ _ hcy, sub_self]
    have hwx : fcCplx (w : Fin 9 → ℝ) = mu • fcCplx y := by
      refine sub_eq_zero.mp ?_
      refine fcGamma_injective ?_
      rw [hzero, map_zero]
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hy0 (funext fun j => by simpa using h j)
    have hyj : ((y j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hj
    have hcoord : (((w : Fin 9 → ℝ) j : ℝ) : ℂ) = mu * ((y j : ℝ) : ℂ) := by
      have h := congrFun hwx j
      simpa only [fcCplx_apply, Pi.smul_apply, smul_eq_mul] using h
    have hmu_eq : mu = (((w : Fin 9 → ℝ) j : ℝ) : ℂ) * (((y j : ℝ) : ℂ))⁻¹ := by
      rw [hcoord, mul_assoc, mul_inv_cancel₀ hyj, mul_one]
    have h' : (((w : Fin 9 → ℝ) j : ℝ) : ℂ) / ((y j : ℝ) : ℂ) = mu := by
      rw [hmu_eq, div_eq_mul_inv]
    refine ⟨(w : Fin 9 → ℝ) j / y j, Subtype.ext (funext fun j' => ?_)⟩
    have h := congrFun hwx j'
    simp only [fcCplx_apply, Pi.smul_apply, smul_eq_mul] at h
    show ((w : Fin 9 → ℝ) j / y j : ℝ) * y j' = (w : Fin 9 → ℝ) j'
    refine Complex.ofReal_inj.mp ?_
    push_cast
    rw [h']
    exact h.symm

end

end Work.Drive
