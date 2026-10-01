import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.NumberTheory.Stepanov.kopparty_sq_nonvanishing
import Submission.Commons.NumberTheory.Stepanov.ncard_points_superelliptic
import Submission.Commons.NumberTheory.Stepanov.char_sum_eq_ncard_sub_card
import Submission.Commons.NumberTheory.Stepanov.hasseDeriv_eval_X_pow_card

namespace Commons.NumberTheory.Stepanov

open Polynomial

set_option maxHeartbeats 1000000

noncomputable section

variable {F : Type*} [Field F]

/-! ## The coefficient-wise Hasse derivative `D ℓ` on `F[X][Y] -/

/-- Coefficient-wise Hasse derivative: apply `hasseDeriv ℓ` to every `Y`-coefficient of `P`. -/
def D (ℓ : ℕ) (P : Polynomial (Polynomial F)) : Polynomial (Polynomial F) :=
  P.sum (fun j a => Polynomial.monomial j (Polynomial.hasseDeriv ℓ a))

lemma D_coeff (ℓ : ℕ) (P : Polynomial (Polynomial F)) (j : ℕ) :
    (D ℓ P).coeff j = Polynomial.hasseDeriv ℓ (P.coeff j) := by
  rw [D, Polynomial.coeff_sum]
  simp only [Polynomial.coeff_monomial]
  rw [Polynomial.sum_def, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Polynomial.mem_support_iff] at h
    simp only [ne_eq, not_not] at h
    rw [h, map_zero]

lemma D_add (ℓ : ℕ) (P Q : Polynomial (Polynomial F)) : D ℓ (P + Q) = D ℓ P + D ℓ Q := by
  apply Polynomial.ext; intro j
  rw [D_coeff, Polynomial.coeff_add, map_add, Polynomial.coeff_add, D_coeff, D_coeff]

lemma D_smul (ℓ : ℕ) (c : F) (P : Polynomial (Polynomial F)) : D ℓ (c • P) = c • D ℓ P := by
  apply Polynomial.ext; intro j
  rw [D_coeff, Polynomial.coeff_smul, map_smul, Polynomial.coeff_smul, D_coeff]

lemma D_zero (ℓ : ℕ) : D ℓ (0 : Polynomial (Polynomial F)) = 0 := by
  rw [D]; simp [Polynomial.sum_zero_index]

/-- `D ℓ` as a linear map. -/
def Dlm (ℓ : ℕ) : Polynomial (Polynomial F) →ₗ[F] Polynomial (Polynomial F) where
  toFun := D ℓ
  map_add' := D_add ℓ
  map_smul' := D_smul ℓ

@[simp] lemma Dlm_apply (ℓ : ℕ) (P : Polynomial (Polynomial F)) : Dlm ℓ P = D ℓ P := rfl

/-! ## The coefficient-to-polynomial linear map `toPolyLm` -/

/-- The monomial `X ^ i * Y ^ j` as an `F`-linear map `F → F[X][Y]`. -/
def monomLM {F : Type*} [Field F] (i j : ℕ) : F →ₗ[F] Polynomial (Polynomial F) :=
  (Polynomial.monomial j).restrictScalars F ∘ₗ (Polynomial.monomial i : F →ₗ[F] Polynomial F)

lemma monomLM_apply {F : Type*} [Field F] (i j : ℕ) (a : F) :
    monomLM i j a = Polynomial.monomial j (Polynomial.monomial i a) := by
  simp [monomLM]

/-- The linear map sending a family of coefficients supported on `i ≤ A`, `j ≤ B` to the
bivariate polynomial `∑ c_{i,j} X^i Y^j`. -/
def toPolyLm {F : Type*} [Field F] (A B : ℕ) :
    (Fin (A+1) × Fin (B+1) → F) →ₗ[F] Polynomial (Polynomial F) :=
  ∑ p : Fin (A+1) × Fin (B+1),
    (monomLM (p.1:ℕ) (p.2:ℕ)).comp (LinearMap.proj (R:=F) (φ:=fun _ => F) p)

lemma toPolyLm_apply {F : Type*} [Field F] (A B : ℕ) (c : Fin (A+1) × Fin (B+1) → F) :
    toPolyLm A B c = ∑ p : Fin (A+1) × Fin (B+1),
      Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p)) := by
  simp only [toPolyLm, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    monomLM_apply]

lemma toPolyLm_coeff {F : Type*} [Field F] (A B : ℕ) (c : Fin (A+1) × Fin (B+1) → F)
    (i : Fin (A+1)) (j : Fin (B+1)) :
    ((toPolyLm A B c).coeff (j:ℕ)).coeff (i:ℕ) = c (i,j) := by
  rw [toPolyLm_apply]
  have h1 : (∑ p : Fin (A+1) × Fin (B+1),
      Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))).coeff (j:ℕ)
      = ∑ p : Fin (A+1) × Fin (B+1),
        (Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))).coeff (j:ℕ) := by
    simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff (Polynomial F) (j:ℕ))
      (fun p : Fin (A+1) × Fin (B+1) =>
        Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))) Finset.univ
  rw [h1]
  have h2 : (∑ p : Fin (A+1) × Fin (B+1),
        (Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))).coeff (j:ℕ)).coeff (i:ℕ)
      = ∑ p : Fin (A+1) × Fin (B+1),
        ((Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))).coeff (j:ℕ)).coeff
          (i:ℕ) := by
    simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff F (i:ℕ))
      (fun p : Fin (A+1) × Fin (B+1) =>
        (Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))).coeff (j:ℕ))
      Finset.univ
  rw [h2]
  rw [Finset.sum_eq_single (i,j)]
  · rw [Polynomial.coeff_monomial, if_pos rfl, Polynomial.coeff_monomial, if_pos rfl]
  · rintro ⟨i',j'⟩ _ hij
    rw [Polynomial.coeff_monomial]
    by_cases h : (j':ℕ) = (j:ℕ)
    · rw [if_pos h, Polynomial.coeff_monomial, if_neg]
      intro hic
      exact hij (by ext <;> simp_all)
    · rw [if_neg h, Polynomial.coeff_zero]
  · intro hmem; simp at hmem


/-! ## Degree bounds for `D` and for the `Y = X` specialization -/

lemma D_coeff_natDegree_le (ℓ : ℕ) (P : Polynomial (Polynomial F)) (A : ℕ)
    (hA : ∀ j, (P.coeff j).natDegree ≤ A) :
    ∀ j, ((D ℓ P).coeff j).natDegree ≤ A := by
  intro j
  rw [D_coeff]
  exact (Polynomial.natDegree_hasseDeriv_le (P.coeff j) ℓ).trans ((Nat.sub_le _ _).trans (hA j))

lemma D_natDegree_le (ℓ : ℕ) (P : Polynomial (Polynomial F)) :
    (D ℓ P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [D_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hm, map_zero]

/-- `(P.eval X).natDegree ≤ A + B` if the `Y`-coefficients of `P` have `X`-degree `≤ A` and
`deg_Y P ≤ B`. -/
lemma eval_X_natDegree_le (P : Polynomial (Polynomial F)) (A B : ℕ)
    (hcoeff : ∀ j, (P.coeff j).natDegree ≤ A) (hdeg : P.natDegree ≤ B) :
    (P.eval (X : Polynomial F)).natDegree ≤ A + B := by
  classical
  rw [Polynomial.eval_eq_sum_range]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro i hi
  rw [Function.comp_apply]
  calc (P.coeff i * (X : Polynomial F) ^ i).natDegree
      ≤ (P.coeff i).natDegree + ((X:Polynomial F)^i).natDegree := Polynomial.natDegree_mul_le
    _ = (P.coeff i).natDegree + i := by rw [Polynomial.natDegree_X_pow]
    _ ≤ A + B := by
        have : i ≤ P.natDegree := by rw [Finset.mem_range] at hi; omega
        have := hcoeff i
        omega

/-- A polynomial all of whose coefficients of index `< N` vanish is zero. -/
lemma eq_zero_of_coeff_eq_zero {p : Polynomial F} {N : ℕ} (hdeg : p.natDegree < N)
    (h : ∀ n < N, p.coeff n = 0) : p = 0 := by
  apply Polynomial.ext; intro n
  rw [Polynomial.coeff_zero]
  by_cases hn : n < N
  · exact h n hn
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (by omega))

/-! ## `g` separable of degree `≥ 1` is not a constant multiple of a square -/

lemma not_const_mul_sq_of_separable (g : Polynomial F) (hsep : g.Separable) (hdeg : 1 ≤ g.natDegree) :
    ∀ (a : F) (h : Polynomial F), g ≠ Polynomial.C a * h ^ 2 := by
  intro a h hg
  have hdg : h ∣ g := ⟨Polynomial.C a * h, by rw [hg]; ring⟩
  have hdg' : h ∣ Polynomial.derivative g := by
    rw [hg, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_pow]
    simp only [Nat.reduceSub, pow_one]
    refine ⟨Polynomial.C a * (Polynomial.C (2:F) * Polynomial.derivative h), by ring_nf⟩
  have hd1 : h ∣ (1 : Polynomial F) := by
    obtain ⟨u, v, huv⟩ := hsep
    obtain ⟨k, hk⟩ := hdg
    obtain ⟨k', hk'⟩ := hdg'
    exact ⟨u*k + v*k', by rw [← huv, hk', hk]; ring⟩
  have hnd : h.natDegree = 0 := by
    obtain ⟨k, hk⟩ := hd1
    have hh : h ≠ 0 := by rintro rfl; rw [zero_mul] at hk; exact one_ne_zero hk
    have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact one_ne_zero hk
    have := Polynomial.natDegree_mul hh hk0
    rw [← hk, Polynomial.natDegree_one] at this
    omega
  have : (Polynomial.C a * h ^ 2).natDegree ≤ 0 := by
    calc (Polynomial.C a * h ^ 2).natDegree ≤ (h^2).natDegree := Polynomial.natDegree_C_mul_le a (h^2)
      _ = 2 * h.natDegree := Polynomial.natDegree_pow h 2
      _ = 0 := by rw [hnd, mul_zero]
  rw [← hg] at this
  omega

/-! ## The cofactors `w i` with `hasseDeriv i (g^u) = g^(u-i) * w i` -/

private lemma hasseDeriv_pow_factor_aux {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (_hd : 1 ≤ g.natDegree) (u i : ℕ) (hi : i ≤ u) :
    ∃ w : Polynomial F, Polynomial.hasseDeriv i (g ^ u) = g ^ (u - i) * w ∧
      w.natDegree ≤ i * g.natDegree := by
  have key : ∀ (u i : ℕ), i ≤ u → g ^ (u - i) ∣ Polynomial.hasseDeriv i (g ^ u) := by
    intro u
    induction u with
    | zero =>
      intro i hi
      have : i = 0 := Nat.le_zero.mp hi
      subst this; simp
    | succ v ih =>
      intro i hi
      rw [pow_succ, Polynomial.hasseDeriv_mul]
      apply Finset.dvd_sum
      rintro ⟨a, b⟩ hab
      have habx : a + b = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      rcases Nat.eq_zero_or_pos b with hb0 | hb1
      · rw [hb0, add_zero] at habx
        rw [← habx]
        simp only [hb0, Polynomial.hasseDeriv_zero]
        by_cases hav : a ≤ v
        · have h1 : g ^ (v - a) ∣ Polynomial.hasseDeriv a (g ^ v) := ih a hav
          have h2 : v + 1 - a = (v - a) + 1 := by omega
          rw [h2, pow_succ]
          exact mul_dvd_mul h1 dvd_rfl
        · have h3 : v + 1 - a = 0 := by omega
          rw [h3, pow_zero]; exact one_dvd _
      · have ha_le : a ≤ v := by omega
        have h1 : g ^ (v - a) ∣ Polynomial.hasseDeriv a (g ^ v) := ih a ha_le
        have hle : v + 1 - i ≤ v - a := by omega
        have h2 : g ^ (v + 1 - i) ∣ g ^ (v - a) := pow_dvd_pow g hle
        exact dvd_mul_of_dvd_left (dvd_trans h2 h1) _
  obtain ⟨w, hw⟩ := key u i hi
  refine ⟨w, hw, ?_⟩
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  · have hgu : g ^ (u - i) ≠ 0 := pow_ne_zero _ hg
    have hwnd : (Polynomial.hasseDeriv i (g ^ u)).natDegree
        = (u - i) * g.natDegree + w.natDegree := by
      rw [hw, Polynomial.natDegree_mul hgu hw0, Polynomial.natDegree_pow]
    have hle := Polynomial.natDegree_hasseDeriv_le (g ^ u) i
    rw [Polynomial.natDegree_pow] at hle
    set A := (u - i) * g.natDegree with hA
    set B := u * g.natDegree with hB
    set C := i * g.natDegree with hC
    have h1 : A + w.natDegree ≤ B := by rw [← hwnd]; exact hle.trans (Nat.sub_le _ _)
    have h2 : A + C = B := by rw [hA, hB, hC, ← Nat.add_mul, Nat.sub_add_cancel hi]
    omega

/-- The cofactor `w` in `hasseDeriv i (g^u) = g^(u-i) * w`. -/
private noncomputable def wcoef {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) (u i : ℕ) : Polynomial F :=
  if h : i ≤ u then Classical.choose (hasseDeriv_pow_factor_aux g hg hd u i h) else 0

private lemma wcoef_spec {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) (u i : ℕ) (hi : i ≤ u) :
    Polynomial.hasseDeriv i (g ^ u) = g ^ (u - i) * wcoef g hg hd u i ∧
      (wcoef g hg hd u i).natDegree ≤ i * g.natDegree := by
  have h := Classical.choose_spec (hasseDeriv_pow_factor_aux g hg hd u i hi)
  rw [wcoef, dif_pos hi]
  exact h

/-! ## The Frobenius-form auxiliary maps `A₀`, `A₁` and the key identity -/

/-- Multiplication by a fixed polynomial, as an `F`-linear map. -/
def mulLM {F : Type*} [Field F] (a : Polynomial F) : Polynomial F →ₗ[F] Polynomial F :=
  (LinearMap.mulLeft (Polynomial F) a).restrictScalars F

/-- The `Y = X` specialization `F[X][Y] → F[X]`. -/
def evX {F : Type*} [Field F] : Polynomial (Polynomial F) →ₗ[F] Polynomial F :=
  (Polynomial.leval (Polynomial.X : Polynomial F)).restrictScalars F

@[simp] lemma mulLM_apply {F : Type*} [Field F] (a p : Polynomial F) : mulLM a p = a * p := rfl
@[simp] lemma evX_apply {F : Type*} [Field F] (P : Polynomial (Polynomial F)) :
    evX P = Polynomial.eval (Polynomial.X : Polynomial F) P := rfl

variable {F : Type*} [Field F]

/-- `A₀,ℓ`: the `ℓ`-th summand coming from `P`, as a linear map on `F[X][Y]`. -/
def A0lm (g : Polynomial F) (ℓ : ℕ) : Polynomial (Polynomial F) →ₗ[F] Polynomial F :=
  (mulLM (g^ℓ)).comp (evX.comp (Dlm ℓ))

/-- `A₁,ℓ`: the `ℓ`-th summand coming from `Q`, as a linear map on `F[X][Y]`. -/
def A1lm (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (u ℓ : ℕ) :
    Polynomial (Polynomial F) →ₗ[F] Polynomial F :=
  ∑ i ∈ Finset.range (ℓ+1),
    (mulLM (g^(ℓ-i) * wcoef g hg hd u i)).comp (evX.comp (Dlm (ℓ-i)))

lemma A0lm_apply (g : Polynomial F) (ℓ : ℕ) (P : Polynomial (Polynomial F)) :
    A0lm g ℓ P = g^ℓ * (D ℓ P).eval (Polynomial.X : Polynomial F) := by
  simp [A0lm, LinearMap.comp_apply]

lemma A1lm_apply (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (u ℓ : ℕ)
    (Q : Polynomial (Polynomial F)) :
    A1lm g hg hd u ℓ Q = ∑ i ∈ Finset.range (ℓ+1),
      (g^(ℓ-i) * wcoef g hg hd u i) * (D (ℓ-i) Q).eval (Polynomial.X : Polynomial F) := by
  simp only [A1lm, LinearMap.sum_apply, LinearMap.comp_apply, mulLM_apply, evX_apply, Dlm_apply]

/-! ## Degree bounds for `A₀`, `A₁` -/

lemma A0lm_natDegree_le (g : Polynomial F) (ℓ A B : ℕ) (P : Polynomial (Polynomial F))
    (hA : ∀ j, (P.coeff j).natDegree ≤ A) (hB : P.natDegree ≤ B) :
    (A0lm g ℓ P).natDegree ≤ ℓ * g.natDegree + (A + B) := by
  rw [A0lm_apply]
  calc (g^ℓ * (D ℓ P).eval (Polynomial.X : Polynomial F)).natDegree
      ≤ (g^ℓ).natDegree + ((D ℓ P).eval (Polynomial.X : Polynomial F)).natDegree :=
        Polynomial.natDegree_mul_le
    _ = ℓ * g.natDegree + ((D ℓ P).eval (Polynomial.X : Polynomial F)).natDegree := by
        rw [Polynomial.natDegree_pow]
    _ ≤ ℓ * g.natDegree + (A + B) := by
        have h := eval_X_natDegree_le (D ℓ P) A B (D_coeff_natDegree_le ℓ P A hA)
          ((D_natDegree_le ℓ P).trans hB)
        omega

lemma A1lm_natDegree_le (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (u ℓ A B : ℕ)
    (hℓu : ℓ ≤ u) (Q : Polynomial (Polynomial F))
    (hA : ∀ j, (Q.coeff j).natDegree ≤ A) (hB : Q.natDegree ≤ B) :
    (A1lm g hg hd u ℓ Q).natDegree ≤ ℓ * g.natDegree + (A + B) := by
  rw [A1lm_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro i hi
  rw [Finset.mem_range] at hi
  have hiu : i ≤ u := by omega
  have hw := (wcoef_spec g hg hd u i hiu).2
  have hD := eval_X_natDegree_le (D (ℓ-i) Q) A B (D_coeff_natDegree_le (ℓ-i) Q A hA)
    ((D_natDegree_le (ℓ-i) Q).trans hB)
  calc ((g^(ℓ-i) * wcoef g hg hd u i) * (D (ℓ-i) Q).eval (Polynomial.X : Polynomial F)).natDegree
      ≤ (g^(ℓ-i) * wcoef g hg hd u i).natDegree
          + ((D (ℓ-i) Q).eval (Polynomial.X : Polynomial F)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ ((ℓ-i) * g.natDegree + i * g.natDegree) + (A + B) := by
        have h1 : (g^(ℓ-i) * wcoef g hg hd u i).natDegree
            ≤ (g^(ℓ-i)).natDegree + (wcoef g hg hd u i).natDegree := Polynomial.natDegree_mul_le
        rw [Polynomial.natDegree_pow] at h1
        omega
    _ = ℓ * g.natDegree + (A + B) := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (by omega : i ≤ ℓ)]

/-! ## The key Frobenius-form identity -/

lemma hasseDeriv_frobenius_form {F : Type*} [Field F] [Fintype F]
    (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree)
    (u ℓ : ℕ) (hq : ℓ < Fintype.card F) (hℓu : ℓ ≤ u) (P Q : Polynomial (Polynomial F)) :
    g^ℓ * Polynomial.hasseDeriv ℓ (P.eval (Polynomial.X ^ Fintype.card F)
        + g^u * Q.eval (Polynomial.X ^ Fintype.card F))
      = (Polynomial.C (g^ℓ) * D ℓ P).eval (Polynomial.X ^ Fintype.card F)
        + g^u * ((∑ i ∈ Finset.range (ℓ+1),
            Polynomial.C (g^(ℓ-i) * wcoef g hg hd u i) * D (ℓ-i) Q).eval
              (Polynomial.X ^ Fintype.card F)) := by
  have hsplit : Polynomial.hasseDeriv ℓ (P.eval (Polynomial.X ^ Fintype.card F)
        + g^u * Q.eval (Polynomial.X ^ Fintype.card F))
      = Polynomial.hasseDeriv ℓ (P.eval (Polynomial.X ^ Fintype.card F))
        + Polynomial.hasseDeriv ℓ (g^u * Q.eval (Polynomial.X ^ Fintype.card F)) :=
    map_add (Polynomial.hasseDeriv ℓ) _ _
  have hP : Polynomial.hasseDeriv ℓ (P.eval (Polynomial.X ^ Fintype.card F))
      = (D ℓ P).eval (Polynomial.X ^ Fintype.card F) :=
    hasseDeriv_eval_X_pow_card P ℓ hq
  have hQ : Polynomial.hasseDeriv ℓ (g^u * Q.eval (Polynomial.X ^ Fintype.card F))
      = ∑ i ∈ Finset.range (ℓ+1),
          Polynomial.hasseDeriv i (g^u) * (D (ℓ-i) Q).eval (Polynomial.X ^ Fintype.card F) := by
    rw [Polynomial.hasseDeriv_mul]
    have hstep : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal ℓ,
        Polynomial.hasseDeriv ij.1 (g^u)
          * Polynomial.hasseDeriv ij.2 (Q.eval (Polynomial.X ^ Fintype.card F)))
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal ℓ,
            Polynomial.hasseDeriv ij.1 (g^u)
              * (D ij.2 Q).eval (Polynomial.X ^ Fintype.card F) := by
      apply Finset.sum_congr rfl
      rintro ⟨i,j⟩ hij
      have hj : j < Fintype.card F := by
        have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij; omega
      rw [hasseDeriv_eval_X_pow_card Q j hj]
      rfl
    rw [hstep,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => Polynomial.hasseDeriv i (g^u) * (D j Q).eval (Polynomial.X ^ Fintype.card F))]
  rw [hsplit, hP, hQ, mul_add]
  congr 1
  · rw [Polynomial.eval_mul, Polynomial.eval_C]
  · rw [Finset.mul_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hiu : i ≤ u := by omega
    rw [Polynomial.eval_mul, Polynomial.eval_C, (wcoef_spec g hg hd u i hiu).1]
    have he : ℓ + (u - i) = u + (ℓ - i) := by omega
    calc g ^ ℓ * (g ^ (u - i) * wcoef g hg hd u i
            * eval (Polynomial.X ^ Fintype.card F) (D (ℓ - i) Q))
        = g ^ (ℓ + (u - i)) * (wcoef g hg hd u i
            * eval (Polynomial.X ^ Fintype.card F) (D (ℓ - i) Q)) := by
          rw [pow_add]; ring
      _ = g ^ (u + (ℓ - i)) * (wcoef g hg hd u i
            * eval (Polynomial.X ^ Fintype.card F) (D (ℓ - i) Q)) := by rw [he]
      _ = g ^ u * (g ^ (ℓ - i) * wcoef g hg hd u i
            * eval (Polynomial.X ^ Fintype.card F) (D (ℓ - i) Q)) := by
          rw [pow_add]; ring

/-! ## The constraint polynomial `A₀,ℓ P + A₁,ℓ Q` and the vanishing lemma -/

/-- The `ℓ`-th constraint polynomial of Stepanov's method. -/
def condPoly (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (u ℓ : ℕ) :
    (Polynomial (Polynomial F) × Polynomial (Polynomial F)) →ₗ[F] Polynomial F :=
  (A0lm g ℓ).comp (LinearMap.fst F (Polynomial (Polynomial F)) (Polynomial (Polynomial F)))
    + (A1lm g hg hd u ℓ).comp (LinearMap.snd F (Polynomial (Polynomial F)) (Polynomial (Polynomial F)))

lemma condPoly_apply (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (u ℓ : ℕ)
    (P Q : Polynomial (Polynomial F)) :
    condPoly g hg hd u ℓ (P,Q) = A0lm g ℓ P + A1lm g hg hd u ℓ Q := by
  simp [condPoly, LinearMap.comp_apply]

lemma eval_X_C_mul (g : Polynomial F) (ℓ : ℕ) (P : Polynomial (Polynomial F)) :
    (Polynomial.C (g^ℓ) * D ℓ P).eval (Polynomial.X : Polynomial F) = A0lm g ℓ P := by
  rw [A0lm_apply, Polynomial.eval_mul, Polynomial.eval_C]

lemma eval_X_C_sum (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (u ℓ : ℕ)
    (Q : Polynomial (Polynomial F)) :
    (∑ i ∈ Finset.range (ℓ+1),
        Polynomial.C (g^(ℓ-i) * wcoef g hg hd u i) * D (ℓ-i) Q).eval (Polynomial.X : Polynomial F)
      = A1lm g hg hd u ℓ Q := by
  rw [A1lm_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C]

lemma eval_eval_Xq_eq {F : Type*} [Field F] [Fintype F] (p : Polynomial (Polynomial F)) (x : F) :
    Polynomial.eval x (p.eval (Polynomial.X ^ Fintype.card F))
      = Polynomial.eval x (p.eval Polynomial.X) := by
  have h1 : Polynomial.eval x (Polynomial.eval (Polynomial.X ^ Fintype.card F) p)
      = Polynomial.eval₂ (Polynomial.evalRingHom x)
          (Polynomial.eval x (Polynomial.X ^ Fintype.card F)) p :=
    (Polynomial.eval₂_at_apply (f := Polynomial.evalRingHom x) (Polynomial.X ^ Fintype.card F)
      (p := p)).symm
  have h2 : Polynomial.eval x (Polynomial.eval (Polynomial.X : Polynomial F) p)
      = Polynomial.eval₂ (Polynomial.evalRingHom x)
          (Polynomial.eval x (Polynomial.X : Polynomial F)) p :=
    (Polynomial.eval₂_at_apply (f := Polynomial.evalRingHom x) (Polynomial.X : Polynomial F)
      (p := p)).symm
  rw [h1, h2, Polynomial.eval_pow, Polynomial.eval_X, FiniteField.pow_card]

/-- If the constraint polynomial `A₀,ℓ P + A₁,ℓ Q` vanishes identically and `g x^u = 1`, then the
`ℓ`-th Hasse derivative of `R = P(X, X^q) + g^u Q(X, X^q)` vanishes at `x`. -/
lemma hasseDeriv_eval_eq_zero_of_cond {F : Type*} [Field F] [Fintype F]
    (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (u ℓ : ℕ)
    (hq : ℓ < Fintype.card F) (hℓu : ℓ ≤ u) (hu : 1 ≤ u) (P Q : Polynomial (Polynomial F))
    (hcond : A0lm g ℓ P + A1lm g hg hd u ℓ Q = 0) (x : F) (hx : g.eval x ^ u = 1) :
    (Polynomial.hasseDeriv ℓ (P.eval (Polynomial.X ^ Fintype.card F)
      + g^u * Q.eval (Polynomial.X ^ Fintype.card F))).eval x = 0 := by
  have keyU : Polynomial.eval x ((Polynomial.C (g^ℓ) * D ℓ P).eval (Polynomial.X ^ Fintype.card F))
      = Polynomial.eval x (A0lm g ℓ P) := by
    rw [eval_eval_Xq_eq, eval_X_C_mul]
  have keyV : Polynomial.eval x ((∑ i ∈ Finset.range (ℓ+1),
        Polynomial.C (g^(ℓ-i) * wcoef g hg hd u i) * D (ℓ-i) Q).eval
          (Polynomial.X ^ Fintype.card F))
      = Polynomial.eval x (A1lm g hg hd u ℓ Q) := by
    rw [eval_eval_Xq_eq, eval_X_C_sum]
  have keyL : Polynomial.eval x (g^ℓ * Polynomial.hasseDeriv ℓ (P.eval (Polynomial.X ^ Fintype.card F)
        + g^u * Q.eval (Polynomial.X ^ Fintype.card F)))
      = (g.eval x)^ℓ * Polynomial.eval x (Polynomial.hasseDeriv ℓ
          (P.eval (Polynomial.X ^ Fintype.card F)
            + g^u * Q.eval (Polynomial.X ^ Fintype.card F))) := by
    rw [Polynomial.eval_mul, Polynomial.eval_pow]
  have hval : Polynomial.eval x (A0lm g ℓ P) = - Polynomial.eval x (A1lm g hg hd u ℓ Q) := by
    have hh := congrArg (Polynomial.eval x) hcond
    rw [Polynomial.eval_add, Polynomial.eval_zero] at hh
    linear_combination (norm := ring) hh
  have hgx : g.eval x ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega : u ≠ 0)] at hx; exact one_ne_zero hx.symm
  have h := congrArg (Polynomial.eval x) (hasseDeriv_frobenius_form g hg hd u ℓ hq hℓu P Q)
  rw [keyL, Polynomial.eval_add] at h
  rw [keyU, Polynomial.eval_mul, Polynomial.eval_pow, keyV] at h
  rw [hval, hx, one_mul, neg_add_cancel] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hgx)

/-! ## `toPolyLm` degree bounds and injectivity -/

lemma toPolyLm_coeff_natDegree_le (A B : ℕ) (c : Fin (A+1) × Fin (B+1) → F) :
    ∀ j, ((toPolyLm A B c).coeff j).natDegree ≤ A := by
  intro j
  rw [toPolyLm_apply]
  have h1 : (∑ p : Fin (A+1) × Fin (B+1),
      Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))).coeff j
      = ∑ p : Fin (A+1) × Fin (B+1),
        (Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))).coeff j := by
    simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff (Polynomial F) j)
      (fun p : Fin (A+1) × Fin (B+1) =>
        Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))) Finset.univ
  rw [h1]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro p _
  rw [Function.comp_apply, Polynomial.coeff_monomial]
  split_ifs with h
  · exact (Polynomial.natDegree_monomial_le (c p)).trans (by have hh := p.1.2; omega)
  · simp

lemma toPolyLm_natDegree_le (A B : ℕ) (c : Fin (A+1) × Fin (B+1) → F) :
    (toPolyLm A B c).natDegree ≤ B := by
  rw [toPolyLm_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro p _
  rw [Function.comp_apply]
  have h1 : (Polynomial.monomial (p.2:ℕ) (Polynomial.monomial (p.1:ℕ) (c p))).natDegree ≤ (p.2:ℕ) :=
    Polynomial.natDegree_monomial_le _
  have h2 : (p.2:ℕ) ≤ B := by
    have hh : ((p.2 : Fin (B+1)) : ℕ) < B + 1 := (p.2).isLt
    omega
  exact h1.trans h2

lemma toPolyLm_injective (A B : ℕ) : Function.Injective (toPolyLm (F := F) A B) := by
  intro c c' h
  funext p
  obtain ⟨i,j⟩ := p
  have h2 := congrArg (fun P => (P.coeff (j:ℕ)).coeff (i:ℕ)) h
  rw [toPolyLm_coeff, toPolyLm_coeff] at h2
  exact h2

/-- `(P.eval (X ^ q)).natDegree ≤ A + q * B` when the `Y`-coefficients of `P` have `X`-degree
`≤ A` and `deg_Y P ≤ B`. -/
lemma eval_Xq_natDegree_le (P : Polynomial (Polynomial F)) (A B q : ℕ)
    (hcoeff : ∀ j, (P.coeff j).natDegree ≤ A) (hdeg : P.natDegree ≤ B) :
    (P.eval ((Polynomial.X : Polynomial F) ^ q)).natDegree ≤ A + q * B := by
  classical
  rw [Polynomial.eval_eq_sum_range]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro i hi
  rw [Function.comp_apply]
  calc (P.coeff i * ((Polynomial.X : Polynomial F) ^ q) ^ i).natDegree
      ≤ (P.coeff i).natDegree + (((Polynomial.X : Polynomial F) ^ q) ^ i).natDegree :=
        Polynomial.natDegree_mul_le
    _ = (P.coeff i).natDegree + q * i := by rw [← pow_mul, Polynomial.natDegree_X_pow]
    _ ≤ A + q * B := by
        have hi' : i ≤ P.natDegree := by rw [Finset.mem_range] at hi; omega
        have := hcoeff i
        nlinarith [hdeg, hi']  -- hmm

/-! ## Counting roots with multiplicity -/

lemma X_sub_C_pow_dvd_of_hasseDeriv {F : Type*} [Field F] {R : Polynomial F} {x : F} {M : ℕ}
    (h : ∀ ℓ < M, (Polynomial.hasseDeriv ℓ R).eval x = 0) :
    (Polynomial.X - Polynomial.C x)^M ∣ R := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, ← Polynomial.taylor_apply, Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.taylor_coeff]
  exact h d hd

lemma card_mul_le_natDegree_of_pow_dvd {R : Polynomial F} (hR : R ≠ 0)
    {S : Finset F} {M : ℕ} (h : ∀ x ∈ S, (Polynomial.X - Polynomial.C x)^M ∣ R) :
    S.card * M ≤ R.natDegree := by
  classical
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0; simp
  · have hQdvd : (∏ x ∈ S, (Polynomial.X - Polynomial.C x)^M) ∣ R := by
      refine Finset.prod_dvd_of_coprime ?_ h
      intro x hx y hy hxy
      have hxy' : (x : F) - y ≠ 0 := sub_ne_zero.mpr hxy
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr hxy')).pow
    have hQdvd' : (∏ x ∈ S, (Polynomial.X - Polynomial.C x))^M ∣ R := by
      rw [← Finset.prod_pow]; exact hQdvd
    have hdeg : ((∏ x ∈ S, (Polynomial.X - Polynomial.C x))^M).natDegree ≤ R.natDegree :=
      Polynomial.natDegree_le_of_dvd hQdvd' hR
    rw [Polynomial.natDegree_pow] at hdeg
    have hQdeg : (∏ x ∈ S, (Polynomial.X - Polynomial.C x) : Polynomial F).natDegree = S.card := by
      rw [Polynomial.natDegree_prod _ _ (fun x _ => Polynomial.X_sub_C_ne_zero x)]
      simp [Polynomial.natDegree_X_sub_C]
    rw [hQdeg, Nat.mul_comm] at hdeg
    exact hdeg

/-! ## The Stepanov counting lemma -/

theorem stepanov_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (g : Polynomial F) (hsep : g.Separable) (hd : 1 ≤ g.natDegree)
    (A B M : ℕ) (hA : 2*A + 2*(g.natDegree+1) < Fintype.card F) (hB : B < Fintype.card F)
    (hM : M ≤ (Fintype.card F - 1)/2 + 1)
    (hdim : M*(A+B+1) + g.natDegree*M*M < 2*((A+1)*(B+1))) :
    (({a : F | g.eval a ^ ((Fintype.card F - 1)/2) = 1} : Set F).ncard) * M ≤
      A + Fintype.card F * B + (Fintype.card F - 1)/2 * g.natDegree := by
  classical
  have hg : g ≠ 0 := by intro h0; rw [h0] at hd; simp at hd
  have hnd := not_const_mul_sq_of_separable g hsep hd
  have hq3 : 3 ≤ Fintype.card F := by
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    have hp3 : 3 ≤ ringChar F := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hF
      · have := hp.two_le; omega
    calc 3 ≤ ringChar F := hp3
      _ ≤ ringChar F ^ (n:ℕ) := Nat.le_self_pow (ne_of_gt (PNat.pos n)) (ringChar F)
      _ = Fintype.card F := hn.symm
  have hu1 : 1 ≤ (Fintype.card F - 1)/2 := by omega
  let ι := Fin (A+1) × Fin (B+1)
  let E := (ι → F) × (ι → F)
  let pairLM : E →ₗ[F] (Polynomial (Polynomial F) × Polynomial (Polynomial F)) :=
    LinearMap.prod ((toPolyLm (F := F) A B).comp (LinearMap.fst F (ι → F) (ι → F)))
      ((toPolyLm (F := F) A B).comp (LinearMap.snd F (ι → F) (ι → F)))
  let Cc := (ℓ : Fin M) → Fin (A + B + ℓ.val * g.natDegree + 1) → F
  let Φ : E →ₗ[F] Cc := LinearMap.pi (fun ℓ : Fin M => LinearMap.pi
    (fun k : Fin (A + B + ℓ.val * g.natDegree + 1) =>
      (Polynomial.lcoeff F k).comp
        ((condPoly g hg hd ((Fintype.card F - 1)/2) ℓ.val).comp pairLM)))
  have hfinE : Module.finrank F E = 2 * ((A+1)*(B+1)) := by
    simp only [E, ι, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Fintype.card_prod, Fintype.card_fin]
    ring
  have hfinCle : Module.finrank F Cc ≤ M*(A+B+1) + g.natDegree*M*M := by
    have h1 : Module.finrank F Cc
        = ∑ ℓ : Fin M, (A + B + ℓ.val * g.natDegree + 1) := by
      simp only [Cc, Module.finrank_pi_fintype, Module.finrank_self, Fintype.card_fin,
        Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    rw [h1, Fin.sum_univ_eq_sum_range (fun i => (A + B + i * g.natDegree + 1)) M]
    calc ∑ i ∈ Finset.range M, (A + B + i * g.natDegree + 1)
        ≤ ∑ i ∈ Finset.range M, ((A + B + 1) + g.natDegree * M) := by
          apply Finset.sum_le_sum
          intro i hi
          have h2 : i * g.natDegree ≤ M * g.natDegree :=
            Nat.mul_le_mul_right _ (le_of_lt (Finset.mem_range.mp hi))
          have h3 : g.natDegree * M = M * g.natDegree := Nat.mul_comm _ _
          omega
      _ = M * ((A + B + 1) + g.natDegree * M) := by
          rw [Finset.sum_const, Finset.card_range]
          simp
      _ = M*(A+B+1) + g.natDegree*M*M := by ring
  have hlt : Module.finrank F Cc < Module.finrank F E := by
    rw [hfinE]
    exact lt_of_le_of_lt hfinCle hdim
  have hker : Φ.ker ≠ ⊥ := by
    intro hbot
    have h1 := Φ.finrank_range_add_finrank_ker
    have h2 : Module.finrank F Φ.range ≤ Module.finrank F Cc := Submodule.finrank_le _
    rw [hbot] at h1
    simp only [finrank_bot, add_zero] at h1
    omega
  obtain ⟨x, hxker, hx0⟩ := (Submodule.ne_bot_iff Φ.ker).mp hker
  rw [LinearMap.mem_ker] at hxker
  obtain ⟨c, c'⟩ := x
  set P : Polynomial (Polynomial F) := toPolyLm (F := F) A B c with hP
  set Q : Polynomial (Polynomial F) := toPolyLm (F := F) A B c' with hQ
  have hpair : pairLM (c,c') = (P, Q) := by
    rw [show pairLM (c,c') = ((toPolyLm (F:=F) A B) c, (toPolyLm (F:=F) A B) c') from rfl,
      ← hP, ← hQ]
  have hΦ : ∀ (ℓ : Fin M) (k : Fin (A + B + ℓ.val * g.natDegree + 1)),
      Φ (c,c') ℓ k = (condPoly g hg hd ((Fintype.card F - 1)/2) ℓ.val (P,Q)).coeff k := by
    intro ℓ k
    rfl
  have hcond : ∀ ℓ : Fin M,
      A0lm g ℓ.val P + A1lm g hg hd ((Fintype.card F - 1)/2) ℓ.val Q = 0 := by
    intro ℓ
    have hdegC : (condPoly g hg hd ((Fintype.card F - 1)/2) ℓ.val (P,Q)).natDegree
        < A + B + ℓ.val * g.natDegree + 1 := by
      rw [condPoly_apply]
      refine (Polynomial.natDegree_add_le _ _).trans_lt ?_
      rw [max_lt_iff]
      refine ⟨?_, ?_⟩
      · have h1 := A0lm_natDegree_le g ℓ.val A B P (toPolyLm_coeff_natDegree_le A B c)
            (toPolyLm_natDegree_le A B c)
        omega
      · have h2 := A1lm_natDegree_le g hg hd ((Fintype.card F - 1)/2) ℓ.val A B
            (by have := ℓ.isLt; omega) Q (toPolyLm_coeff_natDegree_le A B c')
            (toPolyLm_natDegree_le A B c')
        omega
    apply eq_zero_of_coeff_eq_zero hdegC
    intro n hn
    have hk := congrFun (congrFun hxker ℓ) ⟨n, hn⟩
    rw [hΦ] at hk
    exact hk
  have hRne : P.eval (Polynomial.X ^ Fintype.card F)
      + g ^ ((Fintype.card F - 1)/2) * Q.eval (Polynomial.X ^ Fintype.card F) ≠ 0 := by
    have hPQ : P ≠ 0 ∨ Q ≠ 0 := by
      by_contra hc
      push Not at hc
      obtain ⟨hP0, hQ0⟩ := hc
      apply hx0
      have hc0 : c = 0 := toPolyLm_injective (F := F) A B (by simp [← hP, hP0])
      have hc0' : c' = 0 := toPolyLm_injective (F := F) A B (by simp [← hQ, hQ0])
      exact Prod.ext hc0 hc0' 
    exact kopparty_sq_nonvanishing g hnd A hA P Q hPQ
      (toPolyLm_coeff_natDegree_le A B c) (toPolyLm_coeff_natDegree_le A B c')
      (lt_of_le_of_lt (toPolyLm_natDegree_le A B c) hB)
      (lt_of_le_of_lt (toPolyLm_natDegree_le A B c') hB)
  have hmult : ∀ x ∈ ({a : F | g.eval a ^ ((Fintype.card F - 1)/2) = 1} : Set F).toFinset,
      (Polynomial.X - Polynomial.C x)^M ∣ P.eval (Polynomial.X ^ Fintype.card F)
        + g ^ ((Fintype.card F - 1)/2) * Q.eval (Polynomial.X ^ Fintype.card F) := by
    intro x hxS
    have hxS' : g.eval x ^ ((Fintype.card F - 1)/2) = 1 := by
      simpa using (Set.mem_toFinset.mp hxS)
    apply X_sub_C_pow_dvd_of_hasseDeriv
    intro ℓ hℓ
    refine hasseDeriv_eval_eq_zero_of_cond g hg hd ((Fintype.card F - 1)/2) ℓ ?_ ?_ hu1 P Q
      (hcond ⟨ℓ, hℓ⟩) x hxS'
    · omega
    · omega
  have hcard := card_mul_le_natDegree_of_pow_dvd hRne hmult
  have hRdeg : (P.eval (Polynomial.X ^ Fintype.card F)
      + g ^ ((Fintype.card F - 1)/2) * Q.eval (Polynomial.X ^ Fintype.card F)).natDegree
      ≤ A + Fintype.card F * B + (Fintype.card F - 1)/2 * g.natDegree := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · have h1 := eval_Xq_natDegree_le P A B (Fintype.card F) (toPolyLm_coeff_natDegree_le A B c)
          (toPolyLm_natDegree_le A B c)
      exact h1.trans (Nat.le_add_right _ _)
    · calc (g ^ ((Fintype.card F - 1)/2) * Q.eval (Polynomial.X ^ Fintype.card F)).natDegree
          ≤ (g ^ ((Fintype.card F - 1)/2)).natDegree
              + (Q.eval (Polynomial.X ^ Fintype.card F)).natDegree := Polynomial.natDegree_mul_le
        _ ≤ (Fintype.card F - 1)/2 * g.natDegree + (A + Fintype.card F * B) := by
            have h1 := eval_Xq_natDegree_le Q A B (Fintype.card F)
              (toPolyLm_coeff_natDegree_le A B c') (toPolyLm_natDegree_le A B c')
            rw [Polynomial.natDegree_pow]
            omega
        _ ≤ A + Fintype.card F * B + (Fintype.card F - 1)/2 * g.natDegree := by omega
  rw [Set.ncard_eq_toFinset_card']
  exact hcard.trans hRdeg

/-! ## The character sum as a difference of counting functions -/

private lemma quadraticChar_eq_indicator {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (y : F) :
    quadraticChar F y
      = (if y ^ (Fintype.card F / 2) = 1 then (1:ℤ) else 0)
        - (if y ^ (Fintype.card F / 2) = -1 then (1:ℤ) else 0) := by
  have hcard2 : Fintype.card F / 2 ≠ 0 := by
    have := Fintype.one_lt_card (α := F); omega
  have hne : (1:F) ≠ -1 := (Ring.neg_one_ne_one_of_char_ne_two hF).symm
  rcases eq_or_ne y 0 with rfl | hy
  · rw [quadraticChar_zero, zero_pow hcard2]
    rw [if_neg zero_ne_one, if_neg (neg_ne_zero.mpr one_ne_zero).symm]
    norm_num
  · have hcast : ((quadraticChar F y : ℤ) : F) = y ^ (Fintype.card F / 2) :=
      quadraticChar_eq_pow_of_char_ne_two' hF y
    have hmem : (quadraticChar F y : ℤ) = 1 ∨ (quadraticChar F y : ℤ) = -1 :=
      sq_eq_one_iff.mp (quadraticChar_sq_one hy)
    rcases hmem with h1 | h1
    · have hy1 : y ^ (Fintype.card F / 2) = 1 := by rw [← hcast, h1]; norm_num
      rw [h1]
      rw [if_pos hy1]
      rw [if_neg (fun hc => hne (hy1.symm.trans hc))]
      norm_num
    · have hy1 : y ^ (Fintype.card F / 2) = -1 := by rw [← hcast, h1]; norm_num
      rw [h1]
      rw [if_pos hy1]
      rw [if_neg (fun hc => hne (hy1.symm.trans hc).symm)]
      norm_num

private lemma abs_quadraticChar_le_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a : F) : |(quadraticChar F a : ℝ)| ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [quadraticChar_zero]; norm_num
  · have h := sq_eq_one_iff.mp (quadraticChar_sq_one ha)
    rcases h with h | h
    · rw [show (quadraticChar F a : ℝ) = 1 by exact_mod_cast h]; norm_num
    · rw [show (quadraticChar F a : ℝ) = -1 by exact_mod_cast h]; norm_num

private lemma char_sum_eq_ncard_sub {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (g : Polynomial F) :
    (∑ a : F, quadraticChar F (g.eval a))
      = (({a : F | g.eval a ^ (Fintype.card F / 2) = 1} : Set F).ncard : ℤ)
        - (({a : F | g.eval a ^ (Fintype.card F / 2) = -1} : Set F).ncard : ℤ) := by
  classical
  have h1 : (∑ a : F, quadraticChar F (g.eval a))
      = (∑ a ∈ (Finset.univ : Finset F),
            (if g.eval a ^ (Fintype.card F / 2) = 1 then (1:ℤ) else 0))
        - (∑ a ∈ (Finset.univ : Finset F),
            (if g.eval a ^ (Fintype.card F / 2) = -1 then (1:ℤ) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    exact quadraticChar_eq_indicator hF (g.eval a)
  have hf1 : (Finset.univ.filter (fun a : F => g.eval a ^ (Fintype.card F / 2) = 1))
      = ({a : F | g.eval a ^ (Fintype.card F / 2) = 1} : Set F).toFinset := by
    apply Finset.ext; intro a; simp [Set.mem_toFinset]
  have hf2 : (Finset.univ.filter (fun a : F => g.eval a ^ (Fintype.card F / 2) = -1))
      = ({a : F | g.eval a ^ (Fintype.card F / 2) = -1} : Set F).toFinset := by
    apply Finset.ext; intro a; simp [Set.mem_toFinset]
  rw [h1, Finset.sum_boole, Finset.sum_boole]
  rw [show {x ∈ (Finset.univ : Finset F) | g.eval x ^ (Fintype.card F / 2) = 1}
        = Finset.univ.filter _ from rfl,
      show {x ∈ (Finset.univ : Finset F) | g.eval x ^ (Fintype.card F / 2) = -1}
        = Finset.univ.filter _ from rfl, hf1, hf2,
      Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']

private lemma abs_char_sum_le_card {F : Type*} [Field F] [Fintype F] [DecidableEq F] (g : Polynomial F) :
    |∑ a : F, (quadraticChar F (g.eval a) : ℝ)| ≤ (Fintype.card F : ℝ) := by
  calc |∑ a : F, (quadraticChar F (g.eval a) : ℝ)|
      ≤ ∑ a : F, |(quadraticChar F (g.eval a) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : F, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        exact abs_quadraticChar_le_one (g.eval a)
    _ = (Fintype.card F : ℝ) := by simp

/-- The explicit degree threshold for the Stepanov bound. -/
def Qnat (D : ℕ) : ℕ := 1000 * (D + 1)^2 + 1000

/-- Elementary arithmetic for the dimension count: the Stepanov parameters satisfy the
dimension inequality. -/
private lemma hdim_arith (q s d A B : ℕ) (hs : s * s ≤ q)
    (hA2 : 2*A + 2*d + 4 ≤ q) (hA3 : q ≤ 2*A + 2*d + 5)
    (hB2 : 2*B ≤ s + 2*d + 4) (hB3 : s + 2*d + 4 ≤ 2*B + 2)
    (hsd : 20*(d+1) ≤ s) :
    s*(A+B+1) + d*s*s < 2*((A+1)*(B+1)) := by
  have hsq : (s:ℚ)*(s:ℚ) ≤ (q:ℚ) := by exact_mod_cast hs
  have hsdq : (20*((d:ℚ)+1)) ≤ (s:ℚ) := by exact_mod_cast hsd
  have hA2q : (2*(A:ℚ) + 2*d + 4) ≤ (q:ℚ) := by exact_mod_cast hA2
  have hA3q : (q:ℚ) ≤ 2*(A:ℚ) + 2*d + 5 := by exact_mod_cast hA3
  have hB2q : (2*(B:ℚ)) ≤ (s:ℚ) + 2*d + 4 := by exact_mod_cast hB2
  have hB3q : (s:ℚ) + 2*d + 4 ≤ 2*(B:ℚ) + 2 := by exact_mod_cast hB3
  have hgoalq : (s:ℚ)*((A:ℚ)+(B:ℚ)+1) + (d:ℚ)*(s:ℚ)*(s:ℚ)
      < 2*(((A:ℚ)+1)*((B:ℚ)+1)) := by
    nlinarith [hsq, hsdq, hA2q, hA3q, hB2q, hB3q]
  exact_mod_cast hgoalq

/-- Elementary real arithmetic for the final bound: with `s = ⌊√q⌋` and the Stepanov parameters,
the counting bound implies the character-sum bound. -/
private lemma final_arith (q s d A B : ℕ) (hq1 : 1 ≤ q) (hsq : s*s ≤ q) (hq2 : q < (s+1)*(s+1))
    (hA : A ≤ q/2) (hB : B ≤ s/2 + d + 2) :
    (2*((A:ℝ) + (q:ℝ)*B + (((q-1)/2:ℕ):ℝ)*d) - ((q:ℝ)-(d:ℝ))*s) / s
      ≤ (17*d+22)*Real.sqrt q := by
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hq2; omega
    · exact h
  have hs0 : (0:ℝ) < s := by exact_mod_cast hs1
  have hsqR : (s:ℝ)*(s:ℝ) ≤ (q:ℝ) := by exact_mod_cast hsq
  have hq2R : (q:ℝ) ≤ (s:ℝ)*(s:ℝ) + 2*s := by
    have h1 : (s+1)*(s+1) = s*s + 2*s + 1 := by ring
    rw [h1] at hq2
    have : q ≤ s*s + 2*s := by omega
    exact_mod_cast this
  have hs_sqrt : (s:ℝ) ≤ Real.sqrt (q:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq]
    exact_mod_cast hsq
  have h1le : (1:ℝ) ≤ Real.sqrt (q:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [one_pow]
    exact_mod_cast hq1
  have hA' : (A:ℝ) ≤ (q:ℝ)/2 := by
    have h0 : ((q/2 : ℕ) : ℝ) ≤ (q:ℝ)/2 := Nat.cast_div_le
    have h1 : (A:ℝ) ≤ ((q/2 : ℕ) : ℝ) := by exact_mod_cast hA
    linarith
  have hB' : (B:ℝ) ≤ (s:ℝ)/2 + d + 2 := by
    have h0 : ((s/2 : ℕ) : ℝ) ≤ (s:ℝ)/2 := Nat.cast_div_le
    have h1 : (B:ℝ) ≤ ((s/2 + d + 2 : ℕ) : ℝ) := by exact_mod_cast hB
    push_cast at h1
    linarith
  have hC' : (((q-1)/2:ℕ):ℝ)*(d:ℝ) ≤ (q:ℝ)*d/2 := by
    have h0 : 2*((q-1)/2) ≤ q := le_trans (Nat.mul_div_le (q-1) 2) (Nat.sub_le q 1)
    have h0R : (2:ℝ)*(((q-1)/2:ℕ):ℝ) ≤ (q:ℝ) := by exact_mod_cast h0
    nlinarith [h0R]
  have hN : (A:ℝ) + (q:ℝ)*B + (((q-1)/2:ℕ):ℝ)*d
      ≤ (q:ℝ)/2 + (q:ℝ)*((s:ℝ)/2 + d + 2) + (q:ℝ)*d/2 := by
    have hq0 : (0:ℝ) ≤ q := by positivity
    nlinarith [hA', hB', hC', hq0]
  have hstep : 2*((A:ℝ) + (q:ℝ)*B + (((q-1)/2:ℕ):ℝ)*d) - ((q:ℝ)-(d:ℝ))*s
      ≤ 5*(q:ℝ) + 3*(q:ℝ)*d + (d:ℝ)*s := by
    have hq0 : (0:ℝ) ≤ q := by positivity
    nlinarith [hN, hq0]
  have hstep2 : 5*(q:ℝ) + 3*(q:ℝ)*d + (d:ℝ)*s
      ≤ ((3*(d:ℝ)+5)*s + 7*(d:ℝ)+10)*s := by
    nlinarith [hq2R, hs0]
  have hstep3 : ((3*(d:ℝ)+5)*s + 7*(d:ℝ)+10)*s
      ≤ (17*(d:ℝ)+22)*Real.sqrt (q:ℝ)*s := by
    have hs0' : (0:ℝ) ≤ s := le_of_lt hs0
    have h3 : (0:ℝ) ≤ 3*(d:ℝ)+5 := by positivity
    have h4 : (3*(d:ℝ)+5)*s ≤ (3*(d:ℝ)+5)*Real.sqrt q :=
      mul_le_mul_of_nonneg_left hs_sqrt h3
    have h5 : (7:ℝ)*(d:ℝ)+10 ≤ (14*(d:ℝ)+17)*Real.sqrt q := by
      nlinarith [h1le, show (0:ℝ) ≤ d by positivity]
    have h6 : (3*(d:ℝ)+5)*Real.sqrt q + (14*(d:ℝ)+17)*Real.sqrt q
        = (17*(d:ℝ)+22)*Real.sqrt q := by ring
    nlinarith [h4, h5, hs0', h6]
  have hfinal := le_trans hstep (le_trans hstep2 hstep3)
  rw [div_le_iff₀ hs0]
  linarith [hfinal]

/-- **Main quantitative input**: for `#F ≥ Qnat (deg g)` the quadratic character sum of a separable
`g` of degree `≥ 1` is bounded by `(17 deg g + 22) √(#F)`.  (Assembled from `stepanov_count`.) -/
theorem stepanov_char_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (g : Polynomial F) (hsep : g.Separable) (hd : 1 ≤ g.natDegree)
    (hQ : Qnat g.natDegree ≤ Fintype.card F) :
    |∑ a : F, (quadraticChar F (g.eval a) : ℝ)| ≤ (17*g.natDegree + 22) * Real.sqrt (Fintype.card F) := by
  classical
  obtain ⟨α, hαnsq⟩ := FiniteField.exists_nonsquare (F := F) hF
  set q := Fintype.card F with hq_def
  set d := g.natDegree with hd_def
  set s := Nat.sqrt q with hs_def
  have hd1 : 1 ≤ d := hd
  have hg : g ≠ 0 := by
    intro h0
    have hd0 : d = 0 := by rw [hd_def, h0]; simp
    omega
  have hQbig : 1000*(d+1)^2 + 1000 ≤ q := hQ
  have hq1 : 1 ≤ q := by nlinarith [hQbig]
  have hs_sq : s*s ≤ q := Nat.sqrt_le q
  have hq_lt : q < (s+1)*(s+1) := Nat.lt_succ_sqrt q
  have hs20 : 20*(d+1) ≤ s := by
    rw [Nat.le_sqrt]
    nlinarith [hQbig]
  have hs1 : 1 ≤ s := by nlinarith [hs20]
  have h2d4 : 2*d + 4 ≤ q := by
    have h1 : (20*(d+1))*(20*(d+1)) ≤ s*s := Nat.mul_le_mul hs20 hs20
    nlinarith [h1, hs_sq]
  have hqodd : Odd q := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)
  have hqdiv : q/2 = (q-1)/2 := by obtain ⟨k,hk⟩ := hqodd; omega
  have hu1 : 1 ≤ (q-1)/2 := by omega
  have h17 : ((17*d + 22 : ℕ) : ℝ) = 17*(d:ℝ) + 22 := by push_cast; ring
  -- the two sets and the zero set
  set Sg : Set F := {a : F | g.eval a ^ ((q-1)/2) = 1} with hSg_def
  set Sa : Set F := {a : F | g.eval a ^ ((q-1)/2) = -1} with hSa_def
  set T : Set F := {a : F | g.eval a = 0} with hT_def
  have hne1 : (1:F) ≠ -1 := (Ring.neg_one_ne_one_of_char_ne_two hF).symm
  have hdisj : Disjoint Sg Sa := by
    rw [Set.disjoint_left]
    intro a ha hb
    rw [hSg_def] at ha
    rw [hSa_def] at hb
    simp only [Set.mem_setOf_eq] at ha hb
    rw [ha] at hb
    exact hne1 hb
  have hpow : ∀ {a : F}, a ≠ 0 → a ^ ((q-1)/2) = 1 ∨ a ^ ((q-1)/2) = -1 := by
    intro a ha
    have h := FiniteField.pow_dichotomy hF ha
    rwa [← hq_def, hqdiv] at h
  have hcov : Tᶜ ⊆ Sg ∪ Sa := by
    intro a ha
    rw [hT_def] at ha
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha
    rcases hpow ha with h | h
    · exact Or.inl (by rw [hSg_def]; exact h)
    · exact Or.inr (by rw [hSa_def]; exact h)
  have hTle : T.ncard ≤ d := by
    have hsub : T ⊆ (g.roots.toFinset : Set F) := by
      intro a ha
      rw [hT_def] at ha
      simp only [Set.mem_setOf_eq] at ha
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hg).mpr ha)
    calc T.ncard ≤ (g.roots.toFinset : Set F).ncard := Set.ncard_le_ncard hsub
      _ = g.roots.toFinset.card := Set.ncard_coe_finset _
      _ ≤ g.roots.card := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := Polynomial.card_roots' g
      _ = d := rfl
  have hxynat : q - d ≤ Sg.ncard + Sa.ncard := by
    have h1 : Tᶜ.ncard ≤ (Sg ∪ Sa).ncard := Set.ncard_le_ncard hcov
    have h2 : T.ncard + Tᶜ.ncard = q := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
    have h4 : Sg.ncard + Sa.ncard = (Sg ∪ Sa).ncard := (Set.ncard_union_eq hdisj).symm
    omega
  -- parameters
  set A := (q - 2*d - 4)/2 with hA_def
  set M := s with hM_def
  set B := s/2 + d + 2 with hB_def
  set X := A + q*B + ((q-1)/2)*d with hX_def
  have hAh : 2*A + 2*(g.natDegree+1) < Fintype.card F := by
    rw [hA_def]
    have h := Nat.mul_div_le (q - 2*d - 4) 2
    omega
  have hBh : B < Fintype.card F := by
    rw [hB_def]
    have h1 : 2*(s/2) ≤ s := Nat.mul_div_le s 2
    have h2 : s ≤ q := by nlinarith [hs_sq, hs1]
    omega
  have hMh : M ≤ (Fintype.card F - 1)/2 + 1 := by
    have h2 : 2*s ≤ q + 1 := by nlinarith [hs_sq, hs1]
    omega
  have hdim : M*(A+B+1) + g.natDegree*M*M < 2*((A+1)*(B+1)) := by
    have h := hdim_arith q s d A B hs_sq ?_ ?_ ?_ ?_ hs20
    · exact h
    · rw [hA_def]
      have h := Nat.mul_div_le (q - 2*d - 4) 2
      omega
    · rw [hA_def]
      have h := Nat.div_add_mod (q - 2*d - 4) 2
      have hmod : (q - 2*d - 4) % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
      omega
    · rw [hB_def]
      have h := Nat.mul_div_le s 2
      omega
    · rw [hB_def]
      have h := Nat.div_add_mod s 2
      have hmod : s % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
      omega
  have hcount_g : Sg.ncard * M ≤ X :=
    stepanov_count (F := F) hF g hsep hd A B M hAh hBh hMh hdim
  -- the twisted polynomial
  have hαne : α ≠ 0 := fun h => hαnsq (h ▸ IsSquare.zero)
  have hαu : α ^ ((q-1)/2) = -1 := by
    have h1 : quadraticChar F α = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hαnsq
    have h2 : ((quadraticChar F α : ℤ) : F) = α ^ (Fintype.card F / 2) :=
      quadraticChar_eq_pow_of_char_ne_two' hF α
    rw [h1] at h2
    norm_num at h2
    rw [← hq_def, hqdiv] at h2
    exact h2.symm
  have hsep_α : (α • g).Separable := by
    rw [Polynomial.smul_eq_C_mul]
    exact Polynomial.Separable.unit_mul (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hαne)) hsep
  have hndeg : (α • g).natDegree = g.natDegree := by
    rw [Polynomial.smul_eq_C_mul, Polynomial.natDegree_C_mul hαne]
  have hset : ({a : F | (α • g).eval a ^ ((q-1)/2) = 1} : Set F) = Sa := by
    rw [hSa_def]
    ext a
    simp only [Set.mem_setOf_eq]
    have hev : (α • g).eval a = α * g.eval a := by
      rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    rw [hev, mul_pow, hαu]
    constructor
    · intro h
      rw [neg_mul, one_mul] at h
      exact neg_eq_iff_eq_neg.mp h
    · intro h
      rw [h, neg_mul, one_mul, neg_neg]
  have hcount_α : Sa.ncard * M ≤ X := by
    have h := stepanov_count (F := F) hF (α • g) hsep_α (by rw [hndeg]; exact hd) A B M
      (by rw [hndeg]; exact hAh) hBh hMh (by rw [hndeg]; exact hdim)
    rw [hset, hndeg] at h
    exact h
  -- real-valued assembly
  have hMpos : (0:ℝ) < (M:ℝ) := by
    have : (0:ℕ) < M := by omega
    exact_mod_cast this
  have hxR : (Sg.ncard : ℝ) * (M:ℝ) ≤ (X:ℝ) := by exact_mod_cast hcount_g
  have hyR : (Sa.ncard : ℝ) * (M:ℝ) ≤ (X:ℝ) := by exact_mod_cast hcount_α
  have hx : (Sg.ncard : ℝ) ≤ (X:ℝ) / (M:ℝ) := by
    rw [le_div_iff₀ hMpos]; linarith [hxR]
  have hy : (Sa.ncard : ℝ) ≤ (X:ℝ) / (M:ℝ) := by
    rw [le_div_iff₀ hMpos]; linarith [hyR]
  have hxyR : ((q:ℝ) - (d:ℝ)) ≤ (Sg.ncard : ℝ) + (Sa.ncard : ℝ) := by
    have h := Nat.cast_le (α := ℝ).mpr hxynat
    have h1 : ((q - d : ℕ) : ℝ) = (q:ℝ) - (d:ℝ) := by
      rw [Nat.cast_sub (R := ℝ) (by omega : d ≤ q)]
    rw [h1] at h
    push_cast at h
    linarith
  have hZeq : (∑ a : F, quadraticChar F (g.eval a)) = (Sg.ncard : ℤ) - (Sa.ncard : ℤ) := by
    have h := char_sum_eq_ncard_sub hF g
    rw [← hq_def, hqdiv] at h
    exact h
  have hsumR : (∑ a : F, (quadraticChar F (g.eval a) : ℝ))
      = (Sg.ncard : ℝ) - (Sa.ncard : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hZeq
    push_cast at h
    simpa using h
  have hAle : A ≤ q/2 := by rw [hA_def]; exact Nat.div_le_div_right (by omega)
  have hBle : B ≤ s/2 + d + 2 := by rw [hB_def]
  have harith := final_arith q s d A B hq1 hs_sq hq_lt hAle hBle
  have hXc : (X:ℝ) = (A:ℝ) + (q:ℝ)*(B:ℝ) + (((q-1)/2 : ℕ):ℝ)*(d:ℝ) := by
    simp only [hX_def]; push_cast; ring
  have h3 : (2*(X:ℝ) - ((q:ℝ)-(d:ℝ))*(M:ℝ))/(M:ℝ)
      ≤ (17*(d:ℝ)+22)*Real.sqrt (q:ℝ) := by
    have hM_eq : (M:ℝ) = (s:ℝ) := rfl
    rw [hXc, hM_eq]
    exact harith
  have hupper : (Sg.ncard:ℝ) - (Sa.ncard:ℝ) ≤ 2*((X:ℝ)/(M:ℝ)) - (q:ℝ) + (d:ℝ) := by
    linarith [hx, hy, hxyR]
  have hlower : -((Sg.ncard:ℝ) - (Sa.ncard:ℝ)) ≤ 2*((X:ℝ)/(M:ℝ)) - (q:ℝ) + (d:ℝ) := by
    linarith [hx, hy, hxyR]
  have h1 : |(Sg.ncard:ℝ) - (Sa.ncard:ℝ)| ≤ 2*((X:ℝ)/(M:ℝ)) - (q:ℝ) + (d:ℝ) :=
    abs_le.mpr ⟨by linarith [hlower], hupper⟩
  have h2 : 2*((X:ℝ)/(M:ℝ)) - (q:ℝ) + (d:ℝ)
      = (2*(X:ℝ) - ((q:ℝ)-(d:ℝ))*(M:ℝ))/(M:ℝ) := by
    field_simp
    ring
  rw [hsumR]
  calc |(Sg.ncard:ℝ) - (Sa.ncard:ℝ)| ≤ 2*((X:ℝ)/(M:ℝ)) - (q:ℝ) + (d:ℝ) := h1
    _ = (2*(X:ℝ) - ((q:ℝ)-(d:ℝ))*(M:ℝ))/(M:ℝ) := h2
    _ ≤ (17*(d:ℝ)+22)*Real.sqrt (q:ℝ) := h3

theorem stepanov_bound_general :
    ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F], ringChar F ≠ 2 →
      ∀ (g : Polynomial F), g.Separable → 1 ≤ g.natDegree →
      ∀ D : ℕ, g.natDegree ≤ D →
      |∑ a : F, (quadraticChar F (g.eval a) : ℝ)| ≤ C D * Real.sqrt (Fintype.card F) := by
  classical
  refine ⟨fun D => max (17*(D:ℝ) + 22) ((Qnat D : ℕ) : ℝ) + 1, ?_, ?_⟩
  · intro D
    have h1 : (0:ℝ) ≤ max (17*(D:ℝ)+22) ((Qnat D : ℕ) : ℝ) :=
      le_trans (by positivity) (le_max_left _ _)
    linarith
  · intro F _ _ _ hF g hsep hd D hD
    have hQmono : Qnat g.natDegree ≤ Qnat D := by
      simp only [Qnat]
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)) 1000
    by_cases hQ : Qnat g.natDegree ≤ Fintype.card F
    · have h := stepanov_char_sum hF g hsep hd hQ
      have hCD : (17*(g.natDegree:ℝ) + 22) ≤ max (17*(D:ℝ)+22) ((Qnat D : ℕ):ℝ) + 1 := by
        have h1 : (17*(g.natDegree:ℝ)+22) ≤ 17*(D:ℝ)+22 := by
          have h2 : (g.natDegree:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
          linarith
        have h3 : 17*(D:ℝ)+22 ≤ max (17*(D:ℝ)+22) ((Qnat D : ℕ) : ℝ) := le_max_left _ _
        linarith
      calc |∑ a : F, (quadraticChar F (g.eval a) : ℝ)|
          ≤ (17*(g.natDegree:ℝ) + 22) * Real.sqrt (Fintype.card F) := h
        _ ≤ (max (17*(D:ℝ)+22) ((Qnat D : ℕ):ℝ) + 1) * Real.sqrt (Fintype.card F) :=
            mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _)
    · have h := abs_char_sum_le_card (F := F) g
      have hcard : (Fintype.card F : ℝ) < ((Qnat g.natDegree : ℕ) : ℝ) := by
        have h1 : Fintype.card F < Qnat g.natDegree := lt_of_not_ge hQ
        exact_mod_cast h1
      have hQm : ((Qnat g.natDegree : ℕ) : ℝ) ≤ ((Qnat D : ℕ) : ℝ) := by exact_mod_cast hQmono
      have hDmax : ((Qnat D : ℕ) : ℝ) ≤ max (17*(D:ℝ)+22) ((Qnat D : ℕ) : ℝ) + 1 := by
        have h3 : ((Qnat D : ℕ) : ℝ) ≤ max (17*(D:ℝ)+22) ((Qnat D : ℕ) : ℝ) := le_max_right _ _
        linarith
      have hlt : (Fintype.card F : ℝ) < max (17*(D:ℝ)+22) ((Qnat D : ℕ) : ℝ) + 1 := by linarith
      have hsqrt1 : (1:ℝ) ≤ Real.sqrt (Fintype.card F) := by
        apply Real.le_sqrt_of_sq_le
        rw [one_pow]
        have h2 : 1 ≤ Fintype.card F := le_of_lt Fintype.one_lt_card
        exact_mod_cast h2
      have hpos : (0:ℝ) ≤ max (17*(D:ℝ)+22) ((Qnat D : ℕ) : ℝ) + 1 := by
        have h3 : (0:ℝ) ≤ max (17*(D:ℝ)+22) ((Qnat D : ℕ) : ℝ) :=
          le_trans (by positivity) (le_max_left _ _)
        linarith
      calc |∑ a : F, (quadraticChar F (g.eval a) : ℝ)| ≤ (Fintype.card F : ℝ) := h
        _ ≤ (max (17*(D:ℝ)+22) ((Qnat D : ℕ):ℝ) + 1) * Real.sqrt (Fintype.card F) :=
            calc (Fintype.card F : ℝ)
                ≤ max (17*(D:ℝ)+22) ((Qnat D : ℕ):ℝ) + 1 := le_of_lt hlt
              _ = (max (17*(D:ℝ)+22) ((Qnat D : ℕ):ℝ) + 1) * 1 := by ring
              _ ≤ (max (17*(D:ℝ)+22) ((Qnat D : ℕ):ℝ) + 1) * Real.sqrt (Fintype.card F) :=
                  mul_le_mul_of_nonneg_left hsqrt1 hpos

end
end Commons.NumberTheory.Stepanov