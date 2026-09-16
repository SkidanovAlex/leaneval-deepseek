import Submission.ZagierHoffmanProof.StepK11

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Level-2 monic parametrization

`HeadD F 2 ≃ F × F`: monic quadratic `X² + a·X + b ↤ (a,b)`.  Together with the
substituted level-1 identity this is the engine of the elementary `EvalStep F 2` proof
(PLAN SESSION 145).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `X² + a·X + b` is monic of degree two. -/
lemma quad_monic_natDegree (a b : F) :
    (X^2 + C a * X + C b : F[X]).Monic ∧ (X^2 + C a * X + C b : F[X]).natDegree = 2 := by
  classical
  let p : F[X] := X^2 + C a * X + C b
  have hdeg_le : p.natDegree ≤ 2 := by
    dsimp [p]
    have h2 : (C a * X : F[X]).natDegree ≤ 1 := by
      by_cases ha : a = 0
      · simp [ha]
      · have hn := Polynomial.natDegree_C_mul_X a ha
        rw [hn]
    have hsum1 : (X^2 + C a * X : F[X]).natDegree ≤ 2 := by
      have h1 : (X^2 : F[X]).natDegree = 2 := by exact Polynomial.natDegree_X_pow 2
      calc
        (X^2 + C a * X : F[X]).natDegree ≤ max (X^2 : F[X]).natDegree (C a * X : F[X]).natDegree :=
              Polynomial.natDegree_add_le _ _
        _ ≤ 2 := by omega
    calc
      (X^2 + C a * X + C b : F[X]).natDegree
          ≤ max ((X^2 + C a * X : F[X]).natDegree) ((C b : F[X]).natDegree) :=
            Polynomial.natDegree_add_le _ _
      _ ≤ 2 := by
            have h4 : (C b : F[X]).natDegree ≤ 2 := by simp
            omega
  have hc2 : p.coeff 2 = 1 := by
    dsimp [p]
    have h1 : (X^2 : F[X]).coeff 2 = 1 := by
      simp [Polynomial.coeff_X_pow 2 2]
    have h2 : (C a * X : F[X]).coeff 2 = 0 := by
      simp [Polynomial.coeff_C_mul_X a 2]
    have h3 : (C b : F[X]).coeff 2 = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simp)
    rw [Polynomial.coeff_add, Polynomial.coeff_add, h1, h2, h3]
    simp
  have hdeg : p.natDegree = 2 := by
    apply le_antisymm hdeg_le
    by_contra h
    have hlt : p.natDegree < 2 := by omega
    have h0 : p.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [hc2] at h0
    exact (one_ne_zero : (1 : F) ≠ 0) h0
  have hmon : p.Monic := by
    change p.leadingCoeff = 1
    rw [show p.leadingCoeff = p.coeff p.natDegree by rfl]
    rw [hdeg, hc2]
  exact ⟨hmon, hdeg⟩

/-- Every monic polynomial of natural degree two is `X² + a·X + b`. -/
lemma monic_deg_two_eq_X_sq_add (p : F[X]) (hp : p.Monic) (hdeg : p.natDegree = 2) :
    p = X^2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp
  · by_cases hk1 : k = 1
    · subst k
      simp [Polynomial.coeff_C_mul_X]
    · by_cases hk2 : k = 2
      · subst k
        have hc2 : p.coeff 2 = 1 := by
          simpa [hdeg] using hp.coeff_natDegree
        have h1 : (X^2 : F[X]).coeff 2 = 1 := by
          simp [Polynomial.coeff_X_pow 2 2]
        have h2 : (C (p.coeff 1) * X : F[X]).coeff 2 = 0 := by
          simp [Polynomial.coeff_C_mul_X]
        have h3 : (C (p.coeff 0) : F[X]).coeff 2 = 0 := by
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simp)
        rw [Polynomial.coeff_add, Polynomial.coeff_add, h1, h2, h3, hc2]
        simp
      · -- k ≥ 3
        have hbig : 2 < k := by omega
        have hpk : p.coeff k = 0 := by
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have h1 : (X^2 : F[X]).coeff k = 0 := by
          rw [Polynomial.coeff_X_pow 2 k]
          simp [hk2]
        have h2 : (C (p.coeff 1) * X : F[X]).coeff k = 0 := by
          rw [Polynomial.coeff_C_mul_X]
          simp [hk1]
        have h3 : (C (p.coeff 0) : F[X]).coeff k = 0 := by
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
            have hc : (C (p.coeff 0) : F[X]).natDegree = 0 := by simp
            omega)
        rw [Polynomial.coeff_add, Polynomial.coeff_add, h1, h2, h3, hpk]
        simp

/-- The monic quadratic `X² + a·X + b`. -/
noncomputable def headTwo (a b : F) : HeadD F 2 :=
  ⟨X^2 + C a * X + C b, quad_monic_natDegree F a b⟩

/-- The linear coefficients of a monic quadratic. -/
def headTwoCoeffs (p : HeadD F 2) : F × F := (p.1.coeff 1, p.1.coeff 0)

/-- Monic quadratics over `F` are exactly `X² + a·X + b`, `(a,b) : F × F`. -/
noncomputable def headD_two_equiv_F : HeadD F 2 ≃ (F × F) where
  toFun := headTwoCoeffs F
  invFun := fun ab => headTwo F ab.1 ab.2
  left_inv := by
    intro p
    apply Subtype.ext
    exact (monic_deg_two_eq_X_sq_add F p.1 p.2.1 p.2.2).symm
  right_inv := by
    intro ab
    dsimp [headTwoCoeffs, headTwo]
    simp

/-- `Hsum F 2 1` is the sum over the linear coefficients of the inverses of the monic
quadratics. -/
lemma Hsum_two_eq_sum_quad :
    letI : Fintype F := Fintype.ofFinite F
    Hsum F 2 1 = ∑ ab : F × F,
      (((X^2 + C ab.1 * X + C ab.2 : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  dsimp [Hsum]
  apply Fintype.sum_equiv (headD_two_equiv_F F)
  intro p
  have hx : p.1 = X^2 + C (p.1.coeff 1) * X + C (p.1.coeff 0) := by
    exact monic_deg_two_eq_X_sq_add F p.1 p.2.1 p.2.2
  rw [hx]
  simp [pow_one, headD_two_equiv_F, headTwoCoeffs]


/-- `∏_c (Z + Cc) = Z^q − Z`: the Carlitz product, substituted. -/
lemma carlitzOne_subst (Z : F[X]) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∏ c : F, (Z + C c : F[X])) = Z ^ (Nat.card F) - Z := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  have h := carlitzOne_eq_prod_X_add_C F
  dsimp [carlitzOne] at h
  have hc := congrArg (fun p : F[X] => p.comp Z) h
  rw [Polynomial.prod_comp] at hc
  symm at hc
  simpa using hc

/-- `∏_{b ≠ c}(Z + Cb) = (qPoly c).comp Z`: qPoly substituted. -/
lemma qPoly_subst (c : F) (Z : F[X]) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    ∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X]) = (qPoly F c).comp Z := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  have hc := congrArg (fun p : F[X] => p.comp Z) (by
    change (qPoly F c) = ∏ b ∈ (Finset.univ : Finset F).erase c, (X + C b : F[X])
    rfl)
  rw [Polynomial.prod_comp] at hc
  simpa using hc.symm

/-- `Σ_c ∏_{b≠c}(Z + Cb) = −1`: the A₁ = −1 identity, substituted. -/
lemma Aone_subst (Z : F[X]) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ c : F, ∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X])) = -1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  have h := A_one_eq_neg_one F
  have hc := congrArg (fun p : F[X] => p.comp Z) h
  dsimp [A] at hc
  rw [Polynomial.sum_comp] at hc
  have hstep : ∀ c : F, ((qPoly F c ^ 1 : F[X]).comp Z) =
      ∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X]) := by
    intro c
    rw [pow_one]
    exact (qPoly_subst F c Z).symm
  rw [Finset.sum_congr rfl (by intro c hc2; exact hstep c)] at hc
  simpa using hc
/-- The quadratic factor and the complementary product multiply to the full product. -/
lemma Z_add_C_erase_mul (Z : F[X]) (c : F) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (Z + C c : F[X]) * (∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X])) =
      ∏ b : F, (Z + C b : F[X]) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  exact Finset.mul_prod_erase (s := (Finset.univ : Finset F))
    (f := fun b : F => (Z + C b : F[X])) (a := c) (by simp)

/-- A monic-linear factor `Z + C c` is invertible in `RatFunc F` for nonconstant `Z`. -/
lemma Z_add_C_ne_zero (Z : F[X]) (hZ : Z.natDegree ≠ 0) (c : F) :
    (Z + C c : F[X]) ≠ 0 := by
  intro hz
  have hZc : Z = -C c := by
    calc
      Z = (Z + C c) - C c := by ring
      _ = -C c := by rw [hz]; simp
  have : Z.natDegree = 0 := by
    rw [hZc]
    simp
  omega

/-- `(Z+Cc)^{-1} = (∏_{b≠c}(Z+Cb))·(∏_b(Z+Cb))^{-1}` in `RatFunc F`. -/
lemma Z_add_C_inv_eq (Z : F[X]) (hZ : Z.natDegree ≠ 0) (c : F) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (((Z + C c : F[X]) : RatFunc F)⁻¹) =
      (((∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X])) : F[X]) : RatFunc F) *
        (((∏ b : F, (Z + C b : F[X])) : F[X]) : RatFunc F)⁻¹ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  have hfac := congrArg (algebraMap (F[X]) (RatFunc F)) (Z_add_C_erase_mul F Z c)
  have hfacC : (((Z + C c : F[X]) : F[X]) : RatFunc F) *
      (((∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X])) : F[X]) : RatFunc F) =
      (((∏ b : F, (Z + C b : F[X])) : F[X]) : RatFunc F) := by
    simpa [map_mul] using hfac
  have hZc : (Z + C c : F[X]) ≠ 0 := Z_add_C_ne_zero F Z hZ c
  have hZc0 : (((Z + C c : F[X]) : F[X]) : RatFunc F) ≠ 0 := by
    intro hz
    exact hZc (RatFunc.algebraMap_injective F (by simpa using hz))
  have hP : (∏ b : F, (Z + C b : F[X])) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    exact Z_add_C_ne_zero F Z hZ b
  have hP0 : (((∏ b : F, (Z + C b : F[X])) : F[X]) : RatFunc F) ≠ 0 := by
    intro hz
    exact hP (RatFunc.algebraMap_injective F (by simpa using hz))
  field_simp [hZc0, hP0]
  exact hfacC.symm


/-- `Σ_c (Z+Cc)^{-1} = (Z−Z^q)^{-1}` in `RatFunc F`, for nonconstant `Z`. -/
lemma Hsum_one_subst (Z : F[X]) (hZ : Z.natDegree ≠ 0) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ c : F, (((Z + C c : F[X]) : RatFunc F)⁻¹)) =
      (((Z - Z ^ (Nat.card F) : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  have hprod : (∏ b : F, (Z + C b : F[X])) = Z ^ (Nat.card F) - Z := carlitzOne_subst F Z
  have hA : (∑ c : F, ∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X])) = -1 :=
    Aone_subst F Z
  have hP : (∏ b : F, (Z + C b : F[X])) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    exact Z_add_C_ne_zero F Z hZ b
  have hP0 : (((∏ b : F, (Z + C b : F[X])) : F[X]) : RatFunc F) ≠ 0 := by
    intro hz
    exact hP (RatFunc.algebraMap_injective F (by simpa using hz))
  calc
    (∑ c : F, (((Z + C c : F[X]) : RatFunc F)⁻¹))
        = ∑ c : F, ((((∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X])) : F[X]) : RatFunc F) *
            (((∏ b : F, (Z + C b : F[X])) : F[X]) : RatFunc F)⁻¹) := by
          apply Finset.sum_congr rfl
          intro c hc
          exact Z_add_C_inv_eq F Z hZ c
    _ = (∑ c : F, (((∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X])) : F[X]) : RatFunc F)) *
        (((∏ b : F, (Z + C b : F[X])) : F[X]) : RatFunc F)⁻¹ := by
          rw [Finset.sum_mul]
    _ = (((∏ b : F, (Z + C b : F[X])) : F[X]) : RatFunc F)⁻¹ *
          (((∑ c : F, ∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X])) : F[X]) : RatFunc F) := by
          rw [mul_comm]
          congr 1
          exact (map_sum (algebraMap (F[X]) (RatFunc F)) (fun c : F =>
            (∏ b ∈ (Finset.univ : Finset F).erase c, (Z + C b : F[X]))) (Finset.univ : Finset F)).symm
    _ = (((∏ b : F, (Z + C b : F[X])) : F[X]) : RatFunc F)⁻¹ * (((-1 : F[X]) : F[X]) : RatFunc F) := by
          rw [hA]
    _ = (((Z - Z ^ (Nat.card F) : F[X]) : RatFunc F)⁻¹) := by
          have hPneg : (Z ^ (Nat.card F) - Z : F[X]) = -(Z - Z ^ (Nat.card F)) := by ring
          have hA0 : ((Z - Z ^ (Nat.card F) : F[X]) : RatFunc F) ≠ 0 := by
            intro hz
            have hz' : (Z - Z ^ (Nat.card F) : F[X]) = 0 :=
              RatFunc.algebraMap_injective F (by simpa using hz)
            have h0 : (∏ b : F, (Z + C b : F[X])) = 0 := by
              rw [hprod, hPneg, hz']
              ring
            exact hP h0
          -- (∏b(Z+Cb)) = Z^q−Z = −(Z−Z^q) ; so P⁻¹·(−1) = (Z−Z^q)⁻¹
          rw [hprod]
          have hnegP : ((Z ^ (Nat.card F) - Z : F[X]) : RatFunc F) =
              -(((Z - Z ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F) := by
            exact (congrArg (algebraMap (F[X]) (RatFunc F)) hPneg).trans
              (map_neg (algebraMap (F[X]) (RatFunc F)) (Z - Z ^ (Nat.card F) : F[X]))
          rw [hnegP]
          have hm1 : (((-1 : F[X]) : F[X]) : RatFunc F) = -1 := by simp
          rw [hm1]
          field_simp [hA0] <;> ring


lemma add_pow_card (p q : F[X]) :
    (p + q) ^ (Nat.card F) = p ^ (Nat.card F) + q ^ (Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F (ringChar F) := ringChar.charP F
  rcases FiniteField.card (K := F) (p := ringChar F) with ⟨n, hprime, hcard⟩
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  have hcard' : Nat.card F = (ringChar F) ^ (n : ℕ) := by
    rw [← Fintype.card_eq_nat_card]
    exact hcard
  haveI : CharP (F[X]) (ringChar F) := by
    refine charP_of_injective_algebraMap (R := F) (A := F[X]) ?_ (ringChar F)
    intro a b h
    exact Polynomial.C_injective h
  rw [hcard']
  exact add_pow_char_pow p q (ringChar F) (n : ℕ)

/-- `γ^|F| = γ` for `γ : F`. -/
lemma pow_card_eq_self (γ : F) : γ ^ (Nat.card F) = γ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [← Fintype.card_eq_nat_card]
  exact FiniteField.pow_card (K := F) γ

/-- `(X²+uX) − (X²+uX)^q = (X−X^q)(X+X^q+u)` in `F[X]` (Frobenius + u^q = u). -/
lemma D_u_factor (u : F) :
    (X^2 + C u * X : F[X]) - (X^2 + C u * X) ^ (Nat.card F) =
      (X - X ^ (Nat.card F)) * (X + X ^ (Nat.card F) + C u) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hf := add_pow_card F (X^2 : F[X]) (C u * X)
  have hsq : (X^2 : F[X]) ^ (Nat.card F) = (X ^ (Nat.card F)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    exact Nat.mul_comm 2 (Nat.card F)
  have hcu : (C u * X : F[X]) ^ (Nat.card F) = C u * X ^ (Nat.card F) := by
    calc
      (C u * X : F[X]) ^ (Nat.card F) = (C u) ^ (Nat.card F) * X ^ (Nat.card F) := by
            rw [mul_pow]
      _ = C (u ^ (Nat.card F)) * X ^ (Nat.card F) := by
            congr 1
            exact (map_pow C u (Nat.card F)).symm
      _ = C u * X ^ (Nat.card F) := by
            congr 1
            rw [pow_card_eq_self F u]
  have hmain : (X^2 + C u * X : F[X]) - (((X ^ (Nat.card F)) ^ 2) + C u * (X ^ (Nat.card F))) =
      (X - X ^ (Nat.card F)) * (X + X ^ (Nat.card F) + C u) := by
    let Xq : F[X] := X ^ (Nat.card F)
    change (X^2 + C u * X) - (Xq ^ 2 + C u * Xq) = (X - Xq) * (X + Xq + C u)
    ring
  rw [hf, hsq, hcu]
  exact hmain


/-- `X² + uX` has degree two. -/
lemma quad1_natDegree (u : F) : (X^2 + C u * X : F[X]).natDegree = 2 := by
  have hq := quad_monic_natDegree F u (0 : F)
  have hc0 : (C (0 : F) : F[X]) = 0 := by simp
  simpa [hc0, add_zero] using hq.2
/-- `X + X^q` has degree `q` (hence is nonconstant). -/
lemma X_add_Xq_natDegree : (X + X ^ (Nat.card F) : F[X]).natDegree = Nat.card F := by
  classical
  have hlt : (X : F[X]).natDegree < (X ^ (Nat.card F) : F[X]).natDegree := by
    have hq : 2 ≤ Nat.card F := card_ge_two F
    have hX : (X : F[X]).natDegree = 1 := by exact Polynomial.natDegree_X (R := F)
    have hXq : (X ^ (Nat.card F) : F[X]).natDegree = Nat.card F := by
      exact Polynomial.natDegree_X_pow (Nat.card F)
    omega
  have hXq : (X ^ (Nat.card F) : F[X]).natDegree = Nat.card F := by
    exact Polynomial.natDegree_X_pow (Nat.card F)
  exact (Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt).trans hXq
/-- non-constancy of `X²+uX` for the substitution lemma. -/
lemma quad1_nonconst (u : F) : (X^2 + C u * X : F[X]).natDegree ≠ 0 := by
  rw [quad1_natDegree F u]
  norm_num
/-- non-constancy of `X+X^q`. -/
lemma X_add_Xq_nonconst : (X + X ^ (Nat.card F) : F[X]).natDegree ≠ 0 := by
  rw [X_add_Xq_natDegree F]
  have hq : 2 ≤ Nat.card F := card_ge_two F
  omega


/-- `Hsum F 2 1 = Σ_u Σ_v (X²+uX+v)⁻¹` (nested form). -/
lemma Hsum_two_nested :
    letI : Fintype F := Fintype.ofFinite F
    Hsum F 2 1 = ∑ u : F, ∑ v : F,
      (((X^2 + C u * X + C v : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [Hsum_two_eq_sum_quad F]
  rw [Fintype.sum_prod_type (fun ab : F × F =>
      (((X^2 + C ab.1 * X + C ab.2 : F[X]) : RatFunc F)⁻¹))]

/-- per-`u`, the inner `v`-sum collapses: `Σ_v (X²+uX+v)⁻¹ = D_u⁻¹` (RatFunc). -/
lemma Hsum_two_vcollapse (u : F) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ v : F, (((X^2 + C u * X + C v : F[X]) : RatFunc F)⁻¹)) =
      ((((X^2 + C u * X) - (X^2 + C u * X) ^ (Nat.card F) : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  have h := Hsum_one_subst F (X^2 + C u * X : F[X]) (quad1_nonconst F u)
  simpa using h



/-- `X − X^q ≠ 0` in `F[X]`. -/
lemma A_poly_ne_zero : (X - X ^ (Nat.card F) : F[X]) ≠ 0 := by
  intro hz
  have hsub : (X : F[X]) = X ^ (Nat.card F) := sub_eq_zero.mp hz
  have hX : (X : F[X]).natDegree = 1 := by exact Polynomial.natDegree_X (R := F)
  have hXq : (X ^ (Nat.card F) : F[X]).natDegree = Nat.card F := by
    exact Polynomial.natDegree_X_pow (Nat.card F)
  have hc := congrArg Polynomial.natDegree hsub
  rw [hX, hXq] at hc
  have hq : 2 ≤ Nat.card F := card_ge_two F
  omega

/-- `X − X^{q²} ≠ 0` in `F[X]`. -/
lemma F0_poly_ne_zero : (X - X ^ ((Nat.card F) ^ 2) : F[X]) ≠ 0 := by
  intro hz
  have hsub : (X : F[X]) = X ^ ((Nat.card F) ^ 2) := sub_eq_zero.mp hz
  have hX : (X : F[X]).natDegree = 1 := by exact Polynomial.natDegree_X (R := F)
  have hXq : (X ^ ((Nat.card F) ^ 2) : F[X]).natDegree = (Nat.card F) ^ 2 := by
    exact Polynomial.natDegree_X_pow ((Nat.card F) ^ 2)
  have hc := congrArg Polynomial.natDegree hsub
  rw [hX, hXq] at hc
  have hq : 2 ≤ Nat.card F := card_ge_two F
  nlinarith

/-- `X + X^q + u ≠ 0` in `F[X]`. -/
lemma B_poly_ne_zero (u : F) : (X + X ^ (Nat.card F) + C u : F[X]) ≠ 0 := by
  intro hz
  have hsub : (X ^ (Nat.card F) : F[X]) = -(X + C u) := by
    linear_combination hz
  have hXq : (X ^ (Nat.card F) : F[X]).natDegree = Nat.card F := by
    exact Polynomial.natDegree_X_pow (Nat.card F)
  have hb : (X + C u : F[X]).natDegree ≤ 1 := by
    have hX : (X : F[X]).natDegree = 1 := by exact Polynomial.natDegree_X (R := F)
    have hCu : (C u : F[X]).natDegree = 0 := by simp
    calc
      (X + C u : F[X]).natDegree ≤ max X.natDegree (C u).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by omega
  have hc := congrArg Polynomial.natDegree hsub
  rw [hXq, Polynomial.natDegree_neg] at hc
  have hq : 2 ≤ Nat.card F := card_ge_two F
  omega

/-- `Hsum F 1 1 = (X−X^q)⁻¹`. -/
lemma U1_eq_A_inv :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    Hsum F 1 1 = (((X - X ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  rw [Hsum_one_eq_sum_inv F]
  have h := Hsum_one_subst F (X : F[X]) (by
    have hX : (X : F[X]).natDegree = 1 := by exact Polynomial.natDegree_X (R := F)
    rw [hX]
    norm_num)
  simpa using h


lemma EvalStep_two : EvalStep F 2 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  dsimp [EvalStep]
  have hU1 := U1_eq_A_inv F
  let Acast : RatFunc F := (((X - X ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)
  let F0c : RatFunc F := (((X - X ^ ((Nat.card F) ^ 2) : F[X]) : F[X]) : RatFunc F)
  let Bcast (u : F) : RatFunc F := (((X + X ^ (Nat.card F) + C u : F[X]) : F[X]) : RatFunc F)
  let Dcast (u : F) : RatFunc F := ((((X^2 + C u * X) - (X^2 + C u * X) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)
  have hA0 : Acast ≠ 0 := by
    dsimp [Acast]
    intro hz
    exact A_poly_ne_zero F (RatFunc.algebraMap_injective F (by simpa using hz))
  have hF00 : F0c ≠ 0 := by
    dsimp [F0c]
    intro hz
    exact F0_poly_ne_zero F (RatFunc.algebraMap_injective F (by simpa using hz))
  have hB0 (u : F) : Bcast u ≠ 0 := by
    dsimp [Bcast]
    intro hz
    exact B_poly_ne_zero F u (RatFunc.algebraMap_injective F (by simpa using hz))
  have hperu (u : F) : (Dcast u)⁻¹ * F0c = (Acast⁻¹ * F0c) * (Bcast u)⁻¹ := by
    have hDu := congrArg (algebraMap (F[X]) (RatFunc F)) (D_u_factor F u)
    have hDuC : Dcast u = Acast * Bcast u := by
      dsimp [Dcast, Acast, Bcast]
      simpa [map_mul] using hDu
    field_simp [hDuC, hA0, hB0 u, hF00]
    exact hDuC.symm
  have hZ2 : (∑ u : F, (Bcast u)⁻¹) = F0c⁻¹ := by
    have h := Hsum_one_subst F (X + X ^ (Nat.card F) : F[X]) (X_add_Xq_nonconst F)
    have hf := add_pow_card F (X : F[X]) (X ^ (Nat.card F) : F[X])
    have hqq : (X ^ (Nat.card F) : F[X]) ^ (Nat.card F) = X ^ ((Nat.card F) ^ 2) := by
      calc
        (X ^ (Nat.card F) : F[X]) ^ (Nat.card F) = X ^ ((Nat.card F) * (Nat.card F)) := by
              exact (pow_mul X (Nat.card F) (Nat.card F)).symm
        _ = X ^ ((Nat.card F) ^ 2) := by
              congr 1
              exact (pow_two (Nat.card F)).symm
    have hpoly : ((X + X ^ (Nat.card F) : F[X]) - (X + X ^ (Nat.card F)) ^ (Nat.card F)) =
        (X - X ^ ((Nat.card F) ^ 2) : F[X]) := by
      calc
        (X + X ^ (Nat.card F)) - (X + X ^ (Nat.card F)) ^ (Nat.card F)
            = (X + X ^ (Nat.card F)) - (X ^ (Nat.card F) + (X ^ (Nat.card F)) ^ (Nat.card F)) := by rw [hf]
        _ = X - X ^ ((Nat.card F) ^ 2) := by
              rw [hqq]
              ring
    rw [hpoly] at h
    simpa [Bcast, F0c] using h
  have h1 : (∑ u : F, (∑ v : F, (((X^2 + C u * X + C v : F[X]) : F[X]) : RatFunc F)⁻¹)) * F0c
      = (∑ u : F, (Dcast u)⁻¹ * F0c) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    rw [Hsum_two_vcollapse F u]
  have h2 : (∑ u : F, (Dcast u)⁻¹ * F0c) = (∑ u : F, (Acast⁻¹ * F0c) * (Bcast u)⁻¹) := by
    apply Finset.sum_congr rfl
    intro u _
    exact hperu u
  have h3 : (∑ u : F, (Acast⁻¹ * F0c) * (Bcast u)⁻¹) = (Acast⁻¹ * F0c) * (∑ u : F, (Bcast u)⁻¹) := by
    rw [← Finset.mul_sum]
  have h4 : (Acast⁻¹ * F0c) * (∑ u : F, (Bcast u)⁻¹) = (Acast⁻¹ * F0c) * F0c⁻¹ := by
    rw [hZ2]
  have h5 : (Acast⁻¹ * F0c) * F0c⁻¹ = Acast⁻¹ := by
    field_simp [hF00]
  rw [hU1]
  rw [Hsum_two_nested F]
  change (∑ u : F, (∑ v : F, (((X^2 + C u * X + C v : F[X]) : F[X]) : RatFunc F)⁻¹)) * F0c = Acast⁻¹
  rw [h1, h2, h3, h4, h5]


