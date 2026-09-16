import Mathlib.FieldTheory.Finite.Basic
import Submission.ZagierHoffmanProof.Linear

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Every monic polynomial of natural degree one is of the form `X + C c`. -/
lemma monic_deg_one_eq_X_add_C (p : F[X]) (hp : p.Monic) (hdeg : p.natDegree = 1) :
    p = Polynomial.X + Polynomial.C (p.coeff 0) := by
  have h := Polynomial.eq_X_add_C_of_degree_le_one (R := F) (p := p)
  have hpne : p ≠ 0 := by
    intro hpz
    have : p.natDegree = 0 := by simp [hpz]
    omega
  have hdeg1 : p.degree ≤ 1 := by
    rw [Polynomial.degree_eq_natDegree hpne]
    norm_num [hdeg]
  rw [h hdeg1]
  have hc1 : p.coeff 1 = 1 := by
    simpa [hdeg] using hp.coeff_natDegree
  rw [hc1]
  simp

/-- The monic degree-one polynomial `X + C c`. -/
noncomputable def headOne (c : F) : HeadD F 1 :=
  ⟨X + C c, by
    constructor
    · have hm : (X ^ 1 + C c : F[X]).Monic :=
        Polynomial.monic_X_pow_add_C c (by omega)
      simpa using hm
    · have hd : (X ^ 1 + C c : F[X]).natDegree = 1 :=
        Polynomial.natDegree_X_pow_add_C (n := 1) (r := c)
      simpa using hd⟩

/-- The constant term of a monic degree-one polynomial. -/
def headOneConst (p : HeadD F 1) : F := p.1.coeff 0

/-- Monic degree-one polynomials over `F` are exactly `X + C c`, `c : F`. -/
noncomputable def headD_one_equiv_F : HeadD F 1 ≃ F where
  toFun := headOneConst F
  invFun := headOne F
  left_inv := by
    intro p
    apply Subtype.ext
    exact (monic_deg_one_eq_X_add_C F p.1 p.2.1 p.2.2).symm
  right_inv := by
    intro c
    dsimp [headOneConst, headOne]
    simp

/-- `P F 1 n` is the sum of the inverses of the monic degree-one polynomials:
`∑ c : F, (X + C c)^{-n}`. -/
lemma P_one_eq_sum_translate (n : ℕ+) :
    letI : Fintype F := Fintype.ofFinite F
    P F 1 n = ∑ c : F,
      ((((X + C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n : ℕ))⁻¹ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let e : HeadD F 1 ≃ F := headD_one_equiv_F F
  rw [P_eq_sum F 1 n]
  apply Fintype.sum_equiv e
  intro p
  congr 1
  have hx : p.1 = X + C (e p) := by
    dsimp [e, headD_one_equiv_F, headOneConst, headOne]
    exact monic_deg_one_eq_X_add_C F p.1 p.2.1 p.2.2
  rw [hx]

/-- `X ^ q - X` factors as the product of the linear polynomials `X - C c`
(`q = Nat.card F`). -/
lemma X_pow_card_sub_X_eq_prod_X_sub_C :
    letI : Fintype F := Fintype.ofFinite F
    (X ^ (Nat.card F) - X : F[X]) = ∏ c : F, (X - C c) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Nat.card F := Fintype.card_eq_nat_card
  let p : F[X] := X ^ Fintype.card F - X
  have hdeg : p.natDegree = Fintype.card F := by
    dsimp [p]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card
  have hroots : p.roots = (Finset.univ : Finset F).val := by
    dsimp [p]
    exact FiniteField.roots_X_pow_card_sub_X F
  have hcardroots : p.roots.card = p.natDegree := by
    rw [hroots]
    simp [hdeg]
  have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) hcardroots
  have hq : 2 ≤ Fintype.card F := by
    exact Fintype.one_lt_card
  have hlc : p.leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff, hdeg]
    dsimp [p]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    have h1 : 1 ≠ Fintype.card F := by omega
    simp [h1]
  rw [hlc] at hprod
  have hprod' : p = (Multiset.map (fun a : F => X - C a) p.roots).prod := by
    simpa using hprod.symm
  dsimp [p] at hprod'
  rw [hroots] at hprod'
  rw [hcard] at hprod'
  have hfin : (∏ c : F, (X - C c)) =
      (Multiset.map (fun a : F => X - C a) (Finset.univ : Finset F).val).prod := by
    exact (Finset.prod_eq_multiset_prod (Finset.univ : Finset F) (fun a : F => X - C a)).symm
  rw [hfin]
  exact hprod'

/-- The polynomial `[1] := X ^ q - X` (`q = |F|`), the product of all monic linear
polynomials. -/
noncomputable def carlitzOne : F[X] := X ^ (Nat.card F) - X

/-- `[1] = X ^ q - X` is the product of all `X + C c` as `c` runs over `F`. -/
lemma carlitzOne_eq_prod_X_add_C :
    letI : Fintype F := Fintype.ofFinite F
    carlitzOne F = ∏ c : F, (X + C c) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := X_pow_card_sub_X_eq_prod_X_sub_C F
  -- ∏ c, (X + C c) = ∏ c, (X - C c)  (reindex c ↦ -c)
  have hneg : (∏ c : F, (X + C c)) = ∏ c : F, (X - C c) := by
    -- X + C c = X - C (-c); negation permutes F
    let e : F ≃ F := Equiv.neg F
    calc
      (∏ c : F, (X + C c)) = ∏ c : F, (X - C (-c)) := by
        apply Finset.prod_congr rfl
        intro c hc
        simp
      _ = ∏ c : F, (X - C c) := by
        exact Finset.prod_bij (fun a ha => -a) (by intro a ha; exact Finset.mem_univ _)
          (by intro a ha b hb h; exact neg_injective h) (by intro b hb; refine ⟨-b, Finset.mem_univ _, by simp⟩)
          (by intro a ha; rfl)
  rw [carlitzOne]
  rw [hneg]
  exact h

/-- `Q_c := ∏_{b ≠ c} (X + C b)` (the product of all monic linear factors except one). -/
noncomputable def qPoly (c : F) : F[X] := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  exact ∏ b ∈ (Finset.univ : Finset F).erase c, (X + C b)

/-- `[1] = (X + C c) · Q_c` for every `c`. -/
lemma carlitzOne_eq_mul_qPoly (c : F) :
    carlitzOne F = (X + C c) * qPoly F c := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    carlitzOne F = ∏ b : F, (X + C b) := carlitzOne_eq_prod_X_add_C F
    _ = (X + C c) * ∏ b ∈ (Finset.univ : Finset F).erase c, (X + C b) := by
        exact (Finset.mul_prod_erase (Finset.univ : Finset F) (fun b : F => X + C b)
          (Finset.mem_univ c)).symm
    _ = (X + C c) * qPoly F c := by
        rfl

/-- `A_n := ∑ c : F, Q_c ^ n ∈ F[X]`. -/
noncomputable def A (n : ℕ) : F[X] := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  exact ∑ c : F, (qPoly F c) ^ n

end ZagierHoffmanPositiveChar
