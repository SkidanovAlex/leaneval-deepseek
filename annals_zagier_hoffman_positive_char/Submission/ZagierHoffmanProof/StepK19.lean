import Submission.ZagierHoffmanProof.StepK18

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K19: the monic degree-`d` coefficient parametrisation and the tuple `Hsum`

`HeadD F d ≃ (Fin d → F)` (`headD_degree_equiv`): a monic polynomial of natural
degree `d` is `X^d + Σ_{j<d} a_j·X^j`, `a_j := p.coeff j` (coefficient recovery
`monicPd_coeff_recover` via polynomial extensionality; per-coefficient recovery
`monicPd_coeff_lt` below the leading degree).  Hence `Hsum F d 1` is the sum over the
coefficient tuples of the inverses of the monic polynomials (`Hsum_tuple`).  This is
the base of the nested `stage_step` collapse that yields `EvalStep`/`EvalU ∀d`
(PLAN SESSION 152/153).  All lemmas here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]



/-- coefficient recovery below the leading degree. -/
lemma monicPd_coeff_lt (d : ℕ) (a : Fin d → F) (j : Fin d) :
    (monicPd F d a).coeff (j : ℕ) = a j := by
  classical
  dsimp [monicPd]
  rw [Polynomial.coeff_add]
  have h1 : (X ^ d : F[X]).coeff (j : ℕ) = 0 := by
    rw [Polynomial.coeff_X_pow d (j : ℕ), if_neg]
    exact (by omega : (j : ℕ) ≠ d)
  have h2 : (∑ jj : Fin d, C (a jj) * X ^ (jj : ℕ)).coeff (j : ℕ) = a j := by
    simp [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      have hne : (j : ℕ) ≠ (b : ℕ) := by
        intro hcon
        exact hbj (Fin.ext hcon.symm)
      rw [if_neg hne]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  rw [h1, h2]
  simp

/-- `monicPd` recovers a monic polynomial from its coefficients (coefficient
extensionality, no range-bridge needed). -/
lemma monicPd_coeff_recover (d : ℕ) (p : F[X]) (hp : p.Monic) (hd : p.natDegree = d) :
    monicPd F d (fun j : Fin d => p.coeff (j : ℕ)) = p := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < d
  · rw [monicPd_coeff_lt F d (fun j : Fin d => p.coeff (j : ℕ)) ⟨k, hk⟩]
  · have hdk : d < k ∨ d = k := lt_or_eq_of_le (by omega)
    rcases hdk with hdk | hdk
    · rw [monicPd_coeff_gt F d (fun j : Fin d => p.coeff (j : ℕ)) k hdk]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; omega)).symm
    · have hk' : k = d := hdk.symm
      subst k
      rw [monicPd_coeff_d F d (fun j : Fin d => p.coeff (j : ℕ))]
      have hlc : p.coeff d = p.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hd]
      exact (hlc.trans hp).symm

/-- ★ monic degree-`d` polynomials are exactly the coefficient tuples `Fin d → F`. -/
noncomputable def headD_degree_equiv (d : ℕ) : HeadD F d ≃ (Fin d → F) where
  toFun := fun p j => p.1.coeff (j : ℕ)
  invFun := fun a => ⟨monicPd F d a, monicPd_monic F d a, monicPd_natDegree F d a⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact monicPd_coeff_recover F d p.1 p.2.1 p.2.2
  right_inv := by
    intro a
    funext j
    exact monicPd_coeff_lt F d a j

/-- ★ `Hsum F d 1` as the sum over the coefficient tuples of the monic polynomials. -/
lemma Hsum_tuple (d : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    Hsum F d 1 = ∑ a : Fin d → F,
      ((((monicPd F d a : F[X]) : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  dsimp [Hsum]
  let e : HeadD F d ≃ (Fin d → F) := headD_degree_equiv F d
  rw [Fintype.sum_equiv e]
  intro p
  -- goal: ((p.1 cast)^1)⁻¹ = ((monicPd d (e p) : F[X]) cast)⁻¹
  have hrec' : monicPd F d (e p) = p.1 := by
    dsimp [e, headD_degree_equiv]
    exact monicPd_coeff_recover F d p.1 p.2.1 p.2.2
  calc
    (((p.1 : RatFunc F) ^ 1)⁻¹) = ((p.1 : RatFunc F)⁻¹) := by simp
    _ = ((((monicPd F d (e p) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
          rw [hrec']

end ZagierHoffmanPositiveChar
