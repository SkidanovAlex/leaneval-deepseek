import Mathlib
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZGC.Lc0_ne_zero
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZGC.not_dvd_D0`

The eliminant `P = ASZElim.P a b g ∈ K[X₀,X₁]` has `X₀`-degree `5` (its `X₀⁵`-coefficient is the
scalar `Lc0 a b g`, nonzero under `ha`, `hg`), while the graph coefficient `D0 a b g` has
`X₀`-degree at most `2` and is nonzero (its constant coefficient is `3 (a + 2b)⁶`).
Since `K[X₀,X₁]` is a domain, a nonzero polynomial of `X₀`-degree `≤ 2` cannot be divisible by one
of `X₀`-degree `5` (in `K[X₁][X₀]`).

The main work is the bookkeeping: an explicit regrouping of both `P` and `D0`, the resulting bounds
on `MvPolynomial.degreeOf 0`, the identification of the relevant coefficients, and the transfer of
divisibility through `MvPolynomial.finSuccEquiv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotAS.ASZGC

open MvPolynomial

/-- `degreeOf 0` of `C c * X 0^i * X 1^j` is at most `i`. -/
private lemma degreeOf_zero_C_mul_X0pow_X1pow (K : Type) [Field K] (c : K) (i j : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.C c * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j : MvPolynomial (Fin 2) K)
        ≤ i := by
  have hX1 : MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) = 0 :=
    MvPolynomial.degreeOf_X_of_ne (by decide)
  calc MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C c * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j)
      ≤ MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.C c * MvPolynomial.X 0 ^ i)
        + MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1 ^ j) :=
        MvPolynomial.degreeOf_mul_le (0 : Fin 2) _ _
    _ ≤ (MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.C c)
          + MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0 ^ i))
        + j * MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1) :=
        add_le_add (MvPolynomial.degreeOf_mul_le (0 : Fin 2) _ _)
          (MvPolynomial.degreeOf_pow_le (0 : Fin 2) _ j)
    _ = i := by
        rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow, hX1]
        first | refl_ring1 | ring

/-- `degreeOf 0` of `C c * X 0^i * X 1^j` is at most any `n ≥ i`. -/
private lemma deg_of_shape (K : Type) [Field K] (n : ℕ) (c : K) (i j : ℕ) (h : i ≤ n) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.C c * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j : MvPolynomial (Fin 2) K)
        ≤ n :=
  (degreeOf_zero_C_mul_X0pow_X1pow K c i j).trans h

/-- `degreeOf 0` is subadditive. -/
private lemma degN_of_add (K : Type) [Field K] (n : ℕ) {f g : MvPolynomial (Fin 2) K}
    (hf : MvPolynomial.degreeOf (0 : Fin 2) f ≤ n) (hg : MvPolynomial.degreeOf (0 : Fin 2) g ≤ n) :
    MvPolynomial.degreeOf (0 : Fin 2) (f + g) ≤ n :=
  (MvPolynomial.degreeOf_add_le (0 : Fin 2) f g).trans (max_le hf hg)

/-- `degreeOf 0` of a list sum, from a term-by-term bound. -/
private lemma deg4_list_sum (K : Type) [Field K] (l : List (MvPolynomial (Fin 2) K))
    (h : ∀ p ∈ l, MvPolynomial.degreeOf (0 : Fin 2) p ≤ 4) :
    MvPolynomial.degreeOf (0 : Fin 2) l.sum ≤ 4 := by
  induction l with
  | nil => simp
  | cons p t ih =>
      rw [List.sum_cons]
      exact degN_of_add K 4 (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

/-! ### The `P` regrouping -/

/-- The `X 0 ^ 5`-part of `P`. -/
private noncomputable def Phead (K : Type) [Field K] (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (a ^(5:ℕ) * g ^(2:ℕ) + -1 * a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ) + 2 * b ^(5:ℕ) * g ^(2:ℕ))
    * MvPolynomial.X 0 ^(5:ℕ) * MvPolynomial.X 1 ^(0:ℕ)

/-- The remaining part of `P`, all of whose monomials have `X 0`-degree at most `4`. -/
private noncomputable def PtailList (K : Type) [Field K] (a b g : K) :
    List (MvPolynomial (Fin 2) K) :=
  [ MvPolynomial.C (2 * a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + -1 * a ^(2:ℕ) * b ^(3:ℕ) + a * b ^(4:ℕ))
      * MvPolynomial.X 0 ^(4:ℕ) * MvPolynomial.X 1 ^(0:ℕ),
    MvPolynomial.C (a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ))
      * MvPolynomial.X 0 ^(3:ℕ) * MvPolynomial.X 1 ^(2:ℕ),
    MvPolynomial.C (-2 * a ^(5:ℕ) * g + b ^(5:ℕ) * g) * MvPolynomial.X 0 ^(3:ℕ) * MvPolynomial.X 1 ^(1:ℕ),
    MvPolynomial.C (-1 * a ^(5:ℕ) + -1 * a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) + -2 * a * b ^(4:ℕ)
        + 2 * b ^(5:ℕ)) * MvPolynomial.X 0 ^(3:ℕ) * MvPolynomial.X 1 ^(0:ℕ),
    MvPolynomial.C (a ^(4:ℕ) * b * g + a ^(3:ℕ) * b ^(2:ℕ) * g + 2 * a ^(2:ℕ) * b ^(3:ℕ) * g + -2 * a * b ^(4:ℕ) * g)
      * MvPolynomial.X 0 ^(2:ℕ) * MvPolynomial.X 1 ^(3:ℕ),
    MvPolynomial.C (a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) + 2 * a * b ^(4:ℕ))
      * MvPolynomial.X 0 ^(2:ℕ) * MvPolynomial.X 1 ^(2:ℕ),
    MvPolynomial.C (2 * a ^(5:ℕ) + -1 * b ^(5:ℕ)) * MvPolynomial.X 0 ^(2:ℕ) * MvPolynomial.X 1 ^(0:ℕ),
    MvPolynomial.C (-1 * a ^(5:ℕ) * g ^(2:ℕ) + -2 * b ^(5:ℕ) * g ^(2:ℕ))
      * MvPolynomial.X 0 ^(1:ℕ) * MvPolynomial.X 1 ^(4:ℕ),
    MvPolynomial.C (-2 * a ^(5:ℕ) * g + -2 * a ^(4:ℕ) * b * g + -1 * a ^(3:ℕ) * b ^(2:ℕ) * g
        + 2 * a ^(2:ℕ) * b ^(3:ℕ) * g + a * b ^(4:ℕ) * g + -1 * b ^(5:ℕ) * g)
      * MvPolynomial.X 0 ^(1:ℕ) * MvPolynomial.X 1 ^(3:ℕ),
    MvPolynomial.C (-1 * a ^(5:ℕ) + -1 * a ^(4:ℕ) * b + -1 * a ^(3:ℕ) * b ^(2:ℕ) + -2 * a ^(2:ℕ) * b ^(3:ℕ)
        + 2 * a * b ^(4:ℕ) + -2 * b ^(5:ℕ)) * MvPolynomial.X 0 ^(1:ℕ) * MvPolynomial.X 1 ^(2:ℕ),
    MvPolynomial.C (2 * a ^(5:ℕ) * g ^(3:ℕ) + -1 * b ^(5:ℕ) * g ^(3:ℕ)) * MvPolynomial.X 0 ^(0:ℕ) * MvPolynomial.X 1 ^(5:ℕ),
    MvPolynomial.C (-1 * a ^(5:ℕ) * g + -2 * b ^(5:ℕ) * g) * MvPolynomial.X 0 ^(0:ℕ) * MvPolynomial.X 1 ^(3:ℕ),
    MvPolynomial.C (a ^(5:ℕ) + a ^(4:ℕ) * b + -2 * a ^(3:ℕ) * b ^(2:ℕ) + -1 * a ^(2:ℕ) * b ^(3:ℕ) + 2 * a * b ^(4:ℕ)
        + -2 * b ^(5:ℕ)) * MvPolynomial.X 0 ^(0:ℕ) * MvPolynomial.X 1 ^(2:ℕ),
    MvPolynomial.C (-1 * a ^(5:ℕ) + -2 * b ^(5:ℕ)) * MvPolynomial.X 0 ^(0:ℕ) * MvPolynomial.X 1 ^(0:ℕ) ]

private noncomputable def Ptail (K : Type) [Field K] (a b g : K) : MvPolynomial (Fin 2) K :=
  (PtailList K a b g).sum

private lemma P_decomp (K : Type) [Field K] (a b g : K) :
    Work.MotAS.ASZElim.P a b g = Phead K a b g + Ptail K a b g := by
  simp only [Work.MotAS.ASZElim.P, Phead, Ptail, PtailList, List.sum_cons, List.sum_nil, add_zero]
  refl_ring1

private lemma Phead_deg (K : Type) [Field K] (a b g : K) :
    MvPolynomial.degreeOf (0 : Fin 2) (Phead K a b g) ≤ 5 := by
  simp only [Phead]
  exact deg_of_shape K 5 _ 5 0 (by norm_num)

private lemma Ptail_deg (K : Type) [Field K] (a b g : K) :
    MvPolynomial.degreeOf (0 : Fin 2) (Ptail K a b g) ≤ 4 := by
  have h : Ptail K a b g = (PtailList K a b g).sum := rfl
  rw [h]
  refine deg4_list_sum K _ ?_
  intro p hp
  simp only [PtailList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (refine deg_of_shape K 4 _ _ _ ?_; norm_num)

private lemma P_coeff (K : Type) [Field K] (a b g : K) :
    (Work.MotAS.ASZElim.P a b g).coeff (Finsupp.single (0 : Fin 2) 5)
      = Work.MotAS.ASZGC.Lc0 a b g := by
  have hhead : (Phead K a b g).coeff (Finsupp.single (0 : Fin 2) 5)
      = (a ^(5:ℕ) * g ^(2:ℕ) + -1 * a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ) + 2 * b ^(5:ℕ) * g ^(2:ℕ)) := by
    simp only [Phead, pow_zero, mul_one, MvPolynomial.C_mul_X_pow_eq_monomial]
    rw [MvPolynomial.coeff_monomial, if_pos rfl]
  have htail : (Ptail K a b g).coeff (Finsupp.single (0 : Fin 2) 5) = 0 := by
    have hns : (Finsupp.single (0 : Fin 2) 5 : Fin 2 →₀ ℕ) ∉ (Ptail K a b g).support :=
      MvPolynomial.notMem_support_of_degreeOf_lt (0 : Fin 2) (by
        rw [Finsupp.single_eq_same]
        exact lt_of_le_of_lt (Ptail_deg K a b g) (by norm_num))
    rw [MvPolynomial.mem_support_iff] at hns
    exact not_not.mp hns
  rw [P_decomp K a b g, MvPolynomial.coeff_add, hhead, htail, add_zero]
  simp only [Work.MotAS.ASZGC.Lc0]
  refl_ring1

/-! ### The `D0` regrouping -/

/-- `C 2 = 2` in `MvPolynomial (Fin 2) K`. -/
private lemma C_two (K : Type) [Field K] :
    (MvPolynomial.C (2 : K) : MvPolynomial (Fin 2) K) = (2 : MvPolynomial (Fin 2) K) :=
  map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K) 2

private lemma C_three (K : Type) [Field K] :
    (MvPolynomial.C (3 : K) : MvPolynomial (Fin 2) K) = (3 : MvPolynomial (Fin 2) K) :=
  map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K) 3

private lemma C_four (K : Type) [Field K] :
    (MvPolynomial.C (4 : K) : MvPolynomial (Fin 2) K) = (4 : MvPolynomial (Fin 2) K) :=
  map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K) 4

private noncomputable def D0head (K : Type) [Field K] (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (2 * b ^(6:ℕ) + a * b ^(5:ℕ) + a ^(5:ℕ) * b + 3 * a ^(6:ℕ))

private noncomputable def D0tail (K : Type) [Field K] (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (4 * b ^(6:ℕ) + 3 * a * b ^(5:ℕ) + 2 * a ^(5:ℕ) * b + 4 * a ^(6:ℕ))
      * MvPolynomial.X 0 ^(1:ℕ) * MvPolynomial.X 1 ^(0:ℕ)
  + MvPolynomial.C ((4 * b ^(6:ℕ) + 2 * a * b ^(5:ℕ) + 2 * a ^(5:ℕ) * b + a ^(6:ℕ)) * g)
      * MvPolynomial.X 0 ^(1:ℕ) * MvPolynomial.X 1 ^(1:ℕ)
  + MvPolynomial.C (a * b ^(5:ℕ) + 2 * a ^(2:ℕ) * b ^(4:ℕ) + 4 * a ^(3:ℕ) * b ^(3:ℕ) + 3 * a ^(4:ℕ) * b ^(2:ℕ) + a ^(5:ℕ) * b)
      * MvPolynomial.X 0 ^(2:ℕ) * MvPolynomial.X 1 ^(0:ℕ)

private lemma D0_decomp (K : Type) [Field K] (a b g : K) :
    Work.MotAS.ASZGC.D0 a b g = D0head K a b g + D0tail K a b g := by
  simp only [Work.MotAS.ASZGC.D0, D0head, D0tail, MvPolynomial.C_add, MvPolynomial.C_mul,
    MvPolynomial.C_pow, C_two K, C_three K, C_four K]
  refl_ring1

private lemma D0_deg (K : Type) [Field K] (a b g : K) :
    MvPolynomial.degreeOf (0 : Fin 2) (Work.MotAS.ASZGC.D0 a b g) ≤ 2 := by
  rw [D0_decomp K a b g]
  apply degN_of_add
  · simp only [D0head]
    exact (MvPolynomial.degreeOf_C _ (0 : Fin 2)).le.trans (by norm_num)
  · simp only [D0tail]
    repeat' (first
      | apply degN_of_add
      | (apply deg_of_shape K; norm_num))

private lemma D0_const (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Work.MotAS.ASZGC.D0 a b g).coeff (0 : Fin 2 →₀ ℕ) = 3 * (a + 2 * b) ^(6:ℕ) := by
  rw [← MvPolynomial.constantCoeff_eq, D0_decomp K a b g]
  have hhead : MvPolynomial.constantCoeff (D0head K a b g)
      = 2 * b ^(6:ℕ) + a * b ^(5:ℕ) + a ^(5:ℕ) * b + 3 * a ^(6:ℕ) := by
    simp only [D0head, MvPolynomial.constantCoeff_C]
  have htail : MvPolynomial.constantCoeff (D0tail K a b g) = 0 := by
    have h1 : MvPolynomial.constantCoeff ((MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(1:ℕ)) = 0 := by
      rw [pow_one, MvPolynomial.constantCoeff_X]
    have h2 : MvPolynomial.constantCoeff ((MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(0:ℕ)) = 1 := by
      rw [pow_zero, map_one]
    have h3 : MvPolynomial.constantCoeff ((MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ)) = 0 := by
      rw [pow_two, map_mul, MvPolynomial.constantCoeff_X, zero_mul]
    have h4 : MvPolynomial.constantCoeff ((MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(1:ℕ)) = 0 := by
      rw [pow_one, MvPolynomial.constantCoeff_X]
    simp only [D0tail, map_add, map_mul, MvPolynomial.constantCoeff_C, h1, h2, h3, h4,
      zero_mul, mul_zero, one_mul, mul_one, add_zero]
  rw [map_add, hhead, htail, add_zero]
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have key : 3 * (a + 2 * b) ^(6:ℕ) - (2 * b ^(6:ℕ) + a * b ^(5:ℕ) + a ^(5:ℕ) * b + 3 * a ^(6:ℕ))
      = 5 * (7 * a ^(5:ℕ) * b + 36 * a ^(4:ℕ) * b ^(2:ℕ) + 96 * a ^(3:ℕ) * b ^(3:ℕ)
            + 144 * a ^(2:ℕ) * b ^(4:ℕ) + 115 * a * b ^(5:ℕ) + 38 * b ^(6:ℕ)) := by ring
  rw [h5, zero_mul] at key
  exact (sub_eq_zero.mp key).symm

theorem not_dvd_D0 (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) :
    ¬ Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.D0 a b g := by
  have hlc : Work.MotAS.ASZGC.Lc0 a b g ≠ 0 :=
    Work.MotAS.ASZGC.Lc0_ne_zero K a b g ha hg
  have hPle : MvPolynomial.degreeOf (0 : Fin 2) (Work.MotAS.ASZElim.P a b g) ≤ 5 := by
    rw [P_decomp K a b g]
    refine le_trans (MvPolynomial.degreeOf_add_le (0 : Fin 2) (Phead K a b g) (Ptail K a b g)) ?_
    exact max_le (Phead_deg K a b g) ((Ptail_deg K a b g).trans (by norm_num))
  have hPcoeff : (Work.MotAS.ASZElim.P a b g).coeff (Finsupp.single (0 : Fin 2) 5)
      = Work.MotAS.ASZGC.Lc0 a b g := P_coeff K a b g
  have hPmem : (Finsupp.single (0 : Fin 2) 5 : Fin 2 →₀ ℕ)
      ∈ (Work.MotAS.ASZElim.P a b g).support := by
    rw [MvPolynomial.mem_support_iff, hPcoeff]
    exact hlc
  have hPge : 5 ≤ MvPolynomial.degreeOf (0 : Fin 2) (Work.MotAS.ASZElim.P a b g) := by
    have hh := MvPolynomial.monomial_le_degreeOf (0 : Fin 2) hPmem
    simpa using hh
  have hPdeg : MvPolynomial.degreeOf (0 : Fin 2) (Work.MotAS.ASZElim.P a b g) = 5 :=
    le_antisymm hPle hPge
  have hDle : MvPolynomial.degreeOf (0 : Fin 2) (Work.MotAS.ASZGC.D0 a b g) ≤ 2 :=
    D0_deg K a b g
  have hDcoeff : (Work.MotAS.ASZGC.D0 a b g).coeff (0 : Fin 2 →₀ ℕ)
      = 3 * (a + 2 * b) ^(6:ℕ) := D0_const K a b g
  have ha2b : a + 2 * b ≠ 0 := by
    intro h0
    apply ha
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    have h1 : a = -(2 * b) := by linear_combination h0
    rw [h1]
    linear_combination (norm := refl_ring1 (mod := 5))
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := h
    rw [CharP.cast_eq_zero_iff K 5] at h'
    norm_num at h'
  have hD0ne : Work.MotAS.ASZGC.D0 a b g ≠ 0 := by
    intro h0
    have hc : (Work.MotAS.ASZGC.D0 a b g).coeff (0 : Fin 2 →₀ ℕ) = 0 := by
      rw [h0]; simp
    rw [hDcoeff] at hc
    exact (mul_ne_zero h3 (pow_ne_zero 6 ha2b)) hc
  rintro ⟨h, hh⟩
  have hP0 : (MvPolynomial.finSuccEquiv K 1) (Work.MotAS.ASZElim.P a b g) ≠ 0 := by
    intro hc
    have h := MvPolynomial.natDegree_finSuccEquiv (R := K) (n := 1)
      (Work.MotAS.ASZElim.P a b g)
    rw [hc, Polynomial.natDegree_zero, hPdeg] at h
    exact absurd h (by norm_num)
  have hD0 : (MvPolynomial.finSuccEquiv K 1) (Work.MotAS.ASZGC.D0 a b g) ≠ 0 := by
    intro hc
    exact hD0ne ((MvPolynomial.finSuccEquiv K 1).injective (by rw [hc, map_zero]))
  have hdiv : (MvPolynomial.finSuccEquiv K 1) (Work.MotAS.ASZElim.P a b g)
      ∣ (MvPolynomial.finSuccEquiv K 1) (Work.MotAS.ASZGC.D0 a b g) :=
    ⟨(MvPolynomial.finSuccEquiv K 1) h, by rw [← map_mul, ← hh]⟩
  obtain ⟨q, hq⟩ := hdiv
  have hqne : q ≠ 0 := fun h0 => hD0 (by rw [hq, h0, mul_zero])
  have hmul := Polynomial.natDegree_mul hP0 hqne
  rw [← hq] at hmul
  have hPnat : (MvPolynomial.finSuccEquiv K 1 (Work.MotAS.ASZElim.P a b g)).natDegree = 5 := by
    rw [MvPolynomial.natDegree_finSuccEquiv]; exact hPdeg
  have hDnat : (MvPolynomial.finSuccEquiv K 1 (Work.MotAS.ASZGC.D0 a b g)).natDegree ≤ 2 := by
    rw [MvPolynomial.natDegree_finSuccEquiv]; exact hDle
  omega

end Work.MotAS.ASZGC
