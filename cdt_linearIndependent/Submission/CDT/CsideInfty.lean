import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordDegT_def
import Submission.Commons.FieldTheory.RatFunc.ordDegT_div
import Submission.Commons.FieldTheory.RatFunc.ordDegT_algebraMap
import Submission.Commons.FieldTheory.RatFunc.ordDegT_leading_term
import Submission.Commons.FieldTheory.RatFunc.ordDegT_adjoint_eq_of_indicial

/-!
# The local bound at `∞` of the C-side operator `LL`

The last of the five local bounds of the C-side local/indicial analysis
(`Submission/CDT/CsideLocal` has the other four).  The point `∞` is treated through the
`min`-valuation `ordDegT` (`Commons.FieldTheory.RatFunc.ordDegT`, the negative of the degree of a
rational function), whose uniformizer is `X⁻¹` and whose only structural difference from
`ordAtT α` at a finite point is that the derivative *raises* the order by one:
`ordDegT (D x) = ordDegT x + 1`.

The indicial data are the paper's: `eᵢ = deg c₄ − deg cᵢ = (7,3,2,1,0)`, so that
`eᵢ + i = (7,4,4,4,4)`, `m = 4` and `I = {i : eᵢ + i = 4} = {1,2,3,4}`; the leading coefficients are
`λ = (·, 12, 24, 10, 1)` (only the indices `i ≥ 1` matter), and the indicial value is
`Σ_{i∈I}(−1)ⁱλᵢ∏_{j<i}(−(N+eᵢ+j)) = (N+3)(N+4)²(N+5)`, whose integer roots are `−3, −4, −5`.
Since `Σᵢ(−1)ⁱ Dⁱ(γᵢ b) = −R` and `ordDegT R ≥ −1` (equivalently `deg R ≤ 1`), a value
`N = ordDegT b ≤ −6` forces the indicial value to vanish — impossible — whence
`N ≥ −5`, i.e. `ordInfT b ≤ 5`, i.e. `deg b₃ ≤ 5` (the paper's `N_∞ ≤ 5`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Commons.FieldTheory.RatFunc

namespace Submission.CDT.CsideInfty

variable {K : Type*} [Field K]

/-- `ordDegT` is invariant under negation. -/
theorem ordDegT_neg (x : RatFunc K) : ordDegT (-x) = ordDegT x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [neg_zero]
  · have h1 : ordDegT (-1 : RatFunc K) = 0 := by
      rw [show (-1 : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) (-1) from by simp,
        ordDegT_algebraMap (by norm_num)]
      norm_num
    calc ordDegT (-x) = ordDegT (x / (-1)) := by ring_nf
      _ = ordDegT x - ordDegT (-1) := ordDegT_div hx (by norm_num)
      _ = ordDegT x := by rw [h1, sub_zero]

/-- **The local bound `N_∞ ≤ 5`.**  With the local data at `∞` (the orders `e = (7,3,2,1,0)` of the
`γᵢ` and the leading coefficients `λ = (·,12,24,10,1)` of the `γᵢ` relative to `X^{−eᵢ}`), and an
inhomogeneity `R` with `ordDegT R ≥ −1` (i.e. `deg R ≤ 1`), a solution `b` of the eliminated
equation has `ordDegT b ≥ −5`, i.e. `ordInfT b ≤ 5`: the "pole order at `∞`" of `b` is at most `5`. -/
theorem local_bound_at_infty {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (bb R : RatFunc K) (hb : bb ≠ 0) (hR : ((-1 : ℤ) : WithTop ℤ) ≤ ordDegT R)
    (g : Fin 5 → RatFunc K)
    (he : ∀ i : Fin 5, (((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i : ℤ) : WithTop ℤ) ≤ ordDegT (g i))
    (hlam : ∀ i : Fin 5, ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i + ((i : ℕ) : ℤ) = 4) →
      ((((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i + 1 : ℤ)) : WithTop ℤ) ≤ ordDegT
        (g i - algebraMap (Polynomial K) (RatFunc K)
            (Polynomial.C ((![0, 12, 24, 10, 1] : Fin 5 → K) i))
          * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
              ^ (-((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i))))
    (hsys : (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i]) (g i * bb))
      = -R) :
    ((-5 : ℤ) : WithTop ℤ) ≤ ordDegT bb := by
  classical
  by_contra hcon
  have hcon' : ordDegT bb < ((-5 : ℤ) : WithTop ℤ) := not_le.mp hcon
  set N : ℤ := (Polynomial.natDegree bb.denom : ℤ) - (Polynomial.natDegree bb.num : ℤ) with hNdef
  have hN : ordDegT bb = (N : WithTop ℤ) := by
    rw [ordDegT_def hb, hNdef, WithTop.LinearOrderedAddCommGroup.coe_sub]
  have hNle : N ≤ -6 := by
    rw [hN] at hcon'
    rw [WithTop.coe_lt_coe] at hcon'
    omega
  have hev : ∀ i : Fin 5, ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i) + ((i : ℕ) : ℤ) ≠ 4 →
      (((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i : ℤ) : WithTop ℤ) ≤ ordDegT (g i) :=
    fun i _ => he i
  have hm : ∀ i : Fin 5, 4 ≤ ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i) + ((i : ℕ) : ℤ) := by decide
  have hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 =>
        ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i) + ((i : ℕ) : ℤ) = 4),
      (-1 : ℤ) ^ (i : ℕ) • (((![0, 12, 24, 10, 1] : Fin 5 → K) i)
        * ∏ j ∈ Finset.range (i : ℕ),
            ((-(N + (![7, 3, 2, 1, 0] : Fin 5 → ℤ) i + (j : ℤ)) : ℤ) : K))) ≠ 0 := by
    have hval : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 =>
          ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i) + ((i : ℕ) : ℤ) = 4),
        (-1 : ℤ) ^ (i : ℕ) • (((![0, 12, 24, 10, 1] : Fin 5 → K) i)
          * ∏ j ∈ Finset.range (i : ℕ),
              ((-(N + (![7, 3, 2, 1, 0] : Fin 5 → ℤ) i + (j : ℤ)) : ℤ) : K)))
        = ((N + 3 : ℤ) : K) * ((N + 4 : ℤ) : K) * ((N + 4 : ℤ) : K)
          * ((N + 5 : ℤ) : K) := by
      rw [show (Finset.univ.filter (fun i : Fin 5 =>
            ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) i) + ((i : ℕ) : ℤ) = 4))
          = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
      rw [show ({1, 2, 3, 4} : Finset (Fin 5))
          = insert 1 (insert 2 (insert 3 ({4} : Finset (Fin 5)))) from rfl]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [show ((![0, 12, 24, 10, 1] : Fin 5 → K) (1 : Fin 5)) = (12 : K) from rfl,
        show ((![0, 12, 24, 10, 1] : Fin 5 → K) (2 : Fin 5)) = (24 : K) from rfl,
        show ((![0, 12, 24, 10, 1] : Fin 5 → K) (3 : Fin 5)) = (10 : K) from rfl,
        show ((![0, 12, 24, 10, 1] : Fin 5 → K) (4 : Fin 5)) = (1 : K) from rfl,
        show ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) (1 : Fin 5)) = (3 : ℤ) from rfl,
        show ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) (2 : Fin 5)) = (2 : ℤ) from rfl,
        show ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) (3 : Fin 5)) = (1 : ℤ) from rfl,
        show ((![7, 3, 2, 1, 0] : Fin 5 → ℤ) (4 : Fin 5)) = (0 : ℤ) from rfl,
        show (((1 : Fin 5) : ℕ)) = 1 from rfl, show (((2 : Fin 5) : ℕ)) = 2 from rfl,
        show (((3 : Fin 5) : ℕ)) = 3 from rfl, show (((4 : Fin 5) : ℕ)) = 4 from rfl,
        Finset.prod_range_succ, Finset.prod_range_zero]
      push_cast
      ring
    rw [hval]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
      · rw [Int.cast_ne_zero]; omega
  obtain ⟨r, hr, hb'⟩ := ordDegT_leading_term hb N hN
  have hmain : ordDegT (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) •
      ((fun x : RatFunc K => D x)^[i]) (g i * bb)) = ((N + 4 : ℤ) : WithTop ℤ) :=
    ordDegT_adjoint_eq_of_indicial D hd bb hb N hN r hr hb' g
      (![7, 3, 2, 1, 0] : Fin 5 → ℤ) (![0, 12, 24, 10, 1] : Fin 5 → K) 4 hev hm hlam hP
  rw [hsys, ordDegT_neg] at hmain
  have hthis : ((-1 : ℤ) : WithTop ℤ) ≤ ((N + 4 : ℤ) : WithTop ℤ) := by
    rw [← hmain]; exact hR
  rw [WithTop.coe_le_coe] at hthis
  omega

end Submission.CDT.CsideInfty
