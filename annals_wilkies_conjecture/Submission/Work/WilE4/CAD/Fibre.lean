/-
  WilE4 / CAD — the fibre of a sign-condition cell.

  For a family `G` of polynomials in `m+1` variables and a sign vector `v`, the fibre over a base
  point `x : Fin m → ℝ` is the set of `t : ℝ` such that the sign vector of `G` at `Fin.snoc x t` is
  `v`.  `Fib` is the strict version, `FibCl` the non-strict ("closed") version.

  The corresponding univariate notions `pcell` / `pcellCl` (for a family `Fin k → ℝ[X]`) are
  recorded separately: the algebraic content of the cell-connectivity theorem is proved there.
-/
import Mathlib
import Submission.Work.WilE4.Tower

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial

variable {m k : ℕ}

/-! ## Univariate sign conditions for a family of polynomials -/

/-- The (strict) sign-condition set of a family of real polynomials: the points at which the sign
vector of the family is `v`. -/
def pcell (P : Fin k → Polynomial ℝ) (v : Fin k → SignType) : Set ℝ :=
  {t | ∀ i, SignType.sign ((P i).eval t) = v i}

/-- The non-strict ("closed") sign-condition set of a family of real polynomials. -/
def pcellCl (P : Fin k → Polynomial ℝ) (v : Fin k → SignType) : Set ℝ :=
  {t | ∀ i, (v i = 1 → 0 ≤ (P i).eval t) ∧ (v i = -1 → (P i).eval t ≤ 0) ∧
    (v i = 0 → (P i).eval t = 0)}

theorem pcell_subset_pcellCl (P : Fin k → Polynomial ℝ) (v : Fin k → SignType) :
    pcell P v ⊆ pcellCl P v := by
  intro t ht i
  have hs : SignType.sign ((P i).eval t) = v i := ht i
  refine ⟨?_, ?_, ?_⟩
  · intro h; rw [h] at hs; exact (sign_eq_one_iff.mp hs).le
  · intro h; rw [h] at hs; exact (sign_eq_neg_one_iff.mp hs).le
  · intro h; rw [h] at hs; exact sign_eq_zero_iff.mp hs

theorem pcellCl_isClosed (P : Fin k → Polynomial ℝ) (v : Fin k → SignType) :
    IsClosed (pcellCl P v) := by
  have h : pcellCl P v = (⋂ i, {t : ℝ | v i = 1 → 0 ≤ (P i).eval t}) ∩
                        (⋂ i, {t : ℝ | v i = -1 → (P i).eval t ≤ 0}) ∩
                        (⋂ i, {t : ℝ | v i = 0 → (P i).eval t = 0}) := by
    ext t; simp only [pcellCl, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨⟨fun i => (h i).1, fun i => (h i).2.1⟩, fun i => (h i).2.2⟩
    · intro h; exact fun i => ⟨(h.1.1 i), (h.1.2 i), (h.2 i)⟩
  rw [h]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_iInter fun i => by
      have hh : {t : ℝ | v i = 1 → 0 ≤ (P i).eval t} =
          if v i = 1 then {t : ℝ | (0 : ℝ) ≤ (P i).eval t} else Set.univ := by
        by_cases h1 : v i = 1 <;> simp [h1]
      rw [hh]
      by_cases h1 : v i = 1
      · rw [ite_eq_left h1]; exact isClosed_le continuous_const (Polynomial.continuous _)
      · rw [ite_eq_right h1]; exact isClosed_univ
  · exact isClosed_iInter fun i => by
      have hh : {t : ℝ | v i = -1 → (P i).eval t ≤ 0} =
          if v i = -1 then {t : ℝ | (P i).eval t ≤ 0} else Set.univ := by
        by_cases h1 : v i = -1 <;> simp [h1]
      rw [hh]
      by_cases h1 : v i = -1
      · rw [ite_eq_left h1]; exact isClosed_le (Polynomial.continuous _) continuous_const
      · rw [ite_eq_right h1]; exact isClosed_univ
  · exact isClosed_iInter fun i => by
      have hh : {t : ℝ | v i = 0 → (P i).eval t = 0} =
          if v i = 0 then {t : ℝ | (P i).eval t = 0} else Set.univ := by
        by_cases h1 : v i = 0 <;> simp [h1]
      rw [hh]
      by_cases h1 : v i = 0
      · rw [ite_eq_left h1]; exact isClosed_eq (Polynomial.continuous _) continuous_const
      · rw [ite_eq_right h1]; exact isClosed_univ

/-! ## The fibre of a sign-condition cell -/

/-- The fibre over `x` of the sign condition `v` for the family `G`. -/
def Fib (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (v : Fin G.length → SignType)
    (x : Fin m → ℝ) : Set ℝ :=
  {t | ∀ i, SignType.sign (MvPolynomial.eval (Fin.snoc x t) (G.get i)) = v i}

/-- The non-strict ("closed") version of the fibre. -/
def FibCl (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (v : Fin G.length → SignType)
    (x : Fin m → ℝ) : Set ℝ :=
  {t | ∀ i, (v i = 1 → 0 ≤ MvPolynomial.eval (Fin.snoc x t) (G.get i)) ∧
    (v i = -1 → MvPolynomial.eval (Fin.snoc x t) (G.get i) ≤ 0) ∧
    (v i = 0 → MvPolynomial.eval (Fin.snoc x t) (G.get i) = 0)}

/-- The fibre is the sign-condition set of the family of specialisations. -/
theorem Fib_eq_pcell (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (v : Fin G.length → SignType)
    (x : Fin m → ℝ) :
    Fib G v x = pcell (fun i => Work.WilE4.spec (G.get i) x) v := by
  ext t
  simp only [Fib, pcell, Set.mem_ofPred_eq]
  exact forall_congr' fun i => by rw [← Work.WilE4.spec_eval_snoc]

/-- The non-strict fibre is the non-strict sign-condition set of the specialisations. -/
theorem FibCl_eq_pcellCl (G : List (MvPolynomial (Fin (m + 1)) ℝ))
    (v : Fin G.length → SignType) (x : Fin m → ℝ) :
    FibCl G v x = pcellCl (fun i => Work.WilE4.spec (G.get i) x) v := by
  ext t
  simp only [FibCl, pcellCl, Set.mem_ofPred_eq]
  exact forall_congr' fun i => by rw [← Work.WilE4.spec_eval_snoc]

/-- The fibre is contained in the closed fibre. -/
theorem Fib_subset_FibCl (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (v : Fin G.length → SignType)
    (x : Fin m → ℝ) : Fib G v x ⊆ FibCl G v x := by
  rw [Fib_eq_pcell, FibCl_eq_pcellCl]
  exact pcell_subset_pcellCl _ _

/-- The closed fibre is closed. -/
theorem FibCl_isClosed (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (v : Fin G.length → SignType)
    (x : Fin m → ℝ) : IsClosed (FibCl G v x) := by
  rw [FibCl_eq_pcellCl]
  exact pcellCl_isClosed _ _

end Work.WilE4.CAD
