/-
# Density of the degree filtration of a left ideal of `SkewL R`

This file proves the "density" estimate for the degree filtration `degPart R I k`
(the `R`-module of coefficient vectors, in degrees `0..k`, of the polynomial elements of `I`):

  `rdim (degPart I (k+1)) ≤ rdim (degPart I k) + rdim (constIdeal I (k+1))`,

and its iterated form `rdim (degPart I (k+d)) ≤ rdim (degPart I k) + d * σ` whenever
`rdim (constIdeal I j) ≤ σ` for all `j`.

The proof combines
* `rdimAdditivity` (dimension additivity for a linear map and its kernel part, applied to
  the projection `evZero (k+1) : R^{k+2} → R^1`),
* `degPart_ker_eq_cons` (every element of `degPart I (k+1)` with vanishing constant coefficient
  is a twisted shift `Fin.cons 0 (τ ∘ z)` of an element `z ∈ degPart I k`),
* `rk_cons_le` (matrices built from such twisted shifts have rank at most the dimension of the
  row span of the underlying `Z`).
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.rdimAdditivity
import Submission.Work.ORHughesFree.NaturalExtension.degPart_ker_eq_cons
import Submission.Work.ORHughesFree.NaturalExtension.rk_cons_le

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

variable {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R]

/-- The dimension of the zero submodule vanishes. -/
lemma rdim_bot (rk : SylvesterRank R) (n : ℕ) :
    rdim rk (⊥ : Submodule R (Fin n → R)) = 0 := by
  refine le_antisymm ?_ ?_
  · unfold rdim
    refine csSup_le (rdim_nonempty rk ⊥) ?_
    rintro x ⟨m, A, hA, rfl⟩
    have hzero : A = 0 := by
      ext i j
      have h := congrFun (hA i) j
      simpa using h
    rw [hzero, rk.rk_zero]
  · unfold rdim
    exact le_csSup (rdim_bddAbove rk ⊥) ⟨0, 0, fun i => Fin.elim0 i, by rw [rk.rk_zero]⟩

/-- **Density step.** `dim P_{k+1}(I) ≤ dim P_k(I) + dim T_{k+1}(I)`. -/
theorem rdim_degPart_succ_le (rk : SylvesterRank R)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (I : Set (SkewL R)) (hI : IsLeftIdeal I) (k : ℕ) :
    rdim rk (degPart R I (k + 1)) ≤ rdim rk (degPart R I k) + rdim rk (constIdeal I (k + 1)) := by
  by_cases hne : I.Nonempty
  · have h1 := rdimAdditivity rk (evZero (k + 1)) (degPart R I (k + 1))
    have h2 : (degPart R I (k + 1)).map (evZero (k + 1)) = constIdeal I (k + 1) := rfl
    have h3 : rdim rk ((degPart R I (k + 1)) ⊓ LinearMap.ker (evZero (k + 1)))
        ≤ rdim rk (degPart R I k) := by
      unfold rdim
      refine csSup_le (rdim_nonempty rk _) ?_
      rintro x ⟨m, A, hA, rfl⟩
      have hrow : ∀ i : Fin m, ∃ z ∈ degPart R I k,
          (fun j => A i j)
            = Fin.cons 0 (fun p : Fin (k + 1) => (Multiplicative.ofAdd (1 : ℤ)) • z p) := by
        intro i
        have hi : (fun j => A i j) ∈ degPart R I (k + 1) ∧
            (fun j => A i j) ∈ LinearMap.ker (evZero (k + 1)) := Submodule.mem_inf.mp (hA i)
        have hx0 : (fun j => A i j) 0 = 0 := by
          have h := LinearMap.mem_ker.mp hi.2
          simpa [evZero] using congrFun h 0
        exact degPart_ker_eq_cons I hI hne k hi.1 hx0
      choose z hz hzA using hrow
      refine le_trans (rk_cons_le rk hτ A (fun i p => z i p) hzA) ?_
      refine rdim_mono rk ?_
      rw [Submodule.span_le]
      rintro v ⟨i, rfl⟩
      exact hz i
    rw [h2] at h1
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    have h1 : degPart R (∅ : Set (SkewL R)) (k + 1) = ⊥ := by
      rw [degPart]; simp
    have h2 : degPart R (∅ : Set (SkewL R)) k = ⊥ := by
      rw [degPart]; simp
    have h3 : constIdeal (∅ : Set (SkewL R)) (k + 1) = ⊥ := by
      rw [constIdeal, h1, Submodule.map_bot]
    rw [h1, h2, h3, rdim_bot, rdim_bot, rdim_bot]
    norm_num

/-- **Iterated density.** `dim P_{k+d}(I) ≤ dim P_k(I) + d · σ` whenever every constant-term
ideal `T_j(I)` has dimension at most `σ`. -/
theorem rdim_degPart_add_le (rk : SylvesterRank R)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (I : Set (SkewL R)) (hI : IsLeftIdeal I) (σ : ℝ)
    (hσ : ∀ j : ℕ, rdim rk (constIdeal I j) ≤ σ) (k d : ℕ) :
    rdim rk (degPart R I (k + d)) ≤ rdim rk (degPart R I k) + (d : ℝ) * σ := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := rdim_degPart_succ_le rk hτ I hI (k + d)
    have h2 := hσ (k + d + 1)
    calc rdim rk (degPart R I (k + (d + 1)))
        ≤ rdim rk (degPart R I (k + d)) + rdim rk (constIdeal I (k + d + 1)) := h1
      _ ≤ (rdim rk (degPart R I k) + (d : ℝ) * σ) + σ := add_le_add ih h2
      _ = rdim rk (degPart R I k) + ((d + 1 : ℕ) : ℝ) * σ := by push_cast; ring

end Work.ORHughesFree.NaturalExtension
