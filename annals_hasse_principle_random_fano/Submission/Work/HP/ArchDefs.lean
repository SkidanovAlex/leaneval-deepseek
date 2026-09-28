import Mathlib
import Submission.Work.HP.Defs

/-!
# N12 (`Work.HP.arch`) : auxiliary definitions

Objects used in the proof of `Work.HP.arch` (paper §5.3, "the Archimedean factor is rarely
small").

* `gradF d n a x j` is `∂f_a/∂x_j(x)`, so that `gradVec d n a x` is `∇f_a(x)`.
* `smon d n hd i j` is the monomial `x_i^{d-1}x_j` (which is `x_i^d` when `j = i`).
  These `n+1` monomials are the ones whose coefficients are pinned by the values of `f_a`
  and `∇f_a` at a point `x` with `x_i ≠ 0` (this is the replacement for the paper's
  "coordinate `c_a^{(i)}`" argument).
* `IPt d n a` : `f_a` has a zero on the unit sphere (the paper's `𝕀^loc_{d,n}`).
* `Bset d n λ` : the paper's `𝓑^{(λ)}_{N_{d,n}}`.
* `Lset d n` : the "degenerate" complement `{a : ∃x ∈ S^n, f_a(x) = 0, ∇f_a(x) = 0}`,
  which is the part of `IPt ∩ B(1)` not covered by `⋃_λ Bset λ`; it has measure zero.
* `Uset d n A` : the paper's boundary set `𝒰_{d,n}(A)`.
* `Mdn d n` : a constant with `‖∇f_a(x)‖ ≤ Mdn d n * ‖a‖` for `‖x‖ = 1`.
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators

namespace Work.HP

variable {d n : ℕ}

/-- `∂f_a/∂x_j (x)`, where `f_a = Σ_m a_m x^m`. -/
def gradF (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  ∑ m : Mon d n, a m * ((m.1 j : ℕ) : ℝ) * x j ^ ((m.1 j : ℕ) - 1) *
    ∏ l ∈ Finset.univ.erase j, x l ^ ((m.1 l : ℕ))

/-- The gradient vector `∇f_a(x)`. -/
def gradVec (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => gradF d n a x j

/-- The monomial `x_i^{d-1}x_j` (equal to `x_i^d` when `j = i`), for `d ≥ 1`. -/
def smon (d n : ℕ) (hd : 1 ≤ d) (i j : Fin (n + 1)) : Mon d n :=
  ⟨fun l =>
      if l = i then (if l = j then ⟨d, Nat.lt_succ_self d⟩ else ⟨d - 1, by omega⟩)
      else (if l = j then ⟨1, by omega⟩ else ⟨0, by omega⟩), by
    have key : ∀ l : Fin (n + 1),
        (((if l = i then (if l = j then ⟨d, Nat.lt_succ_self d⟩ else ⟨d - 1, by omega⟩)
          else (if l = j then ⟨1, by omega⟩ else ⟨0, by omega⟩) : Fin (d + 1))) : ℕ)
        = (if l = i then (if l = j then d else d - 1) else (if l = j then 1 else 0)) := by
      intro l
      by_cases h1 : l = i
      · subst h1
        by_cases h2 : l = j <;> simp [h2]
      · by_cases h2 : l = j
        · subst h2
          simp [h1]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun l _ => key l)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have hmem : (j ∈ Finset.univ.erase i) ↔ j ≠ i := by simp
    have hsum : ∑ x ∈ Finset.univ.erase i,
        (if x = i then (if x = j then d else d - 1) else (if x = j then 1 else 0))
        = (if j ≠ i then (1 : ℕ) else 0) := by
      rw [Finset.sum_congr rfl (fun x hx => by
        rw [if_neg (Finset.mem_erase.mp hx).1])]
      rw [Finset.sum_ite_eq']
      simp [hmem]
    have hself : (if i = i then (if i = j then d else d - 1) else (if i = j then 1 else 0))
        = (if i = j then d else d - 1) := by simp
    rw [hsum, hself]
    by_cases hij : i = j
    · simp [hij]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
      omega
  ⟩

/-- The set of the `n+1` special monomials at `i`. -/
def Sset (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) : Set (Mon d n) :=
  Set.range (smon d n hd i)

/-- `a` with the special monomials at `i` set to zero. -/
def zeroS (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (a : Mon d n → ℝ) : Mon d n → ℝ :=
  fun m => if m ∈ Sset d n hd i then 0 else a m


/-- `f_a` has a real zero on the unit sphere (the paper's `𝕀^loc_{d,n}`, apart from `a = 0`). -/
def IPt (d n : ℕ) (a : Mon d n → ℝ) : Prop :=
  ∃ x : Fin (n + 1) → ℝ, rNorm x = 1 ∧ formEvalR d n a x = 0

/-- The paper's stratum `𝓑^{(λ)}_{N_{d,n}}`: forms of norm `≤ 1` with a real zero at which the
gradient has norm between `λ‖a‖` and `2λ‖a‖`. -/
def Bset (d n : ℕ) (lam : ℝ) : Set (Mon d n → ℝ) :=
  {a | rNorm a ≤ 1 ∧ IPt d n a ∧
    ∃ x : Fin (n + 1) → ℝ, rNorm x = 1 ∧ formEvalR d n a x = 0 ∧
      lam * rNorm a < rNorm (gradVec d n a x) ∧ rNorm (gradVec d n a x) ≤ 2 * lam * rNorm a}

/-- Forms of norm `≤ 1` with a real zero where the gradient vanishes ("degenerate" forms).
They are exactly the elements of `IPt ∩ B(1)` that lie in no `Bset d n λ`, `λ > 0`. -/
def Lset (d n : ℕ) : Set (Mon d n → ℝ) :=
  {a | rNorm a ≤ 1 ∧
    ∃ x : Fin (n + 1) → ℝ, rNorm x = 1 ∧ formEvalR d n a x = 0 ∧ gradVec d n a x = 0}

/-- The paper's boundary set `𝒰_{d,n}(A)`: primitive coefficient vectors of norm `≤ A` with a
real zero whose unit neighbourhood is not contained in the set of forms with a real zero. -/
def Uset (d n : ℕ) (A : ℝ) : Set (Mon d n → ℤ) :=
  {a | IsPrim a ∧ eNorm a ≤ A ∧ IPt d n (toR a) ∧
    ¬ (∀ y : Mon d n → ℝ, rNorm (toR a - y) ≤ 1 → IPt d n y)}

/-- A crude bound for `sup {‖∇f_a(x)‖/‖a‖ : ‖a‖ ≤ 1, ‖x‖ = 1}`. -/
def Mdn (d n : ℕ) : ℝ := (n + 1 : ℝ) * (d : ℝ) * (NN d n : ℝ)

/-- The Archimedean factor `τ(a;γ)` (paper (5.2)), for real coefficient vectors. -/
abbrev tauT (d n : ℕ) (a : Mon d n → ℝ) (γ : ℝ) : ℝ := tauArch d n a γ

end Work.HP
