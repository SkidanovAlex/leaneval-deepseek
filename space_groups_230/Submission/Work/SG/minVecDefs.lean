import Mathlib
import Submission.Work.SG.SellingDefs

/-! ## Shared vocabulary for the coset-minimal-vector computation

Definitions and elementary lemmas used in the proof of
`Work.SG.minVecs_eq_sellingVecs`.  The superbase coordinates of `y : IVec` are
`cons0 y = (0, y₀, y₁, y₂) : Fin 4 → ℤ`; the *Selling coefficients* are
`q_{mn} = - bf Q (sb W m) (sb W n) ≥ 0` for an obtuse superbase. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped Matrix BigOperators

/-- The ordered pairs `m < n` of superbase indices. -/
def pairSet : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun p => p.1 < p.2

theorem mem_pairSet {p : Fin 4 × Fin 4} : p ∈ pairSet ↔ p.1 < p.2 := by
  simp [pairSet]

theorem pairSet_sum (f : Fin 4 × Fin 4 → ℤ) :
    ∑ p ∈ pairSet, f p = f (0, 1) + f (0, 2) + f (0, 3) + f (1, 2) + f (1, 3) + f (2, 3) := by
  rw [show pairSet = ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4))
      from by decide]
  simp [Finset.sum_insert]
  ring

/-- The Selling coefficient `q_{mn} = - bf Q (sb W m) (sb W n)`. -/
def sQ (Q W : IMat) (m n : Fin 4) : ℤ := - bf Q (sb W m) (sb W n)

theorem sQ_nonneg {Q W : IMat} (hob : ObSbase Q W) {m n : Fin 4} (h : m ≠ n) :
    0 ≤ sQ Q W m n := by
  have hh := hob m n h
  simp only [sQ]
  linarith

theorem sQ_comm {Q W : IMat} (hsym : Q.transpose = Q) (m n : Fin 4) :
    sQ Q W m n = sQ Q W n m := by
  simp only [sQ]
  rw [bf_comm Q hsym (sb W m) (sb W n)]

theorem sQ_eq_zero_iff {Q W : IMat} {m n : Fin 4} :
    sQ Q W m n = 0 ↔ bf Q (sb W m) (sb W n) = 0 := by
  simp [sQ]

theorem sQ_pos_iff {Q W : IMat} {m n : Fin 4} :
    0 < sQ Q W m n ↔ bf Q (sb W m) (sb W n) < 0 := by
  simp only [sQ, neg_pos]

/-- Parity of the `m`-th superbase coordinate of `y`. -/
def parity (y : IVec) (m : Fin 4) : ℤ := cons0 y m % 2

theorem parity_eq_zero_or_one (y : IVec) (m : Fin 4) : parity y m = 0 ∨ parity y m = 1 :=
  Int.emod_two_eq_zero_or_one _

/-- The parity lower bound `L(y) = ∑_{m<n} q_{mn} · [ε m ≠ ε n]`. -/
def Lb (Q W : IMat) (y : IVec) : ℤ :=
  ∑ p ∈ pairSet, sQ Q W p.1 p.2 * (if parity y p.1 = parity y p.2 then 0 else 1)

theorem Lb_eq_zero_of_no_graph {Q W : IMat} {y : IVec}
    (h : ∀ p ∈ pairSet, sQ Q W p.1 p.2 = 0) : Lb Q W y = 0 := by
  simp only [Lb]
  exact Finset.sum_eq_zero fun p hp => by rw [h p hp]; ring

theorem modEq_cons0 {y y' : IVec} (h : modEq y y') (m : Fin 4) :
    (2 : ℤ) ∣ cons0 y' m - cons0 y m := by
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩
  · simp [cons0]
  · simpa [cons0] using h i

theorem parity_cons0_mod (y : IVec) (m : Fin 4) :
    cons0 (fun i => y i % 2) m = parity y m := by
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩ <;> simp [cons0, parity]

theorem emod_two_sub_sq (a b : ℤ) : (a % 2 - b % 2) ^ 2 = (if a % 2 = b % 2 then 0 else 1) := by
  rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    rcases Int.emod_two_eq_zero_or_one b with hb | hb <;> rw [ha, hb] <;> norm_num

theorem modEq_emod_two (y : IVec) : modEq y (fun i => y i % 2) := fun i =>
  ⟨-(y i / 2), by have := Int.emod_add_mul_ediv (y i) 2; linarith⟩

end Work.SG
