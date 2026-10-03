/-
Auxiliary objects for Peluse's Lemma 2.3 / the Gowers--Cauchy--Schwarz inequality for the
Gowers box norm of `Submission/Work/Peluse/Basic.lean`.

For `t : ℕ`, `Q : Fin t → Finset ℤ` and `W : Finset ℤ` we write `Tuple t Q` for the set of
integer tuples `z` with `z i ∈ Q i`, and define the *box form*

  `winForm t Q W φ = ∑_{z, z' ∈ Tuple t Q} ∑_{x ∈ W} ∏_{ω : Fin t → Bool} C^{|ω|} φ_ω (x + σ(corner z z' ω))`

where `C` is complex conjugation (rendered by `star`), `corner z z' ω` is the coordinatewise
choice of `z`/`z'` along `ω`, and `σ` is the sum of the coordinates.  Keeping the `x`-sum inside
a window `W` keeps every sum finite; for finitely supported `φ_ω` the `tsum` over `ℤ` agrees with
the sum over a large enough window, which is how the main theorem transports the windowed
inequality back to `prodCubeSum`.
-/
import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.BoxNorm

noncomputable section

/-- Integer tuples over the coordinate sets `Q`: a `t`-tuple `z` with `z i ∈ Q i`. -/
abbrev Tuple (t : ℕ) (Q : Fin t → Finset ℤ) : Type := (i : Fin t) → {x : ℤ // x ∈ Q i}

namespace Tuple

variable {t : ℕ} {Q : Fin t → Finset ℤ}

/-- The `ω`-corner of the box with sides `z, z'`: coordinatewise choice. -/
def corner (z z' : Tuple t Q) (ω : Fin t → Bool) : Tuple t Q := fun i => if ω i then z i else z' i

/-- The sum of the coordinates of a tuple. -/
def total (z : Tuple t Q) : ℤ := ∑ i, (z i).1

/-- The tail of an `(n+1)`-tuple. -/
def tail {n : ℕ} {Q : Fin (n+1) → Finset ℤ} (z : Tuple (n+1) Q) :
    Tuple n (fun i => Q i.succ) := fun i => z i.succ

end Tuple

/-- The box form of Peluse's Definition 2.1 over the window `W`. -/
def winForm (t : ℕ) (Q : Fin t → Finset ℤ) (W : Finset ℤ)
    (φ : (Fin t → Bool) → ℤ → ℂ) : ℂ :=
  ∑ z : Tuple t Q, ∑ z' : Tuple t Q, ∑ x ∈ W,
    ∏ ω : Fin t → Bool, (star^[weight ω]) (φ ω (x + Tuple.total (Tuple.corner z z' ω)))

/-- The `2^t`-th root of the box form of a single function. -/
def winNorm (t : ℕ) (Q : Fin t → Finset ℤ) (W : Finset ℤ) (g : ℤ → ℂ) : ℝ :=
  ‖winForm t Q W (fun _ => g)‖ ^ (1 / (2 : ℝ) ^ t)

/-- The box form really is the paper's expression in terms of `cornerShift`. -/
lemma cornerShift_eq_total {t : ℕ} {Q : Fin t → Finset ℤ} (z z' : Tuple t Q)
    (ω : Fin t → Bool) :
    Work.Peluse.cornerShift (fun i => (z i).1) (fun i => (z' i).1) ω
      = Tuple.total (Tuple.corner z z' ω) := by
  unfold Work.Peluse.cornerShift Tuple.total Tuple.corner
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ω i <;> simp [h]

/-- `weight` as a sum of indicators. -/
lemma weight_eq_sum {n : ℕ} (ω : Fin n → Bool) :
    weight ω = ∑ i : Fin n, (if ω i then 1 else 0) := by
  rw [Work.Peluse.weight, Finset.card_filter]

/-- `weight` splits off the first coordinate. -/
lemma weight_cases {n : ℕ} (ω : Fin n → Bool) (β : Bool) :
    weight (Fin.cases β ω : Fin (n+1) → Bool) = weight ω + (if β then 1 else 0) := by
  have h1 : weight (Fin.cases β ω : Fin (n+1) → Bool)
      = ∑ i : Fin (n+1), (if (Fin.cases β ω : Fin (n+1) → Bool) i then 1 else 0) :=
    weight_eq_sum _
  have h2 : weight ω = ∑ i : Fin n, (if ω i then 1 else 0) := weight_eq_sum _
  rw [h1, h2, Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  exact add_comm _ _

/-- The total of a tuple built by `Fin.cases`. -/
lemma total_cases {n : ℕ} {Q : Fin (n+1) → Finset ℤ} (a : {x : ℤ // x ∈ Q 0})
    (w : Tuple n (fun i => Q i.succ)) :
    Tuple.total (Fin.cases a w) = a.1 + Tuple.total w := by
  simp only [Tuple.total, Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]

/-- The corner of a tuple built by `Fin.cases`. -/
lemma corner_cases {n : ℕ} {Q : Fin (n+1) → Finset ℤ} (z z' : Tuple (n+1) Q)
    (β : Bool) (ω : Fin n → Bool) :
    Tuple.corner z z' (Fin.cases β ω : Fin (n+1) → Bool)
      = Fin.cases (if β then z 0 else z' 0)
          (Tuple.corner (Tuple.tail z) (Tuple.tail z') ω) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp only [Tuple.corner, Fin.cases_zero]
    by_cases h : β <;> simp [h]
  · intro j
    simp only [Tuple.corner, Tuple.tail, Fin.cases_succ]
    by_cases h : ω j <;> simp [h]

/-- The total of the corner splits as well. -/
lemma total_corner_cases {n : ℕ} {Q : Fin (n+1) → Finset ℤ} (z z' : Tuple (n+1) Q)
    (β : Bool) (ω : Fin n → Bool) :
    Tuple.total (Tuple.corner z z' (Fin.cases β ω : Fin (n+1) → Bool))
      = (if β then (z 0).1 else (z' 0).1)
        + Tuple.total (Tuple.corner (Tuple.tail z) (Tuple.tail z') ω) := by
  rw [corner_cases, total_cases]
  by_cases h : β <;> simp [h]

/-- Splitting `(n+1)`-tuples into the first coordinate and the tail. -/
def tupleEquiv (n : ℕ) (Q : Fin (n+1) → Finset ℤ) :
    Tuple (n+1) Q ≃ {x : ℤ // x ∈ Q 0} × Tuple n (fun i => Q i.succ) where
  toFun z := (z 0, Tuple.tail z)
  invFun p := Fin.cases p.1 p.2
  left_inv z := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl
  right_inv p := by
    obtain ⟨a, w⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨Fin.cases_zero, ?_⟩
    funext i
    exact Fin.cases_succ i

/-- `star^[n]` is multiplicative. -/
lemma star_iterate_mul (n : ℕ) (z w : ℂ) :
    (star^[n]) (z * w) = (star^[n]) z * (star^[n]) w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, star_mul, mul_comm]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- `star^[n]` commutes with conjugation. -/
lemma star_iterate_conj (n : ℕ) (z : ℂ) :
    (star^[n]) (star z) = star ((star^[n]) z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']

/-- `star^[n+1] = star^[n] ∘ star`. -/
lemma star_iterate_succ (n : ℕ) (z : ℂ) : (star^[n+1]) z = (star^[n]) (star z) :=
  Function.iterate_succ_apply _ _ _

/-- `star^[0]` and `star^[1]` evaluated. -/
lemma star_iterate_zero (z : ℂ) : (star^[0]) z = z := rfl

end

end Work.Peluse.BoxNorm
