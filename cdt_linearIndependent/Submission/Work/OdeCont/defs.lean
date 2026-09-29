import Mathlib

/-!
# Definitions for the local existence theorem for linear ODE systems

We set up the vocabulary used by `Work.OdeCont.local_existence`: the right-hand side
`odeField A b z x` of the linear system `X' = A(z)X + b(z)`, and the Picard iterates
along the straight segment from the initial point `z₀`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.OdeCont

/-- The right-hand side of the linear system `X' = A(z)X + b(z)`:
`odeField A b z x i = ∑_j A z i j * x j + b z i`. -/
def odeField {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (z : ℂ) (x : Fin k → ℂ) : Fin k → ℂ :=
  fun i => (Finset.univ.sum (fun j => A z i j * x j)) + b z i

/-- Picard iterates, in a normed complex vector space `V`, for the initial value problem
`X' = F(z, X)`, `X z₀ = y`, integrating along the straight segment from `z₀`. -/
def iter {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) : ℕ → ℂ → V
  | 0 => fun _ => y
  | (n+1) => fun z =>
      y + ∫ t in (0:ℝ)..1,
        (z - z₀) • F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀)))

/-- The candidate solution obtained as the limit of the Picard iterates (via the telescoping
series of successive differences). -/
def iterLimit {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) : ℂ → V :=
  fun z => iter F z₀ y 0 z + ∑' n, (iter F z₀ y (n+1) z - iter F z₀ y n z)

/-- The sequence `0, F z (X 0 z), F z (X 1 z), …` whose `N`-th term is the `N`-th partial sum
of the telescoping series of derivatives of the Picard differences. -/
def Hz {k : ℕ} (F : ℂ → (Fin k → ℂ) → (Fin k → ℂ)) (z₀ : ℂ) (y : Fin k → ℂ) (z : ℂ) :
    ℕ → (Fin k → ℂ)
  | 0 => 0
  | (n+1) => F z (iter F z₀ y n z)

@[simp] lemma Hz_zero {k : ℕ} (F : ℂ → (Fin k → ℂ) → (Fin k → ℂ)) (z₀ : ℂ) (y : Fin k → ℂ)
    (z : ℂ) : Hz F z₀ y z 0 = 0 := rfl

@[simp] lemma Hz_succ {k : ℕ} (F : ℂ → (Fin k → ℂ) → (Fin k → ℂ)) (z₀ : ℂ) (y : Fin k → ℂ)
    (z : ℂ) (n : ℕ) : Hz F z₀ y z (n+1) = F z (iter F z₀ y n z) := rfl

@[simp] lemma iterLimit_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) (z : ℂ) :
    iterLimit F z₀ y z =
      iter F z₀ y 0 z + ∑' n, (iter F z₀ y (n+1) z - iter F z₀ y n z) := rfl

/-- The Picard iterates for the linear system `X' = A(z)X + b(z)`. -/
def picardIter {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (z₀ : ℂ) (y : Fin k → ℂ) : ℕ → ℂ → (Fin k → ℂ) :=
  iter (fun w x => odeField A b w x) z₀ y

@[simp] lemma iter_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) (z : ℂ) : iter F z₀ y 0 z = y := rfl

lemma iter_succ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) (n : ℕ) (z : ℂ) :
    iter F z₀ y (n+1) z =
      y + ∫ t in (0:ℝ)..1,
        (z - z₀) • F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀))) := rfl

@[simp] lemma picardIter_zero {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (z₀ : ℂ) (y : Fin k → ℂ) (z : ℂ) : picardIter A b z₀ y 0 z = y := rfl

lemma picardIter_succ {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (z₀ : ℂ) (y : Fin k → ℂ) (n : ℕ) (z : ℂ) :
    picardIter A b z₀ y (n+1) z =
      y + ∫ t in (0:ℝ)..1,
        (z - z₀) • odeField A b (z₀ + t • (z - z₀)) (picardIter A b z₀ y n (z₀ + t • (z - z₀))) := rfl

end Work.OdeCont
