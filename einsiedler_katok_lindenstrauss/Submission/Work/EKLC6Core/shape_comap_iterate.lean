import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.shape_comap_conj
import Submission.Work.EKLContract.All

/-!
# `EKLC6Core.shape_comap_iterate` — the shape of an iterated pull-back

The one-step identity `Work.EKLC6Core.shape_comap_conj` says that pulling back the plaque
algebra `A` along the diagonal map `φ = (aDiag t ·)` conjugates the shape by `aDiag t`:

`shape (comap φ A) U x = conjBy (-t) (shape A U (φ x))`.

Iterating this `n` times, and using that conjugation accumulates the exponent vector
(`conjBy s (conjBy u S) = conjBy (s + u) S`, `Work.EKLC6Core.conjBy_add`), gives

`shape (comap φⁿ A) U x = conjBy (-(n • t)) (shape A U (φⁿ x))`.

This is the "iterate covariance" bookkeeping used, e.g., in `EKLC6Core.atomInfo_chain`: it
turns the telescoped shape masses along the `a`-orbit into the shape mass of a single
contracted box.
-/

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Elementary scalar arithmetic for `Fin 3 → ℝ` -/

/-- `((n+1 : ℕ) : ℝ) • t = (n : ℝ) • t + t`. -/
theorem real_nsmul_succ {t : Fin 3 → ℝ} (n : ℕ) :
    (((n + 1 : ℕ) : ℝ)) • t = (n : ℝ) • t + t := by
  rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]

/-- `((n+1 : ℕ) : ℝ) • t = t + (n : ℝ) • t`. -/
theorem real_nsmul_succ' {t : Fin 3 → ℝ} (n : ℕ) :
    (((n + 1 : ℕ) : ℝ)) • t = t + (n : ℝ) • t := by
  rw [real_nsmul_succ]
  exact add_comm _ _

/-- `-t + -(n • t) = -((n+1) • t)`. -/
theorem neg_add_neg_real_nsmul {t : Fin 3 → ℝ} (n : ℕ) :
    -t + -((n : ℝ) • t) = -(((n + 1 : ℕ) : ℝ) • t) := by
  rw [real_nsmul_succ, neg_add]
  exact add_comm _ _

/-! ## The main iterate identity -/

theorem shape_comap_iterate {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    (t : Fin 3 → ℝ) (A : MeasurableSpace Work.EKLContract.X3) (n : ℕ) (x : Work.EKLContract.X3) :
    Work.EKLContract.shape
        (MeasurableSpace.comap ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) A) U x =
      Work.EKLC6Core.conjBy (-((n : ℝ) • t))
        (Work.EKLContract.shape A U ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n] x)) := by
  have key : ∀ n : ℕ, ∀ x : X3,
      shape (MeasurableSpace.comap ((fun y : X3 => aDiag t • y)^[n]) A) U x =
        conjBy (-((n : ℝ) • t)) (shape A U ((fun y : X3 => aDiag t • y)^[n] x)) := by
    intro n
    induction n with
    | zero =>
        intro x
        rw [Function.iterate_zero, MeasurableSpace.comap_id]
        simp
    | succ n ih =>
        intro x
        have hiter : ((fun y : X3 => aDiag t • y)^[n + 1])
            = ((fun y : X3 => aDiag t • y)^[n]) ∘ (fun y : X3 => aDiag t • y) :=
          Function.iterate_succ _ n
        have hA : MeasurableSpace.comap ((fun y : X3 => aDiag t • y)^[n + 1]) A
            = MeasurableSpace.comap (fun y : X3 => aDiag t • y)
                (MeasurableSpace.comap ((fun y : X3 => aDiag t • y)^[n]) A) := by
          rw [hiter]
          exact (MeasurableSpace.comap_comp (m := A)
            (f := (fun y : X3 => aDiag t • y)^[n])
            (g := fun y : X3 => aDiag t • y)).symm
        have hx : ((fun y : X3 => aDiag t • y)^[n + 1]) x
            = ((fun y : X3 => aDiag t • y)^[n]) ((fun y : X3 => aDiag t • y) x) :=
          Function.iterate_succ_apply _ n x
        rw [hA]
        rw [shape_comap_conj (A := MeasurableSpace.comap ((fun y : X3 => aDiag t • y)^[n]) A) hU t x]
        rw [ih ((fun y : X3 => aDiag t • y) x)]
        rw [hx, ← conjBy_add, neg_add_neg_real_nsmul]
  exact key n x

end Work.EKLC6Core
