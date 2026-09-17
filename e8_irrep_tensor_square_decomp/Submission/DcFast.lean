import Submission.E8Engine

/-!
# A kernel-fast dominant-conjugate algorithm

`Submission.E8Orbit.dcX` (and its fast twin `Submission.E8Engine.dcXE`) represent a weight as a
*function* `Fin 8 → ℤ`.  Each reflection builds a new closure `fun j => v j - v i * …`, so after `k`
reflections the evaluation of one coordinate walks a chain of `k` closures: the cost of the whole
algorithm is **quadratic** in the number of reflections (measured: `≈ 30 ms` per reflection for
weights needing `≈ 18` reflections, instead of the `≈ 0.1 ms` a single reflection should cost).

This file represents the weight as an explicit `8`-tuple `W8`, so every reflection is a constant
amount of work and the algorithm is linear.  `dcWE` is proved equal to `dcXE` (hence to `dcX` and
`dc`), and is used for the c-table certificates.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section

namespace Submission.DcFast

open Submission.E8Orbit Submission.E8Character Submission.E8Engine Submission.WeylWeights

/-- A weight, as an explicit `8`-tuple. -/
structure W8 where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  x5 : ℤ
  x6 : ℤ
  x7 : ℤ

/-- The underlying function of an `8`-tuple. -/
def fun' (w : W8) : Fin 8 → ℤ := fun i =>
  if (i : ℕ) = 0 then w.x0 else if (i : ℕ) = 1 then w.x1 else
  if (i : ℕ) = 2 then w.x2 else if (i : ℕ) = 3 then w.x3 else
  if (i : ℕ) = 4 then w.x4 else if (i : ℕ) = 5 then w.x5 else
  if (i : ℕ) = 6 then w.x6 else w.x7

/-- The `8`-tuple of a weight. -/
def mk' (v : Fin 8 → ℤ) : W8 := ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7⟩

@[simp] lemma fun'_mk' (v : Fin 8 → ℤ) : fun' (mk' v) = v := by
  funext i
  fin_cases i <;> rfl

@[simp] lemma mk'_fun' (w : W8) : mk' (fun' w) = w := by
  rcases w with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rfl

/-- The simple reflection on the `8`-tuple, using the sparsity of the `E₈` Cartan matrix (every
node has at most three neighbours). -/
def srefW (i : Fin 8) (w : W8) : W8 :=
  if (i : ℕ) = 0 then
    ⟨-w.x0, w.x1, w.x2 + w.x0, w.x3, w.x4, w.x5, w.x6, w.x7⟩
  else if (i : ℕ) = 1 then
    ⟨w.x0, -w.x1, w.x2, w.x3 + w.x1, w.x4, w.x5, w.x6, w.x7⟩
  else if (i : ℕ) = 2 then
    ⟨w.x0 + w.x2, w.x1, -w.x2, w.x3 + w.x2, w.x4, w.x5, w.x6, w.x7⟩
  else if (i : ℕ) = 3 then
    ⟨w.x0, w.x1 + w.x3, w.x2 + w.x3, -w.x3, w.x4 + w.x3, w.x5, w.x6, w.x7⟩
  else if (i : ℕ) = 4 then
    ⟨w.x0, w.x1, w.x2, w.x3 + w.x4, -w.x4, w.x5 + w.x4, w.x6, w.x7⟩
  else if (i : ℕ) = 5 then
    ⟨w.x0, w.x1, w.x2, w.x3, w.x4 + w.x5, -w.x5, w.x6 + w.x5, w.x7⟩
  else if (i : ℕ) = 6 then
    ⟨w.x0, w.x1, w.x2, w.x3, w.x4, w.x5 + w.x6, -w.x6, w.x7 + w.x6⟩
  else
    ⟨w.x0, w.x1, w.x2, w.x3, w.x4, w.x5, w.x6 + w.x7, -w.x7⟩

lemma fun'_srefW (i : Fin 8) (w : W8) : fun' (srefW i w) = srefE i (fun' w) := by
  funext j
  rcases w with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  fin_cases i <;> fin_cases j <;>
    simp only [fun', srefW, srefE, e8e, Pi.sub_apply] <;>
    (norm_num <;> ring)

/-- `srefW` on an explicit tuple agrees with `srefE`. -/
lemma srefW_mk' (i : Fin 8) (v : Fin 8 → ℤ) : srefW i (mk' v) = mk' (srefE i v) := by
  have h := fun'_srefW i (mk' v)
  rw [fun'_mk'] at h
  have := congrArg mk' h
  rwa [mk'_fun'] at this

/-- The first coordinate of `fun' w` that is negative, computed with `pickNegF` (which is cheap
enough once the state is an explicit tuple). -/
def pickNegW (w : W8) : Option (Fin 8) := pickNegF (fun' w)

lemma pickNegW_mk' (v : Fin 8 → ℤ) : pickNegW (mk' v) = pickNegF v := by
  simp only [pickNegW, fun'_mk']

/-- `n` steps of the reflection algorithm, on explicit tuples. -/
def dclW : ℕ → W8 → W8
  | 0, w => w
  | n + 1, w => match pickNegW w with
      | some i => dclW n (srefW i w)
      | none => w

lemma dclW_mk' : ∀ (n : ℕ) (v : Fin 8 → ℤ), dclW n (mk' v) = mk' (dclE n v) := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
      intro v
      rw [dclW, dclE, pickNegW_mk']
      cases h : pickNegF v with
      | none => rfl
      | some i =>
          simp only [h]
          rw [srefW_mk', ih]

/-- The kernel-fast dominant conjugate: linear in the number of reflections. -/
def dcWE (v : Fin 8 → ℤ) : Fin 8 → ℤ := fun' (dclW 130 (mk' v))

lemma dcWE_eq_dcXE (v : Fin 8 → ℤ) : dcWE v = dcXE v := by
  rw [dcWE, dclW_mk', fun'_mk', dcXE]

lemma dcWE_eq (v : Fin 8 → ℤ) : dcWE v = dcX v := by
  rw [dcWE_eq_dcXE, dcXE_eq]

end Submission.DcFast
