import Submission.Work.NielsenAlign
import Submission.Work.NielsenResidual

open Submission.FreeGroupAut
open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# The residual condition in `align` form

With the quantitative shortening criterion `norm_mul_lt_iff`
(`NielsenAlign.lean`) an *end cancellation* — `|w_i · w_j^{±1}| < |w_i|` —
is exactly a claim about `align` and the tail length of the multiplier:
multiplying `w_j` onto the right of `w_i` shortens `w_i` iff strictly more
than half of `w_j` cancels against the tail of `w_i`.  This file restates the
right-handed end-cancellation half of the residual configuration
(`NoEndCancel`, see `NielsenResidual.lean`) in that `align` form and proves
the easy directional pieces (`right_shorter_iff`, `right_inv_shorter_iff` and
their negations under `NoEndCancel`).  This is the vocabulary in which the
open conjugation mechanism of `double_coset_shortens` must be analysed; the
left-handed variants reduce to these by inversion.
-/

namespace Submission.Nielsen

noncomputable section

variable {n : ℕ}

/-- In `align` form: more than half of `w_j` cancels against the tail of
`w_i`, i.e. right-multiplying `w_i` by `w_j` shortens it. -/
def RightShorter (α : MulAut (FreeGroup (Fin n))) (i j : Fin n) : Prop :=
  2 * align (FreeGroup.toWord (α (FreeGroup.of i)))
        (FreeGroup.toWord (α (FreeGroup.of j)))
    > (FreeGroup.toWord (α (FreeGroup.of j))).length

/-- In `align` form: more than half of `w_j⁻¹` cancels against the tail of
`w_i`, i.e. right-multiplying `w_i` by `w_j⁻¹` shortens it. -/
def RightInvShorter (α : MulAut (FreeGroup (Fin n))) (i j : Fin n) : Prop :=
  2 * align (FreeGroup.toWord (α (FreeGroup.of i)))
        (FreeGroup.toWord ((α (FreeGroup.of j))⁻¹))
    > (FreeGroup.toWord ((α (FreeGroup.of j))⁻¹)).length

/-- `RightShorter` is exactly the norm-inequality `|w_i·w_j| < |w_i|`. -/
theorem right_shorter_iff (α : MulAut (FreeGroup (Fin n))) (i j : Fin n) :
    RightShorter α i j ↔
      FreeGroup.norm (α (FreeGroup.of i) * α (FreeGroup.of j))
        < FreeGroup.norm (α (FreeGroup.of i)) := by
  simpa [RightShorter] using
    (norm_mul_lt_iff (u := α (FreeGroup.of i)) (v := α (FreeGroup.of j))).symm

/-- `RightInvShorter` is exactly the norm-inequality `|w_i·w_j⁻¹| < |w_i|`. -/
theorem right_inv_shorter_iff (α : MulAut (FreeGroup (Fin n))) (i j : Fin n) :
    RightInvShorter α i j ↔
      FreeGroup.norm (α (FreeGroup.of i) * (α (FreeGroup.of j))⁻¹)
        < FreeGroup.norm (α (FreeGroup.of i)) := by
  simpa [RightInvShorter] using
    (norm_mul_lt_iff (u := α (FreeGroup.of i)) (v := (α (FreeGroup.of j))⁻¹)).symm

/-- Under `NoEndCancel` no right-handed end cancellation occurs, in `align`
form: not more than half of `w_j` (nor of `w_j⁻¹`) cancels against the tail
of `w_i`. -/
theorem noEndCancel_right_no_align {α : MulAut (FreeGroup (Fin n))}
    (h : NoEndCancel n α) {i j : Fin n} (hij : i ≠ j) :
    ¬ RightShorter α i j ∧ ¬ RightInvShorter α i j := by
  constructor
  · intro hr
    have hlt : FreeGroup.norm (α (FreeGroup.of i) * α (FreeGroup.of j))
        < FreeGroup.norm (α (FreeGroup.of i)) := (right_shorter_iff α i j).1 hr
    have hge : FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm (α (FreeGroup.of i) * α (FreeGroup.of j)) := (h i j hij).2.1
    omega
  · intro hr
    have hlt : FreeGroup.norm (α (FreeGroup.of i) * (α (FreeGroup.of j))⁻¹)
        < FreeGroup.norm (α (FreeGroup.of i)) := (right_inv_shorter_iff α i j).1 hr
    have hge : FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm (α (FreeGroup.of i) * (α (FreeGroup.of j))⁻¹) := (h i j hij).1
    omega

/-- The automorphism-image basis generates the whole free group: every basis
generator `a_k` is a word in the images `w_j = α(a_j)`.  (This is the
"the `w_j` generate `F_n`" ingredient of the conjugation analysis of
`double_coset_shortens`, automatic for automorphism images.) -/
theorem basis_generates (n : ℕ) (α : MulAut (FreeGroup (Fin n))) (k : Fin n) :
    FreeGroup.of k ∈ Subgroup.closure (Set.range (fun j : Fin n => α (FreeGroup.of j))) := by
  let C : Subgroup (FreeGroup (Fin n)) :=
    Subgroup.closure (Set.range (fun j : Fin n => α (FreeGroup.of j)))
  have hall : ∀ u : FreeGroup (Fin n), α u ∈ C := by
    intro u
    refine Subgroup.closure_induction
      (k := Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)))
      (p := fun x _ => α x ∈ C) ?mem ?one ?mul ?inv (x := u) ?hu
    · intro x hx
      rcases hx with ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨j, rfl⟩
    · change ((α : FreeGroup (Fin n) →* FreeGroup (Fin n)) (1 : FreeGroup (Fin n))) ∈ C
      rw [(α : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_one]
      exact C.one_mem
    · intro x y hx hy hxα hyα
      change ((α : FreeGroup (Fin n) →* FreeGroup (Fin n)) (x * y)) ∈ C
      rw [(α : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_mul]
      change α x * α y ∈ C
      exact C.mul_mem hxα hyα
    · intro x hx hxα
      change ((α : FreeGroup (Fin n) →* FreeGroup (Fin n)) (x⁻¹)) ∈ C
      rw [(α : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_inv]
      exact C.inv_mem hxα
    · rw [FreeGroup.closure_range_of]
      trivial
  have hback : α (α⁻¹ (FreeGroup.of k)) = FreeGroup.of k := by
    simpa using congrArg (fun φ : MulAut (FreeGroup (Fin n)) => φ (FreeGroup.of k))
      (mul_inv_cancel α)
  have mem : α (α⁻¹ (FreeGroup.of k)) ∈ C := hall (α⁻¹ (FreeGroup.of k))
  rwa [hback] at mem


/-! ## The left-handed `align`-form variants (mirrors by inversion)

The left-handed end cancellations `|w_j^{±1} · w_i| < |w_i|` are the
`lam`/`lamNeg` half of the residual configuration.  By inversion
(`norm (x⁻¹) = norm x`, `(a·b)⁻¹ = b⁻¹·a⁻¹`) they reduce to the right-handed
criterion of `norm_mul_lt_iff` applied to the inverted words: shortening
`w_i` on the left by `w_j` is the same as shortening `w_i⁻¹` on the right by
`w_j⁻¹`.  This defines the mirror predicates `LeftShorter`/`LeftInvShorter`,
proves their norm-inequality characterisation (`left_shorter_iff`,
`left_inv_shorter_iff`), and the negations forced by `NoEndCancel`
(`noEndCancel_left_no_align`), completing the full `align`-form description
of the residual configuration (`noEndCancel_align`). -/

/-- In `align` form: more than half of `w_j⁻¹` cancels against the head of
`w_i⁻¹`, i.e. left-multiplying `w_i` by `w_j` shortens it. -/
def LeftShorter (α : MulAut (FreeGroup (Fin n))) (i j : Fin n) : Prop :=
  2 * align (FreeGroup.toWord ((α (FreeGroup.of i))⁻¹))
        (FreeGroup.toWord ((α (FreeGroup.of j))⁻¹))
    > (FreeGroup.toWord ((α (FreeGroup.of j))⁻¹)).length

/-- In `align` form: more than half of `w_j` cancels against the head of
`w_i⁻¹`, i.e. left-multiplying `w_i` by `w_j⁻¹` shortens it. -/
def LeftInvShorter (α : MulAut (FreeGroup (Fin n))) (i j : Fin n) : Prop :=
  2 * align (FreeGroup.toWord ((α (FreeGroup.of i))⁻¹))
        (FreeGroup.toWord (α (FreeGroup.of j)))
    > (FreeGroup.toWord (α (FreeGroup.of j))).length

/-- `LeftShorter` is exactly the norm-inequality `|w_j·w_i| < |w_i|`. -/
theorem left_shorter_iff (α : MulAut (FreeGroup (Fin n))) (i j : Fin n) :
    LeftShorter α i j ↔
      FreeGroup.norm (α (FreeGroup.of j) * α (FreeGroup.of i))
        < FreeGroup.norm (α (FreeGroup.of i)) := by
  unfold LeftShorter
  have hmul := (norm_mul_lt_iff (u := (α (FreeGroup.of i))⁻¹)
      (v := (α (FreeGroup.of j))⁻¹)).symm
  rw [hmul]
  have hEq : FreeGroup.norm ((α (FreeGroup.of i))⁻¹ * (α (FreeGroup.of j))⁻¹)
      = FreeGroup.norm (α (FreeGroup.of j) * α (FreeGroup.of i)) := by
    rw [← mul_inv_rev, norm_inv_eq]
  have hEqI : FreeGroup.norm ((α (FreeGroup.of i))⁻¹)
      = FreeGroup.norm (α (FreeGroup.of i)) := norm_inv_eq
  rw [hEq, hEqI]

theorem left_inv_shorter_iff (α : MulAut (FreeGroup (Fin n))) (i j : Fin n) :
    LeftInvShorter α i j ↔
      FreeGroup.norm ((α (FreeGroup.of j))⁻¹ * α (FreeGroup.of i))
        < FreeGroup.norm (α (FreeGroup.of i)) := by
  unfold LeftInvShorter
  have hmul := (norm_mul_lt_iff (u := (α (FreeGroup.of i))⁻¹)
      (v := α (FreeGroup.of j))).symm
  rw [hmul]
  have hEq : FreeGroup.norm ((α (FreeGroup.of i))⁻¹ * α (FreeGroup.of j))
      = FreeGroup.norm ((α (FreeGroup.of j))⁻¹ * α (FreeGroup.of i)) := by
    have h1 : ((α (FreeGroup.of j))⁻¹ * α (FreeGroup.of i))⁻¹
        = (α (FreeGroup.of i))⁻¹ * α (FreeGroup.of j) := by
      rw [mul_inv_rev, inv_inv]
    rw [← h1, norm_inv_eq]
  have hEqI : FreeGroup.norm ((α (FreeGroup.of i))⁻¹)
      = FreeGroup.norm (α (FreeGroup.of i)) := norm_inv_eq
  rw [hEq, hEqI]

theorem noEndCancel_left_no_align {α : MulAut (FreeGroup (Fin n))}
    (h : NoEndCancel n α) {i j : Fin n} (hij : i ≠ j) :
    ¬ LeftShorter α i j ∧ ¬ LeftInvShorter α i j := by
  constructor
  · intro hl
    have hlt : FreeGroup.norm (α (FreeGroup.of j) * α (FreeGroup.of i))
        < FreeGroup.norm (α (FreeGroup.of i)) := (left_shorter_iff α i j).1 hl
    have hge : FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm (α (FreeGroup.of j) * α (FreeGroup.of i)) := (h i j hij).2.2.2
    omega
  · intro hl
    have hlt : FreeGroup.norm ((α (FreeGroup.of j))⁻¹ * α (FreeGroup.of i))
        < FreeGroup.norm (α (FreeGroup.of i)) := (left_inv_shorter_iff α i j).1 hl
    have hge : FreeGroup.norm (α (FreeGroup.of i))
        ≤ FreeGroup.norm ((α (FreeGroup.of j))⁻¹ * α (FreeGroup.of i)) := (h i j hij).2.2.1
    omega

/-- The full residual configuration in `align` form: under `NoEndCancel`, for
every pair `i ≠ j` none of the four end cancellations occurs — none of
`RightShorter`, `RightInvShorter`, `LeftShorter`, `LeftInvShorter`. -/
theorem noEndCancel_align {α : MulAut (FreeGroup (Fin n))} :
    NoEndCancel n α ↔
      ∀ i j : Fin n, i ≠ j →
        ¬ RightShorter α i j ∧ ¬ RightInvShorter α i j ∧
          ¬ LeftShorter α i j ∧ ¬ LeftInvShorter α i j := by
  constructor
  · intro h i j hij
    rcases noEndCancel_right_no_align h hij with ⟨hr, hri⟩
    rcases noEndCancel_left_no_align h hij with ⟨hl, hli⟩
    exact ⟨hr, hri, hl, hli⟩
  · intro hall i j hij
    rcases hall i j hij with ⟨hr, hri, hl, hli⟩
    constructor
    · by_contra hlt
      exact hri ((right_inv_shorter_iff α i j).2 (by omega))
    constructor
    · by_contra hlt
      exact hr ((right_shorter_iff α i j).2 (by omega))
    constructor
    · by_contra hlt
      exact hli ((left_inv_shorter_iff α i j).2 (by omega))
    · by_contra hlt
      exact hl ((left_shorter_iff α i j).2 (by omega))

end

end Submission.Nielsen
