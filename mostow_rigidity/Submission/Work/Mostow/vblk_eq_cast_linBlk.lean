import Mathlib
import Submission.Work.Mostow.euclidBlockDefs

/-!
# `vblk` agrees with `linBlk` transported along `k + (n - k) = n`

`Work.Mostow.linBlk k m R` is the linear block map on `E (k + m)` (first `k` coordinates fixed,
`R` applied to the last `m`).  `Work.Mostow.vblk k hk R` is the same map written directly in the
coordinates of `E n` (`m = n - k`): coordinates with value `< k` are fixed, the remaining ones are
mapped by `R` acting on the "tail" of the vector.

The statement proved here is the compatibility of the two descriptions: for `e : k + (n - k) = n`,
transporting `linBlk k (n - k) R` along `e` (and the input along `e.symm`) gives `vblk k hk R`.

The proof is a coordinate computation: `WithLp.ofLp_injective` reduces the identity in `E n` to an
identity of functions `Fin n → ℝ`, and `cast_ofLp` describes the coordinates of a vector
transported along an equality of the index type.  The coordinates of `linBlk` in the first block
(`Fin.castAdd`) and the last block (`Fin.natAdd`) are read off from `Fin.append_left` /
`Fin.append_right`, and are compared with the two cases of the `if` in `vblk`.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

/-- Coordinates of a vector of `E` transported along an equality of the index types: the cast is
the "identity" on coordinates, reindexing `Fin n` along `Fin.cast e.symm`. -/
private lemma cast_ofLp {m n : ℕ} (e : m = n) (x : E m) (i : Fin n) :
    (e ▸ x : E n).ofLp i = x.ofLp (Fin.cast e.symm i) := by
  cases e; rfl

/-- The first block of `linBlk` is unchanged. -/
private lemma linBlk_ofLp_castAdd (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) (i : Fin k) :
    (linBlk k m R u).ofLp (Fin.castAdd m i) = u.ofLp (Fin.castAdd m i) := by
  simp [linBlk, Fin.append_left]

/-- The last block of `linBlk` is `R` applied to the normal part of `u`. -/
private lemma linBlk_ofLp_natAdd (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) (i : Fin m) :
    (linBlk k m R u).ofLp (Fin.natAdd k i) = (R (nrmC k m u)).ofLp i := by
  simp [linBlk, nrmC, Fin.append_right]

/-- `linBlk` is the identity on the coordinates with value `< k`. -/
private lemma linBlk_ofLp_of_lt (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m))
    (i : Fin (k + m)) (h : (i : ℕ) < k) : (linBlk k m R u).ofLp i = u.ofLp i := by
  have hi : i = Fin.castAdd m ⟨i.val, h⟩ := Fin.ext rfl
  rw [hi, linBlk_ofLp_castAdd]

/-- On the coordinates with value `≥ k`, `linBlk` is `R` applied to the normal part. -/
private lemma linBlk_ofLp_of_ge (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m))
    (i : Fin (k + m)) (h : ¬ (i : ℕ) < k) :
    (linBlk k m R u).ofLp i = (R (nrmC k m u)).ofLp ⟨i.val - k, by have := i.isLt; omega⟩ := by
  have hle : k ≤ i.val := Nat.le_of_not_lt h
  have hi : i = Fin.natAdd k ⟨i.val - k, by have := i.isLt; omega⟩ := by
    refine Fin.ext ?_
    show i.val = k + (i.val - k)
    omega
  conv_lhs => rw [hi]
  rw [linBlk_ofLp_natAdd]

/-- The normal part of `vblk` is `R` applied to the tail of the vector. -/
private lemma nrmC_tailOf_cast {k n : ℕ} (e : k + (n - k) = n) (u : E n) :
    nrmC k (n - k) (e.symm ▸ u) = tailOf k u := by
  apply WithLp.ofLp_injective
  funext i
  simp only [nrmC, tailOf, WithLp.ofLp_toLp, cast_ofLp]
  exact congrArg u.ofLp (Fin.ext rfl)

theorem vblk_eq_cast_linBlk (k : ℕ) {n : ℕ} (hk : k ≤ n) (e : k + (n - k) = n)
    (R : Submission.Mostow.E (n - k) ≃ₗᵢ[ℝ] Submission.Mostow.E (n - k)) (u : Submission.Mostow.E n) :
    (e ▸ Work.Mostow.linBlk k (n - k) R (e.symm ▸ u) : Submission.Mostow.E n)
      = Work.Mostow.vblk k hk R u := by
  apply WithLp.ofLp_injective
  funext i
  rw [cast_ofLp]
  by_cases hi : (i : ℕ) < k
  · -- both sides keep the `i`-th coordinate
    rw [linBlk_ofLp_of_lt k (n - k) R (e.symm ▸ u) (Fin.cast e.symm i)
        (by rw [Fin.val_cast]; exact hi)]
    rw [cast_ofLp]
    rw [vblk_ofLp_of_lt k hk R u i hi]
    exact congrArg u.ofLp (Fin.ext rfl)
  · -- both sides apply `R` to the tail
    rw [linBlk_ofLp_of_ge k (n - k) R (e.symm ▸ u) (Fin.cast e.symm i)
        (by rw [Fin.val_cast]; exact hi)]
    rw [nrmC_tailOf_cast e u]
    rw [vblk_ofLp_of_ge k hk R u i hi]
    exact congrArg (fun j => (R (tailOf k u)).ofLp j) (Fin.ext rfl)

end

end Work.Mostow
