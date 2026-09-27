import Mathlib
import Submission.Work.Mostow.euclidBlockDefs
import Submission.Work.Mostow.ellipticAux
import Submission.Work.Mostow.vblk_eq_cast_linBlk
import Submission.Work.Mostow.rotCanonAux

/-!
# `blk` is compatible with a refinement of the normal block (version for the `geeS` chain)

Setting: `k, m, r : ℕ` with `r ≤ m`, `RB : E m ≃ₗᵢ[ℝ] E m` fixing the first `r` coordinates and
`RS : E (m - r) ≃ₗᵢ[ℝ] E (m - r)` acting on the remaining ones, i.e. `RB u = vblk r hr RS u`
for all `u : E m`.

Then the block element with normal part `RB` in dimension `k + m` agrees with the block element
with normal part `RS` in dimension `(k + r) + (m - r)`, transported along the equality
`e : (k + r) + (m - r) = k + m` of ambient dimensions.

The proof is: both sides are elements of `PO (k + m) 1`, which acts faithfully
(`Work.Mostow.po_ext`), so it suffices to compare their actions on the chart `E (k + m)`.
By `Work.Mostow.blk_smul_linBlk` each side acts as the corresponding linear block map
`Work.Mostow.linBlk` (the first `k` — resp. `k + r` — coordinates are kept, the rest is acted on by
`RB` — resp. `RS`), and the two linear maps are compared coordinatewise
(`cast_linBlk_eq` below).  `hRB` turns the action of `RB` on the tail into the value-split block
map `Work.Mostow.vblk`.

This file deliberately imports only the light `euclidBlockDefs`/`ellipticAux` chain, so that the
`geeS` development does not have to pull in the heavy `geodDeps` closure.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## Coordinates of `linBlk` -/

/-- The first block of `linBlk` is kept as it is. -/
private lemma linBlk_ofLp_castAdd (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) (i : Fin k) :
    (linBlk k m R u).ofLp (Fin.castAdd m i) = u.ofLp (Fin.castAdd m i) := by
  simp [linBlk, Fin.append_left]

/-- The last block of `linBlk` is `R` applied to the tail. -/
private lemma linBlk_ofLp_natAdd (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) (j : Fin m) :
    (linBlk k m R u).ofLp (Fin.natAdd k j)
      = (R (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j')))).ofLp j := by
  simp [linBlk, Fin.append_right]

/-! ## The coordinate identity -/

/-- `linBlk k m RB` is the transport of `linBlk (k+r) (m-r) RS` along `e`, when `RB` is the
value-split block map of `RS` on `E m`. -/
private lemma cast_linBlk_eq (k m r : ℕ) (hr : r ≤ m) (e : (k + r) + (m - r) = k + m)
    (RB : E m ≃ₗᵢ[ℝ] E m) (RS : E (m - r) ≃ₗᵢ[ℝ] E (m - r))
    (hRB : ∀ u : E m, RB u = vblk r hr RS u) (u : E (k + m)) :
    (e ▸ linBlk (k + r) (m - r) RS (e.symm ▸ u) : E (k + m)) = linBlk k m RB u := by
  apply WithLp.ofLp_injective
  funext i
  rw [cast_applyX ((k + r) + (m - r)) (k + m) e]
  by_cases hi : (i : ℕ) < k
  · -- the first `k` coordinates are kept by both sides
    have hf : (finCongr e.symm) i = Fin.castAdd (m - r) (⟨i.val, by omega⟩ : Fin (k + r)) :=
      Fin.ext rfl
    rw [hf, linBlk_ofLp_castAdd (k + r) (m - r) RS (e.symm ▸ u) ⟨i.val, by omega⟩]
    rw [cast_applyX' ((k + r) + (m - r)) (k + m) e u]
    have key : (linBlk k m RB u).ofLp i = u.ofLp i := by
      have h1 := linBlk_ofLp_castAdd k m RB u ⟨i.val, hi⟩
      rwa [show (Fin.castAdd m ⟨i.val, hi⟩ : Fin (k + m)) = i from Fin.ext rfl] at h1
    rw [key]
    exact congrArg u.ofLp (Fin.ext (by simp))
  · have hk : k ≤ (i : ℕ) := Nat.le_of_not_lt hi
    by_cases hi2 : (i : ℕ) < k + r
    · -- coordinates `k ≤ i < k + r`: both sides keep them (`RB` fixes them via `vblk` of `< r`)
      have hf : (finCongr e.symm) i = Fin.castAdd (m - r) (⟨i.val, hi2⟩ : Fin (k + r)) :=
        Fin.ext rfl
      rw [hf, linBlk_ofLp_castAdd (k + r) (m - r) RS (e.symm ▸ u) ⟨i.val, hi2⟩]
      rw [cast_applyX' ((k + r) + (m - r)) (k + m) e u]
      have hj : i.val - k < m := by omega
      have hi3 : i = Fin.natAdd k (⟨i.val - k, hj⟩ : Fin m) :=
        Fin.ext (by rw [Fin.val_natAdd]; exact (Nat.add_sub_cancel' hk).symm)
      have key : (linBlk k m RB u).ofLp i
          = (RB (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j')))).ofLp
              ⟨i.val - k, hj⟩ := by
        conv_lhs => rw [hi3]
        exact linBlk_ofLp_natAdd k m RB u ⟨i.val - k, hj⟩
      rw [key, hRB (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j')))]
      have hj3 : (i.val - k : ℕ) < r := by omega
      rw [vblk_ofLp_of_lt r hr RS (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j')))
            ⟨i.val - k, hj⟩ (show ((⟨i.val - k, hj⟩ : Fin m).val : ℕ) < r from hj3)]
      exact congrArg u.ofLp (Fin.ext (by rw [Fin.val_natAdd]; exact (Nat.add_sub_cancel' hk).symm))
    · -- coordinates `i ≥ k + r`: both sides apply `RS` to the tail
      have hf : (finCongr e.symm) i
          = Fin.natAdd (k + r) (⟨i.val - (k + r), by omega⟩ : Fin (m - r)) := by
        apply Fin.ext
        show (i.val : ℕ) = (k + r) + (i.val - (k + r))
        omega
      rw [hf, linBlk_ofLp_natAdd (k + r) (m - r) RS (e.symm ▸ u) ⟨i.val - (k + r), by omega⟩]
      have hj : i.val - k < m := by omega
      have hi3 : i = Fin.natAdd k (⟨i.val - k, hj⟩ : Fin m) :=
        Fin.ext (by rw [Fin.val_natAdd]; exact (Nat.add_sub_cancel' hk).symm)
      have key : (linBlk k m RB u).ofLp i
          = (RB (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j')))).ofLp
              ⟨i.val - k, hj⟩ := by
        conv_lhs => rw [hi3]
        exact linBlk_ofLp_natAdd k m RB u ⟨i.val - k, hj⟩
      rw [key, hRB (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j')))]
      have hj3 : ¬ (i.val - k : ℕ) < r := by omega
      rw [vblk_ofLp_of_ge r hr RS (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j')))
            ⟨i.val - k, hj⟩ (show ¬ ((⟨i.val - k, hj⟩ : Fin m).val : ℕ) < r from hj3)]
      -- the vector `RS` is applied to is the same in both descriptions
      have hT : (WithLp.toLp 2 (fun j'' : Fin (m - r) => (e.symm ▸ u).ofLp (Fin.natAdd (k + r) j'')))
          = tailOf r (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j'))) := by
        apply WithLp.ofLp_injective
        funext j''
        rw [cast_applyX' ((k + r) + (m - r)) (k + m) e u, tailOf_ofLp]
        exact congrArg u.ofLp (Fin.ext (by show (k + r) + (j'' : ℕ) = k + (r + (j'' : ℕ)); omega))
      rw [hT]
      have hidx : (⟨i.val - (k + r), by omega⟩ : Fin (m - r)) = ⟨(i.val - k) - r, by omega⟩ :=
        Fin.ext (Nat.sub_sub _ _ _).symm
      exact congrArg (fun ii : Fin (m - r) =>
        (RS (tailOf r (WithLp.toLp 2 (fun j' : Fin m => u.ofLp (Fin.natAdd k j'))))).ofLp ii) hidx

/-! ## The main result -/

theorem geeSVblkCastEq (k m r : ℕ) (hr : r ≤ m) (e : (k + r) + (m - r) = k + m)
    (RB : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (RS : Submission.Mostow.E (m - r) ≃ₗᵢ[ℝ] Submission.Mostow.E (m - r))
    (hRB : ∀ u : Submission.Mostow.E m, RB u = Work.Mostow.vblk r hr RS u) :
    (e ▸ (Submission.Mostow.blk (k + r) (m - r) 1 RS :
      LeanEval.Geometry.MostowRigidity.PO ((k + r) + (m - r)) 1)
      : LeanEval.Geometry.MostowRigidity.PO (k + m) 1)
    = (Submission.Mostow.blk k m 1 RB : LeanEval.Geometry.MostowRigidity.PO (k + m) 1) := by
  apply po_ext (POBasic.ofProp (rcPOActionProp (k + m)))
  intro u
  have h1 : ((e ▸ (blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1)) : PO (k + m) 1) • u
      = (e ▸ ((blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1) • (e.symm ▸ u)) :
          E (k + m)) := by
    have h := cast_smul_po e (blk (k + r) (m - r) 1 RS) (e.symm ▸ u)
    rwa [cast_symm_cast] at h
  rw [h1, blk_smul_linBlk (k + r) (m - r) (rcPOActionProp (k + r))
        (rcPOActionProp ((k + r) + (m - r))) (rcHypIsometryProp ((k + r) + (m - r)))
        RS (e.symm ▸ u)]
  rw [blk_smul_linBlk k m (rcPOActionProp k) (rcPOActionProp (k + m))
        (rcHypIsometryProp (k + m)) RB u]
  exact cast_linBlk_eq k m r hr e RB RS hRB u

end

end Work.Mostow
