import Mathlib
import Submission.Work.Pert.Walk
import Submission.Work.Pert.RBlock7.retPShift
import Submission.Work.Pert.DphiShift
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.DphiP_open

/-!
# `Work.Pert.RetPEquiv` — the `R_equiv` slot of the `PertDataWalk` constructor

`NOTES_pert2_session15.md` §5.39/§5.40: with `Q := Qm Ξ α` for `retDR` and the waist
`Qm Ξ α ∩ Qp Ξ α = retWa (Qm Ξ α) α` for `retP`, the field `R_equiv` is

`IsTEquivariantOn (retP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) α) (retDR f Df τ Φ (Qm Ξ α) α)`

of which the first conjunct is `retDR_isTInvariant` (§5.21) fed `isTInvariant_DphiP` (§5.17), and
the second is `retP_add_one` (§RBlock7) applied pointwise.  Reviewers: "correct as stated";
one proved it in two lines.  The hypotheses are characterised as in §5.40.
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-- **`R_equiv` for the tail rewrite**: `retP` on the waist is `T`-equivariant on `retDR`. -/
theorem retP_isTEquivariantOn_retDR {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ F : ℂ → ℂ} {Ξ : ℝ} {α : ℂ}
    (hinj : Set.InjOn Φ (Qm Ξ α))
    (hab : ∀ z ∈ Qm Ξ α, F z ∈ Qm Ξ α → Φ (F z) = Φ z + 1)
    (hOrb : ∀ z ∈ Qm Ξ α, ∀ z' ∈ Qm Ξ α, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Qm Ξ α) ∧ F^[k] z = z')
    (hcomm : ∀ x : ℂ, F (Tt α x) = Tt α (F x))
    (hDphi : MandelDim.IsTInvariant (DphiP f Df τ Φ (Qm Ξ α)))
    (hG : ∀ w ∈ retDR f Df τ Φ (Qm Ξ α) α, GoodP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) w)
    (hG1 : ∀ w ∈ retDR f Df τ Φ (Qm Ξ α) α, GoodP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) (w + 1))
    (hw : ∀ w ∈ retDR f Df τ Φ (Qm Ξ α) α,
      ∀ j : ℕ, j ≤ mIdxP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) w + 1 →
        F^[j] (invOn Φ (Qm Ξ α ∩ Qp Ξ α)
          (w - (mIdxP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) w : ℂ))) ∈ Qp Ξ α)
    (hw1 : ∀ w ∈ retDR f Df τ Φ (Qm Ξ α) α,
      ∀ j : ℕ, j ≤ mIdxP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) (w + 1) →
        F^[j] (invOn Φ (Qm Ξ α ∩ Qp Ξ α)
          (w + 1 - (mIdxP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) (w + 1) : ℂ))) ∈ Qp Ξ α) :
    MandelDim.IsTEquivariantOn (retP f Df τ Φ (Qm Ξ α ∩ Qp Ξ α) α)
      (retDR f Df τ Φ (Qm Ξ α) α) :=
  ⟨retDR_isTInvariant hDphi,
    fun w hw' => Work.Pert.RBlock7.retP_add_one hinj hab hOrb hcomm (hG w hw') (hG1 w hw') (hw w hw') (hw1 w hw')⟩

/-- **`retP` agrees with `retOf` on the fundamental piece** (5.41): for `w ∈ Φ '' Q` the minimal
level is `0`, so `mIdxP = 0` and the two functions coincide.  This is the only bookkeeping step of
`R_holo` that is not already a supplied lemma (`retOf_holo` on `U`, `retP_add_one` for `hper`,
`differentiableOn_tSat` for the saturation). -/
theorem mIdxP_eq_zero_of_mem_image {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (hw : w ∈ Φ '' Q) : mIdxP f Df τ Φ Q w = 0 := by
  classical
  have hG : GoodP f Df τ Φ Q w :=
    ⟨0, by simpa using hw, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rw [mIdxP, dite_eq_left hG]
  exact (Nat.find_eq_zero hG).mpr ⟨by simpa using hw, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- **Step 2 of `R_holo`'s composition (5.42)**: on the fundamental piece `Φ '' Q` the return map
`retP` agrees with the raw `retOf` (the level index is `0`), which is what lets `retOf_holo` --
proved on `Φ '' (Qm Ξ α ∩ Qp Ξ α)` -- be used as the base of the saturation transfer. -/
theorem retP_eq_retOf_of_mem_image {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {α w : ℂ}
    (hw : w ∈ Φ '' Q) : retP f Df τ Φ Q α w = retOf Φ Q α w := by
  rw [retP, retOf, mIdxP_eq_zero_of_mem_image (f := f) (Df := Df) (τ := τ) (Q := Q) hw]
  simp

/-- **Step 1 of `R_holo`'s composition (5.42)**: the waist image `Φ '' (Qm Ξ α ∩ Qp Ξ α)` is open,
by the open mapping theorem (`Work.Pert.isOpen_image_of_deriv_ne_zero`) at the waist.  The two gate
openness facts are kept as hypotheses (`isOpen_Qm`-style facts exist per gate, `RBlock4/retOf_holo.lean:93`). -/
theorem isOpen_image_waist {Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ}
    (hQm : IsOpen (Qm Ξ α)) (hQp : IsOpen (Qp Ξ α))
    (hΦ : DifferentiableOn ℂ Φ (Qm Ξ α ∩ Qp Ξ α))
    (hder : ∀ z ∈ Qm Ξ α ∩ Qp Ξ α, deriv Φ z ≠ 0) :
    IsOpen (Φ '' (Qm Ξ α ∩ Qp Ξ α)) :=
  isOpen_image_of_deriv_ne_zero (hQm.inter hQp) hΦ hder

end

end Work.Pert
