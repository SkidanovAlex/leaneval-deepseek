import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.euclidBlockDefs
import Submission.Work.Mostow.ellipticDefs
import Submission.Work.Mostow.vblk_eq_cast_linBlk
import Submission.Work.Mostow.rcRotN_eq_linBlk

/-!
# `Work.Mostow.strataAdaptRotN`

The rotation norm `rotN` of a linear isometry of `E m` is unchanged when the isometry is written
as the "value split" block map `vblk d hd T` (first `d` coordinates fixed, `T` applied to the
remaining `m - d` coordinates).

The operator norm of `diag (I_d, T) - 1` equals that of `T - 1`, because the fixed block
contributes nothing; the proof is carried out with the *displacement* form of `rotN`:

* `nib_apply_le_rotN` :  `‖R y - y‖ ≤ rotN R * ‖y‖`;
* `nib_rotN_le_of_unit`:  `(∀ y, ‖y‖ = 1 → ‖R y - y‖ ≤ K) → rotN R ≤ K`.

The value-split block map is the transport (`vblk_eq_cast_linBlk`) of the split block map
`linBlk d (m - d) T` along `e : d + (m - d) = m`, and the displacement of `linBlk` is the
displacement of `T` on the normal chart coordinate (`linBlk_sub_norm_eq`).
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

/-! ## Elementary cast bookkeeping along an equality of dimensions -/

private lemma cast_E_norm {a b : ℕ} (e : a = b) (u : E a) : ‖(e ▸ u : E b)‖ = ‖u‖ := by
  cases e; rfl

private lemma cast_E_sub {a b : ℕ} (e : a = b) (u v : E a) :
    (e ▸ (u - v) : E b) = e ▸ u - e ▸ v := by cases e; rfl

private lemma cast_E_symm_cast {a b : ℕ} (e : a = b) (u : E b) :
    (e ▸ (e.symm ▸ u) : E b) = u := by cases e; rfl

private lemma cast_E_cast_symm {a b : ℕ} (e : a = b) (u : E a) :
    (e.symm ▸ (e ▸ u) : E a) = u := by cases e; rfl

/-! ## The displacement of the linear block map -/

/-- The displacement of `linBlk k m R` at `u` is the displacement of `R` on the normal chart
coordinate `nrmC k m u` (the tangential coordinate is fixed, so it contributes nothing). -/
private lemma linBlk_sub_norm_eq (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    ‖linBlk k m R u - u‖ = ‖R (nrmC k m u) - nrmC k m u‖ := by
  have hsplit := nib_norm_sq_split k m (linBlk k m R u - u)
  have h1 : tanC k m (linBlk k m R u - u) = 0 := by ext i; simp [tanC, linBlk]
  have h2 : nrmC k m (linBlk k m R u - u) = R (nrmC k m u) - nrmC k m u := by
    ext i; simp [nrmC, linBlk]
  rw [h1, h2] at hsplit
  have h2' : ‖linBlk k m R u - u‖ ^ 2 = ‖R (nrmC k m u) - nrmC k m u‖ ^ 2 := by
    rw [hsplit]; simp
  calc ‖linBlk k m R u - u‖ = Real.sqrt (‖linBlk k m R u - u‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖R (nrmC k m u) - nrmC k m u‖ ^ 2) := by rw [h2']
    _ = ‖R (nrmC k m u) - nrmC k m u‖ := Real.sqrt_sq (norm_nonneg _)

/-- The normal chart coordinate is norm-decreasing. -/
private lemma nrmC_norm_le (k m : ℕ) (u : E (k + m)) : ‖nrmC k m u‖ ≤ ‖u‖ := by
  have h : ‖nrmC k m u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [nib_norm_sq_split k m u]; nlinarith [sq_nonneg ‖tanC k m u‖]
  calc ‖nrmC k m u‖ = Real.sqrt (‖nrmC k m u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖u‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖u‖ := Real.sqrt_sq (norm_nonneg _)

theorem strataAdaptRotN (d m : ℕ) (hd : d ≤ m)
    (T : Submission.Mostow.E (m - d) ≃ₗᵢ[ℝ] Submission.Mostow.E (m - d))
    (Q : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (hQ : ∀ y : Submission.Mostow.E m, Q y = Work.Mostow.vblk d hd T y) :
    Submission.Mostow.rotN T = Submission.Mostow.rotN Q := by
  set e : d + (m - d) = m := Nat.add_sub_of_le hd with he
  -- `Q` agrees with the transported split block map
  have hQlin : ∀ u : E m, Q u = e ▸ linBlk d (m - d) T (e.symm ▸ u) := by
    intro u
    rw [hQ u]
    exact (vblk_eq_cast_linBlk d hd e T u).symm
  -- the displacement of `Q` at `e ▸ u` is the transported displacement of `linBlk`
  have hdisp : ∀ u : E (d + (m - d)),
      Q (e ▸ u) - (e ▸ u) = e ▸ (linBlk d (m - d) T u - u) := by
    intro u
    have h1 : Q (e ▸ u) = e ▸ linBlk d (m - d) T u := by
      rw [hQlin (e ▸ u), cast_E_cast_symm]
    rw [h1, cast_E_sub]
  refine le_antisymm ?_ ?_
  · -- `rotN T ≤ rotN Q`
    have hQ0 : (0 : ℝ) ≤ rotN Q := norm_nonneg _
    refine (rcRotN_eq_linBlk d (m - d) T (K := rotN Q) hQ0).mpr ?_
    intro u
    have hlt : ‖linBlk d (m - d) T u - u‖ = ‖Q (e ▸ u) - (e ▸ u)‖ := by
      rw [hdisp u, cast_E_norm]
    rw [hlt]
    calc ‖Q (e ▸ u) - (e ▸ u)‖
        ≤ rotN Q * ‖e ▸ u‖ := nib_apply_le_rotN m Q (e ▸ u)
      _ = rotN Q * ‖u‖ := by rw [cast_E_norm]
  · -- `rotN Q ≤ rotN T`
    refine nib_rotN_le_of_unit (norm_nonneg _) ?_
    intro u hu
    have h1 : Q u - u = e ▸ (linBlk d (m - d) T (e.symm ▸ u) - (e.symm ▸ u)) := by
      rw [hQlin u, cast_E_sub]
      congr 1
      exact (cast_E_symm_cast e u).symm
    rw [h1, cast_E_norm, linBlk_sub_norm_eq]
    calc ‖T (nrmC d (m - d) (e.symm ▸ u)) - nrmC d (m - d) (e.symm ▸ u)‖
        ≤ rotN T * ‖nrmC d (m - d) (e.symm ▸ u)‖ := nib_apply_le_rotN (m - d) T _
      _ ≤ rotN T * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            calc ‖nrmC d (m - d) (e.symm ▸ u)‖ ≤ ‖(e.symm ▸ u : E (d + (m - d)))‖ :=
                  nrmC_norm_le d (m - d) _
              _ = ‖u‖ := cast_E_norm e.symm u
              _ = 1 := hu
      _ = rotN T := mul_one _

end

end Work.Mostow
