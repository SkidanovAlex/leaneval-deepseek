import Mathlib
import Submission.Work.Peluse.TransferUp.RawPowDefs
import Submission.Work.Peluse.TransferUp.boxNormPow_transfer_up
import Submission.Work.Peluse.UControl.piecePetSetup

/-!
# Collapsing the direction AP of a uniformity norm to the support window

`Work.Peluse.uNormPow t (arithIcc 1 L) (symIcc M) f` is the `2^t`-th power of Peluse's uniformity
norm of `f` over the single step set `[L] = {1,…,L}` and the window `symIcc M = [-M,M]`.

The lemma below says that for `f` supported in `[-M,M]` with `M ≥ 1` and any `L ≥ 2M+1`, the norm
at the *long* step set `[L]` dominates the norm at the *collapsed* step set `[2M+1]`, up to the
factor `((2M+1)/L)^t`.  Equivalently (see the proof), the quantity

`M_t(H) := H^t · ‖f‖^{2^t}_{U^t_{[H]}(symIcc M)}`

is nondecreasing in `H`: this is exactly `Work.Peluse.TransferUp.Npow_mono`, the monotonicity of the
`ψ`-kernel normalised box-norm power, which holds for an arbitrary finitely supported `f` and an
arbitrary window of positive cardinality — no support-diameter hypothesis is needed.

Indeed, writing `b_H := uNormPow t (arithIcc 1 H) (symIcc M) f` and
`Npow t (fun _ => 1) (symIcc M) f H = |symIcc M| · H^t · b_H`, the monotonicity of `H ↦ Npow … H`
gives `K^t b_K ≤ L^t b_L` for `K ≤ L`; dividing by `L^t` turns this into the statement with `C = 1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Prop36SW

open Work.Peluse

/-- The quantity `Npow t (fun _ => 1) S f H` of the transfer-up chapter is, definitionally, the
window cardinality times `H^t` times the uniformity-norm power at the step set `arithIcc 1 H`. -/
private lemma npow_one_eq (t : ℕ) (M H : ℕ) (f : ℤ → ℂ) :
    Work.Peluse.TransferUp.Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f H
      = (((Work.Peluse.symIcc M).card : ℝ) * (H : ℝ) ^ t)
        * Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) H) (Work.Peluse.symIcc M) f := by
  simp only [Work.Peluse.TransferUp.Npow, Work.Peluse.uNormPow]

/-- The window `symIcc M` is nonempty. -/
private lemma symIcc_card_pos (M : ℕ) : 0 < (Work.Peluse.symIcc M).card := by
  rw [Work.Peluse.symIcc]
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  simp only [Finset.mem_Icc]
  omega

theorem uNormPowCollapsePlain {t : ℕ} (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ M → 2 * M + 1 ≤ L →
      Work.Peluse.SupportIn f M → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        C * (((2 * M + 1 : ℕ) : ℝ) / (L : ℝ)) ^ t
            * Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1)) (Work.Peluse.symIcc M) f
          ≤ Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M) f := by
  refine ⟨1, one_pos, ?_⟩
  intro L M f _hM hKL hsup _hb
  -- monotonicity of the `ψ`-kernel normalised box-norm power
  have hS : 0 < (Work.Peluse.symIcc M).card := symIcc_card_pos M
  have hKpos : 1 ≤ 2 * M + 1 := by omega
  have hmono := Work.Peluse.TransferUp.Npow_mono t ht (fun _ : Fin t => (1 : ℤ))
      (fun _ => one_ne_zero) (Work.Peluse.symIcc M) hS f
      (Work.Peluse.FinSuppZ.of_supportIn hsup) (H' := 2 * M + 1) (H := L) hKpos hKL
  rw [npow_one_eq t M (2 * M + 1) f, npow_one_eq t M L f] at hmono
  -- cancel the (positive) window cardinality
  have hSpos : (0 : ℝ) < ((Work.Peluse.symIcc M).card : ℝ) := by exact_mod_cast hS
  have hmono' : ((Work.Peluse.symIcc M).card : ℝ)
        * (((2 * M + 1 : ℕ) : ℝ) ^ t
            * Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1))
                (Work.Peluse.symIcc M) f)
      ≤ ((Work.Peluse.symIcc M).card : ℝ)
        * ((L : ℝ) ^ t
            * Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M) f) := by
    simpa only [mul_assoc] using hmono
  have h2 : ((2 * M + 1 : ℕ) : ℝ) ^ t
        * Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1)) (Work.Peluse.symIcc M) f
      ≤ (L : ℝ) ^ t
        * Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M) f :=
    le_of_mul_le_mul_left hmono' hSpos
  -- divide by `L^t`
  have hLpos : 0 < L := by omega
  have hLpow : (0 : ℝ) < (L : ℝ) ^ t := pow_pos (by exact_mod_cast hLpos) t
  have h3 : (((2 * M + 1 : ℕ) : ℝ) / (L : ℝ)) ^ t
        * Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1)) (Work.Peluse.symIcc M) f
      ≤ Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M) f := by
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hLpow]
    exact h2.trans_eq (mul_comm _ _)
  simpa only [one_mul] using h3

end Work.Peluse.Prop36SW
