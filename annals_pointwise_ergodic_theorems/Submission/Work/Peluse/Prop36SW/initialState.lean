import Mathlib
import Submission.Work.Peluse.Prop36SW.parBoxSuccAverage
import Submission.Work.Peluse.Prop36SW.famNorm_eq_pDirFam
import Submission.Work.Peluse.Prop36SW.szZeroCardLe
import Submission.Work.Peluse.Prop36SW.averageAssembly
import Submission.Work.Peluse.Prop36SW.coreCompare

set_option maxHeartbeats 1600000

namespace Work.Peluse.Prop36SW

open Work.Peluse.UControl

noncomputable section

/-! ## The initial state of Peluse's §5 chain

This file proves the *initial state* of the `d - 1`-fold iteration of Lemma 5.7 whose state is
`LState`: the family average `D.famAvg d H c N f` of Proposition 3.4, restricted to the parameters at
which no slot coefficient `slotCoeff D d c (d-2) s (D.pad (d-1) ·)` vanishes, dominates the `LState`
average at the level `H + 1` of the window, with the explicit loss `2 ^ (1 + 2 · |I_{d-1}|)`.

The proof has four steps:

* the level-`d` box `D.parBox d H` is split, by the Fubini `parBoxSuccAverage`, into the level-
  `(d-1)` parameters `a` and the level-`(d-1)` slot coordinates `s` (each in `[-H,H]`), and the
  resulting box norm is identified with the ladder's `pDirFam` family at the coefficients
  `slotCoeff D d c (d-2) s (D.pad (d-1) a)` (`famNorm_eq_pDirFam`);
* the sign bridge (`sum_paramBox_boxNorm_abs`) replaces the coefficients by their absolute values
  (which is `LState`'s `p`) and the reindexing `average_piIcc_eq_average_paramBox` turns the average
  over the `s`-box into the average over the ladder's `paramBox (H+1)` (the same box, since
  `Ioo (-(H+1)) (H+1) = Icc (-H) H`); the window comparison `boxNorm_le_arithIcc_succ` then raises
  the window from `H` to `H+1` at the cost `(4^t)^{1/2^t}` (`t = |I_{d-1}|`); this is `coreCompare`;
* the parameters at which some slot coefficient vanishes carry mass at most `η/4 · |parBox (d-1) H|`
  by `hgood`, so restricting to the good set loses only the factor `2` (`filterAverage`), and the
  bookkeeping (including the two `LState` side conditions `0 < p` and `|p| M₁ M₂ ≤ N`, and the
  non-degeneracy `M₁ M₂ ≤ N`) is `averageAssembly` plus `hbound`;
* the good set is non-empty because otherwise `hgood` would force `4 ≤ η ≤ 1`. -/

/-- `x` lies in the symmetric interval `[-L,L]` when its absolute value is at most `L`. -/
private lemma mem_symIcc_of_natAbs_le {L : ℕ} {x : ℤ} (h : x.natAbs ≤ L) :
    x ∈ Work.Peluse.symIcc L := by
  have h1 : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h1
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  exact abs_le.mp h1

/-- If `x` lies outside the symmetric interval `[-L,L]`, then `L < |x|` (as a natural number). -/
private lemma lt_natAbs_of_notMem_symIcc {L : ℕ} {x : ℤ} (hx : x ∉ Work.Peluse.symIcc L) :
    L < x.natAbs := by
  by_contra h
  push_neg at h
  exact hx (mem_symIcc_of_natAbs_le h)

/-- The box norm of a `1`-bounded function supported in `[-N,N]`, taken on the box `symIcc N`, is at
most `1`. -/
lemma boxNorm_le_one_of_supportIn {t : ℕ} {Q : Fin t → Finset ℤ} {N : ℕ} {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsu : Work.Peluse.SupportIn f N) :
    Work.Peluse.boxNorm t Q (Work.Peluse.symIcc N) f ≤ 1 := by
  have h1 : Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc N) f ≤ 1 :=
    Work.Peluse.BoxNorm.boxNormPow_le_one hf
      (fun x hx => hsu x (lt_natAbs_of_notMem_symIcc hx))
  calc Work.Peluse.boxNorm t Q (Work.Peluse.symIcc N) f
      = (Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc N) f) ^ (1 / (2 : ℝ) ^ t) := rfl
    _ ≤ (1 : ℝ) ^ (1 / (2 : ℝ) ^ t) := Real.rpow_le_rpow (norm_nonneg _) h1 (by positivity)
    _ = 1 := Real.one_rpow _

end

end Work.Peluse.Prop36SW
