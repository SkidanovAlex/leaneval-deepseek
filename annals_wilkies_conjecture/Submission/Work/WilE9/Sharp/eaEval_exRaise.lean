import Mathlib
import Submission.Work.WilE9.Sharp.ExtSystem

set_option autoImplicit false
noncomputable section

namespace Work.WilE9.Sharp

open WilkiesDesign WilkiesDesign.E

/-! ## `eaEval` commutes with the reindexing of the extended system

`exRaise` renames the stratum's variables into the extended ambient (`y` at `exY`, `τ` at `exT`,
`aux` at `exA`) and `exChain` pushes the coefficients of the stratum's chain to the same
coordinates, putting `0` elsewhere.  Consequently, evaluating a raised polynomial in the raised
chain at a point `z` of the extended ambient is the same as evaluating the original polynomial in
the original chain at `exStrat z`, the point of the stratum's own ambient obtained by reading off
the coordinates `y, τ, aux`. -/

/-- The chain functions agree: pushing the coefficients of `c` to the coordinates `y, τ, aux` and
reading them at `z` is the same as reading the original coefficients at `exStrat z`. -/
lemma exChain_ell {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (j : Fin r)
    (z : Fin (Next n m) → ℝ) :
    (exChain c).ell j z = c.ell j (exStrat z) := by
  -- only the coordinate `sIdxE i` of `z` survives in the `i`-th coefficient
  have key : ∀ i : Fin (n + (1 + m)),
      ∑ l : Fin (Next n m), (if sIdxE n m i = l then c.a j i else 0) * z l
        = c.a j i * z (sIdxE n m i) := by
    intro i
    rw [Finset.sum_eq_single (sIdxE n m i)]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsum : (∑ l : Fin (Next n m),
        (∑ i : Fin (n + (1 + m)), if sIdxE n m i = l then c.a j i else 0) * z l)
      = ∑ i : Fin (n + (1 + m)), c.a j i * z (sIdxE n m i) := by
    calc ∑ l : Fin (Next n m),
            (∑ i : Fin (n + (1 + m)), if sIdxE n m i = l then c.a j i else 0) * z l
        = ∑ l : Fin (Next n m), ∑ i : Fin (n + (1 + m)),
            (if sIdxE n m i = l then c.a j i else 0) * z l := by
          simp [Finset.sum_mul]
      _ = ∑ i : Fin (n + (1 + m)), ∑ l : Fin (Next n m),
            (if sIdxE n m i = l then c.a j i else 0) * z l := by
          rw [Finset.sum_comm]
      _ = ∑ i : Fin (n + (1 + m)), c.a j i * z (sIdxE n m i) :=
          Finset.sum_congr rfl fun i _ => key i
  simp only [EAChain.ell, exChain, exStrat, hsum]

theorem eaEval_exRaise {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (P : WilkiesDesign.E.EAPoly (n + (1 + m)) r) (z : Fin (Work.WilE9.Sharp.Next n m) → ℝ) :
    WilkiesDesign.E.eaEval (Work.WilE9.Sharp.exChain c) (Work.WilE9.Sharp.exRaise P) z =
      WilkiesDesign.E.eaEval c P (Work.WilE9.Sharp.exStrat z) := by
  have hell : ∀ j : Fin r, (exChain c).ell j z = c.ell j (exStrat z) :=
    fun j => exChain_ell c j z
  -- the two evaluation functions on the variables of `EAPoly (n + (1 + m)) r` agree
  have hfun : (Sum.elim z fun j => Real.exp ((exChain c).ell j z)) ∘ Sum.map (sIdxE n m) id
      = Sum.elim (exStrat z) fun j => Real.exp (c.ell j (exStrat z)) := by
    funext s
    rcases s with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
      exact congrArg Real.exp (hell j)
  simp only [eaEval, exRaise, MvPolynomial.eval_rename, hfun]

end Work.WilE9.Sharp
