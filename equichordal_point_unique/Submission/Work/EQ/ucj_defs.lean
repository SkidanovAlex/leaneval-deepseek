import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.bwdFanSheets

/-! # Helpers for `Work.EQ.regular_of_uncountable_junction`

The target lemma converts an uncountable junction set of the value `C` into a regular component
of value `C`.  The chain that realises the component is the "candidate chain" of
`Submission.Work.EQ.CycleDefs`, except that its middle `N` coordinates (the labelled backward
iterates of the stable fan) are replaced by an arbitrary family of analytic maps which satisfy
the backward recursion.  In the application those maps are the locally analytic *sheets* of
`Submission.Work.EQ.bwdFanSheets`, which satisfy the same recursion and agree with the labelled
maps on the junction set.

* `ucjChain` is that chain;
* `ucj_eqRelC_bchild` records that a child of `Q` computed with **any** square root of `Q`'s
  radicand is a legitimate predecessor of `Q` in the equichordal relation. -/

namespace Work.EQ

open Filter _root_.Topology Complex Metric

noncomputable section

/-- **The chain with a prescribed "middle".**  Indices `j ≥ 0` carry the forward fan of `ε`
(the principal germ beyond depth `N`), the index `-k` for `1 ≤ k ≤ N` carries `g k z`, and the
indices `j < -N` carry the mirrored fan of `η`.  The parameters are `ψ₁ = z` and `ψ₂ = C/z`, so
the invariant parameter is `C`. -/
def ucjChain (a : ℝ) (h : ℂ → ℂ) (ε η _s : List Bool) (N : ℕ) (C : ℂ)
    (g : ℕ → ℂ → ℂ × ℂ) (z : ℂ) : ChainData :=
  (fun j : ℤ =>
    if 0 ≤ j then
      (if (j.toNat ≤ N) then fan a h (ε.drop j.toNat) (((eqLam a : ℝ) : ℂ) ^ j * z)
       else germC a h (((eqLam a : ℝ) : ℂ) ^ j * z))
    else
      (if (-j).toNat ≤ N then g ((-j).toNat) z
       else eqMirror (fan a h (η.drop ((-j).toNat - N))
              (((eqLam a : ℝ) : ℂ) ^ ((-j).toNat : ℤ) * (C / z)))), z, C / z)

@[simp] theorem ucjChain_psi1 (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (C : ℂ)
    (g : ℕ → ℂ → ℂ × ℂ) (z : ℂ) : (ucjChain a h ε η s N C g z).2.1 = z := rfl

@[simp] theorem ucjChain_psi2 (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (C : ℂ)
    (g : ℕ → ℂ → ℂ × ℂ) (z : ℂ) : (ucjChain a h ε η s N C g z).2.2 = C / z := rfl

/-- The value of `ucjChain` at an index, unfolded (definitional). -/
theorem ucjChain_fst_apply (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (C : ℂ)
    (g : ℕ → ℂ → ℂ × ℂ) (z : ℂ) (j : ℤ) :
    (ucjChain a h ε η s N C g z).1 j =
      (if 0 ≤ j then
        (if j.toNat ≤ N then fan a h (ε.drop j.toNat) (((eqLam a : ℝ) : ℂ) ^ j * z)
         else germC a h (((eqLam a : ℝ) : ℂ) ^ j * z))
      else
        (if (-j).toNat ≤ N then g ((-j).toNat) z
         else eqMirror (fan a h (η.drop ((-j).toNat - N))
                (((eqLam a : ℝ) : ℂ) ^ ((-j).toNat : ℤ) * (C / z))))) := rfl

/-- **A child with a valid root is a predecessor.**  If `ρ` is any square root of the radicand
`bsq (subO1 a Q) ≠ 0`, then `bchild a t ρ Q` is a predecessor of `Q` in the equichordal relation
(the two choices of `ρ` correspond to the two labels). -/
theorem ucj_eqRelC_bchild {a : ℝ} {Q : ℂ × ℂ} {t : Bool} {ρ : ℂ}
    (hρ : ρ ^ 2 = bsq (subO1 a Q)) (h : bsq (subO1 a Q) ≠ 0) :
    EqRelC a (bchild a (if t then (1 : ℂ) else -1) ρ Q) Q := by
  have h2 : ρ ^ 2 = (brho (subO1 a Q)) ^ 2 := by rw [brho_sq]; exact hρ
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with hρ' | hρ'
  · rw [hρ', ← invBranch_eq_bchild]
    exact eqRelC_invBranch t h
  · have hneg : bchild a (if t then (1 : ℂ) else -1) (-(brho (subO1 a Q))) Q
        = bchild a (-(if t then (1 : ℂ) else -1)) (brho (subO1 a Q)) Q := by
      refine Prod.ext ?_ ?_ <;> simp only [bchild] <;> rw [div_neg] <;> ring
    have hc : (-(if t then (1 : ℂ) else -1)) = (if (!t) then (1 : ℂ) else -1) := by
      cases t <;> norm_num
    rw [hρ', hneg, hc, ← invBranch_eq_bchild]
    exact eqRelC_invBranch (!t) h

end

end Work.EQ
