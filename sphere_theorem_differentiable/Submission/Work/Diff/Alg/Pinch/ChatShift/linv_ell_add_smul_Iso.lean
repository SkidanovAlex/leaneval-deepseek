import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Böhm–Wilking inverse of a tensor shifted by a multiple of the round sphere

`linv a' b'` is the explicit inverse of the Böhm–Wilking transform `ell a' b'`.  The point of this
statement is that for an algebraic curvature tensor `S` the inverse of `ell a b S + t • Iso n`
can be computed *explicitly in terms of `S`*: the shift by `t • Iso n` only produces

* a `Ric₀ ∧ id`-term with coefficient `chSg1 n b b' = (b - b')/(1 + (n-2)b')`, and
* an `Iso`-term with coefficient `chSg2 n a a' t (scalAlg S) = (t + 2·scalAlg S·(a-a')/n)/(1+2(n-1)a')`.

This is the identity documented in `Submission/Work/Diff/Alg/Pinch/ChatShiftDefs.lean`; it is used
to push the "shift inclusion" into the `Dpic`-picture.

The proof uses only linearity of `linv`, the computations `ric0 (ell a b S) = (1+(n-2)b) • ric0 S`
(`ric0_ell_linv`), `scalAlg (ell a b S) = (1+2(n-1)a)·scalAlg S` (`scalAlg_ell_of_ne`),
`ric0 (Iso n) = 0` (`ric0_iso`), `scalAlg (Iso n) = n(n-1)` (`scalAlg_iso`) and
`knProd (id2 n) (id2 n) = 2 • Iso n` (`knProd_id2_id2`), followed by a componentwise
`field_simp`/`ring`.
-/

namespace Work.Diff.Alg.Pinch.ChatShift

open Finset Submission.Diff.Alg

theorem linv_ell_add_smul_Iso (n : ℕ) {a b a' b' t : ℝ} {S : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a' ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b' ≠ 0) :
    Work.Diff.Alg.Pinch.linv a' b' (Work.Diff.Alg.Pinch.ell a b S + t • Submission.Diff.Alg.Iso n)
      = S + Work.Diff.Alg.Pinch.chSg1 n b b' •
            Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric0 S) (Work.Diff.Alg.Pinch.id2 n)
          + Work.Diff.Alg.Pinch.chSg2 n a a' t (Submission.Diff.Alg.scalAlg S) •
            Submission.Diff.Alg.Iso n := by
  -- `n = 0` is degenerate: `Curv4 0` is a subsingleton.
  rcases eq_or_ne n 0 with hn0 | hn
  · subst hn0
    exact Subsingleton.elim _ _
  · have hnR : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn
    -- `Ric₀` and `scalAlg` of `ell a b S`
    have hric0ell : Work.Diff.Alg.Pinch.ric0 (Work.Diff.Alg.Pinch.ell a b S)
        = (1 + ((n : ℝ) - 2) * b) • Work.Diff.Alg.Pinch.ric0 S := by
      funext i j
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Work.Diff.Alg.Pinch.ric0_ell_linv n a b hnR hS i j
    have hscalell : Submission.Diff.Alg.scalAlg (Work.Diff.Alg.Pinch.ell a b S)
        = (1 + 2 * ((n : ℝ) - 1) * a) * Submission.Diff.Alg.scalAlg S :=
      Work.Diff.Alg.Pinch.scalAlg_ell_of_ne n a b hnR hS
    -- the same for the shifted tensor `ell a b S + t • Iso n`
    have hric0Y : Work.Diff.Alg.Pinch.ric0 (Work.Diff.Alg.Pinch.ell a b S + t • Submission.Diff.Alg.Iso n)
        = (1 + ((n : ℝ) - 2) * b) • Work.Diff.Alg.Pinch.ric0 S := by
      rw [Work.Diff.Alg.Pinch.ric0_add', Work.Diff.Alg.Pinch.ric0_smul', hric0ell,
        Work.Diff.Alg.Pinch.ric0_iso, smul_zero, add_zero]
    have hscalY : Submission.Diff.Alg.scalAlg
          (Work.Diff.Alg.Pinch.ell a b S + t • Submission.Diff.Alg.Iso n)
        = (1 + 2 * ((n : ℝ) - 1) * a) * Submission.Diff.Alg.scalAlg S
          + t * ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [Work.Diff.Alg.Pinch.scalAlg_add_linv, Work.Diff.Alg.Pinch.scalAlg_smul_linv,
        hscalell, Work.Diff.Alg.Pinch.scalAlg_iso]
    -- unfold `linv`, `ell` and the coefficients `chSg1`, `chSg2`
    rw [Work.Diff.Alg.Pinch.linv, hric0Y, hscalY, Work.Diff.Alg.Pinch.knProd_smul_left_linv,
      Work.Diff.Alg.Pinch.ell, Work.Diff.Alg.Pinch.knProd_id2_id2, Work.Diff.Alg.Pinch.chSg1,
      Work.Diff.Alg.Pinch.chSg2]
    -- name the two denominators so that `field_simp` can discharge them by assumption
    set Bb : ℝ := 1 + ((n : ℝ) - 2) * b' with hBbd
    set A' : ℝ := 1 + 2 * ((n : ℝ) - 1) * a' with hA'd
    have hBbnz : Bb ≠ 0 := by rw [hBbd]; exact hb
    have hA'nz : A' ≠ 0 := by rw [hA'd]; exact ha
    funext i j k l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    rw [hBbd, hA'd]
    ring

end Work.Diff.Alg.Pinch.ChatShift
