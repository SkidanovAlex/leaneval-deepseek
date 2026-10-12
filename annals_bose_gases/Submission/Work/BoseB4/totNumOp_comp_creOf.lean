import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.Ann_cre_ccr
import Submission.Work.BoseB4.Cre_cre_comm
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.totNumOp_comp_creOf` — the number operator and creation

On the real bosonic Fock space `RealFock m` over `m` modes
(`Submission/Work/BoseB4/RealFock.lean`), with the single-mode creation and
annihilation operators `cre m l`, `ann m l` (`Submission/Work/BoseB4/RealFock.lean`)
and the superposed creation operator `creOf m v = Σ_l v_l · cre m l`
(`Submission/Work/BoseB4/ModeFock.lean`), this module proves the mode-system identity

    `[N, creOf m v] = creOf m v`,   i.e.  `N ∘ a†(v) = a†(v) ∘ N + a†(v)`,

for the total number operator `N = totNumOp m = Σ_i a_i† a_i`
(`Submission/Work/BoseB4/DGamma.lean`).  Equivalently: creating a particle in the
superposition `v` raises the total particle number by one, so `a†(v)` intertwines
`N` with `N + 1`.

The proof is entirely the canonical commutation relation: in the occupation-number
model the one-mode operators satisfy `[a_l, a_{l'}^†] = δ_{ll'}`
(`Work.BoseB4.Ann_cre_ccr`) and the creation operators of distinct modes commute
(`Work.BoseB4.Cre_cre_comm`).  Writing `N = Σ_i a_i†a_i`, term by term

    a_i†a_i a_l† = a_i†(a_l† a_i + δ_{il}) = a_l† a_i† a_i + δ_{il} a_l†,

so summing over `i` gives `N a_l† = a_l† N + a_l†` for a single mode, and the
general superposition `creOf m v = Σ_l v_l · a_l†` follows by linearity.

The device for turning these operator identities into Lean proofs: `Module.End ℝ M`
is a (noncommutative) semiring whose multiplication *is* `LinearMap.comp`, so all
the algebraic manipulations are carried out with `*` (and the sum lemmas
`Finset.sum_mul`, `Finset.mul_sum`); the rewrite lemmas of the corpus are stated
with `.comp`, so they are first re-stated in `*` form via `have` (the two are
definitionally equal).
-/

namespace Work.BoseB4

open scoped BigOperators

set_option autoImplicit false

/-- The single-mode relation `N a_l† = a_l† N + a_l†`, where `N = totNumOp m` is the
total number operator and `a_l† = cre m l` creates one quantum in mode `l`. -/
private lemma totNumOp_mul_cre (m : ℕ) (l : Fin m) :
    totNumOp m * cre m l = cre m l * totNumOp m + cre m l := by
  have hstep : ∀ i : Fin m, modeNumOp m i * cre m l
      = cre m l * modeNumOp m i + (if i = l then (1 : ℝ) else 0) • cre m i := by
    intro i
    change cre m i * ann m i * cre m l
        = cre m l * (cre m i * ann m i) + (if i = l then (1 : ℝ) else 0) • cre m i
    have h : ann m i * cre m l
        = cre m l * ann m i
          + (if i = l then (1 : ℝ) else 0) • (1 : Module.End ℝ (RealFock m)) :=
      Ann_cre_ccr i l
    have hCC : cre m i * cre m l = cre m l * cre m i := Cre_cre_comm i l
    rw [mul_assoc, h, mul_add, mul_smul_comm, mul_one]
    rw [← mul_assoc, hCC, mul_assoc]
  rw [totNumOp, Finset.sum_mul]
  rw [show (∑ i : Fin m, modeNumOp m i * cre m l)
        = ∑ i : Fin m,
            (cre m l * modeNumOp m i + (if i = l then (1 : ℝ) else 0) • cre m i)
      from Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.mul_sum]
  · rw [Finset.sum_eq_single l]
    · simp
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ l) h

theorem totNumOp_comp_creOf (m : ℕ) (v : Fin m → ℝ) :
    (Work.BoseB4.totNumOp m).comp (Work.BoseB4.creOf m v)
      = (Work.BoseB4.creOf m v).comp (Work.BoseB4.totNumOp m) + Work.BoseB4.creOf m v := by
  change totNumOp m * creOf m v = creOf m v * totNumOp m + creOf m v
  rw [creOf, Finset.mul_sum]
  simp only [mul_smul_comm]
  rw [show (∑ l : Fin m, v l • (totNumOp m * cre m l))
        = ∑ l : Fin m, v l • (cre m l * totNumOp m + cre m l)
      from Finset.sum_congr rfl (fun l _ => by rw [totNumOp_mul_cre m l])]
  simp only [smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul]
    simp only [smul_mul_assoc]

end Work.BoseB4
