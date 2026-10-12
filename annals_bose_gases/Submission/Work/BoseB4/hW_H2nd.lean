import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.K2ndEval
import Submission.Work.BoseB4.split_HW
import Submission.Work.BoseB4.split_Hbog
import Submission.Work.BoseB4.split_Hchi
import Submission.Work.BoseB4.split_HchiOm
import Submission.Work.BoseB4.split_Hcontact
import Submission.Work.BoseB4.split_Hmu
import Submission.Work.BoseB4.split_Hnn
import Submission.Work.BoseB4.split_number_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.hW_H2nd` — `eq:HLambdaSecond` under the condensate splitting

FS's box Hamiltonian `𝓗^{2nd}_Λ(μ)` (`Work.BoseB4.H2nd`, FS `eq:HLambdaSecond`)
is a finite sum of words in the lattice operators `a_k`, `a_k†`, with the
condensate mode `k = 0` singled out.  The occupation splitting
`Work.BoseB4.split : RealFock m → FockCore (cfock (Excited m))` reads each word as
a word in `a₀ = a0`, `a₀† = a0d` and the levelwise lifts of the excited-mode
operators `annX m k`, `creX m k`, and the `c`-number substitution
`Work.BoseB4.Kafz_lattice` applies to operators written as a finite sum of
**anti-normal** monomials `a₀^p (a₀†)^q (lift B)`.

This module is the bridge between the two: it sums the per-term dictionary
lemmas

* `Work.BoseB4.split_number_sum` (the `∫ τ a_k†a_k dk`, `n₊`, `n₊^H` and
  `ℓ⁻³∫a_k†a_k` rows),
* `Work.BoseB4.split_Hcontact`, `Work.BoseB4.split_Hmu`,
  `Work.BoseB4.split_HW`, `Work.BoseB4.split_Hbog`,
  `Work.BoseB4.split_Hchi`, `Work.BoseB4.split_HchiOm`,
  `Work.BoseB4.split_Hnn`

over the ten named pieces of `H2nd`, and identifies the result with the
anti-normal family `Work.BoseB4.K2ndC` of `Work.BoseB4.K2ndDefs`.  The outcome

    `split (H2nd D x) = (K2ndC D) (split x)`

is exactly the hypothesis `hW` of `Work.BoseB4.Kafz_lattice`, so
`Work.BoseB4.Kafz_H2nd` is its immediate corollary: FS `thm:Kafz` for FS's box
Hamiltonian, with the explicit symbol `Work.BoseB4.K2ndSym`.

## Route

* `H2nd_apply` (`Work.BoseB4.K2ndEval`) splits `H2nd D x` into its ten pieces and
  `LinearMap.map_add` carries `split` inside;
* the per-term lemmas rewrite each piece as `monoOp p q (K…) (split x)`;
* `← LinearMap.add_apply` re-packs the sum of applications into a single
  application of a sum of linear maps, and `congr 1` reduces the claim to an
  identity between linear maps;
* `K2ndC_eq_sum` plus the `Fin 9` evaluation lemmas of `Work.BoseB4.K2ndEval`
  expand `K2ndC` into the same 24 monomials, which `monoOp_add` and `ac_rfl`
  match up.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

set_option maxHeartbeats 2000000 in
theorem hW_H2nd (D : H2ndData m) (x : RealFock m) :
    split (H2nd D x) = (K2ndC D) (split x) := by
  have hkin : split (Hkin D x) = (monoOp 0 0 (Kkin D)) (split x) := by
    simpa only [Hkin, Kkin, CX]
      using split_number_sum (s := exc m) (exc_zero_notMem (m := m)) (D.tau) x
  have hgap : split (Hgap D x) = (monoOp 0 0 (Kgap D)) (split x) := by
    simpa only [Hgap, Kgap, CX, gGap, Finset.smul_sum]
      using split_number_sum (s := exc m) (exc_zero_notMem (m := m)) (fun _ => gGap D) x
  have hgapH : split (HgapH D x) = (monoOp 0 0 (KgapH D)) (split x) := by
    simpa only [HgapH, KgapH, CX, gGapH, Finset.smul_sum]
      using split_number_sum (s := (exc m).filter (fun k => k ∈ D.PHset))
        (by simp [exc]) (fun _ => gGapH D) x
  simp only [H2nd, LinearMap.add_apply, map_add]
  rw [hkin, hgap, hgapH, split_Hcontact D x, split_Hmu D x, split_HW D x, split_Hbog D x,
    split_Hchi D x, split_HchiOm D x, split_Hnn D x]
  simp only [← LinearMap.add_apply]
  congr 1
  rw [K2ndC_eq_sum]
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
    Kvec_0, Kvec_1, Kvec_2, Kvec_3, Kvec_4, Kvec_5, Kvec_6, Kvec_7, Kvec_8,
    Kpvec_0, Kpvec_1, Kpvec_2, Kpvec_3, Kpvec_4, Kpvec_5, Kpvec_6, Kpvec_7, Kpvec_8,
    Kqvec_0, Kqvec_1, Kqvec_2, Kqvec_3, Kqvec_4, Kqvec_5, Kqvec_6, Kqvec_7, Kqvec_8,
    K00, K11, K22, K20, K02, K21, K10, K12, K01, monoOp_add]
  ac_rfl

end Work.BoseB4
