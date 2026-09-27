import Mathlib
import Submission.Work.KT.ExtGen.Basic
import Submission.Work.KT.ExtProdB
import Submission.Work.KT.Basic
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.k0_basic
import Submission.Work.KT.bott_aux
import Submission.Work.KT.BallKFrame
import Submission.Work.KT.EG.kappa_reduce
import Submission.Work.KT.ExtGen.bottSurjOfHker
import Submission.Work.KT.ExtGen.ker_bottMap

/-!
# The *surjectivity half* of the suspension lemma, modulo the `κ`-calculus only

`Work.KT.ExtGen.susp_bijective` has two conjuncts: the injectivity and the surjectivity of
`u ↦ μx u b` on the reduced groups.  Of these, the **surjectivity** conjunct needs *no* Bott
index — it is equivalent to the surjectivity half of `Work.KT.fund_product`, i.e. to the `κ`-calculus
(`EG.kappa_reduce` = (D)), as recorded in `Submission/Work/KT/ExtGen/NOTES_injectivity3.md` §1–§2.

Concretely, the chain is

* `EG.kappa_reduce` (D)  ⟹  `hker`  (every class killed by `Fund.r` is in the image of the Bott map
  — `ExtGen.ker_bottMap`, proved);
* `hker`  ⟹  surjectivity of the external product with `b` (`ExtGen.bottSurjOfHker`, proved, no
  Bott index and no `ext_product` in its closure).

This file performs the last step of that chain, in the exact shape of the second conjunct of
`Work.KT.ExtGen.susp_bijective`:

* `susp_surj_of_hD` — the conditional form, where (D) is a hypothesis.  Its axiom footprint is
  `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`): it rests only on the *proved*
  `ExtGen.ker_bottMap` and `ExtGen.bottSurjOfHker`.
* `susp_bijective_surj` — the same statement with (D) discharged by `EG.kappa_reduce`, i.e. the
  surjectivity conjunct of `Work.KT.ExtGen.susp_bijective` *without* the Bott index.  Its (only)
  remaining input is the `κ`-calculus chain behind `EG.kappa_reduce`
  (`EG.kappa_linearise`, `Fund.kappa_bott`), which is being finished by the `EG`/`Fund` fleet; as
  soon as `EG.kappa_reduce` is `sorry`-free this theorem is too.

The `j = 0` case (`Module.finrank ℝ U = 0`) is vacuous, as in `susp_bijective`: a
zero-dimensional real normed space has empty boundary sphere.
-/

namespace Work.KT.ExtGen

open Work.KT

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

/-- **The surjectivity conjunct of `Work.KT.ExtGen.susp_bijective`, from the `κ`-calculus (D).**

`μfp` is any `K₀`-product on `C(Xq U × S², ℂ)` and `hD` is the form (D) takes in
`ExtGen.ker_bottMap`: every clutched class is, up to the rank-`n` trivial class, an
`C(Xq U, ℂ)`-multiple of the Bott class, at the space `Xq U` whose algebra of continuous functions
is `Kpair U`. -/
theorem susp_surj_of_hD (U : Type) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] (j : ℕ) (hUd : Module.finrank ℝ U = 2 * j)
    (y0U : Ball U) (hU : y0U ∈ bdry U) (y0R : Ball R2) (hR : y0R ∈ bdry R2)
    (y0 : Ball (U × R2)) (hy0 : y0 ∈ bdry (U × R2))
    (μx : K0 (Kpair U) →+ K0 (Kpair R2) →+ K0 (Kpair (U × R2)))
    (hμx : IsExtProd U R2 y0U y0R y0 μx)
    (b : K0 (Kpair R2)) (hb : K0.mapA (augPair R2 y0R) b = 0)
    (hbgen : ∀ z, K0.mapA (augPair R2 y0R) z = 0 → ∃ n : ℤ, z = n • b)
    (hbinf : ∀ n : ℤ, n • b = 0 → n = 0)
    (μfp : K0 C(Xq U × S2, ℂ) →+ K0 C(Xq U × S2, ℂ) →+ K0 C(Xq U × S2, ℂ))
    (hμfp : IsK0Mul μfp)
    (hD : ∀ (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(Xq U × Sph ℂ, ℂ))ˣ),
      ∃ c : K0 C(Xq U, ℂ),
        Fund.kappa (Xq U) n u - cls (Mat.one C(Xq U × S2, ℂ) n)
          = Fund.bottMap (Xq U) μfp c) :
    ∀ z, K0.mapA (augPair (U × R2) y0) z = 0 →
      ∃ u, K0.mapA (augPair U y0U) u = 0 ∧ μx u b = z := by
  by_cases hdim : 1 ≤ Module.finrank ℝ U
  · exact bottSurjOfHker U R2 y0U hU y0R hR y0 hy0 hdim (by simp) b hb hbinf hbgen μx hμx
      μfp hμfp (ker_bottMap (Xq U) μfp hμfp hD)
  · -- `finrank ℝ U = 0`: the boundary is empty, so the statement is vacuous.
    push_neg at hdim
    have h0 : Module.finrank ℝ U = 0 := Nat.lt_one_iff.mp hdim
    haveI : Subsingleton U := Module.finrank_zero_iff.mp h0
    intro z hz
    exfalso
    have hnorm : ‖(y0U : U)‖ = 1 := hU
    rw [Subsingleton.elim (y0U : U) 0, norm_zero] at hnorm
    exact zero_ne_one hnorm

/-- **The surjectivity conjunct of `Work.KT.ExtGen.susp_bijective`, unconditional modulo the
`κ`-calculus**: (D) is discharged by `EG.kappa_reduce`.  The only unfinished input left in its
`#print axioms` is the `EG`/`Fund` `κ`-chain behind `EG.kappa_reduce`; there is no Bott index and
no `Work.KT.fund_product` in the statement's route. -/
theorem susp_bijective_surj (U : Type) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] (j : ℕ) (hUd : Module.finrank ℝ U = 2 * j)
    (y0U : Ball U) (hU : y0U ∈ bdry U) (y0R : Ball R2) (hR : y0R ∈ bdry R2)
    (y0 : Ball (U × R2)) (hy0 : y0 ∈ bdry (U × R2))
    (μx : K0 (Kpair U) →+ K0 (Kpair R2) →+ K0 (Kpair (U × R2)))
    (hμx : IsExtProd U R2 y0U y0R y0 μx)
    (b : K0 (Kpair R2)) (hb : K0.mapA (augPair R2 y0R) b = 0)
    (hbgen : ∀ z, K0.mapA (augPair R2 y0R) z = 0 → ∃ n : ℤ, z = n • b)
    (hbinf : ∀ n : ℤ, n • b = 0 → n = 0) :
    ∀ z, K0.mapA (augPair (U × R2) y0) z = 0 →
      ∃ u, K0.mapA (augPair U y0U) u = 0 ∧ μx u b = z := by
  obtain ⟨μfp, hμfp⟩ := ba_exists_isK0Mul (C(Xq U × S2, ℂ)) (fun x y => mul_comm x y)
  exact susp_surj_of_hD U j hUd y0U hU y0R hR y0 hy0 μx hμx b hb hbgen hbinf μfp hμfp
    (fun n u => EG.kappa_reduce (Xq U) n u μfp hμfp)

end

end Work.KT.ExtGen
