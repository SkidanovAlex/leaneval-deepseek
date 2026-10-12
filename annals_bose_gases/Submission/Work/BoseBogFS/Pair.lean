import Mathlib.Tactic.Module
import Mathlib.Data.Real.Basic
import Submission.Work.BoseBogFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Pair` — the per-pair algebra of FS `eq:BogIdentity`

FS `thm:BogHamDiag` (l. 2290 of `Papers/fournais_solovej/final_v2.tex`) is the statement
that the quadratic Bogoliubov Hamiltonian

  `𝒦^Bog = ½Σ_k[𝒜_k(a_k†a_k + a_{-k}†a_{-k}) + ℬ_k(a_k†a_{-k}† + a_ka_{-k})
                  + 𝒞_k(a_k†+a_{-k}†+a_k+a_{-k})]`

is bounded below by the *diagonalised* form minus the zero point and the `κ`-error, where
FS's `b_k = a_k + α_ka_{-k}† + c_k` of `eq:Defb_k` carries the `c`-number shift `c_k`
**inside**.

This module proves the first block identity of that statement, *directly in
`Work.BoseB7.FockData`* — no mode decomposition (`Work.BoseB6Est.FsBogDecomp`) and no
second-quantisation bridge is needed, because the identity is local to the two modes
`(k,−k)` and uses only the CCR package:

* `bOp_pair_expand` — the block expansion
  `b_k†b_k + b_{-k}†b_{-k} = (1+α²)(n_k+n_{-k}) + 2α(a_k†a_{-k}† + a_ka_{-k})
   + α²([a_k,a_k†]+[a_{-k},a_{-k}†])`;
* `bogBShiftDag_bp` — the shifted `b̂_k†` is the adjoint of `b̂_k` for the Fock form.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The block expansion of the squeezed number operators.**  With
`b_k = a_k + α_k a_{-k}†` (FS `eq:Defb_k` without the shift) and `α_{-k} = α_k`,

  `b_k†b_k + b_{-k}†b_{-k}
     = (1+α_k²)(n_k + n_{-k}) + 2α_k(a_k†a_{-k}† + a_ka_{-k})
       + α_k²([a_k,a_k†] + [a_{-k},a_{-k}†])`.

All that is used is FS `eq:Commutator_general` (`F.ccr`), the annihilation/creation
commutativity and `α (-k) = α k`. -/
theorem bOp_pair_expand (F : FockData Mode) (α : Mode → ℝ) (k : Mode) (hα : α (-k) = α k) :
    (F.bOpDag α k) ∘ₗ (F.bOp α k) + (F.bOpDag α (-k)) ∘ₗ (F.bOp α (-k))
      = (1 + α k ^ 2) • (F.nOp k + F.nOp (-k))
        + (2 * α k) • (F.aDag k ∘ₗ F.aDag (-k) + F.a k ∘ₗ F.a (-k))
        + (α k ^ 2 * (F.ccrK k k + F.ccrK (-k) (-k))) • (1 : F.H →ₗ[ℝ] F.H) := by
  have h1 : F.a (-k) ∘ₗ F.aDag (-k)
      = F.aDag (-k) ∘ₗ F.a (-k) + (F.ccrK (-k) (-k)) • (1 : F.H →ₗ[ℝ] F.H) :=
    F.ccr (-k) (-k)
  have h2 : F.a k ∘ₗ F.aDag k
      = F.aDag k ∘ₗ F.a k + (F.ccrK k k) • (1 : F.H →ₗ[ℝ] F.H) := F.ccr k k
  have h3 : F.aDag k ∘ₗ F.aDag (-k) = F.aDag (-k) ∘ₗ F.aDag k := F.cre_comm k (-k)
  have h4 : F.a (-k) ∘ₗ F.a k = F.a k ∘ₗ F.a (-k) := F.ann_comm (-k) k
  have hp1 : ∀ x : F.H, F.a (-k) (F.aDag (-k) x) = F.aDag (-k) (F.a (-k) x) + F.ccrK (-k) (-k) • x := by
    intro x
    have h := DFunLike.congr_fun h1 x
    simpa [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] using h
  have hp2 : ∀ x : F.H, F.a k (F.aDag k x) = F.aDag k (F.a k x) + F.ccrK k k • x := by
    intro x
    have h := DFunLike.congr_fun h2 x
    simpa [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] using h
  have hp3 : ∀ x : F.H, F.aDag k (F.aDag (-k) x) = F.aDag (-k) (F.aDag k x) := by
    intro x
    have h := DFunLike.congr_fun h3 x
    simpa [LinearMap.comp_apply] using h
  have hp4 : ∀ x : F.H, F.a (-k) (F.a k x) = F.a k (F.a (-k) x) := by
    intro x
    have h := DFunLike.congr_fun h4 x
    simpa [LinearMap.comp_apply] using h
  ext x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    Module.End.one_apply, FockData.bOp, FockData.bOpDag, FockData.nOp, hα, neg_neg,
    map_add, map_smul]
  rw [hp1 x, hp2 x, hp3 x, hp4 x]
  module

/-- The shifted squeezing operator `b̂_k = b_k + c_k` has formal adjoint `b̂_k†` for the
Fock form `bp` (`Work.BoseB7.bOpDag_bp` plus the real shift). -/
theorem bogBShiftDag_bp (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (k : Mode) (g f : F.H) :
    F.bp ((bogBShiftDag F E ρ k) g) f = F.bp g ((bogBShift F E ρ k) f) := by
  simp only [bogBShiftDag, bogBShift, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul, Module.End.one_apply]
  rw [Work.BoseB7.bOpDag_bp F (bogAlpha E ρ) k g f]

end Work.BoseBogFS
