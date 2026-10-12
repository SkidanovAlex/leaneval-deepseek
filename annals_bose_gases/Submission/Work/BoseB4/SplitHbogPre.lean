import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.K2ndDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.SplitHbogPre` — pointwise form of the `split` dictionary

The four dictionary theorems of the split chapter (`Split_ann_zero`,
`Split_cre_zero`, `Split_ann_excited`, `Split_cre_excited`) are stated as
identities of *operators*, `split ∘ a = a' ∘ split`.  For the term-by-term
transport of the Bogoliubov rows of FS `eq:HLambdaSecond` one works instead with
the *pointwise* form, `split (a v) = a' (split v)`, and with the unfolding
`annX m l = annC (Excited m) ⟨l, h⟩` (resp. `creX`) at an excited mode.

This module collects those rewrites, together with the two elementary facts

* `lift B (lift B' w) = lift (B ∘ B') w` and
* `lift B (a0 w) = a0 (lift B w)` (`a0` commutes with every `lift`),

and the ℂ-linearity of `monoOp p q` in its spectator operator over a *weighted
finite sum*, `monoOp_sum_smul`.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-! ## The dictionary, pointwise -/

/-- Condensate annihilation, pointwise: `split ∘ ann m 0 = a₀ ∘ split`. -/
lemma split_apply_ann_zero (v : RealFock m) : split (ann m 0 v) = a0 (split v) := by
  have h := congrArg (fun (f : RealFock m →ₗ[ℝ] FockCore (cfock (Excited m))) => f v)
    (Split_ann_zero (m := m))
  simpa using h

/-- Condensate creation, pointwise: `split ∘ cre m 0 = a₀† ∘ split`. -/
lemma split_apply_cre_zero (v : RealFock m) : split (cre m 0 v) = a0d (split v) := by
  have h := congrArg (fun (f : RealFock m →ₗ[ℝ] FockCore (cfock (Excited m))) => f v)
    (Split_cre_zero (m := m))
  simpa using h

/-- Annihilation of an excited mode, pointwise: `split ∘ ann m l = lift (annC _) ∘ split`. -/
lemma split_apply_ann_of_ne (l : Fin m) (hl : l ≠ 0) (v : RealFock m) :
    split (ann m l v) = lift (annC (Excited m) ⟨l, hl⟩) (split v) := by
  have h := congrArg (fun (f : RealFock m →ₗ[ℝ] FockCore (cfock (Excited m))) => f v)
    (Split_ann_excited (m := m) ⟨l, hl⟩)
  simpa using h

/-- Creation of an excited mode, pointwise: `split ∘ cre m l = lift (creC _) ∘ split`. -/
lemma split_apply_cre_of_ne (l : Fin m) (hl : l ≠ 0) (v : RealFock m) :
    split (cre m l v) = lift (creC (Excited m) ⟨l, hl⟩) (split v) := by
  have h := congrArg (fun (f : RealFock m →ₗ[ℝ] FockCore (cfock (Excited m))) => f v)
    (Split_cre_excited (m := m) ⟨l, hl⟩)
  simpa using h

/-! ## The excited-mode words of `K2ndDefs` as `annC` / `creC` -/

/-- At an excited mode `l ≠ 0` the lattice word `annX m l` is the abstract `annC`. -/
lemma annX_of_ne (l : Fin m) (hl : l ≠ 0) : annX m l = annC (Excited m) ⟨l, hl⟩ := by
  rw [annX, dif_neg hl]

/-- At an excited mode `l ≠ 0` the lattice word `creX m l` is the abstract `creC`. -/
lemma creX_of_ne (l : Fin m) (hl : l ≠ 0) : creX m l = creC (Excited m) ⟨l, hl⟩ := by
  rw [creX, dif_neg hl]

/-! ## `lift` calculus -/

/-- `lift B ∘ lift B' = lift (B ∘ B')`, pointwise. -/
lemma lift_comp_apply (B B' : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (w : FockCore (cfock (Excited m))) :
    lift B (lift B' w) = lift (B.comp B') w := by
  rw [← LinearMap.comp_apply, ← lift_comp]

/-- `lift` commutes with the condensate annihilation `a₀`, pointwise. -/
lemma lift_a0_apply (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (w : FockCore (cfock (Excited m))) : lift B (a0 w) = a0 (lift B w) := by
  have h := congrArg (fun (f : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m))) =>
    f w) (lift_comm_a0 B)
  simpa using h

/-! ## `monoOp` is ℂ-linear in `B` over finite sums -/

/-- `monoOp p q` distributes over a finite sum of spectator operators with
coefficients: the ℂ-linearity in the spectator slot, in the form needed to
expand `Kbog1`, `Kbog2`, … . -/
lemma monoOp_sum_smul {ι : Type*} (s : Finset ι) (p q : ℕ) (c : ι → ℂ)
    (B : ι → cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    monoOp p q (∑ i ∈ s, c i • B i) = ∑ i ∈ s, c i • monoOp p q (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, monoOp_add, monoOp_smul, ih]

end Work.BoseB4
