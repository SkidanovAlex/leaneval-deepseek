import Mathlib
import Submission.Work.TorsorExistence.Defs
import Submission.Work.MotC.TransData
import Submission.Work.MotC.galPoint_markPoint
import Submission.Work.MotC.neg_zpow_eq
import Submission.Work.MotC.gal_sub_eq_of_smul

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The "torsor step" of node C5 (`MotC`)

Node C5 of the audit (`not_algEquiv_twistField`) has two halves:

* an **extension** half — a `𝕜`-isomorphism `K_P ≃ₐ[𝕜] K_{kP}` of the twisted function fields
  extends to `Θ : L(E) ≃ₐ[L] L(E)` with `Θ α_P = α_{kP} Θ`
  (`MotC/exists_algEquiv_fixedField.lean`), and
* an **arithmetic** half — such a `Θ` is (by node C2's classification of the `L`-automorphisms of
  `L(E)`) necessarily of the form `Θ = τ_R^* ∘ [ε]^*`, and conjugating the equation
  `Θ α_P = α_{kP} Θ` with the translation/negation commutation rules of `TransData` forces
  `(k - ε) • P ∈ (σ - 1) E(L)`; as `k - ε ∈ {1,2,3,4}` is a unit modulo `5` and `P` is `5`-torsion,
  this forces `P = σ R' - R'` for some `R'`, contradicting the hypothesis `hP` that the class of `P`
  in `H¹(ℤ/5, E(L))` is nonzero.

This file proves the arithmetic half, in the form in which node C5 consumes it: for *no* point `R`
and unit `ε` does the automorphism `Θ = (TD.neg ^ (ε : ℤ)).trans (TD.τ R)` conjugate the twisted
automorphism `α_P = twistAut D (τ P)` into `α_{kP} = twistAut D (τ (k • P))` (`k = 2` or `k = 3`),
i.e. the equation `Θ ∘ α_P = α_{kP} ∘ Θ` (the equation of the statement, read pointwise) is never
satisfied.

The computation is carried out pointwise on the function field, using only the pointwise forms of
the axioms of `TransData`:

* `τ_{A+B} = τ_B ∘ τ_A` (from `τ_add`),
* `σ ∘ τ_Q = τ_{σQ} ∘ σ` (`coeff_τ`),
* `neg ∘ σ = σ ∘ neg` (`neg_coeff`),
* `neg ∘ τ_Q = τ_{-Q} ∘ neg` (from `neg_τ`, using `neg² = 1`, which itself is `neg_τ 0`),

plus the fact that `neg ^ (ε : ℤ) = neg` for every unit `ε` of `ℤ` (the pullback of `[-1]` is an
involution, `Work.MotC.neg_zpow_eq`).  Since the exponent `ε` disappears from the computation, the
resulting relation is `R - P = σ R + k • P`, i.e. `σ R - R = -(k+1) • P`, a unit multiple of `P`;
the final arithmetic step (`Work.MotC.gal_sub_eq_of_smul`) converts this into a genuine coboundary
`P = σ R' - R'`.
-/

set_option autoImplicit false

namespace Work.MotC

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

theorem torsor_step {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D)
    (hP : ¬ ∃ R : WeierstrassCurve.Affine.Point (Work.MotC.baseCurve D),
      Work.MotC.galPoint D R - R = Work.MotC.markPoint D)
    (k : ℕ) (hk : k = 2 ∨ k = 3)
    (R : WeierstrassCurve.Affine.Point (Work.MotC.baseCurve D)) (ε : ℤˣ) :
    ¬ ∀ x : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D),
        ((TD.neg ^ (ε : ℤ)).trans (TD.τ R))
            (Work.MotC.twistAut D (TD.τ (Work.MotC.markPoint D)) x) =
          Work.MotC.twistAut D (TD.τ (k • Work.MotC.markPoint D))
            (((TD.neg ^ (ε : ℤ)).trans (TD.τ R)) x) := by
  intro h
  -- `[-1]^*` is an involution, so every integral power of it is `[-1]^*` itself.
  have hneg2 : ∀ w : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D),
      TD.neg (TD.neg w) = w := by
    intro w
    have hh := congrArg (fun (e : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) ≃ₐ[D.ext.L]
        WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) => e w) (TD.neg_τ 0)
    simp only [AlgEquiv.trans_apply, TD.τ_zero, AlgEquiv.one_apply, neg_zero] at hh
    exact hh
  rw [neg_zpow_eq D TD ε] at h
  -- pointwise forms of the axioms of `TransData`
  have hτadd : ∀ (A B : WeierstrassCurve.Affine.Point (Work.MotC.baseCurve D))
      (w : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)),
      TD.τ (A + B) w = TD.τ B (TD.τ A w) :=
    fun A B w => by rw [TD.τ_add A B, AlgEquiv.trans_apply]
  have hnegτ : ∀ (Q : WeierstrassCurve.Affine.Point (Work.MotC.baseCurve D))
      (w : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)),
      TD.neg (TD.τ Q w) = TD.τ (-Q) (TD.neg w) := by
    intro Q w
    have hh : ∀ z, TD.neg (TD.τ Q (TD.neg z)) = TD.τ (-Q) z := fun z => by
      have hh2 := congrArg (fun (e : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) ≃ₐ[D.ext.L]
          WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) => e z) (TD.neg_τ Q)
      simpa only [AlgEquiv.trans_apply] using hh2
    have := hh (TD.neg w)
    simpa only [hneg2 w] using this
  have hnegσ : ∀ w : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D),
      TD.neg (Work.MotC.coeffAut D w) = Work.MotC.coeffAut D (TD.neg w) := TD.neg_coeff
  have hτσ : ∀ (Q : WeierstrassCurve.Affine.Point (Work.MotC.baseCurve D))
      (w : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)),
      Work.MotC.coeffAut D (TD.τ Q w) =
        TD.τ (Work.MotC.galPoint D Q) (Work.MotC.coeffAut D w) := TD.coeff_τ
  have htw : ∀ (τ : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) ≃ₐ[D.ext.L]
        WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D))
      (x : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)),
      Work.MotC.twistAut D τ x = Work.MotC.coeffAut D (τ x) := fun τ x => rfl
  -- ## The main computation
  -- After the two chains of rewrites, the hypothesis `h` reads, for every `x`,
  --   `τ_{σ(-P) + R} (σ (neg x)) = τ_{σ(R + kP)} (σ (neg x))`;
  -- since `σ (neg x)` is an arbitrary element of the function field (`σ ∘ neg` is a bijection),
  -- this forces `σ(-P) + R = σ(R + kP)`, i.e. `R - P = σ R + k • P`.
  have hsurj : Function.Surjective (fun x : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) =>
      Work.MotC.coeffAut D (TD.neg x)) :=
    (EquivLike.surjective (Work.MotC.coeffAut D)).comp (EquivLike.surjective TD.neg)
  have hmain : ∀ x : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D),
      TD.τ (Work.MotC.galPoint D (-(Work.MotC.markPoint D)) + R) (Work.MotC.coeffAut D (TD.neg x)) =
        TD.τ (Work.MotC.galPoint D (R + k • Work.MotC.markPoint D)) (Work.MotC.coeffAut D (TD.neg x)) := by
    intro x
    have hx := h x
    have hL : (TD.neg.trans (TD.τ R)) (Work.MotC.twistAut D (TD.τ (Work.MotC.markPoint D)) x) =
        TD.τ (Work.MotC.galPoint D (-(Work.MotC.markPoint D)) + R) (Work.MotC.coeffAut D (TD.neg x)) := by
      rw [AlgEquiv.trans_apply, htw, hnegσ, hnegτ, hτσ, ← hτadd]
    have hR' : Work.MotC.twistAut D (TD.τ (k • Work.MotC.markPoint D)) ((TD.neg.trans (TD.τ R)) x) =
        TD.τ (Work.MotC.galPoint D (R + k • Work.MotC.markPoint D)) (Work.MotC.coeffAut D (TD.neg x)) := by
      rw [AlgEquiv.trans_apply, htw, ← hτadd, hτσ]
    rw [hL, hR'] at hx
    exact hx
  have hfun : ∀ z : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D),
      TD.τ (Work.MotC.galPoint D (-(Work.MotC.markPoint D)) + R) z =
        TD.τ (Work.MotC.galPoint D (R + k • Work.MotC.markPoint D)) z := by
    intro z
    obtain ⟨x, hx⟩ := hsurj z
    rw [← hx]
    exact hmain x
  have hτeq : TD.τ (Work.MotC.galPoint D (-(Work.MotC.markPoint D)) + R) =
      TD.τ (Work.MotC.galPoint D (R + k • Work.MotC.markPoint D)) := AlgEquiv.ext hfun
  have hAB : Work.MotC.galPoint D (-(Work.MotC.markPoint D)) + R =
      Work.MotC.galPoint D (R + k • Work.MotC.markPoint D) := TD.τ_injective hτeq
  have hσP : Work.MotC.galPoint D (Work.MotC.markPoint D) = Work.MotC.markPoint D :=
    Work.MotC.galPoint_markPoint D
  -- `galPoint D` is an additive homomorphism fixing the marked point, so `hAB` becomes
  -- `R - P = σ R + k • P`.
  have hRk : R - Work.MotC.markPoint D = Work.MotC.galPoint D R + k • Work.MotC.markPoint D := by
    rw [map_neg, hσP, map_add, map_nsmul, hσP] at hAB
    simpa [sub_eq_add_neg, add_comm] using hAB
  -- The marked point is `5`-torsion.
  have h5 : (5 : ℕ) • Work.MotC.markPoint D = 0 := by
    have hf := AddMonoidHom.map_nsmul (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L)
      (5 : ℕ) D.P
    have h2 : (5 : ℕ) • (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) D.P = 0 := by
      rw [← hf]
      exact (congrArg _ D.five_smul).trans (map_zero _)
    simpa only [Work.MotC.markPoint] using h2
  obtain ⟨R', hR'⟩ := gal_sub_eq_of_smul (Work.MotC.galPoint D) (Work.MotC.markPoint D) R h5 k hk hRk
  exact hP ⟨R', hR'⟩

end

end Work.MotC
