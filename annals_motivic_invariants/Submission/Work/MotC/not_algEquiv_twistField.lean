import Mathlib
import Submission.Work.MotC.TransData
import Submission.Work.MotC.torsor_step
import Submission.Work.MotC.exists_algEquiv_fixedField
import Submission.Work.MotC.coeffAut_orderOf
import Submission.Work.MotC.galPoint_markPoint
import Submission.Work.MotC.twistAut_algebraMap
import Submission.Work.MotC.fixedField_descent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Node C5: the twisted function fields `K_P` and `K_{kP}` are not isomorphic

This file proves `Work.MotC.not_algEquiv_twistField`, the "arithmetic" half of the auditor's node
C5.  The mathematical content is that no `𝕜`-algebra isomorphism `K_P ≃ₐ[𝕜] K_{kP}` (`k = 2, 3`)
exists, where `K_Q` is the fixed field of the twisted-translation automorphism
`α_Q = twistAut D (τ_Q^*)`, `τ_Q^*` being the pullback of the translation by `Q` on `L(E)`.

The argument has two halves, both already available in the chapter:

* **the torsor step** (`Work.MotC.exists_algEquiv_fixedField`): a `𝕜`-isomorphism
  `θ : K_P ≃ₐ[𝕜] K_{kP}` extends to an `L`-algebra automorphism `Θ` of `L(E)` with
  `Θ α_P = α_{kP} Θ`.  For this one needs `α_P^5 = α_{kP}^5 = 1`, `α_P ≠ 1`, `α_{kP} ≠ 1` and
  that both act on the constants `L` by the generator of the cyclic quintic extension;
* **the arithmetic core** (`Work.MotC.torsor_step`): no automorphism of the form
  `τ_R^* ∘ [-1]^*` (the classification of the automorphisms of `L(E)`, node C2) conjugates
  `α_P` into `α_{kP}`, because that would force `P` to be a Galois coboundary
  `σ R' - R'`, contradicting the hypothesis `hP`.

The new ingredients proved here are the automorphism-theoretic ones: `α_Q = c * τ_Q^*` is the
product of the coefficient (Galois) action `c = coeffAut D` with the restricted translation
pullback, and the two commute whenever `Q` is Galois-fixed, so that
`α_Q ^ n = c ^ n * (τ_Q^*)^n = c ^ n * τ_{nQ}^*`; since `c` has order `5` and `P`, `kP` are
`5`-torsion, `α_Q^5 = 1`, while `α_Q ≠ 1` because it acts on the constants through `σ ≠ 1`.
-/

set_option autoImplicit false

namespace Work.MotC

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- `twistAut D τ` is the product (in the group of `𝕜`-algebra automorphisms of `L(E)`) of the
coefficient action `coeffAut D` with the restriction of scalars of `τ`. -/
theorem twistAut_eq_mul (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (τ : WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[D.ext.L]
      WeierstrassCurve.Affine.FunctionField (baseCurve D)) :
    twistAut D τ = coeffAut D * AlgEquiv.restrictScalars 𝕜 τ := by
  ext x
  rw [twistAut, AlgEquiv.trans_apply, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]

/-- The coefficient action commutes with the (restricted) translation pullback of a
Galois-fixed point.  This is `TransData.coeff_τ` at a point where `σ` acts trivially. -/
theorem commute_coeffAut_tau (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (TD : Work.MotC.TransData D)
    (Q : WeierstrassCurve.Affine.Point (baseCurve D)) (hQ : galPoint D Q = Q) :
    Commute (coeffAut D) (AlgEquiv.restrictScalars 𝕜 (TD.τ Q)) := by
  rw [commute_iff_eq]
  ext x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.restrictScalars_apply, TD.coeff_τ Q x, hQ]

/-- The powers of the (restricted) translation pullback of `Q`: `(τ_Q^*)^n = τ_{nQ}^*`. -/
theorem t_pow (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D)
    (Q : WeierstrassCurve.Affine.Point (baseCurve D)) (n : ℕ) :
    (AlgEquiv.restrictScalars 𝕜 (TD.τ Q)) ^ n
      = AlgEquiv.restrictScalars 𝕜 (TD.τ (n • Q)) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, TD.τ_zero]; rfl
  | succ n ih =>
      rw [pow_succ, ih]
      rw [show (n + 1) • Q = Q + n • Q by rw [succ_nsmul, add_comm]]
      rw [TD.τ_add Q (n • Q)]
      rfl

/-- The powers of the twisted-translation automorphism of a Galois-fixed point:
`α_Q^n = c^n * τ_{nQ}^*` with `c = coeffAut D`. -/
theorem twistAut_pow (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D)
    (Q : WeierstrassCurve.Affine.Point (baseCurve D)) (hQ : galPoint D Q = Q) (n : ℕ) :
    (twistAut D (TD.τ Q)) ^ n
      = (coeffAut D) ^ n * AlgEquiv.restrictScalars 𝕜 (TD.τ (n • Q)) := by
  rw [twistAut_eq_mul, Commute.mul_pow (commute_coeffAut_tau D TD Q hQ), t_pow]

/-- For a Galois-fixed `5`-torsion point `Q`, the twisted-translation automorphism `α_Q` has
order dividing `5`. -/
theorem twistAut_pow_five (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D)
    (Q : WeierstrassCurve.Affine.Point (baseCurve D)) (hQ : galPoint D Q = Q)
    (h5Q : (5 : ℕ) • Q = 0) :
    (twistAut D (TD.τ Q)) ^ 5 = 1 := by
  have hone : AlgEquiv.restrictScalars 𝕜 (1 : WeierstrassCurve.Affine.FunctionField (baseCurve D) ≃ₐ[D.ext.L]
      WeierstrassCurve.Affine.FunctionField (baseCurve D)) = 1 := by
    ext x; rfl
  have hc5 : (coeffAut D) ^ 5 = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp (by rw [coeffAut_orderOf D])
  rw [twistAut_pow D TD Q hQ 5, h5Q, TD.τ_zero, hone, mul_one, hc5]

/-- The twisted-translation automorphism is nontrivial: it acts on the constants `L` through
`σ`, which is not the identity. -/
theorem twistAut_ne_one (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D)
    (Q : WeierstrassCurve.Affine.Point (baseCurve D)) :
    twistAut D (TD.τ Q) ≠ 1 := by
  intro h
  have hσ : D.sigma ≠ 1 := by
    intro hh
    have h1 : orderOf D.sigma = 1 := by rw [hh]; exact orderOf_one
    rw [D.sigma_orderOf] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨l, hl⟩ : ∃ l : D.ext.L, D.sigma l ≠ l := by
    by_contra hc
    push Not at hc
    exact hσ (AlgEquiv.ext hc)
  have h1 := twistAut_algebraMap D (TD.τ Q) l
  rw [h, AlgEquiv.one_apply] at h1
  exact hl ((RingHom.injective
    (algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (baseCurve D)))) h1).symm

theorem not_algEquiv_twistField {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D)
    (hC2 : ∀ Θ : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) ≃ₐ[D.ext.L]
        WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D),
      ∃ (R : WeierstrassCurve.Affine.Point (Work.MotC.baseCurve D)) (ε : ℤˣ),
        Θ = (TD.neg ^ (ε : ℤ)).trans (TD.τ R))
    (hP : ¬ ∃ R : WeierstrassCurve.Affine.Point (Work.MotC.baseCurve D),
      Work.MotC.galPoint D R - R = Work.MotC.markPoint D)
    (k : ℕ) (hk : k = 2 ∨ k = 3) :
    IsEmpty (↥(Work.MotC.twistField D (Work.MotC.twistAut D (TD.τ (Work.MotC.markPoint D)))) ≃ₐ[𝕜]
      ↥(Work.MotC.twistField D (Work.MotC.twistAut D (TD.τ (k • Work.MotC.markPoint D))))) := by
  classical
  rw [isEmpty_iff]
  intro θ
  -- `σ` fixes the marked point and all its multiples
  have hσP : galPoint D (markPoint D) = markPoint D := galPoint_markPoint D
  have hσkP : galPoint D (k • markPoint D) = k • markPoint D := by
    rw [map_nsmul, hσP]
  -- the marked point is `5`-torsion, and so are its multiples
  have h5P : (5 : ℕ) • markPoint D = 0 := by
    have hf := AddMonoidHom.map_nsmul
      (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) (5 : ℕ) D.P
    have h2 : (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) D.P = 0 := by
      rw [← hf]
      exact (congrArg _ D.five_smul).trans (map_zero _)
    simpa only [markPoint] using h2
  have h5kP : (5 : ℕ) • (k • markPoint D) = 0 := by
    rw [← mul_nsmul' (markPoint D) 5 k]
    exact nsmul_eq_zero_of_five_dvd h5P (Nat.dvd_mul_right 5 k)
  -- the two twisted-translation automorphisms of the statement
  have hα5 : (twistAut D (TD.τ (markPoint D))) ^ 5 = 1 :=
    twistAut_pow_five D TD (markPoint D) hσP h5P
  have hβ5 : (twistAut D (TD.τ (k • markPoint D))) ^ 5 = 1 :=
    twistAut_pow_five D TD (k • markPoint D) hσkP h5kP
  have hαne : twistAut D (TD.τ (markPoint D)) ≠ 1 := twistAut_ne_one D TD (markPoint D)
  have hβne : twistAut D (TD.τ (k • markPoint D)) ≠ 1 := twistAut_ne_one D TD (k • markPoint D)
  have hαL : ∀ l : D.ext.L, twistAut D (TD.τ (markPoint D))
      (algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (baseCurve D)) l) =
        algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (baseCurve D)) (D.ext.gen l) :=
    fun l => twistAut_algebraMap D (TD.τ (markPoint D)) l
  have hβL : ∀ l : D.ext.L, twistAut D (TD.τ (k • markPoint D))
      (algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (baseCurve D)) l) =
        algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (baseCurve D)) (D.ext.gen l) :=
    fun l => twistAut_algebraMap D (TD.τ (k • markPoint D)) l
  -- the torsor step: `θ` extends to an `L`-automorphism intertwining the two twisted actions
  obtain ⟨Θ, -, hΘ⟩ := exists_algEquiv_fixedField D.ext
    (WeierstrassCurve.Affine.FunctionField (baseCurve D))
    (twistAut D (TD.τ (markPoint D))) (twistAut D (TD.τ (k • markPoint D)))
    hα5 hβ5 hαne hβne hαL hβL θ
  -- node C2's classification of the `L`-automorphisms of `L(E)`
  obtain ⟨R, ε, hR⟩ := hC2 Θ
  rw [hR] at hΘ
  -- the arithmetic core: this conjugation equation is never satisfied
  exact torsor_step D TD hP k hk R ε hΘ

end

end Work.MotC
