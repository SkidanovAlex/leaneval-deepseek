import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseBoxFock.K1dirBDefs
import Submission.Work.BoseBoxFock.L1Tails.chiBasicFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.continuous_partialFderiv_chiG`

The joint continuity of the partial derivative, in the first variable, of the `χχ`-row integrand
`(w,y) ↦ χ_ℓ(w) G(w,y)`: for `G` of class `C^∞` the map

`p ↦ ∑_j ‖∂_{e_j} (w' ↦ χ_ℓ(w') G(w', p.2)) (p.1)‖²`

is continuous on `ℝ³ × ℝ³` (`e_j` the coordinate vectors).  No hypothesis on `ℓ` is needed: the
corpus window `chiScale ℓ x = chi (ℓ⁻¹ • x)` is `C^∞` for every real `ℓ` (for `ℓ = 0` the inverse
is `0`, so the window is the constant `chi 0`).

The proof is the chain rule.  Writing `Φ(w,y) = χ_ℓ(w)G(w,y)` for the *jointly* smooth integrand,
the derivative in the first variable is the derivative of `Φ` along the inclusion of the first
factor,

`fderiv ℝ (w' ↦ χ_ℓ(w')G(w',y)) w = (fderiv ℝ Φ (w,y)).comp (inl ℝ E E)`,

which is continuous in `(w,y)` by `ContDiff.continuous_fderiv_apply`; the sum of squared norms is
then a continuous image.
-/

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The *jointly* smooth integrand `(w,y) ↦ χ_ℓ(w) G(w,y)` of the `χχ` row. -/
private noncomputable def chiGPair (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 × E3 → ℂ :=
  fun p => chiB ℓ p.1 * G p.1 p.2

private theorem contDiff_chiGPair {ℓ : ℝ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ContDiff ℝ (⊤ : ℕ∞) (chiGPair ℓ G) := by
  have hchi : ContDiff ℝ (⊤ : ℕ∞) (chiB ℓ) :=
    Complex.ofRealCLM.contDiff.comp (Work.BoseBoxFock.L1Tails.contDiff_chiScale ℓ)
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 × E3 => chiB ℓ p.1 * G p.1 p.2) :=
    (hchi.comp contDiff_fst).mul hG
  exact h

/-- The derivative in the first variable of `(w,y) ↦ χ_ℓ(w)G(w,y)` is the composition of the joint
derivative of `Φ` with the inclusion of the first factor. -/
private theorem fderiv_chiGPair_eq {ℓ : ℝ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (w y : E3) :
    fderiv ℝ (fun w' => chiB ℓ w' * G w' y) w
      = (fderiv ℝ (chiGPair ℓ G) (w, y)).comp (ContinuousLinearMap.inl ℝ E3 E3) := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (chiGPair ℓ G) := contDiff_chiGPair hG
  have hNN : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 :=
    WithTop.coe_ne_zero.mpr WithTop.top_ne_zero
  have h1 : HasFDerivAt (chiGPair ℓ G) (fderiv ℝ (chiGPair ℓ G) (w, y)) (w, y) :=
    ((hΦ.differentiable hNN) (w, y)).hasFDerivAt
  have h2 : HasFDerivAt (fun w' : E3 => (w', y)) (ContinuousLinearMap.inl ℝ E3 E3) w :=
    hasFDerivAt_prodMk_left w y
  have h3 : HasFDerivAt ((chiGPair ℓ G) ∘ fun w' : E3 => (w', y))
      ((fderiv ℝ (chiGPair ℓ G) (w, y)).comp (ContinuousLinearMap.inl ℝ E3 E3)) w :=
    h1.comp w h2
  have h4 : (fun w' : E3 => chiB ℓ w' * G w' y)
      = ((chiGPair ℓ G) ∘ fun w' : E3 => (w', y)) := rfl
  rw [h4, h3.fderiv]

theorem continuous_partialFderiv_chiG {ℓ : ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => Work.BoseBoxFock.K1dirB.chiB ℓ w' * G w' p.2) p.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (chiGPair ℓ G) := contDiff_chiGPair hG
  have hNN : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 :=
    WithTop.coe_ne_zero.mpr WithTop.top_ne_zero
  have hcontf : Continuous fun q : (E3 × E3) × (E3 × E3) =>
      (fderiv ℝ (chiGPair ℓ G) q.1) q.2 :=
    hΦ.continuous_fderiv_apply hNN
  rw [show (fun p : E3 × E3 => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiB ℓ w' * G w' p.2) p.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = (fun p : E3 × E3 => ∑ j : Fin 3,
      ‖(fderiv ℝ (chiGPair ℓ G) (p.1, p.2))
        (ContinuousLinearMap.inl ℝ E3 E3 (EuclideanSpace.single j (1 : ℝ)))‖ ^ 2) from by
    funext p
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [fderiv_chiGPair_eq hG p.1 p.2, ContinuousLinearMap.comp_apply]]
  refine continuous_finsetSum Finset.univ (fun j _ => ?_)
  exact (hcontf.comp (continuous_id.prodMk continuous_const)).norm.pow 2

end Work.BoseBoxFock.K1dirB
