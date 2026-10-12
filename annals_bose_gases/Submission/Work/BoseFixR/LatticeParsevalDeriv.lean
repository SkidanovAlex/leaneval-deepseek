import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Submission.Work.BoseFixR.LatticeParsevalDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatticeParsevalDeriv` — the directional derivative of a lattice character

`labChar ℓ N k y = exp (i ⟪k, y⟫)` is differentiable in `y`, with direction derivative
`i ⟪k, ·⟫ * labChar ℓ N k y`.  This is the Leibniz/chain-rule input for the lattice
Parseval identity `LatticeW1sqParseval` (the `∇`-form of the mode expansion): differentiating
`∑_k d k · labChar k` in the coordinate direction `single i 1` multiplies the `k`-th
coefficient by the `i`-component `kmomLab ℓ N k i` of its momentum.

The main lemma is `LatticeParsevalDeriv`; the auxiliary `labChar_hasFDerivAt` records the
per-character derivative (`Complex.exp ∘ (i ⟪k, ·⟫)`, chain rule at the two outer maps).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixR

open Work.BoseBoxFock (kmomLab Lab)

/-- The directional derivative of a single lattice character: the chain rule for
`y ↦ Complex.exp (i ⟪k, y⟫)`. -/
lemma labChar_hasFDerivAt (ℓ : ℝ) (N : ℕ) (k : Lab N)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (labChar ℓ N k)
      (Complex.exp (Complex.I * ((inner ℝ (kmomLab ℓ N k) x : ℝ) : ℂ)) •
        (Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ (kmomLab ℓ N k))))) x := by
  -- the inner product, as a `ℂ`-valued function, is the continuous linear map
  -- `ofRealCLM ∘ innerSL`
  have hbase : HasFDerivAt (⇑(Complex.ofRealCLM.comp (innerSL ℝ (kmomLab ℓ N k))))
      (Complex.ofRealCLM.comp (innerSL ℝ (kmomLab ℓ N k))) x :=
    ContinuousLinearMap.hasFDerivAt _
  have hfun : (⇑(Complex.ofRealCLM.comp (innerSL ℝ (kmomLab ℓ N k))))
      = (fun y : EuclideanSpace ℝ (Fin 3) =>
          ((inner ℝ (kmomLab ℓ N k) y : ℝ) : ℂ)) := by
    funext y
    simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, innerSL_apply_apply]
  rw [hfun] at hbase
  -- multiply by `i` and exponentiate
  exact (hbase.const_mul Complex.I).cexp

theorem LatticeParsevalDeriv {ℓ : ℝ} (N : ℕ) (K : Finset (Work.BoseBoxFock.Lab N))
    (d : Work.BoseBoxFock.Lab N → ℂ) (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        ∑ k ∈ K, d k * Work.BoseFixR.labChar ℓ N k y) x
        (EuclideanSpace.single i 1)
      = ∑ k ∈ K, (d k * (Complex.I * ((Work.BoseBoxFock.kmomLab ℓ N k i : ℝ) : ℂ)))
          * Work.BoseFixR.labChar ℓ N k x := by
  have hchar : ∀ k : Lab N,
      HasFDerivAt (labChar ℓ N k)
        (Complex.exp (Complex.I * ((inner ℝ (kmomLab ℓ N k) x : ℝ) : ℂ)) •
          (Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ (kmomLab ℓ N k))))) x :=
    fun k => labChar_hasFDerivAt ℓ N k x
  -- differentiate the finite sum term by term
  have hsum := HasFDerivAt.sum (u := K) (fun k _ => (hchar k).const_mul (d k))
  have hfun : (∑ k ∈ K, fun y : EuclideanSpace ℝ (Fin 3) =>
      d k * labChar ℓ N k y)
      = (fun y : EuclideanSpace ℝ (Fin 3) => ∑ k ∈ K, d k * labChar ℓ N k y) := by
    funext y
    simp
  rw [hfun] at hsum
  rw [hsum.fderiv]
  -- evaluate the derivative on the coordinate direction `single i 1`
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, innerSL_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [EuclideanSpace.inner_single_right]
  simp only [one_mul, labChar_apply, starRingEnd_apply, star_trivial]
  ring

end Work.BoseFixR
