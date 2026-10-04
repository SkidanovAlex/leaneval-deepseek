/-
# The manifold layer: agreement of the chart nonlinearity with the coordinate DeTurck operator

`Work.Diff.STE.Man.chartNonlin bg` is defined with its principal part made explicit
(`secOpFlat A B + N`), so that it satisfies `IsDeTurckNonlin` for *all* jets.  On the jets that
actually occur (jets of a smooth symmetric, real metric), it agrees with the coordinate DeTurck
operator `pPhi`; this file records that agreement (`chartNonlin_eq_pPhi`) and the resulting
symmetry in the two matrix indices (`chartNonlin_symm`).
-/
import Mathlib
import Submission.Work.Diff.STE.Man.Defs
import Submission.Work.Diff.STE.deTurck.pPhi_decomp
import Submission.Work.Diff.STE.deTurck.pPhi_symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.Man

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

noncomputable section

open Work.Diff.STE.Flat Work.Diff.STE.DeTurck Work.Diff.EXT Work.Diff.STE.deTurck

/-- The two principal parts agree: `secOpFlat A B` is the complex cast of the coordinate principal
part `secOp (reMat A) B'` whenever the second jet `B` is real-valued. -/
lemma secOpFlat_eq_secOp (A : MatC (dim E)) (B : Fin (dim E) → Fin (dim E) → MatC (dim E))
    (hBim : ∀ c d i j, (B c d i j).im = 0) :
    secOpFlat A B
      = ofRealMat (secOp (reMatE A) (bilMatOf (E := E) (fun c d => reMatE (B c d)))) := by
  funext i j
  have hcoe : ∀ c d : Fin (dim E), (((reMat A)⁻¹) c d : ℂ) * B c d i j
      = ((((reMat A)⁻¹) c d * (B c d i j).re : ℝ) : ℂ) := by
    intro c d
    have him : B c d i j = ((B c d i j).re : ℂ) :=
      Complex.ext rfl (by simpa using hBim c d i j)
    rw [him, ← Complex.ofReal_mul]; simp
  simp only [secOpFlat, secOp, ofRealMat_apply, bilMatOf_bB, reMatE, reMat, jInv,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  exact hcoe c d

/-- The symmetry of the lower-order part `pN` of the coordinate DeTurck operator in its two matrix
indices, for a symmetric value and a symmetric first jet. -/
lemma pN_symm (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E)
    (A : MatE (E := E)) (L : LinMat E)
    (hA : ∀ i j, A i j = A j i)
    (hL : ∀ (a : Fin (dim E)) (i j : Fin (dim E)),
      L (bB (E := E) a) i j = L (bB (E := E) a) j i) :
    ∀ i j, pN Abar Lbar Bbar A L i j = pN Abar Lbar Bbar A L j i :=
  fun i j => pPhi_symm A L (0 : BilMat E) Abar Lbar Bbar hA hL
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) i j

/-- **Agreement of the chart nonlinearity with the coordinate DeTurck operator on metric jets.**
If the jet `(A, L, B)` has the symmetries of a smooth symmetric real metric (`A`, `L` symmetric in
the matrix indices, `B` symmetric in the derivative slots and in the matrix indices, and `B`
real-valued), then `chartNonlin bg` agrees there with `pPhi`. -/
theorem chartNonlin_eq_pPhi (bg : (Fin (dim E) → ℝ) → MatE (E := E))
    (x : Fin (dim E) → ℝ) (A : MatC (dim E)) (L : Fin (dim E) → MatC (dim E))
    (B : Fin (dim E) → Fin (dim E) → MatC (dim E))
    (hA : ∀ i j, A i j = A j i)
    (hL : ∀ c i j, L c i j = L c j i)
    (hB1 : ∀ c d, B c d = B d c)
    (hB2 : ∀ c d i j, B c d i j = B c d j i)
    (hBim : ∀ c d i j, (B c d i j).im = 0)
    (hdet : (Matrix.of (reMatE A)).det ≠ 0) :
    chartNonlin bg (x, (A, L, B))
      = ofRealMat (pPhi (bg x)
          (linMatOf (E := E) (fun c => dpd (E := E) c bg x))
          (bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) x))
          (reMatE A) (linMatOf (E := E) (fun c => reMatE (L c)))
          (bilMatOf (E := E) (fun c d => reMatE (B c d)))) := by
  have hA' : ∀ i j, (reMatE A) i j = (reMatE A) j i := fun i j => by
    simp only [reMatE_apply]; rw [hA i j]
  have hL' : ∀ a i j, (linMatOf (E := E) (fun c => reMatE (L c))) (bB (E := E) a) i j
      = (linMatOf (E := E) (fun c => reMatE (L c))) (bB (E := E) a) j i := by
    intro a i j
    simp only [linMatOf_bB, reMatE_apply]; rw [hL a i j]
  have hB1' : ∀ m a b c, (bilMatOf (E := E) (fun c d => reMatE (B c d)))
        (bB (E := E) m) (bB (E := E) a) b c
      = (bilMatOf (E := E) (fun c d => reMatE (B c d))) (bB (E := E) a) (bB (E := E) m) b c := by
    intro m a b c
    simp only [bilMatOf_bB, reMatE_apply]; rw [hB1 m a]
  have hB2' : ∀ m a b c, (bilMatOf (E := E) (fun c d => reMatE (B c d)))
        (bB (E := E) m) (bB (E := E) a) b c
      = (bilMatOf (E := E) (fun c d => reMatE (B c d))) (bB (E := E) m) (bB (E := E) a) c b := by
    intro m a b c
    simp only [bilMatOf_bB, reMatE_apply]; rw [hB2 m a b c]
  have hdec := pPhi_decomp (Abar := bg x)
    (Lbar := linMatOf (E := E) (fun c => dpd (E := E) c bg x))
    (Bbar := bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) x))
    (A := reMatE A) (L := linMatOf (E := E) (fun c => reMatE (L c)))
    (B := bilMatOf (E := E) (fun c d => reMatE (B c d))) hA' hL' hB1' hB2' hdet
  have hN : chartNonlinN bg (x, (A, L))
      = ofRealMat (pN (bg x)
          (linMatOf (E := E) (fun c => dpd (E := E) c bg x))
          (bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) x))
          (reMatE A) (linMatOf (E := E) (fun c => reMatE (L c)))) := rfl
  rw [chartNonlin_eq_secOpFlat_add, hN, secOpFlat_eq_secOp A B hBim, ← ofRealMat_add, ← hdec]

/-- **Symmetry of the chart nonlinearity in the matrix indices** on symmetric jets: this is the
hypothesis `hsymΦ` of `Work.Diff.STE.Flat.TorusShortTimeExistenceSymm`. -/
theorem chartNonlin_symm (bg : (Fin (dim E) → ℝ) → MatE (E := E))
    (x : Fin (dim E) → ℝ) (A : MatC (dim E)) (L : Fin (dim E) → MatC (dim E))
    (B : Fin (dim E) → Fin (dim E) → MatC (dim E))
    (hA : ∀ i j, A i j = A j i)
    (hL : ∀ c i j, L c i j = L c j i)
    (hB1 : ∀ c d, B c d = B d c)
    (hB2 : ∀ c d i j, B c d i j = B c d j i) :
    ∀ i j, chartNonlin bg (x, (A, L, B)) i j = chartNonlin bg (x, (A, L, B)) j i := by
  have hsec : ∀ i j, secOpFlat A B i j = secOpFlat A B j i := by
    intro i j
    simp only [secOpFlat]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => by rw [hB2 c d i j]))
  have hA' : ∀ i j, (reMatE A) i j = (reMatE A) j i := fun i j => by
    simp only [reMatE_apply]; rw [hA i j]
  have hL' : ∀ a i j, (linMatOf (E := E) (fun c => reMatE (L c))) (bB (E := E) a) i j
      = (linMatOf (E := E) (fun c => reMatE (L c))) (bB (E := E) a) j i := by
    intro a i j
    simp only [linMatOf_bB, reMatE_apply]; rw [hL a i j]
  have hN := pN_symm (bg x)
    (linMatOf (E := E) (fun c => dpd (E := E) c bg x))
    (bilMatOf (E := E) (fun c d => dpd (E := E) c (dpd (E := E) d bg) x))
    (reMatE A) (linMatOf (E := E) (fun c => reMatE (L c))) hA' hL'
  intro i j
  simp only [chartNonlin_eq_secOpFlat_add, chartNonlinN, Pi.add_apply]
  rw [hsec i j, hN i j]

end

end Work.Diff.STE.Man
