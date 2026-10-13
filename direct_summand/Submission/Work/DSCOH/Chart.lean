/-
Area DSCOH (curric-46) — the chart Čech complex, as a cochain complex of `A`-modules.

`Work.DSCOH.chartCech ℳ` is the cochain complex whose `q`-th term is the product, over the
`(q+1)`-element subsets `S` of the index set, of the degree-zero part `degZero ℳ S` of the
localization of the graded module `M` at `X_S = ∏_{i ∈ S} Xᵢ`, with the alternating Čech
differential `cechDiff`.  Its cohomology is the algebraic model of `H^q(ℙⁿ, ℱ)` for the
quasi-coherent sheaf `ℱ` associated with `ℳ`.

The main result of the area is `Work.DSCOH.chartCech_finite_vanishing`: for `A` Noetherian and
`M` a finitely generated graded `A[X₀,…,X_{n-1}]`-module, the cohomology of the chart Čech
complex is a finitely generated `A`-module, and vanishes in degrees `> n` (because the complex
has length `n + 1`).
-/
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.cechDiff_comp

open MvPolynomial CategoryTheory

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
  [IsScalarTower A (Poly A n) M]

/-- **The chart Čech complex** of a graded module over `A[X₀,…,X_{n-1}]`, given a proof that
the alternating Čech differential squares to zero. -/
noncomputable def chartCechOf (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (h : ∀ q, (cechDiff (A := A) (n := n) (M := M) ℳ (q + 1)).comp
      (cechDiff (A := A) (n := n) (M := M) ℳ q) = 0) : CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of A (CechTerm (A := A) (n := n) (M := M) ℳ q))
    (fun q => ModuleCat.ofHom (cechDiff (A := A) (n := n) (M := M) ℳ q))
    (fun q => by
      rw [← ModuleCat.ofHom_comp, h q]
      exact ModuleCat.ofHom_zero)

/-- **The chart Čech complex** of a graded module over `A[X₀,…,X_{n-1}]`. -/
noncomputable def chartCech (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] :
    CochainComplex (ModuleCat A) ℕ :=
  chartCechOf ℳ fun q => cechDiff_comp (A := A) (n := n) (M := M) ℳ q

end Work.DSCOH
