/-
Area DSCOH (curric-46) — the chart Čech complex of a graded module over `A[x₀,…,x_{n-1}]`.

This is the algebraic model of the Čech complex of the structure sheaf of `ℙⁿ` (or of a
quasi-coherent sheaf on it) with respect to the standard affine cover by the charts
`D₊(Xᵢ)`: its `q`-th term is the product, over the `(q+1)`-element subsets `S` of the index
set, of the degree-zero part of the localization of the graded module at `X_S = ∏_{i∈S} Xᵢ`.

`cechDiff` is the alternating Čech differential; `Work.DSCOH.cechDiff_comp` proves that it
squares to zero, so that `Work.DSCOH.chartCech` is a cochain complex.
-/
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.resAt_degZero
import Submission.Work.DSCOH.degZero_locMapOf

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
  [IsScalarTower A (Poly A n) M]
variable {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N]
  [IsScalarTower A (Poly A n) N]

/-- The `q`-th term of the chart Čech complex: the product over the `(q+1)`-element subsets `S`
of the index set of the degree-zero part of the localization at the monomial `X_S`. -/
abbrev CechTerm (ℳ : ℕ → Submodule A M) (q : ℕ) : Type _ :=
  ∀ S : {S : Finset (Fin n) // S.card = q + 1}, degZero (A := A) ℳ S.1

/-- The `T`-component of the Čech differential: the alternating sum, over the elements `i` of
`T`, of the structure map from the `(T.erase i)`-component, with sign `(-1)^{#{j ∈ T : j < i}}`.
These are the standard signs for which `d² = 0`. -/
noncomputable def cechDiffComp (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (q : ℕ) (T : {S : Finset (Fin n) // S.card = q + 1 + 1}) :
    CechTerm (A := A) (n := n) (M := M) ℳ q →ₗ[A] degZero (A := A) ℳ T.1 :=
  ∑ i ∈ T.1.attach,
    (-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card •
      ((degPartRestrict (A := A) (n := n) (M := M) ℳ
          (S := T.1.erase i.1) (T := T.1)
          (resAt (n := n) (M := M) (Finset.erase_subset i.1 T.1))
          (fun x hx => resAt_degZero (A := A) (n := n) (M := M) (ℳ := ℳ)
            (Finset.erase_subset i.1 T.1) x hx)).comp
        (LinearMap.proj (R := A)
          (φ := fun S : {S : Finset (Fin n) // S.card = q + 1} => degZero (A := A) ℳ S.1)
          ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩))

/-- The alternating Čech differential of the chart cover. -/
noncomputable def cechDiff (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (q : ℕ) :
    CechTerm (A := A) (n := n) (M := M) ℳ q →ₗ[A] CechTerm (A := A) (n := n) (M := M) ℳ (q + 1) :=
  LinearMap.pi (R := A) fun T => cechDiffComp (A := A) (n := n) (M := M) ℳ q T

/-- The map of chart Čech complexes induced by a map of graded modules. -/
noncomputable def cechMap (ℳ : ℕ → Submodule A M) (𝒩 : ℕ → Submodule A N)
    (φ : M →ₗ[Poly A n] N) (hφ : ∀ d, Submodule.map (φ.restrictScalars A) (ℳ d) ≤ 𝒩 d)
    (q : ℕ) :
    CechTerm (A := A) (n := n) (M := M) ℳ q →ₗ[A]
      CechTerm (A := A) (n := n) (M := N) 𝒩 q :=
  LinearMap.pi (R := A) fun S =>
    (degZeroMapOf (A := A) (n := n) ℳ 𝒩 φ S.1
      (fun x hx => degZero_locMapOf (A := A) (n := n) ℳ 𝒩 φ hφ S.1 x hx)).comp
      (LinearMap.proj (R := A)
        (φ := fun S : {S : Finset (Fin n) // S.card = q + 1} => degZero (A := A) ℳ S.1) S)

end Work.DSCOH
