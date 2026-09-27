import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.ematSpec

/-!
# Fixed boundary points of `g ∈ PO(n,1)` vs eigen-directions of `emat g`

`bd g ξ = ξ` (`ξ ∈ Sph n`, i.e. `ξ` is a null direction) holds exactly when the null
vector `nvec ξ = (ξ,1)` is an eigenvector of the effective matrix `emat g` with a
**non-zero** eigenvalue.

This is the sharp form of the third part of `Work.Mostow.ematSpec` (which characterises
the fixed directions of `mat (rep g)`), combined with the fact that
`emat g = tsign (rep g) • mat (rep g)` with `tsign (rep g) = ±1`: multiplying an
eigen-direction by the scalar `±1` neither creates nor destroys non-zero eigenvalues.

The hypothesis `POActionProp n` is not needed: `bd` and `emat` are both built from the
chosen representative `rep g = Quotient.out g`.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

variable {n : ℕ}

/-- The null vector `nvec ξ = (ξ,1)` is non-zero. -/
lemma nvec_ne_zero (ξ : E n) : nvec ξ ≠ 0 := by
  intro h
  have := congrFun h (Sum.inr 0)
  simp [nvec] at this

/-- `emat g = tsign (rep g) • mat (rep g)`, hence `emat g *ᵥ v = tsign (rep g) • (mat (rep g) *ᵥ v)`. -/
lemma emat_mulVec_eq (g : PO n 1) (v : Fin n ⊕ Fin 1 → ℝ) :
    Matrix.mulVec (emat g) v = tsign (rep g) • Matrix.mulVec (mat (rep g)) v := by
  rw [emat, Matrix.smul_mulVec]

/-- The eigenvalue `c` of an eigen-direction of `mat (rep g)` at a *boundary* point is non-zero. -/
lemma eigenval_ne_zero_of_bd (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (c : ℝ)
    (hc : Matrix.mulVec (mat (rep g)) (nvec ξ) = c • nvec ξ) : c ≠ 0 := by
  intro h0
  have h1 : (Matrix.mulVec (mat (rep g)) (nvec ξ)) (Sum.inr 0) = 0 := by
    rw [hc, h0]
    simp [nvec]
  exact (mat_mulVec_theta_ne_zero (rep g) hξ) h1

theorem bdFixIff (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (g : PO n 1) (ξ : E n)
    (hξ : ξ ∈ Sph n) :
    bd g ξ = ξ ↔ ∃ μ : ℝ, μ ≠ 0 ∧ Matrix.mulVec (emat g) (nvec ξ) = μ • nvec ξ := by
  rw [(ematSpec g).2.2 hξ]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨tsign (rep g) * c, mul_ne_zero (tsign_ne_zero (rep g))
        (eigenval_ne_zero_of_bd g ξ hξ c hc),
      by rw [emat_mulVec_eq, hc, ← smul_smul]⟩
  · rintro ⟨μ, hμ, hμeq⟩
    refine ⟨tsign (rep g) * μ, ?_⟩
    have h1 : tsign (rep g) • Matrix.mulVec (mat (rep g)) (nvec ξ) = μ • nvec ξ := by
      rw [← emat_mulVec_eq]; exact hμeq
    have h2 := congrArg (fun w => tsign (rep g) • w) h1
    simp only [smul_smul, tsign_sq (rep g), one_smul] at h2
    exact h2

end Work.Mostow
