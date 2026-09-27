import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.ematSpec

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

/-- The Minkowski pairing of the null vector `nvec ξ = (ξ,1)` with the hyperboloid lift
`hlift u` is the negative of the Busemann level `lev ξ u`. -/
lemma mink_nvec_hlift (n : ℕ) (ξ u : E n) :
    mink (nvec ξ) (hlift u) = - lev ξ u := by
  simp only [mink, lev, hlift, nvec, tpart, Sum.elim_inl, Sum.elim_inr, PiLp.inner_apply,
    Real.inner_apply]
  have hsum : (∑ i : Fin n, ξ i * u i) = ∑ i : Fin n, u i * ξ i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsum]; ring

/-- The Minkowski form is left-homogeneous in its first argument. -/
lemma mink_smul_left (n : ℕ) (r : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (r • x) y = r * mink x y := by
  simp only [mink, Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

/-- An element `g : PO(n,1)` fixing the boundary point `ξ` and lying on the horosphere of `ξ`
through the base point acts trivially on the null vector `nvec ξ = (ξ,1)`: the effective matrix
`emat g` fixes `nvec ξ`.

The proof identifies the eigenvalue of `emat g` on `nvec ξ` with the reciprocal of the Busemann
level shift `lev ξ (g • 0)`: the sheet lemma `emat g *ᵥ hlift u = hlift (g • u)` combined with the
Minkowski isometry property gives `λ · lev ξ (g • u) = lev ξ u` for all `u`, and the hypothesis
`busemann ξ (g • 0) = 0` says `lev ξ (g • 0) = 1 = lev ξ 0`, whence `λ = 1`. -/
theorem ematFix (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ)
    (hc : busemann ξ (g • (0 : E n)) = 0) :
    Matrix.mulVec (emat g) (nvec ξ) = nvec ξ := by
  obtain ⟨hsheet, hisom, heig⟩ := ematSpec g
  obtain ⟨c, hc0⟩ := (heig hξ).mp hg
  -- `nvec ξ` is an eigenvector of `emat g` with eigenvalue `λ = tsign (rep g) * c`
  have hlam : Matrix.mulVec (emat g) (nvec ξ) = (tsign (rep g) * c) • nvec ξ := by
    rw [emat, Matrix.smul_mulVec, hc0, smul_smul]
  -- the level at the base point and at `g • 0`
  have hlev0 : lev ξ (0 : E n) = 1 := by
    simp [lev, tpart_zero]
  have hlevg0 : lev ξ (g • (0 : E n)) = 1 := by
    rw [lev_eq_exp hξ, hc, Real.exp_zero]
  -- Minkowski pairings of `nvec ξ` with the two lifts
  have e1 : mink (nvec ξ) (hlift (g • (0 : E n))) = - lev ξ (g • (0 : E n)) :=
    mink_nvec_hlift n ξ _
  have e2 : mink (nvec ξ) (hlift (0 : E n)) = - lev ξ (0 : E n) :=
    mink_nvec_hlift n ξ 0
  -- the eigenvalue equation in Minkowski-form language
  have step : (tsign (rep g) * c) * mink (nvec ξ) (hlift (g • (0 : E n)))
      = mink (nvec ξ) (hlift (0 : E n)) := by
    rw [← mink_smul_left n (tsign (rep g) * c) (nvec ξ) (hlift (g • (0 : E n))),
      ← hlam, ← hsheet (0 : E n), hisom (nvec ξ) (hlift (0 : E n))]
  have key : (tsign (rep g) * c) * lev ξ (g • (0 : E n)) = lev ξ 0 := by
    have h := step
    rw [e1, e2] at h
    linarith
  have hlam1 : tsign (rep g) * c = 1 := by
    have h := key
    rw [hlevg0, hlev0, mul_one] at h
    exact h
  rw [hlam, hlam1, one_smul]

end Work.Mostow
