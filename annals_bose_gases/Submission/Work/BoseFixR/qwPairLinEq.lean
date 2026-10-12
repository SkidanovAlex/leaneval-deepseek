import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB7.Estimates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.qwPairLinEq`

The pair operators `a_k + a_{-k}` and their "doubled" companions
`a_k + a_k† + a_{-k} + a_{-k}†` have the same quadratic form on the Fock space:

  `⟨f, (1/2)Σ_k c_k (a_k + a_k† + a_{-k} + a_{-k}†) f⟩ = ⟨(Σ_k c_k (a_k + a_{-k})) f, f⟩`.

The reason is that `a_i†` is the adjoint of `a_i` (`FockData.aDag_adjoint`) and
`bp` is symmetric (`FockData.bp_symm`), so each creation operator contributes
`⟨f, a_i†f⟩ = ⟨a_i f, f⟩ = ⟨f, a_i f⟩`: the form of `a_i + a_i†` is twice that of
`a_i`.  Hence the factor `1/2` in front of the four-term combination produces
exactly the two-term combination.

## Contents

* `bp_sum_smul_qw`, `qw_sum_smul_qw` — linearity of the Fock form `bp` / of the
  quadratic form `qw` in the first argument / in the operator.
* `qwPairLinEq` — the target identity.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixR

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

omit [DecidableEq Mode] in
/-- The Fock form is linear in its first argument along a weighted finite sum of
vectors: `⟨Σ_i w_i u_i, Φ⟩ = Σ_i w_i ⟨u_i, Φ⟩`. -/
lemma bp_sum_smul_qw (F : Work.BoseB7.FockData Mode) (Φ : F.H) {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (u : ι → F.H) :
    F.bp (∑ i ∈ s, w i • u i) Φ = ∑ i ∈ s, w i * F.bp (u i) Φ := by
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])

omit [DecidableEq Mode] in
/-- The quadratic form `qw` is linear in the operator along a weighted finite sum
of operators: `⟨Φ, (Σ_i w_i X_i) Φ⟩ = Σ_i w_i ⟨Φ, X_i Φ⟩`. -/
lemma qw_sum_smul_qw (F : Work.BoseB7.FockData Mode) (Φ : F.H) {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (∑ i ∈ s, w i • X i) = ∑ i ∈ s, w i * F.qw Φ (X i) := by
  have h : (∑ i ∈ s, w i • X i) Φ = ∑ i ∈ s, w i • (X i Φ) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => LinearMap.smul_apply (w i) (X i) Φ)
  unfold Work.BoseB7.FockData.qw
  rw [h, bp_sum_smul_qw F Φ]

/-- **The pair identity.**  For any coefficients `c : Mode → ℝ` and any `f` in the
Fock space, the quadratic form of the symmetrised pair operator
`(1/2)Σ_k c_k (a_k + a_k† + a_{-k} + a_{-k}†)` equals the quadratic form of the
pair operator `Σ_k c_k (a_k + a_{-k})`: the annihilation operators supply exactly
the same form as their adjoints, and the factor `1/2` compensates the doubling. -/
theorem qwPairLinEq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (c : Mode → ℝ) (f : F.H) :
    F.qw f (∑ k : Mode, (1 / 2 : ℝ) • (c k • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))))
      = F.bp ((∑ k : Mode, c k • (F.a k + F.a (-k))) f) f := by
  -- per-mode identity: the form of `a_k + a_k† + a_{-k} + a_{-k}†` is twice that of
  -- `a_k + a_{-k}`, because `⟨a_k† f, f⟩ = ⟨a_k f, f⟩`.
  have hper : ∀ k : Mode,
      ((1 / 2 : ℝ) * c k) * F.qw f (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))
        = c k * F.bp ((F.a k + F.a (-k)) f) f := by
    intro k
    have hq : F.qw f (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))
        = 2 * F.bp ((F.a k + F.a (-k)) f) f := by
      rw [Work.BoseB7.FockData.qw]
      simp only [LinearMap.add_apply, map_add]
      rw [F.aDag_adjoint k f f, F.bp_symm f (F.a k f),
          F.aDag_adjoint (-k) f f, F.bp_symm f (F.a (-k) f)]
      ring
    rw [hq]
    ring
  -- the left-hand side, expanded mode by mode
  have hL : F.qw f (∑ k : Mode,
        (1 / 2 : ℝ) • (c k • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))))
      = ∑ k : Mode,
          ((1 / 2 : ℝ) * c k) * F.qw f (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)) := by
    have hW : (∑ k : Mode,
          (1 / 2 : ℝ) • (c k • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))))
        = ∑ k : Mode,
            ((1 / 2 : ℝ) * c k) • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)) := by
      exact Finset.sum_congr rfl (fun k _ => by rw [smul_smul])
    rw [hW]
    exact qw_sum_smul_qw F f Finset.univ (fun k => (1 / 2 : ℝ) * c k)
      (fun k => F.a k + F.aDag k + F.a (-k) + F.aDag (-k))
  -- the right-hand side, expanded mode by mode
  have hR : F.bp ((∑ k : Mode, c k • (F.a k + F.a (-k))) f) f
      = ∑ k : Mode, c k * F.bp ((F.a k + F.a (-k)) f) f := by
    have hV : (∑ k : Mode, c k • (F.a k + F.a (-k))) f
        = ∑ k : Mode, c k • ((F.a k + F.a (-k)) f) := by
      rw [LinearMap.sum_apply]
      exact Finset.sum_congr rfl
        (fun k _ => LinearMap.smul_apply (c k) (F.a k + F.a (-k)) f)
    rw [hV]
    exact bp_sum_smul_qw F f Finset.univ c (fun k => (F.a k + F.a (-k)) f)
  rw [hL, hR]
  exact Finset.sum_congr rfl (fun k _ => hper k)

end Work.BoseFixR
