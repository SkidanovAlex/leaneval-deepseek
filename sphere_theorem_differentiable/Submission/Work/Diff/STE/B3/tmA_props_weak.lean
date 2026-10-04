/-
# The structural clauses of `tmA` without the first-derivative hypothesis

`Work.Diff.STE.B3.tmA_props` bundles six clauses for `tmA φ lam' γ`, but two of them (the pointwise
bound and the first-derivative bound) need a bound on the *first derivatives* of `γ` on the support
ball.  The four *structural* clauses -- symmetry, ellipticity, smoothness and `1`-periodicity -- do
not: symmetry and ellipticity only use the corresponding properties of `γ`, and smoothness and
periodicity only use that `γ` is smooth on the support ball.  This file records exactly those four
clauses, so that they can be used when the derivative bound of `γ` is not available (e.g. for the
`k = 0` case of `Work.Diff.STE.B3.transport_deTurck_general`, where only the *value* bound of `γ`
follows from the jet hypotheses).

The proofs are copies of the corresponding clauses of `Work.Diff.STE.B3.tmA_props`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.tmA_props

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.STE.B3

/-- **The structural clauses of the periodic coefficient matrix `tmA φ lam' γ`.**  Given a cutoff `φ`
supported in the ball of radius `R ≤ 1/2` and a coefficient family `γ`, symmetric and `c`-elliptic
on that ball (with `0 < lam' ≤ c`), the matrix `tmA φ lam' γ` is symmetric, `lam'`-elliptic, smooth
and `1`-periodic.

No hypothesis on the *derivatives* of `γ` is needed; the pointwise and first-derivative bounds of
`Work.Diff.STE.B3.tmA_props` are not part of this statement. -/
theorem tmA_props_weak {n : ℕ} (R c : ℝ) (hR : R ≤ 1 / 2) (hc : 0 < c) :
    ∀ (φ : (Fin n → ℝ) → ℝ) (γ : (Fin n → ℝ) → Fin n → Fin n → ℝ) (lam' : ℝ),
      0 < lam' → lam' ≤ c →
      ContDiff ℝ (⊤ : ℕ∞) φ → (∀ z, 0 ≤ φ z) → (∀ z, φ z ≤ 1) →
      tsupport φ ⊆ Metric.ball 0 R →
      (∀ p q, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => γ w p q) (Metric.ball 0 R)) →
      (∀ z ∈ Metric.ball 0 R, ∀ p q, γ z p q = γ z q p) →
      (∀ z ∈ Metric.ball 0 R, ∀ ξ : Fin n → ℝ,
        c * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, γ z p q * ξ p * ξ q) →
      (∀ z p q, tmA φ lam' γ z p q = tmA φ lam' γ z q p) ∧
      (∀ z ξ : Fin n → ℝ,
        lam' * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, tmA φ lam' γ z p q * ξ p * ξ q) ∧
      ContDiff ℝ (⊤ : ℕ∞) (tmA φ lam' γ) ∧
      Work.Diff.STE.Periodic1 (tmA φ lam' γ) := by
  intro φ γ lam' hlam hlamc hφ hφ0 hφ1 hφts hγs hγsymm hγpos
  have hφsupp : Function.support φ ⊆ Metric.ball 0 R :=
    fun x hx => hφts (subset_tsupport φ hx)
  have hgmcube : ∀ p q : Fin n, Function.support (gm φ γ lam' p q) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun p q x hx => ball_subset_cube hR (hφsupp (support_gm_subset (γ := γ) (lam' := lam') p q hx))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- symmetry
    intro z p q
    by_cases hpq : p = q
    · subst hpq; rfl
    · rw [tmA_eq_govIdx φ γ hR hφsupp z p q, tmA_eq_govIdx φ γ hR hφsupp z q p]
      by_cases hw : φ (z + iVec (govIdx φ z)) = 0
      · rw [if_neg hpq, if_neg (fun h : q = p => hpq h.symm), hw, zero_mul, zero_mul]
      · rw [if_neg hpq, if_neg (fun h : q = p => hpq h.symm),
          hγsymm _ (hφsupp (Function.mem_support.mpr hw)) p q]
  · -- positive definiteness
    intro z ξ
    have hexp : (∑ p, ∑ q, tmA φ lam' γ z p q * ξ p * ξ q)
        = (∑ p, ∑ q, (if p = q then lam' else 0) * ξ p * ξ q)
          + φ (z + iVec (govIdx φ z))
            * (∑ p, ∑ q, (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))
                * ξ p * ξ q) := by
      have h1 : ∀ p q : Fin n, tmA φ lam' γ z p q
          = (if p = q then lam' else 0) + φ (z + iVec (govIdx φ z))
              * (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0)) :=
        fun p q => tmA_eq_govIdx φ γ hR hφsupp z p q
      simp only [h1]
      rw [sum_sum_add]
      rw [sum_sum_smul]
    rw [hexp, sum_ite_delta]
    have hkey : 0 ≤ φ (z + iVec (govIdx φ z))
        * (∑ p, ∑ q, (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))
            * ξ p * ξ q) := by
      have hγm : (∑ p, ∑ q, (γ (z + iVec (govIdx φ z)) p q - (if p = q then lam' else 0))
            * ξ p * ξ q)
          = (∑ p, ∑ q, γ (z + iVec (govIdx φ z)) p q * ξ p * ξ q)
            - lam' * ∑ p, (ξ p) ^ 2 := by
        rw [sum_sum_sub, sum_ite_delta]
      rw [hγm]
      by_cases hw : φ (z + iVec (govIdx φ z)) = 0
      · rw [hw, zero_mul]
      · have hwb : z + iVec (govIdx φ z) ∈ Metric.ball 0 R :=
          hφsupp (Function.mem_support.mpr hw)
        have hpos := hγpos _ hwb ξ
        have hnorm : (0 : ℝ) ≤ ∑ p, (ξ p) ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
        have : (0 : ℝ) ≤ (∑ p, ∑ q, γ (z + iVec (govIdx φ z)) p q * ξ p * ξ q)
            - lam' * ∑ p, (ξ p) ^ 2 := by nlinarith [hpos, hlamc, hnorm]
        exact mul_nonneg (hφ0 _) this
    linarith
  · -- smoothness
    refine contDiff_pi' (fun p => contDiff_pi' (fun q => ?_))
    have hs : ContDiff ℝ (⊤ : ℕ∞) (tmPer (gm φ γ lam' p q)) :=
      contDiff_tmPer (contDiff_gm p q hφ hφts (hγs p q)) (hgmcube p q)
    have heq : (fun z => tmA φ lam' γ z p q)
        = fun z => (if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) z := rfl
    rw [heq]
    exact contDiff_const.add hs
  · -- periodicity
    intro i x
    ext p q
    have hper : Work.Diff.STE.Periodic1 (tmPer (gm φ γ lam' p q)) :=
      periodic_tmPer (contDiff_gm p q hφ hφts (hγs p q)) (hgmcube p q)
    have hval := hper i x
    have h1 : tmA φ lam' γ (x + Pi.single i 1) p q
        = (if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) (x + Pi.single i 1) := rfl
    have h2 : tmA φ lam' γ x p q
        = (if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) x := rfl
    rw [h1, h2, hval]

end Work.Diff.STE.B3
