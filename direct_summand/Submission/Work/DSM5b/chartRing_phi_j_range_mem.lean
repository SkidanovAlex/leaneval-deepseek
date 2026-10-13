import Mathlib
import Submission.Work.DSM5b.CycleDefs
import Submission.Work.DSM5b.chartRing_mem_pow
import Submission.Work.DSM5b.mem_pow_ideal_sum_prod
import Submission.Work.DSM5b.ccRestr_right_mul_ccRestr_left_uj_eq
import Submission.Work.DSM5b.psi_sum_prod_eq
import Submission.Work.DSM5b.chartRing_sum_mul_eq_algebraMap

namespace Work.DSM5b

open DSMap DSMap.Mix2

universe a

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- **The core valuation estimate of the valuative criterion for the chart Čech complex.**

Setting: `R` a commutative ring, `t : ι → R`, `A ⊆ K` a valuation ring
(`[IsDomain A] [ValuationRing A] [Algebra A K] [IsFractionRing A K]`), `φ : R →+* A`, and
`ψ : chartRing t {i} →+* K` compatible with `φ`.  Fix a family `u : ι → chartRing t {i}` of
generators of the `i`-th chart: `(u l) * algebraMap (t i) = algebraMap (t l)` for all `l`.

Suppose `j` is a "value-maximal" index: for every `l` there is `a : A` with
`ψ (u l) = algebraMap A K a * ψ (u j)`, and `ψ (u j) ≠ 0`.

Let `χ : chartRing t ({i} ∪ {j}) →+* K` be any ring map extending `ψ` along the restriction map
`ccRestr t (Finset.subset_union_left)`.

CONCLUSION: every element of the `j`-th chart, restricted to the overlap `{i} ∪ {j}` and then
evaluated by `χ`, lies in the image of `A`:
`∀ z : chartRing t {j}, χ (ccRestr t (Finset.subset_union_right) z) ∈ (algebraMap A K).range`.

Suggested proof route (see also `Submission/Work/DSM5b/chartRing_div_mem_of_mem_pow.lean`, which
supplies `c / (t i) ^ n ∈ chartRing t {i}` for `c ∈ J ^ n`): write `z = c / t j ^ a` with
`c ∈ J ^ a` (`Work.DSM5b.chartRing_mem_pow`).  In the overlap ring `chartRing t ({i} ∪ {j})` one
has `t j / t i = ccRestr (subset_union_left) (u j)` (use `hu` and the fact that the image of
`t i` is a nonzerodivisor of `Localization.Away (tS t ({i} ∪ {j}))`), hence
`χ (t i / t j) = (ψ (u j))⁻¹` by `hχ` and `hne`; and `z = (c / t i ^ a) * (t i / t j) ^ a`.  Expand
`c = ∑ b, d b * ∏ k, t (b k)` with `b : Fin a → ι` (`Work.DSM5b.mem_pow_ideal_sum_prod`) to get
`ψ (c / t i ^ a) = ∑ b φ (d b) * ∏ k ψ (u (b k))`, and use `hmax` to rewrite each `ψ (u (b k))` as
`algebraMap A K (a (b k)) * ψ (u j)`; the whole expression is then
`(∑ b φ (d b) * ∏ k a (b k)) * (ψ (u j)) ^ a` with the bracket in `A`, so
`χ (locRes z) ∈ A` by `hne`.  Translating `∈ (algebraMap A K).range` with
`ValuationRing.mem_integer_iff` and `Valuation.mem_integer_iff` finishes. -/
theorem chartRing_phi_j_range_mem {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) {A K : Type a} [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] (φ : R →+* A) (i j : ι)
    (u : ι → ↥(DSMap.Mix2.chartRing t {i}))
    (hu : ∀ l : ι, (u l : Localization.Away (DSMap.Mix2.tS t {i}))
        * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l))
    (ψ : ↥(DSMap.Mix2.chartRing t {i}) →+* K)
    (hcompat : ψ.comp (algebraMap R ↥(DSMap.Mix2.chartRing t {i})) = (algebraMap A K).comp φ)
    (hmax : ∀ l : ι, ∃ a : A, ψ (u l) = algebraMap A K a * ψ (u j))
    (hne : ψ (u j) ≠ 0)
    (χ : ↥(DSMap.Mix2.chartRing t ({i} ∪ {j})) →+* K)
    (hχ : χ.comp (ccRestr t (Finset.subset_union_left)).toRingHom = ψ) :
    ∀ z : ↥(DSMap.Mix2.chartRing t {j}),
      χ (ccRestr t (Finset.subset_union_right) z) ∈ (algebraMap A K).range := by
  intro z
  classical
  -- Write `z = c / t j ^ n` with `c ∈ J ^ n`, `J = (t_k)`.
  obtain ⟨n, c, hc, hzc⟩ := chartRing_mem_pow t {j} z
  -- Expand `c = ∑_b d b * ∏_k t (b k)` in the monomials of `J ^ n`.
  obtain ⟨B, d, hcd⟩ := mem_pow_ideal_sum_prod t n c hc
  -- The corresponding element of the `i`-th chart, `∑_b d b * ∏_k u (b k) = c / t i ^ n`.
  set w : ↥(chartRing t {i})
    := ∑ b ∈ B, algebraMap R ↥(chartRing t {i}) (d b) * ∏ k, u (b k) with hwdef
  have hw : (w : Localization.Away (tS t {i}))
      * (algebraMap R (Localization.Away (tS t {i})) (tS t {i})) ^ n
      = algebraMap R (Localization.Away (tS t {i})) c := by
    rw [hwdef]
    exact chartRing_sum_mul_eq_algebraMap t i n c B d hcd u hu
  -- In the overlap chart, `z * (t j / t i) ^ n = w`.
  have hA : ccRestr t (Finset.subset_union_right) z
      * (ccRestr t (Finset.subset_union_left) (u j)) ^ n
      = ccRestr t (Finset.subset_union_left) w :=
    ccRestr_right_mul_ccRestr_left_uj_eq t i j u hu n c z hzc w hw
  -- The value-maximality data, as a single function `a : ι → A`.
  let a : ι → A := fun l => Classical.choose (hmax l)
  have ha : ∀ l, ψ (u l) = algebraMap A K (a l) * ψ (u j) :=
    fun l => Classical.choose_spec (hmax l)
  -- `ψ w = (∑_b φ (d b) * ∏_k a (b k)) * (ψ (u j)) ^ n`.
  have hψ : ψ w = algebraMap A K (∑ b ∈ B, φ (d b) * ∏ k, a (b k)) * (ψ (u j)) ^ n := by
    rw [hwdef]
    exact psi_sum_prod_eq t φ i j u ψ hcompat a ha n B d
  -- `χ` agrees with `ψ` on the image of the `i`-th chart.
  have hχuj : χ (ccRestr t (Finset.subset_union_left) (u j)) = ψ (u j) := by
    have h := RingHom.congr_fun hχ (u j)
    simp only [RingHom.comp_apply] at h
    exact h
  have hχw : χ (ccRestr t (Finset.subset_union_left) w) = ψ w := by
    have h := RingHom.congr_fun hχ w
    simp only [RingHom.comp_apply] at h
    exact h
  have key : χ (ccRestr t (Finset.subset_union_right) z) * (ψ (u j)) ^ n = ψ w := by
    calc χ (ccRestr t (Finset.subset_union_right) z) * (ψ (u j)) ^ n
        = χ (ccRestr t (Finset.subset_union_right) z)
            * (χ (ccRestr t (Finset.subset_union_left) (u j))) ^ n := by rw [hχuj]
      _ = χ (ccRestr t (Finset.subset_union_right) z
            * (ccRestr t (Finset.subset_union_left) (u j)) ^ n) := by rw [map_mul, map_pow]
      _ = χ (ccRestr t (Finset.subset_union_left) w) := congrArg χ hA
      _ = ψ w := hχw
  -- Cancel the nonzero factor `(ψ (u j)) ^ n` in the field `K`.
  refine ⟨∑ b ∈ B, φ (d b) * ∏ k, a (b k), ?_⟩
  exact (mul_right_cancel₀ (pow_ne_zero n hne) (key.trans hψ)).symm

end Work.DSM5b
