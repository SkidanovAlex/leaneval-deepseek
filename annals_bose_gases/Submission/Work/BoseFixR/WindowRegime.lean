import ChallengeDeps
import Submission.Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.WindowRegime` — the dilute window of the box parameters

At FS's parameters every quantity of the box chapter is a monomial in the
diluteness `t = μ·(a v)³`:

* the box side `ℓ = sideAt μ (a v) = (a v)·t^{-163/323}`,
* `d = t^{6/323}`, `s = t^{1/323}`,

so the four conditions requested here are pure monomial comparisons that hold on
*all* sufficiently dilute `μ`, with an explicit threshold.  Concretely, with

    `ε₀ = min ε₁ (min (157^{-323/166}) 1)`

where `ε₁` is the threshold of `exists_adm_chiR0_ge` (the large-box condition
`R ≤ ℓ·χ_{R₀}`), every admissible `μ` (so `0 < μ` and `t = μ(a v)³ ≤ ε₀`):

1. `R ≤ ℓ·χ_{R₀}` — from `exists_adm_chiR0_ge`;
2. `μ ℓ³ = t^{-166/323} ≥ 157` — the exponent `-166/323` is negative and
   `t ≤ 157^{-323/166}`, whose own `-166/323`-power is `157`;
3. `(a v) ≤ d·s·ℓ = (a v)·t^{-156/323}` — since `t ≤ 1` and `-156 ≤ 0`;
4. `d = t^{6/323} ≤ 1` — since `t ≤ 1` and `6 ≥ 0`.

The `ε₀ = 1`-clause of the minimum is what supplies `t ≤ 1`, i.e. both
`d ≤ 1` and `d·s·ℓ ≥ (a v)`.

Nothing here uses the scattering-solution hypotheses (`h`, `hv`, `hv1`,
`hvrad`, `hv_supp`): the statement is arithmetic about the box parameters.
-/

noncomputable section

open scoped Real Topology BigOperators

set_option linter.unusedVariables false

namespace Work.BoseFixR

/-- `d = X⁶ = t^{6/323}` at FS's parameters (definitional). -/
lemma d_eq_fsXp_at (μ a : ℝ) :
    (Work.BoseBox.paramsAt μ a).d = Work.BoseBox.fsXp (μ * a ^ 3) 6 := rfl

/-- `s = X = t^{1/323}` at FS's parameters (definitional). -/
lemma s_eq_fsXp_at (μ a : ℝ) :
    (Work.BoseBox.paramsAt μ a).s = Work.BoseBox.fsXp (μ * a ^ 3) 1 := rfl

/-- **The diluteness threshold for `μ ℓ³ ≥ 157`.**  For `0 < μ` and
`t = μ(a v)³ ≤ 157^{-323/166}` one has `μ · sideAt μ (a v)³ ≥ 157`, because
`μ ℓ³ = t^{-166/323}` and the exponent is negative. -/
lemma one_fifty_seven_le_mu_ell_cube {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ (157 : ℝ) ^ (-(323 / 166 : ℝ))) :
    (157 : ℝ) ≤ μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have h157 : (0 : ℝ) < 157 := by norm_num
  have hpow : (157 : ℝ)
      ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-166) := by
    rw [Work.BoseBox.fsXp]
    have h := Real.rpow_le_rpow_of_nonpos ht0 ht
      (show (-(166 / 323 : ℝ)) ≤ 0 by norm_num)
    have hε : ((157 : ℝ) ^ (-(323 / 166 : ℝ))) ^ (-(166 / 323 : ℝ)) = 157 := by
      rw [← Real.rpow_mul h157.le]
      norm_num
    rw [hε] at h
    have he : (-166 : ℝ) / 323 = -(166 / 323 : ℝ) := by norm_num
    rw [he]
    exact h
  rw [Work.BoseFixB1.mu_ell_cube_eq hav hμ]
  exact hpow

/-- **The diluteness threshold for `d·s·ℓ ≥ (a v)`**, given `t ≤ 1`:
`d·s·ℓ = (a v)·t^{-156/323} ≥ (a v)·1`. -/
lemma a_le_d_mul_s_mul_sideAt {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1) :
    _root_.BoseGases.a v
      ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
  have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hge : (1 : ℝ)
      ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-156) :=
    Work.BoseFixB1.one_le_fsXp_of ht0 ht1 (by norm_num)
  have hprod : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6
        * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1
        * (_root_.BoseGases.a v * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163))
      = _root_.BoseGases.a v
        * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-156) := by
    rw [show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6
          * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1
          * (_root_.BoseGases.a v * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163))
        = _root_.BoseGases.a v
          * (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6
            * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1
            * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163)) by ring]
    rw [Work.BoseBox.fsXp_mul ht0, Work.BoseBox.fsXp_mul ht0]
    congr 1
    norm_num
  rw [d_eq_fsXp_at, s_eq_fsXp_at, Work.BoseFixB1.sideAt_eq_fsXp hav hμ, hprod]
  exact le_mul_of_one_le_right hav.le hge

/-- `d ≤ 1` for `t ≤ 1`: `d = t^{6/323}` with a non-negative exponent. -/
lemma d_le_one {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht1 : μ * a ^ 3 ≤ 1) :
    (Work.BoseBox.paramsAt μ a).d ≤ 1 := by
  have ht0 : (0 : ℝ) < μ * a ^ 3 := by positivity
  rw [d_eq_fsXp_at]
  exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)

theorem WindowRegime {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 ∧
      (157 : ℝ) ≤ μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 ∧
      _root_.BoseGases.a v
        ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ∧
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  have h157 : (0 : ℝ) < 157 := by norm_num
  have hε₂pos : (0 : ℝ) < (157 : ℝ) ^ (-(323 / 166 : ℝ)) := Real.rpow_pos_of_pos h157 _
  refine ⟨min ε₁ (min ((157 : ℝ) ^ (-(323 / 166 : ℝ))) 1),
    lt_min hε₁pos (lt_min hε₂pos one_pos), ?_⟩
  intro μ hAdm
  obtain ⟨hμ, hdil, hOK⟩ := hAdm
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hdil (le_trans (min_le_right _ _) (min_le_right _ _))
  have htε₁ : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₁ := le_trans hdil (min_le_left _ _)
  have htε₂ : μ * (_root_.BoseGases.a v) ^ 3 ≤ (157 : ℝ) ^ (-(323 / 166 : ℝ)) :=
    le_trans hdil (le_trans (min_le_right _ _) (min_le_left _ _))
  refine ⟨hε₁ μ ⟨hμ, htε₁, hOK⟩,
    one_fifty_seven_le_mu_ell_cube hav hμ htε₂,
    a_le_d_mul_s_mul_sideAt hav hμ ht1,
    d_le_one hμ hav ht1⟩

end Work.BoseFixR
