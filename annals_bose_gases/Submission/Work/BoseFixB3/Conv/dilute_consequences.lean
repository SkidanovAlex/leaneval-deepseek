import ChallengeDeps
import Submission.Work.BoseFixB3.Conv.ellAt_mul_kapAt_zpow_neg40
import Submission.Work.BoseFixB3.Conv.ellAt_sq_mul_d_pow_le
import Submission.Work.BoseFixB3.Eps.Arith
import Submission.Work.BoseFixGlue.Pot.ellB_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.dilute_consequences`

The **dilute-regime consequences** of FS §7 that the `B3` chapter consumes: at
FS's parameters there is `ε₀ > 0` such that for every admissible chemical
potential `μ` (`Adm v ε₀ μ`: `0 < μ`, diluteness `μ (a v)³ ≤ ε₀`, FS
`sec:params`) all six parameter inequalities hold at once:

1. `fsXp (μa³) 1 = X ≤ 1` — the diluteness monomial is small,
2. `R ≤ ℓ(μ)·χ_{R₀}`, `ℓ(μ) = ellAt μ (a v)` — the box is large compared with
   the support radius `R` of `v` (FS's localisation condition), with
   `χ_{R₀} = Submission.BoseGases.chiR0`,
3. `ℓ² d^{80} ≤ a²` — the cut-off bookkeeping (`d = (μa³)^{6/323}`),
4. `(ℓκ)^{-40} = d^{80}` — the exact high-momentum decay factor of
   `chi_highpass_decay` (`κ = kapAt μ (a v) = (d²ℓ)⁻¹`, so `κℓ = d^{-2}`),
5. `ℓ > 0`,
6. `κ > 0`.

Everything is arithmetic in the single small parameter `t = μa³` except (2),
which is the large-box statement `Work.BoseBox.sideAt_large` (`ℓ(μ) → ∞` as
`μ → 0⁺`) packaged in `Work.BoseFixGlue.Pot.ellB_ge`; the threshold `ε₀` is the
minimum of that one with `1`, so that the whole conjunction holds on a single
admissibility window.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Conv

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false

theorem dilute_consequences (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      Work.BoseBox.fsXp (μ * (BoseGases.a v) ^ 3) 1 ≤ 1 ∧
      R ≤ Work.BoseFixB3.ellAt μ (BoseGases.a v) * Submission.BoseGases.chiR0 ∧
      (Work.BoseFixB3.ellAt μ (BoseGases.a v)) ^ 2
          * ((Work.BoseFixB3.patAt μ (BoseGases.a v)).d) ^ 80 ≤ (BoseGases.a v) ^ 2 ∧
      (Work.BoseFixB3.ellAt μ (BoseGases.a v) * Work.BoseFixB3.kapAt μ (BoseGases.a v))
          ^ (-(40 : ℤ)) = ((Work.BoseFixB3.patAt μ (BoseGases.a v)).d) ^ 80 ∧
      0 < Work.BoseFixB3.ellAt μ (BoseGases.a v) ∧
      0 < Work.BoseFixB3.kapAt μ (BoseGases.a v) := by
  -- (2) is the only non-arithmetic clause: the large-box condition, uniform in
  -- small diluteness (`ℓ(μ) = sideAt μ (a v) → ∞` as `μ → 0⁺`).
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Work.BoseFixGlue.Pot.ellB_ge (v := v) hav hR
  -- one single admissibility window: `ε₀ := min 1 ε₁`.
  refine ⟨min 1 ε₁, lt_min one_pos hε₁pos, ?_⟩
  intro μ hAdm
  obtain ⟨hμpos, hdil, _hparams⟩ := hAdm
  have ha3 : 0 < (BoseGases.a v) ^ 3 := pow_pos hav 3
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := mul_pos hμpos ha3
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := le_trans hdil (min_le_left _ _)
  have hε1le : μ * (BoseGases.a v) ^ 3 ≤ ε₁ := le_trans hdil (min_le_right _ _)
  obtain ⟨_hℓBpos, hRℓB⟩ := hε₁ μ hμpos hε1le
  have hℓpos : 0 < Work.BoseFixB3.ellAt μ (BoseGases.a v) :=
    Work.BoseFixB3.Eps.ellAt_pos μ (BoseGases.a v) hμpos hav
  have hκpos : 0 < Work.BoseFixB3.kapAt μ (BoseGases.a v) :=
    Work.BoseFixB3.Eps.kapAt_pos ht hℓpos
  refine ⟨?_, ?_, ?_, ?_, hℓpos, hκpos⟩
  · -- (1) `X = (μa³)^{1/323} ≤ 1` for `0 < μa³ ≤ 1`
    exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  · -- (2) `R ≤ ℓ(μ)·χ_{R₀}`; `ellB v μ` is `ellAt μ (a v)` by definition
    simpa [Work.BoseFixB3.ellAt, Work.BoseFixGlue.ℓB] using hRℓB
  · -- (3) `ℓ² d^{80} = a²·(μa³)^{154/323} ≤ a²`
    exact Work.BoseFixB3.Conv.ellAt_sq_mul_d_pow_le μ (BoseGases.a v) hμpos hav ht1
  · -- (4) `(ℓκ)^{-40} = ((d²)^{-1})^{-40} = d^{80}`
    exact Work.BoseFixB3.Conv.ellAt_mul_kapAt_zpow_neg40 μ (BoseGases.a v) hμpos hav

end Work.BoseFixB3.Conv
