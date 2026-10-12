import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.regime_sideAt_ge`

The dilute-regime large-box condition: for every fixed support radius `R > 0`
there is a diluteness threshold `ε₀ > 0` such that for all `μ > 0` with
`μ·(a v)³ ≤ ε₀` the box side `ℓ(μ) = sideAt μ (a v)` at FS's parameters is
large enough that **both**

* `R ≤ ℓ(μ)·d(μ)/16` — the small-box side `dℓ/16` (the diameter of the small
  boxes of App. `SmallBoxes`) is at least the support radius `R`, and
* `R ≤ ℓ(μ)·chiR0` — the support-radius condition of the `C`-node,

where `d(μ) = (paramsAt μ (a v)).d = (μa³)^{6/323}` and
`chiR0 > 0` is the radius of the witness ball on which `χ⋆χ ≥ 1/2`.

Both sides are closed monomials in `t = μ a³`:

    ℓ(μ)·d(μ) = a·(μa³)^{−157/323},      ℓ(μ) = a·(μa³)^{−163/323},

and the exponents are negative, so each factor blows up as `μa³ → 0⁺`.  The
second conjunct is the bare-parameter growth statement `Work.BoseBox.sideAt_large`
at `r₀ := chiR0`; the first is the same computation for the product `ℓ·d`,
recorded below as `eventually_sideAt_mul_d_ge`.
-/

namespace Work.BoseFixB1

open Filter Metric
open scoped Topology Real

/-- **The product `ℓ·d` blows up as `μ → 0⁺`.**  For every fixed radius `R > 0`
and scattering length `a > 0`, for all `μ > 0` sufficiently small the product of
the box side and the small-box parameter `d` satisfies `R ≤ ℓ(μ)·d(μ)/16`.

Indeed `ℓ(μ)·d(μ) = a·(μa³)^{−157/323}` (`d_mul_sideAt_eq`), so with
`t = μa³` the claim is `t^{−157/323} ≥ 16R/a`, which holds for `t ≤ (16R/a)^{−323/157}`. -/
lemma eventually_sideAt_mul_d_ge {a : ℝ} (ha : 0 < a) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ μ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      R ≤ Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d / 16 := by
  -- the target lower bound `C = 16R/a` on `t^{−157/323}`, and the threshold `t ≤ C^{−323/157}`
  set C : ℝ := 16 * R / a with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have ha3 : 0 < a ^ 3 := by positivity
  set δ : ℝ := C ^ (-(323 / 157 : ℝ)) / a ^ 3 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (show -(δ) < (0 : ℝ) by linarith) hδpos]
    with μ hμmem hμpos
  have hμlt : μ < δ := hμmem.2
  have ht0 : 0 < μ * a ^ 3 := mul_pos hμpos ha3
  -- `μ < δ` gives `t = μa³ ≤ C^{−323/157}`
  have htle : μ * a ^ 3 ≤ C ^ (-(323 / 157 : ℝ)) := by
    have h : μ * a ^ 3 < δ * a ^ 3 := mul_lt_mul_of_pos_right hμlt ha3
    rw [hδdef, div_mul_cancel₀ _ (ne_of_gt ha3)] at h
    exact le_of_lt h
  -- `t^{−157/323} ≥ C`
  have hCpow : (C ^ (-(323 / 157 : ℝ))) ^ (-(157 / 323 : ℝ)) = C := by
    rw [← Real.rpow_mul hCpos.le]
    norm_num
  have hkey : C ≤ (μ * a ^ 3) ^ (-(157 / 323 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos ht0 htle (show (-(157 / 323 : ℝ)) ≤ 0 by norm_num)
    rwa [hCpow] at h
  -- `ℓ·d = a·t^{−157/323}`
  have hprod : Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d
      = a * (μ * a ^ 3) ^ (-(157 / 323 : ℝ)) := by
    have h := Work.BoseFixB1.d_mul_sideAt_eq (A := a) (μ := μ) ha hμpos
    rw [Work.BoseBox.fsXp] at h
    rw [mul_comm (Work.BoseBox.sideAt μ a) (Work.BoseBox.paramsAt μ a).d, h]
    norm_num
  rw [hprod]
  -- `R ≤ a·t^{−157/323}/16`
  have h1 : 16 * R ≤ a * (μ * a ^ 3) ^ (-(157 / 323 : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hkey ha.le
    rwa [show a * C = 16 * R by rw [hCdef]; field_simp] at h
  linarith

theorem regime_sideAt_ge {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) {R : ℝ} (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 ∧
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 := by
  -- (1) `ℓ·d/16` eventually dominates `R`; (2) `ℓ·chiR0` eventually dominates `R`
  have h1 := eventually_sideAt_mul_d_ge (a := _root_.BoseGases.a v) hav hR
  have h2 := Work.BoseBox.sideAt_large (a := _root_.BoseGases.a v) hav R
    Submission.BoseGases.chiR0 Submission.BoseGases.chiR0_pos
  have h := h1.and h2
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδpos, hδ⟩ := h
  have ha3 : 0 < (_root_.BoseGases.a v) ^ 3 := by positivity
  refine ⟨min 1 (δ * (_root_.BoseGases.a v) ^ 3 / 2), lt_min one_pos (by positivity), ?_⟩
  intro μ hμpos ht
  have htδ : μ * (_root_.BoseGases.a v) ^ 3 ≤ δ * (_root_.BoseGases.a v) ^ 3 / 2 :=
    le_trans ht (min_le_right _ _)
  have hμδ : μ < δ := by nlinarith [ha3, hδpos]
  exact hδ (y := μ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hμpos]; exact hμδ) hμpos

end Work.BoseFixB1
