import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_mapsTo
import Submission.Work.Horn.FatouQ.chartdict
import Submission.Work.Horn.FatouQ.gfun_differentiableAt
import Submission.Work.Horn.FatouQ.gfun_re_bounds
import Submission.Work.Horn.FatouQ.gfun_injOn
import Submission.Work.Horn.FatouQ.Xfun_differentiableAt
import Submission.Work.Horn.FatouQ.Xfun_holder
import Submission.Work.Horn.FatouQ.Xfun_deriv_close

/-!
# The chart facts for the `q`-th root chart of the Leau–Fatou flower

The chart `w = chartQ q a z = cc q a / z^q` (`cc = -1/(q a)`) maps the `j`-th petal
`Flower.petal q a M j` biholomorphically onto the half plane `{w | M < Re w}`; this file records
the elementary consequences of that dictionary (membership, the two-sided inverse, the induced
dynamics `gfun`, its growth and injectivity, and the differentiability/asymptotics of the
approximate coordinate `Xfun`).

The analytic content (differentiability, the Hölder bound and `deriv → 1`) is proved in the
companion files `gfun_differentiableAt`, `gfun_re_bounds`, `gfun_injOn`, `Xfun_differentiableAt`,
`Xfun_holder`, `Xfun_deriv_close`; here they are assembled into the single `chart_facts` bundle.
-/

namespace Work.Horn.FatouQ

open Work.Horn.Flower Work.Horn

noncomputable section

/-- For `M < Re w` the inverse chart `zBranch q a j w` lands in the `j`-th petal: indeed
`cc q a / w ∈ DM q a M` exactly when `M < Re w`, and the petal is the image of `DM` under
`rootFun q a j`. -/
theorem zBranch_mem_petal {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : PetalDatum f D q a ρ M) (j : Fin q) {w : ℂ} (hw : M < w.re) :
    zBranch q a j w ∈ petal q a M j := by
  have hcc : cc q a ≠ 0 := hd.hgeo.cc_ne_zero
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith [hd.hM]
  exact ⟨cc q a / w, (cc_div_mem_DM_iff hcc hw0).mpr hw, rfl⟩

/-- Each petal sits in the disc `ball 0 ρ` on which the quantitative bounds hold. -/
theorem petal_subset_ball {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : PetalDatum f D q a ρ M) (j : Fin q) {z : ℂ} (hz : z ∈ petal q a M j) :
    z ∈ Metric.ball (0 : ℂ) ρ := by
  have hlt : ‖z‖ < ρ := by
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd (lt_trans (hd.hgeo.petal_norm_pow_lt j z hz) hd.hRM)
      (not_lt.mpr (pow_le_pow_left₀ hd.hρ.le hcon q))
  simpa [Metric.mem_ball, dist_zero_right] using hlt

/-- The inverse chart of the `j`-th petal is never zero. -/
theorem zBranch_ne_zero {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : PetalDatum f D q a ρ M) (j : Fin q) {w : ℂ} (hw : M < w.re) :
    zBranch q a j w ≠ 0 :=
  fun h => hd.hgeo.not_mem_petal_zero j (h ▸ zBranch_mem_petal hd j hw)

/-- The chart dynamics inverts the chart: `zBranch q a j (gfun f q a j w) = f (zBranch q a j w)`
as soon as `M < Re w`.  Uses that `f` maps the petal into itself (up to `0`) and does not vanish
there. -/
theorem zBranch_gfun {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : PetalDatum f D q a ρ M) (j : Fin q) {w : ℂ} (hw : M < w.re) :
    zBranch q a j (gfun f q a j w) = f (zBranch q a j w) := by
  have hzpetal : zBranch q a j w ∈ petal q a M j := zBranch_mem_petal hd j hw
  have hz0 : zBranch q a j w ≠ 0 := zBranch_ne_zero hd j hw
  have hzball : zBranch q a j w ∈ Metric.ball (0 : ℂ) ρ := petal_subset_ball hd j hzpetal
  have hlogpow : ∀ u : ℂ, u ≠ 0 → |u.arg| * (q : ℝ) < Real.pi →
      Complex.log (u ^ q) = (q : ℂ) * Complex.log u :=
    fun u hu hu' => Work.Horn.log_pow_eq hd.hb.hq hu hu'
  have hmaps : f (zBranch q a j w) ∈ petal q a M j := by
    rcases Work.Horn.petal_mapsTo hd.hb hd.hM hd.hRM hd.hgeo hlogpow j hzpetal with h | h
    · exact h
    · exfalso
      have hfz : f (zBranch q a j w) ≠ 0 := by
        rw [hd.hb.hf_eq]
        exact mul_ne_zero hz0 (hd.hb.hunit_ne _ hzball)
      exact hfz h
  rw [gfun]
  exact Work.Horn.FatouQ.zBranch_chartQ hd.hgeo j hmaps


/-- **The chart facts.**  For a Leau–Fatou petal datum of order `q+1`, the `j`-th branch
`zBranch q a j` of the inverse chart maps the half plane `{M < Re w}` into the petal, inverts the
chart `chartQ q a`, the induced map `gfun` is holomorphic, moves `Re w` forward by at least
`1/2`, is injective, and the approximate coordinate `Xfun` is holomorphic, close to the identity
in the Hölder sense and has derivative within `1/4` of `1` far out. -/
theorem chart_facts {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q) :
    (∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j) ∧
    (∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w) ∧
    (∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ≠ 0) ∧
    (∀ w : ℂ, M < w.re →
      Work.Horn.FatouQ.zBranch q a j (Work.Horn.FatouQ.gfun f q a j w) =
        f (Work.Horn.FatouQ.zBranch q a j w)) ∧
    (∀ w : ℂ, M < w.re → DifferentiableAt ℂ (Work.Horn.FatouQ.gfun f q a j) w) ∧
    (∀ w : ℂ, M < w.re → M < (Work.Horn.FatouQ.gfun f q a j w).re) ∧
    (∀ w : ℂ, M < w.re → w.re + 1 / 2 ≤ (Work.Horn.FatouQ.gfun f q a j w).re) ∧
    Set.InjOn (Work.Horn.FatouQ.gfun f q a j) {w : ℂ | M < w.re} ∧
    (∀ w : ℂ, M < w.re → DifferentiableAt ℂ (Work.Horn.FatouQ.Xfun f q a j) w) ∧
    (∃ C0 C1 θ : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ θ < 1 ∧ ∀ w : ℂ, M < w.re →
      ‖Work.Horn.FatouQ.Xfun f q a j w - w‖ ≤ C0 * ‖w‖ ^ θ + C1) ∧
    (∃ N : ℝ, M ≤ N ∧ ∀ w : ℂ, N < w.re →
      ‖deriv (Work.Horn.FatouQ.Xfun f q a j) w - 1‖ ≤ 1 / 4) := by
  have hpetal : ∀ w : ℂ, M < w.re →
      Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j :=
    fun w hw => zBranch_mem_petal hd j hw
  have hchart : ∀ w : ℂ, M < w.re →
      Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w :=
    fun w hw => Work.Horn.FatouQ.chartQ_zBranch hd.hgeo hd.hM j hw
  have hinv : ∀ w : ℂ, M < w.re →
      Work.Horn.FatouQ.zBranch q a j (Work.Horn.FatouQ.gfun f q a j w) =
        f (Work.Horn.FatouQ.zBranch q a j w) :=
    fun w hw => zBranch_gfun hd j hw
  refine ⟨hpetal, hchart, ?_, hinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun w hw => zBranch_ne_zero hd j hw
  · exact gfun_differentiableAt hd j hpetal
  · exact (gfun_re_bounds hd j hpetal hchart).1
  · exact (gfun_re_bounds hd j hpetal hchart).2
  · exact gfun_injOn hd j hpetal hchart hinv
  · exact Xfun_differentiableAt hd j hpetal
  · exact Xfun_holder hd j hpetal hchart
  · exact Xfun_deriv_close hd j hpetal hchart

end

end Work.Horn.FatouQ
