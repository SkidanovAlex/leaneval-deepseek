import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixGlue.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Pot.potInput_holds`

The `pot` clause of `Work.BoseFixGlue.CompareInputs` (FS `lem:LocPotential`, in the
pointwise-in-`x`, whole-space form in which `compare_box_energy_v2` consumes it),
discharged from the *ambient* hypotheses on the interaction `v`:

  `v ∈ L¹`, `tsupport v ⊆ ball 0 R`, `0 < a v`

there is `ε₀ > 0` such that for every admissible `μ` (`Adm v ε₀ μ`),

  `∫_u potWordU N v (g₀ v h) (ℓB v μ) μ u x = −μ N ∫ g₀ + Σ_{i<j} v (xᵢ − xⱼ)`.

The only mathematical content beyond the corpus' `lem:LocPotential`
(`Submission.BoseGases.locPotential_box`, packaged `u`-integrated as
`Work.BoseKinLoc.Pot.pot_average`) is the *dilute regime* `R ≤ ℓ(μ)·chiR0`, which the
admissibility threshold has to supply: the box side `ℓ(μ) = sideAt μ (a v)` blows up as
`μ → 0⁺` (`Work.BoseBox.sideAt_large`), so `ε₀` can be taken small enough.

The two joint-integrability hypotheses `hint`, `hint2` of `Work.BoseKinLoc.Pot.pot_average`
are unused in its proof (the corpus' `locPotential_box` proves all the `u`-integrability it
needs internally), so the identity is re-derived here without them
(`pot_average_noint`), which is what makes the clause available at the ambient hypotheses
alone (`MeasureTheory.MemLp v 1` is not even needed).
-/

namespace Work.BoseFixGlue.Pot

open MeasureTheory Filter Metric
open scoped Topology BigOperators

set_option linter.unusedVariables false

/-! ## 1. FS `lem:LocPotential` without the (unused) joint-integrability hypotheses -/

/-- **FS `lem:LocPotential`**, `u`-averaged form, with the redundant joint-`(u,x)`
integrability hypotheses of `Work.BoseKinLoc.Pot.pot_average` removed (they are not used in
its proof: all integrability of the `u`-integrands is produced inside
`Submission.BoseGases.locPotential_box`). -/
theorem pot_average_noint {N : ℕ} {v g : ℝ³ → ℝ} {ℓ R r₀ μ : ℝ} (hℓ : 0 < ℓ)
    (hg : MeasureTheory.Integrable g) (hv : ∀ x : ℝ³, R ≤ ‖x‖ → v x = 0)
    (hgs : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0) (hR : 0 ≤ R) (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x)
    (x : Submission.BoseGases.X N) :
    (∫ u : ℝ³, Work.BoseKinLoc.potWordU N v g ℓ μ u x)
      = -μ * (N : ℝ) * (∫ y : ℝ³, g y)
        + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2) := by
  -- FS `lem:LocPotential`, assembled pointwise in `x` by the corpus.
  have hbox := Submission.BoseGases.locPotential_box (N := N) (μ := μ)
    hℓ hv hR hg hgs hr₀ hRℓ hC x
  -- the one-body integrals `∫_y g(xᵢ−y)` do not depend on `xᵢ`
  have htrans : (∑ i : Fin N, ∫ y : ℝ³, g (x i - y)) = (N : ℝ) * (∫ y : ℝ³, g y) := by
    rw [Submission.BoseGases.onebody_integral_translate_sum]
    simp [Finset.sum_const, nsmul_eq_mul]
  -- unfold `potWordU` so that `hbox` rewrites the integral
  show (∫ u : ℝ³, (-μ * (∑ i : Fin N, ∫ y : ℝ³,
          Submission.BoseGases.wLoc ℓ g u (x i) y)
        + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
            Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2)))
      = -μ * (N : ℝ) * (∫ y : ℝ³, g y)
        + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)
  rw [← hbox, htrans]
  ring

/-! ## 2. The `pot` clause at the ambient hypotheses -/

theorem potInput_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ Work.BoseFixGlue.PotInput v h ε₀ := by
  -- `ℓ(μ) = sideAt μ (a v)` blows up as `μ → 0⁺`, so `R ≤ ℓ(μ)·chiR0` eventually.
  have hev := Work.BoseBox.sideAt_large (a := BoseGases.a v) hav R Submission.BoseGases.chiR0
    Submission.BoseGases.chiR0_pos
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  -- the threshold: `μa³ ≤ ε₀` forces `μ ≤ δ/2 < δ`
  have ha3 : 0 < (BoseGases.a v) ^ 3 := pow_pos hav 3
  refine ⟨min 1 (δ * (BoseGases.a v) ^ 3 / 2), lt_min one_pos (by positivity), ?_⟩
  intro μ hAdm N L hL Φ hΦ hsym hsupp x
  have hμpos : 0 < μ := hAdm.1
  have htδ : μ * (BoseGases.a v) ^ 3 ≤ δ * (BoseGases.a v) ^ 3 / 2 :=
    le_trans hAdm.2.1 (min_le_right _ _)
  have hμδ : μ < δ := by nlinarith [ha3, hδpos]
  have hℓpos : 0 < ℓB v μ := Work.BoseBox.sideAt_pos hμpos hav
  have hRℓ : R ≤ ℓB v μ * Submission.BoseGases.chiR0 := by
    have h := hδ (y := μ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hμpos]; exact hμδ) hμpos
    simpa [ℓB] using h
  -- the pointwise support forms of `v` and of the kernel `g₀`
  have hv_zero : ∀ y : ℝ³, R ≤ ‖y‖ → v y = 0 := by
    intro y hy
    by_contra hne
    have hyb : y ∈ Metric.ball (0 : ℝ³) R := hv_supp (subset_tsupport v hne)
    rw [Metric.mem_ball, dist_zero_right] at hyb
    exact absurd hyb (not_lt.mpr hy)
  have hg0_zero : ∀ y : ℝ³, R ≤ ‖y‖ → Submission.BoseGases.g0 v h y = 0 :=
    fun y hy => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hy h
  exact pot_average_noint (N := N) (v := v) (g := Submission.BoseGases.g0 v h)
    (ℓ := ℓB v μ) (R := R) (r₀ := Submission.BoseGases.chiR0) (μ := μ)
    hℓpos (Submission.BoseGases.g0_integrable hR hv_supp h) hv_zero hg0_zero hR.le
    Submission.BoseGases.chiR0_pos hRℓ Submission.BoseGases.chiR0_half x

end Work.BoseFixGlue.Pot
