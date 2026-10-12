import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseBoxFock.PCFU.fderiv_dirichletSlice_eq_zero_of_notMem_acube
import Submission.Work.BoseBoxFock.PCFU.integrable_dirichletSlice
import Submission.Work.BoseBoxFock.PCFU.lowSlot_boxRestrictR_factor
import Submission.Work.BoseBoxFock.PCFU.peel_abox_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped ContDiff Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `kcInsN n i (y, r)` is `r` with `y` inserted in slot `i`; consequently updating slot `i` by a
new value `z` inserts `z`.  (The `Function.update` bookkeeping of the slot-`i` slice.) -/
theorem update_kcInsN (n : ℕ) (i : Fin (n + 1)) (y z : E3) (r : Submission.BoseGases.X n) :
    Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z
      = Submission.BoseGases.kcInsN n i (z, r) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Submission.BoseGases.kc_insN_apply_same]
  · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    rw [Function.update_of_ne (Fin.succAbove_ne i j'),
      Submission.BoseGases.kc_insN_apply_succ, Submission.BoseGases.kc_insN_apply_succ]

theorem dirichletPeel {n : ℕ} (i : Fin (n + 1)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ z * Φ (Function.update x i z)) (x i)
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2))
      = ∫ r : Submission.BoseGases.X n,
          (∫ y : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)) := by
  -- The two measures of the peeled product space.
  set μ : MeasureTheory.Measure E3 :=
    (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
      (Submission.BoseGases.acube ℓ) with hμ
  set ν : MeasureTheory.Measure (Submission.BoseGases.X n) :=
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ) with hν
  -- The peeled integrand: the `z`-derivative of the slot-`i` slice, evaluated at `z = p.1`.
  set G : E3 × Submission.BoseGases.X n → ℝ := fun p => ∑ k : Fin 3,
      ‖fderiv ℝ (fun z : E3 => Submission.BoseGases.chiScale ℓ z *
        Φ (Submission.BoseGases.kcInsN n i (z, p.2))) p.1
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 with hG
  -- Integrability of the joint integrand (continuity on the compact product box).
  have hGint : MeasureTheory.Integrable G (μ.prod ν) := by
    rw [hG, hμ, hν]
    exact integrable_dirichletSlice i hℓ hΦ
  -- The peel of the slot-`i` fibre out of the `(n+1)`-particle box.
  have hpeel := peel_abox_integral (n := n) (s := ℓ) hℓ i
    (fun x : Submission.BoseGases.X (n + 1) => ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
      Submission.BoseGases.chiScale ℓ z * Φ (Function.update x i z)) (x i)
      (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
  -- `Function.update (kcInsN n i (y,r)) i z = kcInsN n i (z,r)`, hence the peeled integrand is `G`.
  have hpt : ∀ p : E3 × Submission.BoseGases.X n,
      (fun x : Submission.BoseGases.X (n + 1) => ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
        Submission.BoseGases.chiScale ℓ z * Φ (Function.update x i z)) (x i)
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) (Submission.BoseGases.kcInsN n i p) = G p := by
    rintro ⟨y, r⟩
    rw [hG]
    have h1 : (Submission.BoseGases.kcInsN n i (y, r)) i = y :=
      Submission.BoseGases.kc_insN_apply_same n i y r
    have h2 : ∀ z : E3, Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z
        = Submission.BoseGases.kcInsN n i (z, r) :=
      fun z => update_kcInsN n i y z r
    simp only [h1, h2]
  -- Left-hand side: the box integral is the product integral of `G`.
  have hLHS : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
          Submission.BoseGases.chiScale ℓ z * Φ (Function.update x i z)) (x i)
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2))
      = ∫ p, G p ∂(μ.prod ν) := by
    rw [hμ, hν, hpeel]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- Fubini.
  have hFub : (∫ p, G p ∂(μ.prod ν))
      = ∫ r : Submission.BoseGases.X n, (∫ y : E3, G (y, r) ∂μ) ∂ν :=
    integral_prod_symm G hGint
  -- The `y`-slice vanishes off the cube, so the restricted and unrestricted `y`-integrals agree.
  have hinner : ∀ r : Submission.BoseGases.X n,
      (∫ y : E3, G (y, r) ∂μ) = ∫ y : E3, G (y, r) := by
    intro r
    have hv : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ → G (y, r) = 0 := by
      intro y hy
      simp only [hG]
      rw [fderiv_dirichletSlice_eq_zero_of_notMem_acube (n := n) i hℓ hy r]
      simp
    rw [hμ]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hv
  have hmid : (∫ r : Submission.BoseGases.X n, (∫ y : E3, G (y, r) ∂μ) ∂ν)
      = ∫ r : Submission.BoseGases.X n, (∫ y : E3, G (y, r)) ∂ν := by
    apply integral_congr_ae
    filter_upwards with r
    exact hinner r
  -- Right-hand side: unfold `G` under the two integrals.
  have hRHS : (∫ r : Submission.BoseGases.X n,
          (∫ y : E3, ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
              Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ∂ν)
      = ∫ r : Submission.BoseGases.X n, (∫ y : E3, G (y, r)) ∂ν := by
    apply integral_congr_ae
    filter_upwards with r
    apply integral_congr_ae
    filter_upwards with y
    rw [hG]
  exact hLHS.trans (hFub.trans (hmid.trans hRHS.symm))

end Work.BoseBoxFock.PCFU
