import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.atomPairG
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PotCubicLowBandAux

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

private lemma cons_comp_swap {d : ℕ} (y : Work.BoseDict.Xn d) (z w : Ω) :
    ((Fin.cons z (Fin.cons w y) : Work.BoseDict.Xn (d + 2)) ∘ Equiv.swap (0 : Fin (d + 2)) 1)
      = Fin.cons w (Fin.cons z y) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp
  · simp
  · have h0 : (Fin.succ (Fin.succ k) : Fin (d + 2)) ≠ 0 := Fin.succ_ne_zero _
    have h1 : (Fin.succ (Fin.succ k) : Fin (d + 2)) ≠ 1 := by
      intro hh
      exact Fin.succ_ne_zero k (Fin.succ_inj.mp hh)
    simp [Equiv.swap_apply_def, h0, h1]

theorem annCommSelf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (u v : Fin m → ℝ) {Θ : Work.BoseDict.Xn (d + 2) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x) :
    Work.BoseDict.boxAnnOf e u d (Work.BoseDict.boxAnnOf e v (d + 1) Θ)
      = Work.BoseDict.boxAnnOf e v d (Work.BoseDict.boxAnnOf e u (d + 1) Θ) := by
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hCΘ0 : 0 ≤ CΘ := le_trans (norm_nonneg _) (hCΘ 0)
  have hUnorm : Integrable (fun z : Ω => ‖Work.BoseDict.etaOf e u z‖) :=
    (Work.BoseBoxFock.integrable_etaOf_weakG hmeas hbdd hsupp u).2
  have hVnorm : Integrable (fun z : Ω => ‖Work.BoseDict.etaOf e v z‖) :=
    (Work.BoseBoxFock.integrable_etaOf_weakG hmeas hbdd hsupp v).2
  funext y
  -- the pointwise symmetry of the two `cons` insertions
  have hcons : ∀ z w : Ω,
      Θ (Fin.cons z (Fin.cons w y)) = Θ (Fin.cons w (Fin.cons z y)) := by
    intro z w
    have h := hΘsym (Equiv.swap (0 : Fin (d + 2)) 1) (Fin.cons z (Fin.cons w y))
    rw [cons_comp_swap y z w] at h
    exact h.symm
  -- joint integrability of the common integrand
  have hGint : Integrable (fun p : Ω × Ω =>
      star (Work.BoseDict.etaOf e u p.1) *
        (star (Work.BoseDict.etaOf e v p.2) * Θ (Fin.cons p.2 (Fin.cons p.1 y))))
      (volume.prod volume) := by
    refine (hUnorm.mul_prod (hVnorm.const_mul (max CΘ 0))).mono' ?_ ?_
    · have hA : Measurable (fun p : Ω × Ω => star (Work.BoseDict.etaOf e u p.1)) :=
        Complex.continuous_conj.measurable.comp
          ((Work.MB.etaOf_weak_measurable hmeas u).comp measurable_fst)
      have hB : Measurable (fun p : Ω × Ω => star (Work.BoseDict.etaOf e v p.2)) :=
        Complex.continuous_conj.measurable.comp
          ((Work.MB.etaOf_weak_measurable hmeas v).comp measurable_snd)
      have hC : Measurable (fun p : Ω × Ω =>
          Θ (Fin.cons p.2 (Fin.cons p.1 y))) :=
        hΘm.comp (((Work.BoseBoxFock.continuous_cons_prod (d := d + 1)).comp
          (continuous_snd.prodMk
            ((Work.BoseBoxFock.continuous_cons_fixed (d := d) y).comp continuous_fst))).measurable)
      exact (hA.mul (hB.mul hC)).aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul, norm_mul, norm_star, norm_star]
      have h1 : ‖Θ (Fin.cons p.2 (Fin.cons p.1 y))‖ ≤ max CΘ 0 :=
        (hCΘ _).trans (le_max_left _ _)
      calc ‖Work.BoseDict.etaOf e u p.1‖ *
              (‖Work.BoseDict.etaOf e v p.2‖ * ‖Θ (Fin.cons p.2 (Fin.cons p.1 y))‖)
          ≤ ‖Work.BoseDict.etaOf e u p.1‖ *
              (‖Work.BoseDict.etaOf e v p.2‖ * max CΘ 0) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (norm_nonneg _)
        _ = ‖Work.BoseDict.etaOf e u p.1‖ * (max CΘ 0 * ‖Work.BoseDict.etaOf e v p.2‖) := by
            ring
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun z w : Ω => star (Work.BoseDict.etaOf e u z) *
      (star (Work.BoseDict.etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))) hGint
  have hL : (∫ z : Ω, star (Work.BoseDict.etaOf e u z) *
        ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * ∫ w : Ω,
          star (Work.BoseDict.etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))))
      = (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * ∫ z : Ω, ∫ w : Ω,
          star (Work.BoseDict.etaOf e u z) *
            (star (Work.BoseDict.etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
    rw [show (∫ z : Ω, star (Work.BoseDict.etaOf e u z) *
          ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * ∫ w : Ω,
            star (Work.BoseDict.etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))))
        = ∫ z : Ω, (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * (star (Work.BoseDict.etaOf e u z) *
            ∫ w : Ω, star (Work.BoseDict.etaOf e v w) * Θ (Fin.cons w (Fin.cons z y)))
        from integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))]
    rw [integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only []
    rw [← integral_const_mul]
  have hR : (∫ w : Ω, star (Work.BoseDict.etaOf e v w) *
        ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * ∫ z : Ω,
          star (Work.BoseDict.etaOf e u z) * Θ (Fin.cons z (Fin.cons w y))))
      = (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * ∫ w : Ω, ∫ z : Ω,
          star (Work.BoseDict.etaOf e u z) *
            (star (Work.BoseDict.etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))) := by
    rw [show (∫ w : Ω, star (Work.BoseDict.etaOf e v w) *
          ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * ∫ z : Ω,
            star (Work.BoseDict.etaOf e u z) * Θ (Fin.cons z (Fin.cons w y))))
        = ∫ w : Ω, (Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * (star (Work.BoseDict.etaOf e v w) *
            ∫ z : Ω, star (Work.BoseDict.etaOf e u z) * Θ (Fin.cons z (Fin.cons w y)))
        from integral_congr_ae (Filter.Eventually.of_forall (fun w => by ring))]
    rw [integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    simp only []
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only []
    rw [hcons z w]
    ring
  simp only [Work.BoseDict.boxAnnOf]
  change (Real.sqrt ((d : ℝ) + 1) : ℂ) * (∫ z : Ω, star (Work.BoseDict.etaOf e u z) *
        ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * ∫ w : Ω,
          star (Work.BoseDict.etaOf e v w) * Θ (Fin.cons w (Fin.cons z y))))
    = (Real.sqrt ((d : ℝ) + 1) : ℂ) * (∫ w : Ω, star (Work.BoseDict.etaOf e v w) *
        ((Real.sqrt (((d + 1 : ℕ) : ℝ) + 1) : ℂ) * ∫ z : Ω,
          star (Work.BoseDict.etaOf e u z) * Θ (Fin.cons z (Fin.cons w y))))
  rw [hL, hR, hswap]

end

end Work.BoseBoxFock.PotCubicLowBandAux
