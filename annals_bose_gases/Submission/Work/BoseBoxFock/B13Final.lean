import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.G2_eq
import Submission.Work.BoseBoxFock.ae_eval_compl
import Submission.Work.BoseBoxFock.ae_fibreIns_compl
import Submission.Work.BoseBoxFock.ae_upd2_res_compl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.B13Final` — the `L²` bound on the one-slot fibre, assembled

This module assembles the `L²` bound on the block I/III fibre of the Fournais--Solovej `Q₂` row
(the statement `Work.BoseBoxFock.block13_fibre_L2`).

* §9 reduces the a.e.-measurable state to a strongly measurable representative: the fibre integral
  `Gfun p Θ A B` is unchanged when `Θ` is modified on a null set (the relevant insertions
  `fibreIns`/`upd2` pull the null set back to a null set, a.e. in `w` and in `y` respectively);
* §10 applies the core estimate `block13_core` (which uses the two Cauchy--Schwarz steps and the
  two-slot fibre identities of `B13Main`).

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/-! ## 9. The a.e.-reduction to a strongly measurable state -/

/-- The fibre integral `w ↦ y ↦ ‖Gfun p · A B w y‖²` is unchanged when the state is modified on a
null set. -/
theorem Gfun_integral_eq_of_ae_eq (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ₀ : (Fin n → E3) → ℂ} (A B : E3 → ℂ) (heq : Θ =ᵐ[volume] Θ₀) :
    ∫ w : E3, ∫ y : E3, ‖Gfun p Θ A B w y‖ ^ 2
      = ∫ w : E3, ∫ y : E3, ‖Gfun p Θ₀ A B w y‖ ^ 2 := by
  set N := toMeasurable volume {x : Fin n → E3 | Θ x ≠ Θ₀ x} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact MeasureTheory.ae_iff.mp heq
  have hNsub : {x : Fin n → E3 | Θ x ≠ Θ₀ x} ⊆ N := by
    rw [hNdef]; exact subset_toMeasurable _ _
  have hz : ∀ x : Fin n → E3, x ∉ N → Θ x = Θ₀ x := fun x hx =>
    not_not.mp fun h => hx (hNsub h)
  have h1 := ae_fibreIns_compl p hNm hN0
  have h2 := ae_upd2_res_compl p hp hNm hN0
  have hmain : ∀ᵐ w : E3, ∀ᵐ y : E3, Gfun p Θ A B w y = Gfun p Θ₀ A B w y :=
    h1.mono fun w hw => h2.mono fun y hy => by
      have hwEq : (fun x' : Fib1 p => fibreIns p.2 w x' ∉ N)
          =ᵐ[volume] (fun _ : Fib1 p => True) :=
        hw.mono fun x' hx' => eq_true hx'
      have hlift := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Fib1 p)))
        (ν := (volume : Measure E3))).ae_eq_comp hwEq
      have hw' : ∀ᵐ q : Fib1 p × E3, fibreIns p.2 w q.1 ∉ N := by
        filter_upwards [hlift] with q hq
        exact of_eq_true (by simpa [Function.comp] using hq)
      have h4 : ∀ᵐ q : Fib1 p × E3 ∂(volume.prod volume),
          star (Θ (fibreIns p.2 w q.1)) * A ((fibreIns p.2 w q.1) p.1) * star (B q.2)
              * Θ (Function.update (Function.update (fibreIns p.2 w q.1) p.1 y) p.2 q.2)
            = star (Θ₀ (fibreIns p.2 w q.1)) * A ((fibreIns p.2 w q.1) p.1) * star (B q.2)
              * Θ₀ (Function.update (Function.update (fibreIns p.2 w q.1) p.1 y) p.2 q.2) := by
        filter_upwards [hw', hy] with q hq1 hq2
        rw [update_update_fibreIns (hp := hp)]
        rw [hz _ hq1, hz _ hq2]
      rw [Gfun, Gfun]
      refine integral_congr_ae ?_
      filter_upwards [Measure.ae_ae_of_ae_prod h4] with x' hx'
      exact integral_congr_ae hx'
  have hinner : ∀ᵐ w : E3, (∫ y : E3, ‖Gfun p Θ A B w y‖ ^ 2)
      = ∫ y : E3, ‖Gfun p Θ₀ A B w y‖ ^ 2 := by
    filter_upwards [hmain] with w hw
    refine integral_congr_ae ?_
    filter_upwards [hw] with y hy
    rw [hy]
  exact integral_congr_ae hinner

/-! ## 10. The final statement -/

theorem block13_fibre_L2_aux {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : (Fin n → E3) → ℂ} {A B : E3 → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : AEStronglyMeasurable A) (hAL : Integrable (fun x => ‖A x‖ ^ 2))
    (hBm : AEStronglyMeasurable B) (hBL : Integrable (fun x => ‖B x‖ ^ 2)) :
    ∫ w : E3, ∫ y : E3, ‖Gfun p Θ A B w y‖ ^ 2
      ≤ (∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖B x‖ ^ 2)
        * (∫ x : Fin n → E3, ‖Θ x‖ ^ 2) ^ 2 := by
  set Θ₀ : (Fin n → E3) → ℂ := hΘm.mk Θ with hΘ₀def
  have hΘ₀sm : StronglyMeasurable Θ₀ := hΘm.stronglyMeasurable_mk
  have hΘ₀meas : Measurable Θ₀ := hΘ₀sm.measurable
  have heq : Θ =ᵐ[volume] Θ₀ := hΘm.ae_eq_mk
  have hΘ₀L : Integrable (fun x => ‖Θ₀ x‖ ^ 2) :=
    hΘL.congr (heq.mono fun x hx => congrArg (fun z => ‖z‖ ^ 2) hx)
  -- the projection measurability of `A`
  have hAproj : AEMeasurable (fun x' : Fib1 p => A (x' ⟨p.1, hp⟩)) volume := by
    set M := toMeasurable volume {x : E3 | A x ≠ hAm.aemeasurable.mk A x} with hMdef
    have hMm : MeasurableSet M := measurableSet_toMeasurable _ _
    have hM0 : volume M = 0 := by
      rw [hMdef, measure_toMeasurable]
      exact MeasureTheory.ae_iff.mp hAm.aemeasurable.ae_eq_mk
    have hMsub : {x : E3 | A x ≠ hAm.aemeasurable.mk A x} ⊆ M := by
      rw [hMdef]; exact subset_toMeasurable _ _
    have hgood : ∀ᵐ x' : Fib1 p, x' ⟨p.1, hp⟩ ∉ M := ae_eval_compl p hp hMm hM0
    have hEqA : (fun x' : Fib1 p => A (x' ⟨p.1, hp⟩))
        =ᵐ[volume] (fun x' => hAm.aemeasurable.mk A (x' ⟨p.1, hp⟩)) := by
      filter_upwards [hgood] with x' hx'
      exact not_not.mp fun h => hx' (hMsub h)
    exact AEMeasurable.congr
      (((hAm.aemeasurable.measurable_mk).comp
        (measurable_pi_apply (⟨p.1, hp⟩ : I1 p))).aemeasurable) hEqA.symm
  -- finiteness of the `ℝ≥0∞` masses
  have hc : NB B ≠ ⊤ := by
    rw [NB, ← ofReal_integral_eq_lintegral_ofReal hBL
      (Filter.Eventually.of_forall fun x => by positivity)]
    exact ENNReal.ofReal_ne_top
  have hNA : NA A ≠ ⊤ := by
    rw [NA, ← ofReal_integral_eq_lintegral_ofReal hAL
      (Filter.Eventually.of_forall fun x => by positivity)]
    exact ENNReal.ofReal_ne_top
  have hNE : NE Θ₀ ≠ ⊤ := by
    rw [NE, ← ofReal_integral_eq_lintegral_ofReal hΘ₀L
      (Filter.Eventually.of_forall fun x => by positivity)]
    exact ENNReal.ofReal_ne_top
  have hG2 := G2_eq p hp (NB B) hΘ₀meas hAproj hc hNA hNE
  have hcore := block13_core p hp A B hΘ₀meas hΘ₀L hAL hBL hAproj hBm.aemeasurable hG2
  rw [← Gfun_integral_eq_of_ae_eq p hp A B heq] at hcore
  rwa [← integral_congr_ae (heq.mono fun x hx => congrArg (fun z => ‖z‖ ^ 2) hx)] at hcore

end Work.BoseBoxFock
