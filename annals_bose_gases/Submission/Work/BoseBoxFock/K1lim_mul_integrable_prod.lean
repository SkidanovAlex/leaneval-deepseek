import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.K1lim_mul_integrable
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_slot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_mul_integrable_prod` — integrability of the limit pair kernel with the
`n`-particle variable integrated out first

The target integrates the limit pair kernel `K1lim ℓ W z.1 z.2` against a bounded, box-supported
function `H` of the *joint* variable `(x, z) ∈ Λ(ℓ)^n × (Λ(ℓ) × Λ(ℓ))`, with the `n`-particle
variable `x` integrated out **first**:

    `z ↦ ∫ x, K1lim ℓ W z.1 z.2 * H (x, z)`   is integrable on `Λ(ℓ) × Λ(ℓ)`.

## Route

Since `K1lim ℓ W z.1 z.2` does not depend on `x`, the inner integral is the *marginal*

    `G z = ∫ x, H (x, z)`,

and the target function is `z ↦ K1lim ℓ W z.1 z.2 · G z.1 z.2` (the constant factor is pulled out
of the Bochner integral by `integral_const_mul`, unconditionally).  So it suffices to show that `G`
is a.e. strongly measurable, bounded, and supported in `Λ(ℓ) × Λ(ℓ)`, and then apply the proved
kernel result `K1lim_mul_integrable`.

* **Boundedness of `G`.**  `H` is bounded by some `C` and vanishes outside
  `Λ(ℓ)^n × (Λ(ℓ) × Λ(ℓ))`, so `‖H (x,z)‖ₑ ≤ ofReal C · 1_{Λ(ℓ)^n}(x)`; integrating over `x` and
  using `volume (Λ(ℓ)^n) < ∞` (`Work.MB.volume_boxPow_lt_top`) bounds `‖G z‖` by a constant
  (`enorm_integral_le_lintegral_enorm` + `lintegral_indicator_one` + `ENNReal.toReal_mono`).
* **Support of `G`.**  If `z ∉ Λ(ℓ) × Λ(ℓ)` then `H (x,z) = 0` for every `x`, hence `G z = 0`.
* **A.e. strong measurability of `G`.**  This is the Fubini–measurability statement
  `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`: the marginal of an a.e. strongly
  measurable function of two variables is a.e. strongly measurable.  The swap
  `(z,x) ↦ (x,z)` is measure-preserving (`AEStronglyMeasurable.prod_swap`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

theorem K1lim_mul_integrable_prod {n : ℕ} {l : ℝ} (hl : 0 < l)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    {H : Work.BoseDict.Xn n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hHm : MeasureTheory.AEStronglyMeasurable H MeasureTheory.volume)
    (hHb : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C)
    (hHs : Function.support H ⊆ Set.prod (Work.MB.boxPow n l)
      (Set.prod (Work.BoseK15.corpusBox.boxL l) (Work.BoseK15.corpusBox.boxL l))) :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ∫ x : Work.BoseDict.Xn n, Work.BoseBoxFock.K1lim l W z.1 z.2 * H (x, z))
      (MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨C0, hC0⟩ := hHb
  have hHle : ∀ z, ‖H z‖ ≤ max C0 0 := fun z => (hC0 z).trans (le_max_left _ _)
  -- the marginal in the `n`-particle variable
  set G : E3 → E3 → ℂ := fun w y => ∫ x : Work.BoseDict.Xn n, H (x, (w, y)) with hGdef
  -- ## a.e. strong measurability of the marginal (Fubini)
  have hGm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G) MeasureTheory.volume := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun q : (E3 × E3) × Work.BoseDict.Xn n => H (q.2, q.1))
        (MeasureTheory.volume : Measure ((E3 × E3) × Work.BoseDict.Xn n)) := hHm.prod_swap
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun z : E3 × E3 => ∫ x : Work.BoseDict.Xn n, H (x, z))
        (MeasureTheory.volume : Measure (E3 × E3)) := h1.integral_prod_right'
    have hfun : (fun z : E3 × E3 => ∫ x : Work.BoseDict.Xn n, H (x, z))
        = Function.uncurry G := by
      funext p
      show (∫ x : Work.BoseDict.Xn n, H (x, p)) = G p.1 p.2
      rw [hGdef]
    rwa [hfun] at h2
  -- ## boundedness of the marginal
  have hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C := by
    refine ⟨(ENNReal.ofReal (max C0 0) * volume (Work.MB.boxPow n l)).toReal, fun w y => ?_⟩
    have hB : ENNReal.ofReal (max C0 0) * volume (Work.MB.boxPow n l) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Work.MB.volume_boxPow_lt_top n l)
    -- `H` is dominated by a constant times the indicator of the `n`-particle box
    have hHnorm : ∀ (x : Work.BoseDict.Xn n) (z : E3 × E3),
        ‖H (x, z)‖ₑ ≤ ENNReal.ofReal (max C0 0)
          * (Work.MB.boxPow n l).indicator (1 : Work.BoseDict.Xn n → ENNReal) x := by
      intro x z
      by_cases hx : x ∈ Work.MB.boxPow n l
      · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hHle (x, z))
      · have hz0 : H (x, z) = 0 := by
          by_contra hne
          exact hx (Set.mem_prod.mp (hHs (Function.mem_support.mpr hne))).1
        simp [hz0, hx]
    have hle : ‖G w y‖ₑ ≤ ENNReal.ofReal (max C0 0) * volume (Work.MB.boxPow n l) := by
      rw [hGdef]
      show ‖∫ x : Work.BoseDict.Xn n, H (x, (w, y))‖ₑ ≤ _
      calc ‖∫ x : Work.BoseDict.Xn n, H (x, (w, y))‖ₑ
          ≤ ∫⁻ x : Work.BoseDict.Xn n, ‖H (x, (w, y))‖ₑ :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ x : Work.BoseDict.Xn n, ENNReal.ofReal (max C0 0)
              * (Work.MB.boxPow n l).indicator (1 : Work.BoseDict.Xn n → ENNReal) x :=
            lintegral_mono (fun x => hHnorm x (w, y))
        _ = ENNReal.ofReal (max C0 0) * ∫⁻ x : Work.BoseDict.Xn n,
              (Work.MB.boxPow n l).indicator (1 : Work.BoseDict.Xn n → ENNReal) x :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (max C0 0) * volume (Work.MB.boxPow n l) := by
            rw [lintegral_indicator_one (Work.MB.measurableSet_boxPow n l)]
    calc ‖G w y‖ = (‖G w y‖ₑ).toReal := by simp
      _ ≤ _ := ENNReal.toReal_mono hB hle
  -- ## support of the marginal
  have hGs : Function.support (Function.uncurry G) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL l) (Work.BoseK15.corpusBox.boxL l) := by
    intro p hp
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · by_contra h1
      have hp0 : G p.1 p.2 = 0 := by
        have hH0 : ∀ x : Work.BoseDict.Xn n, H (x, p) = 0 := by
          intro x
          by_contra hne
          exact h1 (Set.mem_prod.mp (Set.mem_prod.mp (hHs (Function.mem_support.mpr hne))).2).1
        rw [hGdef]
        show ∫ x : Work.BoseDict.Xn n, H (x, (p.1, p.2)) = 0
        have : (fun x : Work.BoseDict.Xn n => H (x, (p.1, p.2))) = fun _ => (0 : ℂ) := by
          funext x
          simpa using hH0 x
        rw [this, integral_zero]
      have hp' := hp
      rw [Function.mem_support] at hp'
      exact hp' hp0
    · by_contra h2
      have hp0 : G p.1 p.2 = 0 := by
        have hH0 : ∀ x : Work.BoseDict.Xn n, H (x, p) = 0 := by
          intro x
          by_contra hne
          exact h2 (Set.mem_prod.mp (Set.mem_prod.mp (hHs (Function.mem_support.mpr hne))).2).2
        rw [hGdef]
        show ∫ x : Work.BoseDict.Xn n, H (x, (p.1, p.2)) = 0
        have : (fun x : Work.BoseDict.Xn n => H (x, (p.1, p.2))) = fun _ => (0 : ℂ) := by
          funext x
          simpa using hH0 x
        rw [this, integral_zero]
      have hp' := hp
      rw [Function.mem_support] at hp'
      exact hp' hp0
  -- ## conclude: pull the constant out of the inner integral and apply the kernel theorem
  refine (Work.BoseBoxFock.K1lim_mul_integrable hl hWi hGm hGb hGs).congr ?_
  filter_upwards with z
  show Work.BoseBoxFock.K1lim l W z.1 z.2 * G z.1 z.2
      = ∫ x : Work.BoseDict.Xn n, Work.BoseBoxFock.K1lim l W z.1 z.2 * H (x, z)
  rw [hGdef]
  show Work.BoseBoxFock.K1lim l W z.1 z.2 * ∫ x : Work.BoseDict.Xn n, H (x, (z.1, z.2))
      = ∫ x : Work.BoseDict.Xn n, Work.BoseBoxFock.K1lim l W z.1 z.2 * H (x, z)
  rw [integral_const_mul]

end Work.BoseBoxFock
