import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.exists_fibre_le_of_sum_le
import Submission.Work.BoseBoxFock.sectorSlotLift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sectorSelection` — the `V`-sector choice of the BF3c selection

BF3c (`box_to_model`) step 2: the first *selection* of the fibre argument.  A `V`-supported
one-body slot sum `A = boxSlotSum e T` is block diagonal for the `S`-sector decomposition
`Φ = Σ_S slotExact e S Φ` (`slotSum_sector_split`, proved) and the sectors are orthogonal
(`slotExact_orth_gen`, proved), so both the norm and the quadratic form split:

    ‖Φ‖² = Σ_S ‖Θ_S‖² ,    ⟪Φ, A Φ⟫_ℝ = Σ_S ⟪Θ_S, A Θ_S⟫_ℝ ,    Θ_S := slotExact e S Φ ,

and a finite average argument (`exists_le_of_sum_le`, the local copy of
`Work.BoseBoxFock.exists_fibre_le_of_sum_le`) produces a sector `S` with a *no worse* ratio.  The
extra input of the sector form of the selection is that a sector of *vanishing mass* contributes
nothing to the form, which holds because `Θ_S = 0` a.e. when its mass vanishes.

This is the "finite selection over the sectors" of `FINDING_BF3c_selection_s8.md` §1; the remaining
selections are the pointwise (`y`-wise) one (`exists_fibre_le_of_integral`) and the real/imaginary
one, both downstream of the real-projection rework (`RealProjDefs.lean`).

**Import note.**  The selection step uses the corpus's `Work.BoseBoxFock.exists_fibre_le_of_sum_le`
directly (the earlier local copy was needed only while its cone was blocked by a neighbour's
in-progress file; that file now builds).
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory
open Work.BoseDict

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **real mass** of a state, `ν Θ = re ∫ star Θ · Θ` (the real pairing of `Θ` with itself). -/
def massR {n : ℕ} (Θ : (Fin n → Ω) → ℂ) : ℝ := (∫ x, star (Θ x) * Θ x).re

/-- The pointwise identity `re (star z · z) = ‖z‖²`. -/
theorem star_mul_re_eq_normSq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The real mass is the integral of the squared norm, `ν Θ = ∫ ‖Θ‖²`.  (No integrability
hypothesis: `MassR` is defined through the Bochner integral of `star Θ · Θ`, and
`MeasureTheory.integral_ofReal` commutes that with the `re` of the `ℝ`-valued integral.) -/
theorem massR_eq_integral_normSq {n : ℕ} (Θ : (Fin n → Ω) → ℂ) :
    massR Θ = ∫ x, ‖Θ x‖ ^ 2 := by
  rw [massR]
  have hpt : (fun x : Fin n → Ω => star (Θ x) * Θ x)
      = fun x => ((‖Θ x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    apply Complex.ext
    · rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    · rw [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
      ring
  rw [hpt, show (∫ x : Fin n → Ω, ((‖Θ x‖ ^ 2 : ℝ) : ℂ))
      = ((∫ x, ‖Θ x‖ ^ 2 : ℝ) : ℂ) from integral_ofReal]
  simp

/-- The real mass is nonnegative. -/
theorem massR_nonneg {n : ℕ} (Θ : (Fin n → Ω) → ℂ) : 0 ≤ massR Θ := by
  rw [massR_eq_integral_normSq Θ]
  exact integral_nonneg fun x => by positivity

/-- A bounded, a.e. strongly measurable state with compact support is integrable (the version of
`Work.BoseBoxFock.integrable_mul_of_continuous_hasCompactSupport_of_bounded` with a constant in
place of the continuous factor). -/
theorem integrable_of_bounded_hasCompactSupport {n : ℕ} {f : (Fin n → Ω) → ℂ}
    (hfm : MeasureTheory.AEStronglyMeasurable f)
    (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (hfc : HasCompactSupport f) :
    MeasureTheory.Integrable f := by
  obtain ⟨C, hC⟩ := hfb
  refine MeasureTheory.Integrable.mono' (g := (tsupport f).indicator (fun _ => max C 0)) ?_ hfm ?_
  · rw [integrable_indicator_iff (isClosed_tsupport f).measurableSet]
    exact integrableOn_const (hfc.measure_lt_top.ne)
  · filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx]
      exact (hC x).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hx]
      exact norm_le_zero_iff.mpr (image_eq_zero_of_notMem_tsupport hx)

/-- The squared norm of a bounded, measurable state with compact support is integrable.  Proved by
`Integrable.mono'` against a `set`-abbreviated indicator, so that no `whnf` unification ever has to
unfold the lambda `fun x => ‖Θ x‖ ^ 2` (the phrasing that timed out in the first attempts).  Stated
for a *variable* state, so the call sites never see a large term either. -/
theorem integrable_normSq_of_bounded_compactSupport {n : ℕ} {Θ : (Fin n → Ω) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (hΘc : HasCompactSupport Θ) :
    MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hΘb
  have hCm : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  set g : (Fin n → Ω) → ℝ := (tsupport Θ).indicator (fun _ => max C 0 ^ 2) with hg
  refine MeasureTheory.Integrable.mono' (g := g) ?_ ?_ ?_
  · rw [hg, integrable_indicator_iff (isClosed_tsupport Θ).measurableSet]
    exact integrableOn_const (hΘc.measure_lt_top.ne)
  · exact (hΘm.norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ tsupport Θ
    · rw [hg, Set.indicator_of_mem hx]
      have h1 : (0 : ℝ) ≤ ‖Θ x‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hC x).trans (le_max_left _ _)) 2
    · rw [hg, Set.indicator_of_notMem hx]
      have h0 : Θ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [h0]
      simp

/-- A continuous compactly supported function times a bounded measurable state is integrable. -/
theorem integrable_mul_contCompact_of_bounded {n : ℕ} {g Θ : (Fin n → Ω) → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    MeasureTheory.Integrable (fun x => g x * Θ x) :=
  integrable_mul_of_continuous_hasCompactSupport_of_bounded hg hgc hΘm.aestronglyMeasurable hΘb

/-- **The `V`-sector choice (BF3c, first selection).**  If a `V`-supported one-body slot sum `T`
has a no-worse ratio at the state `Φ` than the constant `c`, then it has a no-worse ratio on some
*sector* `slotExact e S Φ` of positive mass. -/
theorem exists_sector_le_of_slotSum {m n : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : Ω => star (e l z) * e l' z))
    (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (c : ℝ) (hpos : 0 < massR Φ)
    (hc : (∫ x, star (Φ x) * boxSlotSum e T Φ x).re ≤ c * massR Φ) :
    ∃ S : Finset (Fin n), 0 < massR (slotExact e S Φ) ∧
      (∫ x, star (slotExact e S Φ x) * boxSlotSum e T (slotExact e S Φ) x).re
        ≤ c * massR (slotExact e S Φ) := by
  classical
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  have hsec : ∀ S : Finset (Fin n), Measurable (slotExact e S Φ) ∧
      (∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C) ∧ HasCompactSupport (slotExact e S Φ) :=
    fun S => slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  have hIntnorm : ∀ S : Finset (Fin n),
      MeasureTheory.Integrable (fun x => ‖slotExact e S Φ x‖ ^ 2) :=
    fun S => integrable_normSq_of_bounded_compactSupport (hsec S).1 (hsec S).2.1 (hsec S).2.2
  have hintΦ : ∀ S : Finset (Fin n),
      MeasureTheory.Integrable (fun x => star (Φ x) * slotExact e S Φ x) :=
    fun S => integrable_mul_contCompact_of_bounded
      (continuous_star.comp hΦ) (hΦc.comp_left (by simp)) (hsec S).1 (hsec S).2.1
  -- ## the sector pairs
  have horthC : ∀ S : Finset (Fin n),
      (∫ x, star (Φ x) * slotExact e S Φ x)
        = (∫ x, star (slotExact e S Φ x) * slotExact e S Φ x) := by
    intro S
    have h := slotExact_orth_gen e he hec horth S S Φ hΦ hΦc Φ hΦ.measurable hΦb
    rw [if_pos rfl] at h
    exact h.symm
  -- ## 1. the norm splits over the sectors
  have h2 : massR Φ = ∑ S : Finset (Fin n), massR (slotExact e S Φ) := by
    rw [massR]
    have hpt : (fun x : Fin n → Ω => star (Φ x) * Φ x)
        = fun x => ∑ S : Finset (Fin n), star (Φ x) * slotExact e S Φ x := by
      funext x
      have hx : (∑ S : Finset (Fin n), slotExact e S Φ x) = Φ x := by
        simpa only [Finset.sum_apply] using congrFun (slotExact_sum_eq e Φ) x
      rw [← Finset.mul_sum, hx]
    rw [hpt, MeasureTheory.integral_finsetSum _ (fun S _ => hintΦ S),
      Finset.sum_congr rfl (fun S _ => horthC S)]
    simp [massR]
  -- ## 2. the form splits over the sectors
  have h1 : (∫ x, star (Φ x) * boxSlotSum e T Φ x).re
      = ∑ S : Finset (Fin n),
          (∫ x, star (slotExact e S Φ x) * boxSlotSum e T (slotExact e S Φ) x).re := by
    rw [slotSum_sector_split e he hec horth hint T Φ hΦ hΦc]
    simp
  -- ## 3. a sector of vanishing mass contributes nothing to the form
  have hq : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      massR (slotExact e S Φ) = 0 →
        (∫ x, star (slotExact e S Φ x) * boxSlotSum e T (slotExact e S Φ) x).re = 0 := by
    intro S _ h0
    have hν0 : ∫ x, ‖slotExact e S Φ x‖ ^ 2 = 0 := by
      rw [← massR_eq_integral_normSq (slotExact e S Φ), h0]
    have hsupp : volume (Function.support (fun x => ‖slotExact e S Φ x‖ ^ 2)) = 0 := by
      have hpos' : ¬ (0 < ∫ x, ‖slotExact e S Φ x‖ ^ 2) := by rw [hν0]; exact lt_irrefl 0
      have hiff := MeasureTheory.integral_pos_iff_support_of_nonneg_ae
        (f := fun x => ‖slotExact e S Φ x‖ ^ 2)
        (Filter.Eventually.of_forall fun x => by positivity) (hIntnorm S)
      exact le_antisymm (not_lt.mp fun hlt => hpos' (hiff.mpr hlt)) bot_le
    have hsupp2 : volume (Function.support (fun x => slotExact e S Φ x)) = 0 := by
      have hset : Function.support (fun x => slotExact e S Φ x)
          = Function.support (fun x => ‖slotExact e S Φ x‖ ^ 2) := by
        ext x
        simp only [Function.mem_support, ne_eq, sq_eq_zero_iff, norm_eq_zero]
      rw [hset]
      exact hsupp
    have hset0 : {x : Fin n → Ω | ¬ (slotExact e S Φ x = (0 : (Fin n → Ω) → ℂ) x)}
        = Function.support (fun x => slotExact e S Φ x) := by
      ext x
      simp only [Set.mem_setOf_eq, Pi.zero_apply, Function.mem_support, ne_eq]
    have hΘ0 : slotExact e S Φ =ᵐ[volume] 0 := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff, hset0]
      exact hsupp2
    have hzero : (fun x => star (slotExact e S Φ x) * boxSlotSum e T (slotExact e S Φ) x)
        =ᵐ[volume] 0 := by
      filter_upwards [hΘ0] with x hx
      rw [show slotExact e S Φ x = 0 from hx, star_zero, zero_mul]
      simp [Pi.zero_apply]
    rw [MeasureTheory.integral_congr_ae hzero]
    simp
  -- ## 4. the selection
  have hνnn : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      0 ≤ massR (slotExact e S Φ) := fun S _ => massR_nonneg (slotExact e S Φ)
  obtain ⟨S, -, hSpos, hSle⟩ := exists_fibre_le_of_sum_le
    (Finset.univ : Finset (Finset (Fin n)))
    (fun S => (∫ x, star (slotExact e S Φ x) * boxSlotSum e T (slotExact e S Φ) x).re)
    (fun S => massR (slotExact e S Φ)) (c := c) hνnn hq
    (by show 0 < ∑ S : Finset (Fin n), massR (slotExact e S Φ); rw [← h2]; exact hpos)
    (by show (∑ S : Finset (Fin n),
            (∫ x, star (slotExact e S Φ x) * boxSlotSum e T (slotExact e S Φ) x).re)
          ≤ c * ∑ S : Finset (Fin n), massR (slotExact e S Φ)
        rw [← h1, ← h2]
        exact hc)
  exact ⟨S, hSpos, hSle⟩

end Work.BoseBoxFock
