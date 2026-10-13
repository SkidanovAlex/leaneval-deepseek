import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `D_z`-shift estimate for the squared `ℋ^k`-norm

For `k ≥ 1`, `α ∈ ℝ` and `f` of class `C^∞` on the open quadrant and in `ℋ^k`,

`|D_z f|²_{ℋ^{k-1}} ≤ (k + k²) · |f|²_{ℋ^k}`.

The point of the estimate is that shifting by `D_z` *removes* slots from the `ℋ^k`-integrand:
`D_z^{i}(D_z f) = D_z^{i+1} f` and `D_z^j D_θ^i D_z f = D_z^{j+1} D_θ^i f` (`i ≥ 1`), so every
slot of `HkIntegrand α (k-1) (D_z f)` may be compared with a slot of `HkIntegrand α k f`.  The
factor `k + k²` is the crude slot count: `k` for the radial half (each single radial slot is
dominated by the whole integrand, `Work.Spaces.sq_le_HkIntegrand_z`) and `k·k` for the mixed
half (`Work.Spaces.sq_le_HkIntegrand_mixed`).

The mathematical content is the *pointwise* bound on the open quadrant
`Q0 = (0,∞) × (0,π/2)` (`HkIntegrand_shift_le_smooth` below); the only smoothness it needs is
`C^∞` in the sense of `Work.Stability.smoothOrder` — the operators' commutation
`D_z (D_θ^i g) = D_θ^i (D_z g)` is `Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen`.  (The
sibling `Step.HkIntegrand_shift_le` of `EllEstUnifStepAux` is stated for `ContDiffOn ℝ ⊤`,
which in this Mathlib is *analyticity*, so it cannot be applied to the `C^∞` data of the
theorem.)  What remains here is the passage to the integrals, which is done *slicing in `θ`
first*: for each fixed `z > 0` the `θ`-interval bound is `MeasureTheory.integral_mono_of_nonneg`
(nonnegativity, integrability of the majorant — supplied by `HkMem α k f` — and an a.e.
pointwise bound whose exceptional set is the null set `{0, π/2}`), and the resulting `z`-bound is
integrated with the same lemma.  The advantage of this route is that neither `HkSq α (k-1) (D_z f)`
nor any of its slices has to be shown to be (a.e. strongly measurable and) integrable.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## The pointwise bound on the open quadrant -/

/-- The shifted mixed slots, at the genuine smooth order: for `f` of class `C^∞` on the open
quadrant and `(z,θ)` in the open quadrant,

`D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`.

This is `D_z` commutation with `D_θ^i` (`DthIterDzCommOpen`) followed by the algebraic identity
`D_z^j (D_z g) = D_z^{j+1} g` (`Step.DzIter_Dz`), together with the local congruence of iterated
`D_z` on the open quadrant. -/
private lemma mixed_shift_apply_smooth {j i : ℕ} (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Step.DzIter_congr_of_isOpen Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The shifted integrand is dominated by the level-`k` integrand.**  Every slot of
`HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the commutation of `D_z`
with `D_θ^i`), and each single slot is dominated by the whole integrand; counting `k` radial
and `k·k` mixed slots gives the factor `k + k²`. -/
private theorem HkIntegrand_shift_le_smooth (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2 := by
      unfold Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_shift_apply_smooth f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Step.Zsum k f z θ + Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-! ## The target: integration of the pointwise bound -/

/-- **The `D_z`-shift estimate.**  For `k ≥ 1`, if `f` is `C^∞` on the open quadrant
`(0,∞) × (0,π/2)` and lies in `ℋ^k`, then

`|D_z f|²_{ℋ^{k-1}} ≤ (k + k²) · |f|²_{ℋ^k}`. -/
theorem HkSq_Dz_shift_le {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hcd : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
      ≤ (((k : ℝ) + (k : ℝ) * (k : ℝ))) * Work.Spaces.HkSq α k f := by
  have hg : Work.FTS.EllipticEst.SmoothOpen f :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mpr hcd
  -- the open angular interval agrees with the closed one up to a null set
  have hIoo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  -- *step 1*: the angular slice bound, for every `z > 0`
  have hinner : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
        ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]
      exact Set.mem_Ici.mpr (le_of_lt hz)
    have hInt : MeasureTheory.Integrable
        (fun θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.Integrable.const_mul (hmem.1 z hzIz) _
    have hpt : (fun θ => Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ) := by
      rw [MeasureTheory.Measure.restrict_congr_set hIoo]
      exact MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioo.measurableSet
        (fun θ hθ => HkIntegrand_shift_le_smooth α hk f hz hθ hg)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ :=
          MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) z θ) hInt hpt
      _ = ((k : ℝ) + (k : ℝ) * (k : ℝ))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
          MeasureTheory.integral_const_mul _ _
  -- *step 2*: integrability in `z` of the majorant, from the hypothesis `HkMem α k f`
  have hmemIoi : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hmem.2
  have hGint : MeasureTheory.Integrable
      (fun z => ((k : ℝ) + (k : ℝ) * (k : ℝ))
        * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) := hmemIoi.const_mul _
  have hle : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
      ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z => ((k : ℝ) + (k : ℝ) * (k : ℝ))
        * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact hinner z hz
  have hmain : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ)
      ≤ ∫ z in Set.Ioi (0 : ℝ), ((k : ℝ) + (k : ℝ) * (k : ℝ))
        * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) z θ) hGint hle
  calc Work.Spaces.HkSq α (k - 1) (Work.Spaces.Dz f)
      = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
        simp only [Work.Spaces.HkSq, Work.Spaces.Iz,
          MeasureTheory.integral_Ici_eq_integral_Ioi]
    _ ≤ ∫ z in Set.Ioi (0 : ℝ), ((k : ℝ) + (k : ℝ) * (k : ℝ))
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := hmain
    _ = ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkSq α k f := by
        rw [MeasureTheory.integral_const_mul]
        simp only [Work.Spaces.HkSq, Work.Spaces.Iz,
          MeasureTheory.integral_Ici_eq_integral_Ioi]

end Work.FTS.EllipticEst.remov
