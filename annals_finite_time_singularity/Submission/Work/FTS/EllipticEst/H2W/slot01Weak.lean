/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/slot01Weak` — the `(1,0)`-slot of `∂_θθΨ` in the weak class

Target (statement as requested, unchanged):

```
∃ C > 0, ∀ α F Ψ, 0 < α → α ≤ 1/4 → TT.EllWeakPos α 2 F Ψ →
  L2Sq (D_θ(∂_θθΨ) · Wt α) ≤ C · (Σ_{j≤2} L2Sq(∂_θθ²(D_z^jΨ) · w/s^{η/2}) + HkSq α 2 F)
```

This is the `(1,0)`-slot of `∂_θθΨ` at level `2`: by the weight identity
`(D_θ f · Wt)² = (∂_θf)²·w²·sin(2θ)^{2-γ}` the left-hand side is the radial integral
`∫_z w(z)²·I(z)` of the one-dimensional Step-4 quantity `I(z) = ∫_θ (∂_θ³Ψ(z,θ))²sin(2θ)^{2-γ}`
of the slice `Ψ(z,·)`, and the right-hand side is the sum of the pure (`D_z`-only) slots
`∫_z w²·∫_θ (∂_θ²(D_z^jΨ))² sEta` (`j ≤ 2`) together with the `ℋ²`-energy of the source.

## The two analytic inputs, and why they are provided by the sibling files in this directory

The estimate is the sum of two inputs (see `TT/NOTES_slot01.md`):

* `Work.H2W.slot01SliceBound` — the **slice Step 4**: for every `z > 0`,
  `I(z) ≤ K₀(∫_θ (∂_θF)²σ₂ + ∫_θ (∂_θ²Ψ)²sEta + Zt(z) + Dt(z))`, obtained from the
  one-dimensional Step 4 `Work.H2W.sliceStep4Uniform` applied to `u = Ψ(z,·)` together with
  `weakSliceDerivBound` and the endpoint limits of the slices;
* `Work.H2W.slot01ZTBound` — the **Agmon bound**: a.e. in `z`, `Zt(z) ≤ C₁(Ps_1+Ps_2)` and
  `Dt(z) ≤ C₁·Ps_1` (the weak first-order angular estimate `weakFirstIter` applied to the slices
  of `z²∂_z²Ψ` and `D_zΨ`).

Both are proved in the sibling modules of this directory (`Slot01W/SliceBound.lean`,
`Slot01W/ZTBound.lean`), which are **copies of `H2W/slot01SliceBound.lean` and
`H2W/slot01ZTBound.lean` with the same declaration names but with their imports repointed at
currently-buildable modules** (the originals depend on modules that do not build in the current
state of the tree).  The remainder of the proof below is the bookkeeping of
`TT/slot01_le.lean` (weight identities, the pointwise domination `w²·Fs ≤ HkIntegrand α 2 F`,
the identification `w²·Ps_j = Q_j`, the a.e.-to-integral passage and the final arithmetic),
copied here so that the requested statement `Work.FTS.EllipticEst.H2W.slot01Weak` is available
in full; every ingredient is `sorry`-free.

## The bookkeeping, in one paragraph

`LHS = ∫_z w²·I`; a.e. in `z`, `w²·I ≤ M := K₀·HkSq-integrand + K₀(1+3C₁)(Q_0+Q_1+Q_2)`;
`∫_z M = K₀·HkSq α 2 F + K₀(1+3C₁)(L_0+L_1+L_2)` with `L_j = ∫_z Q_j`; hence
`LHS ≤ K₀ HkSq α 2 F + K₀(1+3C₁)Σ_{j≤2}L_j ≤ (K₀(1+3C₁)+1)(Σ_{j≤2}L_j + HkSq α 2 F)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice_step4
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.H2W.sliceStep4Uniform
import Submission.Work.H2W.zeroMeanPoincare
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceBound
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.ZTBound
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false


/-! ## Elementary `rpow` algebra on the angular weights -/

/-- `s ^ 2 * s ^ (-c) = s ^ (2 - c)` for `s ≥ 0` and `c < 2`. -/
theorem slot01_rpow_two_mul_neg {s : ℝ} (hs : 0 ≤ s) {c : ℝ} (hc : c < 2) :
    s ^ 2 * s ^ (-c) = s ^ (2 - c) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    have h2 : (0 : ℝ) < 2 - c := by linarith
    by_cases hc0 : c = 0
    · subst hc0; norm_num
    · rw [Real.zero_rpow (neg_ne_zero.mpr hc0), Real.zero_rpow (ne_of_gt h2), mul_zero]
  · rw [← Real.rpow_natCast s 2, ← Real.rpow_add h]; ring_nf

/-- `(s ^ (-c / 2)) ^ 2 = s ^ (-c)` for `s ≥ 0` and `c > 0`. -/
theorem slot01_sq_rpow_neg_half {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (s ^ (-(c / 2))) ^ 2 = s ^ (-c) := by
  rw [← Real.rpow_natCast (s ^ (-(c / 2))) 2, ← Real.rpow_mul hs]
  ring_nf

/-! ## The `(1,0)` mixed slot: weight identities -/

/-- `D_θ f = sin(2θ)·∂_θ f`. -/
theorem slot01_mixed_zero_one_eq (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed 0 1 f = fun z θ => Real.sin (2 * θ) * Work.Spaces.pth f z θ := by
  funext z θ
  rfl

/-- The squared weight identity for the `(1,0)` slot:
`(D_θ f · Wt α)² = (∂_θ f)² w² sin(2θ)^{2-γ}` on the angular interval. -/
theorem slot01_wt_sq_identity (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) (z : ℝ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_nonneg hθ
  have hγ : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : Work.Spaces.gam α < 2 := by
    rw [Work.Spaces.gam]; linarith
  rw [slot01_mixed_zero_one_eq]
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  have h1 : (Real.sin (2 * θ) * Work.Spaces.pth f z θ
        * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by ring
  rw [h1, slot01_sq_rpow_neg_half hs (Work.Spaces.gam α),
    ← slot01_rpow_two_mul_neg hs hγ2]
  ring

/-- The `(1,0)` slot of any function, as an iterated integral with the angular weight
`σ_γ = sin(2θ)^{2-γ}`. -/
theorem slot01_L2Sq_mixed01_eq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  rw [Work.Spaces.L2Sq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [show (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) from
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => slot01_wt_sq_identity α hα hα4 f z hθ)]
  rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        from setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- The left-hand side, rewritten as an iterated integral with the angular weight `σ_γ`. -/
theorem slot01_LHS_eq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  rw [slot01_L2Sq_mixed01_eq α hα hα4 (Work.Spaces.pthIter 2 Ψ)]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine congrArg (fun t => (Work.Spaces.w z) ^ 2 * t) ?_
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  simp only [Work.Spaces.pthIter_succ]

/-- A pure slot of `HkSq α 2` rewritten as an iterated integral with the weight `sEta`. -/
theorem slot01_pureSlot_eq (η : ℝ) (Ψ : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (η / 2)))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-η)) := by
  rw [Work.Spaces.L2Sq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (η / 2))) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-η) from
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)]
  · rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-η))
          from setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
  · have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_nonneg hθ
    rw [div_eq_mul_inv, ← Real.rpow_neg hs (η / 2)]
    rw [show (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(η / 2)))) ^ 2
        = (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) ^ (-(η / 2))) ^ 2 from by ring]
    rw [slot01_sq_rpow_neg_half hs η]

/-- The weight algebra for a slot: `(A · (w / s^{η/2}))² = A² · s^{-η} · w²`. -/
theorem slot01_slot_sq_eq {η A wv s : ℝ} (hs : 0 ≤ s) :
    (A * (wv / s ^ (η / 2))) ^ 2 = A ^ 2 * s ^ (-η) * wv ^ 2 := by
  rw [div_eq_mul_inv, ← Real.rpow_neg hs (η / 2)]
  rw [show (A * (wv * s ^ (-(η / 2)))) ^ 2 = A ^ 2 * wv ^ 2 * (s ^ (-(η / 2))) ^ 2 from by ring]
  rw [slot01_sq_rpow_neg_half hs η]
  ring

/-! ## The target -/

theorem slot01Weak : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ C * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨K0, hK0pos, hK0⟩ := Work.H2W.slot01SliceBound
  obtain ⟨C1, hC1pos, hC1⟩ := Work.H2W.slot01ZTBound
  have hC1nn : 0 ≤ C1 := hC1pos.le
  have hK0nn : 0 ≤ K0 := hK0pos.le
  refine ⟨K0 * (1 + 3 * C1) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hsmΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ### the pieces of the estimate, as functions of the radius `z`
  set JintF : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 2 F z θ with hJintF
  set Q : ℕ → ℝ → ℝ := fun j z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hQ
  set Ps : ℕ → ℝ → ℝ := fun j z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ with hPs
  set I : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hI
  set Fs : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hFs
  set Zt : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hZt
  set Dt : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hDt
  -- ### elementary nonnegativity
  have hJnn : ∀ z, 0 ≤ JintF z := fun z => by
    rw [hJintF]; beta_reduce
    exact MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 2 F z θ
  have hQnn : ∀ j z, 0 ≤ Q j z := fun j z => by
    rw [hQ]; beta_reduce
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  -- ### the weight identity `w² · Ps j = Q j`
  have hQeq : ∀ j z, (Work.Spaces.w z) ^ 2 * Ps j z = Q j z := by
    intro j z
    rw [hPs, hQ, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall ?_))
    intro θ hθ
    beta_reduce
    have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_nonneg hθ
    rw [slot01_slot_sq_eq (η := Work.Spaces.eta) hs, Work.FTS.EllipticEst.sEta]
    ring
  -- ### the source slot of `F` is dominated by the `ℋ²`-integrand of `F`
  have hFsQ : ∀ z ∈ Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Fs z ≤ JintF z := by
    intro z hz
    rw [hFs, hJintF, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (h.memF.1 z hz) ?_
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun θ hθ => ?_)
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _))
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun θ hθ => ?_)
      beta_reduce
      have h1 := slot01_wt_sq_identity α hα hα4 F z hθ
      rw [show (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          = (Work.Spaces.pth F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) from by ring]
      rw [← h1]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 F z θ 1 0 le_rfl (by norm_num)
  -- ### the a.e.-in-`z` domination `w² · I ≤ K0 · JintF + K0(1+3C1)(Q 0 + Q 1 + Q 2)`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.w z) ^ 2 * I z
        ≤ K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici,
      Filter.Eventually.of_forall (hK0 α F Ψ hα hα4 h), hC1 α F Ψ hα hα4 h]
      with z hz h1 h2
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- at `z = 0` the weight `w` vanishes, and the right-hand side is nonnegative
      subst hz0
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      have hMJ : 0 ≤ K0 * JintF 0 := mul_nonneg hK0nn (hJnn 0)
      have hK1 : 0 ≤ K0 * (1 + 3 * C1) := mul_nonneg hK0nn (by linarith)
      have hsum0 : 0 ≤ Q 0 0 + Q 1 0 + Q 2 0 := by
        have := hQnn 0 0; have := hQnn 1 0; have := hQnn 2 0; linarith
      have hMQ : 0 ≤ K0 * (1 + 3 * C1) * (Q 0 0 + Q 1 0 + Q 2 0) := mul_nonneg hK1 hsum0
      rw [hw0]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      linarith [hMJ, hMQ]
    · -- the honest case `z > 0`
      have h1z : I z ≤ K0 * (Fs z + Ps 0 z + Zt z + Dt z) := by
        simp only [hI, hFs, hPs, hZt, hDt]
        exact h1 hzpos
      have h2z := h2 hzpos
      have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hZ := h2z.1
      have hD := h2z.2
      have hZ' : (Work.Spaces.w z) ^ 2 * Zt z ≤ C1 * (Q 1 z + Q 2 z) := by
        calc (Work.Spaces.w z) ^ 2 * Zt z
            ≤ (Work.Spaces.w z) ^ 2 * (C1 * (Ps 1 z + Ps 2 z)) :=
              mul_le_mul_of_nonneg_left hZ hw
          _ = C1 * (Q 1 z + Q 2 z) := by rw [← hQeq 1 z, ← hQeq 2 z]; ring
      have hD' : (Work.Spaces.w z) ^ 2 * Dt z ≤ C1 * Q 1 z := by
        calc (Work.Spaces.w z) ^ 2 * Dt z
            ≤ (Work.Spaces.w z) ^ 2 * (C1 * Ps 1 z) := mul_le_mul_of_nonneg_left hD hw
          _ = C1 * Q 1 z := by rw [← hQeq 1 z]; ring
      calc (Work.Spaces.w z) ^ 2 * I z
          ≤ (Work.Spaces.w z) ^ 2 * (K0 * (Fs z + Ps 0 z + Zt z + Dt z)) :=
            mul_le_mul_of_nonneg_left h1z hw
        _ = K0 * ((Work.Spaces.w z) ^ 2 * Fs z + (Work.Spaces.w z) ^ 2 * Ps 0 z
              + (Work.Spaces.w z) ^ 2 * Zt z + (Work.Spaces.w z) ^ 2 * Dt z) := by ring
        _ ≤ K0 * (JintF z + Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z) := by
            refine mul_le_mul_of_nonneg_left ?_ hK0nn
            linarith [hFsQ z hz, hQeq 0 z, hZ', hD']
        _ ≤ K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
            have hinner : Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z
                ≤ (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by
              have h3 : 0 ≤ C1 * (3 * Q 0 z + Q 1 z + 2 * Q 2 z) :=
                mul_nonneg hC1nn (by linarith [hQnn 0 z, hQnn 1 z, hQnn 2 z])
              nlinarith [h3, hQnn 0 z, hQnn 1 z, hQnn 2 z]
            calc K0 * (JintF z + Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z)
                = K0 * JintF z + K0 * (Q 0 z + C1 * (Q 1 z + Q 2 z) + C1 * Q 1 z) := by ring
              _ ≤ K0 * JintF z + K0 * ((1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z)) :=
                  add_le_add le_rfl (mul_le_mul_of_nonneg_left hinner hK0nn)
              _ = K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) := by ring
  -- ### integrability of the dominating function
  have hIntJ : MeasureTheory.Integrable JintF
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := h.memF.2
  have hIntQ : ∀ j, j ≤ 2 → MeasureTheory.Integrable (Q j)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro j hj
    have hbase := Work.FTS.EllipticEst.integrableOn_slice_Iz α 2 ((hsmΨ.pth).pth) h.memB j hj
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
    rw [hQ]
    beta_reduce
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp [Work.Spaces.w]
    · refine MeasureTheory.integral_congr_ae
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_))
      beta_reduce
      have hp : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨hzpos, hθ⟩
      have hcomm : Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ) z θ :=
        Work.EllipticEst.H2W.pthIter2_DzIter_comm hsmΨ j hp
      rw [hcomm]
      rfl
  -- ### the integrated comparison
  have hIntQsum : MeasureTheory.Integrable (fun z => Q 0 z + Q 1 z + Q 2 z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hIntQ 0 (by norm_num)).add (hIntQ 1 (by norm_num))).add (hIntQ 2 (by norm_num))
  have hMint : MeasureTheory.Integrable
      (fun z => K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hIntJ.const_mul K0).add (hIntQsum.const_mul (K0 * (1 + 3 * C1)))
  have hmain : ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * I z
      ≤ ∫ z in Work.Spaces.Iz,
          K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (by
        rw [hI]; beta_reduce
        refine MeasureTheory.integral_nonneg_of_ae
          ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
            (Filter.Eventually.of_forall fun θ hθ => ?_))
        exact mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _)))
      hMint hslice
  -- ### the right-hand side
  set L : ℕ → ℝ := fun j => Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) with hLdef
  have hLnn : ∀ j, 0 ≤ L j := fun j => by
    rw [hLdef]; beta_reduce
    rw [Work.Spaces.L2Sq]
    exact MeasureTheory.integral_nonneg fun z =>
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hQint : ∀ j, ∫ z in Work.Spaces.Iz, Q j z = L j := fun j => by
    rw [hQ, hLdef]
    beta_reduce
    rw [Work.Spaces.L2Sq]
  have hJint : ∫ z in Work.Spaces.Iz, JintF z = Work.Spaces.HkSq α 2 F := rfl
  have hsum : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      = L 0 + L 1 + L 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hLdef]
  -- ### the value of the dominating integral
  have hE : ∫ z in Work.Spaces.Iz,
        (K0 * JintF z + K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      = K0 * Work.Spaces.HkSq α 2 F + K0 * (1 + 3 * C1) * (L 0 + L 1 + L 2) := by
    rw [MeasureTheory.integral_add (f := fun z => K0 * JintF z)
      (g := fun z => K0 * (1 + 3 * C1) * (Q 0 z + Q 1 z + Q 2 z))
      (hIntJ.const_mul K0) (hIntQsum.const_mul (K0 * (1 + 3 * C1)))]
    rw [MeasureTheory.integral_const_mul K0 JintF,
      MeasureTheory.integral_const_mul (K0 * (1 + 3 * C1))
        (fun z => Q 0 z + Q 1 z + Q 2 z)]
    rw [MeasureTheory.integral_add (f := fun z => Q 0 z + Q 1 z) (g := fun z => Q 2 z)
      ((hIntQ 0 (by norm_num)).add (hIntQ 1 (by norm_num))) (hIntQ 2 (by norm_num))]
    rw [MeasureTheory.integral_add (f := fun z => Q 0 z) (g := fun z => Q 1 z)
      (hIntQ 0 (by norm_num)) (hIntQ 1 (by norm_num))]
    rw [hJint, hQint 0, hQint 1, hQint 2]
  -- ### assembly
  have hLHS : Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * I z := by
    rw [slot01_LHS_eq α hα hα4 Ψ]
  rw [hLHS, hsum]
  refine le_trans (le_trans hmain (le_of_eq hE)) ?_
  have hH0 : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hS0 : 0 ≤ L 0 + L 1 + L 2 := by
    have := hLnn 0; have := hLnn 1; have := hLnn 2; linarith
  have hKC : 0 ≤ K0 * C1 := mul_nonneg hK0nn hC1nn
  -- `K0 ≤ K0 · (1 + 3 C1)`
  have hXK : K0 ≤ K0 * (1 + 3 * C1) := by nlinarith [hKC]
  have hA : K0 * Work.Spaces.HkSq α 2 F
      ≤ (K0 * (1 + 3 * C1)) * Work.Spaces.HkSq α 2 F :=
    mul_le_mul_of_nonneg_right hXK hH0
  nlinarith [hA, hS0, hH0]

end

end Work.FTS.EllipticEst.H2W
